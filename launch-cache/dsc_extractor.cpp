/* -*- mode: C++; c-basic-offset: 4; tab-width: 4 -*- 
 *
 * Copyright (c) 2011 Apple Inc. All rights reserved.
 *
 * @APPLE_LICENSE_HEADER_START@
 * 
 * This file contains Original Code and/or Modifications of Original Code
 * as defined in and that are subject to the Apple Public Source License
 * Version 2.0 (the 'License'). You may not use this file except in
 * compliance with the License. Please obtain a copy of the License at
 * http://www.opensource.apple.com/apsl/ and read it before using this
 * file.
 * 
 * The Original Code and all software distributed under the License are
 * distributed on an 'AS IS' basis, WITHOUT WARRANTY OF ANY KIND, EITHER
 * EXPRESS OR IMPLIED, AND APPLE HEREBY DISCLAIMS ALL SUCH WARRANTIES,
 * INCLUDING WITHOUT LIMITATION, ANY WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE, QUIET ENJOYMENT OR NON-INFRINGEMENT.
 * Please see the License for the specific language governing rights and
 * limitations under the License.
 * 
 * @APPLE_LICENSE_HEADER_END@
 */

#include <stdlib.h>
#include <stdio.h>
#include <unistd.h>
#include <sys/stat.h>
#include <string.h>
#include <fcntl.h>
#include <stdlib.h>
#include <errno.h>
#include <sys/mman.h>
#include <sys/syslimits.h>
#include <libkern/OSByteOrder.h>
#include <mach-o/fat.h>
#include <mach-o/arch.h>
#include <mach-o/loader.h>
#include <Availability.h>

#define NO_ULEB 
#include "Architectures.hpp"
#include "MachOFileAbstraction.hpp"
#include "CacheFileAbstraction.hpp"

#include "dsc_iterator.h"
#include "dsc_extractor.h"
#include "MachOTrie.hpp"

#include <vector>
#include <set>
#include <map>
#include <unordered_map>
#include <algorithm>
#include <dispatch/dispatch.h>
#include <string>
#include <mach/mach.h>

struct seg_info
{
				seg_info(const char* n, uint64_t o, uint64_t s) 
					: segName(n), offset(o), sizem(s) { }
	const char* segName;
	uint64_t	offset;
	uint64_t	sizem;
};

class CStringHash {
public:
	size_t operator()(const char* __s) const {
		size_t __h = 0;
		for ( ; *__s; ++__s)
			__h = 5 * __h + *__s;
		return __h;
	};
};
class CStringEquals {
public:
	bool operator()(const char* left, const char* right) const { return (strcmp(left, right) == 0); }
};
typedef std::unordered_map<const char*, std::vector<seg_info>, CStringHash, CStringEquals> NameToSegments;

// Filter to find individual symbol re-exports in trie
class NotReExportSymbol {
public:
	NotReExportSymbol(const std::set<int> &rd) :_reexportDeps(rd) {}
	bool operator()(const mach_o::trie::Entry &entry) const {
		bool result = isSymbolReExport(entry);
		if (result) {
			// <rdar://problem/17671438> Xcode 6 leaks in dyld_shared_cache_extract_dylibs
			::free((void*)entry.name);
			const_cast<mach_o::trie::Entry*>(&entry)->name = NULL;
		}
		return result;
	}
private:
	bool isSymbolReExport(const mach_o::trie::Entry &entry) const {
		if ( (entry.flags & EXPORT_SYMBOL_FLAGS_KIND_MASK) != EXPORT_SYMBOL_FLAGS_KIND_REGULAR )
			return true;
		if ( (entry.flags & EXPORT_SYMBOL_FLAGS_REEXPORT) == 0 )
			return true;
		// If the symbol comes from a dylib that is re-exported, this is not an individual symbol re-export
		if ( _reexportDeps.count((int)entry.other) != 0 )
			return true;
		return false;
	}
	const std::set<int> &_reexportDeps;
};

static void append_uleb128(uint64_t value, std::vector<uint8_t>& out) {
	uint8_t byte;
	do {
		byte = value & 0x7F;
		value &= ~0x7F;
		if ( value != 0 )
			byte |= 0x80;
		out.push_back(byte);
		value = value >> 7;
	} while( byte >= 0x80 );
}

class RebaseMaker {
public:
	std::vector<uint8_t> relocs;
	uintptr_t segmentStartMapped;
	int32_t currentSegment;
	RebaseMaker(int32_t _currentSegment, uintptr_t _segmentStartMapped) : currentSegment(_currentSegment), segmentStartMapped(_segmentStartMapped) {
		relocs.push_back(REBASE_OPCODE_SET_TYPE_IMM | REBASE_TYPE_POINTER);
	}
	void addSlide(uint8_t* loc) {
		addReloc(currentSegment, (uintptr_t)loc - segmentStartMapped);
	}
	void addReloc(int32_t segment, uintptr_t segmentOffset) {
		relocs.push_back(REBASE_OPCODE_SET_SEGMENT_AND_OFFSET_ULEB | segment);
		append_uleb128(segmentOffset, relocs);
		relocs.push_back(REBASE_OPCODE_DO_REBASE_IMM_TIMES | 1);
	}
	void finish() {
		relocs.push_back(REBASE_OPCODE_DONE);
	}
};

static void rebaseChain(uint8_t* pageContent, uint16_t startOffset, uintptr_t slideAmount, const dyldCacheSlideInfo2<LittleEndian>* slideInfo, RebaseMaker& slides)
{
	const uintptr_t   deltaMask    = (uintptr_t)(slideInfo->delta_mask());
	const uintptr_t   valueMask    = ~deltaMask;
	const uintptr_t   valueAdd     = (uintptr_t)(slideInfo->value_add());
	const unsigned	  deltaShift   = __builtin_ctzll(deltaMask) - 2;
	
	uint32_t pageOffset = startOffset;
	uint32_t delta = 1;
	while ( delta != 0 ) {
		uint8_t* loc = pageContent + pageOffset;
		uintptr_t rawValue = *((uintptr_t*)loc);
		delta = (uint32_t)((rawValue & deltaMask) >> deltaShift);
		uintptr_t value = (rawValue & valueMask);
		if ( value != 0 ) {
			value += valueAdd;
			value += slideAmount;
		}
		*((uintptr_t*)loc) = value;
		slides.addSlide(loc);
		//dyld::log("         pageOffset=0x%03X, loc=%p, org value=0x%08llX, new value=0x%08llX, delta=0x%X\n", pageOffset, loc, (uint64_t)rawValue, (uint64_t)value, delta);
		pageOffset += delta;
	}
}

template <typename A>
std::vector<uint8_t> slideOutput(macho_header<typename A::P>* mh, uint64_t textOffsetInCache, const void* mapped_cache) {
	typedef typename A::P P;
	
	auto cacheBase = ((uint64_t)mh->getSegment("__TEXT")->vmaddr()) - textOffsetInCache;
	auto dataSegment = mh->getSegment("__DATA");
	
	// grab the slide information from the cache
	const dyldCacheHeader<LittleEndian>* header = (dyldCacheHeader<LittleEndian>*)mapped_cache;
	const dyldCacheFileMapping<LittleEndian>* mappings = (dyldCacheFileMapping<LittleEndian>*)((char*)mapped_cache + header->mappingOffset());
	const dyldCacheFileMapping<LittleEndian>* dataMapping = &mappings[1];
	uint64_t dataStartAddress = dataMapping->address();
	const dyldCacheSlideInfo<LittleEndian>* slideInfo = (dyldCacheSlideInfo<LittleEndian>*)((char*)mapped_cache+header->slideInfoOffset());
	const dyldCacheSlideInfo2<LittleEndian>* slideHeader = (dyldCacheSlideInfo2<LittleEndian>*)(slideInfo);
	const uint32_t  page_size = slideHeader->page_size();
	const uint16_t* page_starts = (uint16_t*)((long)(slideInfo) + slideHeader->page_starts_offset());
	const uint16_t* page_extras = (uint16_t*)((long)(slideInfo) + slideHeader->page_extras_offset());
	
	auto slide = 0;
	auto slideOneSegment = [=](const macho_segment_command<P>* segment, int segmentIndex) {
		auto segmentInFile = (uint8_t*)mh + segment->fileoff();
		RebaseMaker rebaseMaker(segmentIndex, (uintptr_t)segmentInFile);
		uint32_t startAddr = segment->vmaddr() - dataStartAddress;
		uint32_t startPage = startAddr / 0x1000;
		uint32_t startAddrOff = startAddr & 0xfff;
		uint32_t endPage = (((segment->vmaddr() + segment->vmsize() + 0xfff) & ~0xfff) - dataStartAddress) / 0x1000;
		for (int i=startPage; i < endPage; ++i) {
			uint8_t* page = segmentInFile + ((i - startPage) * 0x1000) - startAddrOff;
			uint16_t pageEntry = page_starts[i];
			//dyld::log("page[%d]: page_starts[i]=0x%04X\n", i, pageEntry);
			if ( pageEntry == DYLD_CACHE_SLIDE_PAGE_ATTR_NO_REBASE )
				continue;
			if ( pageEntry & DYLD_CACHE_SLIDE_PAGE_ATTR_EXTRA ) {
				uint16_t chainIndex = (pageEntry & 0x3FFF);
				bool done = false;
				while ( !done ) {
					uint16_t info = page_extras[chainIndex];
					uint16_t pageStartOffset = (info & 0x3FFF)*4;
					//dyld::log("     chain[%d] pageOffset=0x%03X\n", chainIndex, pageStartOffset);
					rebaseChain(page, pageStartOffset, slide, slideHeader, rebaseMaker);
					done = (info & DYLD_CACHE_SLIDE_PAGE_ATTR_END);
					++chainIndex;
				}
			}
			else {
				uint32_t pageOffset = pageEntry * 4;
				//dyld::log("     start pageOffset=0x%03X\n", pageOffset);
				rebaseChain(page, pageOffset, slide, slideHeader, rebaseMaker);
			}
		}
		rebaseMaker.finish();
		return rebaseMaker.relocs;
	};
	auto ret = slideOneSegment(mh->getSegment("__DATA"), 1);
	auto constData = mh->getSegment("__DATA_CONST");
	if (constData) {
		auto c = slideOneSegment(constData, 2);
		ret.insert(ret.end(), c.begin(), c.end());
	}
	return ret;
}

// copied from ObjC2Abstraction

struct my_objc_object {
	uint64_t isa;
};

struct my_objc_class: my_objc_object {
	uint64_t superclass;
	uint64_t cache;
	uint64_t vtable;
	uint64_t data;
};

struct my_objc_class_data {
	uint32_t flags;
	uint32_t instanceStart;
	uint32_t instanceSize;
	uint64_t ivarLayout;
	uint64_t name;
	uint64_t baseMethods;
	uint64_t baseProtocols;
	uint64_t ivars;
	uint64_t weakIvarLayout;
	uint64_t baseProperties;
};

struct my_objc_method {
	uint64_t name;
	uint64_t type;
	uint64_t imp;
};

struct my_objc_method_list {
	uint32_t entsize;
	uint32_t count;
	my_objc_method methods[];
};

template <typename A>
int fixupObjc(macho_header<typename A::P>* mh, uint64_t textOffsetInCache, const void* mapped_cache) {
	typedef typename A::P P;
	auto cacheBase = ((uint64_t)mh->getSegment("__TEXT")->vmaddr()) - textOffsetInCache;
	const macho_section<P>* methnameSec = mh->getSection("__TEXT", "__objc_methname");
	// method name to in-memory address
	std::unordered_map<std::string, uint64_t> methnameToAddr;
	for (uint64_t off = 0; off < methnameSec->size();) {
		const char* methname = (const char*)mh + methnameSec->offset() + off;
		methnameToAddr[methname] = methnameSec->addr() + off;
		off += strlen(methname) + 1;
	}
	const macho_section<P>* selrefsSec = mh->getSection("__DATA", "__objc_selrefs");
	uint64_t* selrefsArr = (uint64_t*)(((char*)mh) + selrefsSec->offset());
	for (uint64_t index = 0; index < selrefsSec->size() / sizeof(uint64_t); index++) {
		const char* origStr = (const char*)mapped_cache + ((selrefsArr[index] & 0xffffffffffffULL) - cacheBase);
		printf("%p\n", origStr);
		selrefsArr[index] = methnameToAddr[origStr];
	}
	// next, fixup the individual classes
	auto dataSeg = mh->getSegment("__DATA");
	
	auto dataConstSeg = mh->getSegment("__DATA_CONST");
	
	auto addrToMyDataConstMapped = [=](uint64_t addr) {
		if (addr == 0) return (const char*)nullptr;
		return (const char*)mh + dataConstSeg->fileoff() + (addr - dataConstSeg->vmaddr());
	};

	auto addrToMyDataMapped = [=](uint64_t addr) {
		if (addr == 0) return (const char*)nullptr;
		if (!(addr >= dataSeg->vmaddr() && addr < dataSeg->vmaddr() + dataSeg->vmsize()) && dataConstSeg) {
			return addrToMyDataConstMapped(addr);
		}
		return (const char*)mh + dataSeg->fileoff() + (addr - dataSeg->vmaddr());
	};
	
	auto addrToTheirTextMapped = [=](uint64_t addr) {
		if (addr == 0) return (const char*)nullptr;
		return (const char*)mapped_cache + (addr - cacheBase);
	};
	
	const macho_section<P>* classlistSec = mh->getSection("__DATA", "__objc_classlist");
	uint64_t* classesArr = (uint64_t*)(((char*)mh) + classlistSec->offset());
	for (uint64_t index = 0; index < classlistSec->size() / sizeof(uint64_t); index++) {
		my_objc_class* cls = (my_objc_class*)addrToMyDataMapped(classesArr[index]);
		my_objc_class_data* clsData = (my_objc_class_data*)addrToMyDataMapped(cls->data);
		if (clsData && clsData->baseMethods) {
			my_objc_method_list* methodList = (my_objc_method_list*)addrToMyDataMapped(clsData->baseMethods);
			for (int methIndex = 0; methIndex < methodList->count; methIndex++) {
				const char* origStr = addrToTheirTextMapped(methodList->methods[methIndex].name);
				methodList->methods[methIndex].name = methnameToAddr[origStr];
			}
			methodList->entsize &= ~3; // clear the optimized flag
		}
		// todo: protocols
	}

	// oh, and remove the optimized flag for the image
	const macho_section<P>* objcImageInfoSection = mh->getSection("__DATA", "__objc_imageinfo");
	uint32_t* objcImageInfo = (uint32_t*)((char*)mh + objcImageInfoSection->offset());
	objcImageInfo[1] &= ~(1 << 3);
	
	// fixup lazy pointers
	// la_symbol_ptr should point into stub_helper
	
	const macho_dyld_info_command<P>* dyldInfo = (const macho_dyld_info_command<P>*)mh->getLoadCommand(LC_DYLD_INFO_ONLY);
	auto runOneLazyBind = [=](uint32_t cmdOff) {
		const uint8_t* cmds = (const uint8_t*)mh + dyldInfo->lazy_bind_off() + cmdOff;
		const uint8_t* cmdsEnd = (const uint8_t*)mh + dyldInfo->lazy_bind_off() + dyldInfo->lazy_bind_size();
		while (cmds < cmdsEnd) {
			uint8_t immediate = *cmds & BIND_IMMEDIATE_MASK;
			uint8_t opcode = *cmds & BIND_OPCODE_MASK;
			++cmds;
			switch (opcode) {
				case BIND_OPCODE_SET_SEGMENT_AND_OFFSET_ULEB:
					return mach_o::trie::read_uleb128(cmds, cmdsEnd);
			}
		}
	};
	const macho_section<P>* lazyStubSec = mh->getSection("__TEXT", "__stub_helper");
	// x86_64 specific
	uint32_t stubStart, stubSize, stubAddrOffset;
	if (mh->cputype() == CPU_TYPE_X86_64) {
		stubStart = 0x10;
		stubSize = 0xa;
		stubAddrOffset = 0x1;
	} else if (mh->cputype() == CPU_TYPE_ARM64) {
		stubStart = 0x18;
		stubSize = 0xc;
		stubAddrOffset = 0x8;
	} else {
		abort();
	}
	
	const uint8_t* lazyStubStart = (const uint8_t*)mh + lazyStubSec->offset();
	const uint8_t* lazyStubEnd = (const uint8_t*)mh + lazyStubSec->offset() + lazyStubSec->size();
	for (const uint8_t* lazyStub = lazyStubStart + stubStart; lazyStub < lazyStubEnd; lazyStub += stubSize) {
		uint32_t offset = *(uint32_t*)(lazyStub + stubAddrOffset);
		uint64_t stubVMAddr = (uint64_t)(lazyStub - lazyStubStart) + lazyStubSec->addr();
		uint32_t lazyBindDataOffset = runOneLazyBind(offset);
		uint64_t* data = (uint64_t*)((uint8_t*)mh + dataSeg->fileoff() + lazyBindDataOffset);
		*data = stubVMAddr;
	}
	return 0;
}

template <typename A>
int optimize_linkedit(macho_header<typename A::P>* mh, uint64_t textOffsetInCache, const void* mapped_cache, uint64_t* newSize) 
{
	typedef typename A::P P;
	typedef typename A::P::E E;
    typedef typename A::P::uint_t pint_t;

	// update header flags
	mh->set_flags(mh->flags() & 0x7FFFFFFF); // remove in-cache bit
	
	// update load commands
	uint64_t cumulativeFileSize = 0;
	const unsigned origLoadCommandsSize = mh->sizeofcmds();
	unsigned bytesRemaining = origLoadCommandsSize;
	unsigned removedCount = 0;
	const macho_load_command<P>* const cmds = (macho_load_command<P>*)((uint8_t*)mh + sizeof(macho_header<P>));
	const uint32_t cmdCount = mh->ncmds();
	const macho_load_command<P>* cmd = cmds;
	macho_segment_command<P>* linkEditSegCmd = NULL;
	macho_symtab_command<P>* symtab = NULL;
	macho_dysymtab_command<P>*	dynamicSymTab = NULL;
	macho_linkedit_data_command<P>*	functionStarts = NULL;
	macho_linkedit_data_command<P>*	dataInCode = NULL;
	macho_dyld_info_command<P>* dyldInfo = NULL;
	uint32_t exportsTrieOffset = 0;
	uint32_t exportsTrieSize = 0;
	std::set<int> reexportDeps;
	int depIndex = 0;
	for (uint32_t i = 0; i < cmdCount; ++i) {
	    bool remove = false;
		fprintf(stderr, "Command %x\n", cmd->cmd());
		switch ( cmd->cmd() ) {
		case macho_segment_command<P>::CMD:
			{
			// update segment/section file offsets
			macho_segment_command<P>* segCmd = (macho_segment_command<P>*)cmd;
			segCmd->set_fileoff(cumulativeFileSize);
			macho_section<P>* const sectionsStart = (macho_section<P>*)((char*)segCmd + sizeof(macho_segment_command<P>));
			macho_section<P>* const sectionsEnd = &sectionsStart[segCmd->nsects()];
			for(macho_section<P>* sect = sectionsStart; sect < sectionsEnd; ++sect) {
				if ( sect->offset() != 0 )
					sect->set_offset((uint32_t)(cumulativeFileSize+sect->addr()-segCmd->vmaddr()));
			}
			if ( strcmp(segCmd->segname(), "__LINKEDIT") == 0 ) {
				linkEditSegCmd = segCmd;
			}
			if ( strcmp(segCmd->segname(), "__DATA") == 0 ) {
				segCmd->set_vmsize((segCmd->vmsize() + 0xfff) & ~0xfff);
			}
			cumulativeFileSize += segCmd->filesize();
			}
			break;
		case LC_DYLD_INFO_ONLY:
			{
			// zero out all dyld info
			/* macho_dyld_info_command<P>* */ dyldInfo = (macho_dyld_info_command<P>*)cmd;
			exportsTrieOffset = dyldInfo->export_off();
			exportsTrieSize = dyldInfo->export_size();
			/*
			dyldInfo->set_rebase_off(0);
			dyldInfo->set_rebase_size(0);
			dyldInfo->set_bind_off(0);
			dyldInfo->set_bind_size(0);
			dyldInfo->set_weak_bind_off(0);
			dyldInfo->set_weak_bind_size(0);
			dyldInfo->set_lazy_bind_off(0);
			dyldInfo->set_lazy_bind_size(0);
			dyldInfo->set_export_off(0);
			dyldInfo->set_export_size(0);
			*/
			}
			break;
		case LC_SYMTAB:
			symtab = (macho_symtab_command<P>*)cmd;
			break;
		case LC_DYSYMTAB:
			dynamicSymTab = (macho_dysymtab_command<P>*)cmd;
			break;
		case LC_FUNCTION_STARTS:
			functionStarts = (macho_linkedit_data_command<P>*)cmd;
			break;
		case LC_DATA_IN_CODE:
			dataInCode = (macho_linkedit_data_command<P>*)cmd;
			break;
		case LC_LOAD_DYLIB:
		case LC_LOAD_WEAK_DYLIB:
		case LC_REEXPORT_DYLIB:
		case LC_LOAD_UPWARD_DYLIB:
			++depIndex;
			if ( cmd->cmd() == LC_REEXPORT_DYLIB ) {
				reexportDeps.insert(depIndex);
			}
			break;
		case LC_SEGMENT_SPLIT_INFO:
			// <rdar://problem/23212513> dylibs iOS 9 dyld caches have bogus LC_SEGMENT_SPLIT_INFO
			remove = true;
			break;
		}
		uint32_t cmdSize = cmd->cmdsize();
		macho_load_command<P>* nextCmd = (macho_load_command<P>*)(((uint8_t*)cmd)+cmdSize);
		if ( remove ) {
			::memmove((void*)cmd, (void*)nextCmd, bytesRemaining);
			++removedCount;
		}
		else {
			bytesRemaining -= cmdSize;
			cmd = nextCmd;
		}
	}
	// zero out stuff removed
	::bzero((void*)cmd, bytesRemaining);
	// update header
	mh->set_ncmds(cmdCount - removedCount);
	mh->set_sizeofcmds(origLoadCommandsSize - bytesRemaining);

	// rebuild symbol table
	if ( linkEditSegCmd == NULL ) {
		fprintf(stderr, "__LINKEDIT not found\n");
		return -1;
	}
	if ( symtab == NULL ) {
		fprintf(stderr, "LC_SYMTAB not found\n");
		return -1;
	}
	if ( dynamicSymTab == NULL ) {
		fprintf(stderr, "LC_DYSYMTAB not found\n");
		return -1;
	}

	if ( dyldInfo == NULL ) {
		fprintf(stderr, "dyldInfo not found\n");
		return -1;
	}
	
	// remove the slide linked list from the dyld cache
	// and generate crappy rebase info
	std::vector<uint8_t> rebaseInfo = slideOutput<A>(mh, textOffsetInCache, mapped_cache);

	linkEditSegCmd->set_fileoff((linkEditSegCmd->fileoff() + 0xfff) & ~0xfff);
	const uint64_t newDyldInfoOffset = linkEditSegCmd->fileoff();
	uint64_t newDyldInfoSize = 0;

	//memcpy((char*)mh + newDyldInfoOffset + newDyldInfoSize, (char*)mapped_cache + dyldInfo->rebase_off(), dyldInfo->rebase_size());
	memcpy((char*)mh + newDyldInfoOffset + newDyldInfoSize, rebaseInfo.data(), rebaseInfo.size());
	dyldInfo->set_rebase_size(rebaseInfo.size());
	dyldInfo->set_rebase_off(newDyldInfoOffset + newDyldInfoSize);
	newDyldInfoSize += dyldInfo->rebase_size();

	memcpy((char*)mh + newDyldInfoOffset + newDyldInfoSize, (char*)mapped_cache + dyldInfo->bind_off(), dyldInfo->bind_size());
	dyldInfo->set_bind_off(newDyldInfoOffset + newDyldInfoSize);
	newDyldInfoSize += dyldInfo->bind_size();

	memcpy((char*)mh + newDyldInfoOffset + newDyldInfoSize, (char*)mapped_cache + dyldInfo->lazy_bind_off(), dyldInfo->lazy_bind_size());
	dyldInfo->set_lazy_bind_off(newDyldInfoOffset + newDyldInfoSize);
	newDyldInfoSize += dyldInfo->lazy_bind_size();

	memcpy((char*)mh + newDyldInfoOffset + newDyldInfoSize, (char*)mapped_cache + dyldInfo->export_off(), dyldInfo->export_size());
	dyldInfo->set_export_off(newDyldInfoOffset + newDyldInfoSize);

	newDyldInfoSize += dyldInfo->export_size();

	const uint64_t newFunctionStartsOffset = newDyldInfoOffset + newDyldInfoSize;
	uint32_t functionStartsSize = 0;
	if ( functionStarts != NULL ) {
		// copy function starts from original cache file to new mapped dylib file
		functionStartsSize = functionStarts->datasize();
		memcpy((char*)mh + newFunctionStartsOffset, (char*)mapped_cache + functionStarts->dataoff(), functionStartsSize);
	}
	const uint64_t newDataInCodeOffset = (newFunctionStartsOffset + functionStartsSize + sizeof(pint_t) - 1) & (-sizeof(pint_t)); // pointer align
	uint32_t dataInCodeSize = 0;
	if ( dataInCode != NULL ) {
		// copy data-in-code info from original cache file to new mapped dylib file
		dataInCodeSize = dataInCode->datasize();
		memcpy((char*)mh + newDataInCodeOffset, (char*)mapped_cache + dataInCode->dataoff(), dataInCodeSize);
	}

	std::vector<mach_o::trie::Entry> exports;
	if ( exportsTrieSize != 0 ) {
		const uint8_t* exportsStart = ((uint8_t*)mapped_cache) + exportsTrieOffset; 
		const uint8_t* exportsEnd = &exportsStart[exportsTrieSize];
		mach_o::trie::parseTrie(exportsStart, exportsEnd, exports);
		exports.erase(std::remove_if(exports.begin(), exports.end(), NotReExportSymbol(reexportDeps)), exports.end());
	}

	// look for local symbol info in unmapped part of shared cache
	dyldCacheHeader<E>* header = (dyldCacheHeader<E>*)mapped_cache;
	macho_nlist<P>* localNlists = NULL;
	uint32_t localNlistCount = 0;
	const char* localStrings = NULL;
	const char* localStringsEnd = NULL;
	if ( header->mappingOffset() > offsetof(dyld_cache_header,localSymbolsSize) ) {
		dyldCacheLocalSymbolsInfo<E>* localInfo = (dyldCacheLocalSymbolsInfo<E>*)(((uint8_t*)mapped_cache) + header->localSymbolsOffset());
		dyldCacheLocalSymbolEntry<E>* entries = (dyldCacheLocalSymbolEntry<E>*)(((uint8_t*)mapped_cache) + header->localSymbolsOffset() + localInfo->entriesOffset());
		macho_nlist<P>* allLocalNlists = (macho_nlist<P>*)(((uint8_t*)localInfo) + localInfo->nlistOffset());
		const uint32_t entriesCount = localInfo->entriesCount();
		for (uint32_t i=0; i < entriesCount; ++i) {
			if ( entries[i].dylibOffset() == textOffsetInCache ) {
				uint32_t localNlistStart = entries[i].nlistStartIndex();
				localNlistCount = entries[i].nlistCount();
				localNlists = &allLocalNlists[localNlistStart];
				localStrings = ((char*)localInfo) + localInfo->stringsOffset();
				localStringsEnd = &localStrings[localInfo->stringsSize()];
				break;
			}
		}
	}
	// compute number of symbols in new symbol table
	const macho_nlist<P>* const mergedSymTabStart = (macho_nlist<P>*)(((uint8_t*)mapped_cache) + symtab->symoff());
	const macho_nlist<P>* const mergedSymTabend = &mergedSymTabStart[symtab->nsyms()];
	uint32_t newSymCount = symtab->nsyms();
	if ( localNlists != NULL ) {
		newSymCount = localNlistCount;
		for (const macho_nlist<P>* s = mergedSymTabStart; s != mergedSymTabend; ++s) {
			// skip any locals in cache
			if ( (s->n_type() & (N_TYPE|N_EXT)) == N_SECT ) 
				continue;
			++newSymCount;
		}
	}
	
	// add room for N_INDR symbols for re-exported symbols
	newSymCount += exports.size();

	// copy symbol entries and strings from original cache file to new mapped dylib file
	const uint64_t newSymTabOffset = (newDataInCodeOffset + dataInCodeSize + sizeof(pint_t) - 1) & (-sizeof(pint_t)); // pointer align
	const uint64_t newIndSymTabOffset = newSymTabOffset + newSymCount*sizeof(macho_nlist<P>);
	const uint64_t newStringPoolOffset = newIndSymTabOffset + dynamicSymTab->nindirectsyms()*sizeof(uint32_t);
	macho_nlist<P>* const newSymTabStart = (macho_nlist<P>*)(((uint8_t*)mh) + newSymTabOffset);
	char* const newStringPoolStart = (char*)mh + newStringPoolOffset;
	const uint32_t* mergedIndSymTab = (uint32_t*)((char*)mapped_cache + dynamicSymTab->indirectsymoff());
	const char* mergedStringPoolStart = (char*)mapped_cache + symtab->stroff();
	const char* mergedStringPoolEnd = &mergedStringPoolStart[symtab->strsize()];
	macho_nlist<P>* t = newSymTabStart;
	int poolOffset = 0;
	uint32_t symbolsCopied = 0;
	newStringPoolStart[poolOffset++] = '\0'; // first pool entry is always empty string
	for (const macho_nlist<P>* s = mergedSymTabStart; s != mergedSymTabend; ++s) {
		// if we have better local symbol info, skip any locals here
		if ( (localNlists != NULL) && ((s->n_type() & (N_TYPE|N_EXT)) == N_SECT) ) 
			continue;
		*t = *s;
		t->set_n_strx(poolOffset);
		const char* symName = &mergedStringPoolStart[s->n_strx()];
		if ( symName > mergedStringPoolEnd )
			symName = "<corrupt symbol name>";
		strcpy(&newStringPoolStart[poolOffset], symName);
		poolOffset += (strlen(symName) + 1);
		++t;
		++symbolsCopied;
	}
	// <rdar://problem/16529213> recreate N_INDR symbols in extracted dylibs for debugger
	for (std::vector<mach_o::trie::Entry>::iterator it = exports.begin(); it != exports.end(); ++it) {
		strcpy(&newStringPoolStart[poolOffset], it->name);
		t->set_n_strx(poolOffset);
		poolOffset += (strlen(it->name) + 1);
		t->set_n_type(N_INDR | N_EXT);
		t->set_n_sect(0);
		t->set_n_desc(0);
		const char* importName = it->importName;
		if ( *importName == '\0' )
			importName = it->name;
		strcpy(&newStringPoolStart[poolOffset], importName);
		t->set_n_value(poolOffset);
		poolOffset += (strlen(importName) + 1);
		++t;
		++symbolsCopied;
	}
	if ( localNlists != NULL ) {
		// update load command to reflect new count of locals
		dynamicSymTab->set_ilocalsym(symbolsCopied);
		dynamicSymTab->set_nlocalsym(localNlistCount);
		// copy local symbols
		for (uint32_t i=0; i < localNlistCount; ++i) {
			const char* localName = &localStrings[localNlists[i].n_strx()];
			if ( localName > localStringsEnd )
				localName = "<corrupt local symbol name>";
			*t = localNlists[i];
			t->set_n_strx(poolOffset);
			strcpy(&newStringPoolStart[poolOffset], localName);
			poolOffset += (strlen(localName) + 1);
			++t;
			++symbolsCopied;
		}
	}
	
	if ( newSymCount != symbolsCopied ) {
		fprintf(stderr, "symbol count miscalculation\n");
		return -1;
	}
	
	// pointer align string pool size
	while ( (poolOffset % sizeof(pint_t)) != 0 )
		++poolOffset; 
	// copy indirect symbol table
	uint32_t* newIndSymTab = (uint32_t*)((char*)mh + newIndSymTabOffset);
	memcpy(newIndSymTab, mergedIndSymTab, dynamicSymTab->nindirectsyms()*sizeof(uint32_t));
	
	// update load commands
	if ( functionStarts != NULL ) {
		functionStarts->set_dataoff((uint32_t)newFunctionStartsOffset);
		functionStarts->set_datasize(functionStartsSize);
	}
	if ( dataInCode != NULL ) {
		dataInCode->set_dataoff((uint32_t)newDataInCodeOffset);
		dataInCode->set_datasize(dataInCodeSize);
	}
	symtab->set_nsyms(symbolsCopied);
	symtab->set_symoff((uint32_t)newSymTabOffset);
	symtab->set_stroff((uint32_t)newStringPoolOffset);
	symtab->set_strsize(poolOffset);
	dynamicSymTab->set_extreloff(0);
	dynamicSymTab->set_nextrel(0);
	dynamicSymTab->set_locreloff(0);
	dynamicSymTab->set_nlocrel(0);
	dynamicSymTab->set_indirectsymoff((uint32_t)newIndSymTabOffset);
	linkEditSegCmd->set_filesize(symtab->stroff()+symtab->strsize() - linkEditSegCmd->fileoff());
	linkEditSegCmd->set_vmsize( (linkEditSegCmd->filesize()+4095) & (-4096) );
	
	// return new size
	*newSize = (symtab->stroff()+symtab->strsize()+4095) & (-4096);
	linkEditSegCmd->set_filesize(*newSize - linkEditSegCmd->fileoff());
	
	fixupObjc<A>(mh, textOffsetInCache, mapped_cache);
	
	// <rdar://problem/17671438> Xcode 6 leaks in dyld_shared_cache_extract_dylibs
	for (std::vector<mach_o::trie::Entry>::iterator it = exports.begin(); it != exports.end(); ++it) {
		::free((void*)(it->name));
	}
	
	return 0;
}



static void make_dirs(const char* file_path) 
{
	//printf("make_dirs(%s)\n", file_path);
	char dirs[strlen(file_path)+1];
	strcpy(dirs, file_path);
	char* lastSlash = strrchr(dirs, '/');
	if ( lastSlash == NULL )
		return;
	lastSlash[1] = '\0';
	struct stat stat_buf;
	if ( stat(dirs, &stat_buf) != 0 ) {
		char* afterSlash = &dirs[1];
		char* slash;
		while ( (slash = strchr(afterSlash, '/')) != NULL ) {
			*slash = '\0';
			::mkdir(dirs, S_IRWXU | S_IRGRP|S_IXGRP | S_IROTH|S_IXOTH);
			//printf("mkdir(%s)\n", dirs);
			*slash = '/';
			afterSlash = slash+1;
		}
	}
}



template <typename A>
size_t dylib_maker(const void* mapped_cache, std::vector<uint8_t> &dylib_data, const std::vector<seg_info>& segments) {		
	typedef typename A::P P;
    
    size_t  additionalSize  = 0;
	for(std::vector<seg_info>::const_iterator it=segments.begin(); it != segments.end(); ++it) {
		additionalSize                          += it->sizem;
	}
    
    dylib_data.reserve(dylib_data.size() + additionalSize);
    
    uint32_t                nfat_archs          = 0;
	uint32_t                offsetInFatFile     = 4096;
    uint8_t                 *base_ptr           = &dylib_data.front();
	    
#define FH reinterpret_cast<fat_header*>(base_ptr)
#define FA reinterpret_cast<fat_arch*>(base_ptr + (8 + (nfat_archs - 1) * sizeof(fat_arch)))
    
    if(dylib_data.size() >= 4096 && OSSwapBigToHostInt32(FH->magic) == FAT_MAGIC) {
		// have fat header, append new arch to end
        nfat_archs                              = OSSwapBigToHostInt32(FH->nfat_arch);
		offsetInFatFile                         = OSSwapBigToHostInt32(FA->offset) + OSSwapBigToHostInt32(FA->size);
    }
    
    dylib_data.resize(offsetInFatFile);
    base_ptr                                    = &dylib_data.front();
    
    FH->magic                                   = OSSwapHostToBigInt32(FAT_MAGIC);
    FH->nfat_arch                               = OSSwapHostToBigInt32(++nfat_archs);
    
    FA->cputype                                 = 0; // filled in later
    FA->cpusubtype                              = 0; // filled in later
    FA->offset                                  = OSSwapHostToBigInt32(offsetInFatFile);
    FA->size                                    = 0; // filled in later
    FA->align                                   = OSSwapHostToBigInt32(12);
    
	// Write regular segments into the buffer
	uint64_t                totalSize           = 0;
    uint64_t				textOffsetInCache	= 0;
	for( std::vector<seg_info>::const_iterator it=segments.begin(); it != segments.end(); ++it) {
        
        if(strcmp(it->segName, "__TEXT") == 0 ) {
			textOffsetInCache					= it->offset;
            const macho_header<P>   *textMH     = reinterpret_cast<macho_header<P>*>((uint8_t*)mapped_cache+textOffsetInCache);
            FA->cputype                         = OSSwapHostToBigInt32(textMH->cputype()); 
            FA->cpusubtype                      = OSSwapHostToBigInt32(textMH->cpusubtype());
            
            // if this cputype/subtype already exist in fat header, then return immediately
            for(uint32_t i=0; i < nfat_archs-1; ++i) {
                fat_arch            *afa        = reinterpret_cast<fat_arch*>(base_ptr+8)+i;
                
                if(   afa->cputype == FA->cputype
                   && afa->cpusubtype == FA->cpusubtype) {
                    //fprintf(stderr, "arch already exists in fat dylib\n");
                    dylib_data.resize(offsetInFatFile);
                    return offsetInFatFile;
                }
            }
		}
        
		//printf("segName=%s, offset=0x%llX, size=0x%0llX\n", it->segName, it->offset, it->sizem);
        std::copy(((uint8_t*)mapped_cache)+it->offset, ((uint8_t*)mapped_cache)+it->offset+it->sizem, std::back_inserter(dylib_data));
        base_ptr                                = &dylib_data.front();
        totalSize                               += it->sizem;
	}
    
	FA->size                                    = OSSwapHostToBigInt32(totalSize); 
    
	// optimize linkedit
	uint64_t                newSize             = dylib_data.size() + 0x10000;
	dylib_data.resize(offsetInFatFile+newSize);
	optimize_linkedit<A>(((macho_header<P>*)(base_ptr+offsetInFatFile)), textOffsetInCache, mapped_cache, &newSize);
	
	// update fat header with new file size
    dylib_data.resize(offsetInFatFile+newSize);
    base_ptr                                    = &dylib_data.front();
	FA->size                                    = OSSwapHostToBigInt32(newSize);
#undef FH
#undef FA
	return offsetInFatFile;
} 


int dyld_shared_cache_extract_dylibs_progress(const char* shared_cache_file_path, const char* extraction_root_path,
													void (^progress)(unsigned current, unsigned total))
{
	struct stat statbuf;
	if (stat(shared_cache_file_path, &statbuf)) {
		fprintf(stderr, "Error: stat failed for dyld shared cache at %s\n", shared_cache_file_path);
		return -1;
	}
		
	int cache_fd = open(shared_cache_file_path, O_RDONLY);
	if (cache_fd < 0) {
		fprintf(stderr, "Error: failed to open shared cache file at %s\n", shared_cache_file_path);
		return -1;
	}
	if (fcntl(cache_fd, F_NOCACHE, 1) == -1) {
		fprintf(stderr, "nocache failed\n");
		return -1;
	}
	
	void* mapped_cache = nullptr;
	// mmap(NULL, statbuf.st_size, PROT_READ, MAP_PRIVATE | MAP_NOCACHE, cache_fd, 0);
	//if (mapped_cache == MAP_FAILED) {
	if ( vm_allocate(mach_task_self(), (vm_address_t*)(&mapped_cache), statbuf.st_size, VM_FLAGS_ANYWHERE | VM_FLAGS_NO_CACHE) != KERN_SUCCESS ) {
		fprintf(stderr, "Error: mmap() for shared cache at %s failed, errno=%d\n", shared_cache_file_path, errno);
		return -1;
	}
	if (pread(cache_fd, mapped_cache, statbuf.st_size, 0) <= 0) {
		fprintf(stderr, "pread failed\n");
		return -1;
	}
    
    close(cache_fd);

	// instantiate arch specific dylib maker
    size_t (*dylib_create_func)(const void*, std::vector<uint8_t>&, const std::vector<seg_info>&) = NULL;
	     if ( strcmp((char*)mapped_cache, "dyld_v1    i386") == 0 ) 
		dylib_create_func = dylib_maker<x86>;
	else if ( strcmp((char*)mapped_cache, "dyld_v1  x86_64") == 0 ) 
		dylib_create_func = dylib_maker<x86_64>;
	else if ( strcmp((char*)mapped_cache, "dyld_v1 x86_64h") == 0 ) 
		dylib_create_func = dylib_maker<x86_64>;
	else if ( strcmp((char*)mapped_cache, "dyld_v1   armv5") == 0 ) 
		dylib_create_func = dylib_maker<arm>;
	else if ( strcmp((char*)mapped_cache, "dyld_v1   armv6") == 0 ) 
		dylib_create_func = dylib_maker<arm>;
	else if ( strcmp((char*)mapped_cache, "dyld_v1   armv7") == 0 ) 
		dylib_create_func = dylib_maker<arm>;
	else if ( strncmp((char*)mapped_cache, "dyld_v1  armv7", 14) == 0 ) 
		dylib_create_func = dylib_maker<arm>;
	else if ( strcmp((char*)mapped_cache, "dyld_v1   arm64") == 0 ) 
		dylib_create_func = dylib_maker<arm64>;
	else {
		fprintf(stderr, "Error: unrecognized dyld shared cache magic.\n");
        munmap(mapped_cache, statbuf.st_size);
		return -1;
	}

	// iterate through all images in cache and build map of dylibs and segments
	__block NameToSegments  map;
	__block int				result              = dyld_shared_cache_iterate(mapped_cache, (uint32_t)statbuf.st_size, ^(const dyld_shared_cache_dylib_info* dylibInfo, const dyld_shared_cache_segment_info* segInfo) {
        map[dylibInfo->path].push_back(seg_info(segInfo->name, segInfo->fileOffset, segInfo->fileSize));
    });

    if(result != 0) {
		fprintf(stderr, "Error: dyld_shared_cache_iterate_segments_with_slide failed.\n");
        munmap(mapped_cache, statbuf.st_size);
		return result;
    }

	// for each dylib instantiate a dylib file
    dispatch_group_t        group               = dispatch_group_create();
    dispatch_semaphore_t    sema                = dispatch_semaphore_create(2);
    dispatch_queue_t        process_queue       = dispatch_get_global_queue(DISPATCH_QUEUE_PRIORITY_LOW, 0);
    dispatch_queue_t        writer_queue        = dispatch_queue_create("dyld writer queue", 0);
    
	__block unsigned        count               = 0;
    
	for ( NameToSegments::iterator it = map.begin(); it != map.end(); ++it) {
		//fprintf(stderr, "%s\n", it->first);
		//if (strcmp(it->first, "/System/Library/Frameworks/ClassKit.framework/ClassKit") != 0) continue;
		bool found = strcmp(it->first, "/System/Library/Frameworks/BusinessChat.framework/Versions/A/BusinessChat") == 0;
		found = found || strcmp(it->first, "/System/Library/Frameworks/BusinessChat.framework/BusinessChat") == 0;
		if (!found) continue;
		dispatch_semaphore_wait(sema, DISPATCH_TIME_FOREVER);
        dispatch_group_async(group, process_queue, ^{
            
            char    dylib_path[PATH_MAX];
            strcpy(dylib_path, extraction_root_path);
            strcat(dylib_path, "/");
            strcat(dylib_path, it->first);
            
            //printf("%s with %lu segments\n", dylib_path, it->second.size());
            // make sure all directories in this path exist
            make_dirs(dylib_path);
            
            // open file, create if does not already exist
			::unlink(dylib_path);
            int fd = ::open(dylib_path, O_CREAT | O_EXLOCK | O_RDWR, 0644);
            if ( fd == -1 ) {
                fprintf(stderr, "can't open or create dylib file %s, errnor=%d\n", dylib_path, errno);
                result    = -1;
                return;
            }
            
            struct stat statbuf;
            if (fstat(fd, &statbuf)) {
                fprintf(stderr, "Error: stat failed for dyld file %s, errnor=%d\n", dylib_path, errno);
                close(fd);
                result    = -1;
                return;
            }
            
            std::vector<uint8_t> *vec   = new std::vector<uint8_t>(statbuf.st_size);
            if(pread(fd, &vec->front(), vec->size(), 0) != (long)vec->size()) {
                fprintf(stderr, "can't read dylib file %s, errnor=%d\n", dylib_path, errno);
                close(fd);
                result    = -1;
                return;
            }
            
            const size_t    offset  = dylib_create_func(mapped_cache, *vec, it->second);
            
            dispatch_group_async(group, writer_queue, ^{
                progress(count++, (unsigned)map.size());
                
                if(offset != vec->size()) {
                    //Write out the first page, and everything after offset
                    if(   pwrite(fd, &vec->front(), 4096, 0) == -1 
                       || pwrite(fd, &vec->front() + offset, vec->size() - offset, offset) == -1) {
                        fprintf(stderr, "error writing, errnor=%d\n", errno);
                        result    = -1;
                    }
                }
                
                delete vec;
                close(fd);
                dispatch_semaphore_signal(sema);
            });
        });
	}
    
    dispatch_group_wait(group, DISPATCH_TIME_FOREVER);
    dispatch_release(group);
    dispatch_release(writer_queue);
    
    munmap(mapped_cache, statbuf.st_size);
	return result;
}



int dyld_shared_cache_extract_dylibs(const char* shared_cache_file_path, const char* extraction_root_path)
{
	return dyld_shared_cache_extract_dylibs_progress(shared_cache_file_path, extraction_root_path, 
													^(unsigned , unsigned) {} );
}


#if 0 
// test program
#include <stdio.h>
#include <stddef.h>
#include <dlfcn.h>


typedef int (*extractor_proc)(const char* shared_cache_file_path, const char* extraction_root_path,
													void (^progress)(unsigned current, unsigned total));

int main(int argc, const char* argv[])
{
	if ( argc != 3 ) {
		fprintf(stderr, "usage: dsc_extractor <path-to-cache-file> <path-to-device-dir>\n");
		return 1;
	}
	
	//void* handle = dlopen("/Volumes/my/src/dyld/build/Debug/dsc_extractor.bundle", RTLD_LAZY);
	void* handle = dlopen("/Applications/Xcode.app/Contents/Developer/Platforms/iPhoneOS.platform/usr/lib/dsc_extractor.bundle", RTLD_LAZY);
	if ( handle == NULL ) {
		fprintf(stderr, "dsc_extractor.bundle could not be loaded\n");
		return 1;
	}
	
	extractor_proc proc = (extractor_proc)dlsym(handle, "dyld_shared_cache_extract_dylibs_progress");
	if ( proc == NULL ) {
		fprintf(stderr, "dsc_extractor.bundle did not have dyld_shared_cache_extract_dylibs_progress symbol\n");
		return 1;
	}
	
	int result = (*proc)(argv[1], argv[2], ^(unsigned c, unsigned total) { printf("%d/%d\n", c, total); } );
	fprintf(stderr, "dyld_shared_cache_extract_dylibs_progress() => %d\n", result);
	return 0;
}


#endif

 
 

