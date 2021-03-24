Class {
	#name : #VMSpurOldSpaceTest,
	#superclass : #VMSpurInitializedOldSpaceTest,
	#category : #'VMMakerTests-MemoryTests'
}

{ #category : #'tests-2-allocation-basic' }
VMSpurOldSpaceTest >> testAllocateAllFreeMemoryShouldLeaveNoFreeMemory [

	memory gc allocateOldSpaceChunkOfBytes: memory gc totalFreeListBytes.
	
	self assert: memory gc totalFreeListBytes equals: 0
]

{ #category : #'tests-8-allocation-strategy-list-bestfit' }
VMSpurOldSpaceTest >> testAllocateBestFitInListShouldAddLeftoverInList [

	self createFreeChunkOfSize: 120.
	self createFreeChunkOfSize: 160.

	"Not exact, nor multiple of a power of 2"
	memory gc allocateOldSpaceChunkOfBytes: 96.

	self denyFreeListEmpty: (self freeListForSize: 24)
]

{ #category : #'tests-8-allocation-strategy-list-bestfit' }
VMSpurOldSpaceTest >> testAllocateBestFitInListShouldRemoveSmallerNodeFromLists [

	self createFreeChunkOfSize: 120.
	self createFreeChunkOfSize: 160.

	"Not exact, nor multiple of a power of 2"
	memory gc allocateOldSpaceChunkOfBytes: 96.

	self assertFreeListEmpty: (self freeListForSize: 120)
]

{ #category : #'tests-8-allocation-strategy-list-bestfit' }
VMSpurOldSpaceTest >> testAllocateBestFitInListShouldReuseSmallerAddress [

	| smallerAddress newAddress |
	smallerAddress := self createFreeChunkOfSize: 120.
	self createFreeChunkOfSize: 160.

	"Not exact, nor multiple of a power of 2"
	newAddress := memory gc allocateOldSpaceChunkOfBytes: 96.

	self assert: newAddress equals: smallerAddress
]

{ #category : #'tests-8-allocation-strategy-list-bestfit' }
VMSpurOldSpaceTest >> testAllocateBestFitInListShouldUseIgnoreBiggerChunk [

	self createFreeChunkOfSize: 120.
	self createFreeChunkOfSize: 160.

	"Not exact, nor multiple of a power of 2"
	memory gc allocateOldSpaceChunkOfBytes: 96.

	self denyFreeListEmpty: (self freeListForSize: 160)
]

{ #category : #'tests-2-allocation-basic' }
VMSpurOldSpaceTest >> testAllocateChunkOfMemoryShouldHaveSoMuchMemoryLessAfter [

	| someBytes freeBytesBefore |
	someBytes := 32.
	freeBytesBefore := memory gc totalFreeListBytes.
	memory gc allocateOldSpaceChunkOfBytes: someBytes.
	
	self assert: memory gc totalFreeListBytes equals: freeBytesBefore - someBytes
]

{ #category : #'tests-5-allocation-strategy' }
VMSpurOldSpaceTest >> testAllocateExactBiggerChunkShouldNotReuseSmallFreeChunk [

	| secondAddress newAddress |
	secondAddress := memory gc allocateOldSpaceChunkOfBytes: 160.
	memory gc freeChunkWithBytes: 160 at: secondAddress.

	newAddress := memory gc allocateOldSpaceChunkOfBytes: 240.
	self deny: newAddress equals: secondAddress
]

{ #category : #'tests-6-allocation-strategy-list-exact' }
VMSpurOldSpaceTest >> testAllocateExactFitInListShouldIgnoreBiggerChunks [

	self createFreeChunkOfSize: 160.
	self createFreeChunkOfSize: 200.

	memory gc allocateOldSpaceChunkOfBytes: 160.

	self assertFreeListEmpty: (self freeListForSize: 160).
	self denyFreeListEmpty: (self freeListForSize: 200)
]

{ #category : #'tests-6-allocation-strategy-list-exact' }
VMSpurOldSpaceTest >> testAllocateExactFitInListShouldRemoveNodeFromList [

	| secondAddress |
	secondAddress := memory gc allocateOldSpaceChunkOfBytes: 160.
	memory gc freeChunkWithBytes: 160 at: secondAddress.

	memory gc allocateOldSpaceChunkOfBytes: 160.
	self assert: (self freeListForSize: 160) equals: 0
]

{ #category : #'tests-6-allocation-strategy-list-exact' }
VMSpurOldSpaceTest >> testAllocateExactFitInListShouldReuseAddress [

	| secondAddress newAddress |
	secondAddress := self createFreeChunkOfSize: 160.

	newAddress := memory gc allocateOldSpaceChunkOfBytes: 160.
	self assert: newAddress equals: secondAddress
]

{ #category : #'tests-9-allocation-strategy-tree' }
VMSpurOldSpaceTest >> testAllocateExactFitTreeRootShouldRemoveRootFromTree [

	memory gc allocateOldSpaceChunkOfBytes: (memory bytesInObject: self freeTreeRootOop).

	self assert: self freeTreeRootOop equals: 0
]

{ #category : #'tests-9-allocation-strategy-tree' }
VMSpurOldSpaceTest >> testAllocateExactTreeRootShouldReuseRootAddress [

	| oldRootAddress newAddress |
	oldRootAddress := self freeTreeRootStartAddress.

	newAddress := memory gc allocateOldSpaceChunkOfBytes: (memory bytesInObject: self freeTreeRootOop).

	self assert: newAddress equals: oldRootAddress
]

{ #category : #'tests-4-free-tree' }
VMSpurOldSpaceTest >> testAllocateHalfOfTreeNodeShouldSplitIt [
	| size childAddress smallerChildOop largerChildOop aBitBiggerThanHalf |
	
	size := 1600.	"Big enough size to be in the tree"
	childAddress := memory gc allocateOldSpaceChunkOfBytes: size.
	memory gc freeChunkWithBytes: size at: childAddress.
	
	aBitBiggerThanHalf := size / 2 + 8.	"node a bit bigger than half"
	childAddress := memory gc allocateOldSpaceChunkOfBytes: aBitBiggerThanHalf.
	memory gc freeChunkWithBytes: aBitBiggerThanHalf at: childAddress.
	
	smallerChildOop := self smallerNodeOf: self freeTreeRootOop.
	self assert: (memory bytesInObject: smallerChildOop) equals: (size - aBitBiggerThanHalf).

	largerChildOop := self largerNodeOf: smallerChildOop.
	self assert: (memory bytesInObject: largerChildOop) equals: aBitBiggerThanHalf
]

{ #category : #'tests-4-free-tree' }
VMSpurOldSpaceTest >> testAllocateInFreeTreeShouldChangeRoot [

	| freeRootOopBeforeAllocation |
	freeRootOopBeforeAllocation := self freeTreeRootOop.
	
	memory gc allocateOldSpaceChunkOfBytes: 800 "Big enough to be in the tree".
	
	self deny: freeRootOopBeforeAllocation equals: self freeTreeRootOop
]

{ #category : #'tests-2-allocation-basic' }
VMSpurOldSpaceTest >> testAllocateManyChunksShouldKeepSingleFreeEntry [

	"Allocation should be contiguous because we have a single big chunk of memory to take memory from"
	memory gc allocateOldSpaceChunkOfBytes: 160.
	memory gc allocateOldSpaceChunkOfBytes: 160.
	memory gc allocateOldSpaceChunkOfBytes: 160.

	self assert: memory gc allFreeObjects size equals: 1
]

{ #category : #'tests-2-allocation-basic' }
VMSpurOldSpaceTest >> testAllocateMoreThanFreeMemoryShouldFailReturningNil [
	
	| address |
	address := memory gc allocateOldSpaceChunkOfBytes: memory gc totalFreeListBytes + 1.
	
	self assert: address isNil
]

{ #category : #'tests-9-allocation-strategy-tree' }
VMSpurOldSpaceTest >> testAllocatePartOfTreeRootShouldAddBigLeftOverAsFreeTreeRoot [

	| leftOverSize |
	leftOverSize := 64 * 8 "more than 63 slots".
	memory gc allocateOldSpaceChunkOfBytes: (memory gc totalFreeListBytes - leftOverSize).

	self assert: (memory bytesInObject: self freeTreeRootOop) equals: leftOverSize
]

{ #category : #'tests-9-allocation-strategy-tree' }
VMSpurOldSpaceTest >> testAllocatePartOfTreeRootShouldAddSmallLeftOverInFreeList [

	| leftOverSize |
	leftOverSize := 120.
	memory gc allocateOldSpaceChunkOfBytes: (memory gc totalFreeListBytes - leftOverSize).

	self denyFreeListEmpty: (self freeListForSize: leftOverSize)
]

{ #category : #'tests-9-allocation-strategy-tree' }
VMSpurOldSpaceTest >> testAllocatePartOfTreeRootShouldReuseRootAddress [

	| oldRootAddress newAddress |
	oldRootAddress := self freeTreeRootStartAddress.

	"At this point we can allocate whatever we want, only the tree has space, so we will take space from the tree anyways"
	self assert: 120 < (memory bytesInObject: self freeTreeRootOop).
	newAddress := memory gc allocateOldSpaceChunkOfBytes: 120.

	self assert: newAddress equals: oldRootAddress
]

{ #category : #'tests-7-allocation-strategy-list-power' }
VMSpurOldSpaceTest >> testAllocatePowerInListShouldAddLeftoverInList [

	| sizeToAllocate powerOfSizeToAllocate leftOverSize |
	sizeToAllocate := 80.
	powerOfSizeToAllocate := sizeToAllocate * (2 ** 2).
	leftOverSize := powerOfSizeToAllocate - sizeToAllocate.
	self createFreeChunkOfSize: powerOfSizeToAllocate.

	memory gc allocateOldSpaceChunkOfBytes: sizeToAllocate.
	self denyFreeListEmpty: (self freeListForSize: leftOverSize)
]

{ #category : #'tests-7-allocation-strategy-list-power' }
VMSpurOldSpaceTest >> testAllocatePowerInListShouldIgnoreNonPowers [

	| sizeToAllocate powerOfSizeToAllocate nonMultipleAddress newAddress |
	"bitSize * allocationUnit equals maxChunckSize in the freeList
	The freeList has bitsPerWords slots.
	Each slots contains a pointer (wordsize), which behaves as a linked list.
	Each linked list contains links free chunks of the same size.
	The nodeSize of each list equals index * allocationUnit.
	For example in 32 bits the free list will have 31 slots (1 for reserved for the tree).
	The last linked list is stored at index 31 (0 based) and will contain nodes of size 248 (index * 8)."
	sizeToAllocate := 10 * wordSize.
	powerOfSizeToAllocate := sizeToAllocate * (2 ** 2).
	
	nonMultipleAddress := self createFreeChunkOfSize: 120.
	
	self createFreeChunkOfSize: powerOfSizeToAllocate.
	
	newAddress := memory gc allocateOldSpaceChunkOfBytes: sizeToAllocate.
	self deny: newAddress equals: nonMultipleAddress.
]

{ #category : #'tests-7-allocation-strategy-list-power' }
VMSpurOldSpaceTest >> testAllocatePowerInListShouldRemoveNodeFromList [

	| sizeToAllocate powerOfSizeToAllocate |
	sizeToAllocate := 10 * wordSize.
	powerOfSizeToAllocate := sizeToAllocate * (2 ** 2).
	self createFreeChunkOfSize: powerOfSizeToAllocate.

	memory gc allocateOldSpaceChunkOfBytes: sizeToAllocate.
	self assertFreeListEmpty: (self freeListForSize: powerOfSizeToAllocate)
]

{ #category : #'tests-7-allocation-strategy-list-power' }
VMSpurOldSpaceTest >> testAllocatePowerInListShouldReuseMultipleAddress [

	| sizeToAllocate freeMultipleAddress newAddress powerOfSizeToAllocate |
	sizeToAllocate := 80.
	powerOfSizeToAllocate := sizeToAllocate * (2 ** 2).
	freeMultipleAddress := self createFreeChunkOfSize: powerOfSizeToAllocate.

	newAddress := memory gc allocateOldSpaceChunkOfBytes: sizeToAllocate.
	self assert: newAddress equals: freeMultipleAddress
]

{ #category : #'tests-5-allocation-strategy' }
VMSpurOldSpaceTest >> testAllocateSmallerChunkShouldReusePartiallyFreeChunk [

	| secondAddress newAddress |
	secondAddress := memory gc allocateOldSpaceChunkOfBytes: 160.
	memory gc freeChunkWithBytes: 160 at: secondAddress.

	newAddress := memory gc allocateOldSpaceChunkOfBytes: 80.
	self assert: newAddress equals: secondAddress
]

{ #category : #'tests-2-allocation-basic' }
VMSpurOldSpaceTest >> testAllocatedChunkAddressesShouldBeInAllocationOrder [

	| secondAddress thirdAddress |
	memory gc allocateOldSpaceChunkOfBytes: 160.
	secondAddress := memory gc allocateOldSpaceChunkOfBytes: 160.
	thirdAddress := memory gc allocateOldSpaceChunkOfBytes: 160.
	
	self assert: secondAddress < thirdAddress
]

{ #category : #'tests-2-allocation-basic' }
VMSpurOldSpaceTest >> testAllocatedChunkOfMemoryShouldRemoveSpaceFromFreeList [

	| freeChunkStartAddress allocatedSize |
	allocatedSize := 16.
	freeChunkStartAddress := self freeTreeRootStartAddress.
	memory gc allocateOldSpaceChunkOfBytes: allocatedSize.
	self
		assert: self freeTreeRootStartAddress
		equals: freeChunkStartAddress + allocatedSize
]

{ #category : #'tests-2-allocation-basic' }
VMSpurOldSpaceTest >> testAllocatedChunkOfMemoryShouldStartWhereFreeChunkStarted [

	| freeChunkStartAddressBeforeAllocation allocatedAddress |
	freeChunkStartAddressBeforeAllocation := self freeTreeRootStartAddress.
	allocatedAddress := memory gc allocateOldSpaceChunkOfBytes: 16.
	self
		assert: allocatedAddress
		equals: freeChunkStartAddressBeforeAllocation
]

{ #category : #'tests-4-free-tree' }
VMSpurOldSpaceTest >> testAllocationLargerThanFreeListLimitShouldUseFreeTree [

	| firstAddress byteSize smallerNodeOop |
	
	byteSize := memory gc numFreeLists * memory allocationUnit.
	firstAddress := memory gc allocateOldSpaceChunkOfBytes: byteSize.
	memory gc freeChunkWithBytes: byteSize at: firstAddress.
	
	smallerNodeOop := self smallerNodeOf: self freeTreeRootOop.
	self assert: smallerNodeOop equals: firstAddress
]

{ #category : #'tests-5-allocation-strategy' }
VMSpurOldSpaceTest >> testAllocationShouldNotLeaveFreeChunkSmallerThanLiliputian [

	| newAddress freeLargeSpaceAddressBeforeAllocation freeAddress |
	freeAddress := memory gc allocateOldSpaceChunkOfBytes: 32.
	memory gc freeChunkWithBytes: 32 at: freeAddress.

	"Allocating 24 bytes should not reuse the 32bytes free chunk because it will leave a free chunk < 16bytes (a liliputian)"	
	freeLargeSpaceAddressBeforeAllocation := self freeTreeRootStartAddress.
	newAddress := memory gc allocateOldSpaceChunkOfBytes: 24.

	self assert: newAddress equals: freeLargeSpaceAddressBeforeAllocation
]

{ #category : #'tests-5-allocation-strategy' }
VMSpurOldSpaceTest >> testChildNodeShouldHaveRootAsParent [

	| smallerChild freeTreeRoot parentNode |
	memory gc freeChunkWithBytes: 800 at: (memory gc allocateOldSpaceChunkOfBytes: 800).
	freeTreeRoot := memory gc freeLists at: 0.
	smallerChild := memory gc fetchPointer: memory gc freeChunkSmallerIndex ofFreeChunk: freeTreeRoot.
	
	parentNode := memory gc fetchPointer: memory gc freeChunkParentIndex ofFreeChunk: smallerChild.
	
	self assert: parentNode equals: freeTreeRoot
]

{ #category : #'tests-5-allocation-strategy' }
VMSpurOldSpaceTest >> testChildSiblingNodesInFreeTreeShouldHavePrevious [

	| freeTreeRoot size child1 child2 nextChildOop child3 siblingOop previousOop |
	size := 800.
	child1 := memory gc allocateOldSpaceChunkOfBytes: size.
	child2 := memory gc allocateOldSpaceChunkOfBytes: size.
	child3 := memory gc allocateOldSpaceChunkOfBytes: size.	
	memory gc freeChunkWithBytes: size at: child1.
	memory gc freeChunkWithBytes: size at: child2.
	memory gc freeChunkWithBytes: size at: child3.
		
	freeTreeRoot := memory gc freeLists at: 0.

	nextChildOop := memory gc fetchPointer: memory gc freeChunkSmallerIndex ofFreeChunk: freeTreeRoot.
	previousOop := memory gc fetchPointer: memory gc freeChunkPrevIndex ofFreeChunk: nextChildOop.
	self assert: previousOop equals: 0.
	
	siblingOop := memory gc fetchPointer: memory gc freeChunkNextIndex ofFreeChunk: nextChildOop.
	previousOop := memory gc fetchPointer: memory gc freeChunkPrevIndex ofFreeChunk: siblingOop.
	self assert: previousOop equals: nextChildOop.

	siblingOop := memory gc fetchPointer: memory gc freeChunkNextIndex ofFreeChunk: nextChildOop.
	previousOop := memory gc fetchPointer: memory gc freeChunkPrevIndex ofFreeChunk: siblingOop.
	self assert: previousOop equals: nextChildOop.
]

{ #category : #'tests-5-allocation-strategy' }
VMSpurOldSpaceTest >> testChildSiblingNodesInFreeTreeShouldNotHaveLarger [

	| freeTreeRoot size child1 child2 nextChildOop child3 largerOop largerThanSmaller siblingOop |
	size := 800.
	child1 := memory gc allocateOldSpaceChunkOfBytes: size.
	child2 := memory gc allocateOldSpaceChunkOfBytes: size.
	child3 := memory gc allocateOldSpaceChunkOfBytes: size.	

	"Create a smaller than smaller chunk to check that this is not propagated to smaller siblings"
	largerThanSmaller := memory gc allocateOldSpaceChunkOfBytes: 808.

	memory gc freeChunkWithBytes: size at: child1.
	memory gc freeChunkWithBytes: size at: child2.
	memory gc freeChunkWithBytes: size at: child3.
	memory gc freeChunkWithBytes: 808 at: largerThanSmaller.
		
	freeTreeRoot := memory gc freeLists at: 0.

	nextChildOop := memory gc fetchPointer: memory gc freeChunkSmallerIndex ofFreeChunk: freeTreeRoot.
	largerOop := memory gc fetchPointer: memory gc freeChunkLargerIndex ofFreeChunk: nextChildOop.
	self assert: (memory startOfObject: largerOop) equals: largerThanSmaller.
	
	siblingOop := memory gc fetchPointer: memory gc freeChunkNextIndex ofFreeChunk: nextChildOop.
	largerOop := memory gc fetchPointer: memory gc freeChunkLargerIndex ofFreeChunk: siblingOop.
	self assert: largerOop equals: 0.

	siblingOop := memory gc fetchPointer: memory gc freeChunkNextIndex ofFreeChunk: siblingOop.
	largerOop := memory gc fetchPointer: memory gc freeChunkLargerIndex ofFreeChunk: siblingOop.
	self assert: largerOop equals: 0.
]

{ #category : #'tests-5-allocation-strategy' }
VMSpurOldSpaceTest >> testChildSiblingNodesInFreeTreeShouldNotHaveParent [

	| freeTreeRoot size child1 child2 nextChild child3 parentOop |
	size := 800.
	child1 := memory gc allocateOldSpaceChunkOfBytes: size.
	child2 := memory gc allocateOldSpaceChunkOfBytes: size.
	child3 := memory gc allocateOldSpaceChunkOfBytes: size.
	memory gc freeChunkWithBytes: size at: child1.
	memory gc freeChunkWithBytes: size at: child2.
	memory gc freeChunkWithBytes: size at: child3.
		
	freeTreeRoot := memory gc freeLists at: 0.

	nextChild := memory gc fetchPointer: memory gc freeChunkSmallerIndex ofFreeChunk: freeTreeRoot.
	parentOop := memory gc fetchPointer: memory gc freeChunkParentIndex ofFreeChunk: nextChild.
	self assert: parentOop equals: freeTreeRoot.
	
	nextChild := memory gc fetchPointer: memory gc freeChunkNextIndex ofFreeChunk: nextChild.
	parentOop := memory gc fetchPointer: memory gc freeChunkParentIndex ofFreeChunk: nextChild.
	self assert: parentOop equals: 0.

	nextChild := memory gc fetchPointer: memory gc freeChunkNextIndex ofFreeChunk: nextChild.
	parentOop := memory gc fetchPointer: memory gc freeChunkParentIndex ofFreeChunk: nextChild.
	self assert: parentOop equals: 0.
]

{ #category : #'tests-5-allocation-strategy' }
VMSpurOldSpaceTest >> testChildSiblingNodesInFreeTreeShouldNotHaveSmaller [

	| freeTreeRoot size child1 child2 nextChildOop child3 smallerOop smallerThanSmaller siblingOop |
	size := 800.
	child1 := memory gc allocateOldSpaceChunkOfBytes: size.
	child2 := memory gc allocateOldSpaceChunkOfBytes: size.
	child3 := memory gc allocateOldSpaceChunkOfBytes: size.	

	"Create a smaller than smaller chunk to check that this is not propagated to smaller siblings"
	smallerThanSmaller := memory gc allocateOldSpaceChunkOfBytes: 792.

	memory gc freeChunkWithBytes: size at: child1.
	memory gc freeChunkWithBytes: size at: child2.
	memory gc freeChunkWithBytes: size at: child3.
	memory gc freeChunkWithBytes: 792 at: smallerThanSmaller.
		
	freeTreeRoot := memory gc freeLists at: 0.

	nextChildOop := memory gc fetchPointer: memory gc freeChunkSmallerIndex ofFreeChunk: freeTreeRoot.
	smallerOop := memory gc fetchPointer: memory gc freeChunkSmallerIndex ofFreeChunk: nextChildOop.
	self assert: (memory startOfObject: smallerOop) equals: smallerThanSmaller.
	
	siblingOop := memory gc fetchPointer: memory gc freeChunkNextIndex ofFreeChunk: nextChildOop.
	smallerOop := memory gc fetchPointer: memory gc freeChunkSmallerIndex ofFreeChunk: siblingOop.
	self assert: smallerOop equals: 0.

	siblingOop := memory gc fetchPointer: memory gc freeChunkNextIndex ofFreeChunk: siblingOop.
	smallerOop := memory gc fetchPointer: memory gc freeChunkSmallerIndex ofFreeChunk: siblingOop.
	self assert: smallerOop equals: 0.
]

{ #category : #'tests-5-allocation-strategy' }
VMSpurOldSpaceTest >> testDeallocateShouldNotChangeRoot [

	| freeRoot address |	
	address := memory gc allocateOldSpaceChunkOfBytes: 800.

	freeRoot := memory gc freeLists at: 0.
	memory gc freeChunkWithBytes: 800 at: address.
	
	self assert: freeRoot equals: (memory gc freeLists at: 0)
]

{ #category : #'tests-5-allocation-strategy' }
VMSpurOldSpaceTest >> testEqualSizeChildNodeInFreeTreeShouldBeInsertedAfterHead [

	| smallerChild freeTreeRoot size child1 child2 nextChild child3 |
	size := 800.
	child1 := memory gc allocateOldSpaceChunkOfBytes: size.
	child2 := memory gc allocateOldSpaceChunkOfBytes: size.
	child3 := memory gc allocateOldSpaceChunkOfBytes: size.
	memory gc freeChunkWithBytes: size at: child1.
	memory gc freeChunkWithBytes: size at: child2.
	memory gc freeChunkWithBytes: size at: child3.
		
	freeTreeRoot := memory gc freeLists at: 0.
	smallerChild := memory gc fetchPointer: memory gc freeChunkSmallerIndex ofFreeChunk: freeTreeRoot.
	
	self assert: smallerChild equals: child1.
	nextChild := memory gc fetchPointer: memory gc freeChunkNextIndex ofFreeChunk: child1.
	self assert: nextChild equals: child3.
	nextChild := memory gc fetchPointer: memory gc freeChunkNextIndex ofFreeChunk: child3.
	self assert: nextChild equals: child2.
]

{ #category : #'tests-5-allocation-strategy' }
VMSpurOldSpaceTest >> testEqualSizeChildNodeShouldBeNextNode [

	| smallerChild freeTreeRoot size child1 child2 nextChild |
	size := 800.
	child1 := memory gc allocateOldSpaceChunkOfBytes: size.
	child2 := memory gc allocateOldSpaceChunkOfBytes: size.
	memory gc freeChunkWithBytes: size at: child1.
	memory gc freeChunkWithBytes: size at: child2.
		
	freeTreeRoot := memory gc freeLists at: 0.
	smallerChild := memory gc fetchPointer: memory gc freeChunkSmallerIndex ofFreeChunk: freeTreeRoot.
	
	self assert: smallerChild equals: child1.
	nextChild := memory gc fetchPointer: memory gc freeChunkNextIndex ofFreeChunk: child1.
	self assert: nextChild equals: child2.
]

{ #category : #'tests-3-free-lists' }
VMSpurOldSpaceTest >> testFreeAChunkShouldBePutAsHeadOfFreeList [
	| firstAddress secondAddress freeListHead chunkSize |
	chunkSize := 32.

	firstAddress := memory gc allocateOldSpaceChunkOfBytes: chunkSize.
	secondAddress := memory gc allocateOldSpaceChunkOfBytes: chunkSize.
	memory gc freeChunkWithBytes: chunkSize at: firstAddress.
	memory gc freeChunkWithBytes: chunkSize at: secondAddress.
	
	freeListHead := self freeListForSize: chunkSize.
	self assert: freeListHead equals: secondAddress
]

{ #category : #'tests-2-allocation-basic' }
VMSpurOldSpaceTest >> testFreeChunkDoesNotGetMergedWithExistingFreeChunks [

	| secondAddress |
	secondAddress := memory gc allocateOldSpaceChunkOfBytes: 160.
	memory gc freeChunkWithBytes: 160 at: secondAddress.

	self assert: memory gc allFreeObjects size equals: 2
]

{ #category : #'tests-3-free-lists' }
VMSpurOldSpaceTest >> testFreeChunkShouldKnowNextChunkOfSameSize [
	| firstAddress secondAddress freeListHead nextFreeChunk allocationSize |
	allocationSize := 32.
	
	firstAddress := memory gc allocateOldSpaceChunkOfBytes: allocationSize.
	secondAddress := memory gc allocateOldSpaceChunkOfBytes: allocationSize.
	memory gc freeChunkWithBytes: allocationSize at: firstAddress.
	memory gc freeChunkWithBytes: allocationSize at: secondAddress.
	
	freeListHead := self freeListForSize: allocationSize.
	nextFreeChunk := self nextNodeOf: freeListHead.

	self assert: nextFreeChunk equals: firstAddress
]

{ #category : #'tests-3-free-lists' }
VMSpurOldSpaceTest >> testFreeChunkShouldKnowPreviousChunkOfSameSize [
	| firstAddress secondAddress freeListHead nextFreeChunk allocationSize previousFreeChunk |
	allocationSize := 32.
	
	firstAddress := memory gc allocateOldSpaceChunkOfBytes: allocationSize.
	secondAddress := memory gc allocateOldSpaceChunkOfBytes: allocationSize.
	memory gc freeChunkWithBytes: allocationSize at: firstAddress.
	memory gc freeChunkWithBytes: allocationSize at: secondAddress.
	
	freeListHead := self freeListForSize: allocationSize.
	nextFreeChunk := self nextNodeOf: freeListHead.

	previousFreeChunk := self previousNodeOf: nextFreeChunk.
	self assert: previousFreeChunk equals: freeListHead
]

{ #category : #'tests-2-allocation-basic' }
VMSpurOldSpaceTest >> testFreeChunksWithSameSizeShouldBeListedAsDifferentFreeChunks [

	| secondAddress newAddress |
	secondAddress := memory gc allocateOldSpaceChunkOfBytes: 160.
	memory gc freeChunkWithBytes: 160 at: secondAddress.
	newAddress := memory gc allocateOldSpaceChunkOfBytes: 80.
	memory gc freeChunkWithBytes: 80 at: newAddress.
	
	self assert: memory gc allFreeObjects size equals: 3
]

{ #category : #'tests-3-free-lists' }
VMSpurOldSpaceTest >> testFreeChunksWithSameSizeShouldShareSingleHead [
	| secondAddress allocationSize firstAddress |
	allocationSize := 32.
	
	firstAddress := memory gc allocateOldSpaceChunkOfBytes: allocationSize.
	secondAddress := memory gc allocateOldSpaceChunkOfBytes: allocationSize.
	memory gc freeChunkWithBytes: allocationSize at: firstAddress.
	memory gc freeChunkWithBytes: allocationSize at: secondAddress.
	
	self assert: memory gc allFreeListHeads size equals: 1
]

{ #category : #'tests-3-free-lists' }
VMSpurOldSpaceTest >> testFreeListsShouldBeIndexedBySlotSize [

	| firstAddress freeListHead |
	
	2 to: memory gc numFreeLists - 1 do: [ :numberOfSlots | | byteSize |
		byteSize := numberOfSlots * memory allocationUnit.
		
		firstAddress := memory gc allocateOldSpaceChunkOfBytes: byteSize.
		memory gc freeChunkWithBytes: byteSize at: firstAddress.
	
		freeListHead := memory gc freeLists at: numberOfSlots.
		self assert: freeListHead equals: firstAddress
	]
]

{ #category : #'tests-1-startup' }
VMSpurOldSpaceTest >> testInitialFreeListShouldBeEmpty [

	2 to: memory gc numFreeLists - 1 do: [ :numberOfSlots |
		self
			assert: (memory gc freeLists at: numberOfSlots)
			equals: 0
	]
]

{ #category : #'tests-1-startup' }
VMSpurOldSpaceTest >> testInitialFreeTreeRootHasNoLargerNode [

	| bigChunk nextNode |
	bigChunk := self freeTreeRootOop.
	nextNode := self largerNodeOf: bigChunk.

	self assert: nextNode equals: 0.
]

{ #category : #'tests-1-startup' }
VMSpurOldSpaceTest >> testInitialFreeTreeRootHasNoNextNode [

	| bigChunk nextNode |
	bigChunk := self freeTreeRootOop.
	nextNode := self nextNodeOf: bigChunk.

	self assert: nextNode equals: 0.
]

{ #category : #'tests-1-startup' }
VMSpurOldSpaceTest >> testInitialFreeTreeRootHasNoParentNode [

	| bigChunk nextNode |
	bigChunk := self freeTreeRootOop.
	nextNode := self parentNodeOf: bigChunk.

	self assert: nextNode equals: 0.
]

{ #category : #'tests-1-startup' }
VMSpurOldSpaceTest >> testInitialFreeTreeRootHasNoPreviousNode [

	| bigChunk nextNode |
	bigChunk := self freeTreeRootOop.
	nextNode := self previousNodeOf: bigChunk.

	self assert: nextNode equals: 0.
]

{ #category : #'tests-1-startup' }
VMSpurOldSpaceTest >> testInitialFreeTreeRootHasNoSmallerNode [

	| bigChunk nextNode |
	bigChunk := self freeTreeRootOop.
	nextNode := self smallerNodeOf: bigChunk.

	self assert: nextNode equals: 0.
]

{ #category : #'tests-1-startup' }
VMSpurOldSpaceTest >> testInitialFreeTreeRootIsFreeObject [

	self assert: (memory gc isFreeObject: self freeTreeRootOop)
]

{ #category : #'tests-1-startup' }
VMSpurOldSpaceTest >> testInitialFreeTreeRootSizeShouldBeTotalFreeSpace [

	self
		assert: (memory bytesInObject: self freeTreeRootOop)
		equals: memory gc totalFreeListBytes
]

{ #category : #'tests-4-free-tree' }
VMSpurOldSpaceTest >> testLargeFreeChunkInFreeTreeNodeShouldStoreChunkOop [

	| firstAddress byteSize smallerNodeOop |
	
	byteSize := 256 "large chunk min size" * memory allocationUnit.
	firstAddress := memory gc allocateOldSpaceChunkOfBytes: byteSize.
	memory gc freeChunkWithBytes: byteSize at: firstAddress.
	
	smallerNodeOop := self smallerNodeOf: self freeTreeRootOop.
	self assert: (memory startOfObject: smallerNodeOop) equals: firstAddress
]

{ #category : #'tests-5-allocation-strategy' }
VMSpurOldSpaceTest >> testNewBigFreeChunkShouldBeFreeTreeChild [

	| firstAddress freeRoot rootSize moreThanHalf newRoot largerChildOop |
	freeRoot := memory gc freeLists at: 0.
	rootSize := memory bytesInObject: freeRoot.
	
	moreThanHalf := ((rootSize / memory allocationUnit) / 2) ceiling + 1 * memory allocationUnit.
	
	"Create a free chunk of more than half of the root, the root has changed"
	firstAddress := memory gc allocateOldSpaceChunkOfBytes: moreThanHalf.
	memory gc freeChunkWithBytes: moreThanHalf at: firstAddress.
	newRoot := memory gc freeLists at: 0.

	"Nodes in the free tree are organized as oops. Each oop points to the base header of the object"
	largerChildOop := memory gc fetchPointer: memory gc freeChunkLargerIndex ofFreeChunk: newRoot.
	"instead, the address returned by allocateOldSpaceChunkOfBytes: returns always an address, not an oop."
	"To get the real address where the oop starts use #startOfObject:"
	self assert: (memory startOfObject: largerChildOop) equals: firstAddress
]

{ #category : #'tests-5-allocation-strategy' }
VMSpurOldSpaceTest >> testNewBigFreeChunkShouldHaveRootAsParent [

	| firstAddress freeRoot rootSize moreThanHalf newRoot largerChildOop parentNodeOop |
	freeRoot := memory gc freeLists at: 0.
	rootSize := memory bytesInObject: freeRoot.
	
	moreThanHalf := ((rootSize / memory allocationUnit) / 2) ceiling + 1 * memory allocationUnit.
	self assert: moreThanHalf > (rootSize / 2).
	
	"Create a free chunk of more than half of the root, the root has changed"
	firstAddress := memory gc allocateOldSpaceChunkOfBytes: moreThanHalf.
	memory gc freeChunkWithBytes: moreThanHalf at: firstAddress.
	newRoot := memory gc freeLists at: 0.

	"Nodes in the free tree are organized as oops. Each oop points to the base header of the object"
	largerChildOop := memory gc fetchPointer: memory gc freeChunkLargerIndex ofFreeChunk: newRoot.
	parentNodeOop := memory gc fetchPointer: memory gc freeChunkParentIndex ofFreeChunk: largerChildOop.
	
	self assert: parentNodeOop equals: newRoot
]

{ #category : #'tests-1-startup' }
VMSpurOldSpaceTest >> testNewMemoryShouldHaveSingleFreeObject [

	self assert: memory gc allFreeObjects size equals: 1
]

{ #category : #'tests-2-allocation-basic' }
VMSpurOldSpaceTest >> testNewObjectShouldBeOld [
	
	| oop |
	oop := memory allocateSlotsInOldSpace: 0 format: 0 classIndex: self zeroSizedObjectClassIndex.
	
	self assert: (memory gc isOldObject: oop)
]

{ #category : #'tests-2-allocation-basic' }
VMSpurOldSpaceTest >> testPartiallyReusingFreeChunkShouldKeepNumberOfEntriesInFreeList [

	| secondAddress freeChunksBefore |
	secondAddress := memory gc allocateOldSpaceChunkOfBytes: 160.

	memory gc freeChunkWithBytes: 160 at: secondAddress.
	freeChunksBefore := memory gc allFreeObjects size.
	memory gc allocateOldSpaceChunkOfBytes: 80.
	
	self assert: memory gc allFreeObjects size equals: freeChunksBefore.
]

{ #category : #'tests-2-allocation-basic' }
VMSpurOldSpaceTest >> testReuseFreeChunkShouldRemoveEntryFromFreeList [

	| secondAddress |
	secondAddress := memory gc allocateOldSpaceChunkOfBytes: 160.
	memory gc freeChunkWithBytes: 160 at: secondAddress.
	memory gc allocateOldSpaceChunkOfBytes: 160.
	
	self assert: memory gc allFreeObjects size equals: 1
]

{ #category : #'tests-3-free-lists' }
VMSpurOldSpaceTest >> testSingleFreeChunkListNextShouldBeZero [
	| firstAddress freeListHead allocationSize |
	allocationSize := 32.

	firstAddress := memory gc allocateOldSpaceChunkOfBytes: allocationSize.
	memory gc freeChunkWithBytes: allocationSize at: firstAddress.

	freeListHead := self freeListForSize: allocationSize.
	self assert: (self nextNodeOf: freeListHead) equals: 0
]

{ #category : #'tests-3-free-lists' }
VMSpurOldSpaceTest >> testSingleFreeChunkListPreviousShouldBeZero [
	| firstAddress freeListHead allocationSize |
	allocationSize := 32.

	firstAddress := memory gc allocateOldSpaceChunkOfBytes: allocationSize.
	memory gc freeChunkWithBytes: allocationSize at: firstAddress.

	freeListHead := self freeListForSize: allocationSize.
	self assert: (self previousNodeOf: freeListHead) equals: 0
]

{ #category : #'tests-5-allocation-strategy' }
VMSpurOldSpaceTest >> testSmallerChildNodeShouldBeFreeTreeChild [

	| smallerChild freeTreeRoot parentNode smallerSize rootSize |
	smallerSize := 800.
	rootSize := memory bytesInObject: (memory gc freeLists at: 0).
	self assert: smallerSize < (rootSize / 2).

	memory gc freeChunkWithBytes: smallerSize at: (memory gc allocateOldSpaceChunkOfBytes: smallerSize).
	freeTreeRoot := memory gc freeLists at: 0.
	smallerChild := memory gc fetchPointer: memory gc freeChunkSmallerIndex ofFreeChunk: freeTreeRoot.
	
	parentNode := memory gc fetchPointer: memory gc freeChunkParentIndex ofFreeChunk: smallerChild.
	
	self assert: parentNode equals: freeTreeRoot
]
