Class {
	#name : #VMSpurOldSpaceBootstrapTest,
	#superclass : #VMSpurMemoryManagerTest,
	#category : #'VMMakerTests-MemoryTests'
}

{ #category : #'tests-memory-bootstrap' }
VMSpurOldSpaceBootstrapTest >> testClassTableHasTablePagesAndHiddenRoots [

	| tableRoot |
	memory nilObject: self newZeroSizedObject.
	"Initialize old space with free list, class table, hidden roots and remembered set to be able to scavenge"
	memory gc initializeFreeList.
	memory segmentManager collapseSegmentsPostSwizzle.
	memory gc updateFreeLists.
	memory gc computeFreeSpacePostSwizzle.
	memory gc initializeOldSpaceFirstFree: memory gc freeOldSpaceStart.

	tableRoot := memory allocateClassTable.
	
	self
		assert: (memory numSlotsOf: tableRoot)
		equals: memory classTableRootSlots + memory hiddenRootSlots
]

{ #category : #'tests-memory-bootstrap' }
VMSpurOldSpaceBootstrapTest >> testFreeListHasAsManySlotsAsRequiredByTheVM [

	| freeListOop |
	freeListOop := memory gc initializeFreeList.

	self assert: (memory numSlotsOf: freeListOop) equals: memory gc numFreeLists
]

{ #category : #'tests-memory-bootstrap' }
VMSpurOldSpaceBootstrapTest >> testFreeListIsWordIndexable [

	| freeListOop |
	freeListOop := memory gc initializeFreeList.

	self assert: (memory formatOf: freeListOop) equals: memory wordIndexableFormat
]

{ #category : #'tests-memory-bootstrap' }
VMSpurOldSpaceBootstrapTest >> testNewFreeListHasAllSlotsInitializedInZero [

	| freeListOop |
	freeListOop := memory gc initializeFreeList.

	0 to: memory gc numFreeLists - 1 do: [ :i |
		self assert: (memory fetchPointer: i ofObject: freeListOop) equals: 0 ]
]

{ #category : #'tests-memory-bootstrap' }
VMSpurOldSpaceBootstrapTest >> testNewFreeListIsValid [

	memory gc initializeFreeList.
	memory gc validFreeTree
]

{ #category : #'tests-memory-bootstrap' }
VMSpurOldSpaceBootstrapTest >> testNewFreeListIsValid2 [

	memory gc initializeFreeList.
	memory gc totalFreeListBytes
]
