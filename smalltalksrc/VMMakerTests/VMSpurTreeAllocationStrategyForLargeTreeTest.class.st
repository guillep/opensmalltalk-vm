Class {
	#name : #VMSpurTreeAllocationStrategyForLargeTreeTest,
	#superclass : #VMSpurTreeAllocationStrategyForSmallTreeTest,
	#category : #'VMMakerTests-MemoryTests'
}

{ #category : #'tests-10-bestfit-liliputian-leftovers' }
VMSpurTreeAllocationStrategyForLargeTreeTest class >> shouldInheritSelectors [

	^ true
]

{ #category : #running }
VMSpurTreeAllocationStrategyForLargeTreeTest >> setUpTree [

	"          1120
	          /    \
	      1056     1184
	      /   \    /   \
	  1024  1088  1152  1216
	"
	| parent childNumber |
	
	chunkAddresses := Dictionary new.
	1024 to: 1216 by: 32 do: [ :size |
		chunkAddresses at: size put: (memory gc allocateOldSpaceChunkOfBytes: size)
	].
	"Allocate the rest of the memory so it does not bother our test."
	memory gc allocateOldSpaceChunkOfBytes: memory gc totalFreeListBytes.

	sizesInBreadthFirstOrder := #( 1120 1056 1184 1024 1088 1152 1216 ).
	sizesInBreadthFirstOrder do: [ :e |
		memory gc freeChunkWithBytes: e at: (chunkAddresses at: e) ].
	
	
	parent := self freeTreeRootOop.
	
	"check that the structure of the tree is as expected"
	childNumber := 1.
	self assert: (memory bytesInObject: parent) equals: (sizesInBreadthFirstOrder at: childNumber).
	self assert: (memory bytesInObject: (self smallerNodeOf: parent)) equals: (sizesInBreadthFirstOrder at: childNumber * 2).
	self assert: (memory bytesInObject: (self largerNodeOf: parent)) equals: (sizesInBreadthFirstOrder at: childNumber * 2 + 1).
	
	parent := self smallerNodeOf: self freeTreeRootOop.
	childNumber := 2.
	self assert: (memory bytesInObject: (self smallerNodeOf: parent)) equals: (sizesInBreadthFirstOrder at: childNumber * 2).
	self assert: (memory bytesInObject: (self largerNodeOf: parent)) equals: (sizesInBreadthFirstOrder at: childNumber * 2 + 1).
	
	parent := self largerNodeOf: self freeTreeRootOop.
	childNumber := 3.
	self assert: (memory bytesInObject: (self smallerNodeOf: parent)) equals: (sizesInBreadthFirstOrder at: childNumber * 2).
	self assert: (memory bytesInObject: (self largerNodeOf: parent)) equals: (sizesInBreadthFirstOrder at: childNumber * 2 + 1).
]

{ #category : #'tests-10-bestfit-liliputian-leftovers' }
VMSpurTreeAllocationStrategyForLargeTreeTest >> test01AllocateBestFitTreeRootWithChildrenShouldReplaceNodeWithSmaller [

	memory gc allocateOldSpaceChunkOfBytes: (self sizeOfChildInBreadthFirstOrder: 1) - 16.
	
	self assert: (memory bytesInObject: self freeTreeRootOop) equals: (self sizeOfChildInBreadthFirstOrder: 2)
]

{ #category : #'tests-10-bestfit-liliputian-leftovers' }
VMSpurTreeAllocationStrategyForLargeTreeTest >> test02AllocateBestFitTreeRootWithChildrenShouldReInsertSmallerLargerChildFromRoot [

	memory gc allocateOldSpaceChunkOfBytes: (self sizeOfChildInBreadthFirstOrder: 1) - 16.

	self assert: (memory bytesInObject: (self largerNodeOf: self freeTreeRootOop)) equals: (self sizeOfChildInBreadthFirstOrder: 5)
]

{ #category : #'tests-10-bestfit-liliputian-leftovers' }
VMSpurTreeAllocationStrategyForLargeTreeTest >> test03AllocateBestFitTreeRootWithChildrenShouldReplaceSmallerChildWithSmallerSmaller [

	memory gc allocateOldSpaceChunkOfBytes: (self sizeOfChildInBreadthFirstOrder: 1) - 16.
	
	self assert: (memory bytesInObject: (self smallerNodeOf: self freeTreeRootOop)) equals: (self sizeOfChildInBreadthFirstOrder: 4)
]

{ #category : #'tests-10-bestfit-liliputian-leftovers' }
VMSpurTreeAllocationStrategyForLargeTreeTest >> test04AllocateBestFitTreeRootWithChildrenShouldInsertLiliputianInFreeList [

	memory gc allocateOldSpaceChunkOfBytes: (self sizeOfChildInBreadthFirstOrder: 1) - 16.
	
	self denyFreeListEmpty: (self freeListForSize: 16)
]

{ #category : #'tests-10-bestfit-liliputian-leftovers' }
VMSpurTreeAllocationStrategyForLargeTreeTest >> test05AllocateBestFitSmallerTreeNodeShouldReplaceNodeWithSmaller [

	memory gc allocateOldSpaceChunkOfBytes: (self sizeOfChildInBreadthFirstOrder: 2) - 16.

	self assert: (memory bytesInObject: (self smallerNodeOf: self freeTreeRootOop)) equals: (self sizeOfChildInBreadthFirstOrder: 4)
]

{ #category : #'tests-10-bestfit-liliputian-leftovers' }
VMSpurTreeAllocationStrategyForLargeTreeTest >> test06AllocateBestFitSmallerTreeNodeShouldReuseNodeAddress [

	| desiredAddress allocatedAddress |
	desiredAddress := memory startOfObject: (self smallerNodeOf: self freeTreeRootOop).
	
	allocatedAddress := memory gc allocateOldSpaceChunkOfBytes: (self sizeOfChildInBreadthFirstOrder: 2) - 16.
	self assert: allocatedAddress equals: desiredAddress
]

{ #category : #'tests-10-bestfit-liliputian-leftovers' }
VMSpurTreeAllocationStrategyForLargeTreeTest >> test07AllocateBestFitSmallerTreeNodeShouldInsertLiliputianInFreeList [

	memory gc allocateOldSpaceChunkOfBytes: (self sizeOfChildInBreadthFirstOrder: 2) - 16.
	
	self denyFreeListEmpty: (self freeListForSize: 16)
]

{ #category : #'tests-10-bestfit-liliputian-leftovers' }
VMSpurTreeAllocationStrategyForLargeTreeTest >> test15AllocateBestFitBiggerTreeNodeShouldReplaceNodeWithSmaller [

	memory gc allocateOldSpaceChunkOfBytes: (self sizeOfChildInBreadthFirstOrder: 3) - 16.
	
	self assert: (memory bytesInObject: (self largerNodeOf: self freeTreeRootOop)) equals: (self sizeOfChildInBreadthFirstOrder: 6)
]

{ #category : #'tests-10-bestfit-liliputian-leftovers' }
VMSpurTreeAllocationStrategyForLargeTreeTest >> test16AllocateBestFitBiggerTreeNodeShouldReuseNodeAddress [

	| desiredAddress allocatedAddress |
	desiredAddress := memory startOfObject: (self largerNodeOf: self freeTreeRootOop).
	
	allocatedAddress := memory gc allocateOldSpaceChunkOfBytes: (self sizeOfChildInBreadthFirstOrder: 3)  - 16.
	self assert: allocatedAddress equals: desiredAddress
]

{ #category : #'tests-10-bestfit-liliputian-leftovers' }
VMSpurTreeAllocationStrategyForLargeTreeTest >> test17AllocateBestFitLargerTreeNodeShouldInsertLiliputianInFreeList [

	memory gc allocateOldSpaceChunkOfBytes: (self sizeOfChildInBreadthFirstOrder: 3) - 16.
	
	self denyFreeListEmpty: (self freeListForSize: 16)
]

{ #category : #'tests-10-bestfit-liliputian-leftovers' }
VMSpurTreeAllocationStrategyForLargeTreeTest >> test20AllocateBestFitSmallerOfSmallerLeafTreeNodeShouldRemoveNode [

	memory gc allocateOldSpaceChunkOfBytes: (self sizeOfChildInBreadthFirstOrder: 4) - 16.

	self assert: (self smallerNodeOf: (self smallerNodeOf: self freeTreeRootOop)) equals: 0
]

{ #category : #'tests-10-bestfit-liliputian-leftovers' }
VMSpurTreeAllocationStrategyForLargeTreeTest >> test21AllocateBestFitSmallerOfSmallerLeafTreeNodeShouldReuseNodeAddress [

	| desiredAddress allocatedAddress |
	desiredAddress := self smallerNodeOf: (self smallerNodeOf: self freeTreeRootOop).
	
	allocatedAddress := memory gc allocateOldSpaceChunkOfBytes: (self sizeOfChildInBreadthFirstOrder: 4) - 16.
	self assert: allocatedAddress equals: desiredAddress
]

{ #category : #'tests-10-bestfit-liliputian-leftovers' }
VMSpurTreeAllocationStrategyForLargeTreeTest >> test22AllocateBestFitSmallerOfSmallerLeafTreeNodeShouldInsertLiliputianInFreeList [

	memory gc allocateOldSpaceChunkOfBytes: (self sizeOfChildInBreadthFirstOrder: 4) - 16.
	
	self denyFreeListEmpty: (self freeListForSize: 16)
]

{ #category : #'tests-10-bestfit-liliputian-leftovers' }
VMSpurTreeAllocationStrategyForLargeTreeTest >> test25AllocateBestFitLargerOfSmallerLeafTreeNodeShouldRemoveNode [

	memory gc allocateOldSpaceChunkOfBytes: (self sizeOfChildInBreadthFirstOrder: 5) - 16.
	
	self assert: (self largerNodeOf: (self smallerNodeOf: self freeTreeRootOop)) equals: 0
]

{ #category : #'tests-10-bestfit-liliputian-leftovers' }
VMSpurTreeAllocationStrategyForLargeTreeTest >> test26AllocateBestFitLargerOfSmallerLeafTreeNodeShouldReuseNodeAddress [

	| desiredAddress allocatedAddress |
	desiredAddress := memory startOfObject: (self largerNodeOf: (self smallerNodeOf: self freeTreeRootOop)).
	allocatedAddress := memory gc allocateOldSpaceChunkOfBytes: (self sizeOfChildInBreadthFirstOrder: 5) - 16.
	self assert: allocatedAddress equals: desiredAddress
]

{ #category : #'tests-10-bestfit-liliputian-leftovers' }
VMSpurTreeAllocationStrategyForLargeTreeTest >> test27AllocateBestFitLargerOfSmallerLeafTreeNodeShouldShouldInsertLiliputianInFreeList [

	memory gc allocateOldSpaceChunkOfBytes: (self sizeOfChildInBreadthFirstOrder: 5) - 16.
	
	self denyFreeListEmpty: (self freeListForSize: 16)
]

{ #category : #'tests-10-bestfit-liliputian-leftovers' }
VMSpurTreeAllocationStrategyForLargeTreeTest >> test30AllocateBestFitSmallerOfLargerLeafTreeNodeShouldRemoveNode [

	memory gc allocateOldSpaceChunkOfBytes: (self sizeOfChildInBreadthFirstOrder: 6) - 16.

	self assert: (self smallerNodeOf: (self largerNodeOf: self freeTreeRootOop)) equals: 0
]

{ #category : #'tests-10-bestfit-liliputian-leftovers' }
VMSpurTreeAllocationStrategyForLargeTreeTest >> test31AllocateBestFitSmallerOfLargerLeafTreeNodeShouldReuseNodeAddress [

	| desiredAddress allocatedAddress |
	desiredAddress := memory startOfObject: (self smallerNodeOf: (self largerNodeOf: self freeTreeRootOop)).
	
	allocatedAddress := memory gc allocateOldSpaceChunkOfBytes: (self sizeOfChildInBreadthFirstOrder: 6) - 16.
	self assert: allocatedAddress equals: desiredAddress
]

{ #category : #'tests-10-bestfit-liliputian-leftovers' }
VMSpurTreeAllocationStrategyForLargeTreeTest >> test32AllocateBestFitSmallerOfLargerLeafTreeNodeShouldInsertLiliputianInFreeList [

	memory gc allocateOldSpaceChunkOfBytes: (self sizeOfChildInBreadthFirstOrder: 6) - 16.

	self denyFreeListEmpty: (self freeListForSize: 16)
]

{ #category : #'tests-10-bestfit-liliputian-leftovers' }
VMSpurTreeAllocationStrategyForLargeTreeTest >> test35AllocateBestFitLargerOfLargerLeafTreeNodeShouldRemoveChildNode [

	memory gc allocateOldSpaceChunkOfBytes: (self sizeOfChildInBreadthFirstOrder: 7) - 16.

	self assert: (self largerNodeOf: (self largerNodeOf: self freeTreeRootOop)) equals: 0
]

{ #category : #'tests-10-bestfit-liliputian-leftovers' }
VMSpurTreeAllocationStrategyForLargeTreeTest >> test36AllocateBestFitLargerOfLargerLeafTreeNodeShouldReuseNodeAddress [

	| desiredAddress allocatedAddress |
	desiredAddress := memory startOfObject: (self largerNodeOf: (self largerNodeOf: self freeTreeRootOop)).
	
	allocatedAddress := memory gc allocateOldSpaceChunkOfBytes: (self sizeOfChildInBreadthFirstOrder: 7) - 16.
	self assert: allocatedAddress equals: desiredAddress
]

{ #category : #'tests-10-bestfit-liliputian-leftovers' }
VMSpurTreeAllocationStrategyForLargeTreeTest >> test37AllocateBestFitLargerOfLargerLeafTreeNodeShouldInsertLiliputianInFreeList [

	memory gc allocateOldSpaceChunkOfBytes: (self sizeOfChildInBreadthFirstOrder: 7) - 16.
	
	self denyFreeListEmpty: (self freeListForSize: 16)
]
