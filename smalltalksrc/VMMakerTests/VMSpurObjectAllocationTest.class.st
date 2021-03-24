Class {
	#name : #VMSpurObjectAllocationTest,
	#superclass : #VMSpurInitializedOldSpaceTest,
	#category : #'VMMakerTests-MemoryTests'
}

{ #category : #tests }
VMSpurObjectAllocationTest >> testAllocateObjectInNewSpaceMovesFreeStart [

	| oldFreeStart |
	oldFreeStart := memory gc freeStart.
	memory allocateSlots: 0 format: memory arrayFormat classIndex: memory arrayClassIndexPun.
	
	self assert: memory gc freeStart > oldFreeStart
]

{ #category : #tests }
VMSpurObjectAllocationTest >> testAllocateObjectInOldSpaceMovesFreeStart [

	| oldFreeStart |
	oldFreeStart := memory gc freeStart.
	memory
		allocateSlots: (memory gc scavengeThreshold / memory wordSize) floor + (memory wordSize * 2)
		format: memory arrayFormat
		classIndex: memory arrayClassIndexPun.
	
	self assert: memory gc freeStart equals: oldFreeStart
]
