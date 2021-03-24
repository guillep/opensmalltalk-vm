Class {
	#name : #VMSpurInitializedOldSpaceTest,
	#superclass : #VMSpurMemoryManagerTest,
	#instVars : [
		'ourEphemeronClass'
	],
	#category : #'VMMakerTests-MemoryTests'
}

{ #category : #testing }
VMSpurInitializedOldSpaceTest class >> isAbstract [

	^ self == VMSpurInitializedOldSpaceTest
]

{ #category : #helpers }
VMSpurInitializedOldSpaceTest >> assertFreeListEmpty: aFreeListOop [

	self assert: aFreeListOop equals: 0
]

{ #category : #helpers }
VMSpurInitializedOldSpaceTest >> createEphemeronClass [
	ourEphemeronClass := self newObjectWithSlots: 3.
	memory 
		storePointer: "InstanceSpecificationIndex" 2
		ofObject: ourEphemeronClass
		withValue: (memory integerObjectOf: Ephemeron format).
	memory ensureBehaviorHash: ourEphemeronClass.
]

{ #category : #helpers }
VMSpurInitializedOldSpaceTest >> createFreeChunkOfSize: aSize [

	| address |
	address := memory gc allocateOldSpaceChunkOfBytes: aSize.
	memory gc freeChunkWithBytes: aSize at: address.
	^ address
]

{ #category : #helpers }
VMSpurInitializedOldSpaceTest >> denyFreeListEmpty: aFreeListOop [

	self deny: aFreeListOop equals: 0
]

{ #category : #tests }
VMSpurInitializedOldSpaceTest >> forgetObject3 [
	memory coInterpreter profileMethod: memory nilObject
]

{ #category : #helpers }
VMSpurInitializedOldSpaceTest >> freeListForSize: allocationSize [
	
	^ memory gc freeLists at: allocationSize / memory allocationUnit
]

{ #category : #helpers }
VMSpurInitializedOldSpaceTest >> freeTreeRootOop [

	"Initially the old space has a single big chunk of free memory and no small free chunks.
	So
	 - the free lists are empty
	 - the single big chunk of memory is the root of the free tree
	
	The root of the free tree has no child nodes"

	^ memory gc freeLists at: 0
]

{ #category : #helpers }
VMSpurInitializedOldSpaceTest >> freeTreeRootStartAddress [

	"The free tree lists stores the oop of free tree nodes.
	That means that the address stored references the beginning of the base header of the tree node.
	This is important because tree nodes can be large objects and have more than one header.
	
	We use #startOfObject: to return invariably the address where the node starts"
	^ memory startOfObject: self freeTreeRootOop
]

{ #category : #helpers }
VMSpurInitializedOldSpaceTest >> largerNodeOf: aNode [

	^ memory gc
		fetchPointer: memory gc freeChunkLargerIndex
		ofFreeChunk: aNode
]

{ #category : #helpers }
VMSpurInitializedOldSpaceTest >> newEphemeronObject [

"In pharo Ephemerons have 3 slots"
	
	^ self
		newObjectWithSlots: 3
		format: memory ephemeronFormat
		classIndex: (memory ensureBehaviorHash: ourEphemeronClass)
]

{ #category : #helpers }
VMSpurInitializedOldSpaceTest >> nextNodeOf: aNode [

	^ memory gc
		fetchPointer: memory gc freeChunkNextIndex
		ofFreeChunk: aNode
]

{ #category : #helpers }
VMSpurInitializedOldSpaceTest >> parentNodeOf: aNode [

	^ memory gc
		fetchPointer: memory gc freeChunkParentIndex
		ofFreeChunk: aNode
]

{ #category : #helpers }
VMSpurInitializedOldSpaceTest >> previousNodeOf: aNode [

	^ memory gc
		fetchPointer: memory gc freeChunkPrevIndex
		ofFreeChunk: aNode
]

{ #category : #running }
VMSpurInitializedOldSpaceTest >> setUp [

	super setUp.
	self initializeOldSpaceForScavenger.
	self initializeOldSpaceForFullGC.
	memory lastHash: 1.
]

{ #category : #helpers }
VMSpurInitializedOldSpaceTest >> smallerNodeOf: aNode [

	^ memory gc
		fetchPointer: memory gc freeChunkSmallerIndex
		ofFreeChunk: aNode
]
