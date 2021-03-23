Class {
	#name : #PushDownBlockSorter,
	#superclass : #BasicBlockSorter,
	#category : #'VMMaker-JIT'
}

{ #category : #sorting }
PushDownBlockSorter >> sort: aListOfBasicBlocks [

	| finalOrder pendingBlocks |
	finalOrder := self newLinkedList.
	pendingBlocks := self newLinkedList.
	
	aListOfBasicBlocks do: [ :basicBlock |
		basicBlock isPushDownBlock
			ifTrue: [ pendingBlocks add: basicBlock ]
			ifFalse: [ finalOrder add: basicBlock ] ].
		
	pendingBlocks do: [ :pendingBlock | finalOrder add: pendingBlock ].
	^ finalOrder
]
