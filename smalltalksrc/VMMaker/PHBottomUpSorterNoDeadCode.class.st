Class {
	#name : #PHBottomUpSorterNoDeadCode,
	#superclass : #PettisHansenBottomUpSorter,
	#category : #'VMMaker-JIT'
}

{ #category : #sorting }
PHBottomUpSorterNoDeadCode >> sortBlocksInChains: chainsToSort [

	| finalOrder worklist |
	chainsToSort isEmpty ifTrue: [ ^ chainsToSort ].
	
	finalOrder := self newLinkedList.
	worklist := chainsToSort sorted: [ :a :b | a priority < b priority ].
	[ worklist isEmpty ] whileFalse: [ | processedChain |
		processedChain := worklist removeFirst.
		processedChain blocksDo: [ :b |
			finalOrder add: b ] ].

	^ finalOrder
]
