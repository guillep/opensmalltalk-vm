Class {
	#name : #PHBottomUpSorterNoDeadCode,
	#superclass : #PettisHansenBottomUpSorter,
	#category : #'VMMaker-JIT'
}

{ #category : #sorting }
PHBottomUpSorterNoDeadCode >> sortBlocksInChains: aSetOfChains [

	| finalOrder worklist |
	finalOrder := OrderedCollection new.
	aSetOfChains ifEmpty: [ ^ finalOrder ].

	worklist := (aSetOfChains sorted: [ :a :b | a priority < b priority ]) asOrderedCollection.
	[ worklist isEmpty ] whileFalse: [ | processedChain |
		processedChain := worklist removeFirst.
		processedChain blocksDo: [ :b |
			finalOrder add: b ] ].

	^ finalOrder
]
