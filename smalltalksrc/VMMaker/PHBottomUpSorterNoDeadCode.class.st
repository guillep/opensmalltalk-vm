Class {
	#name : #PHBottomUpSorterNoDeadCode,
	#superclass : #PettisHansenBottomUpSorter,
	#category : #'VMMaker-JIT'
}

{ #category : #sorting }
PHBottomUpSorterNoDeadCode >> sortBlocksInChains: chainsToSort [

	<var: #chain1 type: #'PHChain *'>
	<var: #chain2 type: #'PHChain *'>
	<var: #processedChain type: #'PHChain *'>
	| finalOrder worklist |
	chainsToSort isEmpty ifTrue: [ ^ chainsToSort ].
	
	finalOrder := self newLinkedList.
	worklist := chainsToSort sorted: [ :a :b | 
		| chain1 chain2 |
		chain1 := self cCoerce: a to: #'PHChain *'.
		chain2 := self cCoerce: b to: #'PHChain *'.
		chain1 priority < chain2 priority ].
	[ worklist isEmpty ] whileFalse: [
		| processedChain |
		processedChain := self cCoerce: worklist removeFirst to: #'PHChain *'.
		processedChain blocksDo: [ :b |
			finalOrder add: b ] ].

	^ finalOrder
]
