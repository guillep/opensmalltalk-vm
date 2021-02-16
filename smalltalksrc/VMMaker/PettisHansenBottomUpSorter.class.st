Class {
	#name : #PettisHansenBottomUpSorter,
	#superclass : #VMClass,
	#category : #'VMMaker-JIT'
}

{ #category : #translation }
PettisHansenBottomUpSorter class >> typeForSelf [
	"Should not receive the receiver as first argument, it is implicit"
	^#implicit
]

{ #category : #sorting }
PettisHansenBottomUpSorter >> basicBlockEdgesOf: aListOfBasicBlocks [
	| sortedEdges |
	sortedEdges := self newLinkedList.
	aListOfBasicBlocks do: [ :aBasicBlock | | aBlockEdges |
		aBlockEdges := aBasicBlock outgoingEdges.
		aBlockEdges do: [ :anElement |
			sortedEdges insert: anElement sortedBy: [ :e1 :e2 | 
				| edge1 edge2 |
				edge1 := self cCoerce: e1 to: #'PHEdge *'.
				edge2 := self cCoerce: e2 to: #'PHEdge *'.
				edge1 weight >= edge2 weight ].
			 ] ].
	^ sortedEdges
]

{ #category : #sorting }
PettisHansenBottomUpSorter >> hotPathChainsOf: aListOfBasicBlocks [

	<var: #basicBlock type: #'BasicBlock *'>
	<var: #basicBlock1 type: #'BasicBlock *'>
	<var: #basicBlock2 type: #'BasicBlock *'>
	<var: #edge type: #'PHEdge *'>
	<var: #fromChain type: #'PHChain *'>
	<var: #toChain type: #'PHChain *'>
	| priority fromChain toChain list |
	aListOfBasicBlocks do: [ :basicBlock | | chain |
		chain := self newBlockChain.
		chain blocks add: basicBlock.
		basicBlock chain: chain.
	].
	priority := 0.
	(self basicBlockEdgesOf: aListOfBasicBlocks)
		do: [ :e | | edge |
			edge := self cCoerce: e to: #'PHEdge *'.
			fromChain := edge from chain.
			toChain := edge to chain.
			(edge from ~= edge to and: [ 
				edge from = fromChain tail
					and: [ edge to = toChain head ] ])
						ifTrue: [ 
							priority := priority + 1.
							fromChain priority: ((fromChain priority min: toChain priority) min: priority).
							fromChain append: toChain.
							"Update all the blocks in the to-chain to use the same merged chain"
							toChain blocks do: [ :b | | basicBlock1 |
								basicBlock1 := self cCoerce: b to: #'BasicBlock *'.
								basicBlock1 chain: fromChain
							]
						] ].
	
	"Collect all the different chains"
	list := self newLinkedList.
	aListOfBasicBlocks do: [ :e |
		| basicBlock2 |
		basicBlock2 := self cCoerce: e to: #'BasicBlock *'.
		(list includes: basicBlock2)
			ifFalse: [ list add: basicBlock2 chain ].
	].
	^ list
]

{ #category : #'basic-blocks' }
PettisHansenBottomUpSorter >> newBlockChain [
	| chain |
	<var: 'chain' type: #'PHChain *'>

	self cCode: [ 
		chain := self
			cCoerce: (self malloc: (self sizeof: PHChain))
			to: #'PHChain *'.
	] inSmalltalk: [ 
		chain := PHChain new.
	].
	"Initial size = 0"
	chain setChainPriority: 1000.
	chain setChainBlocks: self newLinkedList.
	^ chain
]

{ #category : #sorting }
PettisHansenBottomUpSorter >> sort: aListOfBasicBlocks [

	| chains |
	chains := self hotPathChainsOf: aListOfBasicBlocks.
	^ self sortBlocksInChains: chains
]

{ #category : #sorting }
PettisHansenBottomUpSorter >> sortBlocksInChains: aSetOfChains [

	| finalOrder worklist min |
	finalOrder := self newLinkedList.
	aSetOfChains isEmpty ifTrue: [ ^ finalOrder ].

	worklist := self newLinkedList.
	min := aSetOfChains first.
	aSetOfChains do: [ :each |
		each priority < min priority
			ifTrue: [ min := each ] ].
	
	worklist add: min.
	[ worklist isEmpty ] whileFalse: [ | processedChain |
		processedChain := worklist removeFirst.
		processedChain blocksDo: [ :b |
			finalOrder add: b ].
		processedChain blocksDo: [ :block |
			block successors do: [ :succ |
				(finalOrder includes: succ) ifFalse: [ | theChain |
					"If not placed, treat its worklist (if not already done)"
					theChain := aSetOfChains detect: [ :aChain | aChain includesBlock: succ ].
					(worklist includes: theChain) ifFalse: [
							worklist
								insert: theChain
								sortedBy: [ :a :b | a priority < b priority ] ].
				]
			]
		]
	].

	^ finalOrder
]
