Class {
	#name : #PettisHansenBottomUpSorter,
	#superclass : #VMClass,
	#category : #'VMMaker-JIT'
}

{ #category : #sorting }
PettisHansenBottomUpSorter >> basicBlockEdgesOf: basicBlocks [
	
	| sortedEdges |
	sortedEdges := self newLinkedList.
	basicBlocks do: [ :aBasicBlock | | aBlockEdges |
		aBlockEdges := aBasicBlock outgoingEdges.
		aBlockEdges do: [ :edge |
			sortedEdges insert: edge sortedBy: [ :e1 :e2 | e1 weight >= e2 weight ].
			 ] ].
	^ sortedEdges
]

{ #category : #sorting }
PettisHansenBottomUpSorter >> hotPathChainsOf: basicBlocks [

	| priority fromChain toChain list |
	basicBlocks do: [ :e |
		e chain: (PHChain with: e).
	].
	priority := 0.
	(self basicBlockEdgesOf: basicBlocks)
		do: [ :e |
			fromChain := e from chain.
			toChain := e to chain.
			(e from ~= e to and: [ 
				e from = fromChain tail
					and: [ e to = toChain head ] ])
						ifTrue: [ 
							priority := priority + 1.
							fromChain priority: ((fromChain priority min: toChain priority) min: priority).
							fromChain append: toChain.
							"Update all the blocks in the to-chain to use the same merged chain"
							toChain blocks do: [ :b |
								b chain: fromChain
							]
						] ].
	
	"Collect all the different chains"
	list := self newLinkedList.
	basicBlocks do: [ :e |
		(list includes: e chain)
			ifFalse: [ list add: e chain ].		
	].
	^ list
]

{ #category : #sorting }
PettisHansenBottomUpSorter >> sort: basicBlocks [

	| chains |
	chains := self hotPathChainsOf: basicBlocks.
	^ self sortBlocksInChains: chains
]

{ #category : #sorting }
PettisHansenBottomUpSorter >> sortBlocksInChains: aSetOfChains [

	| finalOrder worklist min |
	finalOrder := OrderedCollection new.
	aSetOfChains isEmpty ifTrue: [ ^ finalOrder ].

	worklist := OrderedCollection new.
	min := aSetOfChains first.
	aSetOfChains do: [ :each |
		each priority < min priority
			ifFalse: [ min := each ] ].
	
	worklist add: min.
	[ worklist isEmpty ] whileFalse: [ | processedChain |
		processedChain := worklist removeFirst.
		processedChain blocksDo: [ :b |
			finalOrder add: b ].
		processedChain blocksDo: [ :block |
			block successors do: [ :succ |
				(finalOrder includes: succ) ifFalse: [ | theChain |
					"If not placed, treat its worklist (if not already done)"
					theChain := aSetOfChains detect: [ :aChain | aChain includes: succ ].
					(worklist includes: theChain)
						ifFalse: [ worklist := (worklist, { theChain }) sorted: [ :a :b | a priority < b priority ] ].
					 ] ] ]
	].

	^ finalOrder
]
