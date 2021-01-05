Class {
	#name : #PettisHansenBottomUpSorter,
	#superclass : #Object,
	#category : #'VMMaker-JIT'
}

{ #category : #sorting }
PettisHansenBottomUpSorter >> basicBlockEdgesOf: basicBlocks [
	
	^ basicBlocks flatCollect: [ :e | e outgoingEdges ]
]

{ #category : #sorting }
PettisHansenBottomUpSorter >> hotPathChainsOf: basicBlocks [

	| chains priority fromChain toChain |
	chains := Dictionary new.
	basicBlocks do: [ :e |
		chains at: e put: (PHChain with: e).
	].
	priority := 0.
	((self basicBlockEdgesOf: basicBlocks) sorted: [ :e1 :e2 | e1 weight > e2 weight  ])
		do: [ :e |
			fromChain := chains at: e from.
			toChain := chains at: e to.
			(e from ~= e to and: [ 
				e from = fromChain tail
					and: [ e to = toChain head ] ])
						ifTrue: [ 
							priority := priority + 1.
							fromChain priority: ((fromChain priority min: toChain priority) min: priority).
							fromChain append: toChain.
							"Update all the blocks in the to-chain to use the same merged chain"
							toChain blocks do: [ :b |
								chains at: b put: fromChain
							]
						] ].

	chains ifEmpty: [ ^ #() ].
	^ chains values asSet
]

{ #category : #sorting }
PettisHansenBottomUpSorter >> sort: basicBlocks [

	| chains |
	chains := self hotPathChainsOf: basicBlocks.
	^ self sortBlocksInChains: chains
]

{ #category : #sorting }
PettisHansenBottomUpSorter >> sortBlocksInChains: aSetOfChains [

	| finalOrder worklist |
	finalOrder := OrderedCollection new.
	aSetOfChains ifEmpty: [ ^ finalOrder ].

	worklist := OrderedCollection new.
	worklist add: (aSetOfChains inject: aSetOfChains anyOne into: [:min :each | 
		min priority < each priority
			ifTrue: [ min ]
			ifFalse: [ each ]]).
	[ worklist isEmpty ] whileFalse: [ | processedChain |
		processedChain := worklist removeFirst.
		processedChain blocksDo: [ :b |
			finalOrder add: b ].
		processedChain blocksDo: [ :block |
			block successors do: [ :succ |
				(finalOrder includes: succ) ifFalse: [ | theChain |
					"If not placed, treat its worklist (if not already done)"
					theChain := aSetOfChains detect: [ :aChain | aChain contains: succ ].
					(worklist includes: theChain)
						ifFalse: [ worklist := (worklist, theChain) sorted: [ :a :b | a priority < b priority ] ].
					 ] ] ]
	].

	^ finalOrder
]
