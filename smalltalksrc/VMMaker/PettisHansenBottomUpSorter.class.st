Class {
	#name : #PettisHansenBottomUpSorter,
	#superclass : #Object,
	#category : #'VMMaker-JIT'
}

{ #category : #sorting }
PettisHansenBottomUpSorter >> basicBlockEdgesOf: basicBlocks [
	
	^ basicBlocks gather: [ :e |
		e successors collect: [ :s |
			PHEdge new
				from: e;
				to: s;
				yourself ] ]
]

{ #category : #sorting }
PettisHansenBottomUpSorter >> sort: basicBlocks [

	| chains priority fromChain toChain |
	chains := Dictionary new.
	basicBlocks do: [ :e |
		chains at: e put: (PHChain with: e).
	].
	priority := 0.
	((self basicBlockEdgesOf: basicBlocks) sorted: [ :e1 :e2 | e1 priority > e2 priority  ])
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
	^ chains anyOne blocks
]
