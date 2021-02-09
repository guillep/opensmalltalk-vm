Class {
	#name : #PettisHansenBottomUpSorterTest,
	#superclass : #TestCase,
	#category : #'VMMakerTests-BasicBlocks'
}

{ #category : #tests }
PettisHansenBottomUpSorterTest >> testControlFlowWithDegenerateBlocks [

	| basicBlocks bA bB bD bE order |
	basicBlocks := OrderedCollection new.
	basicBlocks add: (bA := PHBasicBlockMock named: 'A').
	basicBlocks add: (bB := PHBasicBlockMock named: 'B').
	basicBlocks add: (bD := PHBasicBlockMock named: 'D').
	basicBlocks add: (bE := PHBasicBlockMock named: 'E').
	
	bA addSuccessor: bB weight: 1.
	bA addSuccessor: bD weight: 7.
	bB addSuccessor: bD weight: 1.
	bD addSuccessor: bE weight: 8.

	order := PettisHansenBottomUpSorter new sort: basicBlocks.
	
	self assert: order asArray equals: { bA . bD . bE .  bB }
]

{ #category : #tests }
PettisHansenBottomUpSorterTest >> testControlFlowWithDegenerateBlocksReturnsThreeChains [

	| basicBlocks b0 b1 b2 b3 b4 chains |
	basicBlocks := OrderedCollection new.
	basicBlocks add: (b0 := PHBasicBlockMock named: '0').
	basicBlocks add: (b1 := PHBasicBlockMock named: '1').
	basicBlocks add: (b2 := PHBasicBlockMock named: '2').
	basicBlocks add: (b3 := PHBasicBlockMock named: '3').
	basicBlocks add: (b4 := PHBasicBlockMock named: '4').
	
	b0 addSuccessor: b1 weight: 1.
	b0 addSuccessor: b2 weight: 2.
	b0 addSuccessor: b3 weight: 7.
	b1 addSuccessor: b3 weight: 1.
	b2 addSuccessor: b4 weight: 2.
	b3 addSuccessor: b4 weight: 8.

	chains := PettisHansenBottomUpSorter new hotPathChainsOf: basicBlocks.
	
	self assert: (chains anySatisfy: [ :c | c includesAll: {b0 . b3 . b4} ]).
	self assert: (chains anySatisfy: [ :c | 
		(c includes: b1) and: [ c size = 1 ] ]).
	self assert: (chains anySatisfy: [ :c | 
		(c includes: b2) and: [ c size = 1 ] ]).
]

{ #category : #tests }
PettisHansenBottomUpSorterTest >> testControlFlowWithTwoChainsBlocks [

	| basicBlocks bA bB bC bD bE bF order |
	basicBlocks := OrderedCollection new.
	basicBlocks add: (bA := PHBasicBlockMock named: 'A').
	basicBlocks add: (bB := PHBasicBlockMock named: 'B').
	basicBlocks add: (bC := PHBasicBlockMock named: 'C').
	basicBlocks add: (bD := PHBasicBlockMock named: 'D').
	basicBlocks add: (bE := PHBasicBlockMock named: 'E').
	basicBlocks add: (bF := PHBasicBlockMock named: 'F').
	
	bA addSuccessor: bB weight: 7.
	bA addSuccessor: bC weight: 3.
	bB addSuccessor: bD weight: 4.
	bB addSuccessor: bE weight: 3.
	bC addSuccessor: bE weight: 3.
	bD addSuccessor: bF weight: 4.
	bE addSuccessor: bF weight: 6.

	order := PettisHansenBottomUpSorter new sort: basicBlocks.
	
	self assert: order asArray equals: { bA . bB . bD . bC . bE . bF }
]

{ #category : #tests }
PettisHansenBottomUpSorterTest >> testControlFlowWithTwoChainsReturnsTwoChains [

	| basicBlocks bA bB bC bD bE bF chains |
	basicBlocks := OrderedCollection new.
	basicBlocks add: (bA := PHBasicBlockMock named: 'A').
	basicBlocks add: (bB := PHBasicBlockMock named: 'B').
	basicBlocks add: (bC := PHBasicBlockMock named: 'C').
	basicBlocks add: (bD := PHBasicBlockMock named: 'D').
	basicBlocks add: (bE := PHBasicBlockMock named: 'E').
	basicBlocks add: (bF := PHBasicBlockMock named: 'F').
	
	bA addSuccessor: bB weight: 7.
	bA addSuccessor: bC weight: 3.
	bB addSuccessor: bD weight: 4.
	bB addSuccessor: bE weight: 3.
	bC addSuccessor: bE weight: 3.
	bD addSuccessor: bF weight: 4.
	bE addSuccessor: bF weight: 6.

	chains := PettisHansenBottomUpSorter new hotPathChainsOf: basicBlocks.
	
	self assert: (chains anySatisfy: [ :c | c includesAll: {bA . bB . bD } ]).
	self assert: (chains anySatisfy: [ :c | c includesAll: {bC . bE . bF} ]).
]

{ #category : #tests }
PettisHansenBottomUpSorterTest >> testEmptyBasicBlockListReturnsEmptyList [

	| sorted |
	sorted := PettisHansenBottomUpSorter new sort: #().
	self assert: sorted isEmpty
]

{ #category : #tests }
PettisHansenBottomUpSorterTest >> testForkControlFlowReturnsListSortedByWeight [

	| sorted basicBlocks a b c |
	basicBlocks := OrderedCollection new.
	basicBlocks add: (a := PHBasicBlockMock named: 'A').
	basicBlocks add: (b := PHBasicBlockMock named: 'B').
	basicBlocks add: (c := PHBasicBlockMock named: 'C').
	
	"A-100->B is stronger than the others, thus the final order should be A, B, C"
	a addSuccessor: b weight: 100.
	a addSuccessor: c weight: 40.
	b addSuccessor: c weight: 30.

	sorted := PettisHansenBottomUpSorter new sort: basicBlocks.
	
	self assert: sorted first equals: a.
	self assert: sorted second equals: b.
	self assert: sorted third equals: c.
]

{ #category : #tests }
PettisHansenBottomUpSorterTest >> testLinearBasicBlockListReturnsLinearList [

	| sorted basicBlocks a b c |
	basicBlocks := OrderedCollection new.
	basicBlocks add: (a := PHBasicBlockMock named: 'A').
	basicBlocks add: (b := PHBasicBlockMock named: 'B').
	basicBlocks add: (c := PHBasicBlockMock named: 'C').
	
	a addSuccessor: b.
	b addSuccessor: c.

	sorted := PettisHansenBottomUpSorter new sort: basicBlocks.
	
	self assert: sorted first equals: a.
	self assert: sorted second equals: b.
	self assert: sorted third equals: c.
]
