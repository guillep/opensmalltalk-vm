Class {
	#name : #PettisHansenBottomUpSorterTest,
	#superclass : #TestCase,
	#category : #'VMMakerTests-BasicBlocks'
}

{ #category : #tests }
PettisHansenBottomUpSorterTest >> testEmptyBasicBlockListReturnsEmptyList [

	| sorted |
	sorted := PettisHansenBottomUpSorter new sort: #().
	self assert: sorted isEmpty
]

{ #category : #tests }
PettisHansenBottomUpSorterTest >> testLinearBasicBlockListReturnsLinearList [

	| sorted basicBlocks a b c |
	basicBlocks := OrderedCollection new.
	basicBlocks add: (a := PHBasicBlockMock named: 'A').
	basicBlocks add: (b := PHBasicBlockMock named: 'B').
	basicBlocks add: (c := PHBasicBlockMock named: 'C').
	
	a successors: { b }.
	b successors: { c }.

	sorted := PettisHansenBottomUpSorter new sort: basicBlocks.
	
	self assert: sorted first equals: a.
	self assert: sorted second equals: b.
	self assert: sorted third equals: c.
]
