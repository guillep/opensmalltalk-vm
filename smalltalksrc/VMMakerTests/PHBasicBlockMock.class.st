Class {
	#name : #PHBasicBlockMock,
	#superclass : #BasicBlock,
	#instVars : [
		'name',
		'outgoingEdges'
	],
	#category : #'VMMakerTests-BasicBlocks'
}

{ #category : #'as yet unclassified' }
PHBasicBlockMock class >> named: aString [ 
	
	^ self new
		name: aString;
		yourself
]

{ #category : #accessing }
PHBasicBlockMock >> addSuccessor: aSuccessor [

	self addSuccessor: aSuccessor weight: 10
]

{ #category : #accessing }
PHBasicBlockMock >> addSuccessor: aSuccessor weight: aWeight [

	outgoingEdges add: (PHEdge new
		from: self;
		to: aSuccessor;
		weight: aWeight;
		yourself)
]

{ #category : #'as yet unclassified' }
PHBasicBlockMock >> id [

	^ name
]

{ #category : #accessing }
PHBasicBlockMock >> initialize [

	super initialize.
	outgoingEdges := OrderedCollection new
]

{ #category : #testing }
PHBasicBlockMock >> isFallingThroughBlock: aBasicBlock [
	"In the tests we do not re-order instructions"
	^ false
]

{ #category : #testing }
PHBasicBlockMock >> isJumpingConditionallyOnTrueBranchToBlock: aBasicBlock [
	"In the tests we do not re-order instructions"
	^ false
]

{ #category : #'as yet unclassified' }
PHBasicBlockMock >> name: aString [ 
	
	name := aString
]

{ #category : #'as yet unclassified' }
PHBasicBlockMock >> outgoingEdges [
	^ outgoingEdges
]

{ #category : #accessing }
PHBasicBlockMock >> printOn: aStream [

	aStream
		nextPutAll: self class name;
		nextPutAll: '(';
		print: name;
		nextPutAll: ')'
]

{ #category : #accessing }
PHBasicBlockMock >> successors [

	^ outgoingEdges collect: [ :e | e to ]
]

{ #category : #accessing }
PHBasicBlockMock >> successors: anObject [
	outgoingEdges := anObject
]
