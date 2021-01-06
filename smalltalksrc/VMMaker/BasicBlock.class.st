Class {
	#name : #BasicBlock,
	#superclass : #Object,
	#instVars : [
		'firstInstructionIndex',
		'lastInstructionIndex',
		'compiler',
		'index'
	],
	#category : #'VMMaker-JIT'
}

{ #category : #accessing }
BasicBlock >> compiler [
	^ compiler
]

{ #category : #accessing }
BasicBlock >> compiler: anObject [
	compiler := anObject
]

{ #category : #accessing }
BasicBlock >> firstInstruction [

	^ compiler abstractInstructionAt: firstInstructionIndex
]

{ #category : #accessing }
BasicBlock >> firstInstructionIndex [
	^ firstInstructionIndex
]

{ #category : #accessing }
BasicBlock >> firstInstructionIndex: anObject [
	firstInstructionIndex := anObject
]

{ #category : #'as yet unclassified' }
BasicBlock >> id [
	
	^ index
]

{ #category : #accessing }
BasicBlock >> index: anIndex [

	index := anIndex
]

{ #category : #'as yet unclassified' }
BasicBlock >> instructionBeforeLastInstruction [
	
	^ compiler abstractInstructionAt: lastInstructionIndex - 1
]

{ #category : #accessing }
BasicBlock >> instructions [

	^ (firstInstructionIndex to: lastInstructionIndex)
		collect: [ :i | compiler abstractInstructionAt: i ]
]

{ #category : #'as yet unclassified' }
BasicBlock >> lastInstruction [
	
	^ compiler abstractInstructionAt: lastInstructionIndex
]

{ #category : #accessing }
BasicBlock >> lastInstructionIndex [
	^ lastInstructionIndex
]

{ #category : #accessing }
BasicBlock >> lastInstructionIndex: anObject [

	lastInstructionIndex := anObject
]

{ #category : #'as yet unclassified' }
BasicBlock >> outgoingEdges [
	
	| outgoingEdges |
	outgoingEdges := OrderedCollection new.

	self instructionBeforeLastInstruction isJump
		ifTrue: [ | targetLabel |
			targetLabel := self instructionBeforeLastInstruction
				resolveJumpTarget;
				jmpTarget.
			targetLabel isLabel ifTrue: [ outgoingEdges add: (PHEdge new
				from: self;
				to: targetLabel basicBlock;
				weight: self instructionBeforeLastInstruction jumpWeight;
				yourself) ] ].
		
	self lastInstruction isJump
		ifTrue: [ | targetLabel |
			targetLabel := self lastInstruction
				resolveJumpTarget;
				jmpTarget.
			targetLabel isLabel ifTrue: [ outgoingEdges add: (PHEdge new
				from: self;
				to: targetLabel basicBlock;
				weight: self lastInstruction jumpWeight;
				yourself) ] ].

	^ outgoingEdges
]

{ #category : #accessing }
BasicBlock >> printOn: aStream [

	aStream
		nextPutAll: 'BasicBlock(';
		nextPutAll: 'id=';
		nextPutAll: index asString;
		nextPutAll: ', address=';
		nextPutAll: (self firstInstruction address ifNil: [ '--' ] ifNotNil: [ :a | a asString ]);
		nextPutAll: ')'
]

{ #category : #'as yet unclassified' }
BasicBlock >> successors [
	
	^ self outgoingEdges collect: [ :e | e to ]
]
