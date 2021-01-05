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
1haltIf: [ TEST and: [anObject < firstInstructionIndex]].
	lastInstructionIndex := anObject
]

{ #category : #accessing }
BasicBlock >> printOn: aStream [

	aStream
		nextPutAll: 'BasicBlock(';
		nextPutAll: 'id=';
		nextPutAll: index asString;
		nextPutAll: ', address=';
		nextPutAll: (self firstInstruction address ifNil: [ '--' ] ifNotNil: [ :a | a hex ]);
		nextPutAll: ')'
]

{ #category : #'as yet unclassified' }
BasicBlock >> successors [
	
	| successors |
	successors := OrderedCollection new.

	self instructionBeforeLastInstruction isJump
		ifTrue: [ | targetLabel |
			targetLabel := self instructionBeforeLastInstruction jmpTarget.
			targetLabel isLabel ifTrue: [ successors add: targetLabel basicBlock ] ].
		
	self lastInstruction isJump
		ifTrue: [ | targetLabel |
			targetLabel := self lastInstruction jmpTarget.
			targetLabel isLabel ifTrue: [ successors add: targetLabel basicBlock ] ].

	^ successors
]
