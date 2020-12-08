Class {
	#name : #BasicBlock,
	#superclass : #Object,
	#instVars : [
		'firstInstructionIndex',
		'lastInstructionIndex',
		'compiler'
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
BasicBlock >> firstInstructionIndex [
	^ firstInstructionIndex
]

{ #category : #accessing }
BasicBlock >> firstInstructionIndex: anObject [
	firstInstructionIndex := anObject
]

{ #category : #accessing }
BasicBlock >> instructions [

	^ (firstInstructionIndex to: lastInstructionIndex)
		collect: [ :i | compiler abstractInstructionAt: i ]
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
