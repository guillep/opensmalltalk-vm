Class {
	#name : #BasicBlock,
	#superclass : #VMStructType,
	#instVars : [
		'firstInstructionIndex',
		'lastInstructionIndex',
		'compiler',
		'index',
		'chain'
	],
	#category : #'VMMaker-JIT'
}

{ #category : #translation }
BasicBlock class >> filteredInstVarNames [
	"Eliminate bcpc, which is development-time only."
	^ super filteredInstVarNames copyWithoutAll: #( 'compiler' 'index' )
]

{ #category : #translation }
BasicBlock class >> instVarNamesAndTypesForTranslationDo: aBinaryBlock [
	
	self filteredInstVarNames do:
		[:ivn|
		 aBinaryBlock
			value: ivn
			value: (ivn caseOf: {
						['firstInstructionIndex'] -> [#usqInt].
						['lastInstructionIndex'] -> [#usqInt].
						['chain'] -> [#'PHChain *'] })]
]

{ #category : #accessing }
BasicBlock >> chain [

	^ chain
]

{ #category : #accessing }
BasicBlock >> chain: anObject [

	chain := anObject
]

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

{ #category : #modifying }
BasicBlock >> invertConditionalJump [
	
	| inverseOpcode targetA |
	inverseOpcode := compiler inverseBranchFor: self instructionBeforeLastInstruction opcode.
	self instructionBeforeLastInstruction opcode: inverseOpcode.
	
	targetA := self instructionBeforeLastInstruction getJmpTarget.
	self instructionBeforeLastInstruction jmpTarget: self lastInstruction getJmpTarget.
	self lastInstruction jmpTarget: targetA
]

{ #category : #testing }
BasicBlock >> isFallingThroughBlock: aBasicBlock [
	
	| lastInstruction |
	lastInstruction := self lastInstruction.
	^ lastInstruction isJump
		and: [ lastInstruction getJmpTarget = aBasicBlock label ]
]

{ #category : #testing }
BasicBlock >> isJumpingConditionallyOnTrueBranchToBlock: aBasicBlock [ 
	"A conditional jump is represented by two jumps:
		a conditional jump (the true branch) followed by a non conditional jump (the false branch).
	Then, if the instruction before last anwers true to #isJump, we have a conditional jump.
	#isJump answers true if the instruction is jump, conditional or not.

	Then check that the jump target of the condition is the entry label of the block"
	| instructionBeforeLast |
	instructionBeforeLast := self instructionBeforeLastInstruction.
	^ instructionBeforeLast isJump
		and: [ instructionBeforeLast getJmpTarget = aBasicBlock label ]
	
]

{ #category : #accessing }
BasicBlock >> label [
	
	^ self firstInstruction 
]

{ #category : #'as yet unclassified' }
BasicBlock >> lastInstruction [
	
	^ compiler abstractInstructionAt: lastInstructionIndex
]

{ #category : #accessing }
BasicBlock >> lastInstructionIndex: anObject [

	lastInstructionIndex := anObject
]

{ #category : #'as yet unclassified' }
BasicBlock >> newEdgeFrom: fromBasicBlock to: toBasicBlock weight: weight [

	| edge |
	<var: 'edge' type: #'PHEdge *'>

	self cCode: [ 
		edge := self
			cCoerce: (self malloc: (self sizeof: PHEdge))
			to: #'PHEdge *'.
	] inSmalltalk: [ 
		edge := PHEdge new.
	].
	"Initialization"
	edge from: fromBasicBlock.
	edge to: toBasicBlock.
	edge weight: weight.
	^ edge
]

{ #category : #'as yet unclassified' }
BasicBlock >> outgoingEdges [
	
	| outgoingEdges |
	outgoingEdges := self newLinkedList.

	self instructionBeforeLastInstruction isJump
		ifTrue: [ | targetLabel |
			targetLabel := self instructionBeforeLastInstruction
				resolveJumpTarget;
				getJmpTarget.
			targetLabel isLabel ifTrue: [ outgoingEdges add: (self
				newEdgeFrom: self
				to: targetLabel getBasicBlock 
				weight: self instructionBeforeLastInstruction getJumpWeight) ] ].
		
	self lastInstruction isJump
		ifTrue: [ | targetLabel |
			targetLabel := self lastInstruction
				resolveJumpTarget;
				getJmpTarget.
			targetLabel isLabel ifTrue: [ outgoingEdges add: (self
				newEdgeFrom: self
				to: targetLabel getBasicBlock 
				weight: self lastInstruction getJumpWeight) ] ].

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

{ #category : #modifying }
BasicBlock >> removeEndingJump [
	
	"Remove the last instruction in this block.
	We can just make this block shorter by one instruction.
	The instruction will still be in the stream of instructions but unreachable."
	lastInstructionIndex := lastInstructionIndex - 1
]

{ #category : #'as yet unclassified' }
BasicBlock >> successors [
	
	^ self outgoingEdges collect: [ :e | e to ]
]
