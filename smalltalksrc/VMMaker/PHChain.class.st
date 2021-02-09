Class {
	#name : #PHChain,
	#superclass : #VMStructType,
	#instVars : [
		'priority',
		'blocks'
	],
	#category : #'VMMaker-JIT'
}

{ #category : #translation }
PHChain class >> instVarNamesAndTypesForTranslationDo: aBinaryBlock [

	self filteredInstVarNames do:
		[:ivn|
		aBinaryBlock
			value: ivn
			value: (ivn caseOf: {
						['priority']			-> [#'usqInt'].
						['blocks']				-> [#'VMLinkedList *']})]
]

{ #category : #modifying }
PHChain >> append: aPHChain [ 
	
	"Merge this chain with the chain in argument.
	Make this chain contain the concatenation of the blocks of both chains, my blocks first.
	At this point, each block has explicit control flow:
		- fallthrough branches are explicit jumps
		- conditional branches have both jump targets for when the condition is true or false
	Fix control flow to remove superfluous jumps (jumps to the next block)"
	
	"
	Prelude: Conditional branches contain explicitly both true and false jump targets.
	They are represented by a sequence of a conditional Jump and a non-conditional Jump.
	The first conditional Jump represents the branch case when the condition is true.
	The second non-conditional Jump represents the branch case when it is false.
	E.g.,
	
	Jmp.Eq target1
	Jmp target2
	
	There are four possible cases.
	1. a block has a jump (conditional or not) to a non contiguous block
		=> do nothing, we must leave the jumps there
	2. a block has a single non conditional jump to a contiguous block
		=> remove the jump and let it be a fallthrough
	3. a block has a conditional jump to a contiguous block when condition false
		=> remove the following jump representing the true case
	4. a block has a conditional jump to a contiguous block when condition true
		=> Inverse the conditions, then 3.
	"
	
	"Case 4"
	(blocks last isJumpingConditionallyOnTrueBranchToBlock: aPHChain blocks first)
		ifTrue: [ blocks last invertConditionalJump ].
	
	"Case 2,3 (they are the same now)"
	(blocks last isFallingThroughBlock: aPHChain blocks first)
		ifTrue: [ blocks last removeEndingJump ].

	"Concatenate block lists"
	blocks concatenateWith: aPHChain blocks
]

{ #category : #accessing }
PHChain >> blocks [
	^ blocks
]

{ #category : #iterating }
PHChain >> blocksDo: aFullBlockClosure [ 
	
	blocks do: aFullBlockClosure
]

{ #category : #accessing }
PHChain >> head [
	
	^ blocks first
]

{ #category : #testing }
PHChain >> includes: aBasicBlock [

	 ^ blocks includes: aBasicBlock
	
]

{ #category : #testing }
PHChain >> includesAll: aCollection [ 
	
	^ blocks includesAll: aCollection
]

{ #category : #printing }
PHChain >> printOn: aStream [

	aStream
		nextPutAll: self class name;
		nextPutAll: '('.
	
	blocks do: [ :b | aStream print: b id; nextPut: $, ].
	
	aStream nextPutAll: ')'
]

{ #category : #accessing }
PHChain >> priority [
	^ priority
]

{ #category : #accessing }
PHChain >> priority: anInteger [ 
	priority := anInteger
]

{ #category : #accessing }
PHChain >> setChainBlocks: aVMLinkedList [ 
	
	blocks := aVMLinkedList
]

{ #category : #accessing }
PHChain >> setChainPriority: anInteger [ 
	
	priority := anInteger
]

{ #category : #accessing }
PHChain >> size [

	^ blocks size
]

{ #category : #accessing }
PHChain >> tail [
	
	^ blocks last
]
