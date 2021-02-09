Class {
	#name : #VMLinkedList,
	#superclass : #VMStructType,
	#instVars : [
		'size',
		'firstNode'
	],
	#category : #'VMMaker-Support'
}

{ #category : #translation }
VMLinkedList class >> instVarNamesAndTypesForTranslationDo: aBinaryBlock [

	self filteredInstVarNames do:
		[:ivn|
		aBinaryBlock
			value: ivn
			value: (ivn caseOf: {
						['size']			-> [#sqInt].
						['firstNode']		-> [#'VMLinkedListNode *']})]
]

{ #category : #adding }
VMLinkedList >> add: anObject [
	
	| node |
	node := self allocateNodeWith: anObject.
	self addLastNode: node
]

{ #category : #adding }
VMLinkedList >> addFirst: anObject [
	
	| node |
	node := self allocateNodeWith: anObject.
	self addFirstNode: node
]

{ #category : #'adding - private' }
VMLinkedList >> addFirstNode: aVMLinkedListNode [ 
	
	"Assumption: the node is orphan"
	
	aVMLinkedListNode setNext: firstNode.
	firstNode := aVMLinkedListNode.
	size := size + 1
]

{ #category : #'adding - private' }
VMLinkedList >> addLastNode: aVMLinkedListNode [ 
	
	self isEmpty ifTrue: [ 
		firstNode := aVMLinkedListNode.
	] ifFalse: [
		firstNode lastNode setNext: aVMLinkedListNode
	].
	size := size + 1
]

{ #category : #allocation }
VMLinkedList >> allocateNodeWith: anObject [ 

	| node |
	self cCode: [ 
		node := self
			cCoerce: (self malloc: (self sizeof: VMLinkedListNode))
			to: 'LinkedListNode *'.
	] inSmalltalk: [
		node := VMLinkedListNode new.
	].
	node setElement: anObject.
	node setNext: nil.
	^ node
]

{ #category : #iterating }
VMLinkedList >> anySatisfy: aFullBlockClosure [ 
	
	self do: [ :e | (aFullBlockClosure value: e) ifTrue: [ ^ true ] ].
	^ false
]

{ #category : #converting }
VMLinkedList >> asArray [
	
	^ Array streamContents: [ :stream |
		self do: [ :e | stream nextPut: e ] ]
]

{ #category : #inserting }
VMLinkedList >> asOrderedCollection [
	<doNotGenerate>
	^ OrderedCollection streamContents: [ :str |
		str nextPutAll: self ]
]

{ #category : #operations }
VMLinkedList >> concatenateWith: aVMLinkedList [ 
	
	"Concatenate the linked list in the argument with myself.
	This destroys the argument, and appends all elements to myself"
	self isEmpty ifTrue: [ 
		firstNode := aVMLinkedList firstNode.
		^ self.
	].
	
	firstNode lastNode setNext: aVMLinkedList firstNode
]

{ #category : #iterating }
VMLinkedList >> detect: aFullBlockClosure [ 

	| currentNode found |
	currentNode := firstNode.
	found := nil.
	[ found isNil and: [ currentNode notNil ] ] whileTrue: [ 
		(aFullBlockClosure value: currentNode element)
			ifTrue: [ found := currentNode element ]
			ifFalse: [ currentNode := currentNode next ].
	].
	^ found
]

{ #category : #iterating }
VMLinkedList >> do: aBlockClosure [
	<inline: true>
	| node |
	node := firstNode.
	[ node isNil ] whileFalse: [ 
		aBlockClosure value: node element.
		node := node next.
	].
]

{ #category : #accessing }
VMLinkedList >> first [

	^ firstNode element
]

{ #category : #accessing }
VMLinkedList >> firstNode [

	^ firstNode
]

{ #category : #accessing }
VMLinkedList >> firstNode: anObject [

	firstNode := anObject
]

{ #category : #testing }
VMLinkedList >> includes: anObject [
	
	self isEmpty ifTrue: [ ^ false ].
	
	^ firstNode nodeIncludes: anObject
]

{ #category : #testing }
VMLinkedList >> includesAll: aCollection [ 
	
	aCollection do: [ :e |
		(self includes: e) ifFalse: [ ^ false ] ].
	^ true
]

{ #category : #inserting }
VMLinkedList >> insert: anObject sortedBy: aCriterion [
	
	<inline: true>
	| node currentNode |
	self isEmpty ifTrue: [ 
		self add: anObject.
		^ self ].
	
	"Should it be before first?"
	(aCriterion value: anObject value: firstNode element)
		ifTrue: [
			self addFirst: anObject.
			^ self ].
	
	"Else recurse and ask each node to test"
	node := self allocateNodeWith: anObject.	
	
	"Check if the object should be inserted 
	- just after a node, 
	- else after some of my next nodes
	
	Assummption: the object cannot be before the first one"
	
	currentNode := firstNode.
	["Should it just be my next? => Insert it"
	(currentNode next isNil or: [aCriterion value: node element value: currentNode next element])
		ifTrue: [
			node setNext: currentNode next.
			currentNode setNext: node.
			^ self ].
	currentNode := currentNode next.
	
	true ] whileTrue.
	^ self
]

{ #category : #testing }
VMLinkedList >> isEmpty [
	
	^ self notEmpty not
]

{ #category : #accessing }
VMLinkedList >> last [
	
	self isEmpty ifTrue: [ self error: 'Trying to access last of empty list' ].
	^ firstNode lastNode element
]

{ #category : #testing }
VMLinkedList >> notEmpty [
	
	^ firstNode notNil
]

{ #category : #printing }
VMLinkedList >> printOn: aStream [
	<doNotGenerate>
	aStream nextPutAll: 'VMLinkedList('.
	self do: [ :e |
		aStream
			print: e;
			nextPut: $, ].
	aStream nextPut: $)
]

{ #category : #removing }
VMLinkedList >> removeFirst [
	
	| removedNode |
	removedNode := firstNode.
	firstNode := firstNode next.

	self flag: #deallocation.
	^ removedNode element
]

{ #category : #accessing }
VMLinkedList >> second [
	
	^ firstNode next element
]

{ #category : #accessing }
VMLinkedList >> size [

	^ size
]

{ #category : #accessing }
VMLinkedList >> size: anObject [

	size := anObject
]

{ #category : #sorting }
VMLinkedList >> sorted: aCriterion [ 
	
	<inline: true>
	| sortedList |
	sortedList := self newLinkedList.
	self do: [ :element |
		sortedList insert: element sortedBy: aCriterion.
	].
	^ sortedList
]

{ #category : #accessing }
VMLinkedList >> third [
	
	^ firstNode next next element
]
