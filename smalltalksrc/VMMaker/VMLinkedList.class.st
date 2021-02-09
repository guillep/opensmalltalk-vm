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
	
	aVMLinkedListNode next: firstNode.
	firstNode := aVMLinkedListNode.
	size := size + 1
]

{ #category : #'adding - private' }
VMLinkedList >> addLastNode: aVMLinkedListNode [ 
	
	self isEmpty ifTrue: [ 
		firstNode := aVMLinkedListNode.
	] ifFalse: [
		firstNode lastNode next: aVMLinkedListNode
	].
	size := size + 1
]

{ #category : #allocation }
VMLinkedList >> allocateNodeWith: anObject [ 

	| node |
	self cCode: [ 
		node := self
			cCoerce: (self malloc: (self sizeof: VMLinkedListNode))
			to: 'VMLinkedListNode *'.
	] inSmalltalk: [
		node := VMLinkedListNode new.
	].
	node value: anObject.
	node next: nil.
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
	
	firstNode lastNode next: aVMLinkedList firstNode
]

{ #category : #iterating }
VMLinkedList >> detect: aFullBlockClosure [ 

	| currentNode found |
	currentNode := firstNode.
	found := nil.
	[ found isNil and: [ currentNode notNil ] ] whileTrue: [ 
		(aFullBlockClosure value: currentNode value)
			ifTrue: [ found := currentNode value ]
			ifFalse: [ currentNode := currentNode next ].
	].
	^ found
]

{ #category : #iterating }
VMLinkedList >> do: aBlockClosure [

	| node |
	node := firstNode.
	[ node isNil ] whileFalse: [ 
		aBlockClosure value: node value.
		node := node next.
	].
]

{ #category : #accessing }
VMLinkedList >> first [

	^ firstNode value
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
	
	^ firstNode includes: anObject
]

{ #category : #testing }
VMLinkedList >> includesAll: aCollection [ 
	
	aCollection do: [ :e |
		(self includes: e) ifFalse: [ ^ false ] ].
	^ true
]

{ #category : #inserting }
VMLinkedList >> insert: anObject sortedBy: aCriterion [
	
	| node |
	self isEmpty ifTrue: [ 
		self add: anObject.
		^ self ].
	
	"Should it be before first?"
	(aCriterion value: anObject value: firstNode value)
		ifTrue: [
			self addFirst: anObject.
			^ self ].
	
	"Else recurse and ask each node to test"
	node := self allocateNodeWith: anObject.	
	^ firstNode insertNode: node sortedBy: aCriterion
]

{ #category : #testing }
VMLinkedList >> isEmpty [
	
	^ self notEmpty not
]

{ #category : #accessing }
VMLinkedList >> last [
	
	self isEmpty ifTrue: [ self error: 'Trying to access last of empty list' ].
	^ firstNode lastNode value
]

{ #category : #testing }
VMLinkedList >> notEmpty [
	
	^ firstNode notNil
]

{ #category : #printing }
VMLinkedList >> printOn: aStream [

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
	^ removedNode value
]

{ #category : #accessing }
VMLinkedList >> second [
	
	^ firstNode next value
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
	
	| sortedList |
	sortedList := self newLinkedList.
	self do: [ :element |
		sortedList insert: element sortedBy: aCriterion.
	].
	^ sortedList
]

{ #category : #accessing }
VMLinkedList >> third [
	
	^ firstNode next next value
]
