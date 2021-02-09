Class {
	#name : #VMLinkedListNode,
	#superclass : #VMStructType,
	#instVars : [
		'next',
		'element'
	],
	#category : #'VMMaker-Support'
}

{ #category : #translation }
VMLinkedListNode class >> instVarNamesAndTypesForTranslationDo: aBinaryBlock [

	self filteredInstVarNames do:
		[:ivn|
		aBinaryBlock
			value: ivn
			value: (ivn caseOf: {
						['element']			-> [#'void *'].
						['next']		-> [#'struct _LinkedListNode *' "recursive definition..."]})]
]

{ #category : #translation }
VMLinkedListNode class >> structTypeName [
	^'LinkedListNode'
]

{ #category : #accessing }
VMLinkedListNode >> element [

	^ element
]

{ #category : #inserting }
VMLinkedListNode >> insertNode: aNode sortedBy: aCriterion [
	
	"Check if the object should be inserted 
	- just after me, 
	- else after some of my next nodes
	
	Assummption: the object cannot be before me"
	
	"Should it just be my next? => Insert it"
	(next isNil or: [aCriterion value: aNode element value: next element])
		ifTrue: [
			aNode setNext: next.
			next := aNode.
			^ self ].
	
	"Else recurse and ask each node to test"
	^ next insertNode: aNode sortedBy: aCriterion
]

{ #category : #accessing }
VMLinkedListNode >> lastNode [
	
	next isNil ifTrue: [ ^ self ].
	^ next lastNode
]

{ #category : #accessing }
VMLinkedListNode >> next [

	^ next
]

{ #category : #testing }
VMLinkedListNode >> nodeIncludes: anObject [
	
	element = anObject ifTrue: [ ^ true ].
	next ifNil: [ ^ false ].
	^ next nodeIncludes: anObject
]

{ #category : #accessing }
VMLinkedListNode >> setElement: anObject [

	element := anObject
]

{ #category : #accessing }
VMLinkedListNode >> setNext: anObject [

	next := anObject
]
