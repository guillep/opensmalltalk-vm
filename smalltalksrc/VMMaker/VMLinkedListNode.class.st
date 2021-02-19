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
	<var: #anObject type: #'void *'>
	element = anObject ifTrue: [ ^ true ].
	next ifNil: [ ^ false ].
	^ next nodeIncludes: anObject
]

{ #category : #accessing }
VMLinkedListNode >> setElement: anObject [
<var: #anObject type: #'void *'>
	element := anObject
]

{ #category : #accessing }
VMLinkedListNode >> setNext: anObject [
	<var: #aVMLinkedListNode type: #'LinkedListNode *'>
	next := anObject
]
