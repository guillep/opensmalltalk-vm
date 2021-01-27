Class {
	#name : #VMLinkedListNode,
	#superclass : #Object,
	#instVars : [
		'value',
		'next'
	],
	#category : #'VMMaker-Support'
}

{ #category : #testing }
VMLinkedListNode >> includes: anObject [
	
	value = anObject ifTrue: [ ^ true ].
	next ifNil: [ ^ false ].
	^ next includes: anObject
]

{ #category : #inserting }
VMLinkedListNode >> insertNode: aNode sortedBy: aCriterion [
	
	"Check if the object should be inserted 
	- just after me, 
	- else after some of my next nodes
	
	Assummption: the object cannot be before me"
	
	"Should it just be my next? => Insert it"
	(next isNil or: [aCriterion value: aNode value value: next value])
		ifTrue: [
			aNode next: next.
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

{ #category : #accessing }
VMLinkedListNode >> next: anObject [

	next := anObject
]

{ #category : #accessing }
VMLinkedListNode >> value [

	^ value
]

{ #category : #accessing }
VMLinkedListNode >> value: anObject [

	value := anObject
]
