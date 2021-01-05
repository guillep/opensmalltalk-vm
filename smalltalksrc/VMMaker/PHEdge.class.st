Class {
	#name : #PHEdge,
	#superclass : #Object,
	#instVars : [
		'from',
		'to'
	],
	#category : #'VMMaker-JIT'
}

{ #category : #accessing }
PHEdge >> from [
	^ from
]

{ #category : #accessing }
PHEdge >> from: anObject [
	from := anObject
]

{ #category : #'as yet unclassified' }
PHEdge >> priority [
	
	^ 10
]

{ #category : #accessing }
PHEdge >> to [
	^ to
]

{ #category : #accessing }
PHEdge >> to: anObject [
	to := anObject
]
