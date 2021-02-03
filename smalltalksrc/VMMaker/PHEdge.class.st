Class {
	#name : #PHEdge,
	#superclass : #VMStructType,
	#instVars : [
		'from',
		'to',
		'weight'
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

{ #category : #accessing }
PHEdge >> to [
	^ to
]

{ #category : #accessing }
PHEdge >> to: anObject [
	to := anObject
]

{ #category : #accessing }
PHEdge >> weight [
	^ weight
]

{ #category : #accessing }
PHEdge >> weight: anObject [
"self haltIf: [ anObject isNil ]."
	weight := anObject
]
