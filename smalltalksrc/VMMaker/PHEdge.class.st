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

{ #category : #translation }
PHEdge class >> instVarNamesAndTypesForTranslationDo: aBinaryBlock [

	self filteredInstVarNames do:
		[:ivn|
		aBinaryBlock
			value: ivn
			value: (ivn caseOf: {
						['from']			-> [#'BasicBlock *'].
						['to']				-> [#'BasicBlock *'].
						['weight']		-> [#usqInt]})]
]

{ #category : #accessing }
PHEdge >> from [
	^ from
]

{ #category : #accessing }
PHEdge >> from: anObject [
	from := anObject
]

{ #category : #printing }
PHEdge >> printOn: aStream [

	aStream
		nextPutAll: 'PHEdge(from=';
		print: from id;
		nextPutAll: ', to=';
		print: to id;
		nextPutAll: ', weight=';
		print: weight;
		nextPut: $)
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
