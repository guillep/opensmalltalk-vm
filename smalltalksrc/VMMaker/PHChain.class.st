Class {
	#name : #PHChain,
	#superclass : #Object,
	#instVars : [
		'priority',
		'blocks'
	],
	#category : #'VMMaker-JIT'
}

{ #category : #'as yet unclassified' }
PHChain class >> with: aPHBasicBlockMock [ 
	
	^ self new
		initializeWithBlock: aPHBasicBlockMock;
		yourself
]

{ #category : #'as yet unclassified' }
PHChain >> append: aPHChain [ 
	
	blocks := blocks , aPHChain blocks
]

{ #category : #'as yet unclassified' }
PHChain >> blocks [
	^ blocks
]

{ #category : #'as yet unclassified' }
PHChain >> head [
	
	^ blocks first
]

{ #category : #'as yet unclassified' }
PHChain >> initializeWithBlock: aPHBasicBlockMock [ 
	
	priority := 1000.
	blocks := { aPHBasicBlockMock }
]

{ #category : #printing }
PHChain >> printOn: aStream [

	aStream
		nextPutAll: self class name;
		nextPutAll: '('.
	
	blocks do: [ :b | aStream print: b id ]  separatedBy: [ aStream nextPut: $, ].
	
	aStream nextPutAll: ')'
]

{ #category : #'as yet unclassified' }
PHChain >> priority [
	^ priority
]

{ #category : #'as yet unclassified' }
PHChain >> priority: anInteger [ 
	priority := anInteger
]

{ #category : #'as yet unclassified' }
PHChain >> tail [
	
	^ blocks last
]
