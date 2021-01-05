Class {
	#name : #PHBasicBlockMock,
	#superclass : #Object,
	#instVars : [
		'successors',
		'name'
	],
	#category : #'VMMakerTests-BasicBlocks'
}

{ #category : #'as yet unclassified' }
PHBasicBlockMock class >> named: aString [ 
	
	^ self new
		name: aString;
		yourself
]

{ #category : #'as yet unclassified' }
PHBasicBlockMock >> id [

	^ name
]

{ #category : #accessing }
PHBasicBlockMock >> initialize [

	super initialize.
	successors := #()
]

{ #category : #'as yet unclassified' }
PHBasicBlockMock >> name: aString [ 
	
	name := aString
]

{ #category : #accessing }
PHBasicBlockMock >> printOn: aStream [

	aStream
		nextPutAll: self class name;
		nextPutAll: '(';
		print: name;
		nextPutAll: ')'
]

{ #category : #accessing }
PHBasicBlockMock >> successors [
	^ successors
]

{ #category : #accessing }
PHBasicBlockMock >> successors: anObject [
	successors := anObject
]
