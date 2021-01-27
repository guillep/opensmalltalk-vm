Class {
	#name : #VMProcessLinkedList,
	#superclass : #VMMockObject,
	#instVars : [
		'firstLink',
		'lastLink'
	],
	#category : #'VMMaker-MT-Tests'
}

{ #category : #accessing }
VMProcessLinkedList >> add: aProcess [
	self haltIf: [ aProcess isInteger ].
	firstLink
		ifNil: [ firstLink := aProcess]
		ifNotNil: [ lastLink nextLink: aProcess ].
	lastLink := aProcess.
	^ aProcess
]
