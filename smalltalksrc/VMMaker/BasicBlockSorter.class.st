Class {
	#name : #BasicBlockSorter,
	#superclass : #VMClass,
	#category : #'VMMaker-JIT'
}

{ #category : #sorting }
BasicBlockSorter >> sort: aListOfBasicBlocks [

	self subclassResponsibility 
]
