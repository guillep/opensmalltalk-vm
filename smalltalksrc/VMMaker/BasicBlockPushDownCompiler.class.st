Class {
	#name : #BasicBlockPushDownCompiler,
	#superclass : #BasicBlockCompiler,
	#category : #'VMMaker-JIT'
}

{ #category : #translation }
BasicBlockPushDownCompiler class >> sorterClasses [

	^ { PushDownBlockSorter }
]

{ #category : #initialization }
BasicBlockPushDownCompiler >> initialize [
	<doNotGenerate>
	super initialize.
	sorter := PushDownBlockSorter new
]
