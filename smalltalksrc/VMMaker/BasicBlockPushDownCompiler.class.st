Class {
	#name : #BasicBlockPushDownCompiler,
	#superclass : #BasicBlockCompiler,
	#category : #'VMMaker-JIT'
}

{ #category : #translation }
BasicBlockPushDownCompiler class >> sorterClasses [

	^ { PushDownBlockSorter }
]
