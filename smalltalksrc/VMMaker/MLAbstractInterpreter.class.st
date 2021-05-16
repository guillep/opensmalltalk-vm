Class {
	#name : #MLAbstractInterpreter,
	#superclass : #VMClass,
	#instVars : [
		'objectMemory',
		'currentBytecode',
		'localIP',
		'instructionPointer',
		'stackPointer',
		'localSP',
		'framePointer',
		'localFP'
	],
	#classVars : [
		'BytecodeTable'
	],
	#category : #'VMMaker-Interpreter'
}

{ #category : #initialization }
MLAbstractInterpreter class >> additionalHeadersDo: aBinaryBlock [

	"Evaluate aBinaryBlock with the names and contents of
	 any additional header files that need to be generated."

	"Do nothing by default"
]

{ #category : #initialization }
MLAbstractInterpreter class >> additionalSelectorTables [
	
	^ #()
]

{ #category : #initialization }
MLAbstractInterpreter class >> bytecodeMappings [

	self subclassResponsibility.
]

{ #category : #initialization }
MLAbstractInterpreter class >> initializeBytecodeTable [

	BytecodeTable := Array new: self numberOfBytecodes.
	self table: BytecodeTable from: self bytecodeMappings
]

{ #category : #testing }
MLAbstractInterpreter class >> isInterpreterClass [

	^true
]

{ #category : #initialization }
MLAbstractInterpreter class >> numberOfBytecodes [

	self subclassResponsibility
]

{ #category : #initialization }
MLAbstractInterpreter class >> preGenerationHook: aCCodeGen [
	"Hook: 
	
	Perform any last-minute changes to the code generator immediately
	before it performs code analysis and generation "
	
]

{ #category : #initialization }
MLAbstractInterpreter class >> preambleCCode [

	"Defining this method to answer a string dumps that string in VMPluginCodeGenerator>>emitCHeaderOn:"
	
	^nil
]

{ #category : #accessing }
MLAbstractInterpreter class >> sourceFileName [
	"Default name"
	^ 'interpreter.c'
]

{ #category : #initialization }
MLAbstractInterpreter class >> table: anArray from: specArray [ 
	"SpecArray is an array of one of (index selector) or (index1 
	 index2 selector) or (index nil) or (index1 index2 nil).  If selector
	 then the entry is the selector, but if nil the entry is the index."
	| contiguous |
	contiguous := 0.
	specArray do:
		[:spec | 
		(spec at: 1) = contiguous ifFalse:
			[self error: 'Non-contiguous table entry'].
		spec size = 2
			ifTrue:
				[anArray
					at: (spec at: 1) + 1
					put: ((spec at: 2) ifNil: [spec at: 1] ifNotNil: [:sym| sym]).
				 contiguous := contiguous + 1]
			ifFalse:
				[(spec at: 1) to: (spec at: 2) do:
					[:i | anArray at: i + 1 put: ((spec at: 3) ifNil: [i] ifNotNil: [:sym| sym])].
				 contiguous := contiguous + ((spec at: 2) - (spec at: 1)) + 1]].
	anArray doWithIndex:
		[:entry :index|
		entry isSymbol ifTrue:
			[(self shouldIncludeMethodForSelector: entry) ifFalse:
				[anArray at: index put: 0]]]
]

{ #category : #'interpreter shell' }
MLAbstractInterpreter >> dispatchOn: anInteger in: selectorArray [
	"Simulate a case statement via selector table lookup.
	The given integer must be between 0 and selectorArray size-1, inclusive.
	For speed, no range test is done, since it is done by the at: operation.
	Note that, unlike many other arrays used in the Interpreter, this method expect NO CArrayAccessor wrapping - it would duplicate the +1. Maybe this would be better updated to make it all uniform"
	<doNotGenerate>
	self perform: (selectorArray at: (anInteger + 1)).
]

{ #category : #'interpreter shell' }
MLAbstractInterpreter >> externalizeIPandSP [
	"Copy the local instruction, stack and frame pointers to global variables for use in primitives and other functions outside the interpret loop."

	instructionPointer := self oopForPointer: localIP.
	stackPointer := localSP.
	framePointer := localFP
]

{ #category : #'interpreter shell' }
MLAbstractInterpreter >> fetchByte [
	"This method uses the preIncrement builtin function which has no Smalltalk equivalent. Thus, it must be overridden in the simulator."

	^objectMemory byteAtPointer: localIP preIncrement
]

{ #category : #'interpreter shell' }
MLAbstractInterpreter >> fetchNextBytecode [
	"This method fetches the next instruction (bytecode). Each bytecode method is responsible for fetching the next bytecode, preferably as early as possible to allow the memory system time to process the request before the next dispatch."
	currentBytecode := self fetchByte
]

{ #category : #'interpreter shell' }
MLAbstractInterpreter >> internalizeIPandSP [
	"Copy the instruction, stack and frame pointers to local variables for rapid access within the interpret loop."
	localIP := self pointerForOop: instructionPointer.
	localSP := self pointerForOop: stackPointer.
	localFP := self pointerForOop: framePointer.
]

{ #category : #'interpreter shell' }
MLAbstractInterpreter >> interpret [
	"This is the main interpreter loop. It normally loops forever, fetching and executing bytecodes. When running in the context of a browser plugin VM, however, it must return control to the browser periodically. This should done only when the state of the currently running Squeak thread is safely stored in the object heap. Since this is the case at the moment that a check for interrupts is performed, that is when we return to the browser if it is time to do so. Interrupt checks happen quite frequently."

	<inline: false>
	self internalizeIPandSP.
	self fetchNextBytecode.
	[true] whileTrue: [self dispatchOn: currentBytecode in: BytecodeTable].
	localIP := localIP - 1.  "undo the pre-increment of IP before returning"
	self externalizeIPandSP.
	^nil

]
