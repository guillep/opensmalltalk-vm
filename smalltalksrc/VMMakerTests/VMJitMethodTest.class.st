Class {
	#name : #VMJitMethodTest,
	#superclass : #VMPrimitiveCallAbstractTest,
	#pools : [
		'CogRTLOpcodes'
	],
	#category : #'VMMakerTests-JitTests'
}

{ #category : #'building suites' }
VMJitMethodTest class >> testParameters [

	^ super testParameters * 
		(ParametrizedTestMatrix new
			addCase: { 
				#jitCompilerClass -> BasicBlockCompiler.
				#bytecodeEncoderClass -> EncoderForSistaV1 };
			addCase: { #jitCompilerClass -> StackToRegisterMappingCogit };
			yourself)
]

{ #category : #tests }
VMJitMethodTest >> comparingSmallIntegers: aBitmap [

	aBitmap size = 32768 ifTrue: [ ^ 17 ].
	^ 23
]

{ #category : #tests }
VMJitMethodTest >> ifTrueIfFalseWithUnknownReceiver: aReceiver [

	^ aReceiver ifTrue: [ 42 ] ifFalse: [ 17 ]
]

{ #category : #running }
VMJitMethodTest >> initialCodeSize [

	^ 16 * 1024
]

{ #category : #running }
VMJitMethodTest >> initializeSpecialSelectors [

	| specialSelectorsArrayOop |
	specialSelectorsArrayOop := self newOldSpaceObjectWithSlots:
		                            Smalltalk specialSelectors size.

	Smalltalk specialSelectors withIndexDo: [ :anElement :anIndex | 
		memory
			storePointer: anIndex - 1
			ofObject: specialSelectorsArrayOop
			withValue: (anElement forMemory: memory) ].
		
	memory splObj: SpecialSelectors put: specialSelectorsArrayOop
]

{ #category : #tests }
VMJitMethodTest >> jitOptions [ 

	^ super jitOptions 
		at: #MULTIPLEBYTECODESETS put: true;
		at: #bytecodeTableInitializer put: #initializeBytecodeTableForSqueakV3PlusClosuresSistaV1Hybrid;
		yourself
]

{ #category : #running }
VMJitMethodTest >> setUp [ 

	super setUp.
	self initializeSpecialSelectors
]

{ #category : #tests }
VMJitMethodTest >> setUpClosedPICPrototype [

	"Nothing for now"
	self flag: #undooo
]

{ #category : #running }
VMJitMethodTest >> setUpTrampolines [

	super setUpTrampolines.
	
	cogit ceSendMustBeBooleanAddFalseTrampoline: (self compileTrampoline: [ cogit RetN: 0 ] named:#ceSendMustBeBooleanAddFalseTrampoline).
	cogit ceSendMustBeBooleanAddTrueTrampoline: (self compileTrampoline: [ cogit RetN: 0 ] named:#ceSendMustBeBooleanAddTrueTrampoline).

	cogit ceCheckForInterruptTrampoline: (self compileTrampoline: [ cogit RetN: 0 ] named:#ceCheckForInterruptTrampoline)
]

{ #category : #tests }
VMJitMethodTest >> testComparingSmallIntegersThatNotFit [
	| callingMethod parameter aSize bytesPerSlot desiredByteSize numberOfWordSizeSlots padding |
	
	aSize := 32768.
	bytesPerSlot := 1.
	desiredByteSize := aSize * bytesPerSlot roundUpTo: self wordSize.
	numberOfWordSizeSlots := desiredByteSize / self wordSize.
	padding := desiredByteSize / bytesPerSlot - aSize.

	parameter := memory
		  allocateSlots: numberOfWordSizeSlots
		  format: memory firstByteFormat + padding
		  classIndex: self nextOrdinaryClassIndex.

	"We replace the sendTrampoline to simulate the message send of #size"
	sendTrampolineAddress := self compileTrampoline: [ 
		cogit MoveCq: (memory integerObjectOf: 32768) R: ReceiverResultReg.
		cogit RetN:0 ] named: #send0argsTrampoline.
	
	cogit ordinarySendTrampolineAt: 0 "args" put: sendTrampolineAddress.
		
	callingMethod := self jitMethod: (self findMethod: #comparingSmallIntegers:).
		
	self 
		callCogMethod: callingMethod 
		receiver: memory nilObject 
		arguments:  { parameter }
		returnAddress: callerAddress.
	
	self 
		assert: (memory integerValueOf: machineSimulator receiverRegisterValue)
		equals: 17
]

{ #category : #tests }
VMJitMethodTest >> testIfTrueIfFalseWithUnknownFalseReceiver [
	
	| method |
	method := self jitMethod: (self findMethod: #ifTrueIfFalseWithUnknownReceiver:).
	
	self 
		callCogMethod: method
		receiver: memory nilObject 
		arguments:  { memory falseObject }
		returnAddress: callerAddress.

	self 
		assert: (memory integerValueOf: machineSimulator receiverRegisterValue)
		equals: 17
]

{ #category : #tests }
VMJitMethodTest >> testIfTrueIfFalseWithUnknownTrueReceiver [
	
	| method |
	method := self jitMethod: (self findMethod: #ifTrueIfFalseWithUnknownReceiver:).
	
	self 
		callCogMethod: method
		receiver: memory nilObject 
		arguments:  { memory trueObject }
		returnAddress: callerAddress.
	
	self 
		assert: (memory integerValueOf: machineSimulator receiverRegisterValue)
		equals: 42
]

{ #category : #tests }
VMJitMethodTest >> testMixedInlinedLiteralsSmokeTest [
	| callingMethod |
	
	callingMethod := self jitMethod: (FreeTypeSubPixelAntiAliasedGlyphRenderer>>#filter:).
	
	self deny: callingMethod address equals: 0.
]

{ #category : #tests }
VMJitMethodTest >> testToDo [
	
	| method |
	method := self jitMethod: (self findMethod: #todo).
	
	self 
		callCogMethod: method
		receiver: memory nilObject 
		arguments:  { }
		returnAddress: callerAddress.
		
	self 
		assert: (memory integerValueOf: machineSimulator receiverRegisterValue)
		equals: 15
]

{ #category : #tests }
VMJitMethodTest >> testWhileSingleLoop [
	
	| method |
	method := self jitMethod: (self findMethod: #whileSingleLoop).
	
	self 
		callCogMethod: method
		receiver: memory nilObject 
		arguments:  { }
		returnAddress: callerAddress.
		
	self halt.

	self 
		assert: (memory integerValueOf: machineSimulator receiverRegisterValue)
		equals: 1
]

{ #category : #tests }
VMJitMethodTest >> todo [

	| accumulator |
	accumulator := 0.
	1 to: 5 do: [ :i |
		accumulator := accumulator + i ].
	^ accumulator
]

{ #category : #tests }
VMJitMethodTest >> whileSingleLoop [

	| accumulator |
	accumulator := 0.
	[ accumulator := accumulator + 1. false ] whileTrue.
	^ accumulator
]
