Class {
	#name : #VMSistaJITCounterTest,
	#superclass : #VMJitMethodTest,
	#category : #'VMMakerTests-SistaJIT'
}

{ #category : #'tests-counterarray' }
VMSistaJITCounterTest >> assertAllocatedCountersOf: aNativeMethod equals: aNumber [

	"In 64 bits, counters still take 32 bits.
	So an odd number of counters still allocate an even number of counters"
	self
		assert: (cogit objectRepresentation numCountersFor: aNativeMethod counters)
		equals: ((aNumber * 4 "bytes taken per counter") roundUpTo: memory wordSize) / 4
]

{ #category : #'tests-counterarray' }
VMSistaJITCounterTest >> createMethodOopFromPharoMethod: aPharoCompiledMethod [

	| methodOop |
	v3Method := aPharoCompiledMethod methodClass compiler
		            encoderClass: EncoderForSistaV1;
		            options: #( + optionFullBlockClosure );
		            compile: aPharoCompiledMethod sourceCode.

	methodOop := methodBuilder
		             fillFromPharoMethod: v3Method;
		             buildMethod.
	^ methodOop
]

{ #category : #'as yet unclassified' }
VMSistaJITCounterTest >> emptyMethod [

	"Nothing. We are compiling this method in the test"
]

{ #category : #running }
VMSistaJITCounterTest >> jitCompilerClass [

	^ SistaCogit
]

{ #category : #running }
VMSistaJITCounterTest >> jitOptions [

	^ super jitOptions
		at: #SistaVM put: true;
		at: #MULTIPLEBYTECODESETS put: true;
		at: #bytecodeTableInitializer put: #initializeBytecodeTableForSqueakV3PlusClosuresSistaV1Hybrid;
		yourself
]

{ #category : #'as yet unclassified' }
VMSistaJITCounterTest >> methodWithAnd: a [

	| return |
	return := a and: [ 17 = a ].
	^ return
]

{ #category : #'as yet unclassified' }
VMSistaJITCounterTest >> methodWithAndAndJump: a [

	(a and: [ a ]) ifTrue: [ ^ 5 ].
	^ 12
]

{ #category : #'as yet unclassified' }
VMSistaJITCounterTest >> methodWithNonConditionalFollowedByConditional: a [

	| result |
	result := a
		ifTrue: [ 5 ]
		ifFalse: [ 17 ].
	
	a ifTrue: [ ^ result ].
	^ nil
]

{ #category : #'as yet unclassified' }
VMSistaJITCounterTest >> methodWithOr: a [

	^ a or: [ 17 = a ]
]

{ #category : #'as yet unclassified' }
VMSistaJITCounterTest >> methodWithSingleJump: a [

	a ifTrue: [ ^ 5 ].
	^ 12
]

{ #category : #'as yet unclassified' }
VMSistaJITCounterTest >> methodWithTwoJumps: a [

	a ifTrue: [ ^ 5 ].
	a ifTrue: [ ^ 5 ].
	^ 12
]

{ #category : #running }
VMSistaJITCounterTest >> newInterpreter [

	| theMemory |
	theMemory := self newMemory.

	CogVMSimulatorLSB
		initializeWithOptions: {
			#BytesPerWord. 8.
			#ObjectMemory. theMemory class name.
			#SistaVM. true.
			#MULTIPLEBYTECODESETS. true.
			#bytecodeTableInitializer. #initializeBytecodeTableForSqueakV3PlusClosuresSistaV1Hybrid}
		objectMemoryClass: theMemory class.
		
	^ CogVMSimulatorLSB basicNew
		objectMemory: theMemory;
		basicInitialize
]

{ #category : #'as yet unclassified' }
VMSistaJITCounterTest >> setUp [

	super setUp.
	cogit initializeInitialCounterValue.
	self setUpTrampolines
]

{ #category : #'tests-counterincrement' }
VMSistaJITCounterTest >> testCounterOfMethodWithAndAndJumpDoesNotIncrementReachedOfAnd [
	
	| nativeMethod picData andCounter |
	self setArrayClassIntoClassTable.
	nativeMethod := self jitMethod: (self class>>#methodWithAndAndJump:).
	
	self 
		callCogMethod: nativeMethod
		receiver: memory nilObject 
		arguments:  { memory trueObject }
		returnAddress: callerAddress.
	
	picData := interpreter picDataFor: nativeMethod.
	self assert: (memory numSlotsOf: picData) equals: 2.
	
	andCounter := memory fetchPointer: 0 ofObject: picData.
	self assert: (memory integerValueOf: (memory fetchPointer: 1 ofObject: andCounter)) equals: 0
]

{ #category : #'tests-counterincrement' }
VMSistaJITCounterTest >> testCounterOfMethodWithAndAndJumpIncrementsReachedOfJump [
	
	| nativeMethod picData jumpCounter |
	self setArrayClassIntoClassTable.
	nativeMethod := self jitMethod: (self class>>#methodWithAndAndJump:).
	
	self 
		callCogMethod: nativeMethod
		receiver: memory nilObject 
		arguments:  { memory trueObject }
		returnAddress: callerAddress.
	
	picData := interpreter picDataFor: nativeMethod.
	self assert: (memory numSlotsOf: picData) equals: 2.
	
	jumpCounter := memory fetchPointer: 1 ofObject: picData.
	self assert: (memory integerValueOf: (memory fetchPointer: 1 ofObject: jumpCounter)) equals: 1
]

{ #category : #'tests-counterincrement' }
VMSistaJITCounterTest >> testCounterOfMethodWithNonConditionalFollowedByConditionalIncrementsNonTakenOfFirst [
	
	| nativeMethod picData lastJumpCounter |
	self setArrayClassIntoClassTable.
	nativeMethod := self jitMethod: (self class>>#methodWithNonConditionalFollowedByConditional:).
	
	self 
		callCogMethod: nativeMethod
		receiver: memory nilObject 
		arguments:  { memory trueObject }
		returnAddress: callerAddress.
	
	picData := interpreter picDataFor: nativeMethod.
	self assert: (memory numSlotsOf: picData) equals: 2.
	
	lastJumpCounter := memory fetchPointer: 0 ofObject: picData.
	self assert: (memory integerValueOf: (memory fetchPointer: 0 ofObject: lastJumpCounter)) equals: 1
]

{ #category : #'tests-counterincrement' }
VMSistaJITCounterTest >> testCounterOfMethodWithNonConditionalFollowedByConditionalIncrementsNonTakenOfLast [
	
	| nativeMethod picData lastJumpCounter |
	self setArrayClassIntoClassTable.
	nativeMethod := self jitMethod: (self class>>#methodWithNonConditionalFollowedByConditional:).
	
	self 
		callCogMethod: nativeMethod
		receiver: memory nilObject 
		arguments:  { memory trueObject }
		returnAddress: callerAddress.
	
	picData := interpreter picDataFor: nativeMethod.
	self assert: (memory numSlotsOf: picData) equals: 2.
	
	lastJumpCounter := memory fetchPointer: 1 ofObject: picData.
	self assert: (memory integerValueOf: (memory fetchPointer: 0 ofObject: lastJumpCounter)) equals: 1
]

{ #category : #'tests-counterincrement' }
VMSistaJITCounterTest >> testCounterOfMethodWithNonConditionalFollowedByConditionalIncrementsReachedOfFirst [
	
	| nativeMethod picData lastJumpCounter |
	self setArrayClassIntoClassTable.
	nativeMethod := self jitMethod: (self class>>#methodWithNonConditionalFollowedByConditional:).
	
	self 
		callCogMethod: nativeMethod
		receiver: memory nilObject 
		arguments:  { memory trueObject }
		returnAddress: callerAddress.
	
	picData := interpreter picDataFor: nativeMethod.
	self assert: (memory numSlotsOf: picData) equals: 2.
	
	lastJumpCounter := memory fetchPointer: 0 ofObject: picData.
	self assert: (memory integerValueOf: (memory fetchPointer: 1 ofObject: lastJumpCounter)) equals: 1
]

{ #category : #'tests-counterincrement' }
VMSistaJITCounterTest >> testCounterOfMethodWithNonConditionalFollowedByConditionalIncrementsReachedOfLast [
	
	| nativeMethod picData lastJumpCounter |
	self setArrayClassIntoClassTable.
	nativeMethod := self jitMethod: (self class>>#methodWithNonConditionalFollowedByConditional:).
	
	self 
		callCogMethod: nativeMethod
		receiver: memory nilObject 
		arguments:  { memory trueObject }
		returnAddress: callerAddress.
	
	picData := interpreter picDataFor: nativeMethod.
	self assert: (memory numSlotsOf: picData) equals: 2.
	
	lastJumpCounter := memory fetchPointer: 1 ofObject: picData.
	self assert: (memory integerValueOf: (memory fetchPointer: 1 ofObject: lastJumpCounter)) equals: 1
]

{ #category : #'tests-counterincrement' }
VMSistaJITCounterTest >> testCounterOfMethodWithOneJumpDoesNotIncrementNonTaken [
	
	| nativeMethod picData jumpCounter |
	self setArrayClassIntoClassTable.
	nativeMethod := self jitMethod: (self class>>#methodWithSingleJump:).
	
	self 
		callCogMethod: nativeMethod
		receiver: memory nilObject 
		arguments:  { memory falseObject }
		returnAddress: callerAddress.
	
	picData := interpreter picDataFor: nativeMethod.
	self assert: (memory numSlotsOf: picData) equals: 1.
	jumpCounter := memory fetchPointer: 0 ofObject: picData.
	
	self assert: (memory integerValueOf: (memory fetchPointer: 2 "non taken" ofObject: jumpCounter)) equals: 0
]

{ #category : #'tests-counterincrement' }
VMSistaJITCounterTest >> testCounterOfMethodWithOneJumpIncrementsNonTaken [
	
	| nativeMethod picData jumpCounter |
	self setArrayClassIntoClassTable.
	nativeMethod := self jitMethod: (self class>>#methodWithSingleJump:).
	
	self 
		callCogMethod: nativeMethod
		receiver: memory nilObject 
		arguments:  { memory trueObject }
		returnAddress: callerAddress.
	
	picData := interpreter picDataFor: nativeMethod.
	self assert: (memory numSlotsOf: picData) equals: 1.
	jumpCounter := memory fetchPointer: 0 ofObject: picData.
	
	self assert: (memory integerValueOf: (memory fetchPointer: 2 "non taken" ofObject: jumpCounter)) equals: 1
]

{ #category : #'tests-counterincrement' }
VMSistaJITCounterTest >> testCounterOfMethodWithOneJumpIncrementsReached [
	
	| nativeMethod picData jumpCounter |
	self setArrayClassIntoClassTable.
	nativeMethod := self jitMethod: (self class>>#methodWithSingleJump:).
	
	self 
		callCogMethod: nativeMethod
		receiver: memory nilObject 
		arguments:  { memory trueObject }
		returnAddress: callerAddress.
	
	picData := interpreter picDataFor: nativeMethod.
	self assert: (memory numSlotsOf: picData) equals: 1.
	jumpCounter := memory fetchPointer: 0 ofObject: picData.
	
	self assert: (memory integerValueOf: (memory fetchPointer: 1 ofObject: jumpCounter)) equals: 1
]

{ #category : #'tests-counterarray' }
VMSistaJITCounterTest >> testMethodCounterInitialValue [
	
	| nativeMethod |
	nativeMethod := self jitMethod: (self class>>#methodWithSingleJump:).

	self deny: nativeMethod counters equals: memory nilObject.

	self
		assert: (memory long32At: nativeMethod counters)
		equals: 16rFFFFFFFF "32-bits full of ones"
]

{ #category : #'tests-counterarray' }
VMSistaJITCounterTest >> testMethodWithAndHasNoCounters [
	
	| nativeMethod |
	nativeMethod := self jitMethod: (self class>>#methodWithAnd:).

	self deny: nativeMethod counters equals: memory nilObject.

	self assertAllocatedCountersOf: nativeMethod equals: 1
]

{ #category : #'tests-counterarray' }
VMSistaJITCounterTest >> testMethodWithNonConditionalFollowedByConditional [
	
	| nativeMethod |
	nativeMethod := self jitMethod: (self class>>#methodWithNonConditionalFollowedByConditional:).

	self deny: nativeMethod counters equals: memory nilObject.

	self
		assert: (cogit objectRepresentation numCountersFor: nativeMethod counters)
		equals: 2
]

{ #category : #'tests-counterarray' }
VMSistaJITCounterTest >> testMethodWithOneJumpHasOneCounters [
	
	| nativeMethod |
	nativeMethod := self jitMethod: (self class>>#methodWithSingleJump:).

	self deny: nativeMethod counters equals: memory nilObject.

	self
		assert: (cogit objectRepresentation numCountersFor: nativeMethod counters)
		equals: ((1 * 4 "bytes taken per counter") roundUpTo: memory wordSize) / 4
]

{ #category : #'tests-counterarray' }
VMSistaJITCounterTest >> testMethodWithOrHasNoCounters [
	
	| nativeMethod |
	nativeMethod := self jitMethod: (self class>>#methodWithOr:).

	self deny: nativeMethod counters equals: memory nilObject.

	self assertAllocatedCountersOf: nativeMethod equals: 1
]

{ #category : #'tests-counterarray' }
VMSistaJITCounterTest >> testMethodWithTwoJumpHasTwoCounters [
	
	| nativeMethod |
	nativeMethod := self jitMethod: (self class>>#methodWithTwoJumps:).

	self deny: nativeMethod counters equals: memory nilObject.

	self
		assert: (cogit objectRepresentation numCountersFor: nativeMethod counters)
		equals: 2
]

{ #category : #'tests-counterarray' }
VMSistaJITCounterTest >> testMethodWithoutJumpsHasNoCounters [
	
	| nativeMethod |
	nativeMethod := self jitMethod: (self class>>#emptyMethod).
	
	self assert: nativeMethod counters equals: 0
]

{ #category : #'tests-picdata' }
VMSistaJITCounterTest >> testPicDataForMethodWithAnd [
	
	| nativeMethod picData |
	self setArrayClassIntoClassTable.
	nativeMethod := self jitMethod: (self class>>#methodWithAnd:).
	
	picData := interpreter picDataFor: nativeMethod.
	
	self assert: (memory numSlotsOf: picData) equals: 0
]

{ #category : #'tests-picdata' }
VMSistaJITCounterTest >> testPicDataForMethodWithAndAndJumpHasOneCounters [
	
	| nativeMethod picData |
	self setArrayClassIntoClassTable.
	nativeMethod := self jitMethod: (self class>>#methodWithAndAndJump:).

	picData := interpreter picDataFor: nativeMethod.
	
	self assert: (memory numSlotsOf: picData) equals: 1
]

{ #category : #'tests-picdata' }
VMSistaJITCounterTest >> testPicDataForMethodWithNoCounters [
	
	| nativeMethod picData |
	self setArrayClassIntoClassTable.
	nativeMethod := self jitMethod: (self class>>#emptyMethod).
	
	picData := interpreter picDataFor: nativeMethod.
	
	self assert: picData equals: 0
]

{ #category : #'tests-picdata' }
VMSistaJITCounterTest >> testPicDataForMethodWithNonConditionalFollowedByConditional [
	
	| nativeMethod picData |
	self setArrayClassIntoClassTable.
	nativeMethod := self jitMethod: (self class>>#methodWithNonConditionalFollowedByConditional:).
	
	picData := interpreter picDataFor: nativeMethod.
	
	self assert: (memory numSlotsOf: picData) equals: 2
]

{ #category : #'tests-picdata' }
VMSistaJITCounterTest >> testPicDataForMethodWithOneJump [
	
	| nativeMethod picData |
	self setArrayClassIntoClassTable.
	nativeMethod := self jitMethod: (self class>>#methodWithSingleJump:).
	
	picData := interpreter picDataFor: nativeMethod.
	
	self assert: (memory numSlotsOf: picData) equals: 1
]

{ #category : #'tests-picdata' }
VMSistaJITCounterTest >> testPicDataForMethodWithOr [
	
	| nativeMethod picData |
	self setArrayClassIntoClassTable.
	nativeMethod := self jitMethod: (self class>>#methodWithOr:).
	
	picData := interpreter picDataFor: nativeMethod.
	
	self assert: (memory numSlotsOf: picData) equals: 0
]

{ #category : #'tests-picdata' }
VMSistaJITCounterTest >> testPicDataForMethodWithTwoJumps [
	
	| nativeMethod picData |
	self setArrayClassIntoClassTable.
	nativeMethod := self jitMethod: (self class>>#methodWithTwoJumps:).
	
	picData := interpreter picDataFor: nativeMethod.
	
	self assert: (memory numSlotsOf: picData) equals: 2
]

{ #category : #'tests-counterarray' }
VMSistaJITCounterTest >> testUnusedCounterInitialValue [
	
	| nativeMethod |
	nativeMethod := self jitMethod: (self class>>#methodWithAnd:).

	self deny: nativeMethod counters equals: memory nilObject.

	self
		assert: (memory long32At: nativeMethod counters)
		equals: 16rFFFFFFFF "32-bits full of ones"
]
