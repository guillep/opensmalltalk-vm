Class {
	#name : #VMSpurScavengeEphemeronTest,
	#superclass : #VMSpurInitializedOldSpaceTest,
	#category : #'VMMakerTests-MemoryTests'
}

{ #category : #'tests-ephemerons-globals' }
VMSpurScavengeEphemeronTest >> testDequeueMournerWithOnlyOneEphemeronShouldEmptyMournQueue [
	| ephemeronObjectOop nonEphemeronObjectOop |
	self createEphemeronClass.
	ephemeronObjectOop := self newEphemeronObject.
	nonEphemeronObjectOop := self newZeroSizedObject.
	memory
		storePointer: 0
		ofObject: ephemeronObjectOop
		withValue: nonEphemeronObjectOop.

	"Force object to not be collected by putting them in special variables"
	self keepObjectInVMVariable1: ephemeronObjectOop.

	memory gc doScavenge: 1.	"TenureByAge"
	ephemeronObjectOop := memory remapObj: ephemeronObjectOop.
	memory gc dequeueMourner.
	self assert: memory gc dequeueMourner equals: nil
	
]

{ #category : #'tests-ephemerons-globals' }
VMSpurScavengeEphemeronTest >> testNewEphemeronObjectShouldBeInstanceOfEphemeronClass [

	| ephemeronObjectOop |
	self createEphemeronClass.
	ephemeronObjectOop := self newEphemeronObject.

	self assert: (memory fetchClassOfNonImm: ephemeronObjectOop) equals: ourEphemeronClass
]

{ #category : #'tests-ephemerons-globals' }
VMSpurScavengeEphemeronTest >> testScavengeEphemeronInRememberdSetBecomesNormalObjectAfterFinalizationIsFired [
	| ephemeronObjectOop nonEphemeronObjectOop |
	self createEphemeronClass.
	ephemeronObjectOop := self newEphemeronObject.
	"Force object to not be collected by putting them in special variables"
	self keepObjectInVMVariable1: ephemeronObjectOop.
	"Move ephemeron to old space"
	memory gc flushNewSpace.
	ephemeronObjectOop := memory remapObj: ephemeronObjectOop.
	
	nonEphemeronObjectOop := self newZeroSizedObject.
	memory
		storePointer: 0
		ofObject: ephemeronObjectOop
		withValue: nonEphemeronObjectOop.
	
	memory gc doScavenge: 1.	"TenureByAge"
	self
		assert: (memory formatOf: ephemeronObjectOop)
		equals: memory nonIndexablePointerFormat
]

{ #category : #'tests-ephemerons-globals' }
VMSpurScavengeEphemeronTest >> testScavengeEphemeronInRememberedSetReferencingDyingObjectShouldBeAddedInTheMournQueue [
	| ephemeronObjectOop nonEphemeronObjectOop  |
	self createEphemeronClass.
	ephemeronObjectOop := self newEphemeronObject.
	"Force object to not be collected by putting them in special variables"
	self keepObjectInVMVariable1: ephemeronObjectOop.
	"Move ephemeron to old space"
	memory gc flushNewSpace.
	ephemeronObjectOop := memory remapObj: ephemeronObjectOop.

	nonEphemeronObjectOop := self newZeroSizedObject.
	memory
		storePointer: 0
		ofObject: ephemeronObjectOop
		withValue: nonEphemeronObjectOop.

	memory gc doScavenge: 1.	"TenureByAge"
	self
		assert: memory gc dequeueMourner
		equals: ephemeronObjectOop
]

{ #category : #'tests-ephemerons-globals' }
VMSpurScavengeEphemeronTest >> testScavengeEphemeronInRememberedSetReferencingDyingObjectShouldFireFinalization [
	| ephemeronObjectOop nonEphemeronObjectOop  oldFinalization |
	self createEphemeronClass.
	ephemeronObjectOop := self newEphemeronObject.
	"Force object to not be collected by putting them in special variables"
	self keepObjectInVMVariable1: ephemeronObjectOop.
	"Move ephemeron to old space"
	memory gc flushNewSpace.
	ephemeronObjectOop := memory remapObj: ephemeronObjectOop.

	nonEphemeronObjectOop := self newZeroSizedObject.
	oldFinalization := memory coInterpreter pendingFinalizationSignals.
	memory
		storePointer: 0
		ofObject: ephemeronObjectOop
		withValue: nonEphemeronObjectOop.

	"Force object to not be collected by putting them in special variables"
	self keepObjectInVMVariable1: ephemeronObjectOop.

	memory gc doScavenge: 1.	"TenureByAge"
	self
		assert: memory coInterpreter pendingFinalizationSignals
		equals: oldFinalization + 1
]

{ #category : #'tests-ephemerons-globals' }
VMSpurScavengeEphemeronTest >> testScavengeEphemeronInRememberedSetReferencingDyingObjectShouldScavengeEphemeronKey [
	| ephemeronObjectOop nonEphemeronObjectOop  nonEphemeronObjectHash |
	self createEphemeronClass.
	ephemeronObjectOop := self newEphemeronObject.
	"Force object to not be collected by putting them in special variables"
	self keepObjectInVMVariable1: ephemeronObjectOop.
	"Move ephemeron to old space"
	memory gc flushNewSpace.
	ephemeronObjectOop := memory remapObj: ephemeronObjectOop.

	nonEphemeronObjectOop := self newZeroSizedObject.
	nonEphemeronObjectHash := memory hashBitsOf: nonEphemeronObjectOop.
	memory
		storePointer: 0
		ofObject: ephemeronObjectOop
		withValue: nonEphemeronObjectOop.

	"Force object to not be collected by putting them in special variables"
	self keepObjectInVMVariable1: ephemeronObjectOop.

	memory gc doScavenge: 1.	"TenureByAge"
	self
		assert: (memory hashBitsOf: nonEphemeronObjectOop)
		equals: nonEphemeronObjectHash
]

{ #category : #'tests-ephemerons-globals' }
VMSpurScavengeEphemeronTest >> testScavengeEphemeronInRememberedSetReferencingSurvivorShouldLeaveEphemeronObjectAsIs [
	| ephemeronObjectOop nonEphemeronObjectOop nonEphemeronObjectHash |
	self createEphemeronClass.
	ephemeronObjectOop := self newEphemeronObject.
	"Force object to not be collected by putting them in special variables"
	self keepObjectInVMVariable1: ephemeronObjectOop.
	"Move ephemeron to old space"
	memory gc flushNewSpace.
	ephemeronObjectOop := memory remapObj: ephemeronObjectOop.

	nonEphemeronObjectOop := self newZeroSizedObject.
	nonEphemeronObjectHash := memory hashBitsOf: nonEphemeronObjectOop.
	memory
		storePointer: 0
		ofObject: ephemeronObjectOop
		withValue: nonEphemeronObjectOop.

	"Force object to not be collected by putting them in special variables"
	self keepObjectInVMVariable1: ephemeronObjectOop.
	self keepObjectInVMVariable2: nonEphemeronObjectOop.
	
	memory gc doScavenge: 1.	"TenureByAge"
	self
		assert: (memory hashBitsOf: (memory fetchPointer: 0 ofObject: ephemeronObjectOop))
		equals: nonEphemeronObjectHash
]

{ #category : #'tests-ephemerons-globals' }
VMSpurScavengeEphemeronTest >> testScavengeEphemeronObjectBecomesNormalObjectAfterFinalizationIsFired [
	| ephemeronObjectOop nonEphemeronObjectOop |
	self createEphemeronClass.
	ephemeronObjectOop := self newEphemeronObject.
	nonEphemeronObjectOop := self newZeroSizedObject.
	memory
		storePointer: 0
		ofObject: ephemeronObjectOop
		withValue: nonEphemeronObjectOop.

	"Force object to not be collected by putting them in special variables"
	self keepObjectInVMVariable1: ephemeronObjectOop.
	
	memory gc doScavenge: 1.	"TenureByAge"
	ephemeronObjectOop := memory remapObj: ephemeronObjectOop.
	self
		assert:
			(memory
				formatOf: ephemeronObjectOop)
		equals: memory nonIndexablePointerFormat
]

{ #category : #'tests-ephemerons-globals' }
VMSpurScavengeEphemeronTest >> testScavengeEphemeronObjectReferencingDyingObjectShouldBeAddedInTheMournQueue [
	| ephemeronObjectOop nonEphemeronObjectOop  |
	self createEphemeronClass.
	ephemeronObjectOop := self newEphemeronObject.
	nonEphemeronObjectOop := self newZeroSizedObject.
	memory
		storePointer: 0
		ofObject: ephemeronObjectOop
		withValue: nonEphemeronObjectOop.

	"Force object to not be collected by putting them in special variables"
	self keepObjectInVMVariable1: ephemeronObjectOop.

	memory gc doScavenge: 1.	"TenureByAge"
	ephemeronObjectOop := memory remapObj: ephemeronObjectOop.
	self
		assert: memory gc dequeueMourner
		equals: ephemeronObjectOop
]

{ #category : #'tests-ephemerons-globals' }
VMSpurScavengeEphemeronTest >> testScavengeEphemeronObjectReferencingDyingObjectShouldFireFinalization [
	| ephemeronObjectOop nonEphemeronObjectOop  oldFinalization |
	self createEphemeronClass.
	ephemeronObjectOop := self newEphemeronObject.
	nonEphemeronObjectOop := self newZeroSizedObject.
	oldFinalization := memory coInterpreter pendingFinalizationSignals.
	memory
		storePointer: 0
		ofObject: ephemeronObjectOop
		withValue: nonEphemeronObjectOop.

	"Force object to not be collected by putting them in special variables"
	self keepObjectInVMVariable1: ephemeronObjectOop.

	memory gc doScavenge: 1.	"TenureByAge"
	ephemeronObjectOop := memory remapObj: ephemeronObjectOop.
	self
		assert: memory coInterpreter pendingFinalizationSignals
		equals: oldFinalization + 1
]

{ #category : #'tests-ephemerons-globals' }
VMSpurScavengeEphemeronTest >> testScavengeEphemeronObjectReferencingDyingObjectShouldScavengeEphemeronKey [
	| ephemeronObjectOop nonEphemeronObjectOop  nonEphemeronObjectHash |
	self createEphemeronClass.
	ephemeronObjectOop := self newEphemeronObject.
	nonEphemeronObjectOop := self newZeroSizedObject.
	nonEphemeronObjectHash := memory hashBitsOf: nonEphemeronObjectOop.
	memory
		storePointer: 0
		ofObject: ephemeronObjectOop
		withValue: nonEphemeronObjectOop.

	"Force object to not be collected by putting them in special variables"
	self keepObjectInVMVariable1: ephemeronObjectOop.

	memory gc doScavenge: 1.	"TenureByAge"
	nonEphemeronObjectOop := memory remapObj: nonEphemeronObjectOop.
	self
		assert: (memory hashBitsOf: nonEphemeronObjectOop)
		equals: nonEphemeronObjectHash
]

{ #category : #'tests-ephemerons-globals' }
VMSpurScavengeEphemeronTest >> testScavengeEphemeronObjectReferencingSurvivorShouldLeaveEphemeronObjectAsIs [
	| ephemeronObjectOop nonEphemeronObjectOop nonEphemeronObjectHash |
	self createEphemeronClass.
	ephemeronObjectOop := self newEphemeronObject.
	nonEphemeronObjectOop := self newZeroSizedObject.
	nonEphemeronObjectHash := memory hashBitsOf: nonEphemeronObjectOop.
	memory
		storePointer: 0
		ofObject: ephemeronObjectOop
		withValue: nonEphemeronObjectOop.

	"Force object to not be collected by putting them in special variables"
	self keepObjectInVMVariable1: ephemeronObjectOop.
	self keepObjectInVMVariable2: nonEphemeronObjectOop.
	
	memory gc doScavenge: 1.	"TenureByAge"
	ephemeronObjectOop := memory remapObj: ephemeronObjectOop.
	self
		assert:
			(memory
				hashBitsOf: (memory fetchPointer: 0 ofObject: ephemeronObjectOop))
		equals: nonEphemeronObjectHash
]

{ #category : #'tests-ephemerons-globals' }
VMSpurScavengeEphemeronTest >> testScavengeTwoEphemeronObjectsReferencingDifferentDyingObjectsShouldBeAddedInTheMournQueueAfterScavengingInEden [
	| ephemeronObjectOop nonEphemeronObjectOop  anotherEphemeronObjectOop anotherNonEphemeronObjectOop |
	self createEphemeronClass.
	ephemeronObjectOop := self newEphemeronObject.
	anotherEphemeronObjectOop := self newEphemeronObject.
	nonEphemeronObjectOop := self newZeroSizedObject.
	anotherNonEphemeronObjectOop := self newZeroSizedObject.
	memory
		storePointer: 0
		ofObject: ephemeronObjectOop
		withValue: nonEphemeronObjectOop.
		
	memory
		storePointer: 0
		ofObject: anotherEphemeronObjectOop
		withValue: anotherNonEphemeronObjectOop.

	"Force object to not be collected by putting them in special variables"
	self keepObjectInVMVariable1: ephemeronObjectOop.
	self keepObjectInVMVariable2: anotherEphemeronObjectOop.

	memory gc doScavenge: 1.	"TenureByAge"
	ephemeronObjectOop := memory remapObj: ephemeronObjectOop.
	anotherEphemeronObjectOop := memory remapObj: anotherEphemeronObjectOop.
	self
		assert: memory gc dequeueMourner
		equals: ephemeronObjectOop.

	self
		assert: memory gc dequeueMourner
		equals: anotherEphemeronObjectOop.
]

{ #category : #'tests-ephemerons-globals' }
VMSpurScavengeEphemeronTest >> testScavengeTwoEphemeronObjectsReferencingDifferentDyingObjectsShouldBeAddedInTheMournQueueAfterScavengingInPastSpace [
	| ephemeronObjectOop nonEphemeronObjectOop  anotherEphemeronObjectOop anotherNonEphemeronObjectOop |
	self createEphemeronClass.
	ephemeronObjectOop := self newEphemeronObject.
	anotherEphemeronObjectOop := self newEphemeronObject.
	nonEphemeronObjectOop := self newZeroSizedObject.
	anotherNonEphemeronObjectOop := self newZeroSizedObject.
	memory
		storePointer: 0
		ofObject: ephemeronObjectOop
		withValue: nonEphemeronObjectOop.
		
	memory
		storePointer: 0
		ofObject: anotherEphemeronObjectOop
		withValue: anotherNonEphemeronObjectOop.

	"Force object to not be collected by putting them in special variables"
	self keepObjectInVMVariable1: ephemeronObjectOop.
	self keepObjectInVMVariable2: anotherEphemeronObjectOop.
	self keepObjectInVMVariable3: anotherNonEphemeronObjectOop.

	"Scavence once so all three objects are moved from eden to past space"
	memory gc doScavenge: 1.	"TenureByAge"
	ephemeronObjectOop := memory remapObj: ephemeronObjectOop.
	anotherEphemeronObjectOop := memory remapObj: anotherEphemeronObjectOop.
	anotherNonEphemeronObjectOop := memory remapObj: anotherNonEphemeronObjectOop.
	
	self forgetObject3.
	memory gc doScavenge: 1.	"TenureByAge"
	ephemeronObjectOop := memory remapObj: ephemeronObjectOop.
	anotherEphemeronObjectOop := memory remapObj: anotherEphemeronObjectOop.

	self
		assert: memory gc dequeueMourner
		equals: anotherEphemeronObjectOop.

	self
		assert: memory gc dequeueMourner
		equals: ephemeronObjectOop.
]

{ #category : #'tests-ephemerons-globals' }
VMSpurScavengeEphemeronTest >> testScavengeTwoEphemeronObjectsReferencingSameDyingObjectsShouldAddOnlyOneEphemeron [
	| ephemeronObjectOop nonEphemeronObjectOop  anotherEphemeronObjectOop |
	self createEphemeronClass.
	ephemeronObjectOop := self newEphemeronObject.
	anotherEphemeronObjectOop := self newEphemeronObject.
	nonEphemeronObjectOop := self newZeroSizedObject.

	memory
		storePointer: 0
		ofObject: ephemeronObjectOop
		withValue: nonEphemeronObjectOop.
		
	memory
		storePointer: 0
		ofObject: anotherEphemeronObjectOop
		withValue: nonEphemeronObjectOop.

	"Force object to not be collected by putting them in special variables"
	self keepObjectInVMVariable1: ephemeronObjectOop.
	self keepObjectInVMVariable2: anotherEphemeronObjectOop.

	memory gc doScavenge: 1.	"TenureByAge"
	ephemeronObjectOop := memory remapObj: ephemeronObjectOop.
	anotherEphemeronObjectOop := memory remapObj: anotherEphemeronObjectOop.

	"Consume the first mourner"
	memory gc dequeueMourner.
	self
		assert: memory gc dequeueMourner
		equals: nil
]

{ #category : #'tests-ephemerons-globals' }
VMSpurScavengeEphemeronTest >> testScavengeTwoEphemeronObjectsReferencingSameDyingObjectsShouldAddOnlySecond [
	| ephemeronObjectOop nonEphemeronObjectOop  anotherEphemeronObjectOop |
	self createEphemeronClass.
	ephemeronObjectOop := self newEphemeronObject.
	anotherEphemeronObjectOop := self newEphemeronObject.
	nonEphemeronObjectOop := self newZeroSizedObject.

	memory
		storePointer: 0
		ofObject: ephemeronObjectOop
		withValue: nonEphemeronObjectOop.
		
	memory
		storePointer: 0
		ofObject: anotherEphemeronObjectOop
		withValue: nonEphemeronObjectOop.

	"Force object to not be collected by putting them in special variables"
	self keepObjectInVMVariable1: ephemeronObjectOop.
	self keepObjectInVMVariable2: anotherEphemeronObjectOop.

	memory gc doScavenge: 1.	"TenureByAge"
	ephemeronObjectOop := memory remapObj: ephemeronObjectOop.
	anotherEphemeronObjectOop := memory remapObj: anotherEphemeronObjectOop.

	self
		assert: memory gc dequeueMourner
		equals: anotherEphemeronObjectOop.
]

{ #category : #'tests-ephemerons-globals' }
VMSpurScavengeEphemeronTest >> testScavengeTwoEphemeronObjectsReferencingSameDyingObjectsShouldBeQueuedAfterConsumingMournQueue [
	| ephemeronObjectOop nonEphemeronObjectOop  anotherEphemeronObjectOop |
	self createEphemeronClass.
	ephemeronObjectOop := self newEphemeronObject.
	anotherEphemeronObjectOop := self newEphemeronObject.
	nonEphemeronObjectOop := self newZeroSizedObject.

	memory
		storePointer: 0
		ofObject: ephemeronObjectOop
		withValue: nonEphemeronObjectOop.
		
	memory
		storePointer: 0
		ofObject: anotherEphemeronObjectOop
		withValue: nonEphemeronObjectOop.

	"Force object to not be collected by putting them in special variables"
	self keepObjectInVMVariable1: ephemeronObjectOop.
	self keepObjectInVMVariable2: anotherEphemeronObjectOop.

	memory gc doScavenge: 1.	"TenureByAge"
	ephemeronObjectOop := memory remapObj: ephemeronObjectOop.

	"The second ephemeron changed format, now it keeps the key strongly.
	Nil the ephemeron key to allow the next ephemeron to be finalized too"
	memory storePointer: 0 ofObject: memory gc dequeueMourner withValue: memory nilObject.
	
	memory gc doScavenge: 1.	"TenureByAge"
	ephemeronObjectOop := memory remapObj: ephemeronObjectOop.

	self
		assert: memory gc dequeueMourner
		equals: ephemeronObjectOop
]

{ #category : #'tests-ephemerons-globals' }
VMSpurScavengeEphemeronTest >> testScavengeTwoEphemeronObjectsReferencingSameDyingObjectsShouldLeaveFirstOneAsEphemeron [
	| ephemeronObjectOop nonEphemeronObjectOop  anotherEphemeronObjectOop |
	self createEphemeronClass.
	ephemeronObjectOop := self newEphemeronObject.
	anotherEphemeronObjectOop := self newEphemeronObject.
	nonEphemeronObjectOop := self newZeroSizedObject.

	memory
		storePointer: 0
		ofObject: ephemeronObjectOop
		withValue: nonEphemeronObjectOop.
		
	memory
		storePointer: 0
		ofObject: anotherEphemeronObjectOop
		withValue: nonEphemeronObjectOop.

	"Force object to not be collected by putting them in special variables"
	self keepObjectInVMVariable1: ephemeronObjectOop.
	self keepObjectInVMVariable2: anotherEphemeronObjectOop.

	memory gc doScavenge: 1.	"TenureByAge"
	ephemeronObjectOop := memory remapObj: ephemeronObjectOop.
	anotherEphemeronObjectOop := memory remapObj: anotherEphemeronObjectOop.

	self assert: (memory isEphemeron: ephemeronObjectOop)
]

{ #category : #'tests-ephemerons-globals' }
VMSpurScavengeEphemeronTest >> testScavengeTwoEphemeronObjectsReferencingSameDyingObjectsShouldScavengeKeyOfSecond [
	| ephemeronObjectOop nonEphemeronObjectOop  anotherEphemeronObjectOop |
	self createEphemeronClass.
	ephemeronObjectOop := self newEphemeronObject.
	anotherEphemeronObjectOop := self newEphemeronObject.
	nonEphemeronObjectOop := self newZeroSizedObject.

	memory
		storePointer: 0
		ofObject: ephemeronObjectOop
		withValue: nonEphemeronObjectOop.
		
	memory
		storePointer: 0
		ofObject: anotherEphemeronObjectOop
		withValue: nonEphemeronObjectOop.

	"Force object to not be collected by putting them in special variables"
	self keepObjectInVMVariable1: ephemeronObjectOop.
	self keepObjectInVMVariable2: anotherEphemeronObjectOop.

	memory gc doScavenge: 1.	"TenureByAge"
	ephemeronObjectOop := memory remapObj: ephemeronObjectOop.
	anotherEphemeronObjectOop := memory remapObj: anotherEphemeronObjectOop.

	self
		assert: (memory
			fetchPointer: 0
			ofObject: ephemeronObjectOop)
		equals: (memory remapObj: nonEphemeronObjectOop)
]
