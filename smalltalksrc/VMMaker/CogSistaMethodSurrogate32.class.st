Class {
	#name : #CogSistaMethodSurrogate32,
	#superclass : #CogMethodSurrogate32,
	#category : #'VMMaker-JITSimulation'
}

{ #category : #accessing }
CogSistaMethodSurrogate32 class >> alignedByteSize [
	^28 + self baseHeaderSize
]

{ #category : #accessing }
CogSistaMethodSurrogate32 class >> offsetOf: aByteSymbol [
	"These should be generated!!"
	^aByteSymbol == #counters
		ifTrue: [20 + self objectMemoryClass baseHeaderSize]
		ifFalse: [super offsetOf: aByteSymbol]
]

{ #category : #accessing }
CogSistaMethodSurrogate32 >> counters [
	^memory unsignedLongAt: address + 24 + baseHeaderSize
]

{ #category : #accessing }
CogSistaMethodSurrogate32 >> counters: aValue [
	^memory
		unsignedLongAt: address + baseHeaderSize + 24
		put: aValue
]
