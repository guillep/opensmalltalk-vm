Extension { #name : #Integer }

{ #category : #'*VMMaker-Tools' }
Integer >> aarch64Disassembled [
	
	^ self disassembleWith: LLVMARMDisassembler aarch64
]

{ #category : #'*VMMaker-Tools' }
Integer >> disassembleWith: aLLVMDisassembler [ 
	
	"Create a byte array big enough to encode the instruction"
	| array |
	array := ByteArray new: self asByteArray size.
	array integerAt: 1 put: self size: array size signed: false.
	^ aLLVMDisassembler disassembleInstructionIn: array pc: 0
]

{ #category : #'*VMMaker-Tools' }
Integer >> inpectionNumberRepresentations [
	<inspectorPresentationOrder: 35 title: 'Integer Representations'>

	| associations |
	associations :=	{
		'decimal' -> self printString.
		'hex' -> self printStringHex.
		'octal' -> (self printStringBase: 8).
		'binary' -> (self printStringBase: 2) } asOrderedCollection.

	^ SpTablePresenter new
		items: associations;
		addColumn: (SpStringTableColumn title: 'Representation' evaluated: [ :assoc | assoc key ]);
		addColumn: (SpStringTableColumn title: 'Value' evaluated: [ :assoc | assoc value ]);	
		yourself
]
