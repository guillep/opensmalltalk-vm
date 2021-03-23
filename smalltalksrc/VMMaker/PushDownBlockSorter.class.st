Class {
	#name : #PushDownBlockSorter,
	#superclass : #BasicBlockSorter,
	#category : #'VMMaker-JIT'
}

{ #category : #sorting }
PushDownBlockSorter >> sort: aListOfBasicBlocks [

	<var: #basicBlock type: #'BasicBlock *'>
	<var: #previousBlock type: #'BasicBlock *'>
	| finalOrder pendingBlocks |
	
	finalOrder := self newLinkedList.
	pendingBlocks := self newLinkedList.
	
	aListOfBasicBlocks do: [ :basicBlock |
		basicBlock isPushDownBlock
			ifTrue: [ pendingBlocks add: basicBlock ]
			ifFalse: [ | previousBlock |

				"When deciding the final order of blocks, remove redundant jumps to fall through branches.
				Could be implemented better by just remembering the block from the last loop iteration"
				finalOrder notEmpty ifTrue: [
					previousBlock := finalOrder last.
					(previousBlock isFallingThroughBlock: basicBlock)
						ifTrue: [ previousBlock last removeEndingJump ].
				].	
				finalOrder add: basicBlock ] ].
		
	pendingBlocks do: [ :pendingBlock | finalOrder add: pendingBlock ].
	^ finalOrder
]
