Extension { #name : #BasicBlockCompiler }

{ #category : #'*VMMaker-Tools' }
BasicBlockCompiler >> gtInspectorBlockListIn: composite [
	<gtInspectorPresentationOrder: 0>
	^ composite fastTree
		title: 'Basic Blocks';
		children: [ :aNode | aNode instructions ];
		hasChildren: [ :aNode | aNode isKindOf: BasicBlock ];
		display: [ :anObject | basicBlocks asOrderedCollection ]
]
