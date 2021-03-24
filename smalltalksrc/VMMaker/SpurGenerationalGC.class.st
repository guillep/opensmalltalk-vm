Class {
	#name : #SpurGenerationalGC,
	#superclass : #CogClass,
	#instVars : [
		'remapBufferCount',
		'scavenger',
		'freeStart',
		'coInterpreter',
		'newSpaceStart',
		'newSpaceLimit',
		'needGCFlag',
		'gcStartUsecs',
		'statScavenges',
		'statGCEndUsecs',
		'statSGCDeltaUsecs',
		'statScavengeGCUsecs',
		'statRootTableCount',
		'oldSpaceStart',
		'endOfMemory',
		'totalFreeOldSpace',
		'checkForLeaks',
		'freeLists',
		'freeListsMask',
		'heapMap',
		'mournQueue',
		'remapBuffer',
		'extraRootCount',
		'extraRoots',
		'statAllocatedBytes',
		'oldSpaceUsePriorToScavenge',
		'gcPhaseInProgress',
		'pastSpaceStart',
		'scavengeThreshold',
		'heapSizeAtPreviousGC',
		'freeOldSpaceStart',
		'memory',
		'compactor',
		'objectRepresentation',
		'edenBytes',
		'statMarkCount',
		'markStack',
		'weaklingStack',
		'gcMarkEndUsecs',
		'compactionStartUsecs',
		'marking',
		'unscannedEphemeronsQueueInitialSize',
		'unscannedEphemerons',
		'shrinkThreshold',
		'growHeadroom',
		'statShrinkMemory',
		'statFullGCs',
		'statFullGCUsecs',
		'statCompactionUsecs',
		'gcSweepEndUsecs',
		'statSweepUsecs',
		'statMarkUsecs'
	],
	#classVars : [
		'MarkStackRecord',
		'MarkStackRootIndex',
		'MournQueueRootIndex',
		'RememberedSetRootIndex',
		'WeaklingStackRootIndex'
	],
	#pools : [
		'SpurMemoryManagementConstants'
	],
	#category : #'VMMaker-SpurMemoryManager'
}

{ #category : #'accessing class hierarchy' }
SpurGenerationalGC class >> compactorClass [
	"Answer the compaction algorithm to use."
	^Smalltalk classNamed: (InitializationOptions at: #compactorClass ifAbsent: [#SpurPlanningCompactor])
]

{ #category : #initialization }
SpurGenerationalGC class >> initialize [

	"The hiddenHootsObject contains the classTable pages and up to 8 additional objects.
	 Currently we use four; the three objStacks, the mark stack, the weaklings and the
	 mourn queue, and the rememberedSet."
	MarkStackRootIndex := SpurMemoryManager new classTableRootSlots.
	WeaklingStackRootIndex := MarkStackRootIndex + 1.
	MournQueueRootIndex := MarkStackRootIndex + 2.
	RememberedSetRootIndex := MarkStackRootIndex + 3.
]

{ #category : #'object enumeration' }
SpurGenerationalGC >> accessibleObjectAfter: objOop [
	"Answer the accessible object following the given object or 
	free chunk in the heap. Return nil when heap is exhausted.
	 This is for primitiveNextObject subsequent to primtiiveSomeObject.
	 It also tries to handle more general use by ordering objects as
		eden
		past
		old
	 but this is tricky becaus ethe order in memory is
		past
		eden
		old"
	<inline: false>
	| objAfter |
	objAfter := objOop.
	(self oop: objAfter isLessThan: nilObj) ifTrue: "object in new space"
		[self assert: ((self isInEden: objOop) or: [self isInPastSpace: objOop]).
		 (self oop: objAfter isGreaterThan: pastSpaceStart) ifTrue:
			["Obj is in eden.  Answer next normal object in eden, if there is one."
			 [objAfter := self objectAfter: objAfter limit: freeStart.
			  self oop: objAfter isLessThan: freeStart] whileTrue:
				[(self isNormalObject: objAfter) ifTrue:
					[^objAfter]].
			 "There wasn't a next object in eden. If past space is empty answer nilObj."
			 pastSpaceStart <= scavenger pastSpace start ifTrue:
				[^nilObj].
			 "If the first object in pastSpace is OK, answer it, otherwise fall through to enumerate past space."
			 objAfter := self objectStartingAt: scavenger pastSpace start.
			 (self isNormalObject: objAfter) ifTrue:
				[^objAfter]].
		 "Either objOop was in pastSpace, or enumeration exhaused eden, so enumerate past space."
		 [objAfter := self objectAfter: objAfter limit: pastSpaceStart.
		  self oop: objAfter isLessThan: pastSpaceStart] whileTrue:
			[(self isNormalObject: objAfter) ifTrue:
				[^objAfter]].
		 ^nilObj].
	[objAfter := self objectAfter: objAfter limit: endOfMemory.
	 objAfter = endOfMemory ifTrue:
		[^nil].
	 (self isNormalObject: objAfter) ifTrue:
		[^objAfter]] repeat
]

{ #category : #'weakness and ephemerality' }
SpurGenerationalGC >> activeAndDeferredScan: anEphemeron [
	"Answer whether an ephemeron is active (has an unmarked
	 key) and was pushed on the unscanned ephemerons stack."
	| key |
	<inline: #never>
	self assert: (objectRepresentation isEphemeron: anEphemeron).
	((objectRepresentation isImmediate: (key := objectRepresentation keyOfEphemeron: anEphemeron))
	 or: [objectRepresentation isMarked: key]) ifTrue:
		[^false].
	^self pushOnUnscannedEphemeronsStack: anEphemeron
]

{ #category : #'free space' }
SpurGenerationalGC >> addFreeChunkWithBytes: bytes at: address [
	totalFreeOldSpace := totalFreeOldSpace + bytes.
	^self freeChunkWithBytes: bytes at: address
]

{ #category : #'free space' }
SpurGenerationalGC >> addFreeSubTree: freeTree [
	"Add a freeChunk sub tree back into the large free chunk tree.
	 This is for allocateOldSpaceChunkOf[Exactly]Bytes:[suchThat:]."
	| bytesInArg treeNode bytesInNode subNode |
	"N.B. *can't* use numSlotsOfAny: because of rounding up of odd slots
	 and/or step in size at 1032 bytes in 32-bits or 2048 bytes in 64-bits."
	self assert: (self isFreeObject: freeTree).
	bytesInArg := objectRepresentation bytesInObject: freeTree.
	self assert: bytesInArg >= (self numFreeLists * objectRepresentation allocationUnit).
	treeNode := freeLists at: 0.
	self assert: treeNode ~= 0.
	[bytesInNode := objectRepresentation bytesInObject: treeNode.
	 "check for overlap; could write this as self oop: (self objectAfter: freeChunk) isLessThanOrEqualTo: child...
	  but that relies on headers being correct, etc.  So keep it clumsy..."
	 self assert: ((self oop: freeTree + bytesInArg - objectRepresentation baseHeaderSize isLessThanOrEqualTo: treeNode)
					or: [self oop: freeTree isGreaterThanOrEqualTo: treeNode + bytesInNode - objectRepresentation baseHeaderSize]).
	 self assert: bytesInNode >= (self numFreeLists * objectRepresentation allocationUnit).
	 self assert: bytesInArg ~= bytesInNode.
	 bytesInNode > bytesInArg
		ifTrue:
			[subNode := self fetchPointer: self freeChunkSmallerIndex ofFreeChunk: treeNode.
			 subNode = 0 ifTrue:
				[self storePointer: self freeChunkSmallerIndex ofFreeChunk: treeNode withValue: freeTree.
				 self storePointer: self freeChunkParentIndex ofFreeChunk: freeTree withValue: treeNode.
				 ^self]]
		ifFalse:
			[subNode := self fetchPointer: self freeChunkLargerIndex ofFreeChunk: treeNode.
			 subNode = 0 ifTrue:
				[self storePointer: self freeChunkLargerIndex ofFreeChunk: treeNode withValue: freeTree.
				 self storePointer: self freeChunkParentIndex ofFreeChunk: freeTree withValue: treeNode.
				 ^self]].
	 treeNode := subNode] repeat
]

{ #category : #'plugin support' }
SpurGenerationalGC >> addGCRoot: varLoc [
	"Add the given variable location to the extra roots table."
	<api>
	<var: #varLoc type: #'sqInt *'>
	extraRootCount >= ExtraRootsSize ifTrue: [^false]. "out of space"
	extraRoots at: (extraRootCount := extraRootCount + 1) put: varLoc.
	^true
]

{ #category : #'free space' }
SpurGenerationalGC >> addToFreeList: freeChunk bytes: chunkBytes [
	"Add freeChunk to the relevant freeList.
	 For the benefit of sortedFreeObject:, if freeChunk is large, answer the treeNode it
	 is added to, if it is added to the next list of a freeTreeNode, otherwise answer 0."
	| index |
	"coInterpreter transcript ensureCr. coInterpreter print: 'freeing '. self printFreeChunk: freeChunk."
	self assert: (self isFreeObject: freeChunk).
	self assert: chunkBytes = (objectRepresentation bytesInObject: freeChunk).
	"Too slow to be enabled byt default but useful to debug Selective...
	 self deny: (compactor isSegmentBeingCompacted: (segmentManager segmentContainingObj: freeChunk))."
	index := chunkBytes / objectRepresentation allocationUnit.
	index < self numFreeLists ifTrue:
		[self setNextFreeChunkOf: freeChunk withValue: (freeLists at: index) chunkBytes: chunkBytes.
		(objectRepresentation isLilliputianSize: chunkBytes) ifFalse:
			[self storePointer: self freeChunkPrevIndex ofFreeChunk: freeChunk withValue: 0].
		 freeLists at: index put: freeChunk.
		 freeListsMask := freeListsMask bitOr: 1 << index.
		 ^0].

	^self addToFreeTree: freeChunk bytes: chunkBytes
]

{ #category : #'free space' }
SpurGenerationalGC >> addToFreeTree: freeChunk bytes: chunkBytes [
	"Add freeChunk to the large free chunk tree.
	 For the benefit of sortedFreeObject:, answer the treeNode it is added
	 to, if it is added to the next list of a freeTreeNode, otherwise answer 0."
	| childBytes parent child |
	self assert: (self isFreeObject: freeChunk).
	self assert: chunkBytes = (objectRepresentation bytesInObject: freeChunk).
	self assert: chunkBytes >= (self numFreeLists * objectRepresentation allocationUnit).
	self
		storePointer: self freeChunkNextIndex ofFreeChunk: freeChunk withValue: 0;
		storePointer: self freeChunkPrevIndex ofFreeChunk: freeChunk withValue: 0;
		storePointer: self freeChunkParentIndex ofFreeChunk: freeChunk withValue: 0;
		storePointer: self freeChunkSmallerIndex ofFreeChunk: freeChunk withValue: 0;
		storePointer: self freeChunkLargerIndex ofFreeChunk: freeChunk withValue: 0.
	"Large chunk list organized as a tree, each node of which is a list of chunks of the same size.
	 Beneath the node are smaller and larger blocks."
	parent := 0.
	child := freeLists at: 0.
	[child ~= 0] whileTrue:
		[childBytes := objectRepresentation bytesInObject: child.
		 "check for overlap; could write this as self oop: (self objectAfter: freeChunk) isLessThanOrEqualTo: child...
		  but that relies on headers being correct, etc.  So keep it clumsy..."
		 self assert: ((self oop: freeChunk + chunkBytes - objectRepresentation baseHeaderSize isLessThanOrEqualTo: child)
						or: [self oop: freeChunk isGreaterThanOrEqualTo: child + childBytes - objectRepresentation baseHeaderSize]).
		 childBytes = chunkBytes ifTrue: "size match; add to list at node."
			[self setNextFreeChunkOf: freeChunk withValue: (self fetchPointer: self freeChunkNextIndex ofFreeChunk: child) isLilliputianSize: false. 
			 self setNextFreeChunkOf: child withValue: freeChunk isLilliputianSize: false.
			 ^child].
		 "walk down the tree"
		 parent := child.
		 child := self fetchPointer: (childBytes > chunkBytes
										ifTrue: [self freeChunkSmallerIndex]
										ifFalse: [self freeChunkLargerIndex])
					ofFreeChunk: child].
	parent = 0 ifTrue:
		[self assert: (freeLists at: 0) = 0.
		 freeLists at: 0 put: freeChunk.
		 freeListsMask := freeListsMask bitOr: 1.
		 ^0].
	self assert: (freeListsMask anyMask: 1).
	"insert in tree"
	self storePointer: self freeChunkParentIndex
			ofFreeChunk: freeChunk
				withValue: parent.
	self storePointer: (childBytes > chunkBytes
									ifTrue: [self freeChunkSmallerIndex]
									ifFalse: [self freeChunkLargerIndex])
			ofFreeChunk: parent
				withValue: freeChunk.
	^0
]

{ #category : #'debug support' }
SpurGenerationalGC >> addressCouldBeOldObj: address [
	^(address bitAnd: objectRepresentation baseHeaderSize - 1) = 0
	  and: [self isInOldSpace: address]
]

{ #category : #snapshot }
SpurGenerationalGC >> adjustAllOopsBy: bytesToShift [
	"Adjust all oop references by the given number of bytes. This is
	 done just after reading in an image when the new base address
	 of the object heap is different from the base address in the image,
	 or when loading multiple segments that have been coalesced.  Also
	 set bits in the classTableBitmap corresponding to used classes."

	| obj classIndex |
	self assert: self newSpaceIsEmpty.
	self countNumClassPagesPreSwizzle: bytesToShift.
	(bytesToShift ~= 0
	 or: [segmentManager numSegments > 1]) ifTrue:
		[obj := self objectStartingAt: oldSpaceStart.
		 [self oop: obj isLessThan: freeOldSpaceStart] whileTrue:
			[classIndex := self classIndexOf: obj.
			 classIndex >= self isForwardedObjectClassIndexPun
				ifTrue:
					[self swizzleFieldsOfObject: obj]
				ifFalse:
					[classIndex = self isFreeObjectClassIndexPun ifTrue:
						[self swizzleFieldsOfFreeChunk: obj]].
			 obj := self objectAfter: obj limit: endOfMemory]]
]

{ #category : #'object enumeration' }
SpurGenerationalGC >> allExistingNewSpaceObjectsDo: aBlock [
	<inline: true>
	| prevObj prevPrevObj objOop limit |
	prevPrevObj := prevObj := nil.
	"After a scavenge eden is empty, futureSpace is empty, and all newSpace objects are
	  in pastSpace.  Objects are allocated in eden.  So enumerate only eden and pastSpace."
	objOop := self objectStartingAt: scavenger eden start.
	limit := freeStart.
	[self oop: objOop isLessThan: limit] whileTrue:
		[self assert: (self isEnumerableObjectNoAssert: objOop).
		 aBlock value: objOop.
		 prevPrevObj := prevObj.
		 prevObj := objOop.
		 objOop := self objectAfter: objOop limit: freeStart].
	objOop := self objectStartingAt: scavenger pastSpace start.
	limit := pastSpaceStart.
	[self oop: objOop isLessThan: limit] whileTrue:
		[self assert: (self isEnumerableObjectNoAssert: objOop).
		 aBlock value: objOop.
		 prevPrevObj := prevObj.
		 prevObj := objOop.
		 objOop := self objectAfter: objOop limit: limit].
	self touch: prevPrevObj.
	self touch: prevObj
]

{ #category : #'free space' }
SpurGenerationalGC >> allFreeHeads [
	<doNotGenerate>
	| freeObjects |
	freeObjects := OrderedCollection new.
	0 to: self numFreeLists - 1 do: [:i| | obj |
		obj := freeLists at: i.
		obj ~= 0 ifTrue: [ freeObjects add: obj ]].
	^freeObjects
]

{ #category : #'free space' }
SpurGenerationalGC >> allFreeListHeads [
	<doNotGenerate>
	"Return all the head nodes of the free lists.
	The free lists are all the entries in the freeLists array between 2 and numFreeLists - 1.
	We skip indexes 0 and 1: index 0 is the free tree and index 1 unused"
	
	| freeObjects |
	freeObjects := OrderedCollection new.
	2 to: self numFreeLists - 1 do: [:i| | obj |
		obj := freeLists at: i.
		obj ~= 0 ifTrue: [ freeObjects add: obj ]].
	^freeObjects
]

{ #category : #'free space' }
SpurGenerationalGC >> allFreeObjects [
	<doNotGenerate>
	| freeObjects |
	freeObjects := OrderedCollection new.
	self allFreeObjectsDo:
		[:f| freeObjects addLast: f].
	^freeObjects
]

{ #category : #'free space' }
SpurGenerationalGC >> allFreeObjectsDo: aBlock [
	| obj |
	1 to: self numFreeLists - 1 do:
		[:i|
		obj := freeLists at: i.
		[obj ~= 0] whileTrue:
			[aBlock value: obj.
			 obj := self fetchPointer: self freeChunkNextIndex ofFreeChunk: obj]].
	self allObjectsInFreeTreeDo: aBlock
]

{ #category : #'primitive support' }
SpurGenerationalGC >> allInstancesOf: aClass [
	"Attempt to answer an array of all objects, excluding those that may
	 be garbage collected as a side effect of allocating the result array.
	 If no memory is available answer the number of instances as a SmallInteger.
	 Since objects are at least 16 bytes big, and the largest SmallInteger covers
	 1/4 of the address space, the count can never overflow."
	| classIndex freeChunk ptr start limit count bytes |
	classIndex := self rawHashBitsOf: aClass.
	classIndex = 0 ifTrue:
		[freeChunk := self allocateSlots: 0 format: self arrayFormat classIndex: ClassArrayCompactIndex.
		 ^freeChunk].
	MarkObjectsForEnumerationPrimitives ifTrue:
		[self markObjects: true]. "may not want to revive objects unnecessarily; but marking is sloooow."
	freeChunk := self allocateLargestFreeChunk. "N.B. Does /not/ update totalFreeOldSpace"
	start := freeChunk + self baseHeaderSize.
	limit := self addressAfter: freeChunk.
	(self isClassAtUniqueIndex: aClass)
		ifTrue:
			[self uniqueIndex: classIndex allInstancesInto: start limit: limit resultsInto: [:c :p| count := c. ptr := p]]
		ifFalse:
			[self ambiguousClass: aClass allInstancesInto: start limit: limit resultsInto: [:c :p| count := c. ptr := p]].
	self assert: (self isEmptyObjStack: markStack).
	MarkObjectsForEnumerationPrimitives
		ifTrue:
			[self assert: self allObjectsUnmarked.
			 self emptyObjStack: weaklingStack]
		ifFalse:
			[self assert: (self isEmptyObjStack: weaklingStack)].
	(count > (ptr - start / self bytesPerOop) "not enough room"
	 or: [limit ~= ptr and: [limit - ptr <= self allocationUnit]]) ifTrue: "can't split a single word"
		[self freeObject: freeChunk.
		 ^self integerObjectOf: count].
	count < self numSlotsMask ifTrue:
		[| smallObj |
		 smallObj := self allocateSlots: count format: self arrayFormat classIndex: ClassArrayCompactIndex.
		 0 to: count - 1 do:
			[:i|
			self storePointerUnchecked: i ofObject: smallObj withValue: (self fetchPointer: i ofFreeChunk: freeChunk)].
		 self freeChunkWithBytes: (self bytesInObject: freeChunk) at: (self startOfObject: freeChunk).
		 self beRootIfOld: smallObj.
		 self checkFreeSpace: GCModeFull.
		 ^smallObj].
	bytes := self largeObjectBytesForSlots: count.
	start := self startOfObject: freeChunk.
	self freeChunkWithBytes: limit - start - bytes at: start + bytes.
	totalFreeOldSpace := totalFreeOldSpace - bytes.
	self rawOverflowSlotsOf: freeChunk put: count.
	self set: freeChunk classIndexTo: ClassArrayCompactIndex formatTo: self arrayFormat.
	self possibleRootStoreInto: freeChunk.
	self checkFreeSpace: GCModeFull.
	self runLeakCheckerFor: GCModeFull.
	^freeChunk
	
	
]

{ #category : #'object enumeration' }
SpurGenerationalGC >> allNewSpaceEntitiesDo: aBlock [
	"Enumerate all new space objects, including free objects."
	<inline: true>
	| prevObj prevPrevObj objOop limit |
	prevPrevObj := prevObj := nil.
	"After a scavenge eden is empty, futureSpace is empty, and all newSpace objects are
	  in pastSpace.  Objects are allocated in eden.  So enumerate only pastSpace and eden."
	self assert: (scavenger pastSpace start < scavenger eden start).
	objOop := objectRepresentation objectStartingAt: scavenger pastSpace start.
	limit := pastSpaceStart.
	[self oop: objOop isLessThan: limit] whileTrue:
		[aBlock value: objOop.
		 prevPrevObj := prevObj.
		 prevObj := objOop.
		 objOop := objectRepresentation objectAfter: objOop limit: limit].
	objOop := objectRepresentation objectStartingAt: scavenger eden start.
	[self oop: objOop isLessThan: freeStart] whileTrue:
		[aBlock value: objOop.
		 prevPrevObj := prevObj.
		 prevObj := objOop.
		 objOop := objectRepresentation objectAfter: objOop limit: freeStart].
	self touch: prevPrevObj.
	self touch: prevObj
]

{ #category : #'object enumeration' }
SpurGenerationalGC >> allNewSpaceObjectsDo: aBlock [
	"Enumerate all new space objects, excluding free objects."
	<inline: true>
	self allNewSpaceEntitiesDo:
		[:objOop|
		 self assert: (objectRepresentation isEnumerableObjectNoAssert: objOop).
		 aBlock value: objOop]
]

{ #category : #'primitive support' }
SpurGenerationalGC >> allObjects [
	"Attempt to answer an array of all objects, excluding those that may
	 be garbage collected as a side effect of allocating the result array.
	 If no memory is available answer the number of objects as a SmallInteger.
	 Since objects are at least 16 bytes big, and the largest SmallInteger covers
	 1/4 of the address space, the count can never overflow."
	| freeChunk ptr start limit count bytes |
	MarkObjectsForEnumerationPrimitives ifTrue:
		[self markObjects: true]. "may not want to revive objects unnecessarily; but marking is sloooow."
	freeChunk := self allocateLargestFreeChunk. "N.B. Does /not/ update totalFreeOldSpace"
	ptr := start := freeChunk + self baseHeaderSize.
	limit := self addressAfter: freeChunk.
	count := 0.
	self allHeapEntitiesDo:
		[:obj| "continue enumerating even if no room so as to unmark all objects."
		 (MarkObjectsForEnumerationPrimitives
				ifTrue: [self isMarked: obj]
				ifFalse: [true]) ifTrue:
			[(self isNormalObject: obj)
				ifTrue:
					[MarkObjectsForEnumerationPrimitives ifTrue:
						[self setIsMarkedOf: obj to: false].
					 count := count + 1.
					 ptr < limit ifTrue:
						[self longAt: ptr put: obj.
						 ptr := ptr + self bytesPerOop]]
				ifFalse:
					[MarkObjectsForEnumerationPrimitives ifTrue:
						[(self isSegmentBridge: obj) ifFalse:
							[self setIsMarkedOf: obj to: false]]]]].
	self assert: (self isEmptyObjStack: markStack).
	MarkObjectsForEnumerationPrimitives
		ifTrue:
			[self assert: self allObjectsUnmarked.
			 self emptyObjStack: weaklingStack]
		ifFalse:
			[self assert: (self isEmptyObjStack: weaklingStack)].
	self assert: count >= self numSlotsMask.
	(count > (ptr - start / self bytesPerOop) "not enough room"
	 or: [limit ~= ptr and: [limit - ptr <= self allocationUnit]]) ifTrue: "can't split a single word"
		[self freeChunkWithBytes: (self bytesInObject: freeChunk) at: (self startOfObject: freeChunk).
		 self checkFreeSpace: GCModeFull.
		 ^self integerObjectOf: count].
	bytes := self largeObjectBytesForSlots: count.
	start := self startOfObject: freeChunk.
	self freeChunkWithBytes: limit - start - bytes at: start + bytes.
	totalFreeOldSpace := totalFreeOldSpace - bytes.
	self rawOverflowSlotsOf: freeChunk put: count.
	self set: freeChunk classIndexTo: ClassArrayCompactIndex formatTo: self arrayFormat.
	self possibleRootStoreInto: freeChunk.
	self checkFreeSpace: GCModeFull.
	self runLeakCheckerFor: GCModeFull.
	^freeChunk
	
	
]

{ #category : #'object enumeration' }
SpurGenerationalGC >> allObjectsDo: aBlock [
	<inline: true>
	self allNewSpaceObjectsDo: aBlock.
	self allOldSpaceObjectsDo: aBlock
]

{ #category : #'free space' }
SpurGenerationalGC >> allObjectsInFreeTree: freeNode do: aBlock [
	| listNode |
	freeNode = 0 ifTrue: [^0].
	listNode := freeNode.
	[listNode ~= 0] whileTrue:
		[aBlock value: listNode.
		 listNode := self fetchPointer: self freeChunkNextIndex ofFreeChunk: listNode].
	self allObjectsInFreeTree: (self fetchPointer: self freeChunkSmallerIndex ofFreeChunk: freeNode)
		do: aBlock.
	self allObjectsInFreeTree: (self fetchPointer: self freeChunkLargerIndex ofFreeChunk: freeNode)
		do: aBlock
]

{ #category : #'free space' }
SpurGenerationalGC >> allObjectsInFreeTreeDo: aBlock [
	"Enumerate all objects in the free tree (in order, smaller to larger).
	 This is an iterative version so that the block argument can be
	 inlined by Slang. The trick to an iterative binary tree application is
	 to apply the function on the way back up when returning from a
	 particular direction, in this case up from the larger child."
	<inline: true>
	self freeTreeNodesDo:
		[:freeTreeNode| | next |
		 next := freeTreeNode.
		 [aBlock value: next.
		  next := self fetchPointer: self freeChunkNextIndex ofFreeChunk: next.
		  next ~= 0] whileTrue.
		 freeTreeNode]
]

{ #category : #'gc - global' }
SpurGenerationalGC >> allObjectsUnmarked [
	self allObjectsDo:
		[:o| (objectRepresentation isMarked: o) ifTrue: [ ^false]].
	^true
]

{ #category : #'weakness and ephemerality' }
SpurGenerationalGC >> allOldMarkedWeakObjectsOnWeaklingStack [
	self allOldSpaceEntitiesDo:
		[:o|
		((self isWeakNonImm: o)
		 and: [self isMarked: o]) ifTrue:
			[(self is: o onObjStack: weaklingStack) ifFalse:
				[^false]]].
	^true
]

{ #category : #'object enumeration' }
SpurGenerationalGC >> allOldSpaceEntitiesDo: aBlock [
	<inline: true>
	self allOldSpaceEntitiesFrom: self firstObject do: aBlock
]

{ #category : #'object enumeration' }
SpurGenerationalGC >> allOldSpaceEntitiesForCoalescingFrom: firstObj do: aBlock [
	<inline: true>
	| prevObj prevPrevObj objOop rawNumSlots rawNumSlotsAfter |
	prevPrevObj := prevObj := nil.
	objOop := firstObj.
	[self assert: objOop \\ self allocationUnit = 0.
	 self oop: objOop isLessThan: endOfMemory] whileTrue:
		[self assert: (self long64At: objOop) ~= 0.
		 rawNumSlots := self rawNumSlotsOf: objOop.
		 aBlock value: objOop.
		 "If the number of slot changes coalescing changed an object from a single to a double header.
		  In future have the block return the vaue.  It should know when things change."
		 self flag: 'future work'.
		 rawNumSlotsAfter := self rawNumSlotsOf: objOop.
		 (rawNumSlotsAfter ~= rawNumSlots
		  and: [rawNumSlotsAfter = self numSlotsMask]) ifTrue:
			[objOop := objOop + self baseHeaderSize.
			 self assert: (self objectAfter: prevObj limit: endOfMemory) = objOop].
		 prevPrevObj := prevObj.
		 prevObj := objOop.
		 objOop := self objectAfter: objOop limit: endOfMemory].
	self touch: prevPrevObj.
	self touch: prevObj
]

{ #category : #'object enumeration' }
SpurGenerationalGC >> allOldSpaceEntitiesForCompactingFrom: initialObject to: finalObject do: aBlock [
	<inline: true>
	| limit prevObj prevPrevObj objOop nextObj |
	self assert: (self isOldObject: initialObject).
	self assert: (self oop: finalObject isLessThanOrEqualTo: endOfMemory).
	prevPrevObj := prevObj := nil.
	objOop := initialObject.
	limit := (self oop: finalObject isLessThan: endOfMemory) ifTrue: [objectRepresentation addressAfter: finalObject] ifFalse: [endOfMemory].
	[self assert: objOop \\ objectRepresentation allocationUnit = 0.
	 self oop: objOop isLessThan: limit] whileTrue:
		[self assert: (objectRepresentation long64At: objOop) ~= 0.
		 nextObj := objectRepresentation objectAfter: objOop limit: endOfMemory.
		 aBlock value: objOop value: nextObj.
		 prevPrevObj := prevObj.
		 prevObj := objOop.
		 objOop := nextObj].
	self touch: prevPrevObj.
	self touch: prevObj
]

{ #category : #'object enumeration' }
SpurGenerationalGC >> allOldSpaceEntitiesFrom: initialObject do: aBlock [
	<inline: true>
	| prevObj prevPrevObj objOop |
	self assert: (self isOldObject: initialObject).
	prevPrevObj := prevObj := nil.
	objOop := initialObject.
	[self assert: objOop \\ objectRepresentation allocationUnit = 0.
	 self oop: objOop isLessThan: endOfMemory] whileTrue:
		[self assert: (objectRepresentation long64At: objOop) ~= 0.
		 aBlock value: objOop.
		 prevPrevObj := prevObj.
		 prevObj := objOop.
		 objOop := objectRepresentation objectAfter: objOop limit: endOfMemory].
	self touch: prevPrevObj.
	self touch: prevObj
]

{ #category : #'object enumeration' }
SpurGenerationalGC >> allOldSpaceEntitiesFrom: initialObject to: finalObject do: aBlock [
	<inline: true>
	| prevObj prevPrevObj objOop |
	self assert: ((self isNonImmediate: initialObject) and: [segmentManager isInSegments: initialObject]).
	self assert: ((self isNonImmediate: finalObject) and: [segmentManager isInSegments: finalObject]).
	prevPrevObj := prevObj := nil.
	objOop := initialObject.
	[self assert: objOop \\ self allocationUnit = 0.
	 self oop: objOop isLessThanOrEqualTo: finalObject] whileTrue:
		[self assert: (self long64At: objOop) ~= 0.
		 aBlock value: objOop.
		 prevPrevObj := prevObj.
		 prevObj := objOop.
		 objOop := self objectAfter: objOop limit: endOfMemory].
	self touch: prevPrevObj.
	self touch: prevObj
]

{ #category : #'object enumeration' }
SpurGenerationalGC >> allOldSpaceObjectsDo: aBlock [
	<inline: true>
	self allOldSpaceObjectsFrom: self firstObject do: aBlock
]

{ #category : #'object enumeration' }
SpurGenerationalGC >> allOldSpaceObjectsFrom: initialObject do: aBlock [
	"Enumerate all objects (i.e. exclude bridges, forwarders and free chunks)
	 in oldSpace starting at initialObject."
	<inline: true>
	self allOldSpaceEntitiesFrom: initialObject
		do: [:objOop|
			 (objectRepresentation isEnumerableObject: objOop) ifTrue:
				[aBlock value: objOop]]
]

{ #category : #'object enumeration' }
SpurGenerationalGC >> allPastSpaceEntitiesDo: aBlock [
	"Enumerate all past space objects, including free objects."
	<inline: true>
	| prevObj prevPrevObj objOop |
	prevPrevObj := prevObj := nil.
	objOop := objectRepresentation objectStartingAt: scavenger pastSpace start.
	[self oop: objOop isLessThan: pastSpaceStart] whileTrue:
		[aBlock value: objOop.
		 prevPrevObj := prevObj.
		 prevObj := objOop.
		 objOop := objectRepresentation objectAfter: objOop limit: pastSpaceStart].
	self touch: prevPrevObj.
	self touch: prevObj
]

{ #category : #'object enumeration' }
SpurGenerationalGC >> allPastSpaceObjectsDo: aBlock [
	"Enumerate all past space objects, excluding free objects."
	<inline: true>
	self allPastSpaceEntitiesDo:
		[:objOop|
		 self assert: (objectRepresentation isEnumerableObjectNoAssert: objOop).
		 aBlock value: objOop]
]

{ #category : #'weakness and ephemerality' }
SpurGenerationalGC >> allUnscannedEphemeronsAreActive [
	unscannedEphemerons start to: unscannedEphemerons top - objectRepresentation bytesPerOop by: objectRepresentation bytesPerOop do:
		[:p| | key |
		key := objectRepresentation keyOfMaybeFiredEphemeron: (objectRepresentation longAt: p).
		((objectRepresentation isImmediate: key) or: [objectRepresentation isMarked: key]) ifTrue:
			[^false]].
	^true
]

{ #category : #testing }
SpurGenerationalGC >> allocateMemoryOfSize: memoryBytes initialAddress: initialAddress [
	<doNotGenerate>

	^ memoryManager allocate: memoryBytes
]

{ #category : #asd }
SpurGenerationalGC >> allocateMemoryOfSize: memoryBytes newSpaceSize: newSpaceBytes stackSize: stackBytes codeSize: codeBytes methodCacheSize: methodCacheSize primitiveTraceLogSize: primitiveLogSize rumpCStackSize: rumpCStackSize initialAddress: initialAddress [

	"Intialize the receiver for bootsraping an image.
	 Set up a large oldSpace and an empty newSpace and set-up freeStart and scavengeThreshold
	 to allocate in oldSpace.  Later on (in initializePostBootstrap) freeStart and scavengeThreshold
	 will be set to sane values."

	<doNotGenerate>
	| allocatedMemory newSpaceStartOffset |
	self assert: (memoryBytes \\ objectRepresentation allocationUnit = 0 and: [ 
			 newSpaceBytes \\ objectRepresentation allocationUnit = 0 and: [ 
				 codeBytes \\ objectRepresentation allocationUnit = 0 and: [ 
					 initialAddress \\ objectRepresentation allocationUnit = 0 ] ] ]).
	newSpaceStartOffset := codeBytes + stackBytes
	                 + methodCacheSize + primitiveLogSize
	                 + rumpCStackSize.
	allocatedMemory := newSpaceStartOffset + newSpaceBytes + memoryBytes.
	memory := self
		allocateMemoryOfSize: allocatedMemory
		initialAddress: initialAddress.
	newSpaceStart := initialAddress + newSpaceStartOffset.
	endOfMemory := freeOldSpaceStart := initialAddress + allocatedMemory.
	"leave newSpace empty for the bootstrap"
	freeStart := newSpaceBytes + newSpaceStart.
	oldSpaceStart := newSpaceLimit := newSpaceBytes + newSpaceStart.
	scavengeThreshold := allocatedMemory. "i.e. /don't/ scavenge."
	scavenger := SpurGenerationScavenger simulatorClass new.
	scavenger manager: objectRepresentation.
	scavenger
		newSpaceStart: newSpaceStart
		newSpaceBytes: newSpaceBytes
		survivorBytes: newSpaceBytes // self scavengerDenominator.
	compactor := self class compactorClass simulatorClass new
		             manager: objectRepresentation;
		             yourself
]

{ #category : #allocation }
SpurGenerationalGC >> allocateNewSpaceSlots: numSlots format: formatField classIndex: classIndex [
	"Allocate an object with numSlots in newSpace.  This is for the `ee' execution engine allocations,
	 and must be satisfied.  If no memory is available, abort.  If the allocation pushes freeStart past
	 scavengeThreshold and a scavenge is not already scheduled, schedule a scavenge."
	| numBytes newObj |
	"Object headers are 8 bytes in length if the slot size fits in the num slots field (max implies overflow),
	 16 bytes otherwise (num slots in preceding word).
	 Objects always have at least one slot, for the forwarding pointer,
	 and are multiples of 8 bytes in length."
	numSlots >= objectRepresentation numSlotsMask
		ifTrue:
			[(objectRepresentation wordSize >= 8 and: [numSlots > 16rffffffff]) ifTrue:
				[^nil]. "overflow size must fit in 32-bits"
			 newObj := freeStart + objectRepresentation baseHeaderSize.
			 numBytes := objectRepresentation largeObjectBytesForSlots: numSlots]
		ifFalse:
			[newObj := freeStart.
			 numBytes := objectRepresentation smallObjectBytesForSlots: numSlots].
	
	freeStart + numBytes > scavengeThreshold ifTrue:
		[needGCFlag ifFalse: [self scheduleScavenge].
		 freeStart + numBytes > scavenger eden limit ifTrue:
			[self error: 'no room in eden for allocateNewSpaceSlots:format:classIndex:'.
			 ^0]].
	numSlots >= objectRepresentation numSlotsMask
		ifTrue: "for header parsing we put a saturated slot count in the prepended overflow size word"
			[self flag: #endianness.
			 self longAt: freeStart put: numSlots.
			 self longAt: freeStart + 4 put: self numSlotsMask << self numSlotsHalfShift.
			 self long64At: newObj put: (objectRepresentation headerForSlots: self numSlotsMask format: formatField classIndex: classIndex)]
		ifFalse:
			[objectRepresentation long64At: newObj put: (objectRepresentation headerForSlots: numSlots format: formatField classIndex: classIndex)].
	self assert: numBytes \\ objectRepresentation allocationUnit = 0.
	self assert: newObj \\ objectRepresentation allocationUnit = 0.
	freeStart := freeStart + numBytes.
	^newObj
]

{ #category : #'free space' }
SpurGenerationalGC >> allocateOldSpaceChunkOfBytes: chunkBytes [
	"Answer a chunk of oldSpace from the free lists, if available,
	 otherwise answer nil.  Break up a larger chunk if one of the
	 exact size does not exist.  N.B.  the chunk is simply a pointer, it
	 has no valid header.  The caller *must* fill in the header correctly."
	<var: #chunkBytes type: #usqInt>
	| initialIndex chunk index nodeBytes parent child |
	"for debugging:" "totalFreeOldSpace := self totalFreeListBytes"
	totalFreeOldSpace := totalFreeOldSpace - chunkBytes. "be optimistic (& don't wait for the write)"
	initialIndex := chunkBytes / objectRepresentation allocationUnit.
	(initialIndex < self numFreeLists and: [1 << initialIndex <= freeListsMask]) ifTrue:
		[(freeListsMask anyMask: 1 << initialIndex) ifTrue:
			[(chunk := freeLists at: initialIndex) ~= 0 ifTrue:
				[self assert: chunk = (objectRepresentation startOfObject: chunk).
				 self assertValidFreeObject: chunk.
				 self unlinkFreeChunk: chunk atIndex: initialIndex chunkBytes: chunkBytes.
				^ chunk].
			 freeListsMask := freeListsMask - (1 << initialIndex)].
		 "first search for free chunks of a multiple of chunkBytes in size"
		 index := initialIndex.
		 [(index := index + index) < self numFreeLists
		  and: [1 << index <= freeListsMask]] whileTrue:
			[(freeListsMask anyMask: 1 << index) ifTrue:
				[(chunk := freeLists at: index) ~= 0 ifTrue:
					[self assert: chunk = (objectRepresentation startOfObject: chunk).
					 self assertValidFreeObject: chunk.
					 self unlinkFreeChunk: chunk atIndex: index isLilliputianSize: false.
					 self assert: (objectRepresentation bytesInObject: chunk) = (index * objectRepresentation allocationUnit).
					 self freeChunkWithBytes: index * objectRepresentation allocationUnit - chunkBytes
						at: (objectRepresentation startOfObject: chunk) + chunkBytes.
					^chunk].
				 freeListsMask := freeListsMask - (1 << index)]].
		 "now get desperate and use the first that'll fit.
		  Note that because the minimum free size is 16 bytes (2 * allocationUnit), to
		  leave room for the forwarding pointer/next free link, we can only break chunks
		  that are at least 16 bytes larger, hence start at initialIndex + 2."
		 index := initialIndex + 1.
		 [(index := index + 1) < self numFreeLists
		  and: [1 << index <= freeListsMask]] whileTrue:
			[(freeListsMask anyMask: 1 << index) ifTrue:
				[(chunk := freeLists at: index) ~= 0 ifTrue:
					[self assert: chunk = (objectRepresentation startOfObject: chunk).
					 self assertValidFreeObject: chunk.
					 self unlinkFreeChunk: chunk atIndex: index isLilliputianSize: false.
					 self assert: (objectRepresentation bytesInObject: chunk) = (index * objectRepresentation allocationUnit).
					 self freeChunkWithBytes: index * objectRepresentation allocationUnit - chunkBytes
						at: (objectRepresentation startOfObject: chunk) + chunkBytes.
					^chunk].
				 freeListsMask := freeListsMask - (1 << index)]]].

	"Large chunk, or no space on small free lists.  Search the large chunk list.
	 Large chunk list organized as a tree, each node of which is a list of chunks
	 of the same size. Beneath the node are smaller and larger blocks.
	 When the search ends parent should hold the smallest chunk at least as
	 large as chunkBytes, or 0 if none."
	parent := 0.
	child := freeLists at: 0.
	[child ~= 0] whileTrue:
		[| childBytes |
		 self assertValidFreeObject: child.
		 childBytes := objectRepresentation bytesInObject: child.
		 childBytes = chunkBytes
			ifTrue: "size match; try to remove from list at node."
				[chunk := self fetchPointer: self freeChunkNextIndex
								ofFreeChunk: child.
				 chunk ~= 0 ifTrue:
					[self assertValidFreeObject: chunk.
					 self 
						setNextFreeChunkOf: child 
						withValue: (self fetchPointer: self freeChunkNextIndex ofFreeChunk: chunk) 
						isLilliputianSize: false.
					 ^objectRepresentation startOfObject: chunk].
				 nodeBytes := childBytes.
				 parent := child.
				 child := 0] "break out of loop to remove interior node"
			ifFalse:
				["Note that because the minimum free size is 16 bytes (2 * allocationUnit), to
				  leave room for the forwarding pointer/next free link, we can only break chunks
				  that are at least 16 bytes larger, hence reject chunks < 2 * allocationUnit larger."
				childBytes <= (chunkBytes + objectRepresentation allocationUnit)
					ifTrue: "node too small; walk down the larger size of the tree"
						[child := self fetchPointer: self freeChunkLargerIndex ofFreeChunk: child]
					ifFalse:
						[parent := child. "parent will be smallest node >= chunkBytes + allocationUnit"
						 nodeBytes := childBytes.
						 child := self fetchPointer: self freeChunkSmallerIndex ofFreeChunk: child]]].
	parent = 0 ifTrue:
		[totalFreeOldSpace := totalFreeOldSpace + chunkBytes. "optimism was unfounded"
		 ^nil].

	"self printFreeChunk: parent"
	self assert: (nodeBytes = chunkBytes or: [nodeBytes >= (chunkBytes + (2 * objectRepresentation allocationUnit))]).
	self assert: (objectRepresentation bytesInObject: parent) = nodeBytes.

	"attempt to remove from list"
	chunk := self fetchPointer: self freeChunkNextIndex ofFreeChunk: parent.
	chunk ~= 0 ifTrue:
		[self assert: (chunkBytes = nodeBytes or: [chunkBytes + objectRepresentation allocationUnit < nodeBytes]).
		self 
			setNextFreeChunkOf: parent 
			withValue: (self fetchPointer: self freeChunkNextIndex ofFreeChunk: chunk) 
			isLilliputianSize: false.
		 chunkBytes ~= nodeBytes ifTrue:
			[self freeChunkWithBytes: nodeBytes - chunkBytes
					at: (objectRepresentation startOfObject: chunk) + chunkBytes].
		 ^self startOfObject: chunk].

	"no list; remove the interior node"
	chunk := parent.
	self unlinkSolitaryFreeTreeNode: chunk.

	"if there's space left over, add the fragment back."
	chunkBytes ~= nodeBytes ifTrue:
		[self freeChunkWithBytes: nodeBytes - chunkBytes
				at: (objectRepresentation startOfObject: chunk) + chunkBytes].
	^objectRepresentation startOfObject: chunk
]

{ #category : #'free space' }
SpurGenerationalGC >> allocateOldSpaceChunkOfBytes: chunkBytes suchThat: acceptanceBlock [
	"Answer a chunk of oldSpace from the free lists that satisfies acceptanceBlock,
	 if available, otherwise answer nil.  Break up a larger chunk if one of the exact
	 size cannot be found.  N.B.  the chunk is simply a pointer, it has no valid header.
	 The caller *must* fill in the header correctly."
	<var: #chunkBytes type: #usqInt>
	| initialIndex node next prev index child childBytes acceptedChunk acceptedNode |
	<inline: true> "must inline for acceptanceBlock"
	"for debugging:" "totalFreeOldSpace := self totalFreeListBytes"
	totalFreeOldSpace := totalFreeOldSpace - chunkBytes. "be optimistic (& don't wait for the write)"
	initialIndex := chunkBytes / objectRepresentation allocationUnit.
	(initialIndex < self numFreeLists and: [1 << initialIndex <= freeListsMask]) ifTrue:
		[(freeListsMask anyMask: 1 << initialIndex) ifTrue:
			[(node := freeLists at: initialIndex) = 0
				ifTrue: [freeListsMask := freeListsMask - (1 << initialIndex)]
				ifFalse:
					[prev := 0.
					 [node ~= 0] whileTrue:
						[self assert: node = (self startOfObject: node).
						 self assertValidFreeObject: node.
						 next := self fetchPointer: self freeChunkNextIndex ofFreeChunk: node.
						 (acceptanceBlock value: node) ifTrue:
							[prev = 0
								ifTrue: [self unlinkFreeChunk: node atIndex: initialIndex chunkBytes: chunkBytes]
								ifFalse: [self setNextFreeChunkOf: prev withValue: next chunkBytes: chunkBytes].
							 ^node].
						 prev := node.
						 node := next]]].
		 "first search for free chunks of a multiple of chunkBytes in size"
		 index := initialIndex.
		 [(index := index + initialIndex) < self numFreeLists
		  and: [1 << index <= freeListsMask]] whileTrue:
			[(freeListsMask anyMask: 1 << index) ifTrue:
				[(node := freeLists at: index) = 0
					ifTrue: [freeListsMask := freeListsMask - (1 << index)]
					ifFalse:
						[prev := 0.
						 [node ~= 0] whileTrue:
							[self assert: node = (self startOfObject: node).
							  self assertValidFreeObject: node.
							 next := self fetchPointer: self freeChunkNextIndex ofFreeChunk: node.
							 (acceptanceBlock value: node) ifTrue:
								[prev = 0
									ifTrue: [self unlinkFreeChunk: node atIndex: index isLilliputianSize: false.]
									ifFalse: [self setNextFreeChunkOf: prev withValue: next isLilliputianSize: false.]. 
								 self freeChunkWithBytes: index * self allocationUnit - chunkBytes
									at: (self startOfObject: node) + chunkBytes.
								 ^node].
							 prev := node.
							 node := next]]]].
		 "now get desperate and use the first that'll fit.
		  Note that because the minimum free size is 16 bytes (2 * allocationUnit), to
		  leave room for the forwarding pointer/next free link, we can only break chunks
		  that are at least 16 bytes larger, hence start at initialIndex + 2."
		 index := initialIndex + 1.
		 [(index := index + 1) < self numFreeLists
		  and: [1 << index <= freeListsMask]] whileTrue:
			[(freeListsMask anyMask: 1 << index) ifTrue:
				[(node := freeLists at: index) = 0
					ifTrue: [freeListsMask := freeListsMask - (1 << index)]
					ifFalse:
						[prev := 0.
						 [node ~= 0] whileTrue:
							[self assert: node = (self startOfObject: node).
							  self assertValidFreeObject: node.
							 next := self fetchPointer: self freeChunkNextIndex ofFreeChunk: node.
							 (acceptanceBlock value: node) ifTrue:
								[prev = 0
									ifTrue: [self unlinkFreeChunk: node atIndex: index isLilliputianSize: false.]
									ifFalse: [self setNextFreeChunkOf: prev withValue: next isLilliputianSize: false.]. 
								 self freeChunkWithBytes: index * self allocationUnit - chunkBytes
									at: (self startOfObject: node) + chunkBytes.
								 ^node].
							 prev := node.
							 node := next]]]]].

	"Large chunk, or no space on small free lists.  Search the large chunk list.
	 Large chunk list organized as a tree, each node of which is a list of chunks
	 of the same size. Beneath the node are smaller and larger blocks.
	 When the search ends parent should hold the smallest chunk at least as
	 large as chunkBytes, or 0 if none.  acceptedChunk and acceptedNode save
	 us from having to back-up when the acceptanceBlock filters-out all nodes
	 of the right size, but there are nodes of the wrong size it does accept."
	child := freeLists at: 0.
	node := acceptedChunk := acceptedNode := 0.
	[child ~= 0] whileTrue:
		[ self assertValidFreeObject: child.
		 childBytes := objectRepresentation bytesInObject: child.
		 childBytes = chunkBytes ifTrue: "size match; try to remove from list at node."
			[node := child.
			 [prev := node.
			  node := self fetchPointer: self freeChunkNextIndex ofFreeChunk: node.
			  node ~= 0] whileTrue:
				[(acceptanceBlock value: node) ifTrue:
					[self assertValidFreeObject: node.
					 self 
						setNextFreeChunkOf: prev 
						withValue: (self fetchPointer: self freeChunkNextIndex ofFreeChunk: node) 
						isLilliputianSize: false.
					 ^self startOfObject: node]].
			 (acceptanceBlock value: child) ifTrue:
				[next := self fetchPointer: self freeChunkNextIndex ofFreeChunk: child.
				 next = 0
					ifTrue: "no list; remove the interior node"
						[self unlinkSolitaryFreeTreeNode: child]
					ifFalse: "list; replace node with it"
						[self inFreeTreeReplace: child with: next].
				 ^objectRepresentation startOfObject: child]].
		 child ~= 0 ifTrue:
			["Note that because the minimum free size is 16 bytes (2 * allocationUnit), to
			  leave room for the forwarding pointer/next free link, we can only break chunks
			  that are at least 16 bytes larger, hence reject chunks < 2 * allocationUnit larger."
			childBytes <= (chunkBytes + objectRepresentation allocationUnit)
				ifTrue: "node too small; walk down the larger size of the tree"
					[child := self fetchPointer: self freeChunkLargerIndex ofFreeChunk: child]
				ifFalse:
					[self flag: 'we can do better here; preferentially choosing the lowest node. That would be a form of best-fit since we are trying to compact down'.
					 node := child.
					 child := self fetchPointer: self freeChunkSmallerIndex ofFreeChunk: node.
					 acceptedNode = 0 ifTrue:
						[acceptedChunk := node.
						 "first search the list."
						 [acceptedChunk := self fetchPointer: self freeChunkNextIndex
													ofFreeChunk: acceptedChunk.
						  (acceptedChunk ~= 0 and: [acceptanceBlock value: acceptedChunk]) ifTrue:
							[acceptedNode := node].
						  acceptedChunk ~= 0 and: [acceptedNode = 0]] whileTrue.
						 "nothing on the list; will the node do?  This prefers
						  acceptable nodes higher up the tree over acceptable
						  list elements further down, but we haven't got all day..."
						 (acceptedNode = 0
						  and: [acceptanceBlock value: node]) ifTrue:
							[acceptedNode := node.
							 child := 0 "break out of loop now we have an acceptedNode"]]]]].

	acceptedNode ~= 0 ifTrue:
		[acceptedChunk ~= 0 ifTrue:
			[self assert: (self bytesInObject: acceptedChunk) >= (chunkBytes + self allocationUnit).
			 [next := self fetchPointer: self freeChunkNextIndex ofFreeChunk: acceptedNode.
			  next ~= acceptedChunk] whileTrue:
				[acceptedNode := next].
			 self 
				setNextFreeChunkOf: acceptedNode 
				withValue: (self fetchPointer: self freeChunkNextIndex ofFreeChunk: acceptedChunk) 
				isLilliputianSize: false.
			self freeChunkWithBytes: (self bytesInObject: acceptedChunk) - chunkBytes
					at: (self startOfObject: acceptedChunk) + chunkBytes.
			^self startOfObject: acceptedChunk].
		next := self fetchPointer: self freeChunkNextIndex ofFreeChunk: acceptedNode.
		next = 0
			ifTrue: "no list; remove the interior node"
				[self unlinkSolitaryFreeTreeNode: acceptedNode]
			ifFalse: "list; replace node with it"
				[self inFreeTreeReplace: acceptedNode with: next].
		 self assert: (objectRepresentation bytesInObject: acceptedNode) >= (chunkBytes + objectRepresentation allocationUnit).
		 self freeChunkWithBytes: (objectRepresentation bytesInObject: acceptedNode) - chunkBytes
				at: (objectRepresentation startOfObject: acceptedNode) + chunkBytes.
		^objectRepresentation startOfObject: acceptedNode].

	totalFreeOldSpace := totalFreeOldSpace + chunkBytes. "optimism was unfounded"
	^nil
]

{ #category : #allocation }
SpurGenerationalGC >> allocateSmallNewSpaceSlots: numSlots format: formatField classIndex: classIndex [
	"Allocate an object with numSlots in newSpace, where numSlots is known to be small.
	 This is for the `ee' execution engine allocations, and must be satisfied.  If no memory
	 is available, abort.  If the allocation pushes freeStart past scavengeThreshold and a
	 scavenge is not already scheduled, schedule a scavenge."
	<inline: true>
	| numBytes newObj |
	self assert: numSlots < objectRepresentation numSlotsMask.
	newObj := freeStart.
	numBytes := objectRepresentation smallObjectBytesForSlots: numSlots.
	self assert: numBytes \\ objectRepresentation allocationUnit = 0.
	self assert: newObj \\ objectRepresentation allocationUnit = 0.
	freeStart + numBytes > scavengeThreshold ifTrue:
		[needGCFlag ifFalse: [self scheduleScavenge].
		 freeStart + numBytes > scavenger eden limit ifTrue:
			[self error: 'no room in eden for allocateSmallNewSpaceSlots:format:classIndex:'.
			 ^0]].
	objectRepresentation long64At: newObj put: (objectRepresentation headerForSlots: numSlots format: formatField classIndex: classIndex).
	freeStart := freeStart + numBytes.
	^newObj
]

{ #category : #'free space' }
SpurGenerationalGC >> assertFreeChunkPrevHeadZero [
	|min|
	self wordSize = 8 ifTrue: [min := 3] ifFalse: [min := 2].
	min to: self numFreeLists - 1 do:
		[:i| 
		 	(freeLists at: i) ~= 0 ifTrue:
				[self deny: (self isLilliputianSize: (freeLists at: i)).
				 self assert: (self fetchPointer: self freeChunkPrevIndex ofFreeChunk: (freeLists at: i)) = 0]].
	"Large chunks"
	self freeTreeNodesDo: [:freeNode |
		self assert: (self fetchPointer: self freeChunkPrevIndex ofFreeChunk: freeNode) = 0.
		freeNode].
	^ true
]

{ #category : #'free space' }
SpurGenerationalGC >> assertInnerValidFreeObject: objOop [
	<inline: #never> "we don't want to inline so we can nest that in an assertion with the return true so the production VM does not generate any code here, while in simulation, the code breaks on the assertion we want to."
	| chunk index |
	self assert: (self oop: (objectRepresentation addressAfter: objOop) isLessThanOrEqualTo: endOfMemory).
	chunk := self fetchPointer: self freeChunkNextIndex ofFreeChunk: objOop.
	self assert: (chunk = 0 or: [self isFreeOop: chunk]).
	(objectRepresentation isLilliputianSize: (objectRepresentation bytesInObject: objOop)) ifFalse:
		["double linkedlist assertions"
		 chunk := self fetchPointer: self freeChunkNextIndex ofFreeChunk: objOop.
		 chunk = 0 ifFalse: 
			[self assert: (self isFreeOop: chunk).
			 self assert: objOop = (self fetchPointer: self freeChunkPrevIndex ofFreeChunk: chunk)].
		chunk := self fetchPointer: self freeChunkPrevIndex ofFreeChunk: objOop.
		index := (objectRepresentation bytesInObject: objOop) / objectRepresentation allocationUnit.
		(index < self numFreeLists and: [1 << index <= freeListsMask]) 
			ifTrue: 
				[(freeLists at: index) = objOop ifTrue: [self assert: chunk = 0]]
			ifFalse: 
				[self freeTreeNodesDo: [:freeNode |
					freeNode = objOop ifTrue: [self assert: chunk = 0]. freeNode]].
		 chunk = 0 ifFalse: 
			[self assert: (self isFreeOop: chunk).
			 self assert: objOop = (self fetchPointer: self freeChunkNextIndex ofFreeChunk: chunk)]].
	(self isLargeFreeObject: objOop) ifTrue: 
		["Tree assertions"
		chunk := self fetchPointer: self freeChunkParentIndex ofFreeChunk: objOop.
		self assert: (chunk = 0 or: [(self isFreeOop: chunk) and: [self isLargeFreeObject: chunk]]).
		chunk := self fetchPointer: self freeChunkSmallerIndex ofFreeChunk: objOop.
		self assert: (chunk = 0 or: [(self isFreeOop: chunk) and: [self isLargeFreeObject: chunk]]).
		chunk := self fetchPointer: self freeChunkLargerIndex ofFreeChunk: objOop.
		self assert: (chunk = 0 or: [(self isFreeOop: chunk) and: [self isLargeFreeObject: chunk]])].
	^ true
]

{ #category : #'free space' }
SpurGenerationalGC >> assertValidFreeObject: objOop [
	<inline: true>
	"assertInnerValidFreeObject: is never inlined and always returns true.
	 For the production VM, this is entirely removed.
	 For the other VMs and in simulation, the code breaks at the first warning/assertion failure"
	self assert: (self assertInnerValidFreeObject: objOop)
]

{ #category : #'growing/shrinking memory' }
SpurGenerationalGC >> assimilateNewSegment: segInfo [
	"Update after adding a segment.
	 Here we set freeOldSpaceStart & endOfMemory if required."
	<var: #segInfo type: #'SpurSegmentInfo *'>
	segInfo segLimit >= endOfMemory ifTrue:
		[freeOldSpaceStart :=
		 endOfMemory := segInfo segLimit - self bridgeSize]
]

{ #category : #'growing/shrinking memory' }
SpurGenerationalGC >> attemptToShrink [
	"Attempt to shrink memory after successfully reclaiming lots of memory.
	 If there's enough memory to shrink then be sure to attept to shrink by
	 at least growHeaqdroom because segments are typically of that size."
	(totalFreeOldSpace > shrinkThreshold
	 and: [totalFreeOldSpace > growHeadroom
	 and: [objectRepresentation segmentManager shrinkObjectMemory: (totalFreeOldSpace - growHeadroom max: growHeadroom)]]) ifTrue:
		[statShrinkMemory := statShrinkMemory + 1]
]

{ #category : #snapshot }
SpurGenerationalGC >> baseAddressOfImage [
	^oldSpaceStart
]

{ #category : #'gc - scavenge/compact' }
SpurGenerationalGC >> beginSlidingCompaction [
	gcPhaseInProgress := SlidingCompactionInProgress
]

{ #category : #'debug support' }
SpurGenerationalGC >> bitsSetInFreeSpaceMaskForAllFreeLists [
	0 to: self numFreeLists - 1 do:
		[:i|
		((freeLists at: i) ~= 0
		 and: [1 << i noMask: freeListsMask]) ifTrue:
			[^false]].
	^true
]

{ #category : #segments }
SpurGenerationalGC >> bridgeSize [
	^2 * objectRepresentation baseHeaderSize
]

{ #category : #'free space' }
SpurGenerationalGC >> bytesLeft: includeSwapSpace [
	"Answer the amount of available free space. If includeSwapSpace is true, include
	 possibly available swap space. If includeSwapSpace is false, include possibly available
	 physical memory.  N.B. includeSwapSpace is ignored; answer total heap free space
	 minus the reserve available for flushing the tsack zone."
	^totalFreeOldSpace
	+ (scavenger eden limit - freeStart)
	+ (scavenger pastSpace limit - pastSpaceStart)
	+ (scavenger futureSpace limit - scavenger futureSpace limit)
	- coInterpreter interpreterAllocationReserveBytes
]

{ #category : #'free space' }
SpurGenerationalGC >> bytesLeftInOldSpace [
	"Answer the amount of available free old space.  Used by primitiveFullGC
	 to answer the current available memory."
	^totalFreeOldSpace
]

{ #category : #'debug support' }
SpurGenerationalGC >> cheapAddressCouldBeInHeap: address [ 
	^(address bitAnd: self wordSize - 1) = 0
	  and: [(self oop: address isGreaterThanOrEqualTo: newSpaceStart)
	  and: [self oop: address isLessThan: endOfMemory]]
]

{ #category : #'plugin support' }
SpurGenerationalGC >> cheapIsInMemory: address [
	"Answer if the given address is in ST object memory.  For simulation only."
	<doNotGenerate>
	^address >= newSpaceStart and: [address < endOfMemory]
]

{ #category : #allocation }
SpurGenerationalGC >> checkAllocFiller [
	<doNotGenerate>
	"in the Spur bootstrap coInterpreter may not be initialized..."
	^coInterpreter notNil and: [coInterpreter checkAllocFiller]
]

{ #category : #'gc - scavenging' }
SpurGenerationalGC >> checkForAvailableSlots: slots [
	"Check for slots worth of free space being available.  Answer if that many slots are available.
	 If that many slots are not availabe, schedule a scavenge."
	<inline: true>
	freeStart + (self bytesPerOop * slots) <= scavengeThreshold ifTrue:
		[^true].
	needGCFlag := true.
	^false
]

{ #category : #'debug support' }
SpurGenerationalGC >> checkFreeSpace: gcModes [
	self assert: self bitsSetInFreeSpaceMaskForAllFreeLists.
	self assert: totalFreeOldSpace = self totalFreeListBytes.
	(gcModes > 0
	 and: [checkForLeaks allMask: (GCModeFreeSpace bitOr: gcModes)]) ifTrue:
		[self runLeakCheckerForFreeSpace: GCModeFreeSpace]
]

{ #category : #'debug support' }
SpurGenerationalGC >> checkHeapFreeSpaceIntegrity [
	"Perform an integrity/leak check using the heapMap.  Assume clearLeakMapAndMapAccessibleFreeSpace
	 has set a bit at each free chunk's header.  Scan all objects in the heap checking that no pointer points
	 to a free chunk and that all free chunks that refer to others refer to marked chunks.  Answer if all checks pass."
	| ok total |
	<inline: false>
	<var: 'total' type: #usqInt>
	ok := true.
	total := 0.
	0 to: self numFreeLists - 1 do:
		[:i|
		(freeLists at: i) ~= 0 ifTrue:
			[(heapMap heapMapAtWord: (self pointerForOop: (freeLists at: i))) = 0 ifTrue:
				[coInterpreter print: 'leak in free list '; printNum: i; print: ' to non-free '; printHex: (freeLists at: i); cr.
				 ok := false]]].

	"Excuse the duplication but performance is at a premium and we avoid
	 some tests by splitting the newSpace and oldSpace enumerations."
	self allNewSpaceEntitiesDo:
		[:obj| | fieldOop |
		 (self isFreeObject: obj)
			ifTrue:
				[coInterpreter print: 'young object '; printHex: obj; print: ' is free'; cr.
				 ok := false]
			ifFalse:
				[0 to: (memoryManager numPointerSlotsOf: obj) - 1 do:
					[:fi|
					 fieldOop := memoryManager fetchPointer: fi ofObject: obj.
					 (memoryManager isNonImmediate: fieldOop) ifTrue:
						[(heapMap heapMapAtWord: (memoryManager pointerForOop: fieldOop)) ~= 0 ifTrue:
							[coInterpreter print: 'object leak in '; printHex: obj; print: ' @ '; printNum: fi; print: ' = '; printHex: fieldOop; print: ' is free'; cr.
							 ok := false]]]]].
	self allOldSpaceEntitiesDo:
		[:obj| | fieldOop |
		(self isFreeObject: obj)
			ifTrue:
				[(heapMap heapMapAtWord: (self pointerForOop: obj)) = 0 ifTrue:
					[coInterpreter print: 'leak in free chunk '; printHex: obj; print: ' is unmapped?! '; cr.
					 ok := false].
				 fieldOop := memoryManager fetchPointer: self freeChunkNextIndex ofFreeChunk: obj.
				 (fieldOop ~= 0
				 and: [(heapMap heapMapAtWord: (self pointerForOop: fieldOop)) = 0]) ifTrue:
					[coInterpreter print: 'leak in free chunk '; printHex: obj; print: ' @ 0 = '; printHex: fieldOop; print: ' is unmapped'; cr.
					 ok := false].
				(memoryManager isLilliputianSize: (memoryManager bytesInObject: obj)) ifFalse:
					[fieldOop := memoryManager fetchPointer: self freeChunkPrevIndex ofFreeChunk: obj.
					 (fieldOop ~= 0
					 and: [(heapMap heapMapAtWord: (memoryManager pointerForOop: fieldOop)) = 0]) ifTrue:
						[coInterpreter print: 'leak in free chunk '; printHex: obj; print: ' @ 0 = '; printHex: fieldOop; print: ' is unmapped'; cr.
						 ok := false]].
				(self isLargeFreeObject: obj) ifTrue:
					[self freeChunkParentIndex to: self freeChunkLargerIndex do:
						[:fi|
						 fieldOop := self fetchPointer: fi ofFreeChunk: obj.
						 (fieldOop ~= 0
						 and: [(heapMap heapMapAtWord: (memoryManager pointerForOop: fieldOop)) = 0]) ifTrue:
							[coInterpreter print: 'leak in free chunk '; printHex: obj; print: ' @ '; printNum: fi; print: ' = '; printHex: fieldOop; print: ' is unmapped'; cr.
							 ok := false]]].
				total := total + (memoryManager bytesInObject: obj)]
			ifFalse:
				[0 to: (memoryManager numPointerSlotsOf: obj) - 1 do:
					[:fi|
					 (memoryManager isForwarded: obj)
						ifTrue: 
							[self assert: fi = 0. "I'm now trying to use forwarders in GC algorithms..."
							 fieldOop := memoryManager fetchPointer: fi ofMaybeForwardedObject: obj] 
						ifFalse: "We keep #fetchPointer:ofObject: API here for assertions"
							[fieldOop := memoryManager fetchPointer: fi ofObject: obj].
					 (memoryManager isNonImmediate: fieldOop) ifTrue:
						[(heapMap heapMapAtWord: (memoryManager pointerForOop: fieldOop)) ~= 0 ifTrue:
							[coInterpreter print: 'object leak in '; printHex: obj; print: ' @ '; printNum: fi; print: ' = '; printHex: fieldOop; print: ' is free'; cr.
							 ok := false]]]]].
	total ~= totalFreeOldSpace ifTrue:
		[coInterpreter print: 'incorrect totalFreeOldSpace; expected '; printNum: totalFreeOldSpace; print: ' found '; printNum: total; cr.
		 ok := false].
	^ok
]

{ #category : #'debug support' }
SpurGenerationalGC >> checkHeapIntegrity: excludeUnmarkedObjs classIndicesShouldBeValid: classIndicesShouldBeValid [
	"Perform an integrity/leak check using the heapMap.  Assume clearLeakMapAndMapAccessibleObjects
	 has set a bit at each (non-free) object's header.  Scan all objects in the heap checking that every
	 pointer points to a header.  Scan the rememberedSet, remapBuffer and extraRootTable checking
	 that every entry is a pointer to a header. Check that the number of roots is correct and that all
	 rememberedSet entries have their isRemembered: flag set.  Answer if all checks pass."
	| ok numRememberedObjectsInHeap |
	<inline: false>
	ok := true.
	numRememberedObjectsInHeap := 0.
	0 to: self numFreeLists - 1 do:
		[:i|
		(freeLists at: i) ~= 0 ifTrue:
			[(heapMap heapMapAtWord: (self pointerForOop: (freeLists at: i))) ~= 0 ifTrue:
				[coInterpreter print: 'leak in free list '; printNum: i; print: ' to non-free '; printHex: (freeLists at: i); cr.
				 ok := false]]].

	"Excuse the duplication but performance is at a premium and we avoid
	 some tests by splitting the newSpace and oldSpace enumerations."
	self allNewSpaceEntitiesDo:
		[:obj| | fieldOop classIndex classOop |
		(self isFreeObject: obj)
			ifTrue:
				[coInterpreter print: 'young object '; printHex: obj; print: ' is free'; cr.
				 ok := false]
			ifFalse:
				[((self isMarked: obj) not and: [excludeUnmarkedObjs]) ifFalse:
					[(self isRemembered: obj) ifTrue:
						[coInterpreter print: 'young object '; printHex: obj; print: ' is remembered'; cr.
						 ok := false]].
					 (self isForwarded: obj)
						ifTrue:
							[fieldOop := self fetchPointer: 0 ofMaybeForwardedObject: obj.
							 (heapMap heapMapAtWord: (self pointerForOop: fieldOop)) = 0 ifTrue:
								[coInterpreter print: 'object leak in forwarder '; printHex: obj; print: ' to unmapped '; printHex: fieldOop; cr.
								 ok := false]]
						ifFalse:
							[classOop := self classOrNilAtIndex: (classIndex := self classIndexOf: obj).
							 (classIndicesShouldBeValid
							  and: [classOop = objectRepresentation nilObject
							  and: [(self isHiddenObj: obj) not]]) ifTrue:
								[coInterpreter print: 'object leak in '; printHex: obj; print: ' invalid class index '; printHex: classIndex; print: ' -> '; print: (classOop ifNil: ['nil'] ifNotNil: ['nilObj']); cr.
								 ok := false].
							 0 to: (self numPointerSlotsOf: obj) - 1 do:
								[:fi|
								 fieldOop := self fetchPointer: fi ofObject: obj.
								 (self isNonImmediate: fieldOop) ifTrue:
									[(heapMap heapMapAtWord: (self pointerForOop: fieldOop)) = 0 ifTrue:
										[coInterpreter print: 'object leak in '; printHex: obj; print: ' @ '; printNum: fi; print: ' = '; printHex: fieldOop; cr.
										 ok := false]]]]]].
	self allOldSpaceEntitiesDo:
		[:obj| | containsYoung fieldOop classIndex classOop |
		(self isFreeObject: obj)
			ifTrue:
				[(heapMap heapMapAtWord: (self pointerForOop: obj)) ~= 0 ifTrue:
					[coInterpreter print: 'leak in free chunk '; printHex: obj; print: ' is mapped?! '; cr.
					 ok := false].
				 fieldOop := self fetchPointer: self freeChunkNextIndex ofFreeChunk: obj.
				 (fieldOop ~= 0
				 and: [(heapMap heapMapAtWord: (self pointerForOop: fieldOop)) ~= 0]) ifTrue:
					[coInterpreter print: 'leak in free chunk '; printHex: obj; print: ' @ 0 = '; printHex: fieldOop; print: ' is mapped'; cr.
					 ok := false].
				(self isLilliputianSize: (self bytesInObject: obj)) ifFalse:
					[fieldOop := self fetchPointer: self freeChunkPrevIndex ofFreeChunk: obj.
					 (fieldOop ~= 0
					 and: [(heapMap heapMapAtWord: (self pointerForOop: fieldOop)) ~= 0]) ifTrue:
						[coInterpreter print: 'leak in free chunk '; printHex: obj; print: ' @ 1 = '; printHex: fieldOop; print: ' is mapped'; cr.
						 ok := false]].
				(self isLargeFreeObject: obj) ifTrue:
					[self freeChunkParentIndex to: self freeChunkLargerIndex do:
						[:fi|
						 fieldOop := self fetchPointer: fi ofFreeChunk: obj.
						 (fieldOop ~= 0
						 and: [(heapMap heapMapAtWord: (self pointerForOop: fieldOop)) ~= 0]) ifTrue:
							[coInterpreter print: 'leak in free chunk '; printHex: obj; print: ' @ '; printNum: fi; print: ' = '; printHex: fieldOop; print: ' is mapped'; cr.
							 
							 ok := false].]]]
			ifFalse:
				[(excludeUnmarkedObjs and: [(self isMarked: obj) not]) ifFalse:
					[containsYoung := false.
					 (self isRemembered: obj) ifTrue:
						[numRememberedObjectsInHeap := numRememberedObjectsInHeap + 1.
						 (scavenger isInRememberedSet: obj) ifFalse:
							[coInterpreter print: 'remembered object '; printHex: obj; print: ' is not in remembered table'; cr.
							 ok := false]].
					 (self isForwarded: obj)
						ifTrue:
							[fieldOop := self fetchPointer: 0 ofMaybeForwardedObject: obj.
							 (heapMap heapMapAtWord: (self pointerForOop: fieldOop)) = 0 ifTrue:
								[coInterpreter print: 'object leak in forwarder '; printHex: obj; print: ' to unmapped '; printHex: fieldOop; cr.
								 ok := false].
							 (self isReallyYoung: fieldOop) ifTrue:
								[containsYoung := true]]
						ifFalse:
							[classOop := self classOrNilAtIndex: (classIndex := self classIndexOf: obj).
							 (classIndicesShouldBeValid
							  and: [classOop = objectRepresentation nilObject
							  and: [classIndex > self lastClassIndexPun]]) ifTrue:
								[coInterpreter print: 'object leak in '; printHex: obj; print: ' invalid class index '; printHex: classIndex; print: ' -> '; print: (classOop ifNil: ['nil'] ifNotNil: ['nilObj']); cr.
								 ok := false].
							 0 to: (self numPointerSlotsOf: obj) - 1 do:
								[:fi|
								 fieldOop := self fetchPointer: fi ofObject: obj.
								 (self isNonImmediate: fieldOop) ifTrue:
									[(self heapMapAtWord: (self pointerForOop: fieldOop)) = 0 ifTrue:
										[coInterpreter print: 'object leak in '; printHex: obj; print: ' @ '; printNum: fi; print: ' = '; printHex: fieldOop; cr.
										 ok := false].
									 "don't be misled by CogMethods; they appear to be young, but they're not"
									 (self isReallyYoung: fieldOop) ifTrue:
										[containsYoung := true]]]].
					 containsYoung ifTrue:
						[(self isRemembered: obj) ifFalse:
							[coInterpreter print: 'unremembered object '; printHex: obj; print: ' contains young oop(s)'; cr.
							 ok := false]]]]].
	numRememberedObjectsInHeap ~= scavenger rememberedSetSize ifTrue:
		[coInterpreter
			print: 'root count mismatch. #heap roots ';
			printNum: numRememberedObjectsInHeap;
			print: '; #roots ';
			printNum: scavenger rememberedSetSize;
			cr.
		"But the system copes with overflow..."
		self flag: 'no support for remembered set overflow yet'.
		"ok := rootTableOverflowed and: [needGCFlag]"].
	scavenger rememberedSetWithIndexDo:
		[:obj :i|
		(obj bitAnd: self wordSize - 1) ~= 0
			ifTrue:
				[coInterpreter print: 'misaligned oop in remembered set @ '; printNum: i; print: ' = '; printHex: obj; cr.
				 
				 ok := false]
			ifFalse:
				[(heapMap heapMapAtWord: (self pointerForOop: obj)) = 0
					ifTrue:
						[coInterpreter print: 'object leak in remembered set @ '; printNum: i; print: ' = '; printHex: obj; cr.
						 
						 ok := false]
					ifFalse:
						[(self isYoung: obj) ifTrue:
							[coInterpreter print: 'non-root in remembered set @ '; printNum: i; print: ' = '; printHex: obj; cr.
							 
							 ok := false]]]].
	self objStack: mournQueue do:
		[:i :page| | obj |
		obj := self fetchPointer: i ofObject: page.
		(obj bitAnd: self wordSize - 1) ~= 0
			ifTrue:
				[coInterpreter print: 'misaligned oop in mournQueue @ '; printNum: i; print: ' in '; printHex: page; print: ' = '; printHex: obj; cr.
				 
				 ok := false]
			ifFalse:
				[(excludeUnmarkedObjs and: [(self isMarked: obj) not]) ifFalse:
					[(heapMap heapMapAtWord: (self pointerForOop: obj)) = 0 ifTrue:
						[coInterpreter print: 'object leak in mournQueue @ '; printNum: i; print: ' in '; printHex: page; print: ' = '; printHex: obj; cr.
						 
						 ok := false]]]].
	1 to: remapBufferCount do:
		[:ri| | obj |
		obj := remapBuffer at: ri.
		(obj bitAnd: self wordSize - 1) ~= 0
			ifTrue:
				[coInterpreter print: 'misaligned remapRoot @ '; printNum: ri; print: ' = '; printHex: obj; cr.
				 
				 ok := false]
			ifFalse:
				[(heapMap heapMapAtWord: (self pointerForOop: obj)) = 0 ifTrue:
					[coInterpreter print: 'object leak in remapRoots @ '; printNum: ri; print: ' = '; printHex: obj; cr.
					 
					 ok := false]]].
	1 to: extraRootCount do:
		[:ri| | obj |
		obj := (extraRoots at: ri) at: 0.
		(obj bitAnd: self wordSize - 1) ~= 0
			ifTrue:
				[coInterpreter print: 'misaligned extraRoot @ '; printNum: ri; print: ' => '; printHex: obj; cr.
				 
				 ok := false]
			ifFalse:
				[(heapMap heapMapAtWord: (self pointerForOop: obj)) = 0 ifTrue:
					[coInterpreter print: 'object leak in extraRoots @ '; printNum: ri; print: ' => '; printHex: obj; cr.
					 
					 ok := false]]].
	^ok
]

{ #category : #'debug support' }
SpurGenerationalGC >> checkMemoryMap [
	self assert: (self isYoungObject: newSpaceStart).
	self assert: (self isYoungObject: newSpaceLimit - self wordSize).
	self assert: (self isOldObject: newSpaceStart) not.
	self assert: (self isOldObject: newSpaceLimit - self wordSize) not.
	self assert: (self isYoungObject: newSpaceLimit) not.
	self assert: (self isYoungObject: oldSpaceStart) not.
	self assert: (self isYoungObject: endOfMemory) not.
	self assert: (self isOldObject: newSpaceLimit).
	self assert: (self isOldObject: oldSpaceStart).
	self assert: (self isOldObject: endOfMemory)
]

{ #category : #'debug support' }
SpurGenerationalGC >> checkOkayYoungReferrer: obj [
	"Verify that the given obj is a valid youngReferrer. Check remembered is set and
	 is in remembered set.  Answer true if OK.  Otherwise print reason and answer false.
	 Assumes the object contains young references."

	(self oop: obj isLessThan: newSpaceLimit) ifTrue:
		[^true].

	(self isRemembered: obj) ifFalse:
		[ self print: 'remembered bit is not set in '; printHex: obj; cr. ^false ].

	(gc scavenger isInRememberedSet: obj) ifTrue: [^true].

	self printHex: obj; print: ' has remembered bit set but is not in remembered set'; cr.

	^false

]

{ #category : #'debug support' }
SpurGenerationalGC >> clearLeakMapAndMapAccessibleFreeSpace [
	"Perform an integrity/leak check using the heapMap.  Set a bit at each free chunk's header."
	<inline: false>
	heapMap clearHeapMap.
	self allOldSpaceEntitiesFrom: self firstObject
		do: [:objOop|
			(self isFreeObject: objOop) ifTrue:
				[heapMap heapMapAtWord: (self pointerForOop: objOop) Put: 1]]
]

{ #category : #accessing }
SpurGenerationalGC >> compactor [
	"This is really only for tests..."
	^compactor
]

{ #category : #'free space' }
SpurGenerationalGC >> computeFreeSpacePostSwizzle [
	totalFreeOldSpace := self totalFreeListBytes.
	self checkFreeSpace: 0
]

{ #category : #'class table' }
SpurGenerationalGC >> countNumClassPagesPreSwizzle: bytesToShift [
	"Compute the used size of the class table before swizzling.  Needed to
	 initialize the classTableBitmap which is populated during adjustAllOopsBy:"
	| firstObj classTableRoot nilObjPreSwizzle |
	firstObj := self objectStartingAt: oldSpaceStart. "a.k.a. nilObj"
	"first five objects are nilObj, falseObj, trueObj, freeListsObj, classTableRootObj"
	classTableRoot := self noInlineObjectAfter:
							(self noInlineObjectAfter:
									(self noInlineObjectAfter:
											(self noInlineObjectAfter: firstObj
												limit: endOfMemory)
										limit: endOfMemory)
								limit: endOfMemory)
							limit: endOfMemory.
	nilObjPreSwizzle := oldSpaceStart - bytesToShift.
	numClassTablePages := self numSlotsOf: classTableRoot.
	self assert: numClassTablePages = (self classTableRootSlots + self hiddenRootSlots).
	2 to: numClassTablePages - 1 do:
		[:i|
		(self fetchPointer: i ofObject: classTableRoot) = nilObjPreSwizzle ifTrue:
			[numClassTablePages := i.
			 ^self]]
	
]

{ #category : #'allocation accounting' }
SpurGenerationalGC >> currentAllocatedBytes [
	"Compute the current allocated bytes since last set.
	 This is the cumulative total in statAllocatedBytes plus the allocation since the last scavenge."
	| use |
	"Slang infers the type of the difference between two unsigned variables as signed.
	 In this case we want it to be unsigned."
	<var: 'use' type: #usqInt>
	use := objectRepresentation segmentManager totalOldSpaceCapacity - totalFreeOldSpace.
	^statAllocatedBytes
	 + (freeStart - scavenger eden start)
	 + (use - oldSpaceUsePriorToScavenge)
]

{ #category : #'weakness and ephemerality' }
SpurGenerationalGC >> dequeueMourner [
	"Answer the top mourner (ephemeron or weak array) from the queue or
	 nil if the queue is empty. We don't care about order; ephemerons are
	 fired in an arbitrary order based on where they are in the heap."
	^mournQueue ~= objectRepresentation nilObject ifTrue:
		[objectRepresentation popObjStack: mournQueue]
]

{ #category : #'free space' }
SpurGenerationalGC >> detachFreeObject: freeChunk [
	<inline: true>
	| chunkBytes |
	chunkBytes := objectRepresentation bytesInObject: freeChunk.
	totalFreeOldSpace := totalFreeOldSpace - chunkBytes.
	self unlinkFreeChunk: freeChunk chunkBytes: chunkBytes
]

{ #category : #'allocation accounting' }
SpurGenerationalGC >> doAllocationAccountingForScavenge [
	<inline: true>
	statAllocatedBytes := self currentAllocatedBytes
]

{ #category : #'gc - scavenging' }
SpurGenerationalGC >> doScavenge: tenuringCriterion [
	"The inner shell for scavenge, abstrascted out so globalGarbageCollect can use it."
	<inline: false>
	self doAllocationAccountingForScavenge.
	gcPhaseInProgress := ScavengeInProgress.
	pastSpaceStart := scavenger scavenge: tenuringCriterion.
	self assert: (self
					oop: pastSpaceStart
					isGreaterThanOrEqualTo: scavenger pastSpace start
					andLessThanOrEqualTo: scavenger pastSpace limit).
	freeStart := scavenger eden start.
	self initSpaceForAllocationCheck: (self addressOf: scavenger eden) limit: scavengeThreshold.
	gcPhaseInProgress := 0.
	self resetAllocationAccountingAfterGC
]

{ #category : #accessing }
SpurGenerationalGC >> endOfMemory [
	<cmacro: '() GIV(endOfMemory)'>
	^endOfMemory
]

{ #category : #accessing }
SpurGenerationalGC >> endOfMemory: anInteger [ 
	<doNotGenerate>
	endOfMemory := anInteger
]

{ #category : #'gc - scavenge/compact' }
SpurGenerationalGC >> endSlidingCompaction [
	gcPhaseInProgress := 0
]

{ #category : #'debug support' }
SpurGenerationalGC >> existInstancesInNewSpaceOf: classObj [
	| classIndex |
	classIndex := memoryManager rawHashBitsOf: classObj.
	self allNewSpaceObjectsDo:
		[:obj|
		(memoryManager classIndexOf: obj) = classIndex ifTrue:
			[^true]].
	^false
]

{ #category : #'class table' }
SpurGenerationalGC >> expungeDuplicateAndUnmarkedClasses: expungeUnmarked [
	"Bits have been set in the classTableBitmap corresponding to
	 used classes.  Any class in the class table that does not have a
	 bit set has no instances with that class index.  However, becomeForward:
	 can create duplicate entries, and these duplicate entries wont match their
	 identityHash. So expunge duplicates by eliminating unmarked entries that
	 don't occur at their identityHash."
	1 to: objectRepresentation numClassTablePages - 1 do: "Avoid expunging the puns by not scanning the 0th page."
		[:i| | classTablePage |
		classTablePage := objectRepresentation fetchPointer: i ofObject: objectRepresentation hiddenRootsObject.
		 0 to: objectRepresentation classTablePageSize - 1 do:
			[:j| | classOrNil classIndex |
			 classOrNil := objectRepresentation fetchPointer: j ofObject: classTablePage.
			 classIndex := i << objectRepresentation classTableMajorIndexShift + j.
			 self assert: (classOrNil = objectRepresentation nilObject or: [objectRepresentation coInterpreter addressCouldBeClassObj: classOrNil]).
			 "only remove a class if it is at a duplicate entry or it is unmarked and we're expunging unmarked classes."
			 classOrNil = objectRepresentation nilObject
				ifTrue:
					[classIndex < objectRepresentation classTableIndex ifTrue:
						[objectRepresentation classTableIndex: classIndex]]
				ifFalse:
					[((expungeUnmarked and: [(objectRepresentation isMarked: classOrNil) not])
					   or: [(objectRepresentation rawHashBitsOf: classOrNil) ~= classIndex]) ifTrue:
						[objectRepresentation storePointerUnchecked: j
							ofObject: classTablePage
							withValue: objectRepresentation nilObject.
						 "but if it is marked, it should still be in the table at its correct index."
						 self assert: ((expungeUnmarked and: [(objectRepresentation isMarked: classOrNil) not])
									or: [(objectRepresentation classAtIndex: (objectRepresentation rawHashBitsOf: classOrNil)) = classOrNil]).
						 "If the removed class is before the classTableIndex, set the
						  classTableIndex to point to the empty slot so as to reuse it asap."
						 classIndex < objectRepresentation classTableIndex ifTrue:
							[objectRepresentation classTableIndex: classIndex]]]]].
	"classTableIndex must never index the first page, which is reserved for classes known to the VM."
	self assert: objectRepresentation classTableIndex >= (1 << objectRepresentation classTableMajorIndexShift)
]

{ #category : #'heap management' }
SpurGenerationalGC >> fetchPointer: fieldIndex ofFreeChunk: objOop [
	"Different because it does an assertion at simulation time checking its not a forwarder"
	^objectRepresentation longAt: objOop + objectRepresentation baseHeaderSize + (fieldIndex << objectRepresentation shiftForWord)
]

{ #category : #'free space' }
SpurGenerationalGC >> findLargestFreeChunk [
	"Answer, but do not remove, the largest free chunk in the free lists."
	| treeNode childNode |
	treeNode := freeLists at: 0.
	treeNode = 0 ifTrue:
		[^nil].
	[self assertValidFreeObject: treeNode.
	 self assert: (objectRepresentation bytesInObject: treeNode) >= (self numFreeLists * objectRepresentation allocationUnit).
	 childNode := self fetchPointer: self freeChunkLargerIndex ofFreeChunk: treeNode.
	 childNode ~= 0] whileTrue:
		[treeNode := childNode].
	^treeNode
]

{ #category : #'weakness and ephemerality' }
SpurGenerationalGC >> fireAllUnscannedEphemerons [
	self assert: (self noUnscannedEphemerons) not.
	self assert: self allUnscannedEphemeronsAreActive.
	unscannedEphemerons start to: unscannedEphemerons top - objectRepresentation bytesPerOop by: objectRepresentation bytesPerOop do:
		[:p|
		objectRepresentation coInterpreter fireEphemeron: (objectRepresentation longAt: p)]
]

{ #category : #'object enumeration' }
SpurGenerationalGC >> firstAccessibleObject [
	<inline: false>
	self assert: nilObj = oldSpaceStart.
	"flush newSpace to settle the enumeration."
	self flushNewSpace.
	^nilObj
]

{ #category : #'free space' }
SpurGenerationalGC >> firstLilliputianChunk [
	^freeLists at: self lilliputianChunkIndex
]

{ #category : #'object enumeration' }
SpurGenerationalGC >> firstObject [
	"Return the first object or free chunk in the heap."

	^objectRepresentation nilObject
]

{ #category : #'gc - scavenging' }
SpurGenerationalGC >> flushEden [
	"Fush everything in eden.  Do so by doing a non-tenuring scavenge."
	self scavengingGCTenuringIf: DontTenure.
	self assert: pastSpaceStart = scavenger pastSpace start.
	self assert: freeStart = scavenger eden start
]

{ #category : #'gc - scavenging' }
SpurGenerationalGC >> flushNewSpace [
	"Fush everything in new space.  Do so by setting the tenure
	 threshold above everything in newSpace, i.e. newSpaceLimit."
	| savedTenuringThreshold |
	savedTenuringThreshold := scavenger getRawTenuringThreshold.
	scavenger setRawTenuringThreshold: newSpaceLimit.
	self scavengingGCTenuringIf: TenureByAge.
	scavenger setRawTenuringThreshold: savedTenuringThreshold.
	self assert: scavenger rememberedSetSize = 0.
	self assert: pastSpaceStart = scavenger pastSpace start.
	self assert: freeStart = scavenger eden start
]

{ #category : #'gc - scavenging' }
SpurGenerationalGC >> flushNewSpaceInstancesOf: aClass [
	| classIndex |
	classIndex := memoryManager rawHashBitsOf: aClass.
	classIndex = 0 ifTrue: "no instances; nothing to do"
		[^self].
	scavenger tenuringClassIndex: classIndex.
	self scavengingGCTenuringIf: TenureByClass.
	self assert: (self existInstancesInNewSpaceOf: aClass) not
]

{ #category : #compaction }
SpurGenerationalGC >> followForwardedObjStacks [
	"Compaction will move objStack pages as well as ordinary objects.
	 So they need their slots followed."
	self followForwardedInObjStack: markStack atIndex: MarkStackRootIndex.
	self followForwardedInObjStack: weaklingStack atIndex: WeaklingStackRootIndex.
	self followForwardedInObjStack: mournQueue atIndex: MournQueueRootIndex
]

{ #category : #'free space' }
SpurGenerationalGC >> freeChunkLargerIndex [
	"for organizing the tree of large free chunks."
	^4
]

{ #category : #'free space' }
SpurGenerationalGC >> freeChunkNextIndex [
	"for linking objecs on each free list, or, during pigCompact, doubly-
	 linking the free objects in address order using the xor link hack."
	^0
]

{ #category : #'free space' }
SpurGenerationalGC >> freeChunkParentIndex [
	"for organizing the tree of large free chunks."
	^2
]

{ #category : #'free space' }
SpurGenerationalGC >> freeChunkPrevIndex [
	"For linking objecs on each free list, doubly-linking the free objects.
	 Free chunks of size 1 do not have a prev index."
	^1
]

{ #category : #'free space' }
SpurGenerationalGC >> freeChunkSmallerIndex [
	"for organizing the tree of large free chunks."
	^3
]

{ #category : #'free space' }
SpurGenerationalGC >> freeChunkWithBytes: bytes at: address [
	<inline: false>
	| freeChunk |
	self assert: (self isInOldSpace: address).
	self assert: (objectRepresentation segmentManager segmentContainingObj: address) = (objectRepresentation segmentManager segmentContainingObj: address + bytes).
	freeChunk := objectRepresentation  initFreeChunkWithBytes: bytes at: address.
	self addToFreeList: freeChunk bytes: bytes.
	self assert: freeChunk = (objectRepresentation objectStartingAt: address).
	^freeChunk
]

{ #category : #'free space' }
SpurGenerationalGC >> freeListHeadsEmpty [
	0 to: self numFreeLists - 1 do:
		[:i| (freeLists at: i) ~= 0 ifTrue: [^false]].
	^true
]

{ #category : #accessing }
SpurGenerationalGC >> freeLists [
	<doNotGenerate>
	^ freeLists
]

{ #category : #'free space' }
SpurGenerationalGC >> freeListsObj [
	self assert: (objectRepresentation firstIndexableField: (self oldSpaceObjectAfter: objectRepresentation trueObject)) = freeLists.
	^self oldSpaceObjectAfter: objectRepresentation trueObject
]

{ #category : #'free space' }
SpurGenerationalGC >> freeListsObject [
	^self objectAfter: trueObj
]

{ #category : #'free space' }
SpurGenerationalGC >> freeObject: objOop [
	"Free an object in oldSpace.  Coalesce if possible to reduce fragmentation."
	<api>
	<inline: false>
	| bytes start next |
	self assert: (self isInOldSpace: objOop).
	(objectRepresentation isRemembered: objOop) ifTrue:
		[scavenger forgetObject: objOop].
	bytes := objectRepresentation bytesInObject: objOop.
	start := objectRepresentation startOfObject: objOop.
	next := objectRepresentation objectStartingAt: start + bytes.
	(self isFreeObject: next) ifTrue:
		[self detachFreeObject: next.
		 bytes := bytes + (self bytesInObject: next)].
	totalFreeOldSpace := totalFreeOldSpace + bytes.
	^self freeChunkWithBytes: bytes at: start
]

{ #category : #snapshot }
SpurGenerationalGC >> freeOldSpaceStart [
	^freeOldSpaceStart
]

{ #category : #'free space' }
SpurGenerationalGC >> freeSize [
	^totalFreeOldSpace
]

{ #category : #'debug support' }
SpurGenerationalGC >> freeSpaceCharacterisation [
	<doNotGenerate>
	| n s |
	n := 0.
	s := Bag new.
	self allFreeObjectsDo:
		[:f| n := n + 1. s add: (self bytesInObject: f)].
	^{ n. s sortedCounts. s sortedElements }
]

{ #category : #accessing }
SpurGenerationalGC >> freeStart [
	"This is a horrible hack and only works because C macros are generated after Interpreter variables."
	<cmacro: '() GIV(freeStart)'>
	^freeStart
]

{ #category : #accessing }
SpurGenerationalGC >> freeStart: anInteger [ 
	freeStart := anInteger
]

{ #category : #'free space' }
SpurGenerationalGC >> freeTreeNodesDo: aBlock [
	"Enumerate all nodes in the free tree (in order, smaller to larger),
	 but *not* including the next nodes of the same size off each tree node.
	 This is an iterative version so that the block argument can be
	 inlined by Slang. The trick to an iterative binary tree application is
	 to apply the function on the way back up when returning from a
	 particular direction, in this case up from the larger child.

	 N.B For the convenience of rebuildFreeTreeFromSortedFreeChunks
	 aBlock *MUST* answer the freeTreeNode it was invoked with, or
	 its replacement if it was replaced by aBlock."
	<inline: true>
	| treeNode cameFrom |
	treeNode := freeLists at: 0.
	treeNode = 0 ifTrue:
		[^self].
	cameFrom := -1.
	[| smallChild largeChild |
	 self assert: (objectRepresentation bytesInObject: treeNode) >= (self numFreeLists * objectRepresentation allocationUnit).
	 smallChild := self fetchPointer: self freeChunkSmallerIndex ofFreeChunk: treeNode.
	 largeChild := self fetchPointer: self freeChunkLargerIndex ofFreeChunk: treeNode.
	 self assert: (smallChild = 0 or: [treeNode = (self fetchPointer: self freeChunkParentIndex ofFreeChunk: smallChild)]).
	 self assert: (largeChild = 0 or: [treeNode = (self fetchPointer: self freeChunkParentIndex ofFreeChunk: largeChild)]).
	 "apply if the node has no children, or it has no large children and we're
	  returning from the small child, or we're returning from the large child."
	 ((smallChild = 0 and: [largeChild = 0])
	  or: [largeChild = 0
			ifTrue: [cameFrom = smallChild]
			ifFalse: [cameFrom = largeChild]])
		ifTrue:
			[treeNode := aBlock value: treeNode.
			 "and since we've applied we must move on up"
			 cameFrom := treeNode.
			 treeNode := self fetchPointer: self freeChunkParentIndex ofFreeChunk: treeNode]
		ifFalse:
			[(smallChild ~= 0 and: [cameFrom ~= smallChild])
				ifTrue:
					[treeNode := smallChild]
				ifFalse:
					[self assert: largeChild ~= 0.
					 treeNode := largeChild].
			 cameFrom := -1].
	 treeNode ~= 0] whileTrue
]

{ #category : #'gc - global' }
SpurGenerationalGC >> freeUnscannedEphemerons [
	"Free all the memory allocated to keep the unscanned ephemerons"
	
	self free: unscannedEphemerons start
]

{ #category : #'gc - global' }
SpurGenerationalGC >> fullGC [
	"Perform a full eager compacting GC.  Answer the size of the largest free chunk."
	<returnTypeC: #usqLong>
	<inline: #never> "for profiling"
	needGCFlag := false.
	gcStartUsecs := objectRepresentation coInterpreter ioUTCMicrosecondsNow.
	statMarkCount := 0.
	objectRepresentation coInterpreter preGCAction: GCModeFull.
	objectRepresentation globalGarbageCollect.
	objectRepresentation coInterpreter postGCAction: GCModeFull.
	statGCEndUsecs := objectRepresentation coInterpreter ioUTCMicrosecondsNow.
	self updateFullGCStats.
	^(freeLists at: 0) ~= 0
		ifTrue: [objectRepresentation bytesInObject: self findLargestFreeChunk]
		ifFalse: [0]
]

{ #category : #'gc - global' }
SpurGenerationalGC >> globalGarbageCollect [
	<inline: true> "inline into fullGC"
	self assert: self validObjStacks.
	self assert: (objectRepresentation isEmptyObjStack: markStack).
	self assert: (objectRepresentation isEmptyObjStack: weaklingStack).

	"Mark objects /before/ scavenging, to empty the rememberedTable of unmarked roots."
	self markObjects: true.
	gcMarkEndUsecs := objectRepresentation coInterpreter ioUTCMicrosecondsNow.
	
	scavenger forgetUnmarkedRememberedObjects.
	self doScavenge: MarkOnTenure.

	"Mid-way the leak check must be more lenient.  Unmarked classes will have been
	 expunged from the table, but unmarked instances will not yet have been reclaimed."
	self runLeakCheckerFor: GCModeFull
		excludeUnmarkedObjs: true
		classIndicesShouldBeValid: true.
	compactionStartUsecs := objectRepresentation coInterpreter ioUTCMicrosecondsNow.
	objectRepresentation segmentManager prepareForGlobalSweep. "for notePinned:"
	compactor compact.
	self attemptToShrink.
	self setHeapSizeAtPreviousGC.

	self assert: self validObjStacks.
	self assert: (objectRepresentation isEmptyObjStack: markStack).
	self assert: (objectRepresentation isEmptyObjStack: weaklingStack).
	self assert: self allObjectsUnmarked.
	self runLeakCheckerFor: GCModeFull
]

{ #category : #accessing }
SpurGenerationalGC >> growHeadroom [
	^growHeadroom
]

{ #category : #accessing }
SpurGenerationalGC >> growHeadroom: aValue [
	^growHeadroom := aValue
]

{ #category : #'growing/shrinking memory' }
SpurGenerationalGC >> growOldSpaceByAtLeast: minAmmount [
	"Attempt to grow memory by at least minAmmount.
	 Answer the size of the new segment, or nil if the attempt failed."
	| ammount headroom total start interval |
	<var: #segInfo type: #'SpurSegmentInfo *'>
	"statGrowMemory counts attempts, not successes."
	statGrowMemory := statGrowMemory + 1."we need to include overhead for a new object header plus the segment bridge."
	ammount := minAmmount + (self baseHeaderSize * 2 + self bridgeSize).
	"round up to the nearest power of two."
	ammount := 1 << (ammount - 1) highBit.
	"and grow by at least growHeadroom."
	ammount := ammount max: growHeadroom.

	"Now apply the maxOldSpaceSize limit, if one is in effect."
	maxOldSpaceSize > 0 ifTrue:
		[total := segmentManager totalBytesInSegments.
		 total >= maxOldSpaceSize ifTrue:
			[^nil].
		 headroom := maxOldSpaceSize - total.
		 headroom < ammount ifTrue:
			[headroom < (minAmmount + (self baseHeaderSize * 2 + self bridgeSize)) ifTrue:
				[^nil].
			 ammount := headroom]].
		 
	start := coInterpreter ioUTCMicrosecondsNow.
	^(segmentManager addSegmentOfSize: ammount) ifNotNil:
		[:segInfo|
		 self assimilateNewSegment: segInfo.
		 "and add the new free chunk to the free list; done here
		  instead of in assimilateNewSegment: for the assert"
		 self addFreeChunkWithBytes: segInfo segSize - self bridgeSize at: segInfo segStart.
		 self assert: (self addressAfter: (self objectStartingAt: segInfo segStart))
					= (segInfo segLimit - self bridgeSize).
		 self checkFreeSpace: GCModeFreeSpace.
		 segmentManager checkSegments.
		 interval := coInterpreter ioUTCMicrosecondsNow - start.
		 interval > statMaxAllocSegmentTime ifTrue: [statMaxAllocSegmentTime := interval].
		 segInfo segSize]
]

{ #category : #'growing/shrinking memory' }
SpurGenerationalGC >> growToAccomodateContainerWithNumSlots: numSlots [
	"Grow memory to accomodate a container (an Array) with numSlots.
	 Grow by at least the growHeadroom.  Supports allInstancesOf: and allObjects."
	| delta |
	delta := self baseHeaderSize * 2 + (numSlots * self bytesPerOop).
	self growOldSpaceByAtLeast: (growHeadroom max: delta)
]

{ #category : #'free space' }
SpurGenerationalGC >> inFreeTreeReplace: treeNode with: newNode [
	"Part of reorderReversedTreeList:.  Switch treeNode with newNode in
	 the tree, but do nothing to the list linked through freeChunkNextIndex."
	| relative |
	self storePointer: self freeChunkPrevIndex ofFreeChunk: newNode withValue: 0.
	"copy parent, smaller, larger"
	self freeChunkParentIndex to: self freeChunkLargerIndex do:
		[:i|
		relative := self fetchPointer: i ofFreeChunk: treeNode.
		i = self freeChunkParentIndex
			ifTrue:
				[relative = 0
					ifTrue: "update root to point to newNode"
						[self assert: (freeLists at: 0) = treeNode.
						 freeLists at: 0 put: newNode]
					ifFalse: "replace link from parent to treeNode with link to newNode."
						[self storePointer: (treeNode = (self fetchPointer: self freeChunkSmallerIndex ofFreeChunk: relative)
												ifTrue: [self freeChunkSmallerIndex]
												ifFalse: [self freeChunkLargerIndex])
							ofFreeChunk: relative
							withValue: newNode]]
			ifFalse:
				[relative ~= 0 ifTrue:
					[self assert: (self fetchPointer: self freeChunkParentIndex ofFreeChunk: relative) = treeNode.
					 self storePointer: self freeChunkParentIndex ofFreeChunk: relative withValue: newNode]].
		self storePointer: i ofFreeChunk: newNode withValue: relative.
		self storePointer: i ofFreeChunk: treeNode withValue: 0]
]

{ #category : #'debug support' }
SpurGenerationalGC >> inLineRunLeakCheckerFor: gcModes excludeUnmarkedObjs: excludeUnmarkedObjs classIndicesShouldBeValid: classIndicesShouldBeValid [
	<inline: true>
	(gcModes anyMask: checkForLeaks) ifTrue:
		[(gcModes anyMask: GCModeFull)
			ifTrue: [coInterpreter reverseDisplayFrom: 0 to: 7]
			ifFalse: [coInterpreter reverseDisplayFrom: 8 to: 15].
		 memoryManager clearLeakMapAndMapAccessibleObjects.
		 self asserta: (self checkHeapIntegrity: excludeUnmarkedObjs classIndicesShouldBeValid: classIndicesShouldBeValid).
		 self asserta: coInterpreter checkInterpreterIntegrity = 0.
		 self asserta: coInterpreter checkStackIntegrity.
		 self asserta: (coInterpreter checkCodeIntegrity: gcModes)]
]

{ #category : #'free space' }
SpurGenerationalGC >> increaseFreeOldSpaceBy: bytes [ 
	totalFreeOldSpace := totalFreeOldSpace + bytes

]

{ #category : #allocation }
SpurGenerationalGC >> initSpaceForAllocationCheck: aNewSpace limit: limit [
	<var: 'aNewSpace' type: #'SpurNewSpaceSpace *'>
	<var: 'limit' type: #usqInt>
	memory ifNotNil:
		[self checkAllocFiller ifTrue:
			[aNewSpace start
				to: limit - 1
				by: self wordSize
				do: [:p| self longAt: p put: p]]]
]

{ #category : #snapshot }
SpurGenerationalGC >> initialHeadroom: extraVmMemory givenFreeOldSpaceInImage: freeOldSpaceInImage [
	"Answer how much headroom to allocate, if any, on loading the image.
	 If the image already conatins lots of free space, we should not allocate lots more."
	<inline: true>
	| headroom |
	headroom := extraVmMemory = 0
					ifTrue: [growHeadroom ifNil: [16*1024*1024]]
					ifFalse: [extraVmMemory].
	freeOldSpaceInImage >= headroom ifTrue:
		[^0].
	freeOldSpaceInImage >= (headroom * 7 // 8) ifTrue:
		[^headroom // 8].
	freeOldSpaceInImage >= (headroom * 3 // 4) ifTrue:
		[^headroom // 4].
	freeOldSpaceInImage >= (headroom * 5 // 8) ifTrue:
		[^headroom * 3 // 8].
	freeOldSpaceInImage >= (headroom // 2) ifTrue:
		[^headroom // 2].
	^headroom
]

{ #category : #initialization }
SpurGenerationalGC >> initialize [

	super initialize.
	totalFreeOldSpace := 0.
	checkForLeaks := 0.
	remapBufferCount := 0.
	statAllocatedBytes := 0.
	statScavenges := statShrinkMemory := 0.
	statScavengeGCUsecs := 0.
	needGCFlag := false.
	extraRootCount := 0.
	
	statFullGCs := 0.
	statFullGCUsecs := 0.
	statCompactionUsecs := 0.
	statMarkUsecs := 0.
	gcSweepEndUsecs := 0.
	
	"We can initialize things that are allocated but are lazily initialized."
	unscannedEphemerons := SpurContiguousObjStack new.
	unscannedEphemeronsQueueInitialSize := 10000. "10k by default"
	
	marking := false.
	
	scavenger := SpurGenerationScavenger simulatorClass new.
	compactor := self class compactorClass simulatorClass new.
]

{ #category : #bootstrap }
SpurGenerationalGC >> initializeFreeList [

	| freeListOop |
	freeListOop := self objectMemory
		allocateSlots: self numFreeLists
		format: objectRepresentation wordIndexableFormat
		classIndex: objectRepresentation wordSizeClassIndexPun.
	0 to: self numFreeLists - 1 do: [ :i |
		objectRepresentation
			storePointerUnchecked: i
			ofObject: freeListOop
			withValue: 0].
	self initializeFreeSpacePostLoad: freeListOop.
	^ freeListOop
]

{ #category : #bootstrap }
SpurGenerationalGC >> initializeFreeListInOldSpace: inOldSpace [

	| freeListOop |
	
	freeListOop := inOldSpace ifTrue: [
		self objectMemory
			allocateSlotsInOldSpace: self numFreeLists
			format: objectRepresentation wordIndexableFormat
			classIndex: objectRepresentation wordSizeClassIndexPun.
	] ifFalse: [ 
		self
			allocateSlots: self numFreeLists
			format: objectRepresentation wordIndexableFormat
			classIndex: objectRepresentation wordSizeClassIndexPun.
	].
	0 to: self numFreeLists - 1 do: [ :i |
		objectRepresentation
			storePointerUnchecked: i
			ofObject: freeListOop
			withValue: 0].
	^ freeListOop
]

{ #category : #snapshot }
SpurGenerationalGC >> initializeFreeSpacePostLoad: freeListObj [
	"Reinitialize the free list info.  The freeLists object needs to be swizzled
	 because its neither a free, nor a pointer object.  Free objects have already
	 been swizzled in adjustAllOopsBy:"
	
	self assert: (objectRepresentation numSlotsOf: freeListObj) = self numFreeLists.
	self assert: (objectRepresentation formatOf: freeListObj) = objectRepresentation wordIndexableFormat.
	freeLists := objectRepresentation firstIndexableField: freeListObj.
	freeListsMask := 0.
	0 to: self numFreeLists - 1 do:
		[:i|
		(freeLists at: i) ~= 0 ifTrue:
			[freeListsMask := freeListsMask bitOr: (1 << i).
			 freeLists at: i put: (objectRepresentation segmentManager swizzleObj: (freeLists at: i))]]
]

{ #category : #'gc - global' }
SpurGenerationalGC >> initializeMarkStack [
	objectRepresentation ensureRoomOnObjStackAt: MarkStackRootIndex
]

{ #category : #'gc - scavenging' }
SpurGenerationalGC >> initializeNewSpaceVariables [
	<inline: #never>
	
	freeStart := scavenger eden start.
	pastSpaceStart := scavenger pastSpace start.
	scavengeThreshold := scavenger eden limit
							- (scavenger edenBytes // 64)
							- coInterpreter interpreterAllocationReserveBytes.
	newSpaceStart := scavenger pastSpace start min: scavenger futureSpace start.
	self assert: newSpaceStart < scavenger eden start.
	self initSpaceForAllocationCheck: (self addressOf: scavenger eden) limit: scavengeThreshold
]

{ #category : #'free space' }
SpurGenerationalGC >> initializeOldSpaceFirstFree: startOfFreeOldSpace [
	<var: 'startOfFreeOldSpace' type: #usqInt>
	| limit freeOldStart freeChunk |
	<var: 'limit' type: #usqInt>
	<var: 'freeOldStart' type: #usqInt>
	limit := endOfMemory - self bridgeSize.
	limit > startOfFreeOldSpace ifTrue:
		[totalFreeOldSpace := totalFreeOldSpace + (limit - startOfFreeOldSpace).
		 freeOldStart := startOfFreeOldSpace.
		 self wordSize > 4 ifTrue:
			[[limit - freeOldStart >= (1 << 32)] whileTrue:
				[freeChunk := self freeChunkWithBytes: (1 << 32) at: freeOldStart.
				 freeOldStart := freeOldStart + (1 << 32).
				 self assert: freeOldStart = (self addressAfter: freeChunk)]].
		freeOldStart < limit ifTrue:
			[freeChunk := self freeChunkWithBytes: limit - freeOldStart at: freeOldStart.
			 self assert: (objectRepresentation addressAfter: freeChunk) = limit]].
	endOfMemory := endOfMemory - self bridgeSize.
	freeOldSpaceStart := endOfMemory.
	self checkFreeSpace: GCModeFreeSpace
]

{ #category : #'spur bootstrap' }
SpurGenerationalGC >> initializePostBootstrap [
	"The heap has just been bootstrapped into a modified newSpace occupying all of memory
	 above newSpace (and the codeZone). Put things back to some kind of normalcy."
	freeOldSpaceStart := freeStart.
	freeStart := scavenger eden start.
	pastSpaceStart := scavenger pastSpace start.
	scavengeThreshold := scavenger eden limit - (scavenger edenBytes // 64)
]

{ #category : #'gc - global' }
SpurGenerationalGC >> initializeUnscannedEphemerons [
	"Initialize unscannedEphemerons to use the largest free chunk
	 or unused eden space, which ever is the larger."
	
	| allocation |
	"Allocate initially space for 10K ephemerons"
	allocation := (self calloc: (self sizeof: #'void *') _: unscannedEphemeronsQueueInitialSize).
	allocation ifNil: [ self error: 'Cannot allocate space for unscanned ephemerons' ].
	unscannedEphemerons
				start: allocation asInteger;
				limit: allocation asInteger + ((self sizeof: #'void *') * unscannedEphemeronsQueueInitialSize).
	unscannedEphemerons top: unscannedEphemerons start
]

{ #category : #'gc - global' }
SpurGenerationalGC >> initializeWeaklingStack [
	objectRepresentation ensureRoomOnObjStackAt: WeaklingStackRootIndex
]

{ #category : #'object enumeration' }
SpurGenerationalGC >> instanceAfter: objOop [
	| actualObj classIndex |
	actualObj := objOop.
	classIndex := self classIndexOf: objOop.

	(self isInEden: objOop) ifTrue:
		[[actualObj := self objectAfter: actualObj limit: freeStart.
		  self oop: actualObj isLessThan: freeStart] whileTrue:
			[classIndex = (self classIndexOf: actualObj) ifTrue:
				[^actualObj]].
		 actualObj := (self oop: pastSpaceStart isGreaterThan: scavenger pastSpace start)
						ifTrue: [self objectStartingAt: scavenger pastSpace start]
						ifFalse: [nilObj]].

	(self isInPastSpace: actualObj) ifTrue:
		[[actualObj := self objectAfter: actualObj limit: pastSpaceStart.
		  self oop: actualObj isLessThan: pastSpaceStart] whileTrue:
			[classIndex = (self classIndexOf: actualObj) ifTrue:
				[^actualObj]].
		 actualObj := nilObj].

	[actualObj := self objectAfter: actualObj limit: endOfMemory.
	 self oop:actualObj isLessThan: endOfMemory] whileTrue:
		[classIndex = (self classIndexOf: actualObj) ifTrue:
			[^actualObj]].
	^nil
]

{ #category : #'object testing' }
SpurGenerationalGC >> isFreeObject: objOop [
	^(objectRepresentation classIndexOf: objOop) = self isFreeObjectClassIndexPun
]

{ #category : #'class table puns' }
SpurGenerationalGC >> isFreeObjectClassIndexPun [
	<cmacro>
	^0
]

{ #category : #'object testing' }
SpurGenerationalGC >> isFreeOop: oop [
	^(objectRepresentation isNonImmediate: oop) and: [self isFreeObject: oop]
]

{ #category : #'object testing' }
SpurGenerationalGC >> isInEden: objOop [
	^self
		oop: objOop
		isGreaterThanOrEqualTo: scavenger eden start
		andLessThan: freeStart
]

{ #category : #'object testing' }
SpurGenerationalGC >> isInFutureSpace: address [
	^self
		oop: address
		isGreaterThanOrEqualTo: scavenger futureSpace start
		andLessThan: scavenger futureSurvivorStart
]

{ #category : #'plugin support' }
SpurGenerationalGC >> isInMemory: address [ 
	"Answer if the given address is in ST object memory."
	(self isInNewSpace: address) ifTrue:
		[^(self isInEden: address)
			or: [(self isInPastSpace: address)
			or: [self scavengeInProgress and: [self isInFutureSpace: address]]]].
	^segmentManager isInSegments: address
]

{ #category : #'object testing' }
SpurGenerationalGC >> isInNewSpace: objOop [
	^(self oop: objOop isLessThan: newSpaceLimit)
	  and: [self oop: objOop isGreaterThanOrEqualTo: newSpaceStart]
]

{ #category : #'object testing' }
SpurGenerationalGC >> isInOldSpace: address [
	<api>
	^self
		oop: address
		isGreaterThanOrEqualTo: oldSpaceStart
		andLessThan: endOfMemory
]

{ #category : #'object testing' }
SpurGenerationalGC >> isInPastSpace: address [
	^self
		oop: address
		isGreaterThanOrEqualTo: scavenger pastSpace start
		andLessThan: pastSpaceStart
]

{ #category : #'free space' }
SpurGenerationalGC >> isLargeFreeObject: objOop [
	^(objectRepresentation bytesInObject: objOop) >= (self numFreeLists * objectRepresentation allocationUnit)
]

{ #category : #'object testing' }
SpurGenerationalGC >> isOldObject: objOop [
	<api>
	"Answer if obj is old. Require that obj is non-immediate."
	self assert: (objectRepresentation isNonImmediate: objOop).
	^self oop: objOop isGreaterThanOrEqualTo: oldSpaceStart
]

{ #category : #'gc - scavenging' }
SpurGenerationalGC >> isScavengeSurvivor: oop [
	<doNotGenerate>
	^scavenger isScavengeSurvivor: oop
]

{ #category : #'object testing' }
SpurGenerationalGC >> isYoung: oop [
	<api>
	"Answer if oop is young."
	^(objectRepresentation isNonImmediate: oop)
	 and: [self oop: oop isLessThan: newSpaceLimit]
]

{ #category : #'object testing' }
SpurGenerationalGC >> isYoungObject: objOop [
	<api>
	"Answer if obj is young. Require that obj is non-immediate."
	self assert: (objectRepresentation isNonImmediate: objOop).
	^self oop: objOop isLessThan: newSpaceLimit
]

{ #category : #'free space' }
SpurGenerationalGC >> lowSpaceThreshold: threshold [
	lowSpaceThreshold := threshold.
	"N.B. The threshold > 0 guard eliminates a warning when
		self lowSpaceThreshold: 0
	 is inlined into setSignalLowSpaceFlagAndSaveProcess"
	(threshold > 0
	 and: [totalFreeOldSpace < threshold]) ifTrue:
		[self growOldSpaceByAtLeast: threshold - totalFreeOldSpace].
	self assert: totalFreeOldSpace >= lowSpaceThreshold
]

{ #category : #'gc - global' }
SpurGenerationalGC >> mapExtraRoots [
	(objectRepresentation shouldRemapObj: objectRepresentation specialObjectsOop) ifTrue:
		[objectRepresentation specialObjectsOop: (objectRepresentation remapObj: objectRepresentation specialObjectsOop)].
	self assert: remapBufferCount = 0.
	"1 to: remapBufferCount do:
		[:i | | oop |
		oop := remapBufferCount at: i.
		((self isImmediate: oop) or: [self isFreeObject: oop]) ifFalse:
			[(self shouldRemapObj: oop) ifTrue:
				[remapBuffer at: i put: (self remapObj: oop)]]]."
	1 to: extraRootCount do:
		[:i | | oop |
		oop := (extraRoots at: i) at: 0.
		((objectRepresentation isImmediate: oop) or: [self isFreeObject: oop]) ifFalse:
			[(objectRepresentation shouldRemapObj: oop) ifTrue:
				[(extraRoots at: i) at: 0 put: (objectRepresentation remapObj: oop)]]]
]

{ #category : #'weakness and ephemerality' }
SpurGenerationalGC >> mapMournQueue [
	<inline: #never>
	objectRepresentation objStack: mournQueue do:
		[:i :page| | mourner |
		mourner := objectRepresentation fetchPointer: i ofObject: page.
		(objectRepresentation isNonImmediate: mourner) ifTrue: "someone could try and become weaklings into immediates..."
			[(objectRepresentation isForwarded: mourner) ifTrue:
				[mourner := objectRepresentation followForwarded: mourner].
			 (scavenger isScavengeSurvivor: mourner) ifFalse:
				[mourner := scavenger copyAndForwardMourner: mourner].
			 "we could check for change but writes are cheasp with write buffers..."
			 objectRepresentation storePointerUnchecked: i ofObject: page withValue: mourner]]
]

{ #category : #'gc - global' }
SpurGenerationalGC >> markAccessibleObjectsAndFireEphemerons [
	self assert: marking.
	self assert: objectRepresentation validClassTableRootPages.
	self assert: objectRepresentation segmentManager allBridgesMarked.
	self cCode: [] "for debugging markAndTrace: set (MarkStackRecord := OrderedCollection new)"
		inSmalltalk: [MarkStackRecord ifNotNil: [MarkStackRecord resetTo: 1]].

	"This must come first to enable stack page reclamation.  It clears
	  the trace flags on stack pages and so must precede any marking.
	  Otherwise it will clear the trace flags of reached pages."
	objectRepresentation coInterpreter initStackPageGC.
	self markAndTraceHiddenRoots.
	self markAndTraceExtraRoots.
	self assert: objectRepresentation validClassTableRootPages.
	objectRepresentation coInterpreter markAndTraceInterpreterOops: true.
	self assert: self validObjStacks.
	self markWeaklingsAndMarkAndFireEphemerons.
	self assert: self validObjStacks
]

{ #category : #'weakness and ephemerality' }
SpurGenerationalGC >> markAllUnscannedEphemerons [
	"After firing the unscanned ephemerons we must scan-mark them.
	 The wrinkle is that doing so may add more ephemerons to the set.
	 So we remove the first element, by overwriting it with the last element,
	 and decrementing the top, and then markAndTrace its contents."
	self assert: (self noUnscannedEphemerons) not.
	self assert: self allUnscannedEphemeronsAreActive.
	[unscannedEphemerons top > unscannedEphemerons start] whileTrue:
		[| ephemeron key lastptr |
		 ephemeron := objectRepresentation longAt: unscannedEphemerons start.
		 lastptr := unscannedEphemerons top - objectRepresentation bytesPerOop.
		 lastptr > unscannedEphemerons start ifTrue:
			[objectRepresentation longAt: unscannedEphemerons start put: (objectRepresentation longAt: lastptr)].
		 unscannedEphemerons top: lastptr.
		 key := objectRepresentation followedKeyOfMaybeFiredEphemeron: ephemeron.
		 objectRepresentation setIsMarkedOf: ephemeron to: false. "to get it to be fully scanned in markAndTrace:"
		 self
			markAndTrace: key;
			markAndTrace: ephemeron]
]

{ #category : #'gc - global' }
SpurGenerationalGC >> markAndShouldScan: objOop [
	"Helper for markAndTrace:.
	 Mark the argument, and answer if its fields should be scanned now.
	 Immediate objects don't need to be marked.
	 Already marked objects have already been processed.
	 Pure bits objects don't need scanning, although their class does.
	 Weak objects should be pushed on the weakling stack.
	 Anything else need scanning."
	| format |
	<inline: true>
	(objectRepresentation isImmediate: objOop) ifTrue:
		[^false].
	"if markAndTrace: is to follow and eliminate forwarding pointers
	 in its scan it cannot be handed an r-value which is forwarded."
	self assert: (objectRepresentation isForwarded: objOop) not.
	(objectRepresentation isMarked: objOop) ifTrue:
		[^false].
	objectRepresentation setIsMarkedOf: objOop to: true.
	format := objectRepresentation formatOf: objOop.
	(objectRepresentation isPureBitsFormat: format) ifTrue: "avoid pushing non-pointer objects on the markStack."
		["Avoid tracing classes of non-objects on the heap, e.g. IRC caches, Sista counters."
		 (objectRepresentation classIndexOf: objOop) > objectRepresentation lastClassIndexPun ifTrue:
			[self markAndTraceClassOf: objOop].
		 ^false].
	format = objectRepresentation weakArrayFormat ifTrue: "push weaklings on the weakling stack to scan later"
		[objectRepresentation push: objOop onObjStack: weaklingStack.
		 ^false].
	(format = objectRepresentation ephemeronFormat
	 and: [self activeAndDeferredScan: objOop]) ifTrue:
		[^false].
	^true
]

{ #category : #'gc - global' }
SpurGenerationalGC >> markAndTrace: objOop [
	"Mark the argument, and all objects reachable from it, and any remaining objects
	 on the mark stack. Follow forwarding pointers in the scan."
	<api>
	<inline: #never>
	"if markAndTrace: is to follow and eliminate forwarding pointers
	 in its scan it cannot be handed an r-value which is forwarded.
	 The assert for this is in markAndShouldScan:"
	(self markAndShouldScan: objOop) ifFalse:
		[^self].

	"Now scan the object, and any remaining objects on the mark stack."
	self markLoopFrom: objOop
]

{ #category : #'gc - global' }
SpurGenerationalGC >> markAndTraceClassOf: objOop [
	"Ensure the class of the argument is marked, pushing it on the markStack if not already marked.
	 And for one-way become, which can create duplicate entries in the class table, make sure
	 objOop's classIndex refers to the classObj's actual classIndex.
	 Note that this is recursive, but the metaclass chain should terminate quickly."
	<inline: false>
	| classIndex classObj realClassIndex |
	classIndex := objectRepresentation classIndexOf: objOop.
	classObj := objectRepresentation classOrNilAtIndex: classIndex.
	self assert: (objectRepresentation coInterpreter objCouldBeClassObj: classObj).
	realClassIndex := objectRepresentation rawHashBitsOf: classObj.
	(classIndex ~= realClassIndex
	 and: [classIndex > objectRepresentation lastClassIndexPun]) ifTrue:
		[objectRepresentation setClassIndexOf: objOop to: realClassIndex].
	(objectRepresentation isMarked: classObj) ifFalse:
		[objectRepresentation setIsMarkedOf: classObj to: true.
		 self markAndTraceClassOf: classObj.
		 objectRepresentation push: classObj onObjStack: markStack]
]

{ #category : #'gc - global' }
SpurGenerationalGC >> markAndTraceExtraRoots [
	| oop |
	self assert: remapBufferCount = 0.
	"1 to: remapBufferCount do:
		[:i|
		 oop := remapBuffer at: i.
		 ((self isImmediate: oop) or: [self isFreeObject: oop]) ifFalse:
			[self markAndTrace: oop]]."
	1 to: extraRootCount do:
		[:i|
		oop := (extraRoots at: i) at: 0.
		((self isImmediate: oop) or: [self isFreeObject: oop]) ifFalse:
			[self markAndTrace: oop]]
]

{ #category : #'gc - global' }
SpurGenerationalGC >> markAndTraceHiddenRoots [
	"The hidden roots hold both the class table pages and the obj stacks,
	 and hence need special treatment.  The obj stacks must be marked
	 specially; their pages must be marked, but only the contents of the
	 mournQueue should be marked.

	 If a class table page is weak we can mark and trace the hiddenRoots,
	 which will not trace through class table pages because they are weak.
	 But if class table pages are strong, we must mark the pages and *not*
	 trace them so that only classes reachable from the true roots will be
	 marked, and unreachable classes will be left unmarked."

	objectRepresentation markAndTraceObjStack: markStack andContents: false.
	objectRepresentation markAndTraceObjStack: weaklingStack andContents: false.
	objectRepresentation markAndTraceObjStack: mournQueue andContents: true.

	objectRepresentation setIsMarkedOf: self rememberedSetObj to: true.
	objectRepresentation setIsMarkedOf: self freeListsObj to: true.

	(objectRepresentation isWeakNonImm: objectRepresentation classTableFirstPage) ifTrue:
		[^self markAndTrace: objectRepresentation hiddenRootsObject].

	objectRepresentation setIsMarkedOf: objectRepresentation hiddenRootsObject to: true.
	self markAndTrace: objectRepresentation classTableFirstPage.
	1 to: objectRepresentation numClassTablePages - 1 do:
		[:i| objectRepresentation setIsMarkedOf: (objectRepresentation fetchPointer: i ofObject: objectRepresentation hiddenRootsObject)
				to: true]
]

{ #category : #'weakness and ephemerality' }
SpurGenerationalGC >> markAndTraceWeaklingsFrom: startIndex [
	"Mark weaklings on the weaklingStack, ignoring startIndex
	 number of elements on the bottom of the stack.  Answer
	 the size of the stack *before* the enumeration began."
	^objectRepresentation  objStack: weaklingStack from: startIndex do:
		[:weakling|
		 self deny: (self isForwarded: weakling).
		 self markAndTraceClassOf: weakling.
		"N.B. generateToByDoLimitExpression:negative:on: guards against (unsigned)0 - 1 going +ve"
		 0 to: (self numStrongSlotsOfWeakling: weakling) - 1 do:
			[:i| | field |
			field := self followOopField: i ofObject: weakling.
			((self isImmediate: field) or: [self isMarked: field]) ifFalse:
				[self markAndTrace: field]]]
]

{ #category : #'image segment in/out' }
SpurGenerationalGC >> markAsCopiedIntoSegment: anObjectInTheHeap [
	"This is part of storeImageSegmentInto:outPointers:roots:."
	<inline: true>
	self setIsMarkedOf: anObjectInTheHeap to: true
]

{ #category : #'weakness and ephemerality' }
SpurGenerationalGC >> markInactiveEphemerons [
	"Go through the unscanned ephemerons, marking the inactive ones, and
	 removing them from the unscanned ephemerons. Answer if any inactive
	 ones were found. We cannot fire the ephemerons until all are found to
	 be active since scan-marking an inactive ephemeron later in the set may
	 render a previously-observed active ephemeron as inactive."
	| foundInactive ptr |
	foundInactive := false.
	ptr := unscannedEphemerons start.
	[ptr < unscannedEphemerons top] whileTrue:
		[| ephemeron key |
		 key := objectRepresentation followedKeyOfEphemeron: (ephemeron := objectRepresentation longAt: ptr).
		 ((objectRepresentation isImmediate: key) or: [objectRepresentation isMarked: key])
			ifTrue:
				[foundInactive := true.
				 "Now remove the inactive ephemeron from the set, and scan-mark it.
				  Scan-marking it may add more ephemerons to the set."
				 unscannedEphemerons top: unscannedEphemerons top - objectRepresentation bytesPerOop.
				 unscannedEphemerons top > ptr ifTrue:
					[objectRepresentation longAt: ptr put: (objectRepresentation longAt: unscannedEphemerons top)].
				 self markAndTrace: ephemeron]
			ifFalse:
				[ptr := ptr + objectRepresentation bytesPerOop]].
	^foundInactive
]

{ #category : #'gc - global' }
SpurGenerationalGC >> markLoopFrom: objOop [
	"Scan objOop and all objects on the mark stack, until the mark stack is empty.
	 N.B. When the incremental GC is written this will probably be refactored as
	 markLoopFrom: objOop while: aBlock"
	<inline: true>
	| objToScan field index numStrongSlots scanLargeObject |

	"Now scan the object, and any remaining objects on the mark stack."
	objToScan := objOop.
	"To avoid overflowing the mark stack when we encounter large objects, we
	 push the obj, then its numStrongSlots, and then index the object from the stack."
	[(objectRepresentation isImmediate: objToScan)
		ifTrue: [scanLargeObject := true]
		ifFalse:
			[numStrongSlots := objectRepresentation numStrongSlotsOfInephemeral: objToScan.
			 scanLargeObject := numStrongSlots > objectRepresentation traceImmediatelySlotLimit].
	 scanLargeObject
		ifTrue: "scanning a large object. scan until hitting an unmarked object, then switch to it, if any."
			[(objectRepresentation isImmediate: objToScan)
				ifTrue:
					[index := objectRepresentation integerValueOf: objToScan.
					 objToScan := objectRepresentation topOfObjStack: markStack]
				ifFalse:
					[index := numStrongSlots.
					 self markAndTraceClassOf: objToScan].
			 [index > 0] whileTrue:
				[index := index - 1.
				 field := objectRepresentation fetchPointer: index ofObject: objToScan.
				 (objectRepresentation isNonImmediate: field) ifTrue:
					[(objectRepresentation isForwarded: field) ifTrue: "fixFollowedField: is /not/ inlined"
						[field := objectRepresentation fixFollowedField: index ofObject: objToScan withInitialValue: field].
					 (self markAndShouldScan: field) ifTrue:
						[index > 0 ifTrue:
							[(objectRepresentation topOfObjStack: markStack) ~= objToScan ifTrue: 
								[objectRepresentation push: objToScan onObjStack: markStack].
							 objectRepresentation push: (objectRepresentation integerObjectOf: index) onObjStack: markStack].
						 objToScan := field.
						 index := -1]]].
			 index >= 0 ifTrue: "if loop terminated without finding an unmarked referent, switch to top of stack."
				[objToScan := objectRepresentation popObjStack: markStack.
				 objToScan = objOop ifTrue:
					[objToScan := objectRepresentation popObjStack: markStack]]]
		ifFalse: "scanning a small object. scan, marking, pushing unmarked referents, then switch to the top of the stack."
			[index := numStrongSlots.
			 self markAndTraceClassOf: objToScan.
			 [index > 0] whileTrue:
				[index := index - 1.
				 field := objectRepresentation fetchPointer: index ofObject: objToScan.
				 (objectRepresentation isNonImmediate: field) ifTrue:
					[(objectRepresentation isForwarded: field) ifTrue: "fixFollowedField: is /not/ inlined"
						[field := objectRepresentation fixFollowedField: index ofObject: objToScan withInitialValue: field].
					 (self markAndShouldScan: field) ifTrue:
						[objectRepresentation push: field onObjStack: markStack.
						 ((objectRepresentation rawNumSlotsOf: field) > objectRepresentation traceImmediatelySlotLimit
						  and: [(numStrongSlots := objectRepresentation numStrongSlotsOfInephemeral: field) > objectRepresentation traceImmediatelySlotLimit]) ifTrue:
							[objectRepresentation push: (objectRepresentation integerObjectOf: numStrongSlots) onObjStack: markStack]]]].
			 objToScan := objectRepresentation popObjStack: markStack].
	 objToScan notNil] whileTrue
]

{ #category : #'gc - global' }
SpurGenerationalGC >> markObjects: objectsShouldBeUnmarkedAndUnmarkedClassesShouldBeExpunged [
	<inline: #never> "for profiling"
	"Mark all accessible objects.  objectsShouldBeUnmarkedAndUnmarkedClassesShouldBeExpunged
	 is true if all objects are unmarked and/or if unmarked classes shoud be removed from the class table."
	"If the incremental collector is running mark bits may be set; stop it and clear them if necessary."
	self cCode: '' inSmalltalk: [objectRepresentation coInterpreter transcript nextPutAll: 'marking...'; flush].
	self runLeakCheckerFor: GCModeFull.

	self shutDownIncrementalGC: objectsShouldBeUnmarkedAndUnmarkedClassesShouldBeExpunged.
	self initializeUnscannedEphemerons.
	self initializeMarkStack.
	self initializeWeaklingStack.
	marking := true.
	self markAccessibleObjectsAndFireEphemerons.
	self expungeDuplicateAndUnmarkedClasses: objectsShouldBeUnmarkedAndUnmarkedClassesShouldBeExpunged.
	self nilUnmarkedWeaklingSlots.
	self freeUnscannedEphemerons.
	marking := false
]

{ #category : #'image segment in/out' }
SpurGenerationalGC >> markObjectsIn: arrayOfRoots [
	"This is part of storeImageSegmentInto:outPointers:roots:."
	self setIsMarkedOf: arrayOfRoots to: true.
	0 to: (self numSlotsOf: arrayOfRoots) - 1 do:
		[:i| | oop |
		oop := self followField: i ofObject: arrayOfRoots.
		(self isNonImmediate: oop) ifTrue:
			[self setIsMarkedOf: oop to: true]]
]

{ #category : #'spur bootstrap' }
SpurGenerationalGC >> markStack [
	^markStack
]

{ #category : #accessing }
SpurGenerationalGC >> markStack: anOop [ 
	<doNotGenerate>
	markStack := anOop
]

{ #category : #'gc - global' }
SpurGenerationalGC >> markWeaklingsAndMarkAndFireEphemerons [
	"After the initial scan-mark is complete ephemerons can be processed.
	 Weaklings have accumulated on the weaklingStack, but more may be
	 uncovered during ephemeron processing.  So trace the strong slots
	 of the weaklings, and as ephemerons are processed ensure any newly
	 reached weaklings are also traced."
	| numTracedWeaklings |
	<inline: false>
	numTracedWeaklings := 0.
	[objectRepresentation coInterpreter markAndTraceUntracedReachableStackPages.
	 objectRepresentation coInterpreter markAndTraceMachineCodeOfMarkedMethods.
	 "Make sure all reached weaklings have their strong slots traced before firing ephemerons..."
	 [numTracedWeaklings := self markAndTraceWeaklingsFrom: numTracedWeaklings.
	  (objectRepresentation sizeOfObjStack: weaklingStack) > numTracedWeaklings] whileTrue.
	 self noUnscannedEphemerons ifTrue:
		[objectRepresentation coInterpreter
			markAndTraceUntracedReachableStackPages;
	 		markAndTraceMachineCodeOfMarkedMethods;
			freeUntracedStackPages;
			freeUnmarkedMachineCode.
		 ^self].
	 self markInactiveEphemerons ifFalse:
		[self fireAllUnscannedEphemerons].
	 self markAllUnscannedEphemerons]
		repeat
]

{ #category : #'header format' }
SpurGenerationalGC >> markedBitFullShift [
	<cmacro>
	"bit 1 of 2-bit field above identityHash (little endian)"
	^55
]

{ #category : #'header format' }
SpurGenerationalGC >> markedBitHalfShift [
	<cmacro>
	"bit 1 of 2-bit field above identityHash (little endian)"
	^23
]

{ #category : #accessing }
SpurGenerationalGC >> marking [
	^ marking
]

{ #category : #snapshot }
SpurGenerationalGC >> memoryBaseForImageRead [
	"Answer the address to read the image into."
	^oldSpaceStart
]

{ #category : #snapshot }
SpurGenerationalGC >> memoryLimit [
	^endOfMemory
]

{ #category : #'spur bootstrap' }
SpurGenerationalGC >> mournQueue [
	^mournQueue
]

{ #category : #accessing }
SpurGenerationalGC >> mournQueue: anOop [ 
	<doNotGenerate>
	mournQueue := anOop
]

{ #category : #accessing }
SpurGenerationalGC >> needGCFlag [
	^needGCFlag
]

{ #category : #accessing }
SpurGenerationalGC >> needGCFlag: anInteger [
	needGCFlag := anInteger ~= 0
]

{ #category : #'gc - scavenging' }
SpurGenerationalGC >> newSpaceIsEmpty [
	^freeStart = scavenger eden start
	  and: [pastSpaceStart = scavenger pastSpace start]
]

{ #category : #accessing }
SpurGenerationalGC >> newSpaceLimit [
	<cmacro: '() GIV(newSpaceLimit)'>
	^newSpaceLimit
]

{ #category : #accessing }
SpurGenerationalGC >> newSpaceSize [
	^(freeStart - scavenger eden start)
	 + (pastSpaceStart - scavenger pastSpace start)
]

{ #category : #accessing }
SpurGenerationalGC >> newSpaceStart [
	^newSpaceStart
]

{ #category : #'weakness and ephemerality' }
SpurGenerationalGC >> nilUnmarkedWeaklingSlots [
	"Nil the unmarked slots in the weaklings on the
	 weakling stack, finalizing those that lost references.
	 Finally, empty the weaklingStack."
	<inline: #never> "for profiling"
	self cCode: '' inSmalltalk: [objectRepresentation coInterpreter transcript nextPutAll: 'nilling...'; flush].
	self eassert: [self allOldMarkedWeakObjectsOnWeaklingStack].
	weaklingStack = objectRepresentation nilObject ifTrue:
		[^self].
	objectRepresentation objStack: weaklingStack from: 0 do:
		[:weakling| | anyUnmarked |
		anyUnmarked := self nilUnmarkedWeaklingSlotsIn: weakling.
		anyUnmarked ifTrue:
			["fireFinalization: could grow the mournQueue and if so,
			  additional pages must be marked to avoid being GC'ed."
			 self assert: marking.
			 coInterpreter fireFinalization: weakling]].
	objectRepresentation emptyObjStack: weaklingStack
]

{ #category : #'weakness and ephemerality' }
SpurGenerationalGC >> noUnscannedEphemerons [
	^unscannedEphemerons top = unscannedEphemerons start
]

{ #category : #'free space' }
SpurGenerationalGC >> numFreeLists [
	"Answer the number of free lists.  We use freeListsMask, a bitmap, to avoid
	 reading empty list heads.  This should fit in a machine word to end up in a
	 register during free chunk allocation."
	^ self wordSize * 8
]

{ #category : #'object enumeration' }
SpurGenerationalGC >> objectAfter: objOop [
	<api>
	"Object parsing.
	1. all objects have at least a word following the header, for a forwarding pointer.
	2. objects with an overflow size have a preceeing word with a saturated slotSize.  If the word following
	    an object doesn't have a saturated size field it must be a single-header object.  If the word following
	   does have a saturated slotSize it must be the overflow size word."
	<inline: false>
	(self oop: objOop isLessThan: newSpaceLimit) ifTrue:
		[(self isInEden: objOop) ifTrue:
			[^self objectAfter: objOop limit: freeStart].
		 (self isInPastSpace: objOop) ifTrue:
			[^self objectAfter: objOop limit: pastSpaceStart].
		 ^self objectAfter: objOop limit: scavenger futureSurvivorStart].
	^objectRepresentation objectAfter: objOop limit: endOfMemory
]

{ #category : #'object enumeration' }
SpurGenerationalGC >> objectBefore: objOop [
	<api>
	| prev |
	prev := nil.
	(self oop: objOop isLessThan: newSpaceLimit) ifTrue:
		[self allNewSpaceEntitiesDo:
			[:o|
			 (self oop: o isGreaterThanOrEqualTo: objOop) ifTrue:
				[^prev].
			 prev := o].
		 ^prev].
	self allOldSpaceEntitiesDo:
		[:o|
		 (self oop: o isGreaterThanOrEqualTo: objOop) ifTrue:
			[^prev].
		 prev := o].
	^prev
]

{ #category : #accessing }
SpurGenerationalGC >> objectMemory [
	
	^ objectRepresentation 
]

{ #category : #accessing }
SpurGenerationalGC >> objectRepresentation: aSpurObjectRepresentation [ 
	objectRepresentation := aSpurObjectRepresentation
]

{ #category : #'image segment in/out' }
SpurGenerationalGC >> objectsReachableFromRoots: arrayOfRoots [
	"This is part of storeImageSegmentInto:outPointers:roots:.
	 Answer an Array of all the objects only reachable from the argument, an Array of root objects,
	 starting with arrayOfRoots.  If there is no space, answer a SmallInteger whose value is the
	 number of slots required.  This is used to collect the objects to include in an image segment
	 on Spur, separate from creating the segment, hence simplifying the implementation.
	 Thanks to Igor Stasenko for this idea."

	| freeChunk ptr start limit count oop objOop |
	<var: #freeChunk type: #usqInt> "& hence start & ptr are too; limit is also because of addressAfter:"
	<inline: #never>
	self assert: (self isArray: arrayOfRoots).
	"Mark all objects except those only reachable from the arrayOfRoots by marking
	 each object in arrayOfRoots and then marking all reachable objects (from the
	 system roots).  This leaves unmarked only objects reachable from the arrayOfRoots.
	 N.B. A side-effect of the marking is that all forwarders in arrayOfRoots will be followed."
 	self assert: self allObjectsUnmarked.
	self markObjectsIn: arrayOfRoots.
	self markObjects: false.

	"After the mark phase all unreachable weak slots will have been nilled
	 and all active ephemerons fired."
	self assert: (self isEmptyObjStack: markStack).
	self assert: (self isEmptyObjStack: weaklingStack).
	self assert: self noUnscannedEphemerons.

	"Now unmark the roots before collecting the transitive closure of unmarked objects accessible from the roots."
	self unmarkObjectsIn: arrayOfRoots.

	"Use the largest free chunk to answer the result."
	freeChunk := self allocateLargestFreeChunk. "N.B. Does /not/ update totalFreeOldSpace"
	totalFreeOldSpace := totalFreeOldSpace - (self bytesInObject: freeChunk). "but must update so that growth in the markStack does not cause assert fails."
	ptr := start := freeChunk + self baseHeaderSize.
	limit := self addressAfter: freeChunk.
	count := 0.

	"First put the arrayOfRoots; order is important."
	self noCheckPush: arrayOfRoots onObjStack: markStack.

	"Now collect the roots and the transitive closure of unmarked objects from them."
	[self isEmptyObjStack: markStack] whileFalse:
		[objOop := self popObjStack: markStack.
		 self assert: (self isMarked: objOop).
		 count := count + 1.
		 ptr < limit ifTrue:
			[self longAt: ptr put: objOop.
			 ptr := ptr + self bytesPerOop].
		 oop := self fetchClassOfNonImm: objOop.
		 (self isMarked: oop) ifFalse:
			[self setIsMarkedOf: oop to: true.
			 self noCheckPush: oop onObjStack: markStack].
		 ((self isContextNonImm: objOop)
		  and: [coInterpreter isStillMarriedContext: objOop]) "widow now, before the copy loop"
			ifTrue:
				[0 to: (coInterpreter numSlotsOfMarriedContext: objOop) - 1 do:
					[:i|
					 oop := coInterpreter fetchPointer: i ofMarriedContext: objOop.
					 ((self isImmediate: oop)
					  or: [self isMarked: oop]) ifFalse:
						[self setIsMarkedOf: oop to: true.
						 self noCheckPush: oop onObjStack: markStack]]]
			ifFalse:
				[0 to: (self numPointerSlotsOf: objOop) - 1 do:
					[:i|
					 oop := self fetchPointer: i ofObject: objOop.
					 ((self isImmediate: oop)
					  or: [self isMarked: oop]) ifFalse:
						[self setIsMarkedOf: oop to: true.
						 self noCheckPush: oop onObjStack: markStack]]]].

	self unmarkAllObjects.

	"Now try and allocate the result"
	(count > (ptr - start / self bytesPerOop) "not enough room"
	 or: [limit ~= ptr and: [limit - ptr <= self allocationUnit]]) ifTrue: "can't split a single word"
		[self freeObject: freeChunk.
		 self checkFreeSpace: GCModeImageSegment.
		 ^self integerObjectOf: count].
	"There's room; set the format, & classIndex and shorten."
	self setFormatOf: freeChunk to: self arrayFormat.
	self setClassIndexOf: freeChunk to: ClassArrayCompactIndex.
	self shorten: freeChunk toIndexableSize: count.
	(self isForwarded: freeChunk) ifTrue:
		[freeChunk := self followForwarded: freeChunk].
	self possibleRootStoreInto: freeChunk.
	self checkFreeSpace: GCModeImageSegment.
	self runLeakCheckerFor: GCModeImageSegment.
	^freeChunk
]

{ #category : #'object enumeration' }
SpurGenerationalGC >> oldSpaceObjectAfter: objOop [
	<api>
	"Object parsing.
	1. all objects have at least a word following the header, for a forwarding pointer.
	2. objects with an overflow size have a preceeing word with a saturated slotSize.  If the word following
	    an object doesn't have a saturated size field it must be a single-header object.  If the word following
	   does have a saturated slotSize it must be the overflow size word."
	<inline: false>
	^objectRepresentation objectAfter: objOop limit: endOfMemory
]

{ #category : #accessing }
SpurGenerationalGC >> oldSpaceSize [
	^ objectRepresentation segmentManager totalBytesInSegments
]

{ #category : #accessing }
SpurGenerationalGC >> oldSpaceStart [
	<cmacro: '() GIV(oldSpaceStart)'>
	^ oldSpaceStart
]

{ #category : #accessing }
SpurGenerationalGC >> pastSpaceStart [
	<cmacro: '() GIV(pastSpaceStart)'>
	^pastSpaceStart
]

{ #category : #compaction }
SpurGenerationalGC >> prepareObjStacksForPlanningCompactor [
	"SpurPlanningCompactor overwrites the first fields of all moved objects, and saves these
	 fields in a data structure from which they can only be retrieved while scanning the heap.
	 The first field of an objStack page is its stack index, and so to know how many fields in an
	 objStack page to update it is necessary to save the ObjStackTopx field somewhere temporarily.
	 We use the hash field."

	objectRepresentation
		prepareObjStackForPlanningCompactor: markStack;
		prepareObjStackForPlanningCompactor: weaklingStack;
		prepareObjStackForPlanningCompactor: mournQueue
]

{ #category : #'debug printing' }
SpurGenerationalGC >> printFreeChunk: freeChunk printAsTreeNode: printAsTreeNode [
	| numBytes |
	numBytes := self bytesInObject: freeChunk.
	coInterpreter
		print: 'freeChunk '; printHexPtrnp: freeChunk.
	printAsTreeNode ifTrue:
		[coInterpreter
			print: ((freeChunk = (freeLists at: 0)) ifTrue: [' + '] ifFalse: [' - ']);
			printHexPtrnp:(self addressAfter: freeChunk)].
	coInterpreter
		print: ' bytes '; printNum: numBytes;
		print: ' next '; printHexPtrnp: (self fetchPointer: self freeChunkNextIndex
											ofFreeChunk: freeChunk).
	(self isLilliputianSize: numBytes) ifFalse: 
		[coInterpreter
			print: ' prev '; printHexPtrnp: (self fetchPointer: self freeChunkPrevIndex
											ofFreeChunk: freeChunk).].
	(numBytes >= (self numFreeLists * self allocationUnit)
	 and: [printAsTreeNode]) ifTrue:
		[coInterpreter
			print: ' ^ '; printHexPtrnp: (self fetchPointer: self freeChunkParentIndex
											ofFreeChunk: freeChunk);
			print: ' < '; printHexPtrnp: (self fetchPointer: self freeChunkSmallerIndex
											ofFreeChunk: freeChunk);
			print: ' > '; printHexPtrnp: (self fetchPointer: self freeChunkLargerIndex
											ofFreeChunk: freeChunk)].
	coInterpreter cr
]

{ #category : #'debug printing' }
SpurGenerationalGC >> printFreeList: chunkOrIndex [
	<api>
	| freeChunk |
	(chunkOrIndex >= 0 and: [chunkOrIndex < self numFreeLists]) ifTrue:
		[^self printFreeList: (freeLists at: chunkOrIndex)].
	freeChunk := chunkOrIndex.
	[freeChunk ~= 0] whileTrue:
		[self printFreeChunk: freeChunk.
		 freeChunk := self fetchPointer: self freeChunkNextIndex ofFreeChunk: freeChunk]
]

{ #category : #'debug printing' }
SpurGenerationalGC >> printFreeListHeads [
	<api>
	| expectedMask |
	expectedMask := 0.
	0 to: self numFreeLists - 1 do:
		[:i|
		coInterpreter printHex: (freeLists at: i).
		(freeLists at: i) ~= 0 ifTrue:
			[expectedMask := expectedMask + (1 << i)].
		i + 1 \\ (32 >> self logBytesPerOop) = 0
			ifTrue: [coInterpreter cr]
			ifFalse: [coInterpreter print: '  ']].
	coInterpreter
		cr;
		print: 'mask: '; printHexnp: freeListsMask;
		print: ' expected: '; printHexnp: expectedMask;
		cr
]

{ #category : #'debug printing' }
SpurGenerationalGC >> printFreeTree [
	<api>
	self printFreeTreeChunk: (freeLists at: 0)
]

{ #category : #'weakness and ephemerality' }
SpurGenerationalGC >> pushOnUnscannedEphemeronsStack: anEphemeron [
	"Attempt to push anEphemeron on the unscanned ephemerons stack
	 and answer if the attempt succeeded.  Note that the ephemeron
	 stack overflowing isn't a disaster; it simply means treating the
	 ephemeron as strong in this GC cycle."
	<inline: false>
	self assert: (objectRepresentation isEphemeron: anEphemeron).
	unscannedEphemerons top >= unscannedEphemerons limit ifTrue: [ | desiredSize reallocated |
		"Reallocate and duplication"
		desiredSize := (unscannedEphemerons limit - unscannedEphemerons start) * 2.
		reallocated := self
			realloc: unscannedEphemerons start
			_: desiredSize.
		reallocated ifNil: [ self error: 'Not enough room to grow unscannedEphemerons queue' ].
		unscannedEphemerons limit: reallocated + desiredSize.
		unscannedEphemerons top: reallocated + (unscannedEphemerons top - unscannedEphemerons start).
		unscannedEphemerons start: reallocated ].

	objectRepresentation longAt: unscannedEphemerons top put: anEphemeron.
	unscannedEphemerons top: unscannedEphemerons top + objectRepresentation bytesPerOop.
	^true
]

{ #category : #'weakness and ephemerality' }
SpurGenerationalGC >> queueMourner: anEphemeronOrWeakArray [
	"Add the ephemeron to the queue and make it non-ephemeral, to avoid subsequent firing.
	 Alas this means that other ephemerons on the same object not identified in this sccavenge
	 or GC will not fire until later.  But that's life."
	self assert: ((objectRepresentation isNonImmediate: anEphemeronOrWeakArray)
				and: [(objectRepresentation formatOf: anEphemeronOrWeakArray) = objectRepresentation ephemeronFormat
				   or: [(objectRepresentation formatOf: anEphemeronOrWeakArray) = objectRepresentation weakArrayFormat]]).
	self deny: ((objectRepresentation formatOf: anEphemeronOrWeakArray) = objectRepresentation ephemeronFormat
				and: [objectRepresentation is: anEphemeronOrWeakArray onObjStack: mournQueue]).
	objectRepresentation ensureRoomOnObjStackAt: MournQueueRootIndex.
	objectRepresentation push: anEphemeronOrWeakArray onObjStack: mournQueue
]

{ #category : #compaction }
SpurGenerationalGC >> relocateObjStacksForPlanningCompactor [
	"Relocate all non-empty objStack pages, following the objStacks from the roots."

	markStack := objectRepresentation relocateObjStackForPlanningCompactor: markStack.
	weaklingStack := objectRepresentation relocateObjStackForPlanningCompactor: weaklingStack.
	mournQueue := objectRepresentation relocateObjStackForPlanningCompactor: mournQueue
]

{ #category : #accessing }
SpurGenerationalGC >> remapBufferCount [
	<cmacro: '() GIV(remapBufferCount)'>
	^remapBufferCount
]

{ #category : #scavenger }
SpurGenerationalGC >> rememberedSetObj [
	^objectRepresentation fetchPointer: RememberedSetRootIndex ofObject: objectRepresentation hiddenRootsObject
]

{ #category : #scavenger }
SpurGenerationalGC >> rememberedSetObj: anObj [
	self assert: (self isOldObject: anObj).
	objectRepresentation storePointerUnchecked: RememberedSetRootIndex ofObject: objectRepresentation hiddenRootsObject withValue: anObj
]

{ #category : #'plugin support' }
SpurGenerationalGC >> removeGCRoot: varLoc [
	"Remove the given variable location to the extra roots table."
	<api>
	<var: #varLoc type: #'sqInt *'>
	1 to: extraRootCount do:
		[:i|
		varLoc = (extraRoots at: i) ifTrue: "swap varLoc with last entry"
			[extraRoots at: i put: (extraRoots at: extraRootCount).
			 extraRootCount := extraRootCount - 1.
			 ^true]].
	^false "not found"
]

{ #category : #'allocation accounting' }
SpurGenerationalGC >> resetAllocationAccountingAfterGC [
	"oldSpaceUsePriorToScavenge is used to maintain an accurate allocation count.
	 Since scavenging may tenure objects and tenuring does not count as allocation (that
	 would count twice) we must compute heapSizeAtPreviousGC after any tenuring.
	 fullGC reclaims space which does not count as deallocation (that would not count
	 allocations at all), so we must reset heapSizeAtPreviousGC after GC also."
	<inline: true>
	oldSpaceUsePriorToScavenge := objectRepresentation segmentManager totalOldSpaceCapacity - totalFreeOldSpace
]

{ #category : #'free space' }
SpurGenerationalGC >> resetFreeListHeads [
	freeListsMask := 0.
	0 to: self numFreeLists - 1 do:
		[:i| freeLists at: i put: 0]
]

{ #category : #snapshot }
SpurGenerationalGC >> reverseBytesInMemory [
	self reverseBytesFrom: oldSpaceStart to: endOfMemory
]

{ #category : #'debug support' }
SpurGenerationalGC >> runLeakCheckerFor: gcModes [
	<inline: false>
	^self
		inLineRunLeakCheckerFor: gcModes
		excludeUnmarkedObjs: false
		classIndicesShouldBeValid: true
]

{ #category : #'debug support' }
SpurGenerationalGC >> runLeakCheckerFor: gcModes excludeUnmarkedObjs: excludeUnmarkedObjs classIndicesShouldBeValid: classIndicesShouldBeValid [
	<inline: false>
	self inLineRunLeakCheckerFor: gcModes
		excludeUnmarkedObjs: excludeUnmarkedObjs
		classIndicesShouldBeValid: classIndicesShouldBeValid
]

{ #category : #'debug support' }
SpurGenerationalGC >> runLeakCheckerForFreeSpace: gcModes [
	<inline: false>
	(gcModes anyMask: GCModeFreeSpace) ifTrue:
		[coInterpreter reverseDisplayFrom: 16 to: 19.
		 self clearLeakMapAndMapAccessibleFreeSpace.
		 self asserta: self checkHeapFreeSpaceIntegrity]
]

{ #category : #testing }
SpurGenerationalGC >> scavengeInProgress [
	^gcPhaseInProgress == ScavengeInProgress
]

{ #category : #accessing }
SpurGenerationalGC >> scavengeThreshold [
	^ scavengeThreshold
]

{ #category : #accessing }
SpurGenerationalGC >> scavenger [
	<doNotGenerate>
	^ scavenger
]

{ #category : #scavenger }
SpurGenerationalGC >> scavengerDenominator [
	"David's paper uses 140Kb eden + 2 x 28kb survivor spaces,
	 which is 5 7ths for eden and 1 7th each for the survivor spaces.
	 So express scavenger sizes in 7ths"
	^7
]

{ #category : #'gc - scavenging' }
SpurGenerationalGC >> scavengingGCTenuringIf: tenuringCriterion [
	"Run the scavenger."
	<inline: false>
	self assert: remapBufferCount = 0.
	(self asserta: scavenger eden limit - freeStart > objectRepresentation coInterpreter interpreterAllocationReserveBytes) ifFalse:
		[coInterpreter tab;
			printNum: scavenger eden limit - freeStart; space;
			printNum: objectRepresentation coInterpreter interpreterAllocationReserveBytes; space;
			printNum: objectRepresentation coInterpreter interpreterAllocationReserveBytes - (scavenger eden limit - freeStart); cr].
	self checkMemoryMap.
	self checkFreeSpace: GCModeNewSpace.
	self runLeakCheckerFor: GCModeNewSpace.

	objectRepresentation coInterpreter
		preGCAction: GCModeNewSpace;
		"would prefer this to be in mapInterpreterOops, but
		 compatibility with ObjectMemory dictates it goes here."
		flushMethodCacheFrom: newSpaceStart to: newSpaceLimit.
	needGCFlag := false.

	gcStartUsecs := objectRepresentation coInterpreter ioUTCMicrosecondsNow.

	self doScavenge: tenuringCriterion.

	statScavenges := statScavenges + 1.
	statGCEndUsecs := objectRepresentation coInterpreter ioUTCMicrosecondsNow.
	statSGCDeltaUsecs := statGCEndUsecs - gcStartUsecs.
	statScavengeGCUsecs := statScavengeGCUsecs + statSGCDeltaUsecs.
	statRootTableCount := scavenger rememberedSetSize.

	scavenger logScavenge.

	objectRepresentation coInterpreter postGCAction: GCModeNewSpace.

	self runLeakCheckerFor: GCModeNewSpace.
	self checkFreeSpace: GCModeNewSpace
]

{ #category : #'gc - scavenging' }
SpurGenerationalGC >> scheduleScavenge [
	needGCFlag := true.
	objectRepresentation coInterpreter forceInterruptCheck
]

{ #category : #snapshot }
SpurGenerationalGC >> setEndOfMemory: newEndOfMemory [
	"Set by the segment manager after swizzling the image,
	 and by the SpurBootstrap on writing out the transformed image."
	endOfMemory := newEndOfMemory.
	freeOldSpaceStart > newEndOfMemory ifTrue:
		[freeOldSpaceStart := newEndOfMemory]
]

{ #category : #snapshot }
SpurGenerationalGC >> setHeapBase: baseOfHeap memoryLimit: memLimit endOfMemory: memEnd [
	"Set the dimensions of the heap, answering the start of oldSpace. edenBytes holds the desired ``size of eden''
	 which is actually the total size of new space minus the reserve.  edenBytes is then divided up between eden
	 and the two survivor spaces, where each survivor space is a scavengerDenominator (one seventh) of the total."
	"Transcript
		cr; nextPutAll: 'heapBase: '; print: baseOfHeap; nextPut: $/; nextPutAll: baseOfHeap hex;
		nextPutAll: ' memLimit '; print: memLimit; nextPut: $/; nextPutAll: memLimit hex;
		nextPutAll: ' memEnd '; print: memEnd; nextPut: $/; nextPutAll: memEnd hex; cr; flush."
	"This is more than a little counter-intuitive.  Eden must include interpreterAllocationReserveBytes."
	<inline: #never>
	| reserve |
	reserve := coInterpreter interpreterAllocationReserveBytes.
	newSpaceStart := baseOfHeap.
	newSpaceLimit := baseOfHeap + edenBytes + reserve.
	scavenger newSpaceStart: newSpaceStart
				newSpaceBytes: newSpaceLimit - newSpaceStart
				survivorBytes: newSpaceLimit - newSpaceStart - reserve // self scavengerDenominator.

	freeStart := scavenger eden start.
	pastSpaceStart := scavenger pastSpace start.

	oldSpaceStart := newSpaceLimit.
	freeOldSpaceStart := memEnd.
	endOfMemory := memLimit.

	^baseOfHeap
]

{ #category : #'allocation accounting' }
SpurGenerationalGC >> setHeapSizeAtPreviousGC [
	"heapSizeAtPreviousGC is used to invoke full GC when lots of oldSpace objects are created.
	 Also reset oldSpaceUsePriorToScavenge."
	<inline: true>
	heapSizeAtPreviousGC := objectRepresentation segmentManager totalOldSpaceCapacity - totalFreeOldSpace.
	self resetAllocationAccountingAfterGC
]

{ #category : #'growing/shrinking memory' }
SpurGenerationalGC >> setLastSegment: segInfo [
	"Update after removing a segment.
	 Here we cut back endOfMemory if required."
	<var: #segInfo type: #'SpurSegmentInfo *'>
	| currentEnd |
	<var: #currentEnd type: #usqInt>
	currentEnd := segInfo segLimit - self bridgeSize.
	currentEnd <= endOfMemory ifTrue:
		[endOfMemory := currentEnd.
		 freeOldSpaceStart > currentEnd ifTrue:
			[freeOldSpaceStart :=currentEnd]]
]

{ #category : #'free space' }
SpurGenerationalGC >> setNextFreeChunkOf: freeChunk withValue: nextFreeChunk chunkBytes: chunkBytes [
	self 
		setNextFreeChunkOf: freeChunk 
		withValue: nextFreeChunk 
		isLilliputianSize: (objectRepresentation isLilliputianSize: chunkBytes) 
	
	
]

{ #category : #'free space' }
SpurGenerationalGC >> setNextFreeChunkOf: freeChunk withValue: nextFreeChunk isLilliputianSize: lilliputian [ 
	<inline: true> "Inlining is quite important since isLilliputianSize: is often true/false"
	self 
		storePointer: self freeChunkNextIndex 
		ofFreeChunk: freeChunk 
		withValue: nextFreeChunk.
	(nextFreeChunk ~= 0 and: [lilliputian not]) ifTrue:
		[self 
			storePointer: self freeChunkPrevIndex 
			ofFreeChunk: nextFreeChunk 
			withValue: freeChunk]
	
	
]

{ #category : #'free space' }
SpurGenerationalGC >> setObjectFree: objOop [
	"Mark an object free, but do not add it to the free lists.  The wrinkle here
	 is that we don't tolerate a zero-slot count in a free object so that the
	 (self long64At: objOop) ~= 0 assert in isEnumerableObject: isn't triggered."
		 
	(self rawNumSlotsOf: objOop) = 0 ifTrue:
		[self rawNumSlotsOf: objOop put: 1].
	self setFree: objOop
]

{ #category : #'free space' }
SpurGenerationalGC >> shrinkThreshold [
	^shrinkThreshold
]

{ #category : #'free space' }
SpurGenerationalGC >> shrinkThreshold: aValue [
	shrinkThreshold := aValue
]

{ #category : #'gc - incremental' }
SpurGenerationalGC >> shutDownIncrementalGC: objectsShouldBeUnmarked [
	"If the incremental collector is running mark bits may be set; stop it and clear them if necessary."
	self flag: 'need to implement the inc GC first...'.
	objectsShouldBeUnmarked ifTrue:
		[self assert: self allObjectsUnmarked]
]

{ #category : #'free space' }
SpurGenerationalGC >> sizeOfFree: objOop [
	"For compatibility with ObjectMemory, answer the size of a free chunk in bytes.
	 Do *not* use internally."
	self assert: (self isFreeObject: objOop).
	^objectRepresentation bytesInObject: objOop
]

{ #category : #'free space' }
SpurGenerationalGC >> sizeOfLargestFreeChunk [
	"Answer the size of largest free chunk in oldSpace."
	| freeChunk |
	freeChunk := self findLargestFreeChunk.
	freeChunk ifNil:
		[63 to: 1 by: -1 do:
			[:i|
			(freeLists at: i) ifNotNil:
				[:chunk| ^self bytesInObject: chunk]].
		 ^0].
	^objectRepresentation bytesInObject: freeChunk
]

{ #category : #testing }
SpurGenerationalGC >> slidingCompactionInProgress [
	^gcPhaseInProgress == SlidingCompactionInProgress
]

{ #category : #'gc - scavenge/compact' }
SpurGenerationalGC >> slidingCompactionRemapObj: objOop [
	"Scavenge or simply follow objOop.  Answer the new location of objOop.
	 The send should have been guarded by a send of shouldRemapOop:.
	 The method is called remapObj: for compatibility with ObjectMemory."
	<inline: true>
	| resolvedObj |
	self assert: (objectRepresentation shouldRemapOop: objOop).
	(objectRepresentation isForwarded: objOop)
		ifTrue:
			[resolvedObj := objectRepresentation followForwarded: objOop]
		ifFalse:
			[self deny: (self isInFutureSpace: objOop).
			 resolvedObj := objOop].
	gcPhaseInProgress > 0 ifTrue:
		[self scavengeInProgress
			ifTrue:
				[((objectRepresentation isReallyYoung: resolvedObj) "don't scavenge immediate, old, or CogMethod objects."
				  and: [(self isInFutureSpace: resolvedObj) not]) ifTrue: 
					[^scavenger copyAndForward: resolvedObj]]
			ifFalse:
				[self assert: self slidingCompactionInProgress.
				 (compactor isMobile: objOop) ifTrue:
					[^objectRepresentation fetchPointer: 0 ofObject: objOop]]].
	^resolvedObj
]

{ #category : #'gc - scavenge/compact' }
SpurGenerationalGC >> slidingCompactionShouldRemapObj: objOop [
	<inline: true>
	"Answer if the obj should be scavenged, or simply followed. Sent via the compactor
	 from shouldRemapObj:.  We test for being already scavenged because mapStackPages
	 via mapInterpreterOops may be applied twice in the context of a global GC where a
	 scavenge, followed by a scan-mark-free, and final compaction passes may result in
	 scavenged fields being visited twice."
	^(objectRepresentation isForwarded: objOop)
	   or: [gcPhaseInProgress > 0 "Hence either scavengeInProgress or slidingCompactionInProgress"
		   and: [self scavengeInProgress
					ifTrue: [(objectRepresentation isReallyYoungObject: objOop)
							and: [(self isInFutureSpace: objOop) not]]
					ifFalse: [compactor isMobile: objOop]]]
]

{ #category : #'heap management' }
SpurGenerationalGC >> storePointer: fieldIndex ofFreeChunk: objOop withValue: valuePointer [

	self assert: (self isFreeObject: objOop).
	self assert: (valuePointer = 0 or: [self isFreeObject: valuePointer]).		
	^objectRepresentation
		longAt: objOop + objectRepresentation baseHeaderSize + (fieldIndex << objectRepresentation shiftForWord)
		put: valuePointer
]

{ #category : #'gc - scavenging' }
SpurGenerationalGC >> sufficientSpaceAfterGC: numBytes [
	"This is ObjectMemory's funky entry-point into its incremental GC,
	 which is a stop-the-world a young generation reclaimer.  In Spur
	 we run the scavenger.  Answer if space is not low."

	| heapSizePostGC |
	self assert: numBytes = 0.
	1halt.
	self scavengingGCTenuringIf: TenureByAge.
	heapSizePostGC := segmentManager totalOldSpaceCapacity - totalFreeOldSpace.
	(heapSizePostGC - heapSizeAtPreviousGC) asFloat / heapSizeAtPreviousGC >= heapGrowthToSizeGCRatio ifTrue:
		[self fullGC].
	[totalFreeOldSpace < growHeadroom
	 and: [(self growOldSpaceByAtLeast: 0) notNil]] whileTrue:
		[totalFreeOldSpace >= growHeadroom ifTrue:
			[^true]].
	lowSpaceThreshold > totalFreeOldSpace ifTrue: "space is low"
		[lowSpaceThreshold := 0. "avoid signalling low space twice"
		 ^false].
	^true
]

{ #category : #'object enumeration' }
SpurGenerationalGC >> swizzleObjectStacks [

	markStack := self swizzleObjStackAt: MarkStackRootIndex.
	weaklingStack := self swizzleObjStackAt: WeaklingStackRootIndex.
	mournQueue := self swizzleObjStackAt: MournQueueRootIndex.
]

{ #category : #'free space' }
SpurGenerationalGC >> totalFreeListBytes [
	"This method both computes the actual number of free bytes by traversing all free objects
	 on the free lists/tree, and checks that the tree is valid.  It is used mainly by checkFreeSpace."
	| totalFreeBytes bytesInChunk listNode nextNode |
	totalFreeBytes := 0.
	1 to: self numFreeLists - 1 do:
		[:i| 
		bytesInChunk := i * objectRepresentation allocationUnit.
		listNode := freeLists at: i.
		[listNode ~= 0] whileTrue:
			[totalFreeBytes := totalFreeBytes + bytesInChunk.
			 self assertValidFreeObject: listNode.
			 self assert: bytesInChunk = (objectRepresentation bytesInObject: listNode).
			 nextNode := self fetchPointer: self freeChunkNextIndex ofFreeChunk: listNode.
			 self assert: nextNode ~= listNode.
			 listNode := nextNode]].

	self freeTreeNodesDo:
		[:treeNode|
		 bytesInChunk := objectRepresentation bytesInObject: treeNode.
		 self assert: bytesInChunk / objectRepresentation allocationUnit >= self numFreeLists.
		 listNode := treeNode.
		 [listNode ~= 0] whileTrue:
			["self printFreeChunk: listNode"
			 self assertValidFreeObject: listNode.
			 self assert: (listNode = treeNode
						  or: [(self fetchPointer: self freeChunkParentIndex ofFreeChunk: listNode) = 0]).
			 totalFreeBytes := totalFreeBytes + bytesInChunk.
			 self assert: bytesInChunk = (objectRepresentation bytesInObject: listNode).
			 nextNode := self fetchPointer: self freeChunkNextIndex ofFreeChunk: listNode.
			 self assert: nextNode ~= listNode.
			 listNode := nextNode].
		 treeNode].
	^totalFreeBytes
]

{ #category : #'debug support' }
SpurGenerationalGC >> totalFreeOldSpace [
	<doNotGenerate>
	^ totalFreeOldSpace
]

{ #category : #accessing }
SpurGenerationalGC >> totalFreeOldSpace: anInteger [
	totalFreeOldSpace := anInteger
]

{ #category : #'free space' }
SpurGenerationalGC >> unlinkFreeChunk: chunk atIndex: index chunkBytes: chunkBytes [
	^self 
		unlinkFreeChunk: chunk 
		atIndex: index 
		isLilliputianSize: (objectRepresentation isLilliputianSize: chunkBytes) 
]

{ #category : #'free space' }
SpurGenerationalGC >> unlinkFreeChunk: chunk atIndex: index isLilliputianSize: lilliputian [ 
	"Unlink and answer a small chunk from one of the fixed size freeLists"
	<inline: true> "inlining is important because isLilliputianSize: is often true"
	|next|
	self assert: ((objectRepresentation bytesInObject: chunk) = (index * objectRepresentation allocationUnit)
				and: [index > 1 "a.k.a. (self bytesInObject: chunk) > self allocationUnit"
				and: [(objectRepresentation startOfObject: chunk) = chunk]]).
			
	"For some reason the assertion is not compiled correctly"
	self cCode: '' inSmalltalk: [self assert: (objectRepresentation isLilliputianSize: (objectRepresentation bytesInObject: chunk)) = lilliputian].
	
	freeLists
		at: index 
		put: (next := self
				fetchPointer: self freeChunkNextIndex
				ofFreeChunk: chunk).
	(lilliputian not and: [next ~= 0]) ifTrue:
		[self storePointer: self freeChunkPrevIndex ofFreeChunk: next withValue: 0].
	^chunk
]

{ #category : #'free space' }
SpurGenerationalGC >> unlinkFreeChunk: freeChunk chunkBytes: chunkBytes [
	"Unlink a free object from the free lists. Do not alter totalFreeOldSpace. Used for coalescing."
	| index next prev |
	index := chunkBytes / objectRepresentation allocationUnit.
	
	"Pathological 64 bits case - size 1 - single linked list"
	(objectRepresentation isLilliputianSize: chunkBytes) ifTrue:
		[^ self  unlinkLilliputianChunk: freeChunk index: index].
	
	prev := self fetchPointer: self freeChunkPrevIndex ofFreeChunk: freeChunk.
	"Has prev element: update double linked list"
	prev ~= 0 ifTrue:
		[self 
			setNextFreeChunkOf: prev 
			withValue: (self fetchPointer: self freeChunkNextIndex ofFreeChunk: freeChunk) 
			chunkBytes: chunkBytes.
		 ^freeChunk].
	
	"Is the beginning of a list"
	"Small chunk"
	(index < self numFreeLists and: [1 << index <= freeListsMask]) ifTrue: 
		[self unlinkFreeChunk: freeChunk atIndex: index isLilliputianSize: false.
		 ^freeChunk].
	"Large chunk"
	 next := self fetchPointer: self freeChunkNextIndex ofFreeChunk: freeChunk.
	 next = 0
		ifTrue: "no list; remove the interior node"
			[self unlinkSolitaryFreeTreeNode: freeChunk]
		ifFalse: "list; replace node with it"
			[self inFreeTreeReplace: freeChunk with: next].
	^freeChunk
	
	

	
]

{ #category : #'free space' }
SpurGenerationalGC >> unlinkLilliputianChunk: freeChunk index: index [
	| node prev next |
	<inline: #never> "for profiling"
	 node := freeLists at: index.
	 prev := 0.
	 [node ~= 0] whileTrue:
		[self assert: node = (objectRepresentation startOfObject: node).
		 self assertValidFreeObject: node.
		 next := self fetchPointer: self freeChunkNextIndex ofFreeChunk: node.
		 node = freeChunk ifTrue:
			[prev = 0
				ifTrue: [self unlinkFreeChunk: freeChunk atIndex: index isLilliputianSize: true]
				ifFalse: [self setNextFreeChunkOf: prev withValue: next isLilliputianSize: true].
			 ^freeChunk].
		 prev := node.
		 node := next].
	 self error: 'freeChunk not found in lilliputian chunk free list'
	
	

	
]

{ #category : #'free space' }
SpurGenerationalGC >> unlinkSolitaryFreeTreeNode: freeTreeNode [
	"Unlink a freeTreeNode.  Assumes the node has no list (null next link)."
	| parent smaller larger |
	self assert: (self fetchPointer: self freeChunkNextIndex ofFreeChunk: freeTreeNode) = 0.

	"case 1. interior node has one child, P = parent, N = node, S = subtree (mirrored for large vs small)
			___				  ___
			| P |				  | P |
		    _/_				_/_
		    | N |		=>		| S |
		 _/_
		 | S |

	 case 2: interior node has two children, , P = parent, N = node, L = smaller, left subtree, R = larger, right subtree.
	 add the left subtree to the bottom left of the right subtree (mirrored for large vs small) 
			___				  ___
			| P |				  | P |
		    _/_				_/_
		    | N |		=>		| R |
		 _/_  _\_		    _/_
		 | L | | R |		    | L |"

	smaller := self fetchPointer: self freeChunkSmallerIndex ofFreeChunk: freeTreeNode.
	larger := self fetchPointer: self freeChunkLargerIndex ofFreeChunk: freeTreeNode.
	parent := self fetchPointer: self freeChunkParentIndex ofFreeChunk: freeTreeNode.
	parent = 0
		ifTrue: "no parent; stitch the subnodes back into the root"
			[smaller = 0
				ifTrue:
					[larger ~= 0 ifTrue:
						[self storePointer: self freeChunkParentIndex ofFreeChunk: larger withValue: 0].
					 freeLists at: 0 put: larger]
				ifFalse:
					[self storePointer: self freeChunkParentIndex ofFreeChunk: smaller withValue: 0.
					 freeLists at: 0 put: smaller.
					 larger ~= 0 ifTrue:
						[self addFreeSubTree: larger]]]
		ifFalse: "parent; stitch back into appropriate side of parent."
			[smaller = 0
				ifTrue: [self storePointer: (freeTreeNode = (self fetchPointer: self freeChunkSmallerIndex ofFreeChunk: parent)
											ifTrue: [self freeChunkSmallerIndex]
											ifFalse: [self freeChunkLargerIndex])
							ofFreeChunk: parent
							withValue: larger.
						larger ~= 0 ifTrue:
							[self storePointer: self freeChunkParentIndex
								ofFreeChunk: larger
								withValue: parent]]
				ifFalse:
					[self storePointer: (freeTreeNode = (self fetchPointer: self freeChunkSmallerIndex ofFreeChunk: parent)
											ifTrue: [self freeChunkSmallerIndex]
											ifFalse: [self freeChunkLargerIndex])
						ofFreeChunk: parent
						withValue: smaller.
					 self storePointer: self freeChunkParentIndex
						ofFreeChunk: smaller
						withValue: parent.
					 larger ~= 0 ifTrue:
						[self addFreeSubTree: larger]]]
]

{ #category : #accessing }
SpurGenerationalGC >> unscannedEphemeronsQueueInitialSize: anInteger [ 
	
	unscannedEphemeronsQueueInitialSize := anInteger
]

{ #category : #initialization }
SpurGenerationalGC >> updateFreeLists [
	"Snapshot did not guarantee the state of the freelist prevLink, so we need to update it.
	 Effectively transforms the freechunk single linked list in double linked list."
	|min|
	"Small chunks"
	"Skip in 64 bits size 1 which is single linked list - pathological case"
	self wordSize = 8 ifTrue: [min := 3] ifFalse: [min := 2].
	min to: self numFreeLists - 1 do:
		[:i| self updateListStartingAt: (freeLists at: i)].
	"Large chunks"
	self freeTreeNodesDo: [:freeNode |
		self updateListStartingAt: freeNode.
		freeNode]
]

{ #category : #'gc - global' }
SpurGenerationalGC >> updateFullGCStats [	
	"Stats updated (since VM start-up): 
	1) number of full GCs,
	2) time spent in full GC,
	3) time spent in compaction (included in 2)
	4) time spent in sweep phase (included in 2 & 3, 0 if no sweep phase)
	5) time spent in mark phase (included in 2)"
	statFullGCs := statFullGCs + 1.
	statFullGCUsecs := statFullGCUsecs + (statGCEndUsecs - gcStartUsecs).
	statCompactionUsecs := statCompactionUsecs + (statGCEndUsecs - compactionStartUsecs).
	gcSweepEndUsecs = 0 ifFalse: [statSweepUsecs := statSweepUsecs + (gcSweepEndUsecs - compactionStartUsecs)].
	statMarkUsecs := statMarkUsecs + (gcMarkEndUsecs - gcStartUsecs).
]

{ #category : #initialization }
SpurGenerationalGC >> updateListStartingAt: freeNode [ 
	|prev obj|
	freeNode = 0 ifTrue: [^self].
	self deny: (self isLilliputianSize: (self bytesInObject: freeNode)).
	prev := freeNode.
	self storePointer: self freeChunkPrevIndex ofFreeChunk: prev withValue: 0.
	[obj := self fetchPointer: self freeChunkNextIndex ofFreeChunk: prev.
	 obj ~= 0] whileTrue:
		[self storePointer: self freeChunkPrevIndex ofFreeChunk: obj withValue: prev.
		 prev := obj]
]

{ #category : #'obj stacks' }
SpurGenerationalGC >> updateRootOfObjStackAt: objStackRootIndex with: newRootPage [
	objectRepresentation storePointer: objStackRootIndex
		ofObject: objectRepresentation hiddenRootsObject
		withValue: newRootPage.
	objStackRootIndex caseOf: {
		[MarkStackRootIndex]		->	[markStack := newRootPage].
		[WeaklingStackRootIndex]	->	[weaklingStack := newRootPage].
		[MournQueueRootIndex]	->	[mournQueue := newRootPage] }.
	^newRootPage
]

{ #category : #'free space' }
SpurGenerationalGC >> validFreeTree [
	<api>
	^(self validFreeTreeChunk: (freeLists at: 0) parent: 0) isNil
]

{ #category : #'free space' }
SpurGenerationalGC >> validFreeTreeChunk: chunk [
	<inline: false>
	(objectRepresentation segmentManager segmentContainingObj: chunk) ifNil:
		[^false].
	^(self validFreeTreeChunk: chunk parent: (self fetchPointer: self freeChunkParentIndex ofFreeChunk: chunk)) isNil
]

{ #category : #'free space' }
SpurGenerationalGC >> validFreeTreeChunk: chunk parent: parent [
	<var: 'reason' type: #'const char *'>
	<returnTypeC: #'const char *'>
	chunk = 0 ifTrue:
		[^nil].
	(self addressCouldBeOldObj: chunk) ifFalse:
		[^'not in old space'].
	(objectRepresentation bytesInObject: chunk) / objectRepresentation allocationUnit < self numFreeLists ifTrue:
		[^'too small'].
	parent ~= (self fetchPointer: self freeChunkParentIndex ofFreeChunk: chunk) ifTrue:
		[^'bad parent'].

	(objectRepresentation segmentManager segmentContainingObj: chunk) ~~ (objectRepresentation segmentManager segmentContainingObj: (objectRepresentation addressAfter: chunk)) ifTrue:
		[^'not in one segment'].
	(self validFreeTreeChunk: (self fetchPointer: self freeChunkSmallerIndex ofFreeChunk: chunk) parent: chunk) ifNotNil:
		[:reason| ^reason].
	(self validFreeTreeChunk: (self fetchPointer: self freeChunkLargerIndex ofFreeChunk: chunk) parent: chunk) ifNotNil:
		[:reason| ^reason].
	^nil
]

{ #category : #'obj stacks' }
SpurGenerationalGC >> validObjStacks [
	^(markStack = objectRepresentation nilObject or: [objectRepresentation isValidObjStack: markStack])
	  and: [(weaklingStack = objectRepresentation nilObject or: [objectRepresentation isValidObjStack: weaklingStack])
	  and: [mournQueue = objectRepresentation nilObject or: [objectRepresentation isValidObjStack: mournQueue]]]
]

{ #category : #'spur bootstrap' }
SpurGenerationalGC >> weaklingStack [
	^weaklingStack
]

{ #category : #accessing }
SpurGenerationalGC >> weaklingStack: anOop [ 
	<doNotGenerate>
	weaklingStack := anOop
]

{ #category : #'debug support' }
SpurGenerationalGC >> wordSize [
	<doNotGenerate>
	^ memoryManager wordSize
]
