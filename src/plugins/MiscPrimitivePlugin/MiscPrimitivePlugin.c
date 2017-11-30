/* Automatically generated by
	VMPluginCodeGenerator VMMaker.oscog-eem.2285 uuid: 98acc33d-77d9-4edc-8d09-d7853850efd6
   from
	MiscPrimitivePlugin VMMaker.oscog-eem.2285 uuid: 98acc33d-77d9-4edc-8d09-d7853850efd6
	Bitmap Graphics-pre.386 uuid: edc4e679-010f-c24c-b74e-3fe17fbefe4d
	ByteArray Collections-eem.767 uuid: 9705b40c-d81d-4667-b9eb-fbfccbe2e955
	ByteString Collections-eem.767 uuid: 9705b40c-d81d-4667-b9eb-fbfccbe2e955
	SampledSound Sound-pre.64 uuid: 1e82fad7-2c1d-ea42-9b55-cfa86185e99b
 */
static char __buildInfo[] = "MiscPrimitivePlugin VMMaker.oscog-eem.2285 uuid: 98acc33d-77d9-4edc-8d09-d7853850efd6\n\
Bitmap Graphics-pre.386 uuid: edc4e679-010f-c24c-b74e-3fe17fbefe4d\n\
ByteArray Collections-eem.767 uuid: 9705b40c-d81d-4667-b9eb-fbfccbe2e955\n\
ByteString Collections-eem.767 uuid: 9705b40c-d81d-4667-b9eb-fbfccbe2e955\n\
SampledSound Sound-pre.64 uuid: 1e82fad7-2c1d-ea42-9b55-cfa86185e99b " __DATE__ ;



#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

/* Default EXPORT macro that does nothing (see comment in sq.h): */
#define EXPORT(returnType) returnType

/* Do not include the entire sq.h file but just those parts needed. */
#include "sqConfig.h"			/* Configuration options */
#include "sqVirtualMachine.h"	/*  The virtual machine proxy definition */
#include "sqPlatformSpecific.h"	/* Platform specific definitions */

#define true 1
#define false 0
#define null 0  /* using 'null' because nil is predefined in Think C */
#ifdef SQUEAK_BUILTIN_PLUGIN
# undef EXPORT
# define EXPORT(returnType) static returnType
#endif

#include "sqMemoryAccess.h"


/*** Function Prototypes ***/
static sqInt encodeBytesOfinat(sqInt anInt, unsigned char *ba, sqInt i);
static sqInt encodeIntinat(sqInt anInt, unsigned char *ba, sqInt i);
EXPORT(const char*) getModuleName(void);
EXPORT(sqInt) primitiveCompareString(void);
EXPORT(sqInt) primitiveCompressToByteArray(void);
EXPORT(sqInt) primitiveConvert8BitSigned(void);
EXPORT(sqInt) primitiveDecompressFromByteArray(void);
EXPORT(sqInt) primitiveFindFirstInString(void);
EXPORT(sqInt) primitiveFindSubstring(void);
EXPORT(sqInt) primitiveIndexOfAsciiInString(void);
EXPORT(sqInt) primitiveStringHash(void);
EXPORT(sqInt) primitiveTranslateStringWithTable(void);
EXPORT(sqInt) setInterpreter(struct VirtualMachine*anInterpreter);


/*** Variables ***/

#if !defined(SQUEAK_BUILTIN_PLUGIN)
static void * (*arrayValueOf)(sqInt oop);
static sqInt (*failed)(void);
static sqInt (*isBytes)(sqInt oop);
static sqInt (*pop)(sqInt nItems);
static sqInt (*primitiveFail)(void);
static sqInt (*pushInteger)(sqInt integerValue);
static sqInt (*sizeOfSTArrayFromCPrimitive)(void *cPtr);
static sqInt (*stackIntegerValue)(sqInt offset);
static sqInt (*stackValue)(sqInt offset);
#else /* !defined(SQUEAK_BUILTIN_PLUGIN) */
extern void * arrayValueOf(sqInt oop);
extern sqInt failed(void);
extern sqInt isBytes(sqInt oop);
extern sqInt pop(sqInt nItems);
extern sqInt primitiveFail(void);
extern sqInt pushInteger(sqInt integerValue);
extern sqInt sizeOfSTArrayFromCPrimitive(void *cPtr);
extern sqInt stackIntegerValue(sqInt offset);
extern sqInt stackValue(sqInt offset);
extern
#endif
struct VirtualMachine* interpreterProxy;
static const char *moduleName =
#ifdef SQUEAK_BUILTIN_PLUGIN
	"MiscPrimitivePlugin VMMaker.oscog-eem.2285 (i)"
#else
	"MiscPrimitivePlugin VMMaker.oscog-eem.2285 (e)"
#endif
;


/*** Macros ***/
#define asciiValue(aCharacter) aCharacter



/*	Copy the integer anInt into byteArray ba at index i, and return the next
	index 
 */

	/* Bitmap>>#encodeBytesOf:in:at: */
static sqInt
encodeBytesOfinat(sqInt anInt, unsigned char *ba, sqInt i)
{
    sqInt j;

	for (j = 0; j <= 3; j += 1) {
		ba[i + j] = ((((usqInt) anInt) >> ((3 - j) * 8)) & 0xFF);
	}
	return i + 4;
}


/*	Encode the integer anInt in byteArray ba at index i, and return the next
	index. The encoding is as follows...
	0-223	0-223
	224-254	(0-30)*256 + next byte (0-7935)
	255		next 4 bytes */

	/* Bitmap>>#encodeInt:in:at: */
static sqInt
encodeIntinat(sqInt anInt, unsigned char *ba, sqInt i)
{
    sqInt j;

	if (anInt <= 223) {
		ba[i] = anInt;
		return i + 1;
	}
	if (anInt <= 7935) {
		ba[i] = ((anInt / 256) + 224);
		ba[i + 1] = (anInt % 256);
		return i + 2;
	}
	ba[i] = 0xFF;
	/* begin encodeBytesOf:in:at: */
	for (j = 0; j <= 3; j += 1) {
		ba[(i + 1) + j] = ((((usqInt) anInt) >> ((3 - j) * 8)) & 0xFF);
	}
	return (i + 1) + 4;
}


/*	Note: This is hardcoded so it can be run from Squeak.
	The module name is used for validating a module *after*
	it is loaded to check if it does really contain the module
	we're thinking it contains. This is important! */

	/* InterpreterPlugin>>#getModuleName */
EXPORT(const char*)
getModuleName(void)
{
	return moduleName;
}


/*	Return 1, 2 or 3, if string1 is <, =, or > string2, with the collating
	order of characters given by the order array.
 */

	/* ByteString class>>#primitiveCompareString */
EXPORT(sqInt)
primitiveCompareString(void)
{
    unsigned char c1;
    unsigned char c2;
    sqInt i;
    sqInt len1;
    sqInt len2;
    unsigned char *order;
    sqInt rcvr;
    unsigned char *string1;
    unsigned char *string2;

	rcvr = stackValue(3);
	if (!(isBytes(stackValue(2)))) {
		return primitiveFail();
	}
	string1 = arrayValueOf(stackValue(2));
	string1 -= 1;
	if (!(isBytes(stackValue(1)))) {
		return primitiveFail();
	}
	string2 = arrayValueOf(stackValue(1));
	string2 -= 1;
	if (!(isBytes(stackValue(0)))) {
		return primitiveFail();
	}
	order = arrayValueOf(stackValue(0));
	order -= 1;
	if (failed()) {
		return null;
	}
	len1 = sizeOfSTArrayFromCPrimitive(string1 + 1);
	len2 = sizeOfSTArrayFromCPrimitive(string2 + 1);
	for (i = 1; i <= (((len1 < len2) ? len1 : len2)); i += 1) {
		c1 = order[(string1[i]) + 1];
		c2 = order[(string2[i]) + 1];
		if (!(c1 == c2)) {
			if (c1 < c2) {
				if (failed()) {
					return null;
				}
				pop(4);
				pushInteger(1);
				return null;
			}
			else {
				if (failed()) {
					return null;
				}
				pop(4);
				pushInteger(3);
				return null;
			}
		}
	}
	if (len1 == len2) {
		if (failed()) {
			return null;
		}
		pop(4);
		pushInteger(2);
		return null;
	}
	if (len1 < len2) {
		if (failed()) {
			return null;
		}
		pop(4);
		pushInteger(1);
		return null;
	}
	else {
		if (failed()) {
			return null;
		}
		pop(4);
		pushInteger(3);
		return null;
	}
}


/*	Store a run-coded compression of the receiver into the byteArray ba,
	and return the last index stored into. ba is assumed to be large enough.
	The encoding is as follows...
	S {N D}*.
	S is the size of the original bitmap, followed by run-coded pairs.
	N is a run-length * 4 + data code.
	D, the data, depends on the data code...
	0	skip N words, D is absent
	1	N words with all 4 bytes = D (1 byte)
	2	N words all = D (4 bytes)
	3	N words follow in D (4N bytes)
	S and N are encoded as follows...
	0-223	0-223
	224-254	(0-30)*256 + next byte (0-7935)
	255		next 4 bytes */

	/* Bitmap>>#primitiveCompressToByteArray */
EXPORT(sqInt)
primitiveCompressToByteArray(void)
{
    unsigned char *ba;
    int *bm;
    sqInt eqBytes;
    sqInt i;
    sqInt j;
    sqInt j1;
    sqInt j2;
    sqInt j3;
    sqInt j4;
    sqInt j5;
    sqInt j6;
    sqInt j7;
    sqInt k;
    int lowByte;
    sqInt m;
    sqInt rcvr;
    sqInt size;
    int word;

	rcvr = stackValue(2);
	bm = arrayValueOf(stackValue(1));
	bm -= 1;
	if (!(isBytes(stackValue(0)))) {
		return primitiveFail();
	}
	ba = arrayValueOf(stackValue(0));
	ba -= 1;
	if (failed()) {
		return null;
	}
	size = sizeOfSTArrayFromCPrimitive(bm + 1);
	/* begin encodeInt:in:at: */
	if (size <= 223) {
		ba[1] = size;
		i = 1 + 1;
		goto l7;
	}
	if (size <= 7935) {
		ba[1] = ((size / 256) + 224);
		ba[1 + 1] = (size % 256);
		i = 1 + 2;
		goto l7;
	}
	ba[1] = 0xFF;
	/* begin encodeBytesOf:in:at: */
	for (j7 = 0; j7 <= 3; j7 += 1) {
		ba[(1 + 1) + j7] = ((((usqInt) size) >> ((3 - j7) * 8)) & 0xFF);
	}
	i = (1 + 1) + 4;
l7:	/* end encodeInt:in:at: */;
	k = 1;
	while (k <= size) {
		word = bm[k];
		lowByte = word & 0xFF;
		eqBytes = (((((usqInt) word) >> 8) & 0xFF) == lowByte)
		 && ((((((usqInt) word) >> 16) & 0xFF) == lowByte)
		 && (((((usqInt) word) >> 24) & 0xFF) == lowByte));
		j = k;
		while ((j < size)
		 && (word == (bm[j + 1]))) {
			j += 1;
		}
		if (j > k) {

			/* We have two or more = words, ending at j */
			if (eqBytes) {

				/* Actually words of = bytes */
				/* begin encodeInt:in:at: */
				if (((((j - k) + 1) * 4) + 1) <= 223) {
					ba[i] = ((((j - k) + 1) * 4) + 1);
					i += 1;
					goto l1;
				}
				if (((((j - k) + 1) * 4) + 1) <= 7935) {
					ba[i] = ((((((j - k) + 1) * 4) + 1) / 256) + 224);
					ba[i + 1] = (((((j - k) + 1) * 4) + 1) % 256);
					i += 2;
					goto l1;
				}
				ba[i] = 0xFF;
				/* begin encodeBytesOf:in:at: */
				for (j1 = 0; j1 <= 3; j1 += 1) {
					ba[(i + 1) + j1] = ((((usqInt) ((((j - k) + 1) * 4) + 1)) >> ((3 - j1) * 8)) & 0xFF);
				}
				i = (i + 1) + 4;
			l1:	/* end encodeInt:in:at: */;
				ba[i] = lowByte;
				i += 1;
			}
			else {
				/* begin encodeInt:in:at: */
				if (((((j - k) + 1) * 4) + 2) <= 223) {
					ba[i] = ((((j - k) + 1) * 4) + 2);
					i += 1;
					goto l2;
				}
				if (((((j - k) + 1) * 4) + 2) <= 7935) {
					ba[i] = ((((((j - k) + 1) * 4) + 2) / 256) + 224);
					ba[i + 1] = (((((j - k) + 1) * 4) + 2) % 256);
					i += 2;
					goto l2;
				}
				ba[i] = 0xFF;
				/* begin encodeBytesOf:in:at: */
				for (j2 = 0; j2 <= 3; j2 += 1) {
					ba[(i + 1) + j2] = ((((usqInt) ((((j - k) + 1) * 4) + 2)) >> ((3 - j2) * 8)) & 0xFF);
				}
				i = (i + 1) + 4;
			l2:	/* end encodeInt:in:at: */;
				/* begin encodeBytesOf:in:at: */
				for (j3 = 0; j3 <= 3; j3 += 1) {
					ba[i + j3] = ((((usqInt) word) >> ((3 - j3) * 8)) & 0xFF);
				}
				i += 4;
			}
			k = j + 1;
		}
		else {

			/* Check for word of 4 = bytes */
			if (eqBytes) {

				/* Note 1 word of 4 = bytes */
				/* begin encodeInt:in:at: */
				if (((1 * 4) + 1) <= 223) {
					ba[i] = ((1 * 4) + 1);
					i += 1;
					goto l4;
				}
				if (((1 * 4) + 1) <= 7935) {
					ba[i] = ((((1 * 4) + 1) / 256) + 224);
					ba[i + 1] = (((1 * 4) + 1) % 256);
					i += 2;
					goto l4;
				}
				ba[i] = 0xFF;
				/* begin encodeBytesOf:in:at: */
				for (j4 = 0; j4 <= 3; j4 += 1) {
					ba[(i + 1) + j4] = ((((usqInt) ((1 * 4) + 1)) >> ((3 - j4) * 8)) & 0xFF);
				}
				i = (i + 1) + 4;
			l4:	/* end encodeInt:in:at: */;
				ba[i] = lowByte;
				i += 1;
				k += 1;
			}
			else {

				/* Finally, check for junk */
				while ((j < size)
				 && ((bm[j]) != (bm[j + 1]))) {
					j += 1;
				}
				if (j == size) {
					j += 1;
				}
				/* begin encodeInt:in:at: */
				if ((((j - k) * 4) + 3) <= 223) {
					ba[i] = (((j - k) * 4) + 3);
					i += 1;
					goto l6;
				}
				if ((((j - k) * 4) + 3) <= 7935) {
					ba[i] = (((((j - k) * 4) + 3) / 256) + 224);
					ba[i + 1] = ((((j - k) * 4) + 3) % 256);
					i += 2;
					goto l6;
				}
				ba[i] = 0xFF;
				/* begin encodeBytesOf:in:at: */
				for (j6 = 0; j6 <= 3; j6 += 1) {
					ba[(i + 1) + j6] = ((((usqInt) (((j - k) * 4) + 3)) >> ((3 - j6) * 8)) & 0xFF);
				}
				i = (i + 1) + 4;
			l6:	/* end encodeInt:in:at: */;
				for (m = k; m < j; m += 1) {
					/* begin encodeBytesOf:in:at: */
					for (j5 = 0; j5 <= 3; j5 += 1) {
						ba[i + j5] = ((((usqInt) (bm[m])) >> ((3 - j5) * 8)) & 0xFF);
					}
					i += 4;
				}
				k = j;
			}
		}
	}
	if (failed()) {
		return null;
	}
	pop(3);
	pushInteger(i - 1);
	return null;
}


/*	Copy the contents of the given array of signed 8-bit samples into the
	given array of 16-bit signed samples.
 */

	/* SampledSound class>>#primitiveConvert8BitSigned */
EXPORT(sqInt)
primitiveConvert8BitSigned(void)
{
    unsigned char *aByteArray;
    unsigned short *aSoundBuffer;
    sqInt i;
    sqInt n;
    sqInt rcvr;
    unsigned char s;

	rcvr = stackValue(2);
	if (!(isBytes(stackValue(1)))) {
		return primitiveFail();
	}
	aByteArray = arrayValueOf(stackValue(1));
	aByteArray -= 1;
	aSoundBuffer = arrayValueOf(stackValue(0));
	aSoundBuffer -= 1;
	if (failed()) {
		return null;
	}
	n = sizeOfSTArrayFromCPrimitive(aByteArray + 1);
	for (i = 1; i <= n; i += 1) {
		s = aByteArray[i];
		if (s > 0x7F) {
			aSoundBuffer[i] = (((usqInt) (s - 256) << 8));
		}
		else {
			aSoundBuffer[i] = (((usqInt) s << 8));
		}
	}
	if (failed()) {
		return null;
	}
	pop(2);
	return 0;
}


/*	Decompress the body of a byteArray encoded by compressToByteArray (qv)...
	The format is simply a sequence of run-coded pairs, {N D}*.
	N is a run-length * 4 + data code.
	D, the data, depends on the data code...
	0	skip N words, D is absent
	(could be used to skip from one raster line to the next)
	1	N words with all 4 bytes = D (1 byte)
	2	N words all = D (4 bytes)
	3	N words follow in D (4N bytes)
	S and N are encoded as follows (see decodeIntFrom:)...
	0-223	0-223
	224-254	(0-30)*256 + next byte (0-7935)
	255		next 4 bytes */
/*	NOTE: If fed with garbage, this routine could read past the end of ba, but
	it should fail before writing past the ned of bm. */

	/* Bitmap>>#primitiveDecompressFromByteArray */
EXPORT(sqInt)
primitiveDecompressFromByteArray(void)
{
    unsigned int anInt;
    unsigned char *ba;
    int *bm;
    unsigned int code;
    unsigned int data;
    sqInt end;
    sqInt i;
    sqInt index;
    sqInt j;
    sqInt k;
    sqInt m;
    unsigned int n;
    sqInt pastEnd;
    sqInt rcvr;


	/* Force the type, otherwise it is inferred as unsigned char because assigned from ba */
	rcvr = stackValue(3);
	bm = arrayValueOf(stackValue(2));
	bm -= 1;
	if (!(isBytes(stackValue(1)))) {
		return primitiveFail();
	}
	ba = arrayValueOf(stackValue(1));
	ba -= 1;
	index = stackIntegerValue(0);
	if (failed()) {
		return null;
	}

	/* byteArray read index */
	i = index;
	end = sizeOfSTArrayFromCPrimitive(ba + 1);

	/* bitmap write index */
	k = 1;
	pastEnd = (sizeOfSTArrayFromCPrimitive(bm + 1)) + 1;
	while (i <= end) {

		/* Decode next run start N */
		anInt = ba[i];
		i += 1;
		if (!(anInt <= 223)) {
			if (anInt <= 0xFE) {
				anInt = ((anInt - 224) * 256) + (ba[i]);
				i += 1;
			}
			else {
				anInt = 0;
				for (j = 1; j <= 4; j += 1) {
					anInt = (((usqInt) anInt << 8)) + (ba[i]);
					i += 1;
				}
			}
		}
		n = ((usqInt) anInt) >> 2;
		if ((k + n) > pastEnd) {
			primitiveFail();
			return null;
		}
		code = anInt & 3;
		if (code == 0) {

			/* skip */
		}
		if (code == 1) {

			/* n consecutive words of 4 bytes = the following byte */
			data = ba[i];
			i += 1;
			data = data | (((usqInt) data << 8));
			data = data | (((usqInt) data << 16));
			for (j = 1; j <= n; j += 1) {
				bm[k] = data;
				k += 1;
			}
		}
		if (code == 2) {

			/* n consecutive words = 4 following bytes */
			data = 0;
			for (j = 1; j <= 4; j += 1) {
				data = (((usqInt) data << 8)) | (ba[i]);
				i += 1;
			}
			for (j = 1; j <= n; j += 1) {
				bm[k] = data;
				k += 1;
			}
		}
		if (code == 3) {

			/* n consecutive words from the data... */
			for (m = 1; m <= n; m += 1) {
				data = 0;
				for (j = 1; j <= 4; j += 1) {
					data = (((usqInt) data << 8)) | (ba[i]);
					i += 1;
				}
				bm[k] = data;
				k += 1;
			}
		}
	}
	if (failed()) {
		return null;
	}
	pop(3);
	return 0;
}

	/* ByteString class>>#primitiveFindFirstInString */
EXPORT(sqInt)
primitiveFindFirstInString(void)
{
    unsigned char *aString;
    sqInt i;
    char *inclusionMap;
    sqInt rcvr;
    sqInt start;
    sqInt stringSize;

	rcvr = stackValue(3);
	if (!(isBytes(stackValue(2)))) {
		return primitiveFail();
	}
	aString = arrayValueOf(stackValue(2));
	aString -= 1;
	if (!(isBytes(stackValue(1)))) {
		return primitiveFail();
	}
	inclusionMap = arrayValueOf(stackValue(1));
	inclusionMap -= 1;
	start = stackIntegerValue(0);
	if (failed()) {
		return null;
	}
	if ((sizeOfSTArrayFromCPrimitive(inclusionMap + 1)) != 256) {
		if (failed()) {
			return null;
		}
		pop(4);
		pushInteger(0);
		return null;
	}
	i = start;
	stringSize = sizeOfSTArrayFromCPrimitive(aString + 1);
	while ((i <= stringSize)
	 && ((inclusionMap[(aString[i]) + 1]) == 0)) {
		i += 1;
	}
	if (i > stringSize) {
		if (failed()) {
			return null;
		}
		pop(4);
		pushInteger(0);
		return null;
	}
	if (failed()) {
		return null;
	}
	pop(4);
	pushInteger(i);
	return null;
}


/*	Answer the index in the string body at which the substring key first
	occurs, at or beyond start. The match is determined using matchTable,
	which can be used to effect, eg, case-insensitive matches. If no match is
	found, zero will be returned.
	
	The algorithm below is not optimum -- it is intended to be translated to C
	which will go so fast that it wont matter.
 */

	/* ByteString>>#primitiveFindSubstring */
EXPORT(sqInt)
primitiveFindSubstring(void)
{
    unsigned char *body;
    sqInt index;
    unsigned char *key;
    unsigned char *matchTable;
    sqInt rcvr;
    sqInt start;
    sqInt startIndex;
    sqInt startIndexLimiT;

	rcvr = stackValue(4);
	if (!(isBytes(stackValue(3)))) {
		return primitiveFail();
	}
	key = arrayValueOf(stackValue(3));
	key -= 1;
	if (!(isBytes(stackValue(2)))) {
		return primitiveFail();
	}
	body = arrayValueOf(stackValue(2));
	body -= 1;
	start = stackIntegerValue(1);
	if (!(isBytes(stackValue(0)))) {
		return primitiveFail();
	}
	matchTable = arrayValueOf(stackValue(0));
	matchTable -= 1;
	if (failed()) {
		return null;
	}
	if ((sizeOfSTArrayFromCPrimitive(key + 1)) == 0) {
		if (failed()) {
			return null;
		}
		pop(5);
		pushInteger(0);
		return null;
	}
	for (startIndex = (((start < 1) ? 1 : start)), startIndexLimiT = (((sizeOfSTArrayFromCPrimitive(body + 1)) - (sizeOfSTArrayFromCPrimitive(key + 1))) + 1); startIndex <= startIndexLimiT; startIndex += 1) {
		index = 1;
		while ((matchTable[(body[(startIndex + index) - 1]) + 1]) == (matchTable[(key[index]) + 1])) {
			if (index == (sizeOfSTArrayFromCPrimitive(key + 1))) {
				if (failed()) {
					return null;
				}
				pop(5);
				pushInteger(startIndex);
				return null;
			}
			index += 1;
		}
	}
	if (failed()) {
		return null;
	}
	pop(5);
	pushInteger(0);
	return null;
}

	/* ByteString class>>#primitiveIndexOfAsciiInString */
EXPORT(sqInt)
primitiveIndexOfAsciiInString(void)
{
    sqInt anInteger;
    unsigned char *aString;
    sqInt pos;
    sqInt rcvr;
    sqInt start;
    sqInt stringSize;

	rcvr = stackValue(3);
	anInteger = stackIntegerValue(2);
	if (!(isBytes(stackValue(1)))) {
		return primitiveFail();
	}
	aString = arrayValueOf(stackValue(1));
	aString -= 1;
	start = stackIntegerValue(0);
	if (failed()) {
		return null;
	}
	stringSize = sizeOfSTArrayFromCPrimitive(aString + 1);
	for (pos = start; pos <= stringSize; pos += 1) {
		if ((aString[pos]) == anInteger) {
			if (failed()) {
				return null;
			}
			pop(4);
			pushInteger(pos);
			return null;
		}
	}
	if (failed()) {
		return null;
	}
	pop(4);
	pushInteger(0);
	return null;
}


/*	Answer the hash of a byte-indexed collection, using speciesHash as the
	initial value.
	See SmallInteger>>hashMultiply.
	
	The primitive should be renamed at a suitable point in the future */

	/* ByteArray class>>#primitiveStringHash */
EXPORT(sqInt)
primitiveStringHash(void)
{
    unsigned char *aByteArray;
    sqInt byteArraySize;
    int hash;
    sqInt pos;
    sqInt rcvr;
    int speciesHash;

	rcvr = stackValue(2);
	if (!(isBytes(stackValue(1)))) {
		return primitiveFail();
	}
	aByteArray = arrayValueOf(stackValue(1));
	aByteArray -= 1;
	speciesHash = stackIntegerValue(0);
	if (failed()) {
		return null;
	}
	byteArraySize = sizeOfSTArrayFromCPrimitive(aByteArray + 1);
	hash = speciesHash & 0xFFFFFFF;
	for (pos = 1; pos <= byteArraySize; pos += 1) {

		/* Inlined hashMultiply, written this way for translation to C. */
		hash += aByteArray[pos];
		hash = (hash * 1664525) & 0xFFFFFFF;
	}
	if (failed()) {
		return null;
	}
	pop(3);
	pushInteger(hash);
	return null;
}


/*	translate the characters in the string by the given table, in place */

	/* ByteString class>>#primitiveTranslateStringWithTable */
EXPORT(sqInt)
primitiveTranslateStringWithTable(void)
{
    unsigned char *aString;
    sqInt i;
    sqInt rcvr;
    sqInt start;
    sqInt stop;
    unsigned char *table;

	rcvr = stackValue(4);
	if (!(isBytes(stackValue(3)))) {
		return primitiveFail();
	}
	aString = arrayValueOf(stackValue(3));
	aString -= 1;
	start = stackIntegerValue(2);
	stop = stackIntegerValue(1);
	if (!(isBytes(stackValue(0)))) {
		return primitiveFail();
	}
	table = arrayValueOf(stackValue(0));
	table -= 1;
	if (failed()) {
		return null;
	}
	for (i = start; i <= stop; i += 1) {
		aString[i] = (table[(aString[i]) + 1]);
	}
	if (failed()) {
		return null;
	}
	pop(4);
	return 0;
}


/*	Note: This is coded so that it can be run in Squeak. */

	/* InterpreterPlugin>>#setInterpreter: */
EXPORT(sqInt)
setInterpreter(struct VirtualMachine*anInterpreter)
{
    sqInt ok;

	interpreterProxy = anInterpreter;
	ok = ((interpreterProxy->majorVersion()) == (VM_PROXY_MAJOR))
	 && ((interpreterProxy->minorVersion()) >= (VM_PROXY_MINOR));
	if (ok) {
		
#if !defined(SQUEAK_BUILTIN_PLUGIN)
		arrayValueOf = interpreterProxy->arrayValueOf;
		failed = interpreterProxy->failed;
		isBytes = interpreterProxy->isBytes;
		pop = interpreterProxy->pop;
		primitiveFail = interpreterProxy->primitiveFail;
		pushInteger = interpreterProxy->pushInteger;
		sizeOfSTArrayFromCPrimitive = interpreterProxy->sizeOfSTArrayFromCPrimitive;
		stackIntegerValue = interpreterProxy->stackIntegerValue;
		stackValue = interpreterProxy->stackValue;
#endif /* !defined(SQUEAK_BUILTIN_PLUGIN) */
	}
	return ok;
}


#ifdef SQUEAK_BUILTIN_PLUGIN

static char _m[] = "MiscPrimitivePlugin";
void* MiscPrimitivePlugin_exports[][3] = {
	{(void*)_m, "getModuleName", (void*)getModuleName},
	{(void*)_m, "primitiveCompareString\000\000", (void*)primitiveCompareString},
	{(void*)_m, "primitiveCompressToByteArray\000\000", (void*)primitiveCompressToByteArray},
	{(void*)_m, "primitiveConvert8BitSigned\000\000", (void*)primitiveConvert8BitSigned},
	{(void*)_m, "primitiveDecompressFromByteArray\000\001", (void*)primitiveDecompressFromByteArray},
	{(void*)_m, "primitiveFindFirstInString\000\000", (void*)primitiveFindFirstInString},
	{(void*)_m, "primitiveFindSubstring\000\000", (void*)primitiveFindSubstring},
	{(void*)_m, "primitiveIndexOfAsciiInString\000\000", (void*)primitiveIndexOfAsciiInString},
	{(void*)_m, "primitiveStringHash\000\000", (void*)primitiveStringHash},
	{(void*)_m, "primitiveTranslateStringWithTable\000\000", (void*)primitiveTranslateStringWithTable},
	{(void*)_m, "setInterpreter", (void*)setInterpreter},
	{NULL, NULL, NULL}
};

#else /* ifdef SQ_BUILTIN_PLUGIN */

signed char primitiveCompareStringAccessorDepth = 0;
signed char primitiveCompressToByteArrayAccessorDepth = 0;
signed char primitiveConvert8BitSignedAccessorDepth = 0;
signed char primitiveDecompressFromByteArrayAccessorDepth = 1;
signed char primitiveFindFirstInStringAccessorDepth = 0;
signed char primitiveFindSubstringAccessorDepth = 0;
signed char primitiveIndexOfAsciiInStringAccessorDepth = 0;
signed char primitiveStringHashAccessorDepth = 0;
signed char primitiveTranslateStringWithTableAccessorDepth = 0;

#endif /* ifdef SQ_BUILTIN_PLUGIN */
