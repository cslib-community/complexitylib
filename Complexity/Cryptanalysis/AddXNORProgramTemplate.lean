/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Cryptanalysis.AddXNORNativeOutputResources
public import Complexity.Computability.WordRAM.ProgramLiterals
public import Complexity.Computability.WordRAM.ProgramLiterals.Expressions
import all Complexity.Cryptanalysis.AddXNORNativeOutputResources
import all Complexity.Cryptanalysis.AddXNORNativeOutput
import all Complexity.Cryptanalysis.AddXNORNativeGlobalLayout
import all Complexity.Computability.WordRAM.ProgramLiterals
import all Complexity.Computability.WordRAM.ProgramLiterals.Expressions

/-!
# Runtime metadata and the exact native dissection literal template

Widths and quarter lengths are unary metadata; endpoints are binary words.
A fixed expression template generates every immediate in assembler order.
The template is checked against the actual reviewed native code, rather than
postulated as an executable or semantic compiler contract. The instruction graph
is independent of metadata; only its computed scalar constants change.

This is a uniform program-generation component toward the bit model of
[WangLvShenZhang2027], PDF p. 6 and Lemma 8/Theorem 7, pp. 21–22. It does not
supply the source's sharp sorted-list time/space bounds.
-/

public section

namespace Cslib.Cryptanalysis.AddXNOR.ProgramTemplate

open Cslib.WordRAM Cslib.WordRAM.ProgramLiterals Native.Driver

/-- Six unary parameters `m,p,a,b,c,d` and two binary endpoints `s,t`. -/
abbrev Metadata := Input 6 2

/-- The ordinary native code computed from metadata, with endpoints reduced to `m` bits. -/
def nativeCode (h : Metadata) : Code .standard 40 :=
  dissectionOutput (compactSearchLayout (h.1 0) (h.1 1) (h.1 2) (h.1 3) (h.1 4) (h.1 5))
    (compactCounterLayout (h.1 0) (h.1 1) (h.1 2) (h.1 3) (h.1 4) (h.1 5))
    (BitVec.ofNat (h.1 0) (h.2 0)) (BitVec.ofNat (h.1 0) (h.2 1))

-- Shared layout expressions keep the fixed literal table inspectable. The universal
-- `literals_exact` proof rejects any drift from the native program definitions.
private def classModulus : Expr 6 2 := (.powTwo (.parameter 1))
private def prefixLength : Expr 6 2 := (.add (.unary (.parameter 2)) (.unary (.parameter 3)))
private def prefixThirdLength : Expr 6 2 := (.add prefixLength (.unary (.parameter 4)))
private def operandLength : Expr 6 2 := (.add prefixThirdLength (.unary (.parameter 5)))
private def projectionStart : Expr 6 2 := (.add (.literal 1) operandLength)
private def counterStart : Expr 6 2 := (.add projectionStart prefixLength)
private def firstTableEnd : Expr 6 2 := (.add counterStart classModulus)
private def fullModulus : Expr 6 2 := (.powTwo (.parameter 0))
private def startWord : Expr 6 2 := (.mod (.parameter 0) fullModulus)
private def projectedStart : Expr 6 2 := (.mod startWord classModulus)
private def twoClasses : Expr 6 2 := (.mul (.literal 2) classModulus)
private def reversedProjectionStart : Expr 6 2 := (.add counterStart twoClasses)
private def suffixLength : Expr 6 2 := (.add (.unary (.parameter 4)) (.unary (.parameter 5)))
private def secondBase : Expr 6 2 := (.add (.literal 1) (.unary (.parameter 2)))
private def fourthBase : Expr 6 2 := (.add secondBase (.unary (.parameter 3)))
private def backwardCounterStart : Expr 6 2 := (.add reversedProjectionStart suffixLength)
private def backwardTableEnd : Expr 6 2 := (.add backwardCounterStart classModulus)
private def fullMask : Expr 6 2 := (.sub fullModulus (.literal 1))
private def targetWord : Expr 6 2 := (.mod (.parameter 1) fullModulus)
private def complementedTarget : Expr 6 2 := (.sub fullMask targetWord)
private def projectedInverseStart : Expr 6 2 := (.mod complementedTarget classModulus)
private def doubleOperandLength : Expr 6 2 := (.mul (.literal 2) operandLength)
private def scratchOffset : Expr 6 2 := (.add (.literal 1) doubleOperandLength)
private def fourClasses : Expr 6 2 := (.mul (.literal 4) classModulus)
private def middleProjectionStart : Expr 6 2 := (.add scratchOffset fourClasses)
private def thirdProjectionOffset : Expr 6 2 :=
  (.add middleProjectionStart (.unary (.parameter 3)))
private def thirdProjectionStart : Expr 6 2 :=
  (.add thirdProjectionOffset (.unary (.parameter 4)))
private def thirdBase : Expr 6 2 := (.add fourthBase (.unary (.parameter 5)))
private def headOffset : Expr 6 2 := (.add thirdProjectionStart (.unary (.parameter 3)))
private def headBase : Expr 6 2 := (.add headOffset (.unary (.parameter 4)))
private def firstArena : Expr 6 2 := (.add headBase classModulus)
private def firstQuarterCount : Expr 6 2 := (.powTwo (.parameter 2))
private def fourthQuarterCount : Expr 6 2 := (.powTwo (.parameter 5))
private def quarterCountSum : Expr 6 2 := (.add firstQuarterCount fourthQuarterCount)
private def arenaSpan : Expr 6 2 := (.mul (.literal 3) quarterCountSum)
private def inverseHeads : Expr 6 2 := (.add firstArena arenaSpan)
private def inverseArena : Expr 6 2 := (.add inverseHeads classModulus)
private def dictionaryBase : Expr 6 2 := (.add inverseArena arenaSpan)
private def complementedStart : Expr 6 2 := (.sub fullMask startWord)
private def positiveOne : Expr 6 2 := (.add (.literal 0) (.literal 1))
private def statusAddress : Expr 6 2 := (.add dictionaryBase (.literal 1))
private def hitPayloadLength : Expr 6 2 := (.add operandLength (.literal 1))
private def payloadAddressViaSuccessor : Expr 6 2 := (.add statusAddress (.literal 1))
private def payloadAddress : Expr 6 2 := (.add dictionaryBase (.literal 2))
private def afterFirstField : Expr 6 2 := (.add payloadAddress (.unary (.parameter 2)))
private def afterSecondField : Expr 6 2 := (.add afterFirstField (.unary (.parameter 3)))
private def afterThirdField : Expr 6 2 := (.add afterSecondField (.unary (.parameter 4)))
private def reverseFirstOrigin : Expr 6 2 := (.sub afterFirstField (.literal 0))
private def reverseFirstCursor : Expr 6 2 := (.sub reverseFirstOrigin (.literal 1))
private def reverseSecondOrigin : Expr 6 2 := (.sub afterSecondField (.literal 0))
private def reverseSecondCursor : Expr 6 2 := (.sub reverseSecondOrigin (.literal 1))
private def reverseThirdOrigin : Expr 6 2 := (.sub afterThirdField (.literal 0))
private def reverseThirdCursor : Expr 6 2 := (.sub reverseThirdOrigin (.literal 1))
private def afterAllFields : Expr 6 2 := (.add afterThirdField (.unary (.parameter 5)))
private def reverseFourthOrigin : Expr 6 2 := (.sub afterAllFields (.literal 0))
private def reverseFourthCursor : Expr 6 2 := (.sub reverseFourthOrigin (.literal 1))

/-- Fixed literal-expression template in the native assembler's instruction order. -/
def literalTemplate : List (Expr 6 2) :=
  [classModulus, projectionStart, prefixLength, (.literal 0), (.literal 1), (.literal 1),
    counterStart, firstTableEnd, classModulus, projectionStart, counterStart, projectedStart,
    (.literal 1),
    (.literal 0), (.literal 0), (.literal 1), (.literal 1), classModulus,
    reversedProjectionStart, suffixLength, (.literal 0),
    (.literal 1), fourthBase, backwardCounterStart, backwardTableEnd, classModulus,
    reversedProjectionStart, backwardCounterStart, projectedInverseStart, (.literal 1),
    (.literal 0), (.literal 0),
    (.literal 1), (.literal 1), classModulus, (.literal 0), (.literal 1), (.literal 0),
    (.literal 0),
    (.unary (.parameter 1)), (.literal 1), (.literal 0), (.literal 0), (.literal 1),
    (.literal 0), classModulus, middleProjectionStart, (.unary (.parameter 3)), (.literal 0),
    (.literal 1), secondBase, classModulus, thirdProjectionStart,
    (.unary (.parameter 4)), (.literal 0), (.literal 1), thirdBase, (.literal 1),
    (.unary (.parameter 2)), fullModulus, startWord, headBase, firstArena, classModulus,
    (.literal 1), (.literal 0), (.literal 0),
    (.literal 0), (.literal 1), (.literal 2), fourthBase, (.unary (.parameter 5)), fullModulus,
    targetWord, inverseHeads, inverseArena,
    classModulus, (.literal 1), (.literal 0), (.literal 0), (.literal 0), (.literal 0),
    (.literal 1),
    (.literal 2), (.literal 1), (.literal 0), (.literal 1), (.literal 2), (.literal 1),
    secondBase,
    middleProjectionStart, (.unary (.parameter 3)), fullModulus, classModulus, headBase,
    dictionaryBase, (.literal 0), (.literal 0), (.literal 1),
    (.literal 0), (.literal 0), (.literal 0), (.literal 1), (.literal 2), (.literal 1),
    (.literal 0), (.literal 1), (.literal 2), (.literal 1), (.literal 0), (.literal 1),
    (.literal 2), (.literal 1), (.literal 3), (.literal 0), thirdBase, thirdProjectionStart,
    (.unary (.parameter 4)),
    fullModulus, classModulus, inverseHeads, dictionaryBase, (.literal 1), (.literal 0),
    (.literal 0), (.literal 0), (.literal 1),
    (.literal 0), (.literal 1), (.literal 2), (.literal 0), (.literal 0), (.literal 0),
    (.literal 1), (.literal 2), (.literal 1), (.literal 0), (.literal 1), (.literal 2),
    (.literal 1), (.literal 3), (.literal 1), (.literal 3), (.literal 0), (.literal 1),
    classModulus, middleProjectionStart,
    (.unary (.parameter 4)), (.literal 0), (.literal 1), thirdBase, classModulus,
    thirdProjectionStart, (.unary (.parameter 3)),
    (.literal 0), (.literal 1), secondBase, fourthBase, (.unary (.parameter 5)), fullModulus,
    complementedTarget, headBase, firstArena, classModulus,
    (.literal 1), (.literal 0), (.literal 0), (.literal 0), (.literal 1), (.literal 2),
    (.literal 1), (.unary (.parameter 2)), fullModulus, complementedStart, inverseHeads,
    inverseArena, classModulus, (.literal 1), (.literal 0),
    (.literal 0), (.literal 0), (.literal 0), (.literal 1), (.literal 2), (.literal 1),
    (.literal 0), (.literal 1), (.literal 2), (.literal 1), thirdBase, middleProjectionStart,
    (.unary (.parameter 4)),
    fullModulus, classModulus, headBase, dictionaryBase, (.literal 0), (.literal 0),
    (.literal 1), (.literal 0), (.literal 0),
    (.literal 0), (.literal 1), (.literal 2), (.literal 1), (.literal 0), (.literal 1),
    (.literal 2), (.literal 1), (.literal 0), (.literal 1), (.literal 2), (.literal 1),
    (.literal 3), (.literal 0), secondBase, thirdProjectionStart, (.unary (.parameter 3)),
    fullModulus, classModulus, inverseHeads, dictionaryBase,
    (.literal 1), (.literal 0), (.literal 0), (.literal 0), (.literal 1), (.literal 0),
    (.literal 1), (.literal 2), (.literal 0), (.literal 0), (.literal 0), (.literal 1),
    (.literal 2), (.literal 1), (.literal 0), (.literal 1), (.literal 2), (.literal 1),
    (.literal 3), (.literal 1), (.literal 3), (.literal 0), (.literal 1), (.literal 0),
    dictionaryBase,
    positiveOne, statusAddress, (.literal 0), dictionaryBase, hitPayloadLength, statusAddress,
    (.literal 1), (.literal 1), (.unary (.parameter 2)),
    payloadAddressViaSuccessor, (.literal 1), (.literal 1), (.literal 2), (.literal 0),
    (.unary (.parameter 3)), afterFirstField,
    (.literal 1), (.literal 1), (.literal 2), (.literal 0), (.unary (.parameter 4)),
    afterSecondField,
    (.literal 1), (.literal 1), (.literal 2), (.literal 0), (.unary (.parameter 5)),
    afterThirdField,
    (.literal 1), (.literal 1), (.literal 2), (.literal 0), (.unary (.parameter 2)),
    reverseFirstCursor,
    (.literal 1), (.literal 1), (.literal 2), (.literal 0), (.unary (.parameter 3)),
    reverseSecondCursor,
    (.literal 1), (.literal 1), (.literal 2), (.literal 0), (.unary (.parameter 4)),
    reverseThirdCursor,
    (.literal 1), (.literal 1), (.literal 2), (.literal 0), (.unary (.parameter 5)),
    reverseFourthCursor,
    (.literal 1), (.literal 1), (.literal 2), (.literal 0)]

-- The fixed 303-entry literal list requires more than 512 nested simplifier frames.
set_option maxRecDepth 2048 in
/-- Every generated immediate is the actual native immediate, for arbitrary metadata. -/
theorem literals_exact (h : Metadata) :
    evaluate literalTemplate h = (nativeCode h).literals := by
  simp only [evaluate, literalTemplate, List.map_cons, List.map_nil]
  simp only [nativeCode, Code.literals_rename, Code.literals, Op.bin,
    Bool.false_eq_true, ↓reduceIte, Bool.toNat_true, Bool.toNat_false,
    Native.Driver.dissectionOutput,
    Native.Driver.dissection,
    Native.Driver.prepare,
    Native.Driver.countPair,
    Native.Quarter.countHalf,
    Native.Quarter.projectQuarter,
    Native.Counters.projectFrom,
    Native.Counters.projectBody,
    Native.Quarter.countSetup,
    Native.Counters.preprocess,
    Native.initializeTable,
    Native.Counters.layers,
    Native.Counters.iteration,
    Native.Counters.sweep,
    Native.Counters.body,
    Native.Driver.computeBalance,
    Native.Balance.scan,
    Native.Balance.body,
    Native.Balance.smaller,
    Native.Balance.largest,
    Native.Driver.searchLoop,
    Native.Driver.classLoop,
    Native.Driver.classBody,
    Native.Driver.inverseClass,
    Native.Driver.registerSelected,
    Native.Driver.registerCycle,
    Native.Driver.registerKernel,
    Native.Quarter.projectMiddle,
    Native.Quarter.prepareClassBuckets,
    Native.Quarter.inverseSetup,
    Native.Quarter.prepare,
    Native.Quarter.prepareLoop,
    Native.Quarter.prepareBody,
    Native.Quarter.evaluate,
    Native.Quarter.body,
    Native.Quarter.operation,
    Native.Quarter.insert,
    Native.Quarter.Backward.prepare,
    Native.Quarter.Backward.prepareLoop,
    Native.Quarter.Backward.prepareBody,
    Native.Quarter.backwardEvaluate,
    Native.Quarter.reverseOperators,
    Native.Quarter.reverseBody,
    Native.Driver.registerPrepared,
    Native.Driver.registerLayout,
    Native.Quarter.retainClass,
    Native.Quarter.retainClassBody,
    Native.Quarter.retainLoop,
    Native.Quarter.retainBody,
    Native.Dictionary.put,
    Native.Quarter.probeClass,
    Native.Quarter.probeClassBody,
    Native.Quarter.probeScan,
    Native.Quarter.probeScanBody,
    Native.Quarter.probeBody,
    Native.Dictionary.get,
    Native.Quarter.releaseWitness,
    Native.Dictionary.release,
    Native.Dictionary.pop,
    Native.Driver.advanceClass,
    Native.Driver.Output.program, Native.Driver.Output.fields,
    Native.Driver.Output.header,
    Native.Driver.Output.emitFields,
    Native.Driver.Output.emitWord,
    Native.Quarter.OutputBits.program,
    Native.Quarter.OutputBits.body,
    List.cons_append, List.nil_append, List.append_nil]
  simp only [reverseFourthCursor, reverseFourthOrigin, afterAllFields, reverseThirdCursor,
    reverseThirdOrigin, reverseSecondCursor, reverseSecondOrigin, reverseFirstCursor,
    reverseFirstOrigin, afterThirdField, afterSecondField, afterFirstField, payloadAddress,
    payloadAddressViaSuccessor, hitPayloadLength, statusAddress, positiveOne,
    complementedStart, dictionaryBase, inverseArena, inverseHeads, arenaSpan, quarterCountSum,
    fourthQuarterCount, firstQuarterCount, firstArena, headBase, headOffset, thirdBase,
    thirdProjectionStart, thirdProjectionOffset, middleProjectionStart, fourClasses,
    scratchOffset, doubleOperandLength,
    projectedInverseStart, complementedTarget, targetWord, fullMask, backwardTableEnd,
    backwardCounterStart, fourthBase, secondBase, suffixLength, reversedProjectionStart,
    twoClasses, projectedStart, startWord, fullModulus, firstTableEnd, counterStart,
    projectionStart, operandLength, prefixThirdLength, prefixLength,
    classModulus, Expr.eval, Unary.eval,
    BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_not]
  rfl

/-- Erasing scalar values gives one fixed instruction graph. -/
theorem graph_exact (h : Metadata) :
    (nativeCode h).eraseLiterals = (nativeCode ((fun _ => 0), fun _ => 0)).eraseLiterals := by
  rfl

end Cslib.Cryptanalysis.AddXNOR.ProgramTemplate
