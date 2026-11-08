/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Circuit.Boolean.Oracle

/-!
# Oracle-circuit clients

Zero-arity queries inspect the empty word; sequential queries consume earlier answers.
The clients also cover zero-gate inlining and an inhabited relativized circuit class.
-/

namespace ComplexityTests.OracleCircuits

open Cslib Cslib.Circuits Cslib.Circuits.Boolean

private def emptyQuery : Circuit oracleSignature 0 1 :=
  Circuit.oneGate (.query 0) Fin.elim0

example : emptyQuery.eval (oracleInterpretation (0 : Language Bool)) Fin.elim0 0 = false := by
  simp only [emptyQuery, Circuit.eval_oneGate, oracleInterpretation_query,
    Language.slice, List.ofFn_zero, decide_eq_false_iff_not]
  exact Set.notMem_empty _

example : emptyQuery.eval (oracleInterpretation (⊤ : Language Bool)) Fin.elim0 0 = true := by
  simp only [emptyQuery, Circuit.eval_oneGate, oracleInterpretation_query,
    Language.slice, List.ofFn_zero, decide_eq_true_eq]
  trivial

private def unaryQuery : Circuit oracleSignature 1 1 :=
  Circuit.oneGate (.query 1) id

-- The second query's input is the first answer, not an original input wire.
private def adaptiveQuery : Circuit oracleSignature 1 1 :=
  unaryQuery.comp unaryQuery

example (A : Language Bool) (x : BitString 1) :
    adaptiveQuery.eval (oracleInterpretation A) x 0 =
      A.slice 1 (fun _ => A.slice 1 x) := by
  simp [adaptiveQuery, unaryQuery, Circuit.eval_comp, oracleInterpretation]

-- A positive-arity oracle can be a zero-gate projection; unused widths may be constants.
private def replacements : (q : ℕ) → Circuit signature q 1
  | 0 => Circuit.oneGate (.const false) Fin.elim0
  | _ + 1 => Circuit.wiring signature (fun _ => 0)

private def firstBitLanguage : Language Bool :=
  Language.ofSlices fun n x => (replacements n).eval interpretation x 0

private theorem replacements_correct (q : ℕ) :
    (replacements q).Computes interpretation (single (firstBitLanguage.slice q)) := by
  intro x
  simp only [firstBitLanguage, Language.slice_ofSlices]
  funext i
  exact congrArg ((replacements q).eval interpretation x) (Fin.eq_zero i)

example (x : BitString 1) :
    (inlineOracle adaptiveQuery replacements).eval interpretation x 0 = x 0 := by
  rw [eval_inlineOracle adaptiveQuery replacements_correct]
  simp [adaptiveQuery, unaryQuery, Circuit.eval_comp, oracleInterpretation,
    firstBitLanguage, replacements]

example : (inlineOracle adaptiveQuery replacements).size = 0 := by
  rfl

example : (inlineOracle emptyQuery replacements).size = 1 := by
  rfl

example : PPolyOracle (0 : Language Bool) = PPoly :=
  PPolyOracle_eq_PPoly PPoly.zero_mem

example : (⊤ : Language Bool) ∈ PPolyOracle (0 : Language Bool) :=
  PPoly.subset_PPolyOracle _ PPoly.top_mem

end ComplexityTests.OracleCircuits
