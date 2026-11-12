/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.MCSP.FormulaMagnification.Locality

/-!
# Tests: locality of the Oliveira–Santhanam construction

Measures of a hand-built oracle formula, and non-vacuity of the fan-in bound: at concrete
parameters each oracle gate reads far fewer than `2 ^ n` bits, so one gate reading the whole truth
table does not meet the bound.
-/

namespace CslibFrontierTests.FormulaMagnificationLocality

open Cslib Cslib.Circuits Cslib.Circuits.Boolean

/-- Two oracle gates side by side: one reads the first input twice, the other reads the second. -/
private def twoQueries : OracleFormula 2 :=
  OracleFormula.all [OracleFormula.query [.input 0, .input 0], OracleFormula.query [.input 1]]

example : twoQueries.queryCount = 2 ∧ twoQueries.maxQueryArity = 2 ∧
    twoQueries.adaptivity ≤ 1 ∧ twoQueries.leafSize = 3 := by
  refine ⟨by simp [twoQueries], ?_, ?_, by simp [twoQueries]⟩
  · simp [twoQueries, OracleFormula.all]
  · refine OracleFormula.adaptivity_all_le fun E hE => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hE
    rcases hE with rfl | rfl <;> simp

/-- The words beginning with `true`. -/
private def headTrue : Language Bool := {w | w.head? = some true}

private theorem mem_headTrue {w : List Bool} : w ∈ headTrue ↔ w.head? = some true := Iff.rfl

/-- Under `headTrue`, the formula is the conjunction of its two inputs: it accepts
`![true, true]`. -/
example : twoQueries.eval (oracleInterpretation headTrue) ![true, true] = true := by
  rw [twoQueries, OracleFormula.eval_all, decide_eq_true_eq]
  intro E hE
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hE
  rcases hE with rfl | rfl <;> simp [OracleFormula.eval_query_eq_true_iff, mem_headTrue]

/-- ... and rejects `![true, false]`, since the second gate reads `[false]`. -/
example : twoQueries.eval (oracleInterpretation headTrue) ![true, false] = false := by
  rw [twoQueries, OracleFormula.eval_all, decide_eq_false_iff_not]
  intro h
  have := h _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))
  simp [OracleFormula.eval_query_eq_true_iff, mem_headTrue] at this

/-- Non-vacuity at `n = s = 20`, `k = 2`: the fan-in bound is below `2 ^ 20`. -/
example : approxMCSPQueryEncLength 20 20 2 < 2 ^ 20 := by
  have h : Nat.clog 2 (20 + 20 + 1) ≤ 6 := (Nat.clog_le_iff_le_pow (by decide)).mpr (by decide)
  simp only [approxMCSPQueryEncLength, computableFunctionsLogBound,
    SuccinctMCSP.ofFunctionEncLength] at h ⊢
  norm_num at h ⊢
  omega

/-- The explicit polynomial bound applies at those parameters. -/
example : approxMCSPQueryEncLength 20 20 2 ≤ 98 * (2 * (20 + 1)) ^ 3 :=
  approxMCSPQueryEncLength_le_poly le_rfl (by decide)

/-- The class form is inhabited at concrete parameters. -/
example : LocalFormulaClass (fun m => m)
    (fun m => approxMCSPQueryEncLength (Nat.log 2 m) (Nat.log 2 m) 2) (fun _ => 1)
    (fun m => m * approxMCSPQueryEncLength (Nat.log 2 m) (Nat.log 2 m) 2)
    (GapMCSP.yesSet id) (ApproxMCSP.noSet id fun _ => 2) :=
  localFormulaClass_approxMCSP (s₁ := id) (s₂ := id) (k := fun _ => 2) (fun _ => by decide)
    fun _ => le_rfl

/-- The real-error form at `δ = 1 / 4` and `s = id`: fan-in `98 * (4 * (n + 1)) ^ 3`, where
`n = log₂ m`. -/
example : LocalFormulaClass (fun m => m) (fun m => 98 * (4 * (Nat.log 2 m + 1)) ^ 3) (fun _ => 1)
    (fun m => m * (98 * (4 * (Nat.log 2 m + 1)) ^ 3))
    (GapMCSP.yesSet id) (ApproxMCSP.noSetReal id fun _ => 1 / 4) := by
  have h : ⌈(1 : ℝ) / (1 / 4)⌉₊ = 4 := by norm_num
  simpa only [h, id_eq] using
    localFormulaClass_approxMCSP_real_poly (s := id) (δ := fun _ => 1 / 4) (fun _ => by norm_num)
      fun _ => le_rfl

end CslibFrontierTests.FormulaMagnificationLocality
