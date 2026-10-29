/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.MCSP.FormulaMagnification

/-!
# Tests: Oliveira–Santhanam (2018) Formula Magnification

Concrete evaluation and non-vacuity checks for `Complexity.Computability.MCSP.FormulaMagnification`:
encoded length of `SuccinctMCSP` sub-table queries, leaf-size-`≤ 1` formula projections
(`succinctWord`), Adleman amplification, approximate `(1, 1 - 1 / k)-MCSP`, and the
`PartialMCSP` (`MCSP*`) bridge.
-/

namespace ComplexityTests.FormulaMagnification

open Cslib Cslib.Circuits Cslib.Circuits.Boolean Turing.MultiTapeTM

-- Encoded bit length 44, `succinctWord` length and leafSize ≤ 1, evaluation on `![true, false]`,
-- and Adleman's exponential inequality.
example :
    SuccinctMCSP.ofFunctionEncLength 1 2 1 = 44 ∧
    (succinctWord 1 Finset.univ 1).length = 44 ∧
    ((succinctWord 1 Finset.univ 1).map Formula.leafSize).all (· ≤ 1) = true ∧
    evalWord (succinctWord 1 Finset.univ 1) ![true, false] =
      SuccinctMCSP.enc
        (SuccinctMCSP.Instance.ofFunction ((MCSP.truthTable 1).symm ![true, false])
          Finset.univ 1) ∧
    2 ^ 2 * (3 - 1) ^ (3 * (2 + 1)) < 3 ^ (3 * (2 + 1)) := by
  decide

-- Non-vacuity of `exists_seed_tuple_of_one_sided_error` on `Ω = Bool`, `N = 1`, `k = 2`.
example :
    ∃ ωs : Fin (2 * (1 + 1)) → Bool,
      ∀ T ∈ (Finset.univ : Finset (BitString 1)),
        ∃ j : Fin (2 * (1 + 1)), T 0 = ωs j := by
  refine exists_seed_tuple_of_one_sided_error (by decide) Finset.univ (fun T ω => T 0 = ω) ?_
  intro T _
  cases h : T 0 <;> decide

private theorem eq_proj_of_mem_computableFunctions_zero {g : BooleanFunction 1}
    (hg : g ∈ computableFunctions 1 0) : g = fun x : BitString 1 => x 0 := by
  rw [mem_computableFunctions] at hg
  obtain ⟨c, hc, hsize⟩ := hg
  have h0 : c.size = 0 := Nat.le_zero.mp hsize
  funext x
  rw [← Circuit.computes_single_iff.mp hc x]
  cases hw : c.outputs 0 with
  | input i =>
    fin_cases i
    simp [Circuit.eval, hw]
  | gate k =>
    exact (Fin.cast h0 k).elim0

private theorem card_computableFunctions_one_zero_le :
    (computableFunctions 1 0).card ≤ 2 ^ 1 := by
  have hsub : computableFunctions 1 0 ⊆ {fun x : BitString 1 => x 0} := fun g hg =>
    Finset.mem_singleton.mpr (eq_proj_of_mem_computableFunctions_zero hg)
  exact (Finset.card_le_card hsub).trans (by decide)

-- Concrete check of `ApproxMCSP.noSet`: the 1-input constant `true` truth table `![true, true]`
-- belongs to `ApproxMCSP.noSet (fun _ => 0) (fun _ => 2)` because the sole 0-gate function
-- `x ↦ x 0` agrees with `true` on only 1 of the 2 inputs (`2 * 1 ≤ (2 - 1) * 2 ^ 1`).
private theorem const_true_mem_approxMCSP_noSet :
    List.ofFn (![true, true] : BitString (2 ^ 1)) ∈
      ApproxMCSP.noSet (fun _ => 0) (fun _ => 2) := by
  refine (ApproxMCSP.ofFn_mem_noSet_iff (n := 1)).mpr ?_
  intro g hg
  rw [eq_proj_of_mem_computableFunctions_zero hg]
  decide

-- Concrete end-to-end instantiation of `exists_formula_separating_approxMCSP_of_succinctMCSP`
-- at `n = 1, s₁ = 0, s₂ = 0, k = 2, M = 1`, verifying that the produced formula has leaf size at
-- most `(2 ^ 1 + 1) * L = 3 * L` and rejects the concrete no-instance `![true, true]`.
open Classical in
example :
    let L := (Finset.range (2 * (1 + 2) + 1)).sup fun m =>
      formulaSize (Language.slice (SuccinctMCSP.enc '' SuccinctMCSP)
        (SuccinctMCSP.ofFunctionEncLength 1 m 0))
    ∃ F : Formula signature (2 ^ 1),
      F.leafSize ≤ (2 ^ 1 + 1) * L ∧
      (∀ T : BitString (2 ^ 1), List.ofFn T ∈ GapMCSP.yesSet (fun _ => 0) →
        F.eval interpretation T = true) ∧
      F.eval interpretation ![true, true] = false := by
  intro L
  obtain ⟨F, hleaf, hyes, hno⟩ :=
    exists_formula_separating_approxMCSP_of_succinctMCSP
      (s₁ := fun _ => 0) (s₂ := fun _ => 0) (k := fun _ => 2) (n := 1) (M := 1) (L := L)
      (by decide) (by decide) card_computableFunctions_one_zero_le
      (fun m hm => Finset.le_sup (f := fun m =>
        formulaSize (Language.slice (SuccinctMCSP.enc '' SuccinctMCSP)
          (SuccinctMCSP.ofFunctionEncLength 1 m 0)))
        (Finset.mem_range.mpr (Nat.lt_succ_of_le hm)))
  exact ⟨F, hleaf, hyes, hno ![true, true] const_true_mem_approxMCSP_noSet⟩

-- Concrete checks of `PartialMCSP.Instance.restrictTable`, `FormulaPoly`, `FormulaPolyOn`,
-- `card_filter_agreesOn_eq_two_pow`, `computableFunctionsLogBound`, and Lemma 26.
open Classical in
example :
    (PartialMCSP.Instance.restrictTable (n := 1) ![true, false] {![false]} 1).partialFunction
      ![false] = some true ∧
    (PartialMCSP.Instance.restrictTable (n := 1) ![true, false] {![false]} 1).partialFunction
      ![true] = none ∧
    (0 : Language Bool) ∈ FormulaPoly ∧
    (⊤ : Language Bool) ∈ FormulaPoly ∧
    ((0 : Language Bool) : Set (List Bool)) ∈ FormulaPolyOn encBits ∧
    (Finset.univ.filter fun T : BitString (2 ^ 1) =>
      ∀ y ∈ ({![false]} : Finset (BitString 1)),
        (MCSP.truthTable 1).symm T y = y 0).card = 2 ∧
    (Finset.univ.filter fun T : BitString (2 ^ 1) =>
      SuccinctMCSP.Instance.ofFunction
        ((MCSP.truthTable 1).symm T) Finset.univ 0 ∈ SuccinctMCSP).card ≤ 2 ∧
    computableFunctionsLogBound 2 3 = 36 ∧
    computableFunctionsLogBound 4 0 + 1 ≤ 2 ^ 4 := by
  have hle := card_filter_ofFunction_mem_succinctMCSP_le 1 Finset.univ 0
  have hcard : (Finset.univ : Finset (BitString 1)).card = 2 ^ 1 := by simp [BitString]
  rw [hcard, Nat.sub_self, pow_zero, mul_one] at hle
  exact ⟨by decide, by decide, FormulaPoly.zero_mem, FormulaPoly.top_mem,
    mem_FormulaPolyOn_encBits_iff.mpr FormulaPoly.zero_mem,
    by simpa using card_filter_agreesOn_eq_two_pow 1 {![false]} (fun x => x 0),
    hle.trans card_computableFunctions_one_zero_le, by decide, by decide⟩

open Classical in
example :
    ∃ F : Formula signature (2 ^ 4),
      F.leafSize ≤
        formulaSize (Language.slice (SuccinctMCSP.enc '' SuccinctMCSP)
          (avgCaseMCSPQueryEncLength 4 0 1)) ∧
      (∀ T : BitString (2 ^ 4), List.ofFn T ∈ GapMCSP.yesSet (fun _ => 0) →
        F.eval interpretation T = true) ∧
      (Finset.univ.filter fun T : BitString (2 ^ 4) =>
        F.eval interpretation T = true).card ≤ 2 ^ (2 ^ 4 - 1) :=
  exists_formula_zero_error_average_case_of_succinctMCSP (s := fun _ => 0) (n := 4) (r := 1)
    (by decide)

-- Direct check of `exists_formula_ofFunction_SuccinctMCSP_of_agrees` with an explicit agreeing
-- language (`SuccinctMCSP.enc '' SuccinctMCSP`).
open Classical in
example :
    ∃ F : Formula signature (2 ^ 1),
      (∀ T : BitString (2 ^ 1),
        F.eval interpretation T =
          decide (SuccinctMCSP.Instance.ofFunction
            ((MCSP.truthTable 1).symm T) Finset.univ 0 ∈ SuccinctMCSP)) ∧
      F.leafSize ≤
        formulaSize (Language.slice (SuccinctMCSP.enc '' SuccinctMCSP)
          (SuccinctMCSP.ofFunctionEncLength 1 (Finset.univ : Finset (BitString 1)).card 0)) :=
  exists_formula_ofFunction_SuccinctMCSP_of_agrees
    (fun _ => SuccinctMCSP.enc.injective.mem_set_image.symm) 1 Finset.univ 0

end ComplexityTests.FormulaMagnification
