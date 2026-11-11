/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.SharpSAT
public import CslibFrontier.Computability.Complexity.Problems.TwoSAT
public import CslibFrontier.Computability.Complexity.Reduction.CountingTuring
public import CslibFrontier.Logics.Propositional.CNF.ModelCount
import CslibFrontier.Logics.Propositional.CNF.Eval
import CslibFrontier.Logics.Propositional.CNF.ModelCount.Declared
import CslibFrontier.Computability.Complexity.Classes.Ladner
import CslibFrontier.Computability.Complexity.CookLevin.Counting
import CslibFrontier.Computability.Complexity.FineGrained.BruteForce
import CslibFrontier.Computability.Complexity.Problems.SAT.PolyTime
import CslibFrontier.Computability.Complexity.Problems.SharpThreeSAT
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Choose
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Eq
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Foundations.Data.List.OfFn
import CslibFrontier.Foundations.Data.Polynomial.FiniteDifference
import CslibFrontier.Logics.Propositional.CNF.PolyTime
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Data.Nat.Choose.Basic

/-!
# `#2SAT` is `#P`-complete under counting Turing reductions

Valiant's theorem ([Valiant 1979][Valiant1979Enumeration]): counting the satisfying assignments of
a `2-CNF` formula (`SharpTwoSAT`) belongs to `#P` and is `#P`-hard under polynomial-time counting
Turing reductions (`CountingTuringComplete encCNF SharpTwoSAT`).

Given any CNF formula `φ` with `m` clauses and parameter `r : ℕ`, `valiantTwoSAT φ r` replaces
each original variable `v` by `2 * v` and attaches to each clause `i < m` a clause indicator
`zVar r i` together with `r - 1` monotone chain variables `uVar r i j` so that each assignment `σ`
to `φ` extends to `1` solution of gadget `i` when clause `i` is satisfied and `r + 1` solutions
when clause `i` is falsified. Therefore `SharpTwoSAT (valiantTwoSAT φ r) = P(r + 1)` where
`P(X) = ∑ σ, X ^ (φ.countUnsat σ)` has degree at most `m` and `P(0) = SharpSAT φ`. Evaluating `P(0)`
via `Polynomial.eval_zero_eq_sum_neg_one_pow_choose_eval_succ` yields `SharpSAT φ` as a difference
of two nonnegative binomial combinations with no division, completing the counting Turing reduction.

## Main definitions

* `Cslib.Complexity.SharpTwoSAT`: the number of satisfying assignments on occurring variables when
  every clause has length at most `2`, and `0` otherwise.
* `Cslib.Complexity.valiantTwoSAT`: Valiant's `2-CNF` clause-weight gadget formula.

## Main results

* `Cslib.Complexity.SharpTwoSAT.mem_SharpP`: `SharpTwoSAT ∈ SharpP encCNF`.
* `Cslib.Complexity.modelCount_valiantTwoSAT`: exact fibre-count formula
  `∑ σ, (r + 1) ^ (φ.countUnsat ext(σ))`.
* `Cslib.Complexity.countingTuringReducible_SharpSAT_SharpTwoSAT`: `#SAT ≤_T^#P #2SAT`.
* `Cslib.Complexity.SharpTwoSAT_countingTuringComplete`: `#2SAT` is `#P`-complete under counting
  Turing reductions.
* `Cslib.Complexity.SharpTwoSAT_polyTime_implies_P_eq_NP`: if `SharpTwoSAT ∈ FP`, then `P = NP`.

## References

* [L. G. Valiant, *The complexity of enumeration and reliability problems*][Valiant1979Enumeration].
* [L. G. Valiant, *The complexity of computing the permanent*][Valiant1979].
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09].
-/

public section

namespace Cslib.Complexity

open Cslib.Logic.PL Turing.MultiTapeTM

/-- Number of satisfying assignments of `φ` on its occurring variables when every clause has length
at most `2`, and `0` otherwise (`#2SAT`). -/
@[expose] def SharpTwoSAT (φ : CNF ℕ) : ℕ :=
  if φ.all (fun c => decide (c.length ≤ 2)) then φ.modelCount else 0

/-- `#2SAT` belongs to `#P`. -/
theorem SharpTwoSAT.mem_SharpP : SharpTwoSAT ∈ SharpP encCNF :=
  (parsimoniousReducible_guard (computableInPolyTime_all_length_le 2)).mem_SharpP
    SharpSAT.mem_SharpP

/-! ### Valiant's 2-CNF clause-weight gadget construction -/

/-- Auxiliary clause-indicator variable index for clause `i` at weight parameter `r`. -/
@[expose] def zVar (r i : ℕ) : ℕ :=
  2 * (i * (r + 1)) + 1

/-- Auxiliary chain variable index `(i, j)` (`j < r - 1`) at weight parameter `r`. -/
@[expose] def uVar (r i j : ℕ) : ℕ :=
  2 * (i * (r + 1) + j + 1) + 1

/-- Width-`2` tautology clauses ensuring every occurring variable `v` of `φ` appears at `2 * v`. -/
@[expose] def valiantVarTauts (φ : CNF ℕ) : CNF ℕ :=
  φ.distinctVars.map fun v => [(2 * v, true), (2 * v, false)]

/-- Weight gadget for clause `(c, i)` at parameter `r`: forces `zVar r i = false` if `c` holds,
and otherwise permits `r + 1` extensions of `(zVar r i, uVar r i 0, …, uVar r i (r - 2))`. -/
@[expose] def valiantClauseGadget (r : ℕ) (ci : Clause ℕ × ℕ) : CNF ℕ :=
  let c := ci.1
  let i := ci.2
  let litClauses : CNF ℕ := c.map fun l => [(zVar r i, false), (2 * l.1, !l.2)]
  let auxClauses : CNF ℕ :=
    if r = 0 then [[(zVar r i, false)]]
    else if r = 1 then [[(zVar r i, true), (zVar r i, false)]]
    else
      [[(zVar r i, true), (zVar r i, false)], [(zVar r i, true), (uVar r i 0, false)]] ++
        (List.range (r - 2)).map fun j => [(uVar r i j, true), (uVar r i (j + 1), false)]
  litClauses ++ auxClauses

/-- Valiant's `2-CNF` formula at interpolation parameter `r : ℕ`. -/
@[expose] def valiantTwoSAT (φ : CNF ℕ) (r : ℕ) : CNF ℕ :=
  valiantVarTauts φ ++ (φ.zipIdx.flatMap (valiantClauseGadget r))

/-- Every clause of `valiantTwoSAT φ r` has length at most `2`. -/
theorem length_clause_valiantTwoSAT_le (φ : CNF ℕ) (r : ℕ) {c : Clause ℕ}
    (hc : c ∈ valiantTwoSAT φ r) : c.length ≤ 2 := by
  simp only [valiantTwoSAT, List.mem_append, List.mem_flatMap] at hc
  rcases hc with hc | ⟨ci, _, hc⟩
  · obtain ⟨v, _, rfl⟩ := List.mem_map.mp hc
    exact le_rfl
  · simp only [valiantClauseGadget, List.mem_append] at hc
    rcases hc with hc | hc
    · obtain ⟨l, _, rfl⟩ := List.mem_map.mp hc
      exact le_rfl
    · split_ifs at hc with hr0 hr1
      · simp only [List.mem_singleton] at hc
        subst hc
        simp only [List.length_singleton]
        omega
      · simp only [List.mem_singleton] at hc
        subst hc
        exact le_rfl
      · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map] at hc
        rcases hc with (rfl | rfl) | ⟨j, _, rfl⟩ <;> exact le_rfl

/-- Hence `SharpTwoSAT (valiantTwoSAT φ r)` agrees with `(valiantTwoSAT φ r).modelCount`. -/
theorem SharpTwoSAT_valiantTwoSAT (φ : CNF ℕ) (r : ℕ) :
    SharpTwoSAT (valiantTwoSAT φ r) = (valiantTwoSAT φ r).modelCount := by
  rw [SharpTwoSAT]
  split_ifs with h
  · rfl
  · exact absurd (List.all_eq_true.mpr fun c hc =>
      decide_eq_true (length_clause_valiantTwoSAT_le φ r hc)) h

private theorem two_mul_ne_zVar (v r i : ℕ) : 2 * v ≠ zVar r i := by
  unfold zVar
  omega

private theorem two_mul_ne_uVar (v r i j : ℕ) : 2 * v ≠ uVar r i j := by
  unfold uVar
  omega

private theorem zVar_ne_uVar {r i₁ i₂ j : ℕ} (hj : j < r - 1) :
    zVar r i₁ ≠ uVar r i₂ j := by
  unfold zVar uVar
  intro h
  have h1 : i₁ * (r + 1) = i₂ * (r + 1) + (j + 1) := by omega
  have hmod := congrArg (· % (r + 1)) h1
  rw [Nat.mul_mod_left, Nat.add_comm (i₂ * _), Nat.add_mul_mod_self_right,
    Nat.mod_eq_of_lt (by omega)] at hmod
  omega

private theorem zVar_inj {r i₁ i₂ : ℕ} (h : zVar r i₁ = zVar r i₂) : i₁ = i₂ := by
  unfold zVar at h
  have h1 : i₁ * (r + 1) = i₂ * (r + 1) := by omega
  exact Nat.eq_of_mul_eq_mul_right (Nat.succ_pos r) h1

private theorem uVar_inj {r i₁ i₂ j₁ j₂ : ℕ} (hj₁ : j₁ < r - 1) (hj₂ : j₂ < r - 1)
    (h : uVar r i₁ j₁ = uVar r i₂ j₂) : i₁ = i₂ ∧ j₁ = j₂ := by
  unfold uVar at h
  have h1 : i₁ * (r + 1) + (j₁ + 1) = i₂ * (r + 1) + (j₂ + 1) := by omega
  have hdiv := congrArg (· / (r + 1)) h1
  have hmod := congrArg (· % (r + 1)) h1
  rw [Nat.add_comm (i₁ * _), Nat.add_comm (i₂ * _),
    Nat.mul_comm i₁ _, Nat.mul_comm i₂ _,
    Nat.add_mul_div_left _ _ (Nat.succ_pos r), Nat.add_mul_div_left _ _ (Nat.succ_pos r),
    Nat.div_eq_of_lt (by omega), Nat.div_eq_of_lt (by omega), Nat.zero_add, Nat.zero_add] at hdiv
  rw [Nat.add_comm (i₁ * _), Nat.add_comm (i₂ * _),
    Nat.add_mul_mod_self_right, Nat.add_mul_mod_self_right,
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hmod
  exact ⟨hdiv, by omega⟩

private theorem mem_vars_valiantTwoSAT (φ : CNF ℕ) (r w : ℕ) :
    w ∈ (valiantTwoSAT φ r).vars ↔
      (∃ v ∈ φ.vars, w = 2 * v) ∨
        ∃ i < φ.length, w = zVar r i ∨ ∃ j < r - 1, w = uVar r i j := by
  constructor
  · intro hw
    rw [valiantTwoSAT, CNF.vars, List.mem_map] at hw
    obtain ⟨l, hl, rfl⟩ := hw
    rw [List.mem_flatten] at hl
    obtain ⟨c, hc, hl⟩ := hl
    rw [List.mem_append] at hc
    rcases hc with hc | hc
    · obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      have hv' : v ∈ φ.vars := CNF.mem_distinctVars.mp hv
      rcases hl with rfl | rfl <;> exact Or.inl ⟨v, hv', rfl⟩
    · obtain ⟨⟨cl, i⟩, hci, hc⟩ := List.mem_flatMap.mp hc
      have hget := List.mem_zipIdx_iff_getElem?.mp hci
      have hi : i < φ.length := (List.getElem?_eq_some_iff.mp hget).1
      have hclMem : cl ∈ φ := List.mem_of_getElem? hget
      simp only [valiantClauseGadget, List.mem_append] at hc
      rcases hc with hc | hc
      · obtain ⟨lit, hlit, rfl⟩ := List.mem_map.mp hc
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
        rcases hl with rfl | rfl
        · exact Or.inr ⟨i, hi, Or.inl rfl⟩
        · exact Or.inl ⟨lit.1, List.mem_map.mpr
            ⟨lit, List.mem_flatten.mpr ⟨cl, hclMem, hlit⟩, rfl⟩, rfl⟩
      · split_ifs at hc with hr0 hr1
        · simp only [List.mem_singleton] at hc
          subst hc
          simp only [List.mem_singleton] at hl
          cases hl
          exact Or.inr ⟨i, hi, Or.inl rfl⟩
        · simp only [List.mem_singleton] at hc
          subst hc
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
          rcases hl with rfl | rfl <;> exact Or.inr ⟨i, hi, Or.inl rfl⟩
        · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map] at hc
          rcases hc with (rfl | rfl) | ⟨j, hj, rfl⟩
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
            rcases hl with rfl | rfl <;> exact Or.inr ⟨i, hi, Or.inl rfl⟩
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
            rcases hl with rfl | rfl
            · exact Or.inr ⟨i, hi, Or.inl rfl⟩
            · exact Or.inr ⟨i, hi, Or.inr ⟨0, by omega, rfl⟩⟩
          · rw [List.mem_range] at hj
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
            rcases hl with rfl | rfl
            · exact Or.inr ⟨i, hi, Or.inr ⟨j, by omega, rfl⟩⟩
            · exact Or.inr ⟨i, hi, Or.inr ⟨j + 1, by omega, rfl⟩⟩
  · rintro (⟨v, hv, rfl⟩ | ⟨i, hi, hzi | ⟨j, hj, rfl⟩⟩)
    · have hv' : v ∈ φ.distinctVars := CNF.mem_distinctVars.mpr hv
      rw [valiantTwoSAT, CNF.vars, List.mem_map]
      refine ⟨(2 * v, true), List.mem_flatten.mpr ⟨[(2 * v, true), (2 * v, false)], ?_,
        List.mem_cons_self ..⟩, rfl⟩
      exact List.mem_append_left _ (List.mem_map.mpr ⟨v, hv', rfl⟩)
    · subst hzi
      have hci : (φ[i], i) ∈ φ.zipIdx :=
        List.mem_zipIdx_iff_getElem?.mpr (List.getElem?_eq_some_iff.mpr ⟨hi, rfl⟩)
      rw [valiantTwoSAT, CNF.vars, List.mem_map]
      by_cases hr0 : r = 0
      · refine ⟨(zVar r i, false), List.mem_flatten.mpr ⟨[(zVar r i, false)],
          List.mem_append_right _ (List.mem_flatMap.mpr ⟨(φ[i], i), hci, ?_⟩),
          List.mem_cons_self ..⟩, rfl⟩
        simp only [valiantClauseGadget, hr0, ↓reduceIte, List.mem_append, List.mem_singleton,
          or_true]
      · refine ⟨(zVar r i, false), List.mem_flatten.mpr
          ⟨[(zVar r i, true), (zVar r i, false)],
            List.mem_append_right _ (List.mem_flatMap.mpr ⟨(φ[i], i), hci, ?_⟩),
            List.mem_cons_of_mem _ (List.mem_cons_self ..)⟩, rfl⟩
        simp only [valiantClauseGadget, List.mem_append]
        right
        by_cases hr1 : r = 1 <;> simp [hr0, hr1]
    · have hci : (φ[i], i) ∈ φ.zipIdx :=
        List.mem_zipIdx_iff_getElem?.mpr (List.getElem?_eq_some_iff.mpr ⟨hi, rfl⟩)
      rw [valiantTwoSAT, CNF.vars, List.mem_map]
      have hr0 : r ≠ 0 := by omega
      have hr1 : r ≠ 1 := by omega
      cases j with
      | zero =>
        refine ⟨(uVar r i 0, false), List.mem_flatten.mpr
          ⟨[(zVar r i, true), (uVar r i 0, false)],
            List.mem_append_right _ (List.mem_flatMap.mpr ⟨(φ[i], i), hci, ?_⟩),
            List.mem_cons_of_mem _ (List.mem_cons_self ..)⟩, rfl⟩
        simp [valiantClauseGadget, hr0, hr1]
      | succ k =>
        refine ⟨(uVar r i (k + 1), false), List.mem_flatten.mpr
          ⟨[(uVar r i k, true), (uVar r i (k + 1), false)],
            List.mem_append_right _ (List.mem_flatMap.mpr ⟨(φ[i], i), hci, ?_⟩),
            List.mem_cons_of_mem _ (List.mem_cons_self ..)⟩, rfl⟩
        simp only [valiantClauseGadget, hr0, ↓reduceIte, hr1, List.mem_append, List.mem_cons,
          List.not_mem_nil, or_false, List.mem_map, List.mem_range]
        exact Or.inr (Or.inr ⟨k, by omega, rfl⟩)

/-- Number of occurring variables of `valiantTwoSAT φ r` is at most
`φ.vars.length + φ.length * (r + 1)`. -/
theorem numVars_valiantTwoSAT_le (φ : CNF ℕ) (r : ℕ) :
    (valiantTwoSAT φ r).numVars ≤ φ.vars.length + φ.length * (r + 1) := by
  have hsub : (valiantTwoSAT φ r).vars.toFinset ⊆
      φ.vars.toFinset.image (2 * ·) ∪
        ((Finset.range φ.length).biUnion fun i =>
          insert (zVar r i) ((Finset.range (r - 1)).image (uVar r i))) := by
    intro w hw
    rw [List.mem_toFinset, mem_vars_valiantTwoSAT] at hw
    rw [Finset.mem_union]
    rcases hw with ⟨v, hv, rfl⟩ | ⟨i, hi, rfl | ⟨j, hj, rfl⟩⟩
    · exact Or.inl (Finset.mem_image.mpr ⟨v, List.mem_toFinset.mpr hv, rfl⟩)
    · refine Or.inr (Finset.mem_biUnion.mpr ⟨i, Finset.mem_range.mpr hi, Finset.mem_insert_self ..⟩)
    · refine Or.inr (Finset.mem_biUnion.mpr ⟨i, Finset.mem_range.mpr hi,
        Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr hj, rfl⟩)⟩)
  have hImg : (φ.vars.toFinset.image (2 * ·)).card ≤ φ.vars.toFinset.card :=
    Finset.card_image_le
  have hVarsLen : φ.vars.toFinset.card ≤ φ.vars.length := List.toFinset_card_le φ.vars
  have hBi : ((Finset.range φ.length).biUnion fun i =>
      insert (zVar r i) ((Finset.range (r - 1)).image (uVar r i))).card ≤
      ∑ i ∈ Finset.range φ.length,
        (insert (zVar r i) ((Finset.range (r - 1)).image (uVar r i))).card :=
    Finset.card_biUnion_le
  have hSum : ∑ i ∈ Finset.range φ.length,
      (insert (zVar r i) ((Finset.range (r - 1)).image (uVar r i))).card ≤
      ∑ _ ∈ Finset.range φ.length, (r + 1) := by
    refine Finset.sum_le_sum fun i _ => ?_
    have h1 := Finset.card_insert_le (zVar r i) ((Finset.range (r - 1)).image (uVar r i))
    have h2 : ((Finset.range (r - 1)).image (uVar r i)).card ≤ r - 1 :=
      Finset.card_image_le.trans (by simp)
    omega
  have hUnion : (valiantTwoSAT φ r).numVars ≤
      (φ.vars.toFinset.image (2 * ·)).card +
        ((Finset.range φ.length).biUnion fun i =>
          insert (zVar r i) ((Finset.range (r - 1)).image (uVar r i))).card :=
    (Finset.card_le_card hsub).trans (Finset.card_union_le ..)
  have hConstSum : ∑ _ ∈ Finset.range φ.length, (r + 1) = φ.length * (r + 1) := by
    simp [Finset.sum_const, Finset.card_range, smul_eq_mul]
  omega

/-- Binary size bound for `SharpTwoSAT (valiantTwoSAT φ r)` whenever `r ≤ φ.length`. -/
theorem size_SharpTwoSAT_valiantTwoSAT_le {φ : CNF ℕ} {r : ℕ} (hr : r ≤ φ.length) :
    (SharpTwoSAT (valiantTwoSAT φ r)).size ≤
      φ.vars.length + φ.length * (φ.length + 1) + 1 := by
  have hle : SharpTwoSAT (valiantTwoSAT φ r) ≤
      2 ^ (φ.vars.length + φ.length * (φ.length + 1)) := by
    rw [SharpTwoSAT_valiantTwoSAT]
    refine (CNF.modelCount_le_two_pow_numVars _).trans (Nat.pow_le_pow_right (by omega) ?_)
    have hnum := numVars_valiantTwoSAT_le φ r
    have hm : φ.length * (r + 1) ≤ φ.length * (φ.length + 1) :=
      Nat.mul_le_mul_left _ (Nat.succ_le_succ hr)
    omega
  refine Nat.size_le.mpr (hle.trans_lt ?_)
  exact Nat.pow_lt_pow_right (by omega) (by omega)

/-! ### Exact fibre counting and monotone Boolean chain cardinality -/

/-- Monotone-false Boolean sequences of length `m`: once an entry is `false`, all subsequent
entries must be `false`. There are precisely `m + 1` such sequences. -/
private abbrev MonoBools (m : ℕ) : Type :=
  {u : Fin m → Bool //
    ∀ j (hj : j + 1 < m), u ⟨j, by omega⟩ = false → u ⟨j + 1, hj⟩ = false}

private noncomputable instance (m : ℕ) : Fintype (MonoBools m) := by
  classical
  exact Subtype.fintype _

private theorem mono_all_false {m : ℕ} {u : Fin m → Bool}
    (h0 : ∀ (hm : 0 < m), u ⟨0, hm⟩ = false)
    (hstep : ∀ j (hj : j + 1 < m), u ⟨j, by omega⟩ = false → u ⟨j + 1, hj⟩ = false) :
    ∀ i : Fin m, u i = false := by
  rintro ⟨n, hn⟩
  induction n with
  | zero => exact h0 hn
  | succ k ih => exact hstep k hn (ih (by omega))

private def monoBoolsStepEquiv (m : ℕ) : MonoBools (m + 1) ≃ Unit ⊕ MonoBools m where
  toFun u :=
    if h0 : u.1 ⟨0, Nat.succ_pos m⟩ = false then
      Sum.inl ()
    else
      Sum.inr ⟨fun j => u.1 j.succ, fun j hj hfalse => by
        simpa [Fin.succ] using u.2 (j + 1) (Nat.succ_lt_succ hj) hfalse⟩
  invFun
    | Sum.inl () => ⟨fun _ => false, fun _ _ _ => rfl⟩
    | Sum.inr tail =>
      ⟨Fin.cons true tail.1, fun j hj hfalse => by
        cases j with
        | zero => simp at hfalse
        | succ k =>
          change (Fin.cons true tail.1 : Fin (m + 1) → Bool)
            (Fin.succ (⟨k, by omega⟩ : Fin m)) = false at hfalse
          rw [Fin.cons_succ] at hfalse
          have ht := tail.2 k (Nat.lt_of_succ_lt_succ hj) hfalse
          change (Fin.cons true tail.1 : Fin (m + 1) → Bool)
            (Fin.succ (⟨k + 1, by omega⟩ : Fin m)) = false
          rw [Fin.cons_succ]
          exact ht⟩
  left_inv u := by
    obtain ⟨u, hu⟩ := u
    dsimp only
    split_ifs with h0
    · refine Subtype.ext (funext fun i => ?_)
      exact (mono_all_false (fun _ => h0) hu i).symm
    · have htrue : u ⟨0, Nat.succ_pos m⟩ = true := Bool.eq_true_of_not_eq_false h0
      refine Subtype.ext (funext fun i => ?_)
      cases i using Fin.cases with
      | zero => exact htrue.symm
      | succ j => rfl
  right_inv x := by
    cases x with
    | inl u =>
      cases u
      rfl
    | inr tail =>
      dsimp only
      split_ifs with h
      · rw [show (⟨0, Nat.succ_pos m⟩ : Fin (m + 1)) = 0 from rfl, Fin.cons_zero] at h
        exact Bool.noConfusion h
      · exact congrArg Sum.inr (Subtype.ext (funext fun _ => rfl))

private theorem card_monoBools (m : ℕ) : Fintype.card (MonoBools m) = m + 1 := by
  induction m with
  | zero =>
    let _ : Unique (MonoBools 0) :=
      { default := ⟨Fin.elim0, fun _ h => absurd h (Nat.not_lt_zero _)⟩
        uniq := fun u => Subtype.ext (funext fun i => Fin.elim0 i) }
    exact Fintype.card_unique
  | succ m ih =>
    calc
      Fintype.card (MonoBools (m + 1))
        = Fintype.card (Unit ⊕ MonoBools m) := Fintype.card_congr (monoBoolsStepEquiv m)
      _ = 1 + (m + 1) := by rw [Fintype.card_sum, Fintype.card_unit, ih]
      _ = (m + 1) + 1 := by omega

private def clauseAuxPred (r : ℕ) (sat : Bool) (p : Bool × (Fin (r - 1) → Bool)) : Prop :=
  if hr0 : r = 0 then p.1 = false
  else if hr1 : r = 1 then p.1 = true → sat = false
  else
    (p.1 = true → sat = false) ∧
      (p.1 = false → p.2 ⟨0, by omega⟩ = false) ∧
      (∀ j (hj : j + 1 < r - 1), p.2 ⟨j, by omega⟩ = false → p.2 ⟨j + 1, hj⟩ = false)

private noncomputable instance (r : ℕ) (sat : Bool) : DecidablePred (clauseAuxPred r sat) := by
  classical
  exact Classical.decPred _

private theorem card_clauseAuxPred (r : ℕ) (sat : Bool) :
    Fintype.card {p : Bool × (Fin (r - 1) → Bool) // clauseAuxPred r sat p} =
      if sat then 1 else r + 1 := by
  classical
  by_cases hr0 : r = 0
  · subst hr0
    have e : {p : Bool × (Fin (0 - 1) → Bool) // clauseAuxPred 0 sat p} ≃ Unit :=
      { toFun := fun _ => ()
        invFun := fun _ => ⟨(false, Fin.elim0), by simp [clauseAuxPred]⟩
        left_inv := fun ⟨⟨z, u⟩, hp⟩ => by
          simp only [clauseAuxPred, ↓reduceDIte] at hp
          exact Subtype.ext (Prod.ext hp.symm (funext fun i => Fin.elim0 i))
        right_inv := fun _ => rfl }
    rw [Fintype.card_congr e, Fintype.card_unit]
    cases sat <;> rfl
  by_cases hr1 : r = 1
  · subst hr1
    cases sat
    · have e : {p : Bool × (Fin (1 - 1) → Bool) // clauseAuxPred 1 false p} ≃ Bool :=
        { toFun := fun p => p.1.1
          invFun := fun b => ⟨(b, Fin.elim0), by simp [clauseAuxPred]⟩
          left_inv := fun ⟨⟨z, u⟩, _⟩ =>
            Subtype.ext (Prod.ext rfl (funext fun i => Fin.elim0 i))
          right_inv := fun _ => rfl }
      rw [Fintype.card_congr e, Fintype.card_bool]
      rfl
    · have e : {p : Bool × (Fin (1 - 1) → Bool) // clauseAuxPred 1 true p} ≃ Unit :=
        { toFun := fun _ => ()
          invFun := fun _ => ⟨(false, Fin.elim0), by simp [clauseAuxPred]⟩
          left_inv := fun ⟨⟨z, u⟩, hp⟩ => by
            simp only [clauseAuxPred, one_ne_zero, ↓reduceDIte] at hp
            have hz : z = false := Bool.eq_false_iff.mpr fun h => Bool.noConfusion (hp h)
            exact Subtype.ext (Prod.ext hz.symm (funext fun i => Fin.elim0 i))
          right_inv := fun _ => rfl }
      rw [Fintype.card_congr e, Fintype.card_unit]
      rfl
  · cases sat
    · have e : {p : Bool × (Fin (r - 1) → Bool) // clauseAuxPred r false p} ≃
          Unit ⊕ MonoBools (r - 1) :=
        { toFun := fun ⟨⟨z, u⟩, hp⟩ =>
            if hz : z = false then Sum.inl ()
            else Sum.inr ⟨u, by
              simp only [clauseAuxPred, hr0, ↓reduceDIte, hr1] at hp
              exact hp.2.2⟩
          invFun
            | Sum.inl () => ⟨(false, fun _ => false), by
                simp [clauseAuxPred, hr0, hr1]⟩
            | Sum.inr u => ⟨(true, u.1), by
                simp only [clauseAuxPred, hr0, ↓reduceDIte, hr1]
                exact ⟨fun _ => trivial, fun h => Bool.noConfusion h, u.2⟩⟩
          left_inv := fun ⟨⟨z, u⟩, hp⟩ => by
            simp only [clauseAuxPred, hr0, ↓reduceDIte, hr1] at hp
            dsimp only
            split_ifs with hz
            · refine Subtype.ext (Prod.ext hz.symm (funext fun i => ?_))
              exact (mono_all_false (fun _ => hp.2.1 hz) hp.2.2 i).symm
            · have hzt : z = true := Bool.eq_true_of_not_eq_false hz
              exact Subtype.ext (Prod.ext hzt.symm rfl)
          right_inv := fun x => by
            cases x with
            | inl u => cases u; rfl
            | inr u =>
              dsimp only
              simp only [Bool.true_eq_false, ↓reduceDIte] }
      rw [Fintype.card_congr e, Fintype.card_sum, Fintype.card_unit, card_monoBools]
      simp only [Bool.false_eq_true, ↓reduceIte]
      omega
    · have e : {p : Bool × (Fin (r - 1) → Bool) // clauseAuxPred r true p} ≃ Unit :=
        { toFun := fun _ => ()
          invFun := fun _ => ⟨(false, fun _ => false), by simp [clauseAuxPred, hr0, hr1]⟩
          left_inv := fun ⟨⟨z, u⟩, hp⟩ => by
            simp only [clauseAuxPred, hr0, ↓reduceDIte, hr1] at hp
            have hz : z = false := Bool.eq_false_iff.mpr fun h => Bool.noConfusion (hp.1 h)
            refine Subtype.ext (Prod.ext hz.symm (funext fun i => ?_))
            exact (mono_all_false (fun _ => hp.2.1 hz) hp.2.2 i).symm
          right_inv := fun _ => rfl }
      rw [Fintype.card_congr e, Fintype.card_unit]
      rfl

private def valiantVarEquiv (φ : CNF ℕ) (r : ℕ) :
    ((valiantTwoSAT φ r).vars.toFinset → Bool) ≃
      (φ.vars.toFinset → Bool) × (∀ _ : Fin φ.length, Bool × (Fin (r - 1) → Bool)) where
  toFun τ :=
    (fun v => τ ⟨2 * v.1, List.mem_toFinset.mpr
        ((mem_vars_valiantTwoSAT φ r _).mpr (Or.inl ⟨v.1, List.mem_toFinset.mp v.2, rfl⟩))⟩,
      fun i =>
        (τ ⟨zVar r i.1, List.mem_toFinset.mpr
            ((mem_vars_valiantTwoSAT φ r _).mpr (Or.inr ⟨i.1, i.isLt, Or.inl rfl⟩))⟩,
          fun j => τ ⟨uVar r i.1 j.1, List.mem_toFinset.mpr
            ((mem_vars_valiantTwoSAT φ r _).mpr
              (Or.inr ⟨i.1, i.isLt, Or.inr ⟨j.1, j.isLt, rfl⟩⟩))⟩))
  invFun p w :=
    if hev : w.1 % 2 = 0 then
      let v₀ := w.1 / 2
      have hv₀ : v₀ ∈ φ.vars.toFinset := by
        have hw := (mem_vars_valiantTwoSAT φ r w.1).mp (List.mem_toFinset.mp w.2)
        rcases hw with ⟨v, hv, hwv⟩ | ⟨i, _, hwz | ⟨j, _, hwu⟩⟩
        · have : v₀ = v := by omega
          exact this ▸ List.mem_toFinset.mpr hv
        · rw [hwz] at hev; unfold zVar at hev; omega
        · rw [hwu] at hev; unfold uVar at hev; omega
      p.1 ⟨v₀, hv₀⟩
    else
      let q := (w.1 - 1) / 2
      let i := q / (r + 1)
      let k := q % (r + 1)
      have hi : i < φ.length := by
        have hw := (mem_vars_valiantTwoSAT φ r w.1).mp (List.mem_toFinset.mp w.2)
        rcases hw with ⟨v, _, hwv⟩ | ⟨i', hi', hwz | ⟨j, hj, hwu⟩⟩
        · omega
        · have hq : q = i' * (r + 1) := by dsimp only [q]; rw [hwz]; unfold zVar; omega
          have hdiv : q / (r + 1) = i' := by
            rw [hq, Nat.mul_div_cancel _ (Nat.succ_pos r)]
          change q / (r + 1) < φ.length
          rw [hdiv]
          exact hi'
        · have hq : q = i' * (r + 1) + (j + 1) := by dsimp only [q]; rw [hwu]; unfold uVar; omega
          have hdiv : q / (r + 1) = i' := by
            rw [hq, Nat.add_comm (i' * _), Nat.mul_comm i' _,
              Nat.add_mul_div_left _ _ (Nat.succ_pos r), Nat.div_eq_of_lt (by omega), Nat.zero_add]
          change q / (r + 1) < φ.length
          rw [hdiv]
          exact hi'
      if hk : k = 0 then
        (p.2 ⟨i, hi⟩).1
      else
        have hklt : k - 1 < r - 1 := by
          have hw := (mem_vars_valiantTwoSAT φ r w.1).mp (List.mem_toFinset.mp w.2)
          rcases hw with ⟨v, _, hwv⟩ | ⟨i', _, hwz | ⟨j, hj, hwu⟩⟩
          · omega
          · have hq : q = i' * (r + 1) := by dsimp only [q]; rw [hwz]; unfold zVar; omega
            have hmod : q % (r + 1) = 0 := by rw [hq, Nat.mul_mod_left]
            exact absurd hmod hk
          · have hq : q = i' * (r + 1) + (j + 1) := by
              dsimp only [q]; rw [hwu]; unfold uVar; omega
            have hmod : q % (r + 1) = j + 1 := by
              rw [hq, Nat.add_comm (i' * _), Nat.add_mul_mod_self_right,
                Nat.mod_eq_of_lt (by omega)]
            change q % (r + 1) - 1 < r - 1
            rw [hmod]
            omega
        (p.2 ⟨i, hi⟩).2 ⟨k - 1, hklt⟩
  left_inv τ := by
    ext w
    have hw := (mem_vars_valiantTwoSAT φ r w.1).mp (List.mem_toFinset.mp w.2)
    rcases hw with ⟨v, hv, hwv⟩ | ⟨i, hi, hwz | ⟨j, hj, hwu⟩⟩
    · have hev : w.1 % 2 = 0 := by omega
      simp only [hev, ↓reduceDIte]
      congr 1
      ext
      dsimp only
      omega
    · have hodd : w.1 % 2 ≠ 0 := by rw [hwz]; unfold zVar; omega
      have hq : (w.1 - 1) / 2 = i * (r + 1) := by rw [hwz]; unfold zVar; omega
      have hdiv : (w.1 - 1) / 2 / (r + 1) = i := by
        rw [hq, Nat.mul_div_cancel _ (Nat.succ_pos r)]
      have hmod : (w.1 - 1) / 2 % (r + 1) = 0 := by rw [hq, Nat.mul_mod_left]
      simp only [hodd, ↓reduceDIte, hmod]
      congr 1
      exact Subtype.ext (by dsimp only; rw [hdiv, ← hwz])
    · have hodd : w.1 % 2 ≠ 0 := by rw [hwu]; unfold uVar; omega
      have hq : (w.1 - 1) / 2 = i * (r + 1) + (j + 1) := by rw [hwu]; unfold uVar; omega
      have hdiv : (w.1 - 1) / 2 / (r + 1) = i := by
        rw [hq, Nat.add_comm (i * _), Nat.mul_comm i _,
          Nat.add_mul_div_left _ _ (Nat.succ_pos r), Nat.div_eq_of_lt (by omega), Nat.zero_add]
      have hmod : (w.1 - 1) / 2 % (r + 1) = j + 1 := by
        rw [hq, Nat.add_comm (i * _), Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
      simp only [hodd, ↓reduceDIte, hmod, Nat.succ_ne_zero, Nat.add_sub_cancel]
      congr 1
      exact Subtype.ext (by dsimp only; rw [hdiv, ← hwu])
  right_inv p := by
    obtain ⟨σ, aux⟩ := p
    refine Prod.ext (funext fun x => ?_) (funext fun i => Prod.ext ?_ (funext fun j => ?_))
    · dsimp only
      have hev : (2 * x.1) % 2 = 0 := by omega
      simp only [hev, ↓reduceDIte]
      congr 1
      ext
      dsimp only
      omega
    · dsimp only
      have hodd : zVar r i.1 % 2 ≠ 0 := by unfold zVar; omega
      have hq : (zVar r i.1 - 1) / 2 = i.1 * (r + 1) := by unfold zVar; omega
      have hdiv : (zVar r i.1 - 1) / 2 / (r + 1) = i.1 := by
        rw [hq, Nat.mul_div_cancel _ (Nat.succ_pos r)]
      have hmod : (zVar r i.1 - 1) / 2 % (r + 1) = 0 := by rw [hq, Nat.mul_mod_left]
      simp only [hodd, ↓reduceDIte, hmod]
      exact congrArg (fun k => (aux k).1) (Fin.ext hdiv)
    · dsimp only
      have hodd : uVar r i.1 j.1 % 2 ≠ 0 := by unfold uVar; omega
      have hq : (uVar r i.1 j.1 - 1) / 2 = i.1 * (r + 1) + (j.1 + 1) := by unfold uVar; omega
      have hdiv : (uVar r i.1 j.1 - 1) / 2 / (r + 1) = i.1 := by
        rw [hq, Nat.add_comm (i.1 * _), Nat.mul_comm i.1 _,
          Nat.add_mul_div_left _ _ (Nat.succ_pos r), Nat.div_eq_of_lt (by omega), Nat.zero_add]
      have hmod : (uVar r i.1 j.1 - 1) / 2 % (r + 1) = j.1 + 1 := by
        rw [hq, Nat.add_comm (i.1 * _), Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
      simp only [hodd, ↓reduceDIte, hmod, Nat.succ_ne_zero, Nat.add_sub_cancel]
      exact congr (congrArg (fun k => (aux k).2) (Fin.ext hdiv)) (Fin.ext rfl)

private theorem eval_valiantTwoSAT_iff (φ : CNF ℕ) (r : ℕ)
    (τ : (valiantTwoSAT φ r).vars.toFinset → Bool) :
    let τExt (w : ℕ) : Bool :=
      if hw : w ∈ (valiantTwoSAT φ r).vars.toFinset then τ ⟨w, hw⟩ else false
    let p := valiantVarEquiv φ r τ
    let σExt (v : ℕ) : Bool := if hv : v ∈ φ.vars.toFinset then p.1 ⟨v, hv⟩ else false
    (valiantTwoSAT φ r).eval τExt = true ↔
      ∀ i : Fin φ.length, clauseAuxPred r (φ[i].eval σExt) (p.2 i) := by
  intro τExt p σExt
  have hσEq : ∀ v ∈ φ.vars, τExt (2 * v) = σExt v := by
    intro v hv
    have hv' : v ∈ φ.vars.toFinset := List.mem_toFinset.mpr hv
    have hw : 2 * v ∈ (valiantTwoSAT φ r).vars.toFinset :=
      List.mem_toFinset.mpr ((mem_vars_valiantTwoSAT φ r _).mpr (Or.inl ⟨v, hv, rfl⟩))
    simp only [τExt, σExt, hv', hw, ↓reduceDIte, p, valiantVarEquiv, Equiv.coe_fn_mk]
  have hzEq : ∀ i : Fin φ.length, τExt (zVar r i.1) = (p.2 i).1 := by
    intro i
    have hw : zVar r i.1 ∈ (valiantTwoSAT φ r).vars.toFinset :=
      List.mem_toFinset.mpr ((mem_vars_valiantTwoSAT φ r _).mpr (Or.inr ⟨i.1, i.isLt, Or.inl rfl⟩))
    simp only [τExt, hw, ↓reduceDIte, p, valiantVarEquiv, Equiv.coe_fn_mk]
  have huEq : ∀ (i : Fin φ.length) (j : Fin (r - 1)), τExt (uVar r i.1 j.1) = (p.2 i).2 j := by
    intro i j
    have hw : uVar r i.1 j.1 ∈ (valiantTwoSAT φ r).vars.toFinset :=
      List.mem_toFinset.mpr
        ((mem_vars_valiantTwoSAT φ r _).mpr (Or.inr ⟨i.1, i.isLt, Or.inr ⟨j.1, j.isLt, rfl⟩⟩))
    simp only [τExt, hw, ↓reduceDIte, p, valiantVarEquiv, Equiv.coe_fn_mk]
  rw [valiantTwoSAT, CNF.eval_append, Bool.and_eq_true, CNF.eval_flatMap_eq_true_iff]
  have htaut : (valiantVarTauts φ).eval τExt = true := by
    rw [valiantVarTauts, CNF.eval_eq_true_iff]
    intro c hc
    obtain ⟨v, _, rfl⟩ := List.mem_map.mp hc
    cases τExt (2 * v) <;> simp [Clause.eval, Literal.eval]
  rw [iff_true_intro htaut, true_and]
  constructor
  · intro h i
    have hci := h (φ[i], i.1)
      (List.mem_zipIdx_iff_getElem?.mpr (List.getElem?_eq_some_iff.mpr ⟨i.isLt, rfl⟩))
    rw [valiantClauseGadget, CNF.eval_append, Bool.and_eq_true] at hci
    have hlit : (p.2 i).1 = true → φ[i].eval σExt = false := by
      intro hz
      by_contra hsat
      have hsat' : φ[i].eval σExt = true := Bool.eq_true_of_not_eq_false hsat
      rw [Clause.eval_eq_true_iff] at hsat'
      obtain ⟨l, hl, hleval⟩ := hsat'
      have hmem : l.1 ∈ φ.vars :=
        List.mem_map.mpr ⟨l, List.mem_flatten.mpr ⟨φ[i], List.getElem_mem .., hl⟩, rfl⟩
      have hcl : Clause.eval τExt [(zVar r i.1, false), (2 * l.1, !l.2)] = true :=
        (CNF.eval_eq_true_iff τExt _).mp hci.1 _ (List.mem_map.mpr ⟨l, hl, rfl⟩)
      simp only [Clause.eval_cons, Clause.eval_nil, Bool.or_false, Bool.or_eq_true, Literal.eval,
        beq_iff_eq, hzEq i, hz, Bool.true_eq_false, false_or, hσEq l.1 hmem] at hcl
      cases hb : l.2 <;> rw [hb] at hleval hcl <;> exact Bool.noConfusion (hleval.symm.trans hcl)
    have haux := hci.2
    dsimp only at haux
    unfold clauseAuxPred
    split_ifs with hr0 hr1
    · simp only [hr0, ↓reduceIte, CNF.eval_cons, CNF.eval_nil, Bool.and_true, Clause.eval_cons,
        Clause.eval_nil, Bool.or_false, Literal.eval, beq_iff_eq] at haux
      rw [← hr0, hzEq i] at haux
      exact haux
    · exact hlit
    · simp only [hr0, ↓reduceIte, hr1, CNF.eval_append, Bool.and_eq_true, CNF.eval_cons,
        CNF.eval_nil, Bool.and_true, CNF.eval_eq_true_iff, List.mem_map, List.mem_range,
        forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, Clause.eval_cons,
        Clause.eval_nil, Bool.or_false, Bool.or_eq_true, Literal.eval, beq_iff_eq, hzEq i]
        at haux
      refine ⟨hlit, fun hz => ?_, fun j hj hfj => ?_⟩
      · rcases haux.1.2 with h1 | h2
        · simp [hz] at h1
        · simpa [huEq i ⟨0, by omega⟩] using h2
      · rcases haux.2 j (by omega) with h1 | h2
        · simp [huEq i ⟨j, by omega⟩, hfj] at h1
        · simpa [huEq i ⟨j + 1, hj⟩] using h2
  · intro h ⟨c, i⟩ hci
    have hget := List.mem_zipIdx_iff_getElem?.mp hci
    have hi : i < φ.length := (List.getElem?_eq_some_iff.mp hget).1
    have hc : c = φ[i] := (List.getElem?_eq_some_iff.mp hget).2.symm
    subst hc
    have hiPred := h ⟨i, hi⟩
    rw [valiantClauseGadget, CNF.eval_append, Bool.and_eq_true]
    refine ⟨?_, ?_⟩
    · rw [CNF.eval_eq_true_iff]
      intro cl hcl
      obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hcl
      simp only [Clause.eval_cons, Clause.eval_nil, Bool.or_false, Bool.or_eq_true, Literal.eval,
        beq_iff_eq, hzEq ⟨i, hi⟩]
      by_cases hz : (p.2 ⟨i, hi⟩).1 = false
      · exact Or.inl hz
      · have hzt : (p.2 ⟨i, hi⟩).1 = true := Bool.eq_true_of_not_eq_false hz
        have hunsat : φ[i].eval σExt = false := by
          unfold clauseAuxPred at hiPred
          split_ifs at hiPred with hr0 hr1
          · simp [hzt] at hiPred
          · exact hiPred hzt
          · exact hiPred.1 hzt
        have hmem : l.1 ∈ φ.vars :=
          List.mem_map.mpr ⟨l, List.mem_flatten.mpr ⟨φ[i], List.getElem_mem .., hl⟩, rfl⟩
        have hle := (Clause.eval_eq_false_iff σExt φ[i]).mp hunsat l hl
        rw [hσEq l.1 hmem]
        exact Or.inr hle
    · dsimp only
      unfold clauseAuxPred at hiPred
      split_ifs with hr0 hr1
      · simp only [hr0, ↓reduceDIte] at hiPred
        simp [CNF.eval_cons, Clause.eval_cons, Literal.eval, hzEq ⟨i, hi⟩, hiPred]
      · simp [CNF.eval_cons, Clause.eval_cons, Literal.eval]
      · simp only [hr0, ↓reduceDIte, hr1] at hiPred
        simp only [CNF.eval_append, Bool.and_eq_true, CNF.eval_cons, CNF.eval_nil, Bool.and_true,
          CNF.eval_eq_true_iff, List.mem_map, List.mem_range, forall_exists_index, and_imp,
          forall_apply_eq_imp_iff₂, Clause.eval_cons, Clause.eval_nil, Bool.or_false,
          Bool.or_eq_true, Literal.eval, beq_iff_eq, hzEq ⟨i, hi⟩]
        refine ⟨⟨by cases (p.2 ⟨i, hi⟩).1 <;> simp, ?_⟩, fun j hj => ?_⟩
        · by_cases hz : (p.2 ⟨i, hi⟩).1 = true
          · exact Or.inl hz
          · have hzf : (p.2 ⟨i, hi⟩).1 = false := Bool.eq_false_iff.mpr hz
            exact Or.inr (by simpa [huEq ⟨i, hi⟩ ⟨0, by omega⟩] using hiPred.2.1 hzf)
        · by_cases hj1 : (p.2 ⟨i, hi⟩).2 ⟨j, by omega⟩ = true
          · exact Or.inl (by simpa [huEq ⟨i, hi⟩ ⟨j, by omega⟩] using hj1)
          · have hfj : (p.2 ⟨i, hi⟩).2 ⟨j, by omega⟩ = false := Bool.eq_false_iff.mpr hj1
            exact Or.inr
              (by simpa [huEq ⟨i, hi⟩ ⟨j + 1, by omega⟩] using hiPred.2.2 j (by omega) hfj)

private theorem countUnsat_eq_card_filter (φ : CNF ℕ) (σ : ℕ → Bool) :
    φ.countUnsat σ = (Finset.univ.filter fun i : Fin φ.length => φ[i].eval σ = false).card := by
  rw [CNF.countUnsat]
  induction φ with
  | nil => simp
  | cons c cs ih =>
    simp only [List.countP_cons, List.length_cons, Fin.card_filter_univ_succ']
    cases hc : c.eval σ
    · simp [hc, ih]
      omega
    · simp [hc, ih]

/-- **Exact model count of Valiant's `2-CNF` formula**:
`SharpTwoSAT (valiantTwoSAT φ r) = ∑ σ : φ.vars.toFinset → Bool, (r + 1) ^ (φ.countUnsat ext(σ))`.
-/
theorem modelCount_valiantTwoSAT (φ : CNF ℕ) (r : ℕ) :
    (valiantTwoSAT φ r).modelCount =
      ∑ σ : φ.vars.toFinset → Bool,
        (r + 1) ^ (φ.countUnsat
          fun v => if hv : v ∈ φ.vars.toFinset then σ ⟨v, hv⟩ else false) := by
  classical
  rw [← CNF.modelCountOn_vars, CNF.modelCountOn, ← Fintype.card_coe]
  let e : {τ : (valiantTwoSAT φ r).vars.toFinset → Bool //
        (valiantTwoSAT φ r).eval
          (fun w => if hw : w ∈ (valiantTwoSAT φ r).vars.toFinset then τ ⟨w, hw⟩ else false) =
            true} ≃
      Σ σ : φ.vars.toFinset → Bool,
        ∀ i : Fin φ.length,
          {p : Bool × (Fin (r - 1) → Bool) //
            clauseAuxPred r
              (φ[i].eval fun v => if hv : v ∈ φ.vars.toFinset then σ ⟨v, hv⟩ else false) p} :=
    { toFun := fun ⟨τ, hτ⟩ =>
        ⟨(valiantVarEquiv φ r τ).1, fun i =>
          ⟨(valiantVarEquiv φ r τ).2 i,
            (eval_valiantTwoSAT_iff φ r τ).mp (by simpa using hτ) i⟩⟩
      invFun := fun ⟨σ, aux⟩ =>
        ⟨(valiantVarEquiv φ r).symm (σ, fun i => (aux i).1), by
          refine (eval_valiantTwoSAT_iff φ r _).mpr fun i => ?_
          have hp := (valiantVarEquiv φ r).apply_symm_apply (σ, fun i => (aux i).1)
          exact (congrArg (fun p : (φ.vars.toFinset → Bool) ×
              (∀ _ : Fin φ.length, Bool × (Fin (r - 1) → Bool)) =>
            clauseAuxPred r (φ[i].eval fun v =>
              if hv : v ∈ φ.vars.toFinset then p.1 ⟨v, hv⟩ else false) (p.2 i)) hp).mpr
              (aux i).2⟩
      left_inv := fun ⟨τ, hτ⟩ => Subtype.ext ((valiantVarEquiv φ r).symm_apply_apply τ)
      right_inv := fun ⟨σ, aux⟩ => by
        have hp := (valiantVarEquiv φ r).apply_symm_apply (σ, fun i => (aux i).1)
        dsimp only
        refine Sigma.ext (congrArg Prod.fst hp) ?_
        refine Function.hfunext rfl fun i j hij => ?_
        subst hij
        refine (Subtype.heq_iff_coe_eq fun x => ?_).mpr (congrFun (congrArg Prod.snd hp) i)
        dsimp only
        rw [congrArg Prod.fst hp] }
  rw [Fintype.card_congr ((Equiv.subtypeEquivRight (by simp)).trans e)]
  rw [Fintype.card_sigma]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Fintype.card_pi]
  let σExt (v : ℕ) : Bool := if hv : v ∈ φ.vars.toFinset then σ ⟨v, hv⟩ else false
  have hprod : (∏ i : Fin φ.length,
      Fintype.card {p : Bool × (Fin (r - 1) → Bool) //
        clauseAuxPred r (φ[i].eval σExt) p}) =
      ∏ i : Fin φ.length, (if φ[i].eval σExt then 1 else r + 1) := by
    refine Finset.prod_congr rfl fun i _ => ?_
    convert card_clauseAuxPred r (φ[i].eval σExt)
  rw [hprod]
  have hfilt : (Finset.univ.filter fun i : Fin φ.length => ¬(φ[i].eval σExt = true)) =
      Finset.univ.filter fun i : Fin φ.length => φ[i].eval σExt = false :=
    Finset.filter_congr fun i _ => eq_iff_iff.mp (Bool.not_eq_true _)
  have hpow : (∏ i : Fin φ.length, (if φ[i].eval σExt then 1 else r + 1)) =
      (r + 1) ^ (Finset.univ.filter fun i : Fin φ.length => φ[i].eval σExt = false).card := by
    rw [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const, hfilt]
  rw [hpow]
  congr 1
  exact (countUnsat_eq_card_filter φ σExt).symm

/-! ### Binomial finite-difference interpolation over `ℤ` and `ℕ` -/

/-- Exact integer finite-difference identity recovering `SharpSAT φ` from the `2-CNF` counts
`SharpTwoSAT (valiantTwoSAT φ r)` for `r = 0, …, φ.length`. -/
theorem SharpSAT_eq_valiant_sum_int (φ : CNF ℕ) :
    (SharpSAT φ : ℤ) =
      ∑ r ∈ Finset.range (φ.length + 1),
        (-1 : ℤ) ^ r * ((φ.length + 1).choose (r + 1) : ℤ) *
          (SharpTwoSAT (valiantTwoSAT φ r) : ℤ) := by
  classical
  let P : Polynomial ℤ :=
    ∑ σ : φ.vars.toFinset → Bool,
      Polynomial.X ^ (φ.countUnsat fun v => if hv : v ∈ φ.vars.toFinset then σ ⟨v, hv⟩ else false)
  have hdeg : P.natDegree ≤ φ.length := by
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun σ _ => ?_
    exact (Polynomial.natDegree_X_pow_le _).trans (CNF.countUnsat_le_length _ _)
  have hevalP (x : ℤ) : P.eval x = ∑ σ : φ.vars.toFinset → Bool,
      x ^ (φ.countUnsat fun v => if hv : v ∈ φ.vars.toFinset then σ ⟨v, hv⟩ else false) := by
    simpa only [P, Polynomial.coe_evalRingHom, Polynomial.eval_pow, Polynomial.eval_X] using
      map_sum (Polynomial.evalRingHom x)
        (fun σ : φ.vars.toFinset → Bool =>
          Polynomial.X ^
            (φ.countUnsat fun v => if hv : v ∈ φ.vars.toFinset then σ ⟨v, hv⟩ else false))
        Finset.univ
  have hP0 : P.eval 0 = (SharpSAT φ : ℤ) := by
    rw [SharpSAT, ← CNF.modelCountOn_vars, CNF.modelCountOn, hevalP 0]
    have hcard : ((Finset.univ.filter fun σ : φ.vars.toFinset → Bool =>
        φ.eval (fun v => if hv : v ∈ φ.vars.toFinset then σ ⟨v, hv⟩ else false) = true).card :
          ℤ) =
        ∑ σ : φ.vars.toFinset → Bool,
          if φ.eval (fun v => if hv : v ∈ φ.vars.toFinset then σ ⟨v, hv⟩ else false) = true then
            (1 : ℤ)
          else 0 := by
      simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    rw [hcard]
    refine Finset.sum_congr rfl fun σ _ => ?_
    let σExt (v : ℕ) : Bool := if hv : v ∈ φ.vars.toFinset then σ ⟨v, hv⟩ else false
    change (0 : ℤ) ^ φ.countUnsat σExt = if φ.eval σExt = true then (1 : ℤ) else 0
    by_cases h0 : φ.countUnsat σExt = 0
    · rw [h0, pow_zero]
      simp only [CNF.countUnsat_eq_zero_iff.mp h0, ↓reduceIte]
    · have hnev : φ.eval σExt = false :=
        Bool.eq_false_iff.mpr fun h => h0 (CNF.countUnsat_eq_zero_iff.mpr h)
      rw [zero_pow h0, hnev]
      simp only [Bool.false_eq_true, ↓reduceIte]
  have hPr (r : ℕ) : P.eval ((r : ℤ) + 1) = (SharpTwoSAT (valiantTwoSAT φ r) : ℤ) := by
    rw [SharpTwoSAT_valiantTwoSAT, modelCount_valiantTwoSAT, hevalP ((r : ℤ) + 1)]
    simp only [Nat.cast_sum, Nat.cast_pow, Nat.cast_add, Nat.cast_one]
  have hid := Polynomial.eval_zero_eq_sum_neg_one_pow_choose_eval_succ hdeg
  rw [hP0] at hid
  refine hid.trans (Finset.sum_congr rfl fun r _ => ?_)
  rw [hPr r]

/-- Pure nonnegative combination recovering `SharpSAT φ` from the list of `r = 0..φ.length`
answers `[SharpTwoSAT (valiantTwoSAT φ 0), …, SharpTwoSAT (valiantTwoSAT φ φ.length)]`. -/
@[expose] def valiantCombine (p : CNF ℕ × List ℕ) : ℕ :=
  let m := p.1.length
  let posSum := ((p.2.zipIdx).map fun x =>
    if !x.2.testBit 0 then (m + 1).choose (x.2 + 1) * x.1 else 0).sum
  let negSum := ((p.2.zipIdx).map fun x =>
    if x.2.testBit 0 then (m + 1).choose (x.2 + 1) * x.1 else 0).sum
  posSum - negSum

theorem valiantCombine_spec (φ : CNF ℕ) :
    valiantCombine (φ, (List.range (φ.length + 1)).map fun r =>
        SharpTwoSAT (valiantTwoSAT φ r)) = SharpSAT φ := by
  let vals := (List.range (φ.length + 1)).map fun r => SharpTwoSAT (valiantTwoSAT φ r)
  have hzip : vals.zipIdx =
      (List.range (φ.length + 1)).map fun r => (SharpTwoSAT (valiantTwoSAT φ r), r) := by
    apply List.ext_getElem (by simp [vals]) fun i hi _ => by
      simp only [List.length_zipIdx] at hi
      simp [vals]
  have hhalf (wantOdd : Bool) :
      ((((vals.zipIdx).map fun x =>
        if x.2.testBit 0 = wantOdd then (φ.length + 1).choose (x.2 + 1) * x.1 else 0).sum :
          ℕ) : ℤ) =
        ∑ r ∈ Finset.range (φ.length + 1),
          if r % 2 = (if wantOdd then 1 else 0) then
            ((φ.length + 1).choose (r + 1) * SharpTwoSAT (valiantTwoSAT φ r) : ℤ)
          else 0 := by
    rw [hzip, List.map_map, List.sum_map_range, Fin.sum_univ_eq_sum_range, Nat.cast_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    dsimp only [Function.comp_apply]
    by_cases hr2 : r % 2 = 0
    · have htb : r.testBit 0 = false := by simp [Nat.testBit_zero, hr2]
      cases wantOdd <;> simp [htb, hr2]
    · have hr1 : r % 2 = 1 := by omega
      have htb : r.testBit 0 = true := by simp [Nat.testBit_zero, hr1]
      cases wantOdd <;> simp [htb, hr1]
  have hpos : ((((vals.zipIdx).map fun x =>
      if !x.2.testBit 0 then (φ.length + 1).choose (x.2 + 1) * x.1 else 0).sum : ℕ) : ℤ) =
      ∑ r ∈ Finset.range (φ.length + 1),
        if r % 2 = 0 then ((φ.length + 1).choose (r + 1) * SharpTwoSAT (valiantTwoSAT φ r) : ℤ)
        else 0 := by
    simpa only [Bool.not_eq_true', Bool.false_eq_true, ↓reduceIte] using hhalf false
  have hneg : ((((vals.zipIdx).map fun x =>
      if x.2.testBit 0 then (φ.length + 1).choose (x.2 + 1) * x.1 else 0).sum : ℕ) : ℤ) =
      ∑ r ∈ Finset.range (φ.length + 1),
        if r % 2 = 1 then ((φ.length + 1).choose (r + 1) * SharpTwoSAT (valiantTwoSAT φ r) : ℤ)
        else 0 :=
    hhalf true
  have hdiff : ((valiantCombine (φ, vals) : ℤ)) =
      ∑ r ∈ Finset.range (φ.length + 1),
        (-1 : ℤ) ^ r * ((φ.length + 1).choose (r + 1) : ℤ) *
          (SharpTwoSAT (valiantTwoSAT φ r) : ℤ) := by
    have hsplit : (∑ r ∈ Finset.range (φ.length + 1),
        (-1 : ℤ) ^ r * ((φ.length + 1).choose (r + 1) : ℤ) *
          (SharpTwoSAT (valiantTwoSAT φ r) : ℤ)) =
        (∑ r ∈ Finset.range (φ.length + 1),
          if r % 2 = 0 then ((φ.length + 1).choose (r + 1) * SharpTwoSAT (valiantTwoSAT φ r) : ℤ)
          else 0) -
        ∑ r ∈ Finset.range (φ.length + 1),
          if r % 2 = 1 then ((φ.length + 1).choose (r + 1) * SharpTwoSAT (valiantTwoSAT φ r) : ℤ)
          else 0 := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun r _ => ?_
      rcases Nat.mod_two_eq_zero_or_one r with hr0 | hr1
      · have hs : (-1 : ℤ) ^ r = 1 := Even.neg_one_pow (Nat.even_iff.mpr hr0)
        simp [hr0, hs]
      · have hs : (-1 : ℤ) ^ r = -1 := Odd.neg_one_pow (Nat.odd_iff.mpr hr1)
        simp [hr1, hs]
    have hnatle :
        ((vals.zipIdx).map fun x =>
          if x.2.testBit 0 then (φ.length + 1).choose (x.2 + 1) * x.1 else 0).sum ≤
        ((vals.zipIdx).map fun x =>
          if !x.2.testBit 0 then (φ.length + 1).choose (x.2 + 1) * x.1 else 0).sum := by
      have hs0 : 0 ≤ (SharpSAT φ : ℤ) := Nat.cast_nonneg _
      rw [SharpSAT_eq_valiant_sum_int, hsplit, ← hpos, ← hneg] at hs0
      exact Int.ofNat_le.mp (Int.sub_nonneg.mp hs0)
    unfold valiantCombine
    dsimp only [vals]
    rw [Int.ofNat_sub hnatle, hpos, hneg, ← hsplit]
  exact Int.ofNat.inj (hdiff.trans (SharpSAT_eq_valiant_sum_int φ).symm)

/-! ### Polynomial-time certificates and `#P`-completeness of `#2SAT` -/

private theorem computableInPolyTime_zVar :
    ComputableInPolyTime (fun p : ℕ × ℕ => zVar p.1 p.2)
      (encPair encUnary encUnary) encNat := by
  unfold zVar
  exact ComputableTidilyInPolyTime.unary_to_binary.computableInPolyTime.comp
    (by fun_prop)

private theorem computableInPolyTime_uVar :
    ComputableInPolyTime (fun p : (ℕ × ℕ) × ℕ => uVar p.1.1 p.1.2 p.2)
      (encPair (encPair encUnary encUnary) encUnary) encNat := by
  unfold uVar
  exact ComputableTidilyInPolyTime.unary_to_binary.computableInPolyTime.comp
    (by fun_prop)

private theorem computableInPolyTime_valiantVarTauts :
    ComputableInPolyTime valiantVarTauts encCNF encCNF := by
  unfold valiantVarTauts
  have hd : ComputableTidilyInPolyTime (CNF.distinctVars (V := ℕ)) encCNF (encList encNat) :=
    SAT.computableInPolyTime_distinctVars.tidy
  have hmap : ComputableTidilyInPolyTime
      (fun v : ℕ => ([(2 * v, true), (2 * v, false)] : Clause ℕ))
      encNat (encClause encNat) := by
    have hv : ComputableInPolyTime (fun v : ℕ => 2 * v) encNat encNat := by
      have h : ComputableInPolyTime (fun v : ℕ => v + v) encNat encNat :=
        ComputableInPolyTime.binary_add' ComputableInPolyTime.id' ComputableInPolyTime.id'
      convert h using 1
      funext v
      omega
    have hvt := hv.tidy
    fun_prop
  exact (ComputableTidilyInPolyTime.map hmap |>.comp hd).computableInPolyTime

private theorem computableInPolyTime_valiantClauseGadget :
    ComputableInPolyTime (fun p : ℕ × (Clause ℕ × ℕ) => valiantClauseGadget p.1 p.2)
      (encPair encUnary (encPair (encClause encNat) encUnary)) encCNF := by
  unfold valiantClauseGadget
  have hz : ComputableTidilyInPolyTime
      (fun p : ℕ × (Clause ℕ × ℕ) => zVar p.1 p.2.2)
      (encPair encUnary (encPair (encClause encNat) encUnary)) encNat :=
    (computableInPolyTime_zVar.comp
      ((ComputableInPolyTime.fst _ _).prod
        ((ComputableInPolyTime.snd _ _).comp (ComputableInPolyTime.snd _ _)))).tidy
  have hlit : ComputableTidilyInPolyTime
      (fun p : ℕ × (Clause ℕ × ℕ) =>
        p.2.1.map fun l => [(zVar p.1 p.2.2, false), (2 * l.1, !l.2)])
      (encPair encUnary (encPair (encClause encNat) encUnary)) encCNF := by
    have hlist : ComputableTidilyInPolyTime
        (fun p : ℕ × (Clause ℕ × ℕ) => p.2.1)
        (encPair encUnary (encPair (encClause encNat) encUnary))
        (encList (encPair encNat encBool)) :=
      (ComputableTidilyInPolyTime.fst _ _).comp (ComputableTidilyInPolyTime.snd _ _)
    have hbody : ComputableTidilyInPolyTime
        (fun q : (ℕ × (Clause ℕ × ℕ)) × Literal ℕ =>
          ([(zVar q.1.1 q.1.2.2, false), (2 * q.2.1, !q.2.2)] : Clause ℕ))
        (encPair (encPair encUnary (encPair (encClause encNat) encUnary))
          (encPair encNat encBool))
        (encClause encNat) := by
      have hz' : ComputableTidilyInPolyTime
          (fun q : (ℕ × (Clause ℕ × ℕ)) × Literal ℕ => zVar q.1.1 q.1.2.2)
          (encPair (encPair encUnary (encPair (encClause encNat) encUnary))
            (encPair encNat encBool)) encNat :=
        hz.comp (ComputableTidilyInPolyTime.fst _ _)
      have hv2 : ComputableTidilyInPolyTime
          (fun q : (ℕ × (Clause ℕ × ℕ)) × Literal ℕ => 2 * q.2.1)
          (encPair (encPair encUnary (encPair (encClause encNat) encUnary))
            (encPair encNat encBool)) encNat := by
        have h : ComputableInPolyTime
            (fun q : (ℕ × (Clause ℕ × ℕ)) × Literal ℕ => q.2.1 + q.2.1)
            (encPair (encPair encUnary (encPair (encClause encNat) encUnary))
              (encPair encNat encBool)) encNat := by
          have hv : ComputableInPolyTime
              (fun q : (ℕ × (Clause ℕ × ℕ)) × Literal ℕ => q.2.1)
              (encPair (encPair encUnary (encPair (encClause encNat) encUnary))
                (encPair encNat encBool)) encNat :=
            (ComputableInPolyTime.fst _ _).comp (ComputableInPolyTime.snd _ _)
          exact ComputableInPolyTime.binary_add' hv hv
        convert h.tidy using 1
        funext q
        omega
      fun_prop
    exact ComputableTidilyInPolyTime.mapWithInput hlist hbody
  have haux : ComputableTidilyInPolyTime
      (fun p : ℕ × (Clause ℕ × ℕ) =>
        if p.1 = 0 then [[(zVar p.1 p.2.2, false)]]
        else if p.1 = 1 then [[(zVar p.1 p.2.2, true), (zVar p.1 p.2.2, false)]]
        else
          [[(zVar p.1 p.2.2, true), (zVar p.1 p.2.2, false)],
              [(zVar p.1 p.2.2, true), (uVar p.1 p.2.2 0, false)]] ++
            (List.range (p.1 - 2)).map fun j =>
              [(uVar p.1 p.2.2 j, true), (uVar p.1 p.2.2 (j + 1), false)])
      (encPair encUnary (encPair (encClause encNat) encUnary)) encCNF := by
    have hu0 : ComputableTidilyInPolyTime
        (fun p : ℕ × (Clause ℕ × ℕ) => uVar p.1 p.2.2 0)
        (encPair encUnary (encPair (encClause encNat) encUnary)) encNat :=
      (computableInPolyTime_uVar.comp
        (((ComputableInPolyTime.fst _ _).prod
          ((ComputableInPolyTime.snd _ _).comp (ComputableInPolyTime.snd _ _))).prod
          (ComputableInPolyTime.const 0))).tidy
    have hchain : ComputableTidilyInPolyTime
        (fun p : ℕ × (Clause ℕ × ℕ) =>
          (List.range (p.1 - 2)).map fun j =>
            [(uVar p.1 p.2.2 j, true), (uVar p.1 p.2.2 (j + 1), false)])
        (encPair encUnary (encPair (encClause encNat) encUnary)) encCNF := by
      have hr : ComputableTidilyInPolyTime
          (fun p : ℕ × (Clause ℕ × ℕ) => List.range (p.1 - 2))
          (encPair encUnary (encPair (encClause encNat) encUnary)) (encList encUnary) := by
        fun_prop
      have hb : ComputableTidilyInPolyTime
          (fun q : (ℕ × (Clause ℕ × ℕ)) × ℕ =>
            ([(uVar q.1.1 q.1.2.2 q.2, true),
              (uVar q.1.1 q.1.2.2 (q.2 + 1), false)] : Clause ℕ))
          (encPair (encPair encUnary (encPair (encClause encNat) encUnary)) encUnary)
          (encClause encNat) := by
        have hu1 : ComputableTidilyInPolyTime
            (fun q : (ℕ × (Clause ℕ × ℕ)) × ℕ => uVar q.1.1 q.1.2.2 q.2)
            (encPair (encPair encUnary (encPair (encClause encNat) encUnary)) encUnary) encNat :=
          (computableInPolyTime_uVar.comp
            ((((ComputableInPolyTime.fst _ _).comp (ComputableInPolyTime.fst _ _)).prod
              ((ComputableInPolyTime.snd _ _).comp
                ((ComputableInPolyTime.snd _ _).comp (ComputableInPolyTime.fst _ _)))).prod
              (ComputableInPolyTime.snd _ _))).tidy
        have hu2 : ComputableTidilyInPolyTime
            (fun q : (ℕ × (Clause ℕ × ℕ)) × ℕ => uVar q.1.1 q.1.2.2 (q.2 + 1))
            (encPair (encPair encUnary (encPair (encClause encNat) encUnary)) encUnary) encNat :=
          (computableInPolyTime_uVar.comp
            ((((ComputableInPolyTime.fst _ _).comp (ComputableInPolyTime.fst _ _)).prod
              ((ComputableInPolyTime.snd _ _).comp
                ((ComputableInPolyTime.snd _ _).comp (ComputableInPolyTime.fst _ _)))).prod
              ((ComputableTidilyInPolyTime.unary_add.comp
                ((ComputableTidilyInPolyTime.snd _ _).prod
                  (ComputableTidilyInPolyTime.const 1))).computableInPolyTime))).tidy
        fun_prop
      exact ComputableTidilyInPolyTime.mapWithInput hr hb
    have hbranch : ComputableTidilyInPolyTime
        (fun p : ℕ × (Clause ℕ × ℕ) =>
          [[(zVar p.1 p.2.2, true), (zVar p.1 p.2.2, false)],
              [(zVar p.1 p.2.2, true), (uVar p.1 p.2.2 0, false)]] ++
            (List.range (p.1 - 2)).map fun j =>
              [(uVar p.1 p.2.2 j, true), (uVar p.1 p.2.2 (j + 1), false)])
        (encPair encUnary (encPair (encClause encNat) encUnary)) encCNF := by
      fun_prop
    have hr0 : ComputableTidilyInPolyTime
        (fun p : ℕ × (Clause ℕ × ℕ) => decide (p.1 = 0))
        (encPair encUnary (encPair (encClause encNat) encUnary)) encBool :=
      (ComputableInPolyTime.unary_eq'
        (ComputableInPolyTime.fst _ _) (ComputableInPolyTime.const 0)).tidy
    have hr1 : ComputableTidilyInPolyTime
        (fun p : ℕ × (Clause ℕ × ℕ) => decide (p.1 = 1))
        (encPair encUnary (encPair (encClause encNat) encUnary)) encBool :=
      (ComputableInPolyTime.unary_eq'
        (ComputableInPolyTime.fst _ _) (ComputableInPolyTime.const 1)).tidy
    exact ComputableTidilyInPolyTime.ite_decide hr0 (by fun_prop)
      (ComputableTidilyInPolyTime.ite_decide hr1 (by fun_prop) hbranch)
  exact ((ComputableTidilyInPolyTime.listAppend (encClause encNat)).comp
    (hlit.prod haux)).computableInPolyTime

private theorem computableInPolyTime_valiantTwoSAT :
    ComputableInPolyTime (fun p : CNF ℕ × ℕ => valiantTwoSAT p.1 p.2)
      (encPair encCNF encUnary) encCNF := by
  unfold valiantTwoSAT
  have htaut : ComputableTidilyInPolyTime (fun p : CNF ℕ × ℕ => valiantVarTauts p.1)
      (encPair encCNF encUnary) encCNF :=
    (computableInPolyTime_valiantVarTauts.comp (ComputableInPolyTime.fst _ _)).tidy
  have hflat : ComputableTidilyInPolyTime
      (fun p : CNF ℕ × ℕ => p.1.zipIdx.flatMap (valiantClauseGadget p.2))
      (encPair encCNF encUnary) encCNF := by
    refine ComputableTidilyInPolyTime.flatMapWith computableInPolyTime_valiantClauseGadget.tidy
      (ComputableTidilyInPolyTime.snd _ _) ?_
    exact (ComputableTidilyInPolyTime.zipIdx (encClause encNat)).comp
      (ComputableTidilyInPolyTime.fst _ _)
  exact ((ComputableTidilyInPolyTime.listAppend (encClause encNat)).comp
    (htaut.prod hflat)).computableInPolyTime

private theorem computableTidily_valiantParitySum (wantOdd : Bool) :
    ComputableTidilyInPolyTime
      (fun p : CNF ℕ × List ℕ =>
        ((p.2.zipIdx).map fun x =>
          if x.2.testBit 0 == wantOdd then (p.1.length + 1).choose (x.2 + 1) * x.1 else 0).sum)
      (encPair encCNF (encList encNat)) encNat := by
  have hzip : ComputableTidilyInPolyTime
      (fun p : CNF ℕ × List ℕ => p.2.zipIdx)
      (encPair encCNF (encList encNat)) (encList (encPair encNat encUnary)) :=
    (ComputableTidilyInPolyTime.zipIdx encNat).comp (ComputableTidilyInPolyTime.snd _ _)
  have hterm : ComputableTidilyInPolyTime
      (fun q : (CNF ℕ × List ℕ) × (ℕ × ℕ) =>
        if q.2.2.testBit 0 == wantOdd then (q.1.1.length + 1).choose (q.2.2 + 1) * q.2.1 else 0)
      (encPair (encPair encCNF (encList encNat)) (encPair encNat encUnary)) encNat := by
    have hlen : ComputableInPolyTime
        (fun q : (CNF ℕ × List ℕ) × (ℕ × ℕ) => q.1.1.length + 1)
        (encPair (encPair encCNF (encList encNat)) (encPair encNat encUnary)) encUnary :=
      ComputableInPolyTime.unary_add'
        ((SAT.computableInPolyTime_length (ComputableInPolyTime.fst _ _)).comp
          (ComputableInPolyTime.fst _ _))
        (ComputableInPolyTime.const 1)
    have hr1 : ComputableInPolyTime
        (fun q : (CNF ℕ × List ℕ) × (ℕ × ℕ) => q.2.2 + 1)
        (encPair (encPair encCNF (encList encNat)) (encPair encNat encUnary)) encUnary :=
      ComputableInPolyTime.unary_add'
        ((ComputableInPolyTime.snd _ _).comp (ComputableInPolyTime.snd _ _))
        (ComputableInPolyTime.const 1)
    have hch : ComputableInPolyTime
        (fun q : (CNF ℕ × List ℕ) × (ℕ × ℕ) => (q.1.1.length + 1).choose (q.2.2 + 1))
        (encPair (encPair encCNF (encList encNat)) (encPair encNat encUnary)) encNat :=
      ComputableInPolyTime.binary_choose' hlen hr1
    have hmul : ComputableInPolyTime
        (fun q : (CNF ℕ × List ℕ) × (ℕ × ℕ) =>
          (q.1.1.length + 1).choose (q.2.2 + 1) * q.2.1)
        (encPair (encPair encCNF (encList encNat)) (encPair encNat encUnary)) encNat :=
      (ComputableTidilyInPolyTime.binary_mul' hch.tidy
        ((ComputableTidilyInPolyTime.fst _ _).comp
          (ComputableTidilyInPolyTime.snd _ _))).computableInPolyTime
    have hbit : ComputableTidilyInPolyTime
        (fun q : (CNF ℕ × List ℕ) × (ℕ × ℕ) => q.2.2.testBit 0 == wantOdd)
        (encPair (encPair encCNF (encList encNat)) (encPair encNat encUnary)) encBool := by
      have hrBin : ComputableTidilyInPolyTime
          (fun q : (CNF ℕ × List ℕ) × (ℕ × ℕ) => q.2.2)
          (encPair (encPair encCNF (encList encNat)) (encPair encNat encUnary)) encNat :=
        ComputableTidilyInPolyTime.unary_to_binary.comp
          ((ComputableTidilyInPolyTime.snd _ _).comp (ComputableTidilyInPolyTime.snd _ _))
      have htb : ComputableTidilyInPolyTime
          (fun q : (CNF ℕ × List ℕ) × (ℕ × ℕ) => q.2.2.testBit 0)
          (encPair (encPair encCNF (encList encNat)) (encPair encNat encUnary)) encBool :=
        ComputableTidilyInPolyTime.binary_testBit hrBin (ComputableTidilyInPolyTime.const 0)
      exact ComputableTidilyInPolyTime.bool_beq.comp
        (htb.prod (ComputableTidilyInPolyTime.const wantOdd))
    exact hbit.cond hmul.tidy (ComputableTidilyInPolyTime.const 0)
  exact ComputableTidilyInPolyTime.binary_sum.comp
    (ComputableTidilyInPolyTime.mapWithInput hzip hterm)

private theorem computableInPolyTime_valiantCombine :
    ComputableInPolyTime valiantCombine (encPair encCNF (encList encNat)) encNat := by
  unfold valiantCombine
  have hpos : ComputableInPolyTime
      (fun p : CNF ℕ × List ℕ =>
        ((p.2.zipIdx).map fun x =>
          if !x.2.testBit 0 then (p.1.length + 1).choose (x.2 + 1) * x.1 else 0).sum)
      (encPair encCNF (encList encNat)) encNat := by
    have heq :
        (fun p : CNF ℕ × List ℕ =>
          ((p.2.zipIdx).map fun x =>
            if !x.2.testBit 0 then (p.1.length + 1).choose (x.2 + 1) * x.1 else 0).sum) =
          (fun p : CNF ℕ × List ℕ =>
            ((p.2.zipIdx).map fun x =>
              if x.2.testBit 0 == false then (p.1.length + 1).choose (x.2 + 1) * x.1
              else 0).sum) :=
      funext fun p => congrArg List.sum (List.map_congr_left fun x _ => by
        cases x.2.testBit 0 <;> rfl)
    rw [heq]
    exact (computableTidily_valiantParitySum false).computableInPolyTime
  have hneg : ComputableInPolyTime
      (fun p : CNF ℕ × List ℕ =>
        ((p.2.zipIdx).map fun x =>
          if x.2.testBit 0 then (p.1.length + 1).choose (x.2 + 1) * x.1 else 0).sum)
      (encPair encCNF (encList encNat)) encNat := by
    have heq :
        (fun p : CNF ℕ × List ℕ =>
          ((p.2.zipIdx).map fun x =>
            if x.2.testBit 0 then (p.1.length + 1).choose (x.2 + 1) * x.1 else 0).sum) =
          (fun p : CNF ℕ × List ℕ =>
            ((p.2.zipIdx).map fun x =>
              if x.2.testBit 0 == true then (p.1.length + 1).choose (x.2 + 1) * x.1
              else 0).sum) :=
      funext fun p => congrArg List.sum (List.map_congr_left fun x _ => by
        cases x.2.testBit 0 <;> rfl)
    rw [heq]
    exact (computableTidily_valiantParitySum true).computableInPolyTime
  exact ComputableInPolyTime.binary_sub' hpos hneg

/-- **`#SAT` reduces in polynomial time to `#2SAT` via a counting Turing reduction.** -/
theorem countingTuringReducible_SharpSAT_SharpTwoSAT :
    CountingTuringReducible encCNF encCNF SharpSAT SharpTwoSAT := by
  let queries (φ : CNF ℕ) : List (CNF ℕ) :=
    (List.range (φ.length + 1)).map (valiantTwoSAT φ)
  let bound (φ : CNF ℕ) : ℕ :=
    φ.vars.length + φ.length * (φ.length + 1) + 1
  have hqueries : ComputableInPolyTime queries encCNF (encList encCNF) := by
    have hlist : ComputableTidilyInPolyTime (fun φ : CNF ℕ => List.range (φ.length + 1))
        encCNF (encList encUnary) := by
      have hlen : ComputableInPolyTime (fun φ : CNF ℕ => φ.length + 1) encCNF encUnary :=
        ComputableInPolyTime.unary_add'
          (SAT.computableInPolyTime_length ComputableInPolyTime.id')
          (ComputableInPolyTime.const 1)
      exact ComputableTidilyInPolyTime.range.comp hlen.tidy
    exact (ComputableTidilyInPolyTime.mapWithInput hlist
      computableInPolyTime_valiantTwoSAT.tidy).computableInPolyTime
  have hbound : ComputableInPolyTime bound encCNF encUnary := by
    have hv := SAT.computableInPolyTime_vars_length ComputableInPolyTime.id'
    have hm := SAT.computableInPolyTime_length ComputableInPolyTime.id'
    fun_prop
  refine PolyTimeOracleProgram.of_batchNatBits queries bound valiantCombine
    hqueries hbound computableInPolyTime_valiantCombine ?_
    (fun φ => by simpa only [queries, List.map_map, Function.comp_def] using valiantCombine_spec φ)
  intro φ ψ hψ
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hψ
  rw [List.mem_range] at hr
  exact size_SharpTwoSAT_valiantTwoSAT_le (by omega)

/-- **`#2SAT` is `#P`-complete under polynomial-time counting Turing reductions**
[Valiant 1979][Valiant1979]. -/
theorem SharpTwoSAT_countingTuringComplete :
    CountingTuringComplete encCNF SharpTwoSAT :=
  And.intro SharpTwoSAT.mem_SharpP
    (CookLevin.SharpSAT_sharpPHard.trans_countingTuring
      countingTuringReducible_SharpSAT_SharpTwoSAT)

/-- If `#2SAT` is computable in polynomial time (`FP`), then `SAT ∈ P`. -/
theorem SharpTwoSAT_polyTime_implies_SAT_mem_P
    (h : ComputableInPolyTime SharpTwoSAT encCNF encNat) :
    SAT ∈ P encCNF := by
  have hSS : ComputableInPolyTime SharpSAT encCNF encNat :=
    countingTuringReducible_SharpSAT_SharpTwoSAT.computableInPolyTime_of_decoder cnfDecoder h
  refine ⟨fun φ => decide (0 < SharpSAT φ),
    ComputableInPolyTime.binary_lt' (ComputableInPolyTime.const 0) hSS, fun φ => ?_⟩
  rw [decide_eq_true_eq, SharpSAT, CNF.modelCount_pos_iff]
  rfl

/-- If `#2SAT` is computable in polynomial time (`FP`), then `P = NP`. -/
theorem SharpTwoSAT_polyTime_implies_P_eq_NP
    (h : ComputableInPolyTime SharpTwoSAT encCNF encNat)
    {α : Type} (enc : α ↪ List Bool) :
    P enc = NP enc :=
  Ladner.P_eq_NP_of_SAT_mem_P (SharpTwoSAT_polyTime_implies_SAT_mem_P h) enc

end Cslib.Complexity
