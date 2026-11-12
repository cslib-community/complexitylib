/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.AffineDisperser4n.Refuter
import all CslibFrontier.Computability.Circuit.Boolean.AffineDisperser4n.Refuter

/-!
# Correctness of the refuter's affine-representation oracle

`evaluateAux S a val` asks the dense XOR-SAT decider whether the affine system of `S`, the
parameter values `val` and `a = 0` are simultaneously satisfiable. On a well-formed state this
returns the value of the auxiliary variable `a` in the unique solution extending `val`, so
`findAffineRep S a` recovers the affine representation of `a` in the parameters.

## Main results

* `Cslib.Circuits.Boolean.AffineDisperser4n.evaluateAux_eq`: `evaluateAux` evaluates an
  auxiliary variable.
* `Cslib.Circuits.Boolean.AffineDisperser4n.findAffineRep_spec`: `findAffineRep` is the affine
  representation of an auxiliary variable.
-/

public section

namespace Cslib.Circuits.Boolean.AffineDisperser4n

open Cslib.Circuits.Boolean.AffineDisperserCore
open Cslib.Circuits.Boolean.SemiCircuit
open Cslib.Complexity.XORSAT.Dense Cslib.Circuits Cslib.BitString

variable {n : ℕ}

private theorem dot_append {l₁ m₁ : List Bool} (h : l₁.length = m₁.length) (l₂ m₂ : List Bool) :
    dot (l₁ ++ l₂) (m₁ ++ m₂) = dot l₁ m₁ + dot l₂ m₂ := by
  induction l₁ generalizing m₁ with
  | nil =>
    rw [List.eq_nil_of_length_eq_zero h.symm]
    exact (zero_add _).symm
  | cons b l ih =>
    obtain _ | ⟨x, m⟩ := m₁
    · simp at h
    · simp only [List.cons_append, dot]
      rw [ih (by simpa using h), add_assoc]

private theorem dot_toDenseRow (N : ℕ) (T : Finset ℕ) (w : ℕ → Bool) (hT : ∀ i ∈ T, i < N) :
    dot ((List.range N).map fun i => decide (i ∈ T)) ((List.range N).map w) = ∑ i ∈ T, w i := by
  have key : ∀ M, dot ((List.range M).map fun i => decide (i ∈ T)) ((List.range M).map w) =
      ∑ i ∈ Finset.range M, (if i ∈ T then w i else 0) := by
    intro M
    induction M with
    | zero => rfl
    | succ M ih =>
      rw [List.range_succ, List.map_append, List.map_append,
        dot_append (by simp), ih, Finset.sum_range_succ]
      congr 1
      simp only [List.map_cons, List.map_nil, dot]
      by_cases hM : M ∈ T
      · simp only [hM, decide_true, ite_true]
        cases w M <;> rfl
      · simp only [hM, decide_false, ite_false]
        cases w M <;> rfl
  rw [key, ← Finset.sum_filter, Finset.filter_mem_eq_inter,
    Finset.inter_eq_right.2 fun i hi => Finset.mem_range.2 (hT i hi)]

/-- The dense system queried by `evaluateAux S a val`. -/
private abbrev auxSystem (S : State n) (a : ℕ) (val : ℕ → Bool) : System :=
  ((S.eqns.sort (· ≤ ·)).map fun e => toDenseRow (varBound S) (S.eqn e).terms (S.eqn e).rhs) ++
    ((S.params.sort (· ≤ ·)).map fun p => toDenseRow (varBound S) {p} (val p)) ++
    [toDenseRow (varBound S) {a} false]

private theorem evaluateAux_eq_auxSystem (S : State n) (a : ℕ) (val : ℕ → Bool) :
    evaluateAux S a val =
      if Cslib.Complexity.XORSAT.Dense.decide ⟨varBound S, auxSystem S a val⟩ then false
      else true := by
  unfold evaluateAux
  rfl

private theorem width_auxSystem (S : State n) (a : ℕ) (val : ℕ → Bool) :
    Width (varBound S) (auxSystem S a val) := by
  intro e he
  simp only [List.mem_append, List.mem_map, List.mem_singleton] at he
  rcases he with (⟨_, _, rfl⟩ | ⟨_, _, rfl⟩) | rfl <;> simp [toDenseRow]

private theorem lt_varBound {S : State n} {i : ℕ} (hi : i ∈ S.params ∪ S.aux) : i < varBound S :=
  Nat.lt_succ_of_le (Finset.le_sup (f := id) hi)

private theorem dot_toDenseRow_varBound {S : State n} {T : Finset ℕ} (hT : T ⊆ S.params ∪ S.aux)
    (c : Bool) (v : ℕ → Bool) :
    dot (toDenseRow (varBound S) T c).coeffs ((List.range (varBound S)).map v) =
      ∑ i ∈ T, v i :=
  dot_toDenseRow _ _ _ fun _ hi => lt_varBound (hT hi)

private theorem holds_auxSystem_iff {S : State n} (hwf : S.WellFormed) {a : ℕ}
    (ha : a ∈ S.params ∪ S.aux) (val v : ℕ → Bool) :
    Holds (auxSystem S a val) ((List.range (varBound S)).map v) ↔
      S.EqnsHold v ∧ (∀ p ∈ S.params, v p = val p) ∧ v a = false := by
  have hp : ∀ p ∈ S.params, ({p} : Finset ℕ) ⊆ S.params ∪ S.aux := fun p hp =>
    Finset.singleton_subset_iff.2 (Finset.mem_union_left _ hp)
  simp only [Holds, List.forall_mem_append, List.forall_mem_map, Finset.mem_sort,
    List.forall_mem_singleton]
  rw [and_assoc]
  refine and_congr ?_ (and_congr ?_ ?_)
  · refine forall₂_congr fun e he => ?_
    rw [dot_toDenseRow_varBound (hwf.terms_subset e he)]
    rfl
  · refine forall₂_congr fun p hp' => ?_
    rw [dot_toDenseRow_varBound (hp p hp'), Finset.sum_singleton]
    rfl
  · rw [dot_toDenseRow_varBound (Finset.singleton_subset_iff.2 ha), Finset.sum_singleton]
    rfl

private theorem satisfiable_auxSystem_iff {S : State n} (hwf : S.WellFormed) {a : ℕ}
    (ha : a ∈ S.params ∪ S.aux) (val : ℕ → Bool) :
    Satisfiable (varBound S) (auxSystem S a val) ↔
      ∃ v, S.EqnsHold v ∧ (∀ p ∈ S.params, v p = val p) ∧ v a = false := by
  constructor
  · rintro ⟨l, hl, hH⟩
    have hl' : l = (List.range (varBound S)).map fun i => l.getD i false := by
      refine List.ext_getElem (by simp [hl]) fun i h₁ _ => ?_
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h₁]
    rw [hl'] at hH
    exact ⟨_, (holds_auxSystem_iff hwf ha val _).1 hH⟩
  · rintro ⟨v, hv⟩
    exact ⟨_, by simp, (holds_auxSystem_iff hwf ha val v).2 hv⟩

/-- `evaluateAux S a val` is the value of the auxiliary variable `a` in the solution of the affine
system extending the parameter assignment `val`. -/
theorem evaluateAux_eq {S : State n} (hwf : S.WellFormed) {a : ℕ} (ha : a ∈ S.aux)
    {val w : ℕ → Bool} (hw : ∀ j ∈ S.params, w j = val j) (hweq : S.EqnsHold w) :
    evaluateAux S a val = w a := by
  have ha' : a ∈ S.params ∪ S.aux := Finset.mem_union_right _ ha
  have key : Cslib.Complexity.XORSAT.Dense.decide ⟨varBound S, auxSystem S a val⟩ = true ↔
      w a = false := by
    rw [decide_eq_true_iff]
    simp only [width_auxSystem, true_and]
    rw [satisfiable_auxSystem_iff hwf ha']
    constructor
    · rintro ⟨v, hv, hvp, hva⟩
      rw [← hva]
      exact hwf.unique w v (fun j hj => (hw j hj).trans (hvp j hj).symm) hweq hv a ha
    · intro hwa
      exact ⟨w, hweq, hw, hwa⟩
  rw [evaluateAux_eq_auxSystem]
  cases hwa : w a
  · rw [ite_eq_left (key.2 hwa)]
  · have : Cslib.Complexity.XORSAT.Dense.decide ⟨varBound S, auxSystem S a val⟩ ≠ true :=
      fun h => by simp [key.1 h] at hwa
    rw [ite_eq_right this]

/-- On an auxiliary variable `a = c + ∑ j ∈ T, u j`, `evaluateAux S a val` evaluates the affine
expression at `val`. -/
theorem evaluateAux_eq_of_affineIn {S : State n} (hwf : S.WellFormed) {a : ℕ} (ha : a ∈ S.aux)
    {c : Bool} {T : Finset ℕ} (h : S.AffineIn a c T) (val : ℕ → Bool) :
    evaluateAux S a val = c + ∑ j ∈ T, val j := by
  obtain ⟨w, hw, hweq⟩ := hwf.solvable val
  rw [evaluateAux_eq hwf ha hw hweq, h.2 w hweq]
  congr 1
  exact Finset.sum_congr rfl fun j hj => hw j (h.1 hj)

/-- `findAffineRep S Q` is the affine representation of the auxiliary variable `Q` in the
parameters. -/
theorem findAffineRep_spec {S : State n} (hwf : S.WellFormed) {Q : ℕ} (hQ : Q ∈ S.aux) :
    S.AffineIn Q (findAffineRep S Q).1 (findAffineRep S Q).2 := by
  obtain ⟨c, T, h⟩ := hwf.exists_affineIn hQ
  have h0 : evaluateAux S Q (fun _ => false) = c := by
    rw [evaluateAux_eq_of_affineIn hwf hQ h]
    change c + ∑ _j ∈ T, (0 : Bool) = c
    rw [Finset.sum_const_zero, add_zero]
  have hc : (findAffineRep S Q).1 = c := h0
  have hT : (findAffineRep S Q).2 = T := by
    change S.params.filter (fun y => evaluateAux S Q (fun j => j == y) !=
      evaluateAux S Q (fun _ => false)) = T
    ext y
    rw [Finset.mem_filter, h0, evaluateAux_eq_of_affineIn hwf hQ h]
    have hsum : ∑ j ∈ T, (j == y) = if y ∈ T then 1 else 0 := by
      rw [← Finset.sum_ite_eq' T y fun _ => (1 : Bool)]
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases hj : j = y
      · subst hj
        rw [beq_self_eq_true, ite_eq_left rfl]
        rfl
      · rw [beq_false_of_ne hj, ite_eq_right hj]
        rfl
    rw [hsum]
    by_cases hy : y ∈ T
    · simp only [hy, ite_true, iff_true]
      refine ⟨h.1 hy, ?_⟩
      cases c <;> rfl
    · simp only [hy, ite_false, iff_false, not_and]
      intro _
      cases c <;> decide
  rw [hc, hT]
  exact h

end Cslib.Circuits.Boolean.AffineDisperser4n
