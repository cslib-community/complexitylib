/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Foundations.LinearAlgebra.RowSelection
public import Complexity.Foundations.Data.Function.Tabulate
import Mathlib.Data.List.Find

/-!
# Executable rational elimination with original row indices

`eliminate` scans a supplied row list once per column, retaining original row indices
and back-substituting an actual rational candidate. It never enumerates subsets of
rows or Boolean assignments. This implements the algebraic elimination step in
[ChenJiangZhu2027], Lemma 3.1, PDF pp. 10–11, using rational arithmetic.

The correctness results below do not certify encoded polynomial bit time: in
particular, a bound on arithmetic operations is not a bound on intermediate
numerators and denominators. The paper's fraction-free coefficient-growth argument
and an encoded implementation remain separate obligations.

## Main definitions

* `eliminate`: recursive rational elimination with original row indices.
* `eliminateCached`: execution with materialized intermediate tables.

## Main results

* `eliminate_consistent_iff`, `eliminate_point`: consistency detection and back-substitution.
* `eliminate_selected_iff`: the retained original equations have the same solutions.
* `eliminate_unique`: uniqueness when every column has a pivot.
* `eliminateCached_eq`: cached execution preserves all kernel outputs.

-/

public section

namespace Cslib.LinearSystem

open Matrix

variable {I V : Type*} [DecidableEq V] [Fintype V]

/-- Elimination output: original indices, a back-substituted point and consistency. -/
structure Elimination (I V : Type*) where
  /-- Original row indices, in pivot order. -/
  indices : List I
  /-- One rational candidate; irrelevant when `consistent = false`. -/
  point : V → ℚ
  /-- Whether the residual constant equations all vanish. -/
  consistent : Bool

/-- Subtract a multiple of one pivot row from every coefficient row. -/
@[expose] def eliminateRows (A : I → V → ℚ) (p : I) (c : V) : I → V → ℚ :=
  fun i v => A i v - A i c / A p c * A p v

/-- Apply exactly the same row operations to the right-hand side. -/
@[expose] def eliminateRhs (A : I → V → ℚ) (b : I → ℚ) (p : I) (c : V) : I → ℚ :=
  fun i => b i - A i c / A p c * b p

/-- Correct only the pivot coordinate when back-substituting. -/
@[expose] def restorePivot (A : V → ℚ) (b : ℚ) (c : V) (x : V → ℚ) : V → ℚ :=
  x + Pi.single c ((b - A ⬝ᵥ x) / A c)

/-- One finite row scan per column, recursive elimination and back-substitution.
The same `rows` list is retained at every stage; pivot rows become zero rows.
No oracle for dependence, consistency or a rational solution is used. -/
@[expose] def eliminate (rows : List I) : List V → (I → V → ℚ) → (I → ℚ) → Elimination I V
  | [], _, b => ⟨[], fun _ => 0, decide (∀ i ∈ rows, b i = 0)⟩
  | c :: cs, A, b =>
    match rows.find? (fun i => A i c != 0) with
    | none => eliminate rows cs A b
    | some p =>
      let next := eliminate rows cs (eliminateRows A p c) (eliminateRhs A b p c)
      ⟨p :: next.indices, restorePivot (A p) (b p) c next.point, next.consistent⟩

/-- Each pivot consumes one supplied column. -/
theorem eliminate_length_le (rows : List I) (cols : List V) (A : I → V → ℚ) (b : I → ℚ) :
    (eliminate rows cols A b).indices.length ≤ cols.length := by
  induction cols generalizing A b with
  | nil => simp [eliminate]
  | cons c cs ih =>
    simp only [eliminate]
    split
    · exact (ih A b).trans (Nat.le_succ _)
    · simpa only [List.length_cons] using Nat.succ_le_succ
        (ih (eliminateRows A _ c) (eliminateRhs A b _ c))

/-- Every output index is an original input index. -/
theorem eliminate_mem (rows : List I) (cols : List V) (A : I → V → ℚ) (b : I → ℚ)
    (i : I) (hi : i ∈ (eliminate rows cols A b).indices) : i ∈ rows := by
  induction cols generalizing A b with
  | nil => simp [eliminate] at hi
  | cons c cs ih =>
    simp only [eliminate] at hi
    split at hi
    · exact ih A b hi
    · rename_i p hp
      rcases List.mem_cons.mp hi with rfl | hi
      · exact List.mem_of_find?_eq_some hp
      · exact ih _ _ hi

omit [DecidableEq V] [Fintype V] in
private theorem pivot_ne (rows : List I) (A : I → V → ℚ) (c : V) (p : I)
    (hp : rows.find? (fun i => A i c != 0) = some p) : A p c ≠ 0 := by
  simpa using List.find?_some hp

omit [DecidableEq V] [Fintype V] in
private theorem residual_zero (A : I → V → ℚ) (p : I) (c : V) (hp : A p c ≠ 0)
    (i : I) : eliminateRows A p c i c = 0 := by
  simp [eliminateRows, div_mul_cancel₀ _ hp]

omit [DecidableEq V] in
private theorem residual_dot (A : I → V → ℚ) (p : I) (c : V) (i : I) (x : V → ℚ) :
    eliminateRows A p c i ⬝ᵥ x = A i ⬝ᵥ x - A i c / A p c * (A p ⬝ᵥ x) := by
  simp [eliminateRows, dotProduct, sub_mul, Finset.sum_sub_distrib, Finset.mul_sum,
    mul_assoc]

omit [DecidableEq V] in
private theorem residual_iff (A : I → V → ℚ) (b : I → ℚ) (p : I) (c : V)
    (x : V → ℚ) (hp : A p ⬝ᵥ x = b p) (i : I) :
    eliminateRows A p c i ⬝ᵥ x = eliminateRhs A b p c i ↔ A i ⬝ᵥ x = b i := by
  rw [residual_dot, hp]
  exact sub_left_inj

private theorem restore_dot (A : V → ℚ) (b : ℚ) (c : V) (x : V → ℚ)
    (hc : A c ≠ 0) : A ⬝ᵥ restorePivot A b c x = b := by
  rw [restorePivot, dotProduct_add, dotProduct_single]
  field_simp
  ring

private theorem residual_restore (A : I → V → ℚ) (b : I → ℚ) (p : I) (c : V)
    (hp : A p c ≠ 0) (i : I) (x : V → ℚ) :
    eliminateRows A p c i ⬝ᵥ restorePivot (A p) (b p) c x =
      eliminateRows A p c i ⬝ᵥ x := by
  rw [restorePivot, dotProduct_add, dotProduct_single, residual_zero A p c hp i]
  simp

omit [DecidableEq V] [Fintype V] in
private theorem residual_support (rows : List I) (cs : List V) (A : I → V → ℚ)
    (p : I) (c : V) (hp : p ∈ rows) (hc : A p c ≠ 0)
    (hs : ∀ i ∈ rows, ∀ v, v ∉ c :: cs → A i v = 0) :
    ∀ i ∈ rows, ∀ v, v ∉ cs → eliminateRows A p c i v = 0 := by
  intro i hi v hv
  by_cases hvc : v = c
  · subst v; exact residual_zero A p c hc i
  · have hn : v ∉ c :: cs := by simp [hvc, hv]
    simp [eliminateRows, hs i hi v hn, hs p hp v hn]

/-- Back-substitution returns a solution exactly when the computed residual test
accepts. The support hypothesis says all unprocessed nonzero columns are listed. -/
theorem eliminate_consistent_iff (rows : List I) (cols : List V)
    (A : I → V → ℚ) (b : I → ℚ)
    (hs : ∀ i ∈ rows, ∀ v, v ∉ cols → A i v = 0) :
    (eliminate rows cols A b).consistent = true ↔
      ∃ x : V → ℚ, ∀ i ∈ rows, A i ⬝ᵥ x = b i := by
  induction cols generalizing A b with
  | nil =>
    have hz (i : I) (hi : i ∈ rows) : A i = 0 := by
      funext v; exact hs i hi v (by simp)
    simp only [eliminate, decide_eq_true_eq]
    constructor
    · intro hb; exact ⟨0, fun i hi => by simp [hz i hi, hb i hi]⟩
    · rintro ⟨x, hx⟩ i hi
      simpa [hz i hi] using (hx i hi).symm
  | cons c cs ih =>
    simp only [eliminate]
    split
    · rename_i hn
      have hz (i : I) (hi : i ∈ rows) : A i c = 0 := by
        have h := List.find?_eq_none.mp hn i hi
        simpa using h
      apply ih
      intro i hi v hv
      by_cases hvc : v = c
      · simpa [hvc] using hz i hi
      · exact hs i hi v (by simp [hvc, hv])
    · rename_i p hp
      have hpc := pivot_ne rows A c p hp
      have hpr := List.mem_of_find?_eq_some hp
      rw [ih _ _ (residual_support rows cs A p c hpr hpc hs)]
      constructor
      · rintro ⟨x, hx⟩
        refine ⟨restorePivot (A p) (b p) c x, fun i hi => ?_⟩
        apply (residual_iff A b p c _ (restore_dot _ _ _ _ hpc) i).mp
        rw [residual_restore A b p c hpc]
        exact hx i hi
      · rintro ⟨x, hx⟩
        exact ⟨x, fun i hi => (residual_iff A b p c x (hx p hpr) i).mpr (hx i hi)⟩

/-- The point stored by an accepting execution satisfies every input equation. -/
theorem eliminate_point (rows : List I) (cols : List V) (A : I → V → ℚ) (b : I → ℚ)
    (hs : ∀ i ∈ rows, ∀ v, v ∉ cols → A i v = 0)
    (hc : (eliminate rows cols A b).consistent = true) :
    ∀ i ∈ rows, A i ⬝ᵥ (eliminate rows cols A b).point = b i := by
  induction cols generalizing A b with
  | nil =>
    intro i hi
    have hb : ∀ i ∈ rows, b i = 0 := by simpa [eliminate] using hc
    simp [eliminate, hb i hi]
  | cons c cs ih =>
    simp only [eliminate] at hc ⊢
    split at *
    · rename_i hn
      apply ih A b _ hc
      intro i hi v hv
      by_cases hvc : v = c
      · subst v; simpa using List.find?_eq_none.mp hn i hi
      · exact hs i hi v (by simp [hvc, hv])
    · rename_i p hp
      have hpc := pivot_ne rows A c p hp
      have hpr := List.mem_of_find?_eq_some hp
      have hn := ih _ _ (residual_support rows cs A p c hpr hpc hs) hc
      intro i hi
      apply (residual_iff A b p c _ (restore_dot _ _ _ _ hpc) i).mp
      rw [residual_restore A b p c hpc]
      exact hn i hi

/-- On consistent input, the computed original indices have exactly the same
solutions as the entire input. The selected rows retain their original syntax. -/
theorem eliminate_selected_iff (rows : List I) (cols : List V)
    (A : I → V → ℚ) (b : I → ℚ)
    (hs : ∀ i ∈ rows, ∀ v, v ∉ cols → A i v = 0)
    (hc : (eliminate rows cols A b).consistent = true) (x : V → ℚ) :
    (∀ i ∈ (eliminate rows cols A b).indices, A i ⬝ᵥ x = b i) ↔
      ∀ i ∈ rows, A i ⬝ᵥ x = b i := by
  induction cols generalizing A b with
  | nil =>
    have hb : ∀ i ∈ rows, b i = 0 := by simpa [eliminate] using hc
    simp only [eliminate, List.not_mem_nil, false_implies, implies_true, true_iff]
    intro i hi
    have hz : A i = 0 := by funext v; exact hs i hi v (by simp)
    simp [hz, hb i hi]
  | cons c cs ih =>
    simp only [eliminate] at hc ⊢
    split at *
    · rename_i hn
      apply ih A b _ hc
      intro i hi v hv
      by_cases hvc : v = c
      · subst v; simpa using List.find?_eq_none.mp hn i hi
      · exact hs i hi v (by simp [hvc, hv])
    · rename_i p hp
      have hpc := pivot_ne rows A c p hp
      have hpr := List.mem_of_find?_eq_some hp
      have hh := ih _ _ (residual_support rows cs A p c hpr hpc hs) hc
      constructor
      · intro hx
        have hpx := hx p (by simp)
        have hn : ∀ i ∈ (eliminate rows cs (eliminateRows A p c)
            (eliminateRhs A b p c)).indices,
            eliminateRows A p c i ⬝ᵥ x = eliminateRhs A b p c i := by
          intro i hi
          exact (residual_iff A b p c x hpx i).mpr (hx i (List.mem_cons_of_mem p hi))
        exact fun i hi => (residual_iff A b p c x hpx i).mp ((hh.mp hn) i hi)
      · intro hx i hi
        exact hx i (eliminate_mem rows (c :: cs) A b i (by
          simpa only [eliminate, hp] using hi))

private theorem residual_clear (A : I → V → ℚ) (p : I) (c : V)
    (hp : A p c ≠ 0) (i : I) (x : V → ℚ) :
    eliminateRows A p c i ⬝ᵥ (x - Pi.single c (x c)) =
      eliminateRows A p c i ⬝ᵥ x := by
  rw [dotProduct_sub, dotProduct_single, residual_zero A p c hp i]
  simp

/-- If every supplied column has a pivot, the equations determine all coordinates
in that column list. Other coordinates must be fixed equally in both solutions. -/
theorem eliminate_unique (rows : List I) (cols : List V) (A : I → V → ℚ) (b : I → ℚ)
    (hl : (eliminate rows cols A b).indices.length = cols.length)
    (x z : V → ℚ) (hx : ∀ i ∈ rows, A i ⬝ᵥ x = b i)
    (hz : ∀ i ∈ rows, A i ⬝ᵥ z = b i)
    (hout : ∀ v, v ∉ cols → x v = z v) : x = z := by
  induction cols generalizing A b x z with
  | nil => exact funext fun v => hout v (by simp)
  | cons c cs ih =>
    simp only [eliminate] at hl
    split at hl
    · have hh := eliminate_length_le rows cs A b
      simp only [List.length_cons] at hl
      omega
    · rename_i p hp
      have hpc := pivot_ne rows A c p hp
      have hpr := List.mem_of_find?_eq_some hp
      have he : x - Pi.single c (x c) = z - Pi.single c (z c) := by
        apply ih (eliminateRows A p c) (eliminateRhs A b p c)
          (by simpa only [List.length_cons, Nat.succ.injEq] using hl)
        · intro i hi
          rw [residual_clear A p c hpc]
          exact (residual_iff A b p c x (hx p hpr) i).mpr (hx i hi)
        · intro i hi
          rw [residual_clear A p c hpc]
          exact (residual_iff A b p c z (hz p hpr) i).mpr (hz i hi)
        · intro v hv
          by_cases hvc : v = c
          · subst v; simp
          · simp only [Pi.sub_apply, Pi.single_eq_of_ne hvc]
            rw [hout v (by simp [hvc, hv])]
      have hd : x - z = Pi.single c (x c - z c) := by
        funext v
        by_cases hvc : v = c
        · subst v; simp
        · have hh := congrFun he v
          simpa [Pi.single_eq_of_ne hvc] using congrArg (fun q => q - z v) hh
      have hdot : A p c * (x c - z c) = 0 := by
        rw [← dotProduct_single, ← hd, dotProduct_sub, hx p hpr, hz p hpr, sub_self]
      have hc : x c = z c := sub_eq_zero.mp ((mul_eq_zero.mp hdot).resolve_left hpc)
      funext v
      by_cases hv : v = c
      · subst v; exact hc
      · have hh := congrFun he v
        simpa [Pi.single_eq_of_ne hv] using hh

/-- Materialized elimination. Each next matrix and right-hand side is evaluated
into finite lookup tables before the recursive call. In contrast, evaluating
nested coefficient functions directly can recompute earlier arithmetic many times.
The finite lookup scans are explicit; no runtime bound is assumed. -/
@[expose] def eliminateCached [Fintype I] [LinearOrder I] [LinearOrder V]
    (rows : List I) : List V → (I → V → ℚ) → (I → ℚ) → Elimination I V
  | [], _, b => ⟨[], fun _ => 0, decide (∀ i ∈ rows, b i = 0)⟩
  | c :: cs, A, b =>
    match rows.find? (fun i => A i c != 0) with
    | none => eliminateCached rows cs A b
    | some p =>
      let nextA := Cslib.Function.tabulate fun i => Cslib.Function.tabulate (eliminateRows A p c i)
      let nextB := Cslib.Function.tabulate (eliminateRhs A b p c)
      let next := eliminateCached rows cs nextA nextB
      ⟨p :: next.indices, Cslib.Function.tabulate (restorePivot (A p) (b p) c next.point),
        next.consistent⟩

/-- Materialization preserves every output field of the verified kernel. -/
theorem eliminateCached_eq [Fintype I] [LinearOrder I] [LinearOrder V]
    (rows : List I) (cols : List V) (A : I → V → ℚ) (b : I → ℚ) :
    eliminateCached rows cols A b = eliminate rows cols A b := by
  induction cols generalizing A b with
  | nil => simp [eliminateCached, eliminate]
  | cons c cs ih =>
    simp only [eliminateCached, eliminate]
    split
    · exact ih A b
    · simp only [Cslib.Function.tabulate_eq, ih]

end Cslib.LinearSystem
