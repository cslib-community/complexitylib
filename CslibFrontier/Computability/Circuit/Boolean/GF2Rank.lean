/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Cslib.Computability.Circuit.Boolean.Synthesis
public import CslibFrontier.Foundations.Data.BitString.ZModTwo
public import CslibFrontier.Foundations.LinearAlgebra.Matrix.GaussJordan
import CslibFrontier.Computability.Circuit.Boolean.AtLeast
import CslibFrontier.Computability.Circuit.Boolean.Synthesis
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith

/-!
# De Morgan circuits for the rank of a matrix over `ZMod 2`

A matrix `A x : Matrix (Fin r) (Fin c) (ZMod 2)` that depends on the circuit input `x` is given to
a circuit through the bits of its entries (`Cslib.Circuits.Boolean.entryBits`), using the ring
isomorphism `Cslib.BitString.bitEquiv : ZMod 2 ≃+* Bool`. This file synthesises the bits of the
Gauss–Jordan stages of `Matrix.GaussJordan` from those bits, and then the threshold test
`t ≤ (A x).rank`, over the De Morgan basis.

One stage at column `k` follows `Matrix.GaussJordan.stage_apply_zmod_two`. Each row tests whether
it is a candidate (zero before `k`, one at `k`), then whether it is the first candidate (the pivot,
`Matrix.GaussJordan.pivotRow_eq_some_iff`). The pivot row's entries are an exclusive or over the
rows, gated by the pivot test, and each new entry is the old entry exclusive-or the pivot row's
entry when the row has a one at `k` and is not the pivot. A stage costs `14 (r + 1) (r + c + 1)`
gates. The rank is the number of nonzero rows of `Matrix.GaussJordan.reduce`
(`Matrix.GaussJordan.rank_eq_card_reduce_ne_zero`), which a threshold circuit
(`Cslib.Circuits.Boolean.synthesis_atLeast`) compares with `t`.

The bounds count gates only. The construction chains one stage per column; its depth is not
certified here. The gate counts are this library's, not a source's.

## Main definitions

* `Cslib.Circuits.Boolean.entryBits A`: the bits of the entries of a matrix that depends on the
  input.

## Main results

* `Cslib.Circuits.Boolean.synthesis_entryBits_stage`: one stage, within `14 (r + 1) (r + c + 1)`
  gates on top of the current entries.
* `Cslib.Circuits.Boolean.synthesis_entryBits_reduce`: all `c` stages.
* `Cslib.Circuits.Boolean.synthesis_le_rank`: the test `t ≤ (A x).rank`, for `t ≤ r + 1`, within
  `14 (c + 1) (r + 1) (r + c + 1)` gates on top of the entries.
* `Cslib.Circuits.Boolean.synthesis_le_rank_of_synthesis`: the same test when the entries are
  themselves synthesised.

## References

Computing a rank over `ZMod 2` by a polynomial-size circuit is the constructivity step of the
rank property in [Razborov and Rudich, §3.2][RazborovRudich1997], who note that rank is in NC²
without giving an explicit circuit or a gate count.
-/

public section

namespace Cslib.Circuits.Boolean

open Finset Matrix Matrix.GaussJordan Cslib.BitString

variable {n r c : ℕ}

/-- The bits of the entries of a matrix over `ZMod 2` that depends on the input `x`. -/
def entryBits (A : BitString n → Matrix (Fin r) (Fin c) (ZMod 2)) : Set (BooleanFunction n) :=
  Set.range fun p : Fin r × Fin c => fun x => bitEquiv (A x p.1 p.2)

theorem mem_entryBits {A : BitString n → Matrix (Fin r) (Fin c) (ZMod 2)}
    {f : BooleanFunction n} : f ∈ entryBits A ↔ ∃ i l, (fun x => bitEquiv (A x i l)) = f := by
  simp [entryBits]

theorem entry_mem_entryBits (A : BitString n → Matrix (Fin r) (Fin c) (ZMod 2)) (i : Fin r)
    (l : Fin c) : (fun x => bitEquiv (A x i l)) ∈ entryBits A :=
  ⟨(i, l), rfl⟩

private theorem bitEquiv_eq_true_iff (a : ZMod 2) : bitEquiv a = true ↔ a ≠ 0 := by
  revert a
  decide

/-! ### One stage -/

section Stage

variable (A : BitString n → Matrix (Fin r) (Fin c) (ZMod 2)) (k : Fin c)

/-- Row `i` is a pivot candidate for column `k`: zero before `k`, one at `k`. -/
private def candFn (i : Fin r) : BooleanFunction n := fun x =>
  (!decide (∃ l ∈ univ.filter fun l : Fin c => l.1 < k.1, bitEquiv (A x i l) = true)) &&
    bitEquiv (A x i k)

/-- Row `i` is the pivot row for column `k`: the first candidate. -/
private def pivFn (i : Fin r) : BooleanFunction n := fun x =>
  candFn A k i x && !decide (∃ i' ∈ univ.filter fun i' : Fin r => i' < i, candFn A k i' x = true)

/-- The pivot row's entry in column `l`, or `false` if there is no pivot row. -/
private def pivEntryFn (l : Fin c) : BooleanFunction n := fun x =>
  ∑ i, (pivFn A k i x && bitEquiv (A x i l))

/-- The entry `(i, l)` after the stage. -/
private def newFn (p : Fin r × Fin c) : BooleanFunction n := fun x =>
  bitEquiv (A x p.1 p.2) ^^ (bitEquiv (A x p.1 k) && (!pivFn A k p.1 x && pivEntryFn A k p.2 x))

private theorem candFn_eq_true_iff (x : BitString n) (i : Fin r) :
    candFn A k i x = true ↔ IsFreeBefore (A x) k i ∧ A x i k ≠ 0 := by
  simp only [candFn, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
    bitEquiv_eq_true_iff, mem_filter, mem_univ, true_and, not_exists, not_and, not_not,
    IsFreeBefore]

private theorem pivFn_eq_true_iff (x : BitString n) (i : Fin r) :
    pivFn A k i x = true ↔ pivotRow (A x) k = some i := by
  rw [pivotRow_eq_some_iff]
  simp only [pivFn, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, mem_filter,
    mem_univ, true_and, not_exists, candFn_eq_true_iff]
  constructor
  · rintro ⟨⟨hfree, hne⟩, hmin⟩
    exact ⟨hfree, hne, fun i' hi' hfree' => by_contra fun h => hmin i' ⟨hi', hfree', h⟩⟩
  · rintro ⟨hfree, hne, hmin⟩
    exact ⟨⟨hfree, hne⟩, fun i' ⟨hi', hfree', h⟩ => h (hmin i' hi' hfree')⟩

private theorem pivEntryFn_eq (x : BitString n) (l : Fin c) :
    pivEntryFn A k l x = (pivotRow (A x) k).elim false fun p => bitEquiv (A x p l) := by
  unfold pivEntryFn
  rcases h : pivotRow (A x) k with _ | p
  · refine sum_eq_zero fun i _ => ?_
    have : pivFn A k i x = false := by
      rw [← Bool.not_eq_true, pivFn_eq_true_iff, h]
      simp
    simp [this, Bool.zero_eq_false]
  · rw [sum_eq_single p]
    · simp [(pivFn_eq_true_iff A k x p).mpr h]
    · intro i _ hip
      have : pivFn A k i x = false := by
        rw [← Bool.not_eq_true, pivFn_eq_true_iff, h]
        simpa using Ne.symm hip
      simp [this, Bool.zero_eq_false]
    · simp

private theorem newFn_eq (p : Fin r × Fin c) :
    newFn A k p = fun x => bitEquiv (stage (A x) k p.1 p.2) := by
  funext x
  rw [stage_apply_zmod_two, map_add, map_sum]
  unfold newFn
  rw [pivEntryFn_eq, Bool.add_eq_xor]
  congr 1
  rcases h : pivotRow (A x) k with _ | q
  · rw [sum_eq_zero fun i _ => by simp]
    simp [Bool.zero_eq_false]
  · rw [sum_eq_single q (fun q' _ hq' => by simp [Ne.symm hq']) (by simp)]
    by_cases hq : q = p.1
    · subst hq
      simp [(pivFn_eq_true_iff A k x _).mpr h, Bool.zero_eq_false]
    · have : pivFn A k p.1 x = false := by
        rw [← Bool.not_eq_true, pivFn_eq_true_iff, h]
        simpa using hq
      simp [this, hq, map_mul, Bool.mul_eq_and]

/-- **One Gauss–Jordan stage over `ZMod 2`**: the bits of `stage (A x) k` cost at most
`14 (r + 1) (r + c + 1)` gates on top of the bits of `A x`. -/
theorem synthesis_entryBits_stage {s : Set (BooleanFunction n)} (hA : entryBits A ⊆ s) :
    Synthesis interpretation s (entryBits fun x => stage (A x) k)
      (14 * (r + 1) * (r + c + 1)) := by
  have hentry (i : Fin r) (l : Fin c) :
      Synthesis interpretation s {fun x => bitEquiv (A x i l)} 0 :=
    Synthesis.of_mem (hA (entry_mem_entryBits A i l))
  -- candidates
  have h₁ : Synthesis interpretation s (Set.range (candFn A k)) (r * (c + 3)) := by
    refine (Synthesis.family (candFn A k) (fun _ => c + 3) fun i => ?_).mono Set.Subset.rfl
      Set.Subset.rfl (by simp)
    refine (Synthesis.congr_iff ((Synthesis.exists_mem (univ.filter fun l : Fin c => l.1 < k.1) _
      (fun _ => 0) fun l _ => hentry i l).not.and (hentry i k)) fun x => by
        simp [candFn]).mono Set.Subset.rfl Set.Subset.rfl ?_
    simp only [sum_const, smul_eq_mul, zero_add, mul_one]
    have : (univ.filter fun l : Fin c => l.1 < k.1).card ≤ c :=
      (card_filter_le _ _).trans (by simp)
    omega
  -- pivots
  have h₂ : Synthesis interpretation (s ∪ Set.range (candFn A k)) (Set.range (pivFn A k))
      (r * (r + 3)) := by
    refine (Synthesis.family (pivFn A k) (fun _ => r + 3) fun i => ?_).mono Set.Subset.rfl
      Set.Subset.rfl (by simp)
    have hcand (i' : Fin r) : Synthesis interpretation (s ∪ Set.range (candFn A k))
        {candFn A k i'} 0 := Synthesis.of_mem (Or.inr ⟨i', rfl⟩)
    refine (Synthesis.congr_iff ((hcand i).and (Synthesis.exists_mem
      (univ.filter fun i' : Fin r => i' < i) _ (fun _ => 0) fun i' _ => hcand i').not) fun x => by
        simp [pivFn]).mono Set.Subset.rfl Set.Subset.rfl ?_
    simp only [sum_const, smul_eq_mul, zero_add, mul_one]
    have : (univ.filter fun i' : Fin r => i' < i).card ≤ r :=
      (card_filter_le _ _).trans (by simp)
    omega
  -- pivot-row entries
  have h₃ : Synthesis interpretation (s ∪ (Set.range (candFn A k) ∪ Set.range (pivFn A k)))
      (Set.range (pivEntryFn A k)) (c * (5 * r + 1)) := by
    refine (Synthesis.family (pivEntryFn A k) (fun _ => 5 * r + 1) fun l => ?_).mono
      Set.Subset.rfl Set.Subset.rfl (by simp)
    have hpiv (i : Fin r) : Synthesis interpretation
        (s ∪ (Set.range (candFn A k) ∪ Set.range (pivFn A k))) {pivFn A k i} 0 :=
      Synthesis.of_mem (Or.inr (Or.inr ⟨i, rfl⟩))
    have hent (i : Fin r) : Synthesis interpretation
        (s ∪ (Set.range (candFn A k) ∪ Set.range (pivFn A k))) {fun x => bitEquiv (A x i l)} 0 :=
      Synthesis.of_mem (Or.inl (hA (entry_mem_entryBits A i l)))
    refine (Synthesis.sum univ (fun i x => pivFn A k i x && bitEquiv (A x i l)) (fun _ => 1)
      fun i _ => (hpiv i).and (hent i)).mono Set.Subset.rfl Set.Subset.rfl ?_
    simp only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul]
    omega
  -- new entries
  have h₄ : Synthesis interpretation
      (s ∪ (Set.range (candFn A k) ∪ Set.range (pivFn A k) ∪ Set.range (pivEntryFn A k)))
      (Set.range (newFn A k)) (r * c * 7) := by
    refine (Synthesis.family (newFn A k) (fun _ => 7) fun p => ?_).mono Set.Subset.rfl
      Set.Subset.rfl (by simp)
    have hent (i : Fin r) (l : Fin c) : Synthesis interpretation
        (s ∪ (Set.range (candFn A k) ∪ Set.range (pivFn A k) ∪ Set.range (pivEntryFn A k)))
        {fun x => bitEquiv (A x i l)} 0 :=
      Synthesis.of_mem (Or.inl (hA (entry_mem_entryBits A i l)))
    have hpiv : Synthesis interpretation
        (s ∪ (Set.range (candFn A k) ∪ Set.range (pivFn A k) ∪ Set.range (pivEntryFn A k)))
        {pivFn A k p.1} 0 := Synthesis.of_mem (Or.inr (Or.inl (Or.inr ⟨p.1, rfl⟩)))
    have hpe : Synthesis interpretation
        (s ∪ (Set.range (candFn A k) ∪ Set.range (pivFn A k) ∪ Set.range (pivEntryFn A k)))
        {pivEntryFn A k p.2} 0 := Synthesis.of_mem (Or.inr (Or.inr ⟨p.2, rfl⟩))
    exact ((hent p.1 p.2).xor ((hent p.1 k).and (hpiv.not.and hpe))).mono Set.Subset.rfl
      Set.Subset.rfl (by omega)
  have h := ((h₁.comp h₂).comp h₃).trans h₄
  have hset : Set.range (newFn A k) = entryBits fun x => stage (A x) k :=
    congrArg Set.range (funext (newFn_eq A k))
  rw [hset] at h
  refine h.mono Set.Subset.rfl Set.Subset.rfl ?_
  nlinarith [Nat.zero_le (r * c), Nat.zero_le (r * r)]

end Stage

/-! ### All stages and the rank -/

/-- The bits of the first `k` stages cost at most `k` times the cost of a stage. -/
theorem synthesis_entryBits_reduceUpTo (A : BitString n → Matrix (Fin r) (Fin c) (ZMod 2))
    {s : Set (BooleanFunction n)} (hA : entryBits A ⊆ s) (k : ℕ) :
    Synthesis interpretation s (entryBits fun x => reduceUpTo (A x) k)
      (k * (14 * (r + 1) * (r + c + 1))) := by
  induction k with
  | zero => exact (Synthesis.of_subset hA).mono Set.Subset.rfl Set.Subset.rfl (Nat.zero_le _)
  | succ k ih =>
    by_cases hk : k < c
    · have hstage := synthesis_entryBits_stage (fun x => reduceUpTo (A x) k) ⟨k, hk⟩
        (s := s ∪ entryBits fun x => reduceUpTo (A x) k) Set.subset_union_right
      have hset : (entryBits fun x => stage (reduceUpTo (A x) k) ⟨k, hk⟩) =
          entryBits fun x => reduceUpTo (A x) (k + 1) := by
        simp only [reduceUpTo_succ_of_lt _ hk]
      rw [hset] at hstage
      exact (ih.trans hstage).mono Set.Subset.rfl Set.Subset.rfl
        (le_of_eq (Nat.add_one_mul k _).symm)
    · have hset : (entryBits fun x => reduceUpTo (A x) (k + 1)) =
          entryBits fun x => reduceUpTo (A x) k := by
        simp only [reduceUpTo_succ_of_le _ (Nat.le_of_not_lt hk)]
      rw [hset]
      exact ih.mono Set.Subset.rfl Set.Subset.rfl (Nat.mul_le_mul_right _ (Nat.le_succ k))

/-- **Gauss–Jordan elimination over `ZMod 2`**: the bits of `reduce (A x)` cost at most
`14 c (r + 1) (r + c + 1)` gates on top of the bits of `A x`. Only the number of gates is
bounded; depth is not certified. -/
theorem synthesis_entryBits_reduce (A : BitString n → Matrix (Fin r) (Fin c) (ZMod 2))
    {s : Set (BooleanFunction n)} (hA : entryBits A ⊆ s) :
    Synthesis interpretation s (entryBits fun x => reduce (A x))
      (c * (14 * (r + 1) * (r + c + 1))) :=
  synthesis_entryBits_reduceUpTo A hA c

/-- **The rank threshold over `ZMod 2`**: the test `t ≤ (A x).rank`, for `t ≤ r + 1`, costs at
most `14 (c + 1) (r + 1) (r + c + 1)` gates on top of the bits of `A x`. It reduces `A x` and
counts the nonzero rows (`Matrix.GaussJordan.rank_eq_card_reduce_ne_zero`). Only the number of
gates is bounded; depth is not certified. -/
theorem synthesis_le_rank (A : BitString n → Matrix (Fin r) (Fin c) (ZMod 2))
    {s : Set (BooleanFunction n)} (hA : entryBits A ⊆ s) {t : ℕ} (ht : t ≤ r + 1) :
    Synthesis interpretation s {fun x => decide (t ≤ (A x).rank)}
      (14 * (c + 1) * (r + 1) * (r + c + 1)) := by
  have hred := synthesis_entryBits_reduce A hA
  -- the row tests, indexed by `ℕ` for `atLeast`
  let rowFn : ℕ → BooleanFunction n := fun i x =>
    if h : i < r then decide (∃ l ∈ (univ : Finset (Fin c)),
      bitEquiv (reduce (A x) ⟨i, h⟩ l) = true) else false
  have hrow : Synthesis interpretation (s ∪ entryBits fun x => reduce (A x))
      (⋃ i ∈ range r, {rowFn i}) (r * (c + 1 + 1)) := by
    refine (Synthesis.biUnion _ _ (fun _ => c + 1 + 1) fun i hi => ?_).mono Set.Subset.rfl
      Set.Subset.rfl (by simp)
    have hi : i < r := mem_range.mp hi
    have h := Synthesis.exists_mem (s := s ∪ entryBits fun x => reduce (A x)) univ
      (fun l x => bitEquiv (reduce (A x) ⟨i, hi⟩ l)) (fun _ => 0)
      fun l _ => Synthesis.of_mem (Or.inr (entry_mem_entryBits _ _ l))
    refine (Synthesis.congr_iff h fun x => by simp [rowFn, hi]).mono Set.Subset.rfl
      Set.Subset.rfl ?_
    simp
  have hcount := synthesis_atLeast rowFn (k := r) (j := t)
    (s := s ∪ (entryBits (fun x => reduce (A x)) ∪ ⋃ i ∈ range r, {rowFn i}))
    (fun i hi => Or.inr (Or.inr (Set.mem_biUnion (mem_range.mpr hi) rfl))) ht
  have h := (hred.comp hrow).trans hcount
  have key (x : BitString n) : atLeast rowFn r t x = true ↔ decide (t ≤ (A x).rank) = true := by
    rw [rank_eq_card_reduce_ne_zero]
    simp only [atLeast, decide_eq_true_eq]
    suffices hcard : ((range r).filter fun i => rowFn i x = true).card =
        (univ.filter fun i : Fin r => (reduce (A x)).row i ≠ 0).card by
      rw [hcard]
    rw [card_filter, card_filter, ← Fin.sum_univ_eq_sum_range]
    refine sum_congr rfl fun i _ => ?_
    have hiff : rowFn i x = true ↔ (reduce (A x)).row i ≠ 0 := by
      simp only [rowFn, i.2, dite_true, decide_eq_true_eq, mem_univ, true_and,
        bitEquiv_eq_true_iff, Ne, funext_iff, not_forall, Fin.eta, row_apply', Pi.zero_apply]
    simp only [hiff]
  refine (Synthesis.congr_iff h key).mono Set.Subset.rfl Set.Subset.rfl ?_
  nlinarith [Nat.zero_le (r * c), Nat.zero_le (r * r), Nat.zero_le (c * c),
    Nat.zero_le (c * r * r), Nat.zero_le (c * c * r)]

/-- The rank threshold when the bits of the entries are themselves synthesised, for example from
the circuit inputs. -/
theorem synthesis_le_rank_of_synthesis (A : BitString n → Matrix (Fin r) (Fin c) (ZMod 2))
    {s : Set (BooleanFunction n)} {cost : ℕ} (hA : Synthesis interpretation s (entryBits A) cost)
    {t : ℕ} (ht : t ≤ r + 1) :
    Synthesis interpretation s {fun x => decide (t ≤ (A x).rank)}
      (cost + 14 * (c + 1) * (r + 1) * (r + c + 1)) :=
  hA.trans (synthesis_le_rank A Set.subset_union_right ht)

end Cslib.Circuits.Boolean
