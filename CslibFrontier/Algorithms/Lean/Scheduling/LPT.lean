/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.Scheduling.IdenticalMachines
public import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Graham's Longest-Processing-Time Rule

Graham's longest-processing-time rule runs list scheduling with the jobs sorted by
non-increasing processing time. This module proves Graham's sharp approximation ratio
`4/3 - 1/(3m)` ([Graham1969], Theorem 2; announced in [Graham1966], §III, p. 1581): for jobs
listed in non-increasing order every list schedule satisfies `3m · C_LPT ≤ (4m - 1) · C` against
every assignment.

The proof follows the case split of the `4/3` analysis in [WilliamsonShmoys2011], Theorem 2.7, but
the second case is argued differently. If the last-finishing job is short (`3 p_j ≤ OPT`),
Graham's averaging bound already gives `4/3 - 1/(3m)`. Otherwise [WilliamsonShmoys2011] appeal to
Lemma 2.8 (LPT is optimal when every job exceeds `OPT / 3`), whose proof is left as an exercise
there. This module instead uses its own counting lemma, `exists_prefixLoad_add_le_makespan`:
since every job up to `j` is longer than `OPT / 3`, an optimal machine holds at most two of them,
so some machine is light enough when job `j` arrives. This yields the sharp constant directly.

## Main definitions

* `Cslib.Algorithms.Lean.Scheduling.lptOrder`: a permutation listing the jobs by non-increasing
  processing time.
* `lptSchedule`: the LPT rule, `listSchedule` applied in `lptOrder`.

## Main results

* `makespan_comp_perm`, `optMakespan_comp_perm`: relabelling the jobs preserves the makespan
  and the optimum.
* `IsListSchedule.card_mul_makespan_le_of_antitone`,
  `IsListSchedule.makespan_le_optMakespan_of_antitone`: the LPT bound for any list schedule of
  jobs in non-increasing order.
* `makespan_lptSchedule_le`: **Graham's LPT theorem**
  `C_LPT ≤ (4/3 - 1/(3m)) · OPT` ([Graham1969], Theorem 2).
* `makespan_listSchedule_le`: Graham's `2 - 1/m` bound for `listSchedule`.

## References

* [Graham1966] R. L. Graham, *Bounds for certain multiprocessing anomalies*, 1966.
* [Graham1969] R. L. Graham, *Bounds on multiprocessing timing anomalies*, 1969. The theorem
  number is taken from secondary sources; the bound itself is also announced in [Graham1966].
* [WilliamsonShmoys2011] David P. Williamson and David B. Shmoys, *The Design of Approximation
  Algorithms*, Theorem 2.7 and Lemma 2.8 (the `4/3` bound), 2011.
-/

public section

namespace Cslib.Algorithms.Lean.Scheduling

open Finset

variable {α : Type*} {n m : ℕ}

section Reindex

variable [AddCommMonoid α]

/-- Relabelling the jobs does not change the machine loads. -/
theorem load_comp_perm (p : Fin n → α) (σ : Fin n → Fin m) (e : Equiv.Perm (Fin n))
    (i : Fin m) : load (p ∘ e) (σ ∘ e) i = load p σ i := by
  rw [load_def, load_def, sum_filter, sum_filter]
  exact Equiv.sum_comp e (fun j => if σ j = i then p j else 0)

variable [LinearOrder α] [NeZero m]

/-- Relabelling the jobs does not change the makespan. -/
theorem makespan_comp_perm (p : Fin n → α) (σ : Fin n → Fin m) (e : Equiv.Perm (Fin n)) :
    makespan (p ∘ e) (σ ∘ e) = makespan p σ := by
  rw [makespan_def, makespan_def]
  simp only [load_comp_perm]

/-- Relabelling the jobs does not change the optimal makespan. -/
theorem optMakespan_comp_perm (p : Fin n → α) (e : Equiv.Perm (Fin n)) :
    optMakespan m (p ∘ e) = optMakespan m p := by
  refine le_antisymm ?_ ?_
  · obtain ⟨σ, hσ⟩ := exists_makespan_eq_optMakespan (m := m) p
    rw [← hσ, ← makespan_comp_perm p σ e]
    exact optMakespan_le _ _
  · obtain ⟨σ, hσ⟩ := exists_makespan_eq_optMakespan (m := m) (p ∘ e)
    rw [← hσ]
    calc optMakespan m p ≤ makespan p (σ ∘ e.symm) := optMakespan_le _ _
      _ = makespan (p ∘ e) σ := by
          rw [← makespan_comp_perm p (σ ∘ e.symm) e]
          congr 1 with j : 1
          simp

end Reindex

section LPT

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α] [NeZero m]

/-- The counting step of the LPT analysis. Let `τ` be any assignment with makespan `T`, and let job
`j` be no longer than the jobs before it, with `T < 3 · p j`. Then in any assignment `σ` of the
jobs before `j` some machine has load at most `T - p j`. Each machine of `τ` holds at most two of
the jobs `0, …, j`; if every machine of `σ` had load above `T - p j`, every machine of `σ` would
carry an earlier job, and the jobs alone on their machine could share a `τ`-machine with no other
job, which leaves too few `τ`-places for the `j + 1` jobs. This replaces the appeal to
[WilliamsonShmoys2011], Lemma 2.8, in their `4/3` proof; the counting argument is this module's
own route to the sharp constant. -/
theorem exists_prefixLoad_add_le_makespan (p : Fin n → α) (hp : ∀ k, 0 ≤ p k)
    (σ τ : Fin n → Fin m) (j : Fin n) (hanti : ∀ k ≤ j, p j ≤ p k) (hj : makespan p τ < 3 * p j) :
    ∃ i, prefixLoad p σ j i + p j ≤ makespan p τ := by
  by_contra hcon
  push Not at hcon
  set T := makespan p τ
  have hpj : p j ≤ T := le_makespan p hp τ j
  -- The `σ` side: the jobs before `j`, grouped by machine.
  set E : Finset (Fin n) := univ.filter fun k => k.val < j.val with hE
  set F : Fin m → Finset (Fin n) := fun i => E.filter fun k => σ k = i with hF
  have hEcard : #E = j.val := by
    rw [show E = Iio j by
      ext k; simp only [hE, mem_filter, mem_univ, true_and, mem_Iio, Fin.lt_def]]
    exact Fin.card_Iio j
  have hFload : ∀ i, prefixLoad p σ j i = ∑ k ∈ F i, p k := by
    intro i
    simp only [prefixLoad_def, hF, hE, filter_filter]
  have hFne : ∀ i, (F i).Nonempty := by
    intro i
    by_contra h
    rw [not_nonempty_iff_eq_empty] at h
    have := hcon i
    rw [hFload, h, sum_empty, zero_add] at this
    exact absurd this (not_lt.mpr hpj)
  set S : Finset (Fin m) := univ.filter fun i => #(F i) = 1 with hS
  have hσcount : 2 * m ≤ j.val + #S := by
    have h1 : ∀ i, 2 ≤ #(F i) + if #(F i) = 1 then 1 else 0 := by
      intro i
      have := (hFne i).card_pos
      split_ifs with h <;> omega
    have h2 : ∑ i, #(F i) = j.val := by
      rw [← hEcard, card_eq_sum_card_fiberwise (f := σ) (t := univ) fun _ _ => mem_univ _]
    have h3 : ∑ i, (if #(F i) = 1 then 1 else 0) = #S := by
      rw [hS, card_filter]
    calc 2 * m = ∑ _i : Fin m, 2 := by simp [mul_comm]
      _ ≤ ∑ i, (#(F i) + if #(F i) = 1 then 1 else 0) := sum_le_sum fun i _ => h1 i
      _ = j.val + #S := by rw [sum_add_distrib, h2, h3]
  -- The jobs alone on their `σ`-machine; each is longer than `T - p j`.
  set A : Finset (Fin n) := E.filter fun k => #(F (σ k)) = 1 with hA
  have hAcard : #A = #S := by
    rw [card_eq_sum_card_fiberwise (f := σ) (t := S) (s := A)]
    · rw [card_eq_sum_ones S]
      refine sum_congr rfl fun i hi => ?_
      rw [hS, mem_filter] at hi
      rw [← hi.2, hA, filter_filter]
      congr 1
      refine filter_congr fun k _ => ?_
      constructor
      · rintro ⟨-, rfl⟩; rfl
      · rintro rfl; exact ⟨hi.2, rfl⟩
    · intro k hk
      rw [hA, coe_filter] at hk
      simpa [hS] using hk.2
  have hAbig : ∀ a ∈ A, T < p a + p j := by
    intro a ha
    rw [hA, mem_filter] at ha
    obtain ⟨b, hb⟩ := card_eq_one.mp ha.2
    have hab : a ∈ F (σ a) := by simp [hF, ha.1]
    rw [hb, mem_singleton] at hab
    have := hcon (σ a)
    rw [hFload, hb, sum_singleton, ← hab] at this
    exact this
  -- The `τ` side: the jobs `0, …, j`, grouped by machine.
  set J : Finset (Fin n) := univ.filter fun k => k ≤ j with hJ
  set G : Fin m → Finset (Fin n) := fun i => J.filter fun k => τ k = i with hG
  have hJcard : #J = j.val + 1 := by
    rw [show J = Iic j by ext k; simp [hJ]]
    exact Fin.card_Iic j
  have hJp : ∀ k ∈ J, p j ≤ p k := fun k hk => hanti k (by simpa [hJ] using hk)
  have hGsum : ∀ i, ∑ k ∈ G i, p k ≤ T := by
    intro i
    refine le_trans ?_ (load_le_makespan p τ i)
    rw [load_def]
    refine sum_le_sum_of_subset_of_nonneg ?_ fun k _ _ => hp k
    intro k hk
    simp only [hG, mem_filter] at hk
    simp [hk.2]
  have hGcard : ∀ i, #(G i) ≤ 2 := by
    intro i
    by_contra h
    push Not at h
    have h1 := card_nsmul_le_sum (G i) p (p j) fun k hk => hJp k (mem_filter.mp hk).1
    rw [nsmul_eq_mul] at h1
    have h3 : (3 : α) ≤ #(G i) := by exact_mod_cast h
    have hpj0 : 0 ≤ p j := hp j
    nlinarith [hGsum i]
  have hAJ : ∀ a ∈ A, a ∈ J := by
    intro a ha
    simp only [hA, hE, mem_filter, mem_univ, true_and] at ha
    simp only [hJ, mem_filter, mem_univ, true_and]
    exact Fin.le_def.mpr ha.1.le
  have hGA : ∀ a ∈ A, G (τ a) = {a} := by
    intro a ha
    ext b
    simp only [hG, mem_filter, mem_singleton]
    constructor
    · rintro ⟨hbJ, hb⟩
      by_contra hne
      have hsub : ({a, b} : Finset (Fin n)) ⊆ G (τ a) := by
        intro k hk
        simp only [mem_insert, mem_singleton] at hk
        rcases hk with rfl | rfl
        · exact mem_filter.mpr ⟨hAJ k ha, rfl⟩
        · exact mem_filter.mpr ⟨hbJ, hb⟩
      have h1 : p a + p b ≤ T := by
        rw [← sum_pair (Ne.symm hne)]
        exact le_trans (sum_le_sum_of_subset_of_nonneg hsub fun k _ _ => hp k) (hGsum _)
      have := hAbig a ha
      have := hJp b hbJ
      linarith
    · rintro rfl
      exact ⟨hAJ b ha, rfl⟩
  have hinj : Set.InjOn τ A := by
    intro a ha b hb hab
    have h1 := hGA a ha
    rw [hab, hGA b hb] at h1
    exact (singleton_injective h1).symm
  set M : Finset (Fin m) := A.image τ with hM
  have hMcard : #M = #A := card_image_of_injOn hinj
  have hτcount : j.val + 1 + #M ≤ 2 * m := by
    have h1 : ∀ i, #(G i) + (if i ∈ M then 1 else 0) ≤ 2 := by
      intro i
      split_ifs with h
      · obtain ⟨a, ha, rfl⟩ := mem_image.mp h
        rw [hGA a ha, card_singleton]
      · have := hGcard i
        omega
    have h2 : ∑ i, #(G i) = j.val + 1 := by
      rw [← hJcard, card_eq_sum_card_fiberwise (f := τ) (t := univ) fun _ _ => mem_univ _]
    have h3 : ∑ i, (if i ∈ M then 1 else 0) = #M := by
      rw [← card_filter, filter_mem_eq_inter, univ_inter]
    calc j.val + 1 + #M = ∑ i, (#(G i) + if i ∈ M then 1 else 0) := by
          rw [sum_add_distrib, h2, h3]
      _ ≤ ∑ _i : Fin m, 2 := sum_le_sum fun i _ => h1 i
      _ = 2 * m := by simp [mul_comm]
  omega

/-- **Graham's LPT bound** for jobs listed in non-increasing order ([Graham1969], Theorem 2):
every list schedule has makespan at most `4/3 - 1/(3m)` times the makespan of any assignment,
stated as `3m · C_LPT ≤ (4m - 1) · C`. The case split follows the `4/3` proof of
[WilliamsonShmoys2011], Theorem 2.7, with `exists_prefixLoad_add_le_makespan` for long jobs. -/
theorem IsListSchedule.card_mul_makespan_le_of_antitone {p : Fin n → α} {σ : Fin n → Fin m}
    (hσ : IsListSchedule p σ) (hp : ∀ j, 0 ≤ p j) (hanti : Antitone p) (τ : Fin n → Fin m) :
    3 * (m : α) * makespan p σ ≤ (4 * m - 1) * makespan p τ := by
  have hm : (1 : α) ≤ m := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne m)
  set T := makespan p τ
  have hsum := sum_le_card_nsmul_makespan p τ
  rw [nsmul_eq_mul] at hsum
  have hT : 0 ≤ T := by
    have : (0 : α) ≤ ∑ j, p j := sum_nonneg fun j _ => hp j
    nlinarith
  have hpos : (0 : α) < 3 * m := by linarith
  have hB : 0 ≤ (4 * m - 1) * T / (3 * m) :=
    div_nonneg (mul_nonneg (by linarith) hT) hpos.le
  rw [← le_div_iff₀' hpos, makespan_le_iff]
  refine load_le_of_forall_completion_le p σ hB fun j => ?_
  rw [le_div_iff₀' hpos]
  by_cases hsmall : 3 * p j ≤ T
  · have := hσ.completion_le hp j
    nlinarith
  · push Not at hsmall
    obtain ⟨i, hi⟩ :=
      exists_prefixLoad_add_le_makespan p hp σ τ j (fun k hk => hanti hk) hsmall
    have := hσ.prefixLoad_le j i
    nlinarith

/-- **Graham's LPT bound against the optimum**: `C_LPT ≤ (4/3 - 1/(3m)) · OPT`. -/
theorem IsListSchedule.makespan_le_optMakespan_of_antitone {p : Fin n → α} {σ : Fin n → Fin m}
    (hσ : IsListSchedule p σ) (hp : ∀ j, 0 ≤ p j) (hanti : Antitone p) :
    makespan p σ ≤ (4 / 3 - 1 / (3 * m)) * optMakespan m p := by
  obtain ⟨τ, hτ⟩ := exists_makespan_eq_optMakespan (m := m) p
  have h := hσ.card_mul_makespan_le_of_antitone hp hanti τ
  rw [hτ] at h
  have hmpos : (0 : α) < 3 * m := by
    have : (0 : α) < m := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
    linarith
  have hm0 : (m : α) ≠ 0 := by exact_mod_cast NeZero.ne m
  have heq : (4 / 3 - 1 / (3 * (m : α))) * optMakespan m p =
      (4 * m - 1) * optMakespan m p / (3 * m) := by
    field_simp
  rw [heq, le_div_iff₀' hmpos]
  exact h

end LPT

section Algorithm

variable [LinearOrder α]

/-- An ordering of the jobs by non-increasing processing time (`Tuple.sort` for the dual order),
so that `p ∘ lptOrder p` is antitone. -/
def lptOrder (p : Fin n → α) : Equiv.Perm (Fin n) :=
  Tuple.sort fun j => OrderDual.toDual (p j)

theorem antitone_comp_lptOrder (p : Fin n → α) : Antitone (p ∘ lptOrder p) :=
  fun _ _ hab => OrderDual.toDual_le_toDual.mp (Tuple.monotone_sort _ hab)

variable [AddCommMonoid α] [NeZero m]

/-- **Graham's LPT rule** ([Graham1969]): list scheduling with the jobs taken in non-increasing
order of processing time, ties broken by lowest machine index. -/
def lptSchedule (p : Fin n → α) : Fin n → Fin m :=
  listSchedule (p ∘ lptOrder p) ∘ (lptOrder p).symm

theorem makespan_lptSchedule (p : Fin n → α) :
    makespan p (lptSchedule (m := m) p) =
      makespan (p ∘ lptOrder p) (listSchedule (m := m) (p ∘ lptOrder p)) := by
  rw [← makespan_comp_perm p (lptSchedule p) (lptOrder p)]
  congr 1 with j : 1
  simp [lptSchedule]

end Algorithm

section Bound

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α] [NeZero m]

/-- **Graham's bound for `listSchedule`**: `C_LS ≤ (2 - 1/m) · OPT` ([Graham1966];
[WilliamsonShmoys2011], Theorem 2.6 and the refinement after Theorem 2.5). -/
theorem makespan_listSchedule_le (p : Fin n → α) (hp : ∀ j, 0 ≤ p j) :
    makespan p (listSchedule (m := m) p) ≤ (2 - 1 / m) * optMakespan m p :=
  (isListSchedule_listSchedule p).makespan_le_optMakespan hp

/-- **Graham's LPT theorem** ([Graham1969], Theorem 2): `C_LPT ≤ (4/3 - 1/(3m)) · OPT`. The
weaker `4/3` bound is [WilliamsonShmoys2011], Theorem 2.7. -/
theorem makespan_lptSchedule_le (p : Fin n → α) (hp : ∀ j, 0 ≤ p j) :
    makespan p (lptSchedule (m := m) p) ≤ (4 / 3 - 1 / (3 * m)) * optMakespan m p := by
  rw [makespan_lptSchedule, ← optMakespan_comp_perm p (lptOrder p)]
  exact (isListSchedule_listSchedule _).makespan_le_optMakespan_of_antitone (fun j => hp _)
    (antitone_comp_lptOrder p)

end Bound

end Cslib.Algorithms.Lean.Scheduling
