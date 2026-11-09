/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.GetD
import Mathlib.Data.List.MinMax
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# List Scheduling on Identical Machines

This module models non-preemptive scheduling of `n` jobs with processing times `p : Fin n → α`
on `m` identical machines (`P || C_max` in the three-field notation). An assignment
`σ : Fin n → Fin m` has machine loads `load p σ` and makespan `makespan p σ`; `optMakespan m p`
is the minimum over all `m ^ n` assignments. With the jobs processed in list order, job `j` starts
on machine `σ j` at time `prefixLoad p σ j (σ j)`, the load of that machine over the earlier jobs.
`IsListSchedule p σ` states that every job goes to a machine of minimum load over the earlier
jobs ([Graham1966]), and `listSchedule` is the computable rule with lowest-index tie-breaking.

## Main definitions

* `Cslib.Algorithms.Lean.Scheduling.load`, `prefixLoad`, `makespan`, `optMakespan`: machine loads,
  loads over the first `k` jobs, makespan and optimal makespan.
* `IsListSchedule`: Graham's list-scheduling rule as a property of an assignment.
* `argminFin`, `listScheduleAux`, `listSchedule`: computable least-loaded machine and list
  scheduling.
* `grahamTight`: the tight instance with `m (m - 1)` unit jobs and one job of length `m`.

## Main results

* `sum_le_card_nsmul_optMakespan`, `le_optMakespan`: the lower bounds `∑ p ≤ m · OPT` and
  `p j ≤ OPT` ([WilliamsonShmoys2011], (2.4) and (2.3)).
* `IsListSchedule.card_mul_makespan_le`, `IsListSchedule.makespan_le_optMakespan`: **Graham's
  bound** `C_LS ≤ (2 - 1/m) · OPT` ([Graham1966], §II, Theorem (p. 1570) with `n = n'`;
  [WilliamsonShmoys2011], Section 2.3).
* `isListSchedule_listSchedule`: `listSchedule` satisfies `IsListSchedule`.
* `optMakespan_grahamTight`, `IsListSchedule.makespan_grahamTight`: on `grahamTight α m` every
  list schedule has makespan exactly `(2 - 1/m) · OPT = 2m - 1`, so the bound is tight for
  every `m`.

## References

* [Graham1966] R. L. Graham, *Bounds for certain multiprocessing anomalies*, 1966.
* [WilliamsonShmoys2011] David P. Williamson and David B. Shmoys, *The Design of Approximation
  Algorithms*, Section 2.3, 2011.
-/

public section

namespace Cslib.Algorithms.Lean.Scheduling

open Finset

variable {α : Type*} {n m : ℕ}

section Defs

variable [AddCommMonoid α]

/-- The load of machine `i` under the assignment `σ`: the total processing time of the jobs
assigned to `i`. -/
def load (p : Fin n → α) (σ : Fin n → Fin m) (i : Fin m) : α :=
  ∑ j with σ j = i, p j

/-- The load of machine `i` counting only the jobs `j` with `j < k`. With jobs processed in list
order, `prefixLoad p σ j i` is the time at which machine `i` becomes free before job `j`. -/
def prefixLoad (p : Fin n → α) (σ : Fin n → Fin m) (k : ℕ) (i : Fin m) : α :=
  ∑ j : Fin n with j.val < k ∧ σ j = i, p j

/-- List scheduling ([Graham1966], §I.1; [WilliamsonShmoys2011], §2.3): each job, taken in list
order, is assigned to a machine of minimum load over the earlier jobs. -/
def IsListSchedule [LE α] (p : Fin n → α) (σ : Fin n → Fin m) : Prop :=
  ∀ (j : Fin n) (i : Fin m), prefixLoad p σ j (σ j) ≤ prefixLoad p σ j i

end Defs

section Basic

variable [AddCommMonoid α]

theorem load_def (p : Fin n → α) (σ : Fin n → Fin m) (i : Fin m) :
    load p σ i = ∑ j with σ j = i, p j := by
  unfold load; rfl

theorem prefixLoad_def (p : Fin n → α) (σ : Fin n → Fin m) (k : ℕ) (i : Fin m) :
    prefixLoad p σ k i = ∑ j : Fin n with j.val < k ∧ σ j = i, p j := by
  unfold prefixLoad; rfl

theorem isListSchedule_iff [LE α] (p : Fin n → α) (σ : Fin n → Fin m) :
    IsListSchedule p σ ↔
      ∀ (j : Fin n) (i : Fin m), prefixLoad p σ j (σ j) ≤ prefixLoad p σ j i := by
  unfold IsListSchedule; rfl

/-- In a list schedule, job `j` starts on a machine that was least loaded before `j`. -/
theorem IsListSchedule.prefixLoad_le [LE α] {p : Fin n → α} {σ : Fin n → Fin m}
    (hσ : IsListSchedule p σ) (j : Fin n) (i : Fin m) :
    prefixLoad p σ j (σ j) ≤ prefixLoad p σ j i :=
  hσ j i

theorem prefixLoad_zero (p : Fin n → α) (σ : Fin n → Fin m) (i : Fin m) :
    prefixLoad p σ 0 i = 0 := by
  simp [prefixLoad]

theorem prefixLoad_of_le (p : Fin n → α) (σ : Fin n → Fin m) {k : ℕ} (hk : n ≤ k) (i : Fin m) :
    prefixLoad p σ k i = load p σ i := by
  unfold prefixLoad load
  congr 1
  ext j
  simp only [mem_filter, mem_univ, true_and, and_iff_right_iff_imp]
  exact fun _ => lt_of_lt_of_le j.isLt hk

theorem prefixLoad_succ (p : Fin n → α) (σ : Fin n → Fin m) (j : Fin n) (i : Fin m) :
    prefixLoad p σ (j + 1) i = prefixLoad p σ j i + if σ j = i then p j else 0 := by
  unfold prefixLoad
  have : (univ.filter fun k : Fin n => (k : ℕ) < j + 1 ∧ σ k = i) =
      (univ.filter fun k : Fin n => (k : ℕ) < j ∧ σ k = i) ∪
        (univ.filter fun k : Fin n => k = j ∧ σ k = i) := by
    ext k
    simp only [mem_filter, mem_univ, true_and, mem_union]
    constructor
    · rintro ⟨hk, hσ⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with h | h
      · exact Or.inl ⟨h, hσ⟩
      · exact Or.inr ⟨Fin.ext h, hσ⟩
    · rintro (⟨hk, hσ⟩ | ⟨rfl, hσ⟩)
      · exact ⟨by omega, hσ⟩
      · exact ⟨by omega, hσ⟩
  rw [this, sum_union]
  · congr 1
    split_ifs with h
    · rw [show (univ.filter fun k : Fin n => k = j ∧ σ k = i) = {j} by
        ext k; simp only [mem_filter, mem_univ, true_and, mem_singleton]
        exact ⟨fun h' => h'.1, fun h' => ⟨h', h' ▸ h⟩⟩]
      simp
    · rw [sum_eq_zero]
      intro k hk
      simp only [mem_filter, mem_univ, true_and] at hk
      exact absurd (hk.1 ▸ hk.2) h
  · rw [disjoint_filter]
    rintro k - ⟨hk, -⟩ ⟨rfl, -⟩
    omega

/-- The machine loads before job `k` add up to the total processing time of the jobs `j < k`. -/
theorem sum_prefixLoad (p : Fin n → α) (σ : Fin n → Fin m) (k : ℕ) :
    ∑ i, prefixLoad p σ k i = ∑ j : Fin n with j.val < k, p j := by
  unfold prefixLoad
  rw [← sum_fiberwise (univ.filter fun j : Fin n => (j : ℕ) < k) σ p]
  refine sum_congr rfl fun i _ => ?_
  rw [filter_filter]

/-- The machine loads add up to the total processing time. -/
theorem sum_load (p : Fin n → α) (σ : Fin n → Fin m) : ∑ i, load p σ i = ∑ j, p j := by
  simp_rw [← prefixLoad_of_le p σ le_rfl, sum_prefixLoad]
  congr 1
  ext j
  simp

end Basic

section Makespan

variable [AddCommMonoid α] [LinearOrder α] [NeZero m]

/-- The makespan of an assignment: the maximum machine load. -/
def makespan (p : Fin n → α) (σ : Fin n → Fin m) : α :=
  univ.sup' univ_nonempty (load p σ)

variable (m) in
/-- The optimal makespan over all assignments of the jobs to `m` machines. -/
noncomputable def optMakespan (p : Fin n → α) : α :=
  (univ : Finset (Fin n → Fin m)).inf' univ_nonempty (makespan p)

theorem makespan_def (p : Fin n → α) (σ : Fin n → Fin m) :
    makespan p σ = univ.sup' univ_nonempty (load p σ) := by
  unfold makespan; rfl

theorem load_le_makespan (p : Fin n → α) (σ : Fin n → Fin m) (i : Fin m) :
    load p σ i ≤ makespan p σ :=
  le_sup' _ (mem_univ i)

theorem makespan_le_iff (p : Fin n → α) (σ : Fin n → Fin m) {B : α} :
    makespan p σ ≤ B ↔ ∀ i, load p σ i ≤ B := by
  simp [makespan]

theorem optMakespan_le (p : Fin n → α) (σ : Fin n → Fin m) :
    optMakespan m p ≤ makespan p σ :=
  inf'_le _ (mem_univ σ)

theorem exists_makespan_eq_optMakespan (p : Fin n → α) :
    ∃ σ : Fin n → Fin m, makespan p σ = optMakespan m p := by
  obtain ⟨σ, -, h⟩ := exists_mem_eq_inf' (univ_nonempty (α := Fin n → Fin m)) (makespan p)
  exact ⟨σ, h.symm⟩

end Makespan

section LowerBounds

variable [AddCommMonoid α] [LinearOrder α] [IsOrderedAddMonoid α] [NeZero m]

/-- The total processing time is at most `m` times the makespan of any assignment. -/
theorem sum_le_card_nsmul_makespan (p : Fin n → α) (σ : Fin n → Fin m) :
    ∑ j, p j ≤ m • makespan p σ := by
  rw [← sum_load]
  calc ∑ i, load p σ i ≤ ∑ _i : Fin m, makespan p σ :=
        sum_le_sum fun i _ => load_le_makespan p σ i
    _ = m • makespan p σ := by simp

/-- Every job's processing time is at most the makespan, for nonnegative processing times. -/
theorem le_makespan (p : Fin n → α) (hp : ∀ j, 0 ≤ p j) (σ : Fin n → Fin m) (j : Fin n) :
    p j ≤ makespan p σ :=
  calc p j ≤ load p σ (σ j) :=
        single_le_sum (f := p) (fun k _ => hp k) (by simp)
    _ ≤ makespan p σ := load_le_makespan p σ _

/-- Average-load lower bound on the optimum, `∑ p ≤ m · OPT` ([WilliamsonShmoys2011], (2.4)). -/
theorem sum_le_card_nsmul_optMakespan (p : Fin n → α) : ∑ j, p j ≤ m • optMakespan m p := by
  obtain ⟨σ, hσ⟩ := exists_makespan_eq_optMakespan (m := m) p
  rw [← hσ]
  exact sum_le_card_nsmul_makespan p σ

/-- Longest-job lower bound on the optimum ([WilliamsonShmoys2011], (2.3)). -/
theorem le_optMakespan (p : Fin n → α) (hp : ∀ j, 0 ≤ p j) (j : Fin n) :
    p j ≤ optMakespan m p := by
  obtain ⟨σ, hσ⟩ := exists_makespan_eq_optMakespan (m := m) p
  rw [← hσ]
  exact le_makespan p hp σ j

end LowerBounds

section Completion

variable [AddCommMonoid α] [LinearOrder α]

/-- If every job finishes by `B` (its start `prefixLoad p σ j (σ j)` plus `p j`), then every
machine load is at most `B`. -/
theorem load_le_of_forall_completion_le (p : Fin n → α) (σ : Fin n → Fin m) {B : α}
    (hB : 0 ≤ B) (h : ∀ j : Fin n, prefixLoad p σ j (σ j) + p j ≤ B) (i : Fin m) :
    load p σ i ≤ B := by
  have key : ∀ k ≤ n, prefixLoad p σ k i ≤ B := by
    intro k
    induction k with
    | zero => intro; rw [prefixLoad_zero]; exact hB
    | succ k ih =>
      intro hk
      have := prefixLoad_succ p σ ⟨k, hk⟩ i
      simp only at this
      rw [this]
      split_ifs with hσ
      · rw [← hσ]; exact h ⟨k, hk⟩
      · rw [add_zero]; exact ih (by omega)
  rw [← prefixLoad_of_le p σ le_rfl]
  exact key n le_rfl

end Completion

section Graham

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α]

/-- Graham's averaging bound for one job: under list scheduling, job `j` finishes by
`(∑_{k ≠ j} p k) / m + p j`. -/
theorem IsListSchedule.completion_le {p : Fin n → α} {σ : Fin n → Fin m} (hσ : IsListSchedule p σ)
    (hp : ∀ j, 0 ≤ p j) (j : Fin n) :
    (m : α) * (prefixLoad p σ j (σ j) + p j) ≤ ∑ k, p k + (m - 1) * p j := by
  have h1 : (m : α) * prefixLoad p σ j (σ j) ≤ ∑ i, prefixLoad p σ j i := by
    calc (m : α) * prefixLoad p σ j (σ j) = ∑ _i : Fin m, prefixLoad p σ j (σ j) := by
          simp
      _ ≤ ∑ i, prefixLoad p σ j i := sum_le_sum fun i _ => hσ j i
  have h2 : ∑ k : Fin n with k.val < j.val, p k + p j ≤ ∑ k, p k := by
    have hsub : (univ.filter fun k : Fin n => (k : ℕ) < j) ∪ {j} ⊆ univ := subset_univ _
    have hdisj : Disjoint (univ.filter fun k : Fin n => (k : ℕ) < j) {j} := by
      simp
    calc ∑ k : Fin n with k.val < j.val, p k + p j
        = ∑ k ∈ (univ.filter fun k : Fin n => (k : ℕ) < j) ∪ {j}, p k := by
          rw [sum_union hdisj, sum_singleton]
      _ ≤ ∑ k, p k := sum_le_sum_of_subset_of_nonneg hsub fun k _ _ => hp k
  rw [sum_prefixLoad] at h1
  nlinarith

variable [NeZero m]

/-- **Graham's list-scheduling bound** ([Graham1966], §II, Theorem (p. 1570) with `n = n'` and no
precedences; [WilliamsonShmoys2011], Theorem 2.6 and the refinement after Theorem 2.5): every list
schedule has makespan at most `2 - 1/m` times the makespan of any assignment, stated without
division as `m · C_LS ≤ (2m - 1) · C`. -/
theorem IsListSchedule.card_mul_makespan_le {p : Fin n → α} {σ : Fin n → Fin m}
    (hσ : IsListSchedule p σ) (hp : ∀ j, 0 ≤ p j) (τ : Fin n → Fin m) :
    (m : α) * makespan p σ ≤ (2 * m - 1) * makespan p τ := by
  have hm : (1 : α) ≤ m := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne m)
  have hsum := sum_le_card_nsmul_makespan p τ
  rw [nsmul_eq_mul] at hsum
  have hT : 0 ≤ makespan p τ := by
    have : (0 : α) ≤ ∑ j, p j := sum_nonneg fun j _ => hp j
    nlinarith
  have hB : 0 ≤ (2 * m - 1) * makespan p τ / m := by
    apply div_nonneg _ (by linarith)
    exact mul_nonneg (by linarith) hT
  have hmpos : (0 : α) < m := by linarith
  rw [← le_div_iff₀' hmpos, makespan_le_iff]
  refine load_le_of_forall_completion_le p σ hB fun j => ?_
  rw [le_div_iff₀' hmpos]
  have := hσ.completion_le hp j
  have hj := le_makespan p hp τ j
  nlinarith

/-- **Graham's bound against the optimum**: `C_LS ≤ (2 - 1/m) · OPT`. -/
theorem IsListSchedule.makespan_le_optMakespan {p : Fin n → α} {σ : Fin n → Fin m}
    (hσ : IsListSchedule p σ) (hp : ∀ j, 0 ≤ p j) :
    makespan p σ ≤ (2 - 1 / m) * optMakespan m p := by
  obtain ⟨τ, hτ⟩ := exists_makespan_eq_optMakespan (m := m) p
  have h := hσ.card_mul_makespan_le hp τ
  rw [hτ] at h
  have hmpos : (0 : α) < m := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
  rw [show (2 - 1 / (m : α)) * optMakespan m p =
    (2 * m - 1) * optMakespan m p / m by field_simp]
  rw [le_div_iff₀' hmpos]
  exact h

end Graham

section ArgMin

variable [LinearOrder α]

/-- A machine minimizing `f`, the lowest-indexed one among ties (Graham's convention that
simultaneous claims go to the processor of smaller index). -/
def argminFin [NeZero m] (f : Fin m → α) : Fin m :=
  ((List.finRange m).argmin f).getD 0

theorem argminFin_le [NeZero m] (f : Fin m → α) (i : Fin m) : f (argminFin f) ≤ f i := by
  unfold argminFin
  cases h : (List.finRange m).argmin f with
  | none =>
    rw [List.argmin_eq_none] at h
    exact absurd h (List.ne_nil_of_mem (List.mem_finRange i))
  | some x => exact List.le_of_mem_argmin (List.mem_finRange i) h

end ArgMin

section ListSchedule

variable [AddCommMonoid α] [LinearOrder α] [NeZero m]

/-- The machines chosen by list scheduling, in list order, as plain data so that each earlier
choice is computed once: job `n` goes to a least loaded machine (lowest index among ties) for the
schedule of the first `n` jobs. -/
def listScheduleAux : {n : ℕ} → (Fin n → α) → List (Fin m)
  | 0, _ => []
  | _ + 1, p =>
    let l := listScheduleAux (Fin.init p)
    l ++ [argminFin (load (Fin.init p) fun j => l.getD j 0)]

theorem length_listScheduleAux : ∀ {n : ℕ} (p : Fin n → α),
    (listScheduleAux (m := m) p).length = n
  | 0, _ => rfl
  | n + 1, p => by
    simp only [listScheduleAux, List.length_append, List.length_singleton,
      length_listScheduleAux (Fin.init p)]

/-- Graham's list scheduling in list order, with lowest-index tie-breaking. -/
def listSchedule (p : Fin n → α) (j : Fin n) : Fin m := (listScheduleAux p).getD j 0

/-- The recursive description of `listSchedule`: job `n` goes to a least loaded machine for the
schedule of the first `n` jobs. -/
theorem listSchedule_succ (p : Fin (n + 1) → α) :
    listSchedule (m := m) p = Fin.snoc (α := fun _ => Fin m) (listSchedule (Fin.init p))
      (argminFin (load (Fin.init p) (listSchedule (Fin.init p)))) := by
  funext j
  have hlen := length_listScheduleAux (m := m) (Fin.init p)
  induction j using Fin.lastCases with
  | last =>
    rw [Fin.snoc_last]
    unfold listSchedule
    simp only [listScheduleAux, Fin.val_last]
    rw [List.getD_append_right _ _ _ _ (by omega), hlen, Nat.sub_self]
    rfl
  | cast j =>
    rw [Fin.snoc_castSucc]
    unfold listSchedule
    simp only [listScheduleAux, Fin.val_castSucc]
    rw [List.getD_append _ _ _ _ (by omega)]

omit [LinearOrder α] [NeZero m] in
private theorem prefixLoad_snoc (p : Fin (n + 1) → α) (σ : Fin n → Fin m) (x : Fin m) {k : ℕ}
    (hk : k ≤ n) (i : Fin m) :
    prefixLoad p (Fin.snoc (α := fun _ => Fin m) σ x) k i = prefixLoad (Fin.init p) σ k i := by
  unfold prefixLoad
  rw [sum_filter, sum_filter, Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.val_castSucc, Fin.val_last, Fin.init]
  rw [ite_eq_right (by omega), add_zero]

/-- `listSchedule` is a list schedule. -/
theorem isListSchedule_listSchedule (p : Fin n → α) :
    IsListSchedule p (listSchedule (m := m) p) := by
  induction n with
  | zero => exact fun j => j.elim0
  | succ n ih =>
    intro j i
    rw [listSchedule_succ]
    induction j using Fin.lastCases with
    | last =>
      rw [Fin.snoc_last, Fin.val_last, prefixLoad_snoc _ _ _ le_rfl, prefixLoad_snoc _ _ _ le_rfl,
        prefixLoad_of_le _ _ le_rfl, prefixLoad_of_le _ _ le_rfl]
      exact argminFin_le _ i
    | cast j =>
      rw [Fin.snoc_castSucc, Fin.val_castSucc, prefixLoad_snoc _ _ _ j.isLt.le,
        prefixLoad_snoc _ _ _ j.isLt.le]
      exact ih (Fin.init p) j i

end ListSchedule

section Tight

/-- A prefix load with unit processing times is the cast of the number of jobs. -/
private theorem prefixLoad_eq_cast [AddCommMonoidWithOne α] (p : Fin n → α) (σ : Fin n → Fin m)
    {k : ℕ} (hp : ∀ j : Fin n, j.val < k → p j = 1) (i : Fin m) :
    prefixLoad p σ k i = ((prefixLoad (fun _ => (1 : ℕ)) σ k i : ℕ) : α) := by
  unfold prefixLoad
  rw [Nat.cast_sum]
  refine sum_congr rfl fun j hj => ?_
  rw [mem_filter] at hj
  rw [hp j hj.2.1, Nat.cast_one]

/-- The arithmetic step of the tight family: `m (m - 1) ≤ c + (m - 1)(c + 1)` forces
`m - 1 ≤ c`. -/
private theorem sub_one_le_of_mul_le {m c : ℕ} (h : m * (m - 1) ≤ c + (m - 1) * (c + 1)) :
    m - 1 ≤ c := by
  obtain _ | a := m
  · omega
  · simp only [Nat.add_sub_cancel] at h ⊢
    by_contra hlt
    push Not at hlt
    have := Nat.mul_le_mul_right (a + 1) hlt
    nlinarith

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α]

variable (α) in
/-- The standard tight instance for Graham's bound on `m` machines: `m (m - 1)` unit jobs followed
by one job of length `m`. -/
def grahamTight (m : ℕ) (j : Fin (m * (m - 1) + 1)) : α :=
  if j.val < m * (m - 1) then 1 else m

omit [LinearOrder α] [IsStrictOrderedRing α] in
theorem grahamTight_of_lt {j : Fin (m * (m - 1) + 1)} (hj : j.val < m * (m - 1)) :
    grahamTight α m j = 1 :=
  ite_eq_left hj

omit [LinearOrder α] [IsStrictOrderedRing α] in
theorem grahamTight_last : grahamTight α m (Fin.last _) = m :=
  ite_eq_right (lt_irrefl _)

theorem grahamTight_nonneg (j : Fin (m * (m - 1) + 1)) : 0 ≤ grahamTight α m j := by
  unfold grahamTight
  split_ifs
  · exact zero_le_one
  · exact Nat.cast_nonneg m

variable [NeZero m]

/-- In a list schedule of `grahamTight α m`, the long job starts no earlier than `m - 1`: list
scheduling keeps the machine loads within one of each other on unit jobs. -/
private theorem IsListSchedule.load_grahamTight {σ : Fin (m * (m - 1) + 1) → Fin m}
    (hσ : IsListSchedule (grahamTight α m) σ) : 2 * (m : α) - 1 ≤ load (grahamTight α m) σ
      (σ (Fin.last _)) := by
  set c : ℕ → Fin m → ℕ := fun k i => prefixLoad (fun _ => (1 : ℕ)) σ k i with hc
  have hpc : ∀ k ≤ m * (m - 1), ∀ i, prefixLoad (grahamTight α m) σ k i = (c k i : α) :=
    fun k hk i => prefixLoad_eq_cast _ σ (fun j hj => grahamTight_of_lt (by omega)) i
  have hstep : ∀ (k : ℕ) (hk : k < m * (m - 1) + 1) (i : Fin m),
      c (k + 1) i = c k i + if σ ⟨k, hk⟩ = i then 1 else 0 := fun k hk i =>
    prefixLoad_succ (fun _ => (1 : ℕ)) σ ⟨k, hk⟩ i
  have hmin : ∀ (k : ℕ) (hk : k ≤ m * (m - 1)) (i : Fin m),
      c k (σ ⟨k, by omega⟩) ≤ c k i := by
    intro k hk i
    have h := hσ ⟨k, by omega⟩ i
    rw [hpc k hk, hpc k hk] at h
    exact_mod_cast h
  have hbal : ∀ k ≤ m * (m - 1), ∀ i i', c k i ≤ c k i' + 1 := by
    intro k
    induction k with
    | zero =>
      intro _ i i'
      simp only [hc, prefixLoad_zero]
      omega
    | succ k ih =>
      intro hk i i'
      rw [hstep k (by omega), hstep k (by omega)]
      have h1 := ih (by omega) i i'
      have h2 := hmin k (by omega) i'
      split_ifs with hi hi' hi'
      · omega
      · rw [← hi]; omega
      · omega
      · omega
  have hsum : ∑ i, c (m * (m - 1)) i = m * (m - 1) := by
    simp only [hc]
    rw [sum_prefixLoad, sum_const, smul_eq_mul, mul_one]
    have : (univ.filter fun j : Fin (m * (m - 1) + 1) => j.val < m * (m - 1)) =
        Iio (Fin.last _) := by
      ext j
      simp only [mem_filter, mem_univ, true_and, mem_Iio, Fin.lt_def, Fin.val_last]
    rw [this, Fin.card_Iio, Fin.val_last]
  set i₀ := σ (Fin.last _) with hi₀
  have hc₀ : m - 1 ≤ c (m * (m - 1)) i₀ := by
    refine sub_one_le_of_mul_le ?_
    have hrest : ∑ i ∈ univ.erase i₀, c (m * (m - 1)) i ≤ (m - 1) * (c (m * (m - 1)) i₀ + 1) := by
      calc ∑ i ∈ univ.erase i₀, c (m * (m - 1)) i
          ≤ ∑ _i ∈ univ.erase i₀, (c (m * (m - 1)) i₀ + 1) :=
            sum_le_sum fun i _ => hbal _ le_rfl i i₀
        _ = (m - 1) * (c (m * (m - 1)) i₀ + 1) := by
            rw [sum_const, card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin,
              smul_eq_mul]
    calc m * (m - 1) = c (m * (m - 1)) i₀ + ∑ i ∈ univ.erase i₀, c (m * (m - 1)) i := by
          rw [add_sum_erase _ _ (mem_univ i₀), hsum]
      _ ≤ c (m * (m - 1)) i₀ + (m - 1) * (c (m * (m - 1)) i₀ + 1) := Nat.add_le_add_left hrest _
  have hload : load (grahamTight α m) σ i₀ = (c (m * (m - 1)) i₀ : α) + m := by
    have h := prefixLoad_succ (grahamTight α m) σ (Fin.last _) i₀
    rw [Fin.val_last, prefixLoad_of_le _ σ le_rfl, hpc _ le_rfl, ← hi₀, ite_eq_left rfl,
      grahamTight_last] at h
    exact h
  rw [hload]
  have hm : (1 : ℕ) ≤ m := Nat.one_le_iff_ne_zero.mpr (NeZero.ne m)
  have h1 : ((m - 1 : ℕ) : α) ≤ c (m * (m - 1)) i₀ := by exact_mod_cast hc₀
  rw [Nat.cast_sub hm, Nat.cast_one] at h1
  linarith

variable (α m) in
/-- The optimum of the tight instance is `m`: the long job alone on one machine, and `m` unit jobs
on each of the others. -/
theorem optMakespan_grahamTight : optMakespan m (grahamTight α m) = m := by
  have hm : (1 : ℕ) ≤ m := Nat.one_le_iff_ne_zero.mpr (NeZero.ne m)
  refine le_antisymm ?_ ?_
  · -- Unit job `j` goes to machine `j / m + 1`, the long job to machine `0`.
    have hlt : ∀ j : Fin (m * (m - 1) + 1), j.val < m * (m - 1) → j.val / m + 1 < m := by
      intro j hj
      have : j.val / m < m - 1 :=
        (Nat.div_lt_iff_lt_mul (by omega)).mpr (hj.trans_eq (Nat.mul_comm _ _))
      omega
    let τ : Fin (m * (m - 1) + 1) → Fin m := fun j =>
      if hj : j.val < m * (m - 1) then ⟨j.val / m + 1, hlt j hj⟩ else ⟨0, by omega⟩
    have hτ : ∀ j i, τ j = i → (j.val < m * (m - 1) ∧ i.val = j.val / m + 1) ∨
        (j = Fin.last _ ∧ i.val = 0) := by
      intro j i h
      subst h
      by_cases hj : j.val < m * (m - 1)
      · exact Or.inl ⟨hj, by simp [τ, hj]⟩
      · have := j.isLt
        exact Or.inr ⟨Fin.ext (by rw [Fin.val_last]; omega), by simp [τ, hj]⟩
    refine (optMakespan_le _ τ).trans ((makespan_le_iff _ τ).mpr fun i => ?_)
    unfold load
    by_cases hi : i.val = 0
    · calc ∑ j with τ j = i, grahamTight α m j ≤ ∑ j ∈ {Fin.last _}, grahamTight α m j := by
            refine sum_le_sum_of_subset_of_nonneg (fun j hj => ?_)
              fun j _ _ => grahamTight_nonneg j
            rw [mem_filter] at hj
            rcases hτ j i hj.2 with h | h
            · exact absurd (h.2.symm.trans hi) (Nat.succ_ne_zero _)
            · exact mem_singleton.mpr h.1
        _ = m := by rw [sum_singleton, grahamTight_last]
    · have hunit : ∀ j ∈ univ.filter fun j => τ j = i, grahamTight α m j = 1 := by
        intro j hj
        rw [mem_filter] at hj
        rcases hτ j i hj.2 with h | h
        · exact grahamTight_of_lt h.1
        · omega
      rw [sum_congr rfl hunit, sum_const, nsmul_eq_mul, mul_one]
      have hcard : #(univ.filter fun j => τ j = i) ≤ m := by
        calc #(univ.filter fun j => τ j = i) ≤ #(range m) := by
              refine card_le_card_of_injOn (fun j => j.val % m) (fun j _ => ?_) ?_
              · exact mem_range.mpr (Nat.mod_lt _ (by omega))
              · intro j hj j' hj' hjj'
                rw [mem_coe, mem_filter] at hj hj'
                rcases hτ j i hj.2 with h | h
                · rcases hτ j' i hj'.2 with h' | h'
                  · apply Fin.ext
                    rw [← Nat.div_add_mod j.val m, ← Nat.div_add_mod j'.val m]
                    simp only at hjj'
                    rw [hjj', Nat.add_right_cancel (h.2.symm.trans h'.2)]
                  · exact absurd (h.2.symm.trans h'.2) (Nat.succ_ne_zero _)
                · omega
          _ = m := card_range m
      exact_mod_cast hcard
  · calc (m : α) = grahamTight α m (Fin.last _) := grahamTight_last.symm
      _ ≤ optMakespan m (grahamTight α m) := le_optMakespan _ grahamTight_nonneg _

/-- **Tightness of Graham's bound.** Every list schedule of `grahamTight α m` has makespan
`2m - 1 = (2 - 1/m) · OPT`, so the ratio of `IsListSchedule.makespan_le_optMakespan` is attained on
`m` machines for every `m`. -/
theorem IsListSchedule.makespan_grahamTight {σ : Fin (m * (m - 1) + 1) → Fin m}
    (hσ : IsListSchedule (grahamTight α m) σ) :
    makespan (grahamTight α m) σ = (2 - 1 / m) * optMakespan m (grahamTight α m) := by
  have hmpos : (0 : α) < m := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
  rw [optMakespan_grahamTight, sub_mul, div_mul_cancel₀ _ hmpos.ne']
  refine le_antisymm ?_ ((hσ.load_grahamTight).trans (load_le_makespan _ σ _))
  have h := hσ.makespan_le_optMakespan grahamTight_nonneg
  rw [optMakespan_grahamTight, sub_mul, div_mul_cancel₀ _ hmpos.ne'] at h
  exact h

end Tight

end Cslib.Algorithms.Lean.Scheduling
