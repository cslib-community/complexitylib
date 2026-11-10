/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.List.Chain
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# List Scheduling with Precedence Constraints

This module models non-preemptive scheduling of a finite set `J` of jobs with integer processing
times `p : J → ℕ` and a precedence relation `prec` on `m` identical machines
(`P | prec | C_max`) in discrete time. A schedule is given by start times `s : J → ℕ`. Job `j`
occupies the unit time slots `s j, …, s j + p j - 1`. `IsFeasible m prec p s` requires each job to
start after its predecessors finish and at most `m` jobs to run in each slot. `IsGreedy` adds
Graham's list-scheduling condition: a machine idles in a slot only if every job not yet started
has an unfinished predecessor ([Graham1966], §I.1).

## Main definitions

* `Cslib.Algorithms.Lean.Scheduling.Precedence.running`: the jobs occupying a time slot.
* `IsFeasible`, `IsGreedy`: feasible and greedy (list) schedules.
* `makespan`: the latest completion time (`le_makespan`, `makespan_le_iff`).

## Main results

* `IsGreedy.exists_chain`: **Graham's critical chain**. For well-founded precedences there is a
  precedence chain `c` with `m · C ≤ ∑ p + (m - 1) · ∑_{j ∈ c} p j` ([Graham1966], §II, proofs
  of the Proposition (p. 1567) and the Theorem (p. 1570)).
* `IsFeasible.sum_le_mul_makespan`, `IsFeasible.sum_chain_le_makespan`: the work and chain lower
  bounds for every feasible schedule.
* `IsGreedy.mul_makespan_le`: a greedy schedule is within `2 - 1/m` of every feasible schedule,
  `m · C_greedy ≤ (2m - 1) · C`.
* `IsGreedy.mul_makespan_le_of_le`: **Graham's anomaly bound** ([Graham1966], §II, Theorem
  (p. 1570)).
  Relaxing the precedences, shortening jobs and changing the number of machines from `m` to `m'`
  changes the makespan by at most the factor `1 + (m - 1)/m'`.
* `exists_isGreedy`: greedy schedules exist for well-founded precedences and positive processing
  times, built slot by slot.

## Implementation notes

Time is discrete (`ℕ`), so processing times are natural numbers. Graham's bounds are
scale-invariant, so this covers rational processing times after clearing denominators. Real-valued
processing times are not modelled.

`IsFeasible` bounds the number of jobs running in each slot instead of assigning jobs to machines.
For non-preemptive schedules the two are equivalent: the jobs are intervals, interval graphs are
perfect, so if at most `m` intervals overlap at every point they can be coloured with `m` machines.

Graham's model fixes a priority list. `IsGreedy` keeps only the consequence used by the bounds,
that no machine idles while a job is ready, so the theorems apply to every list schedule and to
every other greedy rule.

## References

* [Graham1966] R. L. Graham, *Bounds for certain multiprocessing anomalies*, 1966.
* [CLRS2009] Thomas H. Cormen, Charles E. Leiserson, Ronald L. Rivest, and Clifford Stein,
  *Introduction to Algorithms* (3rd ed.), Section 27.1, 2009.
-/

public section

namespace Cslib.Algorithms.Lean.Scheduling.Precedence

open Finset

variable {J : Type*} [Fintype J]

/-- The jobs occupying the time slot `[t, t + 1)`: job `j`, started at `s j` with processing
time `p j`, occupies the slots `s j ≤ t < s j + p j`. -/
def running (p s : J → ℕ) (t : ℕ) : Finset J := univ.filter fun j => s j ≤ t ∧ t < s j + p j

theorem mem_running {p s : J → ℕ} {t : ℕ} {j : J} :
    j ∈ running p s t ↔ s j ≤ t ∧ t < s j + p j := by
  simp [running]

/-- A non-preemptive schedule on `m` identical machines in integer time: job `j` runs without
interruption in the slots `s j, …, s j + p j - 1`, after all its predecessors have finished, and
at most `m` jobs run in any slot. -/
structure IsFeasible (m : ℕ) (prec : J → J → Prop) (p s : J → ℕ) : Prop where
  prec_le : ∀ i j, prec i j → s i + p i ≤ s j
  card_running_le : ∀ t, #(running p s t) ≤ m

/-- A greedy (list) schedule: a machine is left idle only when no job is ready. If fewer than `m`
jobs run in slot `t`, every job not yet started has a predecessor that is unfinished at `t`. -/
structure IsGreedy (m : ℕ) (prec : J → J → Prop) (p s : J → ℕ) : Prop
    extends IsFeasible m prec p s where
  ready_started : ∀ t j, #(running p s t) < m → t < s j → ∃ i, prec i j ∧ t < s i + p i

/-- The makespan: the latest completion time. -/
def makespan (p s : J → ℕ) : ℕ := univ.sup fun j => s j + p j

theorem le_makespan (p s : J → ℕ) (j : J) : s j + p j ≤ makespan p s :=
  le_sup (f := fun j => s j + p j) (mem_univ j)

theorem makespan_le_iff {p s : J → ℕ} {T : ℕ} : makespan p s ≤ T ↔ ∀ j, s j + p j ≤ T := by
  unfold makespan
  simp [Finset.sup_le_iff]

/-- Summing the number of running jobs over the slots before the makespan counts each job's
processing time once. -/
theorem sum_card_running (p s : J → ℕ) :
    ∑ t ∈ range (makespan p s), #(running p s t) = ∑ j, p j := by
  simp only [running, card_filter]
  rw [sum_comm]
  refine sum_congr rfl fun j _ => ?_
  rw [← card_filter]
  have hj := le_makespan p s j
  rw [show (range (makespan p s)).filter (fun t => s j ≤ t ∧ t < s j + p j) =
      Ico (s j) (s j + p j) by
    ext t
    simp only [mem_filter, mem_range, mem_Ico]
    omega]
  rw [Nat.card_Ico]
  omega

omit [Fintype J] in
/-- A set of slots each covered by a job of a list `c` has at most `∑ j ∈ c, p j` elements. -/
private theorem card_le_sum_of_covered (p s : J → ℕ) (c : List J) (T : Finset ℕ)
    (hT : ∀ t ∈ T, ∃ j ∈ c, (s j ≤ t ∧ t < s j + p j)) : #T ≤ (c.map p).sum := by
  induction c generalizing T with
  | nil =>
    have : T = ∅ := eq_empty_iff_forall_notMem.mpr fun t ht => by simpa using hT t ht
    simp [this]
  | cons j c ih =>
    rw [List.map_cons, List.sum_cons,
      ← card_filter_add_card_filter_not (fun t => s j ≤ t ∧ t < s j + p j)]
    refine Nat.add_le_add ?_ (ih _ fun t ht => ?_)
    · calc #(T.filter fun t => (s j ≤ t ∧ t < s j + p j)) ≤ #(Ico (s j) (s j + p j)) := by
            refine card_le_card fun t ht => ?_
            simp only [mem_filter] at ht
            simpa using ht.2
        _ = p j := by simp
    · rw [mem_filter] at ht
      obtain ⟨i, hi, hrun⟩ := hT t ht.1
      rcases List.mem_cons.mp hi with rfl | hi
      · exact absurd hrun ht.2
      · exact ⟨i, hi, hrun⟩

/-- Graham's chain construction ([Graham1966], §II, proof of the Proposition): for a greedy schedule
and well-founded precedences, every job `j` heads a chain `j = c₀, c₁, …` with `cₖ₊₁ ≺ cₖ` that
covers every slot before `j` finishes in which fewer than `m` jobs run. -/
private theorem exists_chain_covering {m : ℕ} {prec : J → J → Prop} {p s : J → ℕ}
    (hg : IsGreedy m prec p s) (hwf : WellFounded prec) (j : J) :
    ∃ c : List J, c.head? = some j ∧ c.IsChain (flip prec) ∧
      ∀ t < s j + p j, #(running p s t) < m → ∃ i ∈ c, (s i ≤ t ∧ t < s i + p i) := by
  induction j using hwf.induction with
  | _ j ih =>
  classical
  by_cases hex : ∃ t < s j, #(running p s t) < m
  · -- The latest non-busy slot before `j` starts.
    let t₀ := Nat.findGreatest (fun t => #(running p s t) < m) (s j - 1)
    obtain ⟨t, ht, htm⟩ := hex
    have ht₀m : #(running p s t₀) < m :=
      Nat.findGreatest_spec (P := fun t => #(running p s t) < m) (by omega : t ≤ s j - 1) htm
    have ht₀le : t₀ ≤ s j - 1 := Nat.findGreatest_le _
    have ht₀ : t₀ < s j := by omega
    have hmax : ∀ t', t' < s j → #(running p s t') < m → t' ≤ t₀ := fun t' ht' h' =>
      Nat.le_findGreatest (by omega) h'
    obtain ⟨i, hij, hi⟩ := hg.ready_started t₀ j ht₀m ht₀
    obtain ⟨c, hhead, hchain, hcov⟩ := ih i hij
    refine ⟨j :: c, rfl, ?_, ?_⟩
    · refine hchain.cons fun y hy => ?_
      rw [hhead, Option.mem_some_iff] at hy
      exact hy ▸ hij
    · intro t' ht' hm'
      by_cases hsj : s j ≤ t'
      · exact ⟨j, List.mem_cons_self, hsj, ht'⟩
      · push Not at hsj
        have := hmax t' hsj hm'
        obtain ⟨k, hk, hrun⟩ := hcov t' (by omega) hm'
        exact ⟨k, List.mem_cons_of_mem _ hk, hrun⟩
  · push Not at hex
    refine ⟨[j], rfl, List.isChain_singleton j,
      fun t ht hm => ⟨j, List.mem_singleton_self j, ?_, ht⟩⟩
    by_contra h
    push Not at h
    exact absurd (hex t h) (not_le.mpr hm)

/-- **Graham's critical-chain bound** ([Graham1966], §II, proofs of the Proposition and Theorem;
[CLRS2009], Theorem 27.1): for a greedy schedule on `m` machines with well-founded precedences
there is a precedence chain `c` (each job preceding the next) with
`m · C ≤ ∑ p + (m - 1) · ∑_{j ∈ c} p j`. -/
theorem IsGreedy.exists_chain {m : ℕ} {prec : J → J → Prop} {p s : J → ℕ}
    (hg : IsGreedy m prec p s) (hwf : WellFounded prec) :
    ∃ c : List J, c.IsChain prec ∧
      m * makespan p s ≤ ∑ j, p j + (m - 1) * (c.map p).sum := by
  classical
  -- A chain covering every non-busy slot before the makespan.
  obtain ⟨c, hchain, hcov⟩ : ∃ c : List J, c.IsChain (flip prec) ∧
      ∀ t < makespan p s, #(running p s t) < m → ∃ i ∈ c, (s i ≤ t ∧ t < s i + p i) := by
    by_cases hJ : (univ : Finset J).Nonempty
    · obtain ⟨j, -, hj⟩ := exists_mem_eq_sup univ hJ fun j => s j + p j
      obtain ⟨c, -, hchain, hcov⟩ := exists_chain_covering hg hwf j
      exact ⟨c, hchain, fun t ht => hcov t (by rw [makespan] at ht; omega)⟩
    · refine ⟨[], List.isChain_nil, fun t ht _ => ?_⟩
      rw [not_nonempty_iff_eq_empty] at hJ
      simp [makespan, hJ] at ht
  refine ⟨c.reverse, List.isChain_reverse.mpr hchain, ?_⟩
  rw [List.map_reverse, List.sum_reverse]
  set N := (range (makespan p s)).filter fun t => #(running p s t) < m
  have hN : #N ≤ (c.map p).sum := card_le_sum_of_covered p s c N fun t ht => by
    rw [mem_filter, mem_range] at ht
    exact hcov t ht.1 ht.2
  have hslot : ∀ t ∈ range (makespan p s),
      m ≤ #(running p s t) + (m - 1) * (if #(running p s t) < m then 1 else 0) := by
    intro t ht
    split_ifs with h
    · rw [mem_range] at ht
      obtain ⟨i, hi, hrun⟩ := hcov t ht h
      have : 0 < #(running p s t) := card_pos.mpr ⟨i, mem_running.mpr hrun⟩
      omega
    · omega
  calc m * makespan p s = ∑ _t ∈ range (makespan p s), m := by simp [mul_comm]
    _ ≤ ∑ t ∈ range (makespan p s),
          (#(running p s t) + (m - 1) * (if #(running p s t) < m then 1 else 0)) :=
        sum_le_sum hslot
    _ = ∑ j, p j + (m - 1) * #N := by
        rw [sum_add_distrib, sum_card_running, ← mul_sum, sum_boole, Nat.cast_id]
    _ ≤ ∑ j, p j + (m - 1) * (c.map p).sum := by gcongr

/-- Work bound: in a feasible schedule on `m` machines, `∑ p ≤ m · C`. -/
theorem IsFeasible.sum_le_mul_makespan {m : ℕ} {prec : J → J → Prop} {p s : J → ℕ}
    (hf : IsFeasible m prec p s) : ∑ j, p j ≤ m * makespan p s := by
  rw [← sum_card_running]
  calc ∑ t ∈ range (makespan p s), #(running p s t) ≤ ∑ _t ∈ range (makespan p s), m :=
        sum_le_sum fun t _ => hf.card_running_le t
    _ = m * makespan p s := by simp [mul_comm]

private theorem IsFeasible.head_add_sum_le {m : ℕ} {prec : J → J → Prop} {p s : J → ℕ}
    (hf : IsFeasible m prec p s) :
    ∀ (j : J) (c : List J), (j :: c).IsChain prec → s j + ((j :: c).map p).sum ≤ makespan p s
  | j, [], _ => by simpa using le_makespan p s j
  | j, k :: c, h => by
    rw [List.isChain_cons_cons] at h
    have h1 := hf.prec_le j k h.1
    have h2 := hf.head_add_sum_le k c h.2
    simp only [List.map_cons, List.sum_cons] at h2 ⊢
    omega

/-- Span bound: in a feasible schedule, the jobs of a precedence chain run one after another, so
their total processing time is at most the makespan. -/
theorem IsFeasible.sum_chain_le_makespan {m : ℕ} {prec : J → J → Prop} {p s : J → ℕ}
    (hf : IsFeasible m prec p s) {c : List J} (hc : c.IsChain prec) :
    (c.map p).sum ≤ makespan p s := by
  cases c with
  | nil => simp
  | cons j c => have := hf.head_add_sum_le j c hc; omega

/-- **Graham's bound with precedence constraints** ([Graham1966], §II, Theorem (p. 1570) with
`n = n'`; restated in §III, p. 1581): a greedy schedule is within `2 - 1/m` of every feasible
schedule, `m · C_greedy ≤ (2m - 1) · C`. -/
theorem IsGreedy.mul_makespan_le {m : ℕ} {prec : J → J → Prop} {p s s' : J → ℕ}
    (hg : IsGreedy m prec p s) (hwf : WellFounded prec) (hf : IsFeasible m prec p s') :
    m * makespan p s ≤ (2 * m - 1) * makespan p s' := by
  obtain ⟨c, hc, h⟩ := hg.exists_chain hwf
  have h1 := hf.sum_le_mul_makespan
  have h2 := hf.sum_chain_le_makespan hc
  calc m * makespan p s ≤ ∑ j, p j + (m - 1) * (c.map p).sum := h
    _ ≤ m * makespan p s' + (m - 1) * makespan p s' := by gcongr
    _ = (2 * m - 1) * makespan p s' := by
        rcases Nat.eq_zero_or_pos m with rfl | hm
        · simp
        · rw [← add_mul]; congr 1; omega

/-- **Graham's anomaly bound** ([Graham1966], §II, Theorem (p. 1570)): let `s` be a greedy
schedule on `m'` machines for well-founded precedences `prec'` and processing times `p'`, and `s'`
any feasible schedule on `m` machines for stronger precedences `prec ⊇ prec'` and longer processing
times `p ≥ p'`. Then `m' · C ≤ (m + m' - 1) · C'`, i.e. `C / C' ≤ 1 + (m - 1)/m'`. -/
theorem IsGreedy.mul_makespan_le_of_le {m m' : ℕ} {prec prec' : J → J → Prop} {p p' s s' : J → ℕ}
    (hg : IsGreedy m' prec' p' s) (hwf : WellFounded prec') (hprec : ∀ i j, prec' i j → prec i j)
    (hp : ∀ j, p' j ≤ p j) (hf : IsFeasible m prec p s') :
    m' * makespan p' s ≤ (m + m' - 1) * makespan p s' := by
  rcases Nat.eq_zero_or_pos m' with rfl | hm'
  · simp
  obtain ⟨c, hc, h⟩ := hg.exists_chain hwf
  have h1 : ∑ j, p' j ≤ m * makespan p s' :=
    (sum_le_sum fun j _ => hp j).trans hf.sum_le_mul_makespan
  have h2 : (c.map p').sum ≤ makespan p s' :=
    (List.sum_le_sum (by simpa using fun j _ => hp j)).trans
      (hf.sum_chain_le_makespan (hc.imp fun {a b} => hprec a b))
  calc m' * makespan p' s ≤ ∑ j, p' j + (m' - 1) * (c.map p').sum := h
    _ ≤ m * makespan p s' + (m' - 1) * makespan p s' := by gcongr
    _ = (m + m' - 1) * makespan p s' := by rw [← add_mul]; congr 1; omega


section Existence

variable {prec : J → J → Prop} [DecidableEq J]

/-- Invariant of the greedy construction after the slots `0, …, N - 1` are filled: the jobs in
`D` have start times before `N`, the other jobs are parked at `N`. -/
private structure GreedyInv (m : ℕ) (prec : J → J → Prop) (p : J → ℕ) (N : ℕ) (D : Finset J)
    (s : J → ℕ) : Prop where
  lt_of_mem : ∀ j ∈ D, s j < N
  eq_of_notMem : ∀ j ∉ D, s j = N
  prec_le : ∀ i j, prec i j → j ∈ D → i ∈ D ∧ s i + p i ≤ s j
  card_le : ∀ t, #(running p s t ∩ D) ≤ m
  ready : ∀ t < N, ∀ j, #(running p s t) < m → t < s j → ∃ i, prec i j ∧ t < s i + p i
  busy : ∀ t < N, D ≠ univ → (running p s t ∩ D).Nonempty

private theorem greedyInv_zero (m : ℕ) (prec : J → J → Prop) (p : J → ℕ) :
    GreedyInv m prec p 0 ∅ fun _ => 0 where
  lt_of_mem := by simp
  eq_of_notMem := by simp
  prec_le := by simp
  card_le := by simp
  ready := by simp
  busy := by simp

/-- One step of the greedy construction: fill slot `N` with as many ready jobs as there are free
machines. -/
private theorem GreedyInv.step {m : ℕ} {p : J → ℕ} {N : ℕ} {D : Finset J} {s : J → ℕ}
    (hwf : WellFounded prec) (hm : 0 < m) (hp : ∀ j, 0 < p j) (h : GreedyInv m prec p N D s) :
    ∃ D' s', GreedyInv m prec p (N + 1) D' s' := by
  classical
  set r := #(running p s N ∩ D) with hr
  set R := univ.filter fun j => j ∉ D ∧ ∀ i, prec i j → i ∈ D ∧ s i + p i ≤ N with hR
  obtain ⟨A, hAR, hA⟩ := exists_subset_card_eq (s := R) (min_le_left #R (m - r))
  set s' : J → ℕ := fun j => if j ∈ D ∨ j ∈ A then s j else N + 1 with hs'
  have hAD : ∀ j ∈ A, j ∉ D := fun j hj => (mem_filter.mp (hAR hj)).2.1
  have hAs : ∀ j ∈ A, s j = N := fun j hj => h.eq_of_notMem j (hAD j hj)
  have hs'D : ∀ j ∈ D, s' j = s j := fun j hj => by simp [s', hj]
  have hs'A : ∀ j ∈ A, s' j = N := fun j hj => by simp [s', hj, hAs j hj]
  have hs'out : ∀ j, j ∉ D → j ∉ A → s' j = N + 1 := fun j h1 h2 => by simp [s', h1, h2]
  have hrD : r ≤ m := h.card_le N
  have hrun_lt : ∀ t < N, running p s' t = running p s t := by
    intro t ht
    ext j
    simp only [mem_running]
    by_cases hj : j ∈ D
    · rw [hs'D j hj]
    · rw [h.eq_of_notMem j hj]
      by_cases hjA : j ∈ A
      · rw [hs'A j hjA]
      · rw [hs'out j hj hjA]
        omega
  have hrun_ge : ∀ t, N ≤ t → running p s' t ∩ (D ∪ A) ⊆ (running p s N ∩ D) ∪ A := by
    intro t ht j hj
    rw [mem_inter, mem_running] at hj
    rw [mem_union, mem_inter, mem_running]
    rcases mem_union.mp hj.2 with hjD | hjA
    · rw [hs'D j hjD] at hj
      have := h.lt_of_mem j hjD
      exact Or.inl ⟨⟨by omega, by omega⟩, hjD⟩
    · exact Or.inr hjA
  have hdisj : Disjoint (running p s N ∩ D) A :=
    disjoint_left.mpr fun j hj hjA => hAD j hjA (mem_inter.mp hj).2
  have hrunN : running p s' N = (running p s N ∩ D) ∪ A := by
    ext j
    constructor
    · intro hj
      have hjDA : j ∈ D ∪ A := by
        by_contra hn
        rw [mem_union, not_or] at hn
        rw [mem_running, hs'out j hn.1 hn.2] at hj
        omega
      exact hrun_ge N le_rfl (mem_inter.mpr ⟨hj, hjDA⟩)
    · intro hj
      rw [mem_running]
      rcases mem_union.mp hj with hj | hj
      · rw [mem_inter, mem_running] at hj
        rw [hs'D j hj.2]
        exact hj.1
      · rw [hs'A j hj]
        have := hp j
        omega
  have hcardN : #(running p s' N) = r + #A := by
    rw [hrunN, card_union_of_disjoint hdisj]
  -- If slot `N` is not full, every ready job was placed.
  have hAR_eq : #(running p s' N) < m → A = R := by
    intro hlt
    refine eq_of_subset_of_card_le hAR ?_
    have := min_le_right #R (m - r)
    rcases min_choice #R (m - r) with hmin | hmin <;> omega
  refine ⟨D ∪ A, s', ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro j hj
    rcases mem_union.mp hj with hj | hj
    · rw [hs'D j hj]
      have := h.lt_of_mem j hj
      omega
    · rw [hs'A j hj]
      omega
  · intro j hj
    rw [mem_union, not_or] at hj
    exact hs'out j hj.1 hj.2
  · intro i j hij hj
    rcases mem_union.mp hj with hjD | hjA
    · obtain ⟨hiD, hle⟩ := h.prec_le i j hij hjD
      refine ⟨mem_union_left _ hiD, ?_⟩
      rw [hs'D i hiD, hs'D j hjD]
      exact hle
    · obtain ⟨hiD, hle⟩ := (mem_filter.mp (hAR hjA)).2.2 i hij
      refine ⟨mem_union_left _ hiD, ?_⟩
      rw [hs'D i hiD, hs'A j hjA]
      exact hle
  · intro t
    by_cases ht : t < N
    · have hsub : running p s' t ∩ (D ∪ A) ⊆ running p s t ∩ D := by
        intro j hj
        rw [mem_inter, hrun_lt t ht] at hj
        rcases mem_union.mp hj.2 with hjD | hjA
        · exact mem_inter.mpr ⟨hj.1, hjD⟩
        · rw [mem_running, hAs j hjA] at hj
          omega
      exact (card_le_card hsub).trans (h.card_le t)
    · push Not at ht
      calc #(running p s' t ∩ (D ∪ A)) ≤ #((running p s N ∩ D) ∪ A) :=
            card_le_card (hrun_ge t ht)
        _ = r + #A := card_union_of_disjoint hdisj
        _ ≤ m := by
            have := min_le_right #R (m - r)
            omega
  · intro t ht j hm htj
    rcases Nat.lt_succ_iff_lt_or_eq.mp ht with ht | rfl
    · rw [hrun_lt t ht] at hm
      have htj' : t < s j := by
        by_cases hj : j ∈ D
        · rwa [← hs'D j hj]
        · rw [h.eq_of_notMem j hj]
          exact ht
      obtain ⟨i, hij, hi⟩ := h.ready t ht j hm htj'
      refine ⟨i, hij, ?_⟩
      by_cases hiD : i ∈ D
      · rwa [hs'D i hiD]
      · have h1 := h.eq_of_notMem i hiD
        by_cases hiA : i ∈ A
        · rw [hs'A i hiA]
          omega
        · rw [hs'out i hiD hiA]
          omega
    · have hjD : j ∉ D := fun hjD => by
        rw [hs'D j hjD] at htj
        have := h.lt_of_mem j hjD
        omega
      have hjA : j ∉ A := fun hjA => by
        rw [hs'A j hjA] at htj
        omega
      have hjR : j ∉ R := by rwa [← hAR_eq hm]
      rw [hR, mem_filter] at hjR
      simp only [mem_univ, true_and, not_and, not_forall] at hjR
      obtain ⟨i, hij, hi⟩ := hjR hjD
      refine ⟨i, hij, ?_⟩
      by_cases hiD : i ∈ D
      · rw [hs'D i hiD]
        exact not_le.mp (hi hiD)
      · have := hp i
        by_cases hiA : i ∈ A
        · rw [hs'A i hiA]
          omega
        · rw [hs'out i hiD hiA]
          omega
  · intro t ht hDA
    have hD : D ≠ univ := fun hD =>
      hDA (eq_univ_iff_forall.mpr fun x => mem_union_left _ (hD ▸ mem_univ x))
    rcases Nat.lt_succ_iff_lt_or_eq.mp ht with ht | ht
    · obtain ⟨k, hk⟩ := h.busy t ht hD
      refine ⟨k, ?_⟩
      rw [mem_inter, hrun_lt t ht]
      exact ⟨(mem_inter.mp hk).1, mem_union_left _ (mem_inter.mp hk).2⟩
    · rw [ht]
      suffices hne : (running p s N ∩ D ∪ A).Nonempty by
        obtain ⟨k, hk⟩ := hne
        refine ⟨k, mem_inter.mpr ⟨hrunN ▸ hk, ?_⟩⟩
        rcases mem_union.mp hk with hk | hk
        · exact mem_union_left _ (mem_inter.mp hk).2
        · exact mem_union_right _ hk
      by_cases hAne : A.Nonempty
      · obtain ⟨a, ha⟩ := hAne
        exact ⟨a, mem_union_right _ ha⟩
      · rw [not_nonempty_iff_eq_empty] at hAne
        obtain ⟨k, hkD, hkmin⟩ := hwf.has_min {j | j ∉ D} (by
          by_contra hcon
          exact hD (eq_univ_iff_forall.mpr fun x => by
            by_contra hx
            exact hcon ⟨x, hx⟩))
        have hpred : ∀ i, prec i k → i ∈ D := fun i hik => by
          by_contra hiD
          exact hkmin i hiD hik
        by_cases hready : ∀ i, prec i k → s i + p i ≤ N
        · have hkR : k ∈ R := by
            rw [hR, mem_filter]
            exact ⟨mem_univ _, hkD, fun i hik => ⟨hpred i hik, hready i hik⟩⟩
          have hR0 : 0 < #R := card_pos.mpr ⟨k, hkR⟩
          rw [hAne, card_empty] at hA
          have hmr : m ≤ r := by
            rcases min_choice #R (m - r) with hmin | hmin <;> omega
          obtain ⟨j, hj⟩ := card_pos.mp (show 0 < r by omega)
          exact ⟨j, mem_union_left _ hj⟩
        · push Not at hready
          obtain ⟨i, hik, hi⟩ := hready
          have hiD := hpred i hik
          have := h.lt_of_mem i hiD
          exact ⟨i, mem_union_left _ (mem_inter.mpr ⟨mem_running.mpr ⟨by omega, hi⟩, hiD⟩)⟩

omit [DecidableEq J] in
/-- Counting the running jobs over any `N` slots counts each job at most `p j` times. -/
private theorem sum_card_running_range_le (p s : J → ℕ) (N : ℕ) :
    ∑ t ∈ range N, #(running p s t) ≤ ∑ j, p j := by
  classical
  simp only [running, card_filter]
  rw [sum_comm]
  refine sum_le_sum fun j _ => ?_
  rw [← card_filter]
  calc #((range N).filter fun t => s j ≤ t ∧ t < s j + p j) ≤ #(Ico (s j) (s j + p j)) :=
        card_le_card fun t ht => by
          rw [mem_filter] at ht
          exact mem_Ico.mpr ht.2
    _ = p j := by simp

private theorem exists_greedyInv {m : ℕ} {p : J → ℕ} (hwf : WellFounded prec)
    (hm : 0 < m) (hp : ∀ j, 0 < p j) (N : ℕ) : ∃ D s, GreedyInv m prec p N D s := by
  induction N with
  | zero => exact ⟨∅, _, greedyInv_zero m prec p⟩
  | succ N ih =>
    obtain ⟨D, s, h⟩ := ih
    exact h.step hwf hm hp

omit [DecidableEq J] in
/-- **Greedy schedules exist** (list scheduling, [Graham1966], §I.1): for well-founded precedences
and positive processing times, a greedy schedule exists on any `m ≥ 1` machines. -/
theorem exists_isGreedy (m : ℕ) (hm : 0 < m) (prec : J → J → Prop) (hwf : WellFounded prec)
    (p : J → ℕ) (hp : ∀ j, 0 < p j) : ∃ s, IsGreedy m prec p s := by
  classical
  obtain ⟨D, s, h⟩ := exists_greedyInv (prec := prec) hwf hm hp (∑ j, p j + 1)
  have hD : D = univ := by
    by_contra hD
    have hcov : ∀ t ∈ range (∑ j, p j + 1), 1 ≤ #(running p s t) := fun t ht => by
      obtain ⟨k, hk⟩ := h.busy t (mem_range.mp ht) hD
      exact card_pos.mpr ⟨k, (mem_inter.mp hk).1⟩
    have := (card_nsmul_le_sum _ _ 1 hcov).trans (sum_card_running_range_le p s _)
    simp at this
  subst hD
  refine ⟨s, ⟨⟨fun i j hij => (h.prec_le i j hij (mem_univ j)).2, fun t => ?_⟩, ?_⟩⟩
  · simpa using h.card_le t
  · intro t j hlt htj
    exact h.ready t (htj.trans (h.lt_of_mem j (mem_univ j))) j hlt htj

end Existence

end Cslib.Algorithms.Lean.Scheduling.Precedence
