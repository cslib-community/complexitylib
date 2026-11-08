/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Algorithms.Lean.Scheduling.Precedence
public import Mathlib.Order.Lattice.Nat
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List

/-!
# Work, Span and Brent's Theorem

The span `span prec p` of a job system is the largest total processing time of a precedence chain
(the critical-path length). For unit processing times, `Fintype.card J` is the work `W` (the
number of nodes of the computation DAG) and `span prec (fun _ => 1)` is its depth `D`. This module
proves the work and span laws, the greedy-scheduler bound and Brent's scheduling lemma.

## Main definitions

* `Cslib.Algorithms.Lean.Scheduling.Precedence.span`: the critical-path length.

## Main results

* `exists_chain_sum_eq_span`, `sum_chain_le_span`: the span is attained by a chain and bounds all
  chains.
* `IsFeasible.span_le_makespan`, together with `IsFeasible.sum_le_mul_makespan`: the span law
  `D ≤ T` and the work law `W ≤ m · T`, so every schedule satisfies `T ≥ max(W/m, D)`.
* `IsGreedy.mul_makespan_le_sum_add_span`: the **greedy-scheduler bound**
  `m · T ≤ ∑ p + (m - 1) · span` ([CLRS2009], Theorem 27.1, in Graham's sharper form).
* `IsGreedy.mul_makespan_le_card_add_span`, `IsGreedy.makespan_le_card_div_add_span`:
  **Brent's bound** for unit-time DAGs, `m · T ≤ W + (m - 1) · D`, so `T ≤ (W - D)/m + D` and
  `T ≤ ⌊W/m⌋ + D` ([Brent1974], Lemma 2).
* `exists_isFeasible_mul_makespan_le`: **Brent's scheduling lemma** as an existence statement:
  every unit-time DAG has an `m`-processor schedule with `m · T ≤ W + (m - 1) · D`.

## References

* [Brent1974] Richard P. Brent, *The parallel evaluation of general arithmetic expressions*,
  1974.
* [CLRS2009] Thomas H. Cormen, Charles E. Leiserson, Ronald L. Rivest, and Clifford Stein,
  *Introduction to Algorithms* (3rd ed.), Section 27.1, 2009.
-/

public section

namespace Cslib.Algorithms.Lean.Scheduling.Precedence

open Finset

variable {J : Type*} [Fintype J]

section Span

variable {prec : J → J → Prop}

omit [Fintype J] in
/-- A precedence chain of a well-founded relation has no repeated job. -/
theorem nodup_of_isChain (hwf : WellFounded prec) {c : List J} (hc : c.IsChain prec) :
    c.Nodup := by
  have hirr : Std.Irrefl (Relation.TransGen prec) := by
    have := hwf.transGen
    infer_instance
  have hpw : c.Pairwise (Relation.TransGen prec) :=
    List.isChain_iff_pairwise.mp (hc.imp fun {_ _} h => Relation.TransGen.single h)
  exact hpw.nodup

/-- The weighted length of every chain is at most the total processing time. -/
theorem sum_chain_le_sum (hwf : WellFounded prec) (p : J → ℕ) {c : List J}
    (hc : c.IsChain prec) : (c.map p).sum ≤ ∑ j, p j := by
  classical
  rw [← List.sum_toFinset p (nodup_of_isChain hwf hc)]
  exact sum_le_sum_of_subset (subset_univ _)

variable (prec) in
/-- The span (critical-path length) of a job system: the largest total processing time of a
precedence chain. For unit processing times this is the number of jobs on a longest chain. -/
noncomputable def span (p : J → ℕ) : ℕ :=
  sSup {w | ∃ c : List J, c.IsChain prec ∧ (c.map p).sum = w}

omit [Fintype J] in
private theorem bddAbove_chainSums [Finite J] (hwf : WellFounded prec) (p : J → ℕ) :
    BddAbove {w | ∃ c : List J, c.IsChain prec ∧ (c.map p).sum = w} := by
  have := Fintype.ofFinite J
  exact ⟨∑ j, p j, fun _ ⟨_, hc, hw⟩ => hw ▸ sum_chain_le_sum hwf p hc⟩

omit [Fintype J] in
/-- Every precedence chain has weighted length at most the span. -/
theorem sum_chain_le_span [Finite J] (hwf : WellFounded prec) (p : J → ℕ) {c : List J}
    (hc : c.IsChain prec) : (c.map p).sum ≤ span prec p :=
  le_csSup (bddAbove_chainSums hwf p) ⟨c, hc, rfl⟩

omit [Fintype J] in
/-- The span is attained by a precedence chain (a critical path). -/
theorem exists_chain_sum_eq_span [Finite J] (hwf : WellFounded prec) (p : J → ℕ) :
    ∃ c : List J, c.IsChain prec ∧ (c.map p).sum = span prec p :=
  Nat.sSup_mem (s := {w | ∃ c : List J, c.IsChain prec ∧ (c.map p).sum = w})
    ⟨0, [], List.isChain_nil, rfl⟩ (bddAbove_chainSums hwf p)

/-- Span law: every feasible schedule takes at least the span. -/
theorem IsFeasible.span_le_makespan {m : ℕ} {p s : J → ℕ} (hf : IsFeasible m prec p s) :
    span prec p ≤ makespan p s :=
  csSup_le ⟨0, [], List.isChain_nil, rfl⟩ fun _ ⟨_, hc, hw⟩ =>
    hw ▸ hf.sum_chain_le_makespan hc

/-- **Greedy-scheduler bound** ([CLRS2009], Theorem 27.1, with Graham's refinement):
`m · C ≤ ∑ p + (m - 1) · span`. -/
theorem IsGreedy.mul_makespan_le_sum_add_span {m : ℕ} {p s : J → ℕ}
    (hg : IsGreedy m prec p s) (hwf : WellFounded prec) :
    m * makespan p s ≤ ∑ j, p j + (m - 1) * span prec p := by
  obtain ⟨c, hc, h⟩ := hg.exists_chain hwf
  exact h.trans (by gcongr; exact sum_chain_le_span hwf p hc)

end Span

section Brent

variable {prec : J → J → Prop}

/-- **Brent's bound for a greedy schedule** of a unit-time DAG with `W = |J|` nodes and span `D`
(the number of nodes on a longest chain): `m · T ≤ W + (m - 1) · D`, i.e.
`T ≤ (W - D)/m + D` ([Brent1974], Lemma 2; [CLRS2009], Theorem 27.1). -/
theorem IsGreedy.mul_makespan_le_card_add_span {m : ℕ} {s : J → ℕ}
    (hg : IsGreedy m prec (fun _ => 1) s) (hwf : WellFounded prec) :
    m * makespan (fun _ => 1) s ≤ Fintype.card J + (m - 1) * span prec (fun _ => 1) := by
  have h := hg.mul_makespan_le_sum_add_span hwf
  rw [sum_const, card_univ, nsmul_eq_mul, mul_one, Nat.cast_id] at h
  exact h

/-- Brent's bound in the form `T ≤ ⌊W/m⌋ + D`. -/
theorem IsGreedy.makespan_le_card_div_add_span {m : ℕ} {s : J → ℕ}
    (hg : IsGreedy m prec (fun _ => 1) s) (hwf : WellFounded prec) (hm : 0 < m) :
    makespan (fun _ => 1) s ≤ Fintype.card J / m + span prec (fun _ => 1) := by
  have h := hg.mul_makespan_le_card_add_span hwf
  rw [← Nat.add_mul_div_right _ _ hm]
  refine (Nat.le_div_iff_mul_le hm).mpr ?_
  calc makespan (fun _ => 1) s * m = m * makespan (fun _ => 1) s := mul_comm _ _
    _ ≤ Fintype.card J + (m - 1) * span prec (fun _ => 1) := h
    _ ≤ Fintype.card J + span prec (fun _ => 1) * m := by
        rw [mul_comm (m - 1)]
        gcongr
        exact Nat.sub_le m 1

/-- A feasible schedule with positive processing times forces the precedences to be
well-founded. -/
theorem IsFeasible.wellFounded {m : ℕ} {p s : J → ℕ} (hf : IsFeasible m prec p s)
    (hp : ∀ j, 0 < p j) : WellFounded prec :=
  Subrelation.wf (fun {i j} h => (by have := hf.prec_le i j h; have := hp i; omega :
    s i < s j)) (InvImage.wf s wellFounded_lt)

end Brent

section BrentExistence

variable {prec : J → J → Prop}

/-- **Brent's scheduling lemma** ([Brent1974], Lemma 2), in the unit-time DAG form: every finite
DAG of `W = |J|` unit jobs with span `D = span prec (fun _ => 1)` (the number of jobs on a longest
chain, i.e. the time needed with unboundedly many processors) has a feasible schedule on `m ≥ 1`
processors with `m · T ≤ W + (m - 1) · D`. -/
theorem exists_isFeasible_mul_makespan_le (m : ℕ) (hm : 0 < m) (hwf : WellFounded prec) :
    ∃ s, IsFeasible m prec (fun _ => 1) s ∧
      m * makespan (fun _ => 1) s ≤ Fintype.card J + (m - 1) * span prec (fun _ => 1) := by
  obtain ⟨s, hs⟩ := exists_isGreedy m hm prec hwf (fun _ => 1) fun _ => Nat.one_pos
  exact ⟨s, hs.toIsFeasible, hs.mul_makespan_le_card_add_span hwf⟩

end BrentExistence

end Cslib.Algorithms.Lean.Scheduling.Precedence
