/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Algorithms.Lean.StableMatching.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Gale–Shapley deferred acceptance

This module implements proposer-proposing deferred acceptance [GaleShapley1962] as a total,
computable Lean function on `Instance n`, and proves that it terminates within the classical
proposal bound, that its output is stable, and that it is proposer-optimal.

We use the iterative formulation in which one rejection happens at a time; McVitie and Wilson
[McVitieWilson1971] showed that the outcome does not depend on the order of rejections. A state
records, for each proposer `p`, how many receivers have turned `p`
down; `p` currently proposes to its next choice. While some receiver receives proposals from two
proposers, it turns down the one it likes less, which moves on to its next choice. The step
function always turns down the first outranked proposer in index order, so `deferredAcceptance`
is a definite function that `decide` evaluates on concrete instances. The proofs use only
`step_cases` and the invariant `Inv`, so they adapt to any rejection order; order independence is
not stated as a theorem here.

## Main definitions

* `Instance.step`, `Instance.run`: one rejection step, and the state after `k` steps.
* `Instance.finalState`: the state after `(n - 1)^2` steps, which is fixed.
* `Instance.deferredAcceptance`: the proposer-proposing deferred-acceptance matching.
* `Instance.proposals`: the number of proposals made, `∑ p, (finalState p + 1)`.

## Main results

* `Instance.step_run_fixed`, `Instance.run_eq_finalState`: the run stops after at most
  `(n - 1)^2` rejections.
* `Instance.proposals_le`: at most `n^2 - n + 1` proposals are made (see [GusfieldIrving1989]);
  `Instance.proposals_eq` expresses the count through the final partners only.
* `Instance.isStable_deferredAcceptance`, `Instance.exists_isStable`: the output is a (perfect)
  stable matching; hence a stable matching always exists ([GaleShapley1962], Theorem 1).
* `Instance.propRank_deferredAcceptance_le`, `Instance.isProposerOptimal_deferredAcceptance`:
  every proposer weakly prefers its deferred-acceptance partner to its partner in any stable
  matching ([GaleShapley1962], Theorem 2), and receivers are correspondingly worst off
  ([McVitieWilson1971]); `Instance.isProposerOptimal_iff` characterizes the output.
* `Instance.receiverDeferredAcceptance`: receiver-proposing deferred acceptance, which is
  receiver-optimal and proposer-pessimal.

## Cost model

`proposals` counts proposals, the standard cost measure for deferred acceptance. This module does
not charge the cost of finding an outranked proposer or of the surrounding bookkeeping on any
machine model.

## References

* [GaleShapley1962]
* [McVitieWilson1971]
* [GusfieldIrving1989]
-/

public section

namespace Cslib.Algorithms.Lean.StableMatching

namespace Instance

variable {n : ℕ} (I : Instance n)

/-- A deferred-acceptance state: `s p` is the number of receivers that have turned proposer `p`
down so far. Proposer `p` currently proposes to its choice of rank `s p`. -/
abbrev State (n : ℕ) := Fin n → ℕ

/-- The receiver proposer `p` currently proposes to: its choice of rank `s p` (clamped to the
last rank, which reachable states never exceed). -/
@[expose] def target (s : State n) (p : Fin n) : Fin n :=
  I.propPref p ⟨min (s p) (n - 1), by have := p.isLt; omega⟩

/-- Proposer `p` is outranked when its current receiver also receives a proposal from someone it
strictly prefers to `p`. -/
@[expose] def Outranked (s : State n) (p : Fin n) : Prop :=
  ∃ q, I.target s q = I.target s p ∧ I.RecvPrefers (I.target s p) q p

instance (s : State n) (p : Fin n) : Decidable (I.Outranked s p) :=
  inferInstanceAs (Decidable (∃ _, _))

/-- One step of deferred acceptance: the first outranked proposer is turned down and moves on to
its next choice. A state with no outranked proposer is fixed. -/
@[expose] def step (s : State n) : State n :=
  match (List.finRange n).find? (fun p => decide (I.Outranked s p)) with
  | some p => Function.update s p (s p + 1)
  | none => s

/-- The state after `k` steps, starting with every proposer at its first choice. -/
@[expose] def run (k : ℕ) : State n := (I.step)^[k] (fun _ => 0)

/-- A step either fixes a state with no outranked proposer or turns down one outranked proposer. -/
theorem step_cases (s : State n) :
    (I.step s = s ∧ ∀ p, ¬ I.Outranked s p) ∨
      ∃ p, I.Outranked s p ∧ I.step s = Function.update s p (s p + 1) := by
  unfold step
  split
  · rename_i p hp
    right
    exact ⟨p, by simpa using List.find?_some hp, rfl⟩
  · rename_i hp
    left
    refine ⟨rfl, fun p hd => ?_⟩
    have := List.find?_eq_none.1 hp p (List.mem_finRange p)
    simp_all

/-- Within the list, `target` is the choice of rank `s p`. -/
theorem target_of_lt {s : State n} {p : Fin n} (h : s p < n) :
    I.target s p = I.propPref p ⟨s p, h⟩ := by
  unfold target
  congr 2
  omega

/-- The deferred-acceptance invariant: every proposer is within its list; whenever proposer `p`
has been turned down by its choice of rank `k`, that receiver currently receives a proposal from
someone it prefers to `p`; and at most one proposer has reached its last choice. -/
structure Inv (s : State n) : Prop where
  /-- Every proposer is within its list. -/
  lt : ∀ p, s p < n
  /-- A receiver that turned `p` down currently holds a proposal it prefers to `p`. -/
  rejected : ∀ p (k : Fin n), k.val < s p →
    ∃ q, I.target s q = I.propPref p k ∧ I.RecvPrefers (I.propPref p k) q p
  /-- At most one proposer has reached its last choice. -/
  last_unique : ∀ p q, s p + 1 = n → s q + 1 = n → p = q

/-- The initial state satisfies the invariant. -/
theorem inv_init : I.Inv (fun _ => 0) where
  lt p := by have := p.isLt; omega
  rejected p k hk := absurd hk (Nat.not_lt_zero _)
  last_unique p q hp hq := by
    have h1 := p.isLt
    have h2 := q.isLt
    ext
    omega

private theorem target_update_ne (s : State n) {p x : Fin n} (h : x ≠ p) (v : ℕ) :
    I.target (Function.update s p v) x = I.target s x := by
  simp only [target, Function.update_of_ne h]

/-- After a step, each receiver still gets a proposal from someone at least as good. -/
private theorem held_step {s : State n} {p : Fin n} (hp : I.Outranked s p)
    {q x r : Fin n} (hq : I.target s q = r) (hx : I.RecvPrefers r q x) :
    ∃ q', I.target (Function.update s p (s p + 1)) q' = r ∧ I.RecvPrefers r q' x := by
  by_cases hqp : q = p
  · subst hqp
    obtain ⟨y, hy, hyp⟩ := hp
    have hyq : y ≠ q := fun h => lt_irrefl _ (h ▸ hyp)
    refine ⟨y, ?_, ?_⟩
    · rw [I.target_update_ne s hyq, hy, hq]
    · rw [← hq]
      exact lt_trans hyp (hq ▸ hx)
  · exact ⟨q, by rw [I.target_update_ne s hqp, hq], hx⟩

private theorem ne_of_outranks {s : State n} {p q : Fin n}
    (h : I.RecvPrefers (I.target s p) q p) : q ≠ p := by
  rintro rfl
  exact lt_irrefl _ h

/-- Once some proposer has reached its last choice, every receiver is proposed to. -/
private theorem target_surjective_of_last {s : State n} (hs : I.Inv s) {p : Fin n}
    (hp : s p + 1 = n) : Function.Surjective (I.target s) := by
  intro r
  set k := (I.propPref p).symm r with hk
  have hr : I.propPref p k = r := by rw [hk, Equiv.apply_symm_apply]
  rcases Nat.lt_or_ge k.val (s p) with h | h
  · obtain ⟨q, hq, -⟩ := hs.rejected p k h
    exact ⟨q, hq.trans hr⟩
  · refine ⟨p, ?_⟩
    rw [I.target_of_lt (hs.lt p), ← hr]
    congr 1
    ext
    have := k.isLt
    simp only
    omega

private theorem not_outranked_of_last {s : State n} (hs : I.Inv s) {p : Fin n}
    (hp : s p + 1 = n) (x : Fin n) : ¬ I.Outranked s x := by
  rintro ⟨q, hq, hqx⟩
  have hinj := Finite.injective_iff_surjective.2 (I.target_surjective_of_last hs hp)
  exact I.ne_of_outranks hqx (hinj hq)

private theorem inv_update_lt {s : State n} (hs : I.Inv s) {p : Fin n} (hp : I.Outranked s p)
    (x : Fin n) : Function.update s p (s p + 1) x < n := by
  by_cases hxp : x = p
  · subst hxp
    rw [Function.update_self]
    have h1 := hs.lt x
    have h2 : s x + 1 ≠ n := fun h => I.not_outranked_of_last hs h x hp
    omega
  · rw [Function.update_of_ne hxp]
    exact hs.lt x

private theorem inv_update {s : State n} (hs : I.Inv s) {p : Fin n} (hp : I.Outranked s p) :
    I.Inv (Function.update s p (s p + 1)) where
  lt := I.inv_update_lt hs hp
  rejected x k hk := by
    by_cases hxp : x = p
    · subst hxp
      rw [Function.update_self] at hk
      rcases Nat.lt_or_ge k.val (s x) with h | h
      · obtain ⟨q, hq, hqx⟩ := hs.rejected x k h
        exact I.held_step hp hq hqx
      · have hkx : k = ⟨s x, hs.lt x⟩ := by ext; simp only; omega
        have ht : I.target s x = I.propPref x k := by rw [I.target_of_lt (hs.lt x), hkx]
        obtain ⟨y, hy, hyx⟩ := hp
        rw [← ht]
        exact I.held_step ⟨y, hy, hyx⟩ hy hyx
    · rw [Function.update_of_ne hxp] at hk
      obtain ⟨q, hq, hqx⟩ := hs.rejected x k hk
      exact I.held_step hp hq hqx
  last_unique a b ha hb := by
    have key : ∀ x, Function.update s p (s p + 1) x + 1 = n → x = p := by
      intro x hx
      by_contra hxp
      rw [Function.update_of_ne hxp] at hx
      exact I.not_outranked_of_last hs hx p hp
    rw [key a ha, key b hb]

/-- Steps preserve the invariant. -/
theorem inv_step {s : State n} (hs : I.Inv s) : I.Inv (I.step s) := by
  rcases I.step_cases s with ⟨h, -⟩ | ⟨p, hp, h⟩
  · rw [h]; exact hs
  · rw [h]; exact I.inv_update hs hp

/-- Every state of the run satisfies the invariant. -/
theorem inv_run (k : ℕ) : I.Inv (I.run k) := by
  induction k with
  | zero => exact I.inv_init
  | succ k ih =>
    rw [run, Function.iterate_succ_apply']
    exact I.inv_step ih

private theorem sq_aux (n : ℕ) :
    (n - 1) * (n - 2) + (n - 1) = (n - 1) ^ 2 ∧ n * (n - 2) ≤ (n - 1) ^ 2 := by
  rcases n with _ | _ | m
  · simp
  · simp
  · have h1 : m + 1 + 1 - 1 = m + 1 := rfl
    have h2 : m + 1 + 1 - 2 = m := rfl
    rw [h1, h2]
    constructor
    · ring
    · nlinarith

/-- The total number of rejections in an invariant state is at most `(n - 1)^2`. -/
theorem sum_le {s : State n} (hs : I.Inv s) : ∑ p, s p ≤ (n - 1) ^ 2 := by
  by_cases hlast : ∃ p, s p + 1 = n
  · obtain ⟨p, hp⟩ := hlast
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ p)]
    have hrest : ∑ x ∈ Finset.univ.erase p, s x ≤ (Finset.univ.erase p).card * (n - 2) := by
      rw [← smul_eq_mul]
      refine Finset.sum_le_card_nsmul _ _ _ fun x hx => ?_
      have hxp := Finset.ne_of_mem_erase hx
      have h1 := hs.lt x
      have h2 : s x + 1 ≠ n := fun h => hxp (hs.last_unique x p h hp)
      omega
    rw [Finset.card_erase_of_mem (Finset.mem_univ p), Finset.card_univ, Fintype.card_fin] at hrest
    have := (sq_aux n).1
    have hsp : s p = n - 1 := by omega
    rw [hsp]
    linarith
  · push Not at hlast
    have h : ∑ x, s x ≤ (Finset.univ : Finset (Fin n)).card * (n - 2) := by
      rw [← smul_eq_mul]
      refine Finset.sum_le_card_nsmul _ _ _ fun x _ => ?_
      have h1 := hs.lt x
      have h2 := hlast x
      omega
    rw [Finset.card_univ, Fintype.card_fin] at h
    exact h.trans (sq_aux n).2


private theorem sum_update_succ (s : State n) (p : Fin n) :
    ∑ x, Function.update s p (s p + 1) x = ∑ x, s x + 1 := by
  rw [Finset.sum_update_of_mem (Finset.mem_univ p),
    Finset.sum_eq_add_sum_sdiff_singleton_of_mem (Finset.mem_univ p) s]
  omega

/-- Either the run has stopped by step `k`, or it has made exactly `k` rejections. -/
private theorem run_fixed_or_sum (k : ℕ) :
    (∃ j ≤ k, I.step (I.run j) = I.run j) ∨ ∑ x, I.run k x = k := by
  induction k with
  | zero => exact Or.inr (by simp [run])
  | succ k ih =>
    rcases ih with ⟨j, hj, hfix⟩ | hsum
    · exact Or.inl ⟨j, by omega, hfix⟩
    · rcases I.step_cases (I.run k) with ⟨h, -⟩ | ⟨p, -, h⟩
      · exact Or.inl ⟨k, by omega, h⟩
      · right
        rw [run, Function.iterate_succ_apply', ← run, h, sum_update_succ, hsum]

/-- Once the run reaches a fixed state, it stays there. -/
theorem run_fixed_of_le {j k : ℕ} (hjk : j ≤ k) (h : I.step (I.run j) = I.run j) :
    I.run k = I.run j := by
  induction k, hjk using Nat.le_induction with
  | base => rfl
  | succ k _ ih => rw [run, Function.iterate_succ_apply', ← run, ih, h]

/-- Deferred acceptance stops after at most `(n - 1)^2` rejections. -/
theorem step_run_fixed : I.step (I.run ((n - 1) ^ 2)) = I.run ((n - 1) ^ 2) := by
  rcases I.run_fixed_or_sum ((n - 1) ^ 2 + 1) with ⟨j, hj, hfix⟩ | hsum
  · rcases Nat.lt_or_ge j ((n - 1) ^ 2 + 1) with hlt | hge
    · rw [I.run_fixed_of_le (by omega : j ≤ (n - 1) ^ 2) hfix, hfix]
    · have hj' : j = (n - 1) ^ 2 + 1 := by omega
      subst hj'
      have h1 := I.run_fixed_or_sum ((n - 1) ^ 2)
      rcases h1 with ⟨i, hi, hfix'⟩ | hsum'
      · rw [I.run_fixed_of_le hi hfix', hfix']
      · rcases I.step_cases (I.run ((n - 1) ^ 2)) with ⟨h, -⟩ | ⟨p, -, h⟩
        · exact h
        · have := I.sum_le (I.inv_step (I.inv_run ((n - 1) ^ 2)))
          rw [h, sum_update_succ, hsum'] at this
          omega
  · have := I.sum_le (I.inv_run ((n - 1) ^ 2 + 1))
    omega


/-- The state reached by deferred acceptance. -/
@[expose] def finalState : State n := I.run ((n - 1) ^ 2)

/-- The final state satisfies the invariant. -/
theorem inv_finalState : I.Inv I.finalState := I.inv_run _

/-- One more round of the run is one more step. -/
theorem run_succ (k : ℕ) : I.run (k + 1) = I.step (I.run k) := by
  rw [run, Function.iterate_succ_apply']
  rfl

/-- Rejection counts never decrease along the run. -/
theorem run_le_run_succ (k : ℕ) (p : Fin n) : I.run k p ≤ I.run (k + 1) p := by
  rw [run_succ]
  rcases I.step_cases (I.run k) with ⟨h, -⟩ | ⟨q, -, h⟩
  · rw [h]
  · rw [h]
    by_cases hpq : p = q
    · subst hpq; rw [Function.update_self]; omega
    · rw [Function.update_of_ne hpq]

/-- Rejection counts are monotone in the number of rounds. -/
theorem run_mono {j k : ℕ} (hjk : j ≤ k) (p : Fin n) : I.run j p ≤ I.run k p := by
  induction k, hjk using Nat.le_induction with
  | base => exact le_rfl
  | succ k _ ih => exact ih.trans (I.run_le_run_succ k p)

/-- After `(n - 1) ^ 2` rounds the run has reached the final state. -/
theorem run_eq_finalState {k : ℕ} (hk : (n - 1) ^ 2 ≤ k) : I.run k = I.finalState :=
  I.run_fixed_of_le hk I.step_run_fixed

/-- Every intermediate rejection count is bounded by the final one. -/
theorem run_le_finalState (k : ℕ) (p : Fin n) : I.run k p ≤ I.finalState p := by
  rcases le_total k ((n - 1) ^ 2) with h | h
  · exact I.run_mono h p
  · rw [I.run_eq_finalState h]

/-- No proposer is outranked in the final state. -/
theorem not_outranked_finalState (p : Fin n) : ¬ I.Outranked I.finalState p := by
  rcases I.step_cases I.finalState with ⟨-, h⟩ | ⟨q, -, h⟩
  · exact h p
  · have h' := I.step_run_fixed
    rw [← finalState, h] at h'
    have := congrFun h' q
    simp only [Function.update_self] at this
    omega

/-- Distinct proposers end at distinct receivers. -/
theorem target_finalState_injective : Function.Injective (I.target I.finalState) := by
  intro p q hpq
  by_contra hne
  rcases lt_trichotomy (I.recvRank (I.target I.finalState p) p)
      (I.recvRank (I.target I.finalState p) q) with h | h | h
  · exact I.not_outranked_finalState q ⟨p, hpq, hpq ▸ h⟩
  · exact hne ((I.recvPref _).symm.injective h)
  · exact I.not_outranked_finalState p ⟨q, hpq.symm, h⟩

/-- The proposer-proposing deferred-acceptance matching. -/
@[expose] def deferredAcceptance : Matching n :=
  permOfInjective (I.target I.finalState) I.target_finalState_injective

/-- Proposer `p` is matched to the receiver it proposes to in the final state. -/
theorem deferredAcceptance_apply (p : Fin n) :
    I.deferredAcceptance p = I.target I.finalState p := rfl

/-- Proposer `p` ends at its choice of rank `finalState p`. -/
theorem propRank_deferredAcceptance (p : Fin n) :
    (I.propRank p (I.deferredAcceptance p)).val = I.finalState p := by
  rw [deferredAcceptance_apply, I.target_of_lt (I.inv_finalState.lt p), propRank_propPref]

/-- Deferred acceptance outputs a stable matching ([GaleShapley1962], Theorem 1). -/
theorem isStable_deferredAcceptance : I.IsStable I.deferredAcceptance := by
  rintro p r ⟨hp, hr⟩
  have hs := I.inv_finalState
  have hk : (I.propRank p r).val < I.finalState p := by
    rw [← propRank_deferredAcceptance]; exact hp
  obtain ⟨q, hq, hqp⟩ := hs.rejected p _ hk
  rw [propPref_propRank] at hq hqp
  have hq' : I.deferredAcceptance q = r := hq
  have : I.deferredAcceptance.symm r = q := by rw [← hq', Equiv.symm_apply_apply]
  rw [this] at hr
  exact lt_asymm hr hqp


/-- No proposer has been turned down by a receiver it is matched to in the stable matching `ν`. -/
private def NoStableRejected (ν : Matching n) (s : State n) : Prop :=
  ∀ p (k : Fin n), k.val < s p → ν p ≠ I.propPref p k

private theorem noStableRejected_init (ν : Matching n) : I.NoStableRejected ν (fun _ => 0) :=
  fun _ _ hk => absurd hk (Nat.not_lt_zero _)

private theorem noStableRejected_update {ν : Matching n} (hν : I.IsStable ν) {s : State n}
    (hs : I.Inv s) (hN : I.NoStableRejected ν s) {p : Fin n} (hp : I.Outranked s p) :
    I.NoStableRejected ν (Function.update s p (s p + 1)) := by
  intro x k hk
  by_cases hxp : x = p
  · subst hxp
    rw [Function.update_self] at hk
    rcases Nat.lt_or_ge k.val (s x) with h | h
    · exact hN x k h
    · have hkx : k = ⟨s x, hs.lt x⟩ := by ext; simp only; omega
      have ht : I.propPref x k = I.target s x := by rw [I.target_of_lt (hs.lt x), hkx]
      rw [ht]
      intro hνx
      obtain ⟨y, hy, hyx⟩ := hp
      have hyx' : y ≠ x := I.ne_of_outranks hyx
      have hνy : ν y ≠ I.target s x := by
        rw [← hνx]
        exact fun h => hyx' (ν.injective h)
      have hrank : I.propRank y (I.target s y) < I.propRank y (ν y) := by
        have hge : ¬ (I.propRank y (ν y)).val < s y := fun hlt =>
          hN y _ hlt (propPref_propRank I y (ν y)).symm
        rw [I.target_of_lt (hs.lt y), propRank_propPref]
        refine lt_of_le_of_ne (by simp only [Fin.le_def]; omega) fun h => hνy ?_
        rw [← hy, I.target_of_lt (hs.lt y), h, propPref_propRank]
      apply hν y (I.target s x)
      refine ⟨hy ▸ hrank, ?_⟩
      have : ν.symm (I.target s x) = x := by rw [← hνx, Equiv.symm_apply_apply]
      rw [this]
      exact hyx
  · rw [Function.update_of_ne hxp] at hk
    exact hN x k hk

private theorem noStableRejected_run {ν : Matching n} (hν : I.IsStable ν) (k : ℕ) :
    I.NoStableRejected ν (I.run k) := by
  induction k with
  | zero => exact I.noStableRejected_init ν
  | succ k ih =>
    rw [run, Function.iterate_succ_apply', ← run]
    rcases I.step_cases (I.run k) with ⟨h, -⟩ | ⟨p, hp, h⟩
    · rw [h]; exact ih
    · rw [h]; exact I.noStableRejected_update hν (I.inv_run k) ih hp

/-- Proposer-optimality ([GaleShapley1962], Theorem 2): every proposer weakly prefers its
deferred-acceptance partner to its partner in any stable matching. -/
theorem propRank_deferredAcceptance_le {ν : Matching n} (hν : I.IsStable ν) (p : Fin n) :
    I.propRank p (I.deferredAcceptance p) ≤ I.propRank p (ν p) := by
  rw [Fin.le_def, propRank_deferredAcceptance]
  by_contra h
  exact I.noStableRejected_run hν ((n - 1) ^ 2) p _ (by rw [← finalState]; omega)
    (propPref_propRank I p (ν p)).symm


/-- The number of proposals made by deferred acceptance: proposer `p` proposed to its first
`finalState p + 1` choices. -/
@[expose] def proposals : ℕ := ∑ p, (I.finalState p + 1)

/-- The number of proposals depends only on the output: proposer `p` proposed to every receiver
that it ranks no lower than its final partner. -/
theorem proposals_eq :
    I.proposals = ∑ p, ((I.propRank p (I.deferredAcceptance p)).val + 1) := by
  simp only [proposals, propRank_deferredAcceptance]

/-- Deferred acceptance makes at most `n^2 - n + 1` proposals (see [GusfieldIrving1989]). -/
theorem proposals_le : I.proposals ≤ n ^ 2 - n + 1 := by
  have h := I.sum_le I.inv_finalState
  have hp : I.proposals = ∑ p, I.finalState p + n := by
    rw [proposals, Finset.sum_add_distrib]
    simp
  rw [hp]
  rcases n with _ | m
  · simp at h ⊢
  · have : (m + 1) ^ 2 - (m + 1) + 1 = m ^ 2 + (m + 1) := by
      rw [show (m + 1) ^ 2 = m ^ 2 + (m + 1) + m by ring]
      omega
    rw [this]
    simp only [Nat.add_sub_cancel] at h
    omega

/-- Deferred acceptance is the proposer-optimal stable matching. -/
theorem isProposerOptimal_deferredAcceptance : I.IsProposerOptimal I.deferredAcceptance :=
  ⟨I.isStable_deferredAcceptance, fun _ hν p => I.propRank_deferredAcceptance_le hν p⟩

/-- Deferred acceptance is receiver-pessimal ([McVitieWilson1971]). -/
theorem isReceiverPessimal_deferredAcceptance : I.IsReceiverPessimal I.deferredAcceptance :=
  I.isProposerOptimal_deferredAcceptance.isReceiverPessimal

/-- Every market has a stable matching ([GaleShapley1962], Theorem 1). -/
theorem exists_isStable : ∃ μ : Matching n, I.IsStable μ :=
  ⟨I.deferredAcceptance, I.isStable_deferredAcceptance⟩

/-- Every market has a (unique) proposer-optimal stable matching. -/
theorem isProposerOptimal_iff (μ : Matching n) :
    I.IsProposerOptimal μ ↔ μ = I.deferredAcceptance :=
  ⟨fun h => h.unique I.isProposerOptimal_deferredAcceptance,
    fun h => h ▸ I.isProposerOptimal_deferredAcceptance⟩

/-- Receiver-proposing deferred acceptance: run deferred acceptance on the swapped market. -/
@[expose] def receiverDeferredAcceptance : Matching n := I.swap.deferredAcceptance.symm

theorem isStable_receiverDeferredAcceptance : I.IsStable I.receiverDeferredAcceptance := by
  have h := I.swap.isStable_deferredAcceptance
  rw [← Equiv.symm_symm I.swap.deferredAcceptance] at h
  exact (I.isStable_swap_iff _).1 h

/-- Receiver-proposing deferred acceptance is receiver-optimal. -/
theorem isReceiverOptimal_receiverDeferredAcceptance :
    I.IsReceiverOptimal I.receiverDeferredAcceptance := by
  rw [isReceiverOptimal_iff_swap, receiverDeferredAcceptance, Equiv.symm_symm]
  exact I.swap.isProposerOptimal_deferredAcceptance

/-- Receiver-proposing deferred acceptance is proposer-pessimal. -/
theorem isProposerPessimal_receiverDeferredAcceptance :
    I.IsProposerPessimal I.receiverDeferredAcceptance :=
  I.isReceiverOptimal_receiverDeferredAcceptance.isProposerPessimal

end Instance

end Cslib.Algorithms.Lean.StableMatching
