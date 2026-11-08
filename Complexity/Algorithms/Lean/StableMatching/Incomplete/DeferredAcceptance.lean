/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Algorithms.Lean.StableMatching.Incomplete.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Deferred acceptance with incomplete preference lists

This module implements proposer-proposing deferred acceptance [GaleShapley1962] for markets with
incomplete preference lists (`IncompleteInstance m n`) as a total, computable Lean function, and
proves that its output is stable and proposer-optimal.

A state records, for each proposer `p`, how many receivers have turned `p` down; `p` currently
proposes to the receiver at that position of its list, or to nobody once its list is exhausted.
A receiver turns a proposal down when the proposer is unacceptable to it or when it also receives
a proposal from someone it prefers. While some proposer is turned down, the first such proposer
in index order moves on to its next choice. Each step adds one rejection, and the number of
rejections is bounded by the total length of the proposers' lists, so the run stops; at that point
the current proposals form the output matching. Proposers whose lists are exhausted stay
unmatched.

## Main definitions

* `IncompleteInstance.step`, `IncompleteInstance.run`: one rejection step and the state after
  `k` steps.
* `IncompleteInstance.finalState`: the state after `totalLength` steps, which is fixed.
* `IncompleteInstance.deferredAcceptance`: the proposer-proposing deferred-acceptance matching.
* `IncompleteInstance.receiverDeferredAcceptance`: receiver-proposing deferred acceptance.

## Main results

* `IncompleteInstance.step_run_fixed`, `IncompleteInstance.sum_finalState_le`: the run stops
  after at most `totalLength` rejections, the total length of the proposers' lists.
* `IncompleteInstance.isStable_deferredAcceptance`, `IncompleteInstance.exists_isStable`: the
  output is stable, hence every market with incomplete lists has a stable matching
  ([RothSotomayor1990], Theorem 2.8).
* `IncompleteInstance.isProposerOptimal_deferredAcceptance`: every proposer weakly prefers its
  deferred-acceptance outcome to its outcome in any stable matching ([RothSotomayor1990],
  Theorem 2.12; [GaleShapley1962], Theorem 2, for complete lists), and
  `IncompleteInstance.isReceiverPessimal_deferredAcceptance`: receivers are correspondingly worst
  off.
* `IncompleteInstance.isReceiverOptimal_receiverDeferredAcceptance`: the dual statements for
  receiver-proposing deferred acceptance.

## Cost model

No cost is charged. The number of rejections is at most `totalLength`; this module does not
charge the cost of finding a rejected proposer or of the surrounding bookkeeping on any machine
model.

## References

* [GaleShapley1962]
* [RothSotomayor1990]
-/

public section

namespace Cslib.Algorithms.Lean.StableMatching

namespace IncompleteInstance

variable {m n : ℕ} (I : IncompleteInstance m n)

/-- The receiver proposer `p` proposes to after `s p` rejections: the entry at position `s p` of
its list, or `none` once the list is exhausted. -/
@[expose] def target (s : Fin m → ℕ) (p : Fin m) : Option (Fin n) := (I.propPref p)[s p]?

/-- Receiver `r` turns proposer `p` down in state `s`: `p` is unacceptable to `r`, or `r`
receives a proposal from someone it strictly prefers to `p`. -/
@[expose] def TurnsDown (s : Fin m → ℕ) (r : Fin n) (p : Fin m) : Prop :=
  p ∉ I.recvPref r ∨ ∃ q, I.target s q = some r ∧ I.recvRank r (some q) < I.recvRank r (some p)

instance (s : Fin m → ℕ) (r : Fin n) (p : Fin m) : Decidable (I.TurnsDown s r p) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- Proposer `p` is rejected in state `s` when the receiver it proposes to turns it down. -/
@[expose] def Rejected (s : Fin m → ℕ) (p : Fin m) : Prop :=
  ∃ r, I.target s p = some r ∧ I.TurnsDown s r p

instance (s : Fin m → ℕ) (p : Fin m) : Decidable (I.Rejected s p) :=
  inferInstanceAs (Decidable (∃ _, _))

/-- One step of deferred acceptance: the first rejected proposer moves on to its next choice. A
state with no rejected proposer is fixed. -/
@[expose] def step (s : Fin m → ℕ) : Fin m → ℕ :=
  match (List.finRange m).find? (fun p => decide (I.Rejected s p)) with
  | some p => Function.update s p (s p + 1)
  | none => s

/-- The state after `k` steps, starting with every proposer at its first choice. -/
@[expose] def run (k : ℕ) : Fin m → ℕ := (I.step)^[k] (fun _ => 0)

/-- The total length of the proposers' lists, which bounds the number of rejections. -/
@[expose] def totalLength : ℕ := ∑ p, (I.propPref p).length

/-- A step either fixes a state with no rejected proposer or advances one rejected proposer. -/
theorem step_cases (s : Fin m → ℕ) :
    (I.step s = s ∧ ∀ p, ¬ I.Rejected s p) ∨
      ∃ p, I.Rejected s p ∧ I.step s = Function.update s p (s p + 1) := by
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

/-- The deferred-acceptance invariant: no proposer has passed the end of its list, and every
receiver that proposer `p` has passed still turns `p` down. -/
structure Inv (s : Fin m → ℕ) : Prop where
  /-- No proposer has passed the end of its list. -/
  le_length : ∀ p, s p ≤ (I.propPref p).length
  /-- A receiver that `p` has passed still turns `p` down. -/
  turnsDown : ∀ p k r, k < s p → (I.propPref p)[k]? = some r → I.TurnsDown s r p

/-- The initial state satisfies the invariant. -/
theorem inv_init : I.Inv (fun _ => 0) where
  le_length _ := Nat.zero_le _
  turnsDown _ _ _ hk := absurd hk (Nat.not_lt_zero _)

private theorem target_update_ne (s : Fin m → ℕ) {p x : Fin m} (h : x ≠ p) (v : ℕ) :
    I.target (Function.update s p v) x = I.target s x := by
  simp only [target, Function.update_of_ne h]

/-- A rejection persists after the rejected proposer moves on: every receiver that turned some
proposer down still does. -/
private theorem turnsDown_update {s : Fin m → ℕ} {p : Fin m} (hp : I.Rejected s p)
    {r : Fin n} {x : Fin m} (h : I.TurnsDown s r x) :
    I.TurnsDown (Function.update s p (s p + 1)) r x := by
  rcases h with h | ⟨q, hq, hqx⟩
  · exact Or.inl h
  · by_cases hqp : q = p
    · subst hqp
      obtain ⟨r', hr', hd⟩ := hp
      have hrr : r' = r := Option.some_injective _ (hr'.symm.trans hq)
      subst hrr
      rcases hd with hd | ⟨y, hy, hyq⟩
      · exfalso
        have heq : I.recvRank r' (some q) = I.recvRank r' none := List.idxOf_eq_length_iff.2 hd
        have := I.recvRank_le_recvRank_none r' (some x)
        omega
      · have hyq' : y ≠ q := by rintro rfl; exact lt_irrefl _ hyq
        exact Or.inr ⟨y, by rw [I.target_update_ne s hyq', hy], lt_trans hyq hqx⟩
    · exact Or.inr ⟨q, by rw [I.target_update_ne s hqp, hq], hqx⟩

private theorem inv_update {s : Fin m → ℕ} (hs : I.Inv s) {p : Fin m} (hp : I.Rejected s p) :
    I.Inv (Function.update s p (s p + 1)) where
  le_length x := by
    by_cases hxp : x = p
    · subst hxp
      rw [Function.update_self]
      obtain ⟨r, hr, -⟩ := hp
      exact (List.getElem?_eq_some_iff.1 hr).1
    · rw [Function.update_of_ne hxp]
      exact hs.le_length x
  turnsDown x k r hk hkr := by
    by_cases hxp : x = p
    · subst hxp
      rw [Function.update_self] at hk
      rcases Nat.lt_or_ge k (s x) with h | h
      · exact I.turnsDown_update hp (hs.turnsDown x k r h hkr)
      · have hk' : k = s x := by omega
        subst hk'
        obtain ⟨r', hr', hd⟩ := hp
        have hrr : r' = r := Option.some_injective _ (hr'.symm.trans hkr)
        subst hrr
        exact I.turnsDown_update ⟨r', hr', hd⟩ hd
    · rw [Function.update_of_ne hxp] at hk
      exact I.turnsDown_update hp (hs.turnsDown x k r hk hkr)

/-- Steps preserve the invariant. -/
theorem inv_step {s : Fin m → ℕ} (hs : I.Inv s) : I.Inv (I.step s) := by
  rcases I.step_cases s with ⟨h, -⟩ | ⟨p, hp, h⟩
  · rw [h]; exact hs
  · rw [h]; exact I.inv_update hs hp

/-- One more round of the run is one more step. -/
theorem run_succ (k : ℕ) : I.run (k + 1) = I.step (I.run k) := by
  rw [run, Function.iterate_succ_apply']
  rfl

/-- Every state of the run satisfies the invariant. -/
theorem inv_run (k : ℕ) : I.Inv (I.run k) := by
  induction k with
  | zero => exact I.inv_init
  | succ k ih =>
    rw [run, Function.iterate_succ_apply']
    exact I.inv_step ih

/-- The total number of rejections in an invariant state is at most `totalLength`. -/
theorem sum_le {s : Fin m → ℕ} (hs : I.Inv s) : ∑ p, s p ≤ I.totalLength :=
  Finset.sum_le_sum fun p _ => hs.le_length p

/-- Either the run has stopped by step `k`, or it has made at least `k` rejections. -/
private theorem run_fixed_or_le_sum (k : ℕ) :
    (∃ j < k, I.step (I.run j) = I.run j) ∨ k ≤ ∑ x, I.run k x := by
  induction k with
  | zero => exact Or.inr (Nat.zero_le _)
  | succ k ih =>
    rcases ih with ⟨j, hj, hfix⟩ | hsum
    · exact Or.inl ⟨j, by omega, hfix⟩
    · rcases I.step_cases (I.run k) with ⟨h, -⟩ | ⟨p, -, h⟩
      · exact Or.inl ⟨k, by omega, h⟩
      · right
        have hlt : ∑ x, I.run k x < ∑ x, I.run (k + 1) x := by
          rw [run_succ, h]
          refine Finset.sum_lt_sum (fun x _ => ?_) ⟨p, Finset.mem_univ p, ?_⟩
          · by_cases hxp : x = p
            · subst hxp; rw [Function.update_self]; omega
            · rw [Function.update_of_ne hxp]
          · rw [Function.update_self]; omega
        omega

/-- Once the run reaches a fixed state, it stays there. -/
theorem run_fixed_of_le {j k : ℕ} (hjk : j ≤ k) (h : I.step (I.run j) = I.run j) :
    I.run k = I.run j := by
  induction k, hjk using Nat.le_induction with
  | base => rfl
  | succ k _ ih => rw [run, Function.iterate_succ_apply', ← run, ih, h]

/-- Deferred acceptance stops after at most `totalLength` rejections. -/
theorem step_run_fixed : I.step (I.run I.totalLength) = I.run I.totalLength := by
  rcases I.run_fixed_or_le_sum (I.totalLength + 1) with ⟨j, hj, hfix⟩ | hsum
  · rw [I.run_fixed_of_le (by omega : j ≤ I.totalLength) hfix, hfix]
  · have := I.sum_le (I.inv_run (I.totalLength + 1))
    omega

/-- The state reached by deferred acceptance. -/
@[expose] def finalState : Fin m → ℕ := I.run I.totalLength

/-- The final state satisfies the invariant. -/
theorem inv_finalState : I.Inv I.finalState := I.inv_run _

/-- Deferred acceptance makes at most `totalLength` rejections. -/
theorem sum_finalState_le : ∑ p, I.finalState p ≤ I.totalLength := I.sum_le I.inv_finalState

/-- No proposer is rejected in the final state. -/
theorem not_rejected_finalState (p : Fin m) : ¬ I.Rejected I.finalState p := by
  rcases I.step_cases I.finalState with ⟨-, h⟩ | ⟨q, -, h⟩
  · exact h p
  · have h' := I.step_run_fixed
    rw [← finalState, h] at h'
    have := congrFun h' q
    simp only [Function.update_self] at this
    omega

/-- Distinct proposers end at distinct receivers. -/
theorem target_finalState_inj (p q : Fin m) (r : Fin n) (hp : I.target I.finalState p = some r)
    (hq : I.target I.finalState q = some r) : p = q := by
  by_contra hne
  have hpr : p ∈ I.recvPref r := by
    by_contra h; exact I.not_rejected_finalState p ⟨r, hp, Or.inl h⟩
  have hqr : q ∈ I.recvPref r := by
    by_contra h; exact I.not_rejected_finalState q ⟨r, hq, Or.inl h⟩
  rcases lt_trichotomy (I.recvRank r (some p)) (I.recvRank r (some q)) with h | h | h
  · exact I.not_rejected_finalState q ⟨r, hq, Or.inr ⟨p, hp, h⟩⟩
  · exact hne (Option.some_injective _ (I.eq_of_recvRank_eq hpr h)).symm
  · exact I.not_rejected_finalState p ⟨r, hp, Or.inr ⟨q, hq, h⟩⟩

/-- The proposer-proposing deferred-acceptance matching: each proposer is matched to the receiver
it proposes to in the final state, and is unmatched if its list is exhausted. -/
@[expose] def deferredAcceptance : PartialMatching m n :=
  PartialMatching.ofInjOn (I.target I.finalState) I.target_finalState_inj

theorem deferredAcceptance_apply (p : Fin m) :
    I.deferredAcceptance p = (I.propPref p)[I.finalState p]? := rfl

/-- The first occurrence of an element in a list is no later than any of its occurrences. -/
private theorem idxOf_le_of_getElem?_eq {α : Type*} [DecidableEq α] {l : List α} {i : ℕ}
    {a : α} (h : l[i]? = some a) : l.idxOf a ≤ i := by
  obtain ⟨hi, hia⟩ := List.getElem?_eq_some_iff.1 h
  by_contra hlt
  push Not at hlt
  have := List.not_of_lt_findIdx (p := fun x => x == a) (xs := l) hlt
  simp only [hia, beq_self_eq_true] at this
  exact Bool.false_ne_true this.symm

/-- Proposer `p` ranks its deferred-acceptance outcome no worse than its position after the final
number of rejections. -/
theorem propRank_deferredAcceptance_le (p : Fin m) :
    I.propRank p (I.deferredAcceptance p) ≤ I.finalState p := by
  rw [deferredAcceptance_apply]
  cases h : (I.propPref p)[I.finalState p]? with
  | none =>
    rw [propRank_none]
    have := List.getElem?_eq_none_iff.1 h
    have := I.inv_finalState.le_length p
    omega
  | some r => exact idxOf_le_of_getElem?_eq h

/-- The deferred-acceptance matching is individually rational. -/
theorem isIndividuallyRational_deferredAcceptance :
    I.IsIndividuallyRational I.deferredAcceptance := by
  intro p r h
  refine ⟨List.mem_of_getElem? h, ?_⟩
  by_contra hr
  exact I.not_rejected_finalState p ⟨r, h, Or.inl hr⟩

/-- Deferred acceptance outputs a stable matching ([RothSotomayor1990], Theorem 2.8). -/
theorem isStable_deferredAcceptance : I.IsStable I.deferredAcceptance := by
  refine ⟨I.isIndividuallyRational_deferredAcceptance, fun p r ⟨hp, hr⟩ => ?_⟩
  have hk : I.propRank p (some r) < I.finalState p :=
    lt_of_lt_of_le hp (I.propRank_deferredAcceptance_le p)
  have hmem : r ∈ I.propPref p := (I.propRank_some_lt_none_iff p r).1
    (lt_of_lt_of_le hp (I.propRank_le_propRank_none p _))
  have hget : (I.propPref p)[(I.propPref p).idxOf r]? = some r := List.getElem?_idxOf hmem
  rcases I.inv_finalState.turnsDown p _ r hk hget with hd | ⟨q, hq, hqp⟩
  · exact hd (IsBlockingPair.mem_recvPref I ⟨hp, hr⟩)
  · have hsymm : I.deferredAcceptance.symm r = some q := I.deferredAcceptance.eq_some_iff.2 hq
    rw [hsymm] at hr
    exact lt_asymm hr hqp

/-- Every market with incomplete lists has a stable matching ([RothSotomayor1990], Theorem 2.8). -/
theorem exists_isStable : ∃ μ : PartialMatching m n, I.IsStable μ :=
  ⟨I.deferredAcceptance, I.isStable_deferredAcceptance⟩

/-! ### Proposer-optimality -/

/-- No proposer has passed a receiver it is matched to in the stable matching `ν`. -/
private def NoStableRejected (ν : PartialMatching m n) (s : Fin m → ℕ) : Prop :=
  ∀ p k r, k < s p → (I.propPref p)[k]? = some r → ν p ≠ some r

private theorem noStableRejected_init (ν : PartialMatching m n) :
    I.NoStableRejected ν (fun _ => 0) :=
  fun _ _ _ hk => absurd hk (Nat.not_lt_zero _)

/-- Under `NoStableRejected`, every proposer has made at most as many rejections as the rank of
its partner in the stable matching `ν`. -/
private theorem le_propRank_of_noStableRejected {ν : PartialMatching m n}
    (hν : I.IsStable ν) {s : Fin m → ℕ} (hs : I.Inv s) (hN : I.NoStableRejected ν s) (y : Fin m) :
    s y ≤ I.propRank y (ν y) := by
  by_contra hlt
  push Not at hlt
  cases hνy : ν y with
  | none =>
    rw [hνy, propRank_none] at hlt
    have := hs.le_length y
    omega
  | some r =>
    rw [hνy, propRank_some] at hlt
    exact hN y _ r hlt (List.getElem?_idxOf (hν.1 y r hνy).1) hνy

private theorem noStableRejected_update {ν : PartialMatching m n} (hν : I.IsStable ν)
    {s : Fin m → ℕ} (hs : I.Inv s) (hN : I.NoStableRejected ν s) {x : Fin m}
    (hx : I.Rejected s x) : I.NoStableRejected ν (Function.update s x (s x + 1)) := by
  intro p k r hk hkr
  by_cases hpx : p = x
  · subst hpx
    rw [Function.update_self] at hk
    rcases Nat.lt_or_ge k (s p) with h | h
    · exact hN p k r h hkr
    · have hk' : k = s p := by omega
      subst hk'
      intro hνp
      obtain ⟨r', hr', hd⟩ := hx
      have hrr : r' = r := Option.some_injective _ (hr'.symm.trans hkr)
      subst hrr
      rcases hd with hd | ⟨y, hy, hyp⟩
      · exact hd (hν.1 p r' hνp).2
      · have hyp' : y ≠ p := by rintro rfl; exact lt_irrefl _ hyp
        have hsymm : ν.symm r' = some p := ν.eq_some_iff.2 hνp
        have hle := I.le_propRank_of_noStableRejected hν hs hN y
        have hidx : I.propRank y (some r') ≤ s y := idxOf_le_of_getElem?_eq hy
        have hlt : I.propRank y (some r') < I.propRank y (ν y) := by
          refine lt_of_le_of_ne (hidx.trans hle) fun heq => hyp' ?_
          have hmem : r' ∈ I.propPref y := List.mem_of_getElem? hy
          have hνy : ν y = some r' := I.eq_of_propRank_eq hmem heq
          exact ν.inj (b := r') hνy hνp
        exact hν.2 y r' ⟨hlt, hsymm ▸ hyp⟩
  · rw [Function.update_of_ne hpx] at hk
    exact hN p k r hk hkr

private theorem noStableRejected_run {ν : PartialMatching m n} (hν : I.IsStable ν) (k : ℕ) :
    I.NoStableRejected ν (I.run k) := by
  induction k with
  | zero => exact I.noStableRejected_init ν
  | succ k ih =>
    rw [run, Function.iterate_succ_apply', ← run]
    rcases I.step_cases (I.run k) with ⟨h, -⟩ | ⟨p, hp, h⟩
    · rw [h]; exact ih
    · rw [h]; exact I.noStableRejected_update hν (I.inv_run k) ih hp

/-- Proposer-optimality ([RothSotomayor1990], Theorem 2.12): every proposer weakly prefers its
deferred-acceptance outcome to its outcome in any stable matching. -/
theorem propRank_deferredAcceptance_le_of_isStable {ν : PartialMatching m n} (hν : I.IsStable ν)
    (p : Fin m) : I.propRank p (I.deferredAcceptance p) ≤ I.propRank p (ν p) :=
  (I.propRank_deferredAcceptance_le p).trans
    (I.le_propRank_of_noStableRejected hν I.inv_finalState (I.noStableRejected_run hν _) p)

/-- Deferred acceptance is the proposer-optimal stable matching. -/
theorem isProposerOptimal_deferredAcceptance : I.IsProposerOptimal I.deferredAcceptance :=
  ⟨I.isStable_deferredAcceptance, fun _ hν p => I.propRank_deferredAcceptance_le_of_isStable hν p⟩

/-- Deferred acceptance is receiver-pessimal. -/
theorem isReceiverPessimal_deferredAcceptance : I.IsReceiverPessimal I.deferredAcceptance :=
  I.isProposerOptimal_deferredAcceptance.isReceiverPessimal

/-- Deferred acceptance is the unique proposer-optimal stable matching. -/
theorem isProposerOptimal_iff (μ : PartialMatching m n) :
    I.IsProposerOptimal μ ↔ μ = I.deferredAcceptance :=
  ⟨fun h => h.unique I.isProposerOptimal_deferredAcceptance,
    fun h => h ▸ I.isProposerOptimal_deferredAcceptance⟩

/-! ### Receiver-proposing deferred acceptance -/

/-- Receiver-proposing deferred acceptance: run deferred acceptance on the swapped market. -/
@[expose] def receiverDeferredAcceptance : PartialMatching m n :=
  I.swap.deferredAcceptance.symm

theorem isStable_receiverDeferredAcceptance : I.IsStable I.receiverDeferredAcceptance :=
  (I.isStable_swap_iff _).1 I.swap.isStable_deferredAcceptance

/-- Receiver-proposing deferred acceptance is receiver-optimal. -/
theorem isReceiverOptimal_receiverDeferredAcceptance :
    I.IsReceiverOptimal I.receiverDeferredAcceptance := by
  rw [isReceiverOptimal_iff_swap, receiverDeferredAcceptance, PEquiv.symm_symm]
  exact I.swap.isProposerOptimal_deferredAcceptance

/-- Receiver-proposing deferred acceptance is proposer-pessimal. -/
theorem isProposerPessimal_receiverDeferredAcceptance :
    I.IsProposerPessimal I.receiverDeferredAcceptance :=
  I.isReceiverOptimal_receiverDeferredAcceptance.isProposerPessimal

end IncompleteInstance

end Cslib.Algorithms.Lean.StableMatching
