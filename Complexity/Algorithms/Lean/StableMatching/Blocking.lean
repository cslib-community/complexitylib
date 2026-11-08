/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Algorithms.Lean.StableMatching.DeferredAcceptance
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Finset.Max

/-!
# The blocking lemma for deferred acceptance

If some proposers strictly prefer a matching `μ` to the proposer-proposing deferred-acceptance
matching, then `μ` is blocked by a pair `(x, μ q)` in which `q` strictly prefers `μ` while `x` does
not. This is the blocking lemma, which [GaleSotomayor1985] credit to J. S. Hwang; the proof here is
the standard one (see also [GusfieldIrving1989]): either some proposer `q` that prefers `μ` is
matched in `μ` to the deferred-acceptance partner of a proposer `x` that does not, or the set of
proposers preferring `μ` is closed under this map, and then the last rejection in the run of
deferred acceptance that involves a member of this set produces the blocking pair.

Consequences in this file:

* weak Pareto optimality of deferred acceptance for the proposers ([Roth1982], Theorem 6): no
  matching makes every proposer strictly better off;
* coalitional strategy-proofness of deferred acceptance for the proposers [DubinsFreedman1981]:
  no nonempty coalition of proposers can misreport so that, in some stable matching of the
  reported instance, every member gets a partner it truly prefers to its deferred-acceptance
  partner; in particular no single proposer gains by misreporting ([Roth1982], Theorem 5).

The misreported instances are built with `Instance.updatePropPref` from `Basic`.

## Main results

* `Instance.exists_isBlockingPair_of_lt`: the blocking lemma.
* `Instance.not_forall_propRank_lt_deferredAcceptance`: weak Pareto optimality.
* `Instance.not_forall_mem_propRank_lt_of_isStable`: coalitional strategy-proofness.
* `Instance.propRank_deferredAcceptance_le_updatePropPref`: individual strategy-proofness.

## References

* [DubinsFreedman1981]
* [GaleSotomayor1985]
* [GusfieldIrving1989]
* [Roth1982]
-/

public section

namespace Cslib.Algorithms.Lean.StableMatching.Instance

variable {n : ℕ} (I : Instance n)

/-! ### The blocking lemma -/

/-- A receiver that turned `q` down in deferred acceptance prefers its final partner to `q`. -/
theorem recvRank_deferredAcceptance_lt {q r : Fin n}
    (h : I.propRank q r < I.propRank q (I.deferredAcceptance q)) :
    I.recvRank r (I.deferredAcceptance.symm r) < I.recvRank r q := by
  have hk : (I.propRank q r).val < I.finalState q := by
    rw [← propRank_deferredAcceptance]; exact h
  obtain ⟨y, hy, hyq⟩ := I.inv_finalState.rejected q _ hk
  rw [propPref_propRank] at hy hyq
  have hy' : I.deferredAcceptance y = r := hy
  subst hy'
  rw [Equiv.symm_apply_apply]
  exact hyq

/-- First case of the blocking lemma: some proposer that prefers `μ` is matched in `μ` to the
deferred-acceptance partner of a proposer that does not. -/
private theorem blocking_of_not_better {μ : Matching n} {q : Fin n}
    (hq : I.propRank q (μ q) < I.propRank q (I.deferredAcceptance q))
    (hx : ¬ I.propRank (I.deferredAcceptance.symm (μ q)) (μ (I.deferredAcceptance.symm (μ q))) <
      I.propRank (I.deferredAcceptance.symm (μ q))
        (I.deferredAcceptance (I.deferredAcceptance.symm (μ q)))) :
    I.IsBlockingPair μ (I.deferredAcceptance.symm (μ q)) (μ q) := by
  have hDx : I.deferredAcceptance (I.deferredAcceptance.symm (μ q)) = μ q :=
    Equiv.apply_symm_apply _ _
  generalize hxdef : I.deferredAcceptance.symm (μ q) = x at hx hDx ⊢
  have hxq : x ≠ q := by
    rintro rfl
    exact hx hq
  have hμx : μ x ≠ μ q := fun h => hxq (μ.injective h)
  push Not at hx
  rw [hDx] at hx
  refine ⟨lt_of_le_of_ne hx fun h => hμx (I.propRank_injective x h).symm, ?_⟩
  have h := I.recvRank_deferredAcceptance_lt hq
  rw [RecvPrefers, ← hxdef, Equiv.symm_apply_apply]
  rw [hxdef] at h ⊢
  exact h

/-- If `σ` is injective and maps the finite set `B` into itself, it maps `B` onto itself. -/
private theorem exists_eq_of_mapsTo {σ : Fin n → Fin n} (hσ : Function.Injective σ)
    {B : Set (Fin n)} (hB : ∀ q ∈ B, σ q ∈ B) {p : Fin n} (hp : p ∈ B) :
    ∃ q ∈ B, σ q = p :=
  ((Set.toFinite B).injOn_iff_bijOn_of_mapsTo hB).1 hσ.injOn |>.surjOn hp

/-- If a proposer's count is positive at the end, there is a last step at which some member of a
set `B` containing it changes, after which no member of `B` changes. -/
private theorem exists_last_change (B : Finset (Fin n)) {p₀ : Fin n} (hp₀ : p₀ ∈ B)
    (hpos : 0 < I.finalState p₀) :
    ∃ t < (n - 1) ^ 2, ∃ p ∈ B, I.run t p ≠ I.run (t + 1) p ∧
      ∀ q ∈ B, I.run (t + 1) q = I.finalState q := by
  classical
  set N := (n - 1) ^ 2
  let T := (Finset.range N).filter fun k => ∃ p ∈ B, I.run k p ≠ I.run (k + 1) p
  have hT : T.Nonempty := by
    by_contra hT
    rw [Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff] at hT
    have key : ∀ k ≤ N, I.run k p₀ = 0 := by
      intro k hk
      induction k with
      | zero => rfl
      | succ k ih =>
        have h1 := hT (Finset.mem_range.2 (show k < N by omega))
        push Not at h1
        rw [← h1 p₀ hp₀, ih (by omega)]
    have := key N le_rfl
    rw [← finalState] at this
    omega
  set t := T.max' hT
  have ht : t ∈ T := T.max'_mem hT
  rw [Finset.mem_filter, Finset.mem_range] at ht
  obtain ⟨htN, p, hpB, hp⟩ := ht
  refine ⟨t, htN, p, hpB, hp, fun q hq => ?_⟩
  have stable : ∀ k, t + 1 ≤ k → k ≤ N → I.run (t + 1) q = I.run k q := by
    intro k hk hkN
    induction k, hk using Nat.le_induction with
    | base => rfl
    | succ k hk ih =>
      rw [ih (by omega)]
      by_contra hne
      have hmem : k ∈ T := by
        rw [Finset.mem_filter, Finset.mem_range]
        exact ⟨by omega, q, hq, hne⟩
      have := T.le_max' k hmem
      omega
  rw [stable N (by omega) le_rfl]
  rfl

/-- The step taken at a time when proposer `p₀` changes is the one turning `p₀` down. -/
private theorem run_succ_eq_update_of_ne {t : ℕ} {p₀ : Fin n}
    (h : I.run t p₀ ≠ I.run (t + 1) p₀) :
    I.Outranked (I.run t) p₀ ∧
      I.run (t + 1) = Function.update (I.run t) p₀ (I.run t p₀ + 1) := by
  rw [run_succ] at h ⊢
  rcases I.step_cases (I.run t) with ⟨hs, -⟩ | ⟨p, hp, hs⟩
  · rw [hs] at h
    exact absurd rfl h
  · have hpp : p₀ = p := by
      by_contra hne
      rw [hs, Function.update_of_ne hne] at h
      exact h rfl
    subst hpp
    exact ⟨hp, hs⟩

/-- Proposer `p` currently proposes to its choice of rank `s p`. -/
private theorem propRank_target {s : State n} (hs : I.Inv s) (p : Fin n) :
    (I.propRank p (I.target s p)).val = s p := by
  rw [I.target_of_lt (hs.lt p), propRank_propPref]

/-- Second case of the blocking lemma, by the last-change argument on the run. -/
private theorem blocking_of_closed {μ : Matching n} {q₀ : Fin n}
    (hq₀ : I.propRank q₀ (μ q₀) < I.propRank q₀ (I.deferredAcceptance q₀))
    (hcl : ∀ q, I.propRank q (μ q) < I.propRank q (I.deferredAcceptance q) →
      I.propRank (I.deferredAcceptance.symm (μ q)) (μ (I.deferredAcceptance.symm (μ q))) <
        I.propRank (I.deferredAcceptance.symm (μ q))
          (I.deferredAcceptance (I.deferredAcceptance.symm (μ q)))) :
    ∃ x q, I.propRank q (μ q) < I.propRank q (I.deferredAcceptance q) ∧
      I.propRank x (I.deferredAcceptance x) ≤ I.propRank x (μ x) ∧
      I.IsBlockingPair μ x (μ q) := by
  classical
  set D := I.deferredAcceptance with hD
  let B : Finset (Fin n) := Finset.univ.filter fun q => I.propRank q (μ q) < I.propRank q (D q)
  have hB : ∀ q, q ∈ B ↔ I.propRank q (μ q) < I.propRank q (D q) := fun q => by
    simp only [B, Finset.mem_filter, Finset.mem_univ, true_and]
  have hpos : ∀ q ∈ B, 0 < I.finalState q := fun q hq => by
    have h := (hB q).1 hq
    rw [Fin.lt_def, propRank_deferredAcceptance] at h
    omega
  obtain ⟨t, htN, p₀, hp₀B, hch, hfin⟩ :=
    I.exists_last_change B ((hB q₀).2 hq₀) (hpos q₀ ((hB q₀).2 hq₀))
  obtain ⟨hout, hupd⟩ := I.run_succ_eq_update_of_ne hch
  have hsI := I.inv_run t
  have hs'I := I.inv_run (t + 1)
  -- the receiver `p₀` ends at
  have hDp₀ : D p₀ = I.target (I.run (t + 1)) p₀ := by
    rw [hD, deferredAcceptance_apply]
    simp only [target, hfin p₀ hp₀B]
  -- some member of `B` is matched to it in `μ`
  obtain ⟨q, hqB, hq⟩ := exists_eq_of_mapsTo (σ := fun q => D.symm (μ q))
    (fun a b h => μ.injective (D.symm.injective h)) (B := {q | q ∈ B})
    (fun q hq => (hB _).2 (hcl q ((hB q).1 hq))) (p := p₀) hp₀B
  have hμq : μ q = D p₀ := by rw [← hq]; exact (D.apply_symm_apply _).symm
  have hqp : q ≠ p₀ := by
    intro hqp
    have h := (hB q).1 hqB
    rw [hμq, hqp] at h
    exact lt_irrefl _ h
  have hDeq : ∀ y, D y = I.target I.finalState y := fun y => by
    rw [hD, deferredAcceptance_apply]
  have hrun : ∀ y, y ≠ p₀ → I.run (t + 1) y = I.run t y := fun y hy => by
    rw [hupd, Function.update_of_ne hy]
  have htarget : ∀ y, y ≠ p₀ → I.target (I.run (t + 1)) y = I.target (I.run t) y :=
    fun y hy => by simp only [target, hrun y hy]
  -- `q` had already been turned down by `D p₀` before step `t`
  have hk : (I.propRank q (D p₀)).val < I.run t q := by
    have h := (hB q).1 hqB
    rw [hμq, Fin.lt_def, hD, propRank_deferredAcceptance, ← hfin q hqB, hrun q hqp] at h
    exact h
  obtain ⟨x, hx, hxq⟩ := hsI.rejected q _ hk
  rw [propPref_propRank] at hx hxq
  have hxp : x ≠ p₀ := by
    intro hxp
    rw [hxp] at hx
    have h1 := I.propRank_target hsI p₀
    have h2 := I.propRank_target hs'I p₀
    rw [hx] at h1
    rw [← hDp₀, h1, hupd, Function.update_self] at h2
    omega
  have hx' : I.target (I.run (t + 1)) x = D p₀ := by rw [htarget x hxp, hx]
  have hxB : x ∉ B := by
    intro hxB
    refine hxp (D.injective ?_)
    rw [hDeq x, ← hx']
    simp only [target, hfin x hxB]
  have hxle : I.propRank x (D x) ≤ I.propRank x (μ x) :=
    le_of_not_gt (mt (hB x).2 hxB)
  have hxlt : I.propRank x (D p₀) < I.propRank x (D x) := by
    have h1 := I.propRank_target hs'I x
    rw [hx'] at h1
    have h2 : (I.propRank x (D x)).val = I.finalState x := by
      rw [hD, propRank_deferredAcceptance]
    rw [Fin.lt_def, h1, h2]
    refine lt_of_le_of_ne (I.run_le_finalState (t + 1) x) fun heq => hxp (D.injective ?_)
    rw [hDeq x, ← hx']
    simp only [target, heq]
  have hμsymm : μ.symm (μ q) = q := μ.symm_apply_apply q
  refine ⟨x, q, (hB q).1 hqB, hxle, ?_, ?_⟩
  · rw [PropPrefers, hμq]
    exact lt_of_lt_of_le hxlt hxle
  · rw [RecvPrefers, hμsymm, hμq]
    exact hxq

/-- The blocking lemma (Hwang; [GaleSotomayor1985]): if some proposer strictly prefers a matching
`μ` to its deferred-acceptance partner, then `μ` is blocked by a pair `(x, μ q)` where `q`
strictly prefers `μ` and `x` weakly prefers its deferred-acceptance partner to `μ x`. -/
theorem exists_isBlockingPair_of_lt {μ : Matching n} {q₀ : Fin n}
    (hq₀ : I.propRank q₀ (μ q₀) < I.propRank q₀ (I.deferredAcceptance q₀)) :
    ∃ x q, I.propRank q (μ q) < I.propRank q (I.deferredAcceptance q) ∧
      I.propRank x (I.deferredAcceptance x) ≤ I.propRank x (μ x) ∧
      I.IsBlockingPair μ x (μ q) := by
  by_cases h : ∃ q, I.propRank q (μ q) < I.propRank q (I.deferredAcceptance q) ∧
      ¬ I.propRank (I.deferredAcceptance.symm (μ q)) (μ (I.deferredAcceptance.symm (μ q))) <
        I.propRank (I.deferredAcceptance.symm (μ q))
          (I.deferredAcceptance (I.deferredAcceptance.symm (μ q)))
  · obtain ⟨q, hq, hx⟩ := h
    exact ⟨_, q, hq, le_of_not_gt hx, I.blocking_of_not_better hq hx⟩
  · push Not at h
    exact I.blocking_of_closed hq₀ h


/-! ### Consequences -/

/-- Weak Pareto optimality of deferred acceptance for the proposers ([Roth1982], Theorem 6): when
there is at least one proposer, no matching gives every proposer a partner it strictly prefers to
its deferred-acceptance partner. -/
theorem not_forall_propRank_lt_deferredAcceptance [NeZero n] (μ : Matching n) :
    ¬ ∀ p, I.propRank p (μ p) < I.propRank p (I.deferredAcceptance p) := by
  intro h
  obtain ⟨x, -, -, hx, -⟩ := I.exists_isBlockingPair_of_lt (h 0)
  exact absurd (h x) (not_lt_of_ge hx)

/-- Coalitional strategy-proofness of deferred acceptance for the proposers
([DubinsFreedman1981]). Let `J` be obtained from `I` by letting the proposers in a nonempty
coalition `C` misreport their preference lists. Then no matching that is stable for the reported
instance `J` gives every member of `C` a partner it truly prefers to its partner in the
deferred-acceptance matching of the true instance `I`. Applied to `μ = J.deferredAcceptance` this
says that no coalition of proposers can all strictly gain by misreporting. -/
theorem not_forall_mem_propRank_lt_of_isStable {J : Instance n} {C : Set (Fin n)}
    (hrecv : J.recvPref = I.recvPref) (hprop : ∀ p ∉ C, J.propPref p = I.propPref p)
    (hC : C.Nonempty) {μ : Matching n} (hμ : J.IsStable μ) :
    ¬ ∀ p ∈ C, I.propRank p (μ p) < I.propRank p (I.deferredAcceptance p) := by
  intro h
  obtain ⟨p₀, hp₀⟩ := hC
  obtain ⟨x, q, -, hx, hblock⟩ := I.exists_isBlockingPair_of_lt (h p₀ hp₀)
  have hxC : x ∉ C := fun hxC => absurd (h x hxC) (not_lt_of_ge hx)
  refine hμ x (μ q) ?_
  have hpx : ∀ r, J.propRank x r = I.propRank x r := fun r => by
    rw [propRank, propRank, hprop x hxC]
  have hrq : ∀ p, J.recvRank (μ q) p = I.recvRank (μ q) p := fun p => by
    rw [recvRank, recvRank, hrecv]
  obtain ⟨h1, h2⟩ := hblock
  refine ⟨?_, ?_⟩
  · rw [PropPrefers, hpx, hpx]
    exact h1
  · rw [RecvPrefers, hrq, hrq]
    exact h2

/-- Individual strategy-proofness of deferred acceptance for the proposers ([DubinsFreedman1981],
[Roth1982]): if proposer `p` reports the list `π` instead of its true list, then in every matching
that is stable for the reported instance, `p` gets a partner it does not truly prefer to its
deferred-acceptance partner under truthful reporting. -/
theorem propRank_deferredAcceptance_le_of_isStable_updatePropPref (p : Fin n)
    (π : Equiv.Perm (Fin n)) {μ : Matching n} (hμ : (I.updatePropPref p π).IsStable μ) :
    I.propRank p (I.deferredAcceptance p) ≤ I.propRank p (μ p) := by
  refine le_of_not_gt fun h => I.not_forall_mem_propRank_lt_of_isStable (J := I.updatePropPref p π)
    (C := {p}) rfl (fun q hq => Function.update_of_ne hq _ _) ⟨p, rfl⟩ hμ ?_
  rintro q rfl
  exact h

/-- Truthful reporting is a dominant strategy for each proposer under deferred acceptance
([DubinsFreedman1981]; [Roth1982], Theorem 5). -/
theorem propRank_deferredAcceptance_le_updatePropPref (p : Fin n) (π : Equiv.Perm (Fin n)) :
    I.propRank p (I.deferredAcceptance p) ≤
      I.propRank p ((I.updatePropPref p π).deferredAcceptance p) :=
  I.propRank_deferredAcceptance_le_of_isStable_updatePropPref p π (isStable_deferredAcceptance _)

end Cslib.Algorithms.Lean.StableMatching.Instance
