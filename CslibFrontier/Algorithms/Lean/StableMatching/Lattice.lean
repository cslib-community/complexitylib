/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.StableMatching.DeferredAcceptance
public import Mathlib.Order.Lattice
public import Mathlib.Order.BoundedOrder.Basic
public import Mathlib.Order.OrderDual
import Mathlib.Order.Basic

/-!
# The lattice of stable matchings

For two stable matchings `μ` and `ν`, letting every proposer take the better of its two partners
gives a stable matching `propJoin`, in which every receiver gets the worse of its two partners;
letting every proposer take the worse partner gives a stable matching `propMeet`. This is the
lattice theorem that [Knuth1976] attributes to J. H. Conway (see also [GusfieldIrving1989]).
We package it as a `DistribLattice` on the type `Instance.Stable I` of stable
matchings, ordered so that `μ ≤ ν` when every proposer weakly prefers `ν`, with `⊤` the
proposer-proposing and `⊥` the receiver-proposing deferred-acceptance matching.

## Main definitions

* `Instance.propJoin`, `Instance.propMeet`: proposer-wise best and worst of two stable matchings.
* `Instance.Stable`: the stable matchings of `I`, with `DistribLattice` and `BoundedOrder`
  instances.

## Main results

* `Instance.isStable_propJoin`, `Instance.propRank_propJoin`, `Instance.recvRank_propJoin`:
  `propJoin` is stable; proposers get the better and receivers the worse partner.
* `Instance.isStable_propMeet`, `Instance.propRank_propMeet`, `Instance.recvRank_propMeet`: the
  same for `propMeet`, with the roles reversed.
* `Instance.Stable.le_iff`, `Instance.Stable.coe_top`, `Instance.Stable.coe_bot`.

## References

* [Knuth1976]
* [GusfieldIrving1989]
-/

public section

namespace Cslib.Algorithms.Lean.StableMatching

namespace Instance

variable {n : ℕ} (I : Instance n)

/-- Each proposer takes the better of its partners in `μ` and `ν` (as a function; it is a
matching when `μ` and `ν` are stable, see `propJoin`). -/
@[expose] def propBest (μ ν : Matching n) (p : Fin n) : Fin n :=
  if I.propRank p (μ p) ≤ I.propRank p (ν p) then μ p else ν p

theorem propRank_propBest (μ ν : Matching n) (p : Fin n) :
    I.propRank p (I.propBest μ ν p) = min (I.propRank p (μ p)) (I.propRank p (ν p)) := by
  unfold propBest
  split_ifs with h
  · exact (min_eq_left h).symm
  · exact (min_eq_right (le_of_not_ge h)).symm

theorem propBest_mem (μ ν : Matching n) (p : Fin n) :
    I.propBest μ ν p = μ p ∨ I.propBest μ ν p = ν p := by
  unfold propBest
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- Two distinct proposers cannot take the same receiver, one from each of two stable matchings,
when both weakly prefer it to their other partner. -/
private theorem propBest_cross {μ ν : Matching n} (hμ : I.IsStable μ) (hν : I.IsStable ν)
    {p q : Fin n} (hp : I.propRank p (μ p) ≤ I.propRank p (ν p))
    (hq : I.propRank q (ν q) ≤ I.propRank q (μ q)) (h : μ p = ν q) : p = q := by
  by_contra hpq
  have hpq' : ν p ≠ ν q := fun e => hpq (ν.injective e)
  have hqp' : μ q ≠ μ p := fun e => hpq (μ.injective e).symm
  have hp' : I.propRank p (μ p) < I.propRank p (ν p) :=
    lt_of_le_of_ne hp fun e => hpq' (h ▸ (I.propRank_injective p e).symm)
  have hq' : I.propRank q (ν q) < I.propRank q (μ q) :=
    lt_of_le_of_ne hq fun e => hqp' (h ▸ (I.propRank_injective q e).symm)
  have hνs : ν.symm (μ p) = q := by rw [h, Equiv.symm_apply_apply]
  have hμs : μ.symm (μ p) = p := Equiv.symm_apply_apply _ _
  rcases lt_or_gt_of_ne (fun e : I.recvRank (μ p) p = I.recvRank (μ p) q =>
      hpq (I.recvRank_injective (μ p) e)) with hr | hr
  · exact hν p (μ p) ⟨hp', hνs ▸ hr⟩
  · refine hμ q (μ p) ⟨?_, ?_⟩
    · rw [PropPrefers, h]
      exact hq'
    · rw [RecvPrefers, hμs]
      exact hr

/-- The proposer-wise best of two stable matchings is injective. -/
theorem propBest_injective {μ ν : Matching n} (hμ : I.IsStable μ) (hν : I.IsStable ν) :
    Function.Injective (I.propBest μ ν) := by
  intro p q h
  unfold propBest at h
  split_ifs at h with hp hq hq
  · exact μ.injective h
  · exact I.propBest_cross hμ hν hp (le_of_not_ge hq) h
  · exact (I.propBest_cross hμ hν hq (le_of_not_ge hp) h.symm).symm
  · exact ν.injective h

/-- The proposer-wise best of two stable matchings: each proposer takes the partner it prefers. -/
@[expose] def propJoin {μ ν : Matching n} (hμ : I.IsStable μ) (hν : I.IsStable ν) : Matching n :=
  permOfInjective (I.propBest μ ν) (I.propBest_injective hμ hν)

variable {I}

/-- In `propJoin`, every proposer gets the better of its two partners. -/
theorem propRank_propJoin {μ ν : Matching n} (hμ : I.IsStable μ) (hν : I.IsStable ν)
    (p : Fin n) :
    I.propRank p (I.propJoin hμ hν p) = min (I.propRank p (μ p)) (I.propRank p (ν p)) :=
  I.propRank_propBest μ ν p

/-- The proposer-wise best of two stable matchings is stable. -/
theorem isStable_propJoin {μ ν : Matching n} (hμ : I.IsStable μ) (hν : I.IsStable ν) :
    I.IsStable (I.propJoin hμ hν) := by
  rintro p r ⟨hp, hr⟩
  have hp' := hp
  rw [PropPrefers, propRank_propJoin, lt_min_iff] at hp'
  set q := (I.propJoin hμ hν).symm r
  have hq : I.propBest μ ν q = r := (I.propJoin hμ hν).apply_symm_apply r
  rcases I.propBest_mem μ ν q with h | h
  · rw [h] at hq
    refine hμ p r ⟨hp'.1, ?_⟩
    rw [RecvPrefers, ← hq, Equiv.symm_apply_apply, hq]
    exact hr
  · rw [h] at hq
    refine hν p r ⟨hp'.2, ?_⟩
    rw [RecvPrefers, ← hq, Equiv.symm_apply_apply, hq]
    exact hr

/-- In `propJoin`, every receiver gets the worse of its two partners. -/
theorem recvRank_propJoin {μ ν : Matching n} (hμ : I.IsStable μ) (hν : I.IsStable ν)
    (r : Fin n) :
    I.recvRank r ((I.propJoin hμ hν).symm r) =
      max (I.recvRank r (μ.symm r)) (I.recvRank r (ν.symm r)) := by
  have h1 : I.recvRank r (μ.symm r) ≤ I.recvRank r ((I.propJoin hμ hν).symm r) :=
    I.recvRank_le_of_propRank_le hμ (fun p => (propRank_propJoin hμ hν p).trans_le
      (min_le_left _ _)) r
  have h2 : I.recvRank r (ν.symm r) ≤ I.recvRank r ((I.propJoin hμ hν).symm r) :=
    I.recvRank_le_of_propRank_le hν (fun p => (propRank_propJoin hμ hν p).trans_le
      (min_le_right _ _)) r
  set q := (I.propJoin hμ hν).symm r
  have hq : I.propBest μ ν q = r := (I.propJoin hμ hν).apply_symm_apply r
  refine le_antisymm ?_ (max_le h1 h2)
  rcases I.propBest_mem μ ν q with h | h
  · have : μ.symm r = q := by rw [← hq, h, Equiv.symm_apply_apply]
    rw [← this]
    exact le_max_left _ _
  · have : ν.symm r = q := by rw [← hq, h, Equiv.symm_apply_apply]
    rw [← this]
    exact le_max_right _ _

variable (I) in
/-- The proposer-wise worst of two stable matchings: the receiver-wise best, computed in the
swapped market. -/
@[expose] def propMeet {μ ν : Matching n} (hμ : I.IsStable μ) (hν : I.IsStable ν) : Matching n :=
  (I.swap.propJoin ((I.isStable_swap_iff μ).2 hμ) ((I.isStable_swap_iff ν).2 hν)).symm

/-- The proposer-wise worst of two stable matchings is stable. -/
theorem isStable_propMeet {μ ν : Matching n} (hμ : I.IsStable μ) (hν : I.IsStable ν) :
    I.IsStable (I.propMeet hμ hν) :=
  (I.isStable_swap_iff (I.propMeet hμ hν)).1
    (isStable_propJoin ((I.isStable_swap_iff μ).2 hμ) ((I.isStable_swap_iff ν).2 hν))

/-- In `propMeet`, every proposer gets the worse of its two partners. -/
theorem propRank_propMeet {μ ν : Matching n} (hμ : I.IsStable μ) (hν : I.IsStable ν)
    (p : Fin n) :
    I.propRank p (I.propMeet hμ hν p) = max (I.propRank p (μ p)) (I.propRank p (ν p)) := by
  have h := recvRank_propJoin ((I.isStable_swap_iff μ).2 hμ) ((I.isStable_swap_iff ν).2 hν) p
  simp only [swap_recvRank, Equiv.symm_symm] at h
  exact h

/-- In `propMeet`, every receiver gets the better of its two partners. -/
theorem recvRank_propMeet {μ ν : Matching n} (hμ : I.IsStable μ) (hν : I.IsStable ν)
    (r : Fin n) :
    I.recvRank r ((I.propMeet hμ hν).symm r) =
      min (I.recvRank r (μ.symm r)) (I.recvRank r (ν.symm r)) := by
  have h := propRank_propJoin ((I.isStable_swap_iff μ).2 hμ) ((I.isStable_swap_iff ν).2 hν) r
  simp only [swap_propRank] at h
  rw [propMeet, Equiv.symm_symm]
  exact h


variable (I) in
/-- The stable matchings of `I`. They form a finite distributive lattice, ordered so that `μ ≤ ν`
when every proposer weakly prefers its partner in `ν` (`Stable.le_iff`). -/
@[expose] def Stable : Type := {μ : Matching n // I.IsStable μ}

namespace Stable

instance : Fintype I.Stable := inferInstanceAs (Fintype {μ : Matching n // I.IsStable μ})

instance : DecidableEq I.Stable := inferInstanceAs (DecidableEq {μ : Matching n // I.IsStable μ})

/-- The proposers' ranks of their partners, in the order dual to `Fin n` (so that a better partner
is larger). The order on `I.Stable` is pulled back along this injective map. -/
@[expose] def propRanks (μ : I.Stable) : Fin n → (Fin n)ᵒᵈ :=
  fun p => OrderDual.toDual (I.propRank p (μ.1 p))

theorem propRanks_injective : Function.Injective (propRanks (I := I)) := by
  intro μ ν h
  refine Subtype.ext (Equiv.ext fun p => ?_)
  exact I.propRank_injective p (OrderDual.toDual.injective (congrFun h p))

instance : LE I.Stable := ⟨fun μ ν => μ.propRanks ≤ ν.propRanks⟩

instance : LT I.Stable := ⟨fun μ ν => μ.propRanks < ν.propRanks⟩

instance : Max I.Stable := ⟨fun μ ν => ⟨I.propJoin μ.2 ν.2, isStable_propJoin μ.2 ν.2⟩⟩

instance : Min I.Stable := ⟨fun μ ν => ⟨I.propMeet μ.2 ν.2, isStable_propMeet μ.2 ν.2⟩⟩

@[simp] theorem coe_sup (μ ν : I.Stable) : (μ ⊔ ν).1 = I.propJoin μ.2 ν.2 := rfl

@[simp] theorem coe_inf (μ ν : I.Stable) : (μ ⊓ ν).1 = I.propMeet μ.2 ν.2 := rfl

/-- `μ ≤ ν` exactly when every proposer weakly prefers its partner in `ν`. -/
theorem le_iff {μ ν : I.Stable} :
    μ ≤ ν ↔ ∀ p, I.propRank p (ν.1 p) ≤ I.propRank p (μ.1 p) :=
  Pi.le_def

/-- The lattice of stable matchings is distributive (Conway, reported in [Knuth1976]). -/
instance : DistribLattice I.Stable :=
  Function.Injective.distribLattice propRanks propRanks_injective Iff.rfl Iff.rfl
    (fun μ ν => funext fun p => by
      simp only [propRanks, coe_sup, propRank_propJoin]
      rfl)
    (fun μ ν => funext fun p => by
      simp only [propRanks, coe_inf, propRank_propMeet]
      rfl)

instance : BoundedOrder I.Stable where
  top := ⟨I.deferredAcceptance, I.isStable_deferredAcceptance⟩
  le_top μ := le_iff.2 fun p => I.propRank_deferredAcceptance_le μ.2 p
  bot := ⟨I.receiverDeferredAcceptance, I.isStable_receiverDeferredAcceptance⟩
  bot_le μ := le_iff.2 fun p => I.isProposerPessimal_receiverDeferredAcceptance.2 μ.1 μ.2 p

/-- The top stable matching is proposer-proposing deferred acceptance. -/
@[simp] theorem coe_top : (⊤ : I.Stable).1 = I.deferredAcceptance := rfl

/-- The bottom stable matching is receiver-proposing deferred acceptance. -/
@[simp] theorem coe_bot : (⊥ : I.Stable).1 = I.receiverDeferredAcceptance := rfl

end Stable

end Instance

end Cslib.Algorithms.Lean.StableMatching
