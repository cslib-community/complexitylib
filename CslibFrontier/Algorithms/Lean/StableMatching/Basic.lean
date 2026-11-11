/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Data.Fintype.Inv
public import Mathlib.Data.Fintype.Perm

/-!
# Stable matchings

This module sets up the one-to-one two-sided matching model of [GaleShapley1962]: `n` proposers
and `n` receivers, both indexed by `Fin n`, each with a strict and complete preference order over
the other side. A matching pairs proposer `p` with receiver `μ p` for a permutation `μ`, so every
matching is perfect. A pair `(p, r)` blocks `μ` when each strictly prefers the other to its partner
in `μ`; a matching is stable when no pair blocks it.

Preferences are permutations listing agents from most to least preferred: `propPref p k` is
proposer `p`'s `k`-th choice, with rank `0` the favourite, and `recvPref r k` likewise. Ranks are
read off the inverse permutation (`propRank`, `recvRank`), so a smaller rank is better.

## Main definitions

* `Cslib.Algorithms.Lean.StableMatching.Instance`: a two-sided market with strict complete
  preferences.
* `Instance.IsBlockingPair`, `Instance.IsStable`: blocking pairs and stability.
* `Instance.swap`: the market with the roles of the two sides exchanged.
* `Instance.updatePropPref`, `Instance.updateRecvPref`: one agent misreports its list.
* `Instance.IsProposerOptimal`, `Instance.IsReceiverPessimal`: a stable matching that every
  proposer weakly prefers to every other stable matching, and one that every receiver weakly
  dislikes relative to every other stable matching; `Instance.IsReceiverOptimal` and
  `Instance.IsProposerPessimal` are the same notions with the sides exchanged.
* `Cslib.Algorithms.Lean.StableMatching.permOfInjective`: a computable permutation from an
  injective self-map of `Fin n`, used for computed matchings and concrete preference lists.

## Main results

* `Instance.isStable_swap_iff`: `μ.symm` is stable for the swapped market iff `μ` is stable.
* `Instance.recvRank_le_of_propRank_le`, `Instance.propRank_le_of_recvRank_le`: opposing
  interests; if every proposer weakly prefers `μ` to a stable matching `ν`, then every receiver
  weakly prefers `ν` to `μ`, and symmetrically.
* `Instance.IsProposerOptimal.isReceiverPessimal`, `Instance.IsProposerOptimal.unique`,
  `Instance.isReceiverOptimal_iff_swap`.

## References

* [GaleShapley1962]
* [McVitieWilson1971]
* [GusfieldIrving1989]
-/

public section

namespace Cslib.Algorithms.Lean.StableMatching

/-- A one-to-one two-sided market with `n` proposers and `n` receivers, both indexed by `Fin n`.
`propPref p k` is proposer `p`'s `k`-th choice and `recvPref r k` is receiver `r`'s `k`-th choice
(rank `0` is the most preferred). Preferences are strict and complete. -/
structure Instance (n : ℕ) where
  /-- Proposer `p`'s preference list, from most to least preferred receiver. -/
  propPref : Fin n → Equiv.Perm (Fin n)
  /-- Receiver `r`'s preference list, from most to least preferred proposer. -/
  recvPref : Fin n → Equiv.Perm (Fin n)

/-- A matching pairs proposer `p` with receiver `μ p`; `μ.symm r` is receiver `r`'s partner. -/
abbrev Matching (n : ℕ) := Equiv.Perm (Fin n)

/-- A computable permutation from an injective self-map of `Fin n`. For a concrete map the
injectivity proof defaults to `decide`, so `permOfInjective ![2, 0, 1]` lists the agents `2, 0, 1`
in order. -/
@[expose] def permOfInjective {n : ℕ} (f : Fin n → Fin n)
    (hf : Function.Injective f := by decide) :
    Equiv.Perm (Fin n) where
  toFun := f
  invFun := Fintype.bijInv (Finite.injective_iff_bijective.1 hf)
  left_inv := Fintype.leftInverse_bijInv _
  right_inv := Fintype.rightInverse_bijInv _

@[simp] theorem permOfInjective_apply {n : ℕ} (f : Fin n → Fin n) (hf : Function.Injective f)
    (i : Fin n) : permOfInjective f hf i = f i := rfl

namespace Instance

variable {n : ℕ} (I : Instance n)

/-- The rank of receiver `r` in proposer `p`'s list (`0` is the favourite). -/
@[expose] def propRank (p r : Fin n) : Fin n := (I.propPref p).symm r

/-- The rank of proposer `p` in receiver `r`'s list (`0` is the favourite). -/
@[expose] def recvRank (r p : Fin n) : Fin n := (I.recvPref r).symm p

/-- Proposer `p` strictly prefers receiver `r` to receiver `r'`. -/
@[expose] def PropPrefers (p r r' : Fin n) : Prop := I.propRank p r < I.propRank p r'

/-- Receiver `r` strictly prefers proposer `p` to proposer `p'`. -/
@[expose] def RecvPrefers (r p p' : Fin n) : Prop := I.recvRank r p < I.recvRank r p'

instance (p r r' : Fin n) : Decidable (I.PropPrefers p r r') :=
  inferInstanceAs (Decidable (_ < _))

instance (r p p' : Fin n) : Decidable (I.RecvPrefers r p p') :=
  inferInstanceAs (Decidable (_ < _))

/-- `(p, r)` blocks `μ` when `p` strictly prefers `r` to `μ p` and `r` strictly prefers `p` to its
partner `μ.symm r`. -/
@[expose] def IsBlockingPair (μ : Matching n) (p r : Fin n) : Prop :=
  I.PropPrefers p r (μ p) ∧ I.RecvPrefers r p (μ.symm r)

/-- A matching is stable when no pair blocks it. -/
@[expose] def IsStable (μ : Matching n) : Prop := ∀ p r, ¬ I.IsBlockingPair μ p r

instance (μ : Matching n) (p r : Fin n) : Decidable (I.IsBlockingPair μ p r) :=
  inferInstanceAs (Decidable (_ ∧ _))

instance (μ : Matching n) : Decidable (I.IsStable μ) :=
  inferInstanceAs (Decidable (∀ _, _))

theorem propPref_propRank (p r : Fin n) : I.propPref p (I.propRank p r) = r :=
  (I.propPref p).apply_symm_apply r

theorem propRank_propPref (p k : Fin n) : I.propRank p (I.propPref p k) = k :=
  (I.propPref p).symm_apply_apply k

theorem propRank_injective (p : Fin n) : Function.Injective (I.propRank p) :=
  (I.propPref p).symm.injective

theorem recvRank_injective (r : Fin n) : Function.Injective (I.recvRank r) :=
  (I.recvPref r).symm.injective

theorem isBlockingPair_iff (μ : Matching n) (p r : Fin n) :
    I.IsBlockingPair μ p r ↔
      I.propRank p r < I.propRank p (μ p) ∧ I.recvRank r p < I.recvRank r (μ.symm r) :=
  Iff.rfl

variable {I} in
/-- In a stable matching, a receiver that `p` strictly prefers to its partner strictly prefers its
own partner to `p`. -/
theorem IsStable.recvRank_lt {μ : Matching n} (hμ : I.IsStable μ) {p r : Fin n}
    (hp : I.propRank p r < I.propRank p (μ p)) : I.recvRank r (μ.symm r) < I.recvRank r p := by
  rcases lt_trichotomy (I.recvRank r (μ.symm r)) (I.recvRank r p) with h | h | h
  · exact h
  · have hrp : μ.symm r = p := I.recvRank_injective r h
    rw [← hrp, Equiv.apply_symm_apply] at hp
    exact absurd hp (lt_irrefl _)
  · exact absurd ⟨hp, h⟩ (hμ p r)

/-! ### Exchanging the two sides -/

/-- The market with the roles of proposers and receivers exchanged. -/
@[expose] def swap : Instance n := ⟨I.recvPref, I.propPref⟩

@[simp] theorem swap_swap : I.swap.swap = I := rfl

@[simp] theorem swap_propRank (r p : Fin n) : I.swap.propRank r p = I.recvRank r p := rfl

@[simp] theorem swap_recvRank (p r : Fin n) : I.swap.recvRank p r = I.propRank p r := rfl

theorem isBlockingPair_swap (μ : Matching n) (p r : Fin n) :
    I.swap.IsBlockingPair μ.symm r p ↔ I.IsBlockingPair μ p r := by
  simp only [isBlockingPair_iff, swap_propRank, swap_recvRank, Equiv.symm_symm]
  exact and_comm

/-- `μ.symm` is stable for the swapped market exactly when `μ` is stable. -/
theorem isStable_swap_iff (μ : Matching n) : I.swap.IsStable μ.symm ↔ I.IsStable μ := by
  simp only [IsStable, ← I.isBlockingPair_swap μ]
  exact forall_comm

/-! ### Misreports -/

/-- The instance in which proposer `p` reports the list `π` and everyone else reports truthfully. -/
@[expose] def updatePropPref (p : Fin n) (π : Equiv.Perm (Fin n)) : Instance n :=
  ⟨Function.update I.propPref p π, I.recvPref⟩

/-- The instance in which receiver `r` reports the list `π` and everyone else reports truthfully. -/
@[expose] def updateRecvPref (r : Fin n) (π : Equiv.Perm (Fin n)) : Instance n :=
  ⟨I.propPref, Function.update I.recvPref r π⟩

/-- A receiver's misreport is a proposer's misreport in the swapped market. -/
theorem swap_updateRecvPref (r : Fin n) (π : Equiv.Perm (Fin n)) :
    (I.updateRecvPref r π).swap = I.swap.updatePropPref r π := rfl

/-! ### Optimal and pessimal stable matchings -/

/-- A stable matching that every proposer weakly prefers to every stable matching. -/
@[expose] def IsProposerOptimal (μ : Matching n) : Prop :=
  I.IsStable μ ∧ ∀ ν, I.IsStable ν → ∀ p, I.propRank p (μ p) ≤ I.propRank p (ν p)

/-- A stable matching that every proposer weakly dislikes relative to every stable matching. -/
@[expose] def IsProposerPessimal (μ : Matching n) : Prop :=
  I.IsStable μ ∧ ∀ ν, I.IsStable ν → ∀ p, I.propRank p (ν p) ≤ I.propRank p (μ p)

/-- A stable matching that every receiver weakly prefers to every stable matching. -/
@[expose] def IsReceiverOptimal (μ : Matching n) : Prop :=
  I.IsStable μ ∧ ∀ ν, I.IsStable ν → ∀ r, I.recvRank r (μ.symm r) ≤ I.recvRank r (ν.symm r)

/-- A stable matching that every receiver weakly dislikes relative to every stable matching. -/
@[expose] def IsReceiverPessimal (μ : Matching n) : Prop :=
  I.IsStable μ ∧ ∀ ν, I.IsStable ν → ∀ r, I.recvRank r (ν.symm r) ≤ I.recvRank r (μ.symm r)

/-- Opposing interests (see [GusfieldIrving1989]): if every proposer weakly prefers `μ` to the
stable matching `ν`, then every receiver weakly prefers `ν` to `μ`. -/
theorem recvRank_le_of_propRank_le {μ ν : Matching n} (hν : I.IsStable ν)
    (h : ∀ p, I.propRank p (μ p) ≤ I.propRank p (ν p)) (r : Fin n) :
    I.recvRank r (ν.symm r) ≤ I.recvRank r (μ.symm r) := by
  by_contra hlt
  push Not at hlt
  set q := μ.symm r
  have hμq : μ q = r := μ.apply_symm_apply r
  have hne : ν q ≠ r := by grind
  have hlt' : I.propRank q r < I.propRank q (ν q) := by
    refine lt_of_le_of_ne (hμq ▸ h q) fun heq => hne ?_
    exact (I.propRank_injective q heq).symm
  exact hν q r ⟨hlt', hlt⟩

/-- The symmetric form: if every receiver weakly prefers `μ` to the stable matching `ν`, then every
proposer weakly prefers `ν` to `μ`. -/
theorem propRank_le_of_recvRank_le {μ ν : Matching n} (hν : I.IsStable ν)
    (h : ∀ r, I.recvRank r (μ.symm r) ≤ I.recvRank r (ν.symm r)) (p : Fin n) :
    I.propRank p (ν p) ≤ I.propRank p (μ p) :=
  I.swap.recvRank_le_of_propRank_le ((I.isStable_swap_iff ν).2 hν) h p

variable {I} in
theorem IsProposerOptimal.isReceiverPessimal {μ : Matching n} (h : I.IsProposerOptimal μ) :
    I.IsReceiverPessimal μ :=
  ⟨h.1, fun ν hν r => I.recvRank_le_of_propRank_le hν (h.2 ν hν) r⟩

variable {I} in
theorem IsReceiverOptimal.isProposerPessimal {μ : Matching n} (h : I.IsReceiverOptimal μ) :
    I.IsProposerPessimal μ :=
  ⟨h.1, fun ν hν p => I.propRank_le_of_recvRank_le hν (h.2 ν hν) p⟩

theorem isReceiverOptimal_iff_swap (μ : Matching n) :
    I.IsReceiverOptimal μ ↔ I.swap.IsProposerOptimal μ.symm := by
  constructor
  · rintro ⟨hμ, h⟩
    refine ⟨(I.isStable_swap_iff μ).2 hμ, fun ν hν r => ?_⟩
    have := h ν.symm ((I.swap.isStable_swap_iff ν).2 hν) r
    rw [Equiv.symm_symm] at this
    exact this
  · rintro ⟨hμ, h⟩
    exact ⟨(I.isStable_swap_iff μ).1 hμ, fun ν hν r => h ν.symm ((I.isStable_swap_iff ν).2 hν) r⟩

variable {I} in
/-- There is at most one proposer-optimal stable matching. -/
theorem IsProposerOptimal.unique {μ ν : Matching n} (hμ : I.IsProposerOptimal μ)
    (hν : I.IsProposerOptimal ν) : μ = ν := by
  ext p
  exact congrArg Fin.val (I.propRank_injective p (le_antisymm (hμ.2 ν hν.1 p) (hν.2 μ hμ.1 p)))

end Instance

end Cslib.Algorithms.Lean.StableMatching
