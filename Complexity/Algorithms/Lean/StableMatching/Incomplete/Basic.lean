/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Basic.PEquiv
public import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.Basic

/-!
# Stable matchings with incomplete preference lists

This module sets up the one-to-one two-sided matching model with unacceptable partners (the
marriage model of [RothSotomayor1990], Chapter 2): `m` proposers indexed by `Fin m` and `n`
receivers indexed by `Fin n`, the two sides possibly of different sizes. Each agent lists the
agents of the other side that it finds acceptable, from most to least preferred; an agent
prefers every acceptable partner to staying unmatched, and staying unmatched to every
unacceptable partner. A matching is partial: a partial bijection `Fin m ≃. Fin n`, under which
an agent may be unmatched.

A matching is individually rational when every matched agent finds its partner acceptable. A
pair `(p, r)` blocks it when each strictly prefers the other to its outcome in the matching
(being unmatched included); a matching is stable when it is individually rational and has no
blocking pair. Gusfield and Irving treat this setting as stable marriage with incomplete lists
([GusfieldIrving1989], Section 1.4).

Preferences are lists `propPref p : List (Fin n)` and `recvPref r : List (Fin m)`. An outcome
`o : Option (Fin n)` of proposer `p` has rank `propRank p o`: the position of the receiver in
`p`'s list, and the length of the list for `none` or an unlisted receiver. A smaller rank is
better, so every acceptable receiver beats being unmatched. Ranks use the first occurrence of an
agent in a list, so a list with repetitions is equivalent to the list with them removed.

The complete-list model `Instance n` of `Complexity.Algorithms.Lean.StableMatching.Basic` is the
special case of equal sides and complete lists (see
`Complexity.Algorithms.Lean.StableMatching.Incomplete.Complete`).

## Main definitions

* `Cslib.Algorithms.Lean.StableMatching.IncompleteInstance`: a two-sided market with strict,
  possibly incomplete preference lists.
* `Cslib.Algorithms.Lean.StableMatching.PartialMatching`: a partial matching `Fin m ≃. Fin n`;
  `PartialMatching.matchedProposers`, `PartialMatching.matchedReceivers`: its matched agents.
* `IncompleteInstance.propRank`, `IncompleteInstance.recvRank`: ranks of outcomes, with
  `none` ranked below every acceptable partner.
* `IncompleteInstance.IsIndividuallyRational`, `IncompleteInstance.IsBlockingPair`,
  `IncompleteInstance.IsStable`: individual rationality, blocking pairs and stability.
* `IncompleteInstance.swap`: the market with the roles of the two sides exchanged.
* `IncompleteInstance.IsProposerOptimal`, `IncompleteInstance.IsReceiverPessimal` and their
  duals `IncompleteInstance.IsReceiverOptimal`, `IncompleteInstance.IsProposerPessimal`.

## Main results

* `IncompleteInstance.isStable_swap_iff`: `μ.symm` is stable for the swapped market iff `μ` is
  stable.
* `IncompleteInstance.recvRank_le_of_propRank_le`: opposing interests (a form of
  [RothSotomayor1990], Theorem 2.13); if every proposer weakly prefers the individually rational
  matching `μ` to the stable matching `ν`, then every receiver weakly prefers `ν` to `μ`.
* `IncompleteInstance.IsProposerOptimal.unique`: there is at most one proposer-optimal stable
  matching.
* `PartialMatching.card_matchedReceivers`: a matching matches as many receivers as proposers.

## References

* [GusfieldIrving1989]
* [RothSotomayor1990]
-/

public section

namespace Cslib.Algorithms.Lean.StableMatching

/-- A one-to-one two-sided market with `m` proposers and `n` receivers whose preference lists may
be incomplete. `propPref p` lists the receivers acceptable to proposer `p`, from most to least
preferred, and `recvPref r` lists the proposers acceptable to receiver `r`. An agent that does
not appear in a list is unacceptable: the list's owner prefers staying unmatched to it. -/
structure IncompleteInstance (m n : ℕ) where
  /-- Proposer `p`'s acceptable receivers, from most to least preferred. -/
  propPref : Fin m → List (Fin n)
  /-- Receiver `r`'s acceptable proposers, from most to least preferred. -/
  recvPref : Fin n → List (Fin m)

/-- A matching that may leave agents unmatched: proposer `p` is matched to receiver `r` when
`μ p = some r` (equivalently `μ.symm r = some p`), and unmatched when `μ p = none`. -/
abbrev PartialMatching (m n : ℕ) := Fin m ≃. Fin n

namespace PartialMatching

variable {m n : ℕ}

/-- The proposers that `μ` matches. -/
@[expose] def matchedProposers (μ : PartialMatching m n) : Finset (Fin m) :=
  Finset.univ.filter fun p => (μ p).isSome

/-- The receivers that `μ` matches. -/
@[expose] def matchedReceivers (μ : PartialMatching m n) : Finset (Fin n) :=
  Finset.univ.filter fun r => (μ.symm r).isSome

theorem mem_matchedProposers {μ : PartialMatching m n} {p : Fin m} :
    p ∈ matchedProposers μ ↔ (μ p).isSome := by
  simp only [matchedProposers, Finset.mem_filter, Finset.mem_univ, true_and]

theorem mem_matchedReceivers {μ : PartialMatching m n} {r : Fin n} :
    r ∈ matchedReceivers μ ↔ (μ.symm r).isSome := by
  simp only [matchedReceivers, Finset.mem_filter, Finset.mem_univ, true_and]

/-- The receivers matched by `μ` are the partners of the proposers matched by `μ`. -/
theorem matchedReceivers_eq_image (μ : PartialMatching m n) :
    matchedReceivers μ =
      (matchedProposers μ).attach.image fun p => (μ p.1).get (mem_matchedProposers.1 p.2) := by
  ext r
  simp only [Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists, mem_matchedReceivers]
  constructor
  · intro h
    obtain ⟨p, hp⟩ := Option.isSome_iff_exists.1 h
    have hμ : μ p = some r := μ.eq_some_iff.1 hp
    exact ⟨p, mem_matchedProposers.2 (by rw [hμ]; rfl), by simp only [hμ, Option.get_some]⟩
  · rintro ⟨p, hp, rfl⟩
    rw [Option.isSome_iff_exists]
    exact ⟨p, μ.eq_some_iff.2 (Option.some_get _).symm⟩

/-- A matching matches as many proposers as receivers. -/
theorem card_matchedReceivers (μ : PartialMatching m n) :
    (matchedReceivers μ).card = (matchedProposers μ).card := by
  rw [matchedReceivers_eq_image, Finset.card_image_of_injective, Finset.card_attach]
  rintro ⟨p, hp⟩ ⟨q, hq⟩ h
  simp only at h
  refine Subtype.ext (μ.inj (b := (μ p).get (mem_matchedProposers.1 hp)) ?_ ?_)
  · exact Option.get_mem _
  · rw [h]; exact Option.get_mem _

end PartialMatching

namespace IncompleteInstance

variable {m n : ℕ} (I : IncompleteInstance m n)

/-- The rank of outcome `o` for proposer `p`: the position of the receiver in `p`'s list, and the
length of the list when `o = none` or the receiver is unacceptable. A smaller rank is better. -/
@[expose] def propRank (p : Fin m) (o : Option (Fin n)) : ℕ :=
  match o with
  | some r => (I.propPref p).idxOf r
  | none => (I.propPref p).length

/-- The rank of outcome `o` for receiver `r`: the position of the proposer in `r`'s list, and the
length of the list when `o = none` or the proposer is unacceptable. A smaller rank is better. -/
@[expose] def recvRank (r : Fin n) (o : Option (Fin m)) : ℕ :=
  match o with
  | some p => (I.recvPref r).idxOf p
  | none => (I.recvPref r).length

@[simp] theorem propRank_some (p : Fin m) (r : Fin n) :
    I.propRank p (some r) = (I.propPref p).idxOf r := rfl

@[simp] theorem propRank_none (p : Fin m) : I.propRank p none = (I.propPref p).length := rfl

@[simp] theorem recvRank_some (r : Fin n) (p : Fin m) :
    I.recvRank r (some p) = (I.recvPref r).idxOf p := rfl

@[simp] theorem recvRank_none (r : Fin n) : I.recvRank r none = (I.recvPref r).length := rfl

/-- Every outcome is ranked no worse than being unmatched. -/
theorem propRank_le_propRank_none (p : Fin m) (o : Option (Fin n)) :
    I.propRank p o ≤ I.propRank p none := by
  cases o with
  | none => exact le_rfl
  | some r => exact List.idxOf_le_length

/-- Every outcome is ranked no worse than being unmatched. -/
theorem recvRank_le_recvRank_none (r : Fin n) (o : Option (Fin m)) :
    I.recvRank r o ≤ I.recvRank r none := by
  cases o with
  | none => exact le_rfl
  | some p => exact List.idxOf_le_length

/-- Proposer `p` strictly prefers receiver `r` to being unmatched exactly when `r` is on its
list. -/
theorem propRank_some_lt_none_iff (p : Fin m) (r : Fin n) :
    I.propRank p (some r) < I.propRank p none ↔ r ∈ I.propPref p :=
  List.idxOf_lt_length_iff

/-- Receiver `r` strictly prefers proposer `p` to being unmatched exactly when `p` is on its
list. -/
theorem recvRank_some_lt_none_iff (r : Fin n) (p : Fin m) :
    I.recvRank r (some p) < I.recvRank r none ↔ p ∈ I.recvPref r :=
  List.idxOf_lt_length_iff

/-- Ranks are strict on acceptable outcomes: an acceptable receiver has the same rank as an outcome
only if the outcome is that receiver. -/
theorem eq_of_propRank_eq {p : Fin m} {r : Fin n} (hr : r ∈ I.propPref p) {o : Option (Fin n)}
    (h : I.propRank p (some r) = I.propRank p o) : o = some r := by
  cases o with
  | none =>
    have := (I.propRank_some_lt_none_iff p r).2 hr
    omega
  | some r' => exact congrArg some ((List.idxOf_inj hr).1 h).symm

/-- Ranks are strict on acceptable outcomes: an acceptable proposer has the same rank as an outcome
only if the outcome is that proposer. -/
theorem eq_of_recvRank_eq {r : Fin n} {p : Fin m} (hp : p ∈ I.recvPref r) {o : Option (Fin m)}
    (h : I.recvRank r (some p) = I.recvRank r o) : o = some p := by
  cases o with
  | none =>
    have := (I.recvRank_some_lt_none_iff r p).2 hp
    omega
  | some p' => exact congrArg some ((List.idxOf_inj hp).1 h).symm

/-! ### Stability -/

/-- A matching is individually rational when every matched agent finds its partner acceptable. -/
@[expose] def IsIndividuallyRational (μ : PartialMatching m n) : Prop :=
  ∀ p r, μ p = some r → r ∈ I.propPref p ∧ p ∈ I.recvPref r

/-- The pair `(p, r)` blocks `μ` when `p` strictly prefers `r` to its outcome in `μ` and `r`
strictly prefers `p` to its outcome in `μ`. Since being unmatched is ranked below every acceptable
partner, `p` and `r` then find each other acceptable. -/
@[expose] def IsBlockingPair (μ : PartialMatching m n) (p : Fin m) (r : Fin n) : Prop :=
  I.propRank p (some r) < I.propRank p (μ p) ∧ I.recvRank r (some p) < I.recvRank r (μ.symm r)

/-- A matching is stable when it is individually rational and no pair blocks it. -/
@[expose] def IsStable (μ : PartialMatching m n) : Prop :=
  I.IsIndividuallyRational μ ∧ ∀ p r, ¬ I.IsBlockingPair μ p r

instance (μ : PartialMatching m n) : Decidable (I.IsIndividuallyRational μ) :=
  inferInstanceAs (Decidable (∀ _ _, _))

instance (μ : PartialMatching m n) (p : Fin m) (r : Fin n) :
    Decidable (I.IsBlockingPair μ p r) :=
  inferInstanceAs (Decidable (_ ∧ _))

instance (μ : PartialMatching m n) : Decidable (I.IsStable μ) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- In a blocking pair, the receiver finds the proposer acceptable. -/
theorem IsBlockingPair.mem_recvPref {μ : PartialMatching m n} {p : Fin m} {r : Fin n}
    (h : I.IsBlockingPair μ p r) : p ∈ I.recvPref r :=
  (I.recvRank_some_lt_none_iff r p).1 (lt_of_lt_of_le h.2 (I.recvRank_le_recvRank_none r _))

/-- In a blocking pair, the proposer finds the receiver acceptable. -/
theorem IsBlockingPair.mem_propPref {μ : PartialMatching m n} {p : Fin m} {r : Fin n}
    (h : I.IsBlockingPair μ p r) : r ∈ I.propPref p :=
  (I.propRank_some_lt_none_iff p r).1 (lt_of_lt_of_le h.1 (I.propRank_le_propRank_none p _))

/-! ### Exchanging the two sides -/

/-- The market with the roles of proposers and receivers exchanged. -/
@[expose] def swap : IncompleteInstance n m := ⟨I.recvPref, I.propPref⟩

@[simp] theorem swap_propPref : I.swap.propPref = I.recvPref := rfl

@[simp] theorem swap_recvPref : I.swap.recvPref = I.propPref := rfl

@[simp] theorem swap_swap : I.swap.swap = I := rfl

@[simp] theorem swap_propRank : I.swap.propRank = I.recvRank := rfl

@[simp] theorem swap_recvRank : I.swap.recvRank = I.propRank := rfl

theorem isIndividuallyRational_swap_iff (μ : PartialMatching m n) :
    I.swap.IsIndividuallyRational μ.symm ↔ I.IsIndividuallyRational μ := by
  simp only [IsIndividuallyRational, swap_propPref, swap_recvPref, PEquiv.eq_some_iff]
  constructor
  · intro h p r hpr
    exact (h r p hpr).symm
  · intro h r p hrp
    exact (h p r hrp).symm

theorem isBlockingPair_swap_iff (μ : PartialMatching m n) (p : Fin m) (r : Fin n) :
    I.swap.IsBlockingPair μ.symm r p ↔ I.IsBlockingPair μ p r := by
  simp only [IsBlockingPair, swap_propRank, swap_recvRank, PEquiv.symm_symm]
  exact and_comm

/-- `μ.symm` is stable for the swapped market exactly when `μ` is stable. -/
theorem isStable_swap_iff (μ : PartialMatching m n) : I.swap.IsStable μ.symm ↔ I.IsStable μ := by
  rw [IsStable, IsStable, isIndividuallyRational_swap_iff]
  simp only [← I.isBlockingPair_swap_iff μ]
  exact and_congr_right fun _ => forall_comm

/-! ### Optimal and pessimal stable matchings -/

/-- A stable matching that every proposer weakly prefers to every stable matching. -/
@[expose] def IsProposerOptimal (μ : PartialMatching m n) : Prop :=
  I.IsStable μ ∧ ∀ ν, I.IsStable ν → ∀ p, I.propRank p (μ p) ≤ I.propRank p (ν p)

/-- A stable matching that every proposer weakly dislikes relative to every stable matching. -/
@[expose] def IsProposerPessimal (μ : PartialMatching m n) : Prop :=
  I.IsStable μ ∧ ∀ ν, I.IsStable ν → ∀ p, I.propRank p (ν p) ≤ I.propRank p (μ p)

/-- A stable matching that every receiver weakly prefers to every stable matching. -/
@[expose] def IsReceiverOptimal (μ : PartialMatching m n) : Prop :=
  I.IsStable μ ∧ ∀ ν, I.IsStable ν → ∀ r, I.recvRank r (μ.symm r) ≤ I.recvRank r (ν.symm r)

/-- A stable matching that every receiver weakly dislikes relative to every stable matching. -/
@[expose] def IsReceiverPessimal (μ : PartialMatching m n) : Prop :=
  I.IsStable μ ∧ ∀ ν, I.IsStable ν → ∀ r, I.recvRank r (ν.symm r) ≤ I.recvRank r (μ.symm r)

/-- Opposing interests (a form of [RothSotomayor1990], Theorem 2.13, which Roth and Sotomayor
attribute to Knuth): if every proposer weakly prefers the individually rational matching `μ` to the
stable matching `ν`, then every receiver weakly prefers `ν` to `μ`. -/
theorem recvRank_le_of_propRank_le {μ ν : PartialMatching m n} (hμ : I.IsIndividuallyRational μ)
    (hν : I.IsStable ν) (h : ∀ p, I.propRank p (μ p) ≤ I.propRank p (ν p)) (r : Fin n) :
    I.recvRank r (ν.symm r) ≤ I.recvRank r (μ.symm r) := by
  by_contra hlt
  push Not at hlt
  cases hq : μ.symm r with
  | none =>
    rw [hq] at hlt
    exact absurd hlt (not_lt.2 (I.recvRank_le_recvRank_none r _))
  | some q =>
    rw [hq] at hlt
    have hμq : μ q = some r := μ.eq_some_iff.1 hq
    have hacc := hμ q r hμq
    refine hν.2 q r ⟨lt_of_le_of_ne (hμq ▸ h q) fun heq => ?_, hlt⟩
    have hνq : ν q = some r := I.eq_of_propRank_eq hacc.1 heq
    rw [ν.eq_some_iff.2 hνq] at hlt
    exact lt_irrefl _ hlt

/-- The symmetric form: if every receiver weakly prefers the individually rational matching `μ` to
the stable matching `ν`, then every proposer weakly prefers `ν` to `μ`. -/
theorem propRank_le_of_recvRank_le {μ ν : PartialMatching m n} (hμ : I.IsIndividuallyRational μ)
    (hν : I.IsStable ν) (h : ∀ r, I.recvRank r (μ.symm r) ≤ I.recvRank r (ν.symm r)) (p : Fin m) :
    I.propRank p (ν p) ≤ I.propRank p (μ p) :=
  I.swap.recvRank_le_of_propRank_le ((I.isIndividuallyRational_swap_iff μ).2 hμ)
    ((I.isStable_swap_iff ν).2 hν) h p

variable {I} in
theorem IsProposerOptimal.isReceiverPessimal {μ : PartialMatching m n}
    (h : I.IsProposerOptimal μ) : I.IsReceiverPessimal μ :=
  ⟨h.1, fun ν hν r => I.recvRank_le_of_propRank_le h.1.1 hν (h.2 ν hν) r⟩

variable {I} in
theorem IsReceiverOptimal.isProposerPessimal {μ : PartialMatching m n}
    (h : I.IsReceiverOptimal μ) : I.IsProposerPessimal μ :=
  ⟨h.1, fun ν hν p => I.propRank_le_of_recvRank_le h.1.1 hν (h.2 ν hν) p⟩

theorem isReceiverOptimal_iff_swap (μ : PartialMatching m n) :
    I.IsReceiverOptimal μ ↔ I.swap.IsProposerOptimal μ.symm := by
  constructor
  · rintro ⟨hμ, h⟩
    refine ⟨(I.isStable_swap_iff μ).2 hμ, fun ν hν r => ?_⟩
    have := h ν.symm ((I.swap.isStable_swap_iff ν).2 hν) r
    rwa [PEquiv.symm_symm] at this
  · rintro ⟨hμ, h⟩
    exact ⟨(I.isStable_swap_iff μ).1 hμ, fun ν hν r => h ν.symm ((I.isStable_swap_iff ν).2 hν) r⟩

/-- Two individually rational matchings that give proposer `p` outcomes of the same rank give it
the same outcome. -/
theorem eq_of_propRank_eq_of_isIndividuallyRational {μ ν : PartialMatching m n}
    (hμ : I.IsIndividuallyRational μ) (hν : I.IsIndividuallyRational ν) {p : Fin m}
    (h : I.propRank p (μ p) = I.propRank p (ν p)) : μ p = ν p := by
  cases hμp : μ p with
  | some r => exact (I.eq_of_propRank_eq (hμ p r hμp).1 (hμp ▸ h)).symm
  | none =>
    cases hνp : ν p with
    | none => rfl
    | some r =>
      rw [hμp, hνp] at h
      exact absurd h.symm (Nat.ne_of_lt ((I.propRank_some_lt_none_iff p r).2 (hν p r hνp).1))

variable {I} in
/-- There is at most one proposer-optimal stable matching. -/
theorem IsProposerOptimal.unique {μ ν : PartialMatching m n} (hμ : I.IsProposerOptimal μ)
    (hν : I.IsProposerOptimal ν) : μ = ν :=
  PEquiv.ext fun p => I.eq_of_propRank_eq_of_isIndividuallyRational hμ.1.1 hν.1.1
    (le_antisymm (hμ.2 ν hν.1 p) (hν.2 μ hμ.1 p))

end IncompleteInstance

end Cslib.Algorithms.Lean.StableMatching
