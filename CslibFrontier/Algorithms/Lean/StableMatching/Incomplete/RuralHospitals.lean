/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.StableMatching.Incomplete.DeferredAcceptance
import Mathlib.Data.Finset.Card

/-!
# The rural hospitals theorem for the marriage model

In a one-to-one market with strict, possibly incomplete preference lists, every stable matching
matches the same agents ([RothSotomayor1990], Theorem 2.22: in a marriage market with strict
preferences, the set of agents who are single is the same for all stable matchings). See also
[GaleSotomayor1985] and [GusfieldIrving1989], Section 1.4 (locator from secondary sources,
unverified). The rural hospitals theorem proper is the many-to-one version for hospitals with
capacities; the one-to-one statement is often called by the same name.

The proof compares a stable matching `ν` with deferred acceptance `μ`. Every proposer matched in
`ν` is matched in `μ`, because it weakly prefers `μ` and every partner beats being unmatched.
Every receiver matched in `μ` is matched in `ν`, because it weakly prefers `ν`. A matching
matches as many proposers as receivers, so both inclusions are equalities.

## Main results

* `IncompleteInstance.unmatched_eq_of_isStable`: the rural hospitals theorem in the form of
  [RothSotomayor1990], Theorem 2.22: two stable matchings leave the same proposers and the same
  receivers unmatched.
* `IncompleteInstance.matchedProposers_eq_of_isStable`,
  `IncompleteInstance.matchedReceivers_eq_of_isStable`: the same statement for matched agents.
* `IncompleteInstance.card_matchedProposers_eq_of_isStable`: all stable matchings have the same
  number of pairs.
* `IncompleteInstance.matchedProposers_eq_deferredAcceptance`: the matched agents of every
  stable matching are those of deferred acceptance.

## References

* [GaleSotomayor1985]
* [GusfieldIrving1989]
* [RothSotomayor1990]
-/

public section

namespace Cslib.Algorithms.Lean.StableMatching

namespace IncompleteInstance

variable {m n : ℕ} (I : IncompleteInstance m n)

open PartialMatching

/-- A proposer matched in some stable matching is matched by deferred acceptance. -/
theorem matchedProposers_subset_deferredAcceptance {ν : PartialMatching m n} (hν : I.IsStable ν) :
    matchedProposers ν ⊆ matchedProposers I.deferredAcceptance := by
  intro p hp
  rw [mem_matchedProposers] at hp ⊢
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.1 hp
  have hlt : I.propRank p (ν p) < I.propRank p none := by
    rw [hr]; exact (I.propRank_some_lt_none_iff p r).2 (hν.1 p r hr).1
  cases hμ : I.deferredAcceptance p with
  | some _ => rfl
  | none =>
    have := I.propRank_deferredAcceptance_le_of_isStable hν p
    rw [hμ] at this
    omega

/-- A receiver matched by deferred acceptance is matched in every stable matching. -/
theorem matchedReceivers_deferredAcceptance_subset {ν : PartialMatching m n}
    (hν : I.IsStable ν) : matchedReceivers I.deferredAcceptance ⊆ matchedReceivers ν := by
  intro r hr
  rw [mem_matchedReceivers] at hr ⊢
  obtain ⟨p, hp⟩ := Option.isSome_iff_exists.1 hr
  have hlt : I.recvRank r (I.deferredAcceptance.symm r) < I.recvRank r none := by
    rw [hp]
    exact (I.recvRank_some_lt_none_iff r p).2
      (I.isIndividuallyRational_deferredAcceptance p r (PEquiv.eq_some_iff _ |>.1 hp)).2
  cases hνr : ν.symm r with
  | some _ => rfl
  | none =>
    have := I.isReceiverPessimal_deferredAcceptance.2 ν hν r
    rw [hνr] at this
    omega

/-- Every stable matching matches the same proposers as deferred acceptance. -/
theorem matchedProposers_eq_deferredAcceptance {ν : PartialMatching m n} (hν : I.IsStable ν) :
    matchedProposers ν = matchedProposers I.deferredAcceptance := by
  refine Finset.eq_of_subset_of_card_le (I.matchedProposers_subset_deferredAcceptance hν) ?_
  rw [← card_matchedReceivers, ← card_matchedReceivers]
  exact Finset.card_le_card (I.matchedReceivers_deferredAcceptance_subset hν)

/-- Every stable matching matches the same receivers as deferred acceptance. -/
theorem matchedReceivers_eq_deferredAcceptance {ν : PartialMatching m n} (hν : I.IsStable ν) :
    matchedReceivers ν = matchedReceivers I.deferredAcceptance := by
  refine (Finset.eq_of_subset_of_card_le (I.matchedReceivers_deferredAcceptance_subset hν) ?_).symm
  rw [card_matchedReceivers, card_matchedReceivers]
  exact Finset.card_le_card (I.matchedProposers_subset_deferredAcceptance hν)

/-- Two stable matchings match the same proposers. -/
theorem matchedProposers_eq_of_isStable {μ ν : PartialMatching m n} (hμ : I.IsStable μ)
    (hν : I.IsStable ν) : matchedProposers μ = matchedProposers ν :=
  (I.matchedProposers_eq_deferredAcceptance hμ).trans
    (I.matchedProposers_eq_deferredAcceptance hν).symm

/-- Two stable matchings match the same receivers. -/
theorem matchedReceivers_eq_of_isStable {μ ν : PartialMatching m n} (hμ : I.IsStable μ)
    (hν : I.IsStable ν) : matchedReceivers μ = matchedReceivers ν :=
  (I.matchedReceivers_eq_deferredAcceptance hμ).trans
    (I.matchedReceivers_eq_deferredAcceptance hν).symm

/-- The rural hospitals theorem for the marriage model ([RothSotomayor1990], Theorem 2.22): the
set of agents who are single is the same for all stable matchings. Here the proposers and the
receivers that the stable matchings `μ` and `ν` leave unmatched coincide. -/
theorem unmatched_eq_of_isStable {μ ν : PartialMatching m n} (hμ : I.IsStable μ)
    (hν : I.IsStable ν) :
    {p | μ p = none} = {p | ν p = none} ∧ {r | μ.symm r = none} = {r | ν.symm r = none} := by
  have hP := I.matchedProposers_eq_of_isStable hμ hν
  have hR := I.matchedReceivers_eq_of_isStable hμ hν
  constructor
  · ext p
    have := congrArg (p ∈ ·) hP
    simp only [mem_matchedProposers, eq_iff_iff, Option.isSome_iff_ne_none, ne_eq,
      not_iff_not] at this
    exact this
  · ext r
    have := congrArg (r ∈ ·) hR
    simp only [mem_matchedReceivers, eq_iff_iff, Option.isSome_iff_ne_none, ne_eq,
      not_iff_not] at this
    exact this

/-- All stable matchings have the same number of pairs. -/
theorem card_matchedProposers_eq_of_isStable {μ ν : PartialMatching m n} (hμ : I.IsStable μ)
    (hν : I.IsStable ν) : (matchedProposers μ).card = (matchedProposers ν).card := by
  rw [I.matchedProposers_eq_of_isStable hμ hν]

end IncompleteInstance

end Cslib.Algorithms.Lean.StableMatching
