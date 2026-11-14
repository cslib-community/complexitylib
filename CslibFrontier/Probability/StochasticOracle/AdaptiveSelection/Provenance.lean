/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.StochasticOracle.AdaptiveSelection.Discrete

/-!
# Chosen retention from complete oracle proposals

An upper policy may choose which valid families to process, while lower bounds
must retain the oracle's complete proposal history. Decoder compatibility is
checked per supported response against all candidates received so far, allowing
buffered candidates to be retained later.

## Main definitions

* `ProposalsValid`: each newly emitted retention family uses actually received candidates.

## Main results

* `selected_subset_proposedSets_of_valid`: actual retained candidates have source provenance.
-/

public section
namespace Cslib.Probability.StochasticOracle.AdaptiveSelection
open PartialCover
variable {E J Ω : Type*} [DecidableEq E] [DecidableEq J]

/-- At each actual response, every candidate emitted by the chosen retention
decoder has appeared in the complete proposal history, including buffered candidates. -/
@[expose] def ProposalsValid (all retained : List Ω → Ω → List (Finset J))
    (law : List Ω → PMF Ω) (u : ℕ) : Prop :=
  ∀ t, t < u → ∀ h : Fin t → Ω,
    h ∈ (PMF.seqProcess (responseStep law) t).support → ∀ x ∈ (law (PMF.seqHistory h)).support,
      (retained (PMF.seqHistory h) x).foldr (· ∪ ·) ∅ ⊆
        proposedSets all (x :: PMF.seqHistory h)

/-- Processing the complete proposal decoder itself always preserves provenance. -/
theorem ProposalsValid.refl (proposal : List Ω → Ω → List (Finset J))
    (law : List Ω → PMF Ω) (u : ℕ) : ProposalsValid proposal proposal law u := by
  intro t ht h hh x hx
  exact Finset.subset_union_left

/-- Per-response decoder compatibility supplies source provenance of the actual
retained output. No terminal coverage, success or cost conclusion is assumed. -/
theorem selected_subset_proposedSets_of_valid (I : Instance E J) (ρ : ℝ)
    (all retained : List Ω → Ω → List (Finset J)) (law : List Ω → PMF Ω) (u : ℕ)
    (H : ProposalsValid all retained law u) (n : ℕ) (hn : n ≤ u) (h : Fin n → Ω)
    (hh : h ∈ (PMF.seqProcess (responseStep law) n).support) :
    selected I ρ retained (PMF.seqHistory h) ⊆ proposedSets all (PMF.seqHistory h) := by
  induction n with
  | zero => simp [selected, proposedSets]
  | succ n ih =>
    simp only [PMF.seqProcess, PMF.mem_support_bind_iff, PMF.mem_support_map_iff] at hh
    obtain ⟨g, hg, x, hx, rfl⟩ := hh
    rw [PMF.seqHistory_snoc]
    apply (I.retain_subset ρ _ _).trans
    apply Finset.union_subset
    · exact (ih (Nat.le_of_succ_le hn) g hg).trans Finset.subset_union_right
    · exact H n (Nat.lt_of_succ_le hn) g hg x hx

end Cslib.Probability.StochasticOracle.AdaptiveSelection
