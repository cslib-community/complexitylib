/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.IncidenceWireDecoding
public import CslibFrontier.Foundations.Data.BitString.BlockRanks
import Mathlib.Data.List.GetD

/-!
# Complete assignment coverage for the physical incidence wires

The actual prefix-sum wire layout identifies every main-wire assignment with exactly one tuple
of full-width binary ranks. Fitting subset ranks therefore determine exactly one assignment,
including zero-width pairs. This proves assignment coverage, not only equality of cardinalities,
for the construction of [OpenAI2026ETH], Lemma D.2, PDF pp.55–56.

## Main definitions

* `Cslib.Circuits.Frontier.IncidenceNetwork.wireRankEquiv`: the actual layout's word/rank bijection.

## Main results

* `Cslib.Circuits.Frontier.IncidenceNetwork.wireRankEquiv_apply`: correspondence with the actual
  physical block reader.
* `Cslib.Circuits.Frontier.IncidenceNetwork.existsUnique_wireAssignment`: every tuple of valid
  subset ranks has exactly one main-wire assignment, without a supplied decoding identity.
* `Cslib.Circuits.Frontier.IncidenceNetwork.sum_wireAssignments_eq_sum_ranks`: exact reindexing
  of a sum over all main-wire assignments, with no assignment multiplicity.

## References

* [OpenAI2026ETH], Appendix D.3, Lemma D.2, PDF pp.55–56.
-/

public section

namespace Cslib.Circuits.Frontier.IncidenceNetwork

open Cslib.BitString DescribedNetwork

/-- Main-wire assignments and all full-width rank tuples for the actual computed layout. -/
noncomputable def wireRankEquiv (J : ℕ) (sys : List (List (List ℕ))) (d : List ℕ) :
    (Fin (numWires J sys d) → Bool) ≃
      ((b : Fin (J * J)) → Fin (2 ^ blockWidth J sys d b)) :=
  blockRankEquiv (blockWidth J sys d) (J * J)

/-- The bijection reads exactly the index used by both endpoints of each physical block. -/
theorem wireRankEquiv_apply (J : ℕ) (sys : List (List (List ℕ))) (d : List ℕ)
    (x : Fin (numWires J sys d) → Bool) (b : Fin (J * J)) :
    (wireRankEquiv J sys d x b : ℕ) =
      wireIndex J sys d (List.ofFn x) (b / J) (b % J) := by
  rw [wireIndex, Nat.div_add_mod']
  exact blockRankEquiv_apply (blockWidth J sys d) (J * J) x b

/-- Every valid local-rank tuple has one actual main-wire assignment. A rank outside a local
capacity is excluded by the ordinary subset-rank hypothesis, not by an assumed output relation. -/
theorem existsUnique_wireAssignment (J : ℕ) (sys : List (List (List ℕ))) (d : List ℕ)
    (rank : Fin (J * J) → ℕ)
    (hrank : ∀ b, rank b < (pairInc J sys (b / J) (b % J)).length.choose (d.getD b 0)) :
    ∃! x : Fin (numWires J sys d) → Bool,
      ∀ b : Fin (J * J), wireIndex J sys d (List.ofFn x) (b / J) (b % J) = rank b := by
  let q : (b : Fin (J * J)) → Fin (2 ^ blockWidth J sys d b) := fun b =>
    ⟨rank b, (hrank b).trans_le (by
      rw [blockWidth, width, Nat.div_add_mod']
      exact Nat.le_pow_clog Nat.one_lt_two _)⟩
  let x := (wireRankEquiv J sys d).symm q
  have hx : ∀ b : Fin (J * J), wireIndex J sys d (List.ofFn x) (b / J) (b % J) = rank b := by
    intro b
    rw [← wireRankEquiv_apply]
    exact congrArg (fun f => (f b).val) ((wireRankEquiv J sys d).apply_symm_apply q)
  refine ⟨x, hx, fun y hy => ?_⟩
  apply (wireRankEquiv J sys d).injective
  funext b
  apply Fin.ext
  rw [wireRankEquiv_apply, wireRankEquiv_apply, hy b, hx b]

/-- Exact reindexing by the actual wire/rank bijection. This is a mathematical identity for a
finite sum, not an alternative full-enumeration implementation of the native contraction. -/
theorem sum_wireAssignments_eq_sum_ranks {R : Type*} [AddCommMonoid R]
    (J : ℕ) (sys : List (List (List ℕ))) (d : List ℕ) (f : (Fin (J * J) → ℕ) → R) :
    (∑ x : Fin (numWires J sys d) → Bool,
      f (fun b => wireIndex J sys d (List.ofFn x) (b / J) (b % J))) =
        ∑ q : (b : Fin (J * J)) → Fin (2 ^ blockWidth J sys d b), f (fun b => q b) := by
  have h := (wireRankEquiv J sys d).sum_comp (fun q => f (fun b => q b))
  simpa only [wireRankEquiv_apply] using h

end Cslib.Circuits.Frontier.IncidenceNetwork
