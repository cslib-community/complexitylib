/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Fusion.Pullback
public import Complexity.Computability.Circuit.Boolean.Nondeterminism
public import Complexity.Computability.Circuit.Boolean.AltFormula

/-!
# Semi-ultrafilter bounds for universally quantified circuits

For a Boolean verifier, choose a rejecting auxiliary assignment for each false primary input.
A semi-ultrafilter above a true primary input selects auxiliary reference bits by accepting one
side of each auxiliary coordinate. The verifier accepts this fused reference, but rejects every
chosen counterexample. Pulling its AND pairs back gives a cover with exactly its AND count.

The quantifier is the existing `Boolean.forallGuess`. Verifiers are native monotone circuits
with positive and negative input literals supplied for free; constants and OR gates have zero
AND cost. This module proves the cover lower-bound direction of the conondeterministic
characterization, not its converse.

## Main results

* `Cslib.Circuits.Fusion.exists_pairCover_forallGuess`: extract a cover of exact AND cost.
* `Cslib.Circuits.Fusion.pairCoverComplexity_forallGuess_le_cost`: semi-ultrafilter cover
  complexity bounds every native universal verifier's AND count.

## References

* [B. P. Cavalar and I. C. Oliveira, *Boolean Circuit Complexity and Two-Dimensional Cover
  Problems*][CavalarOliveira2025], Theorem 45, credited there to Karchmer.
* Adapted from LowerBound/Fusion/Conondeterministic.lean in
  [S. Schlesinger, *Algebraic circuit formalizations in Complexitylib*][Schlesinger2026Algebraic].
-/

@[expose] public section

namespace Cslib.Circuits.Fusion

open Cslib Boolean

variable {n a : ℕ} (g : BooleanFunction (n + a))

private abbrev trueSet (f : BooleanFunction n) := {x | f x = true}
private abbrev literalSets (n : ℕ) := fun i => {x : BitString n | AltFormula.literals x i = true}
private abbrev Witness := SemifilterWitness (trueSet (forallGuess g)) (literalSets n)
  Semifilter.IsUltra

private theorem exists_rejectingAuxiliary (x : ↥((trueSet (forallGuess g))ᶜ)) :
    ∃ y : BitString a, g (Fin.append x.val y) ≠ true := by
  classical
  have h : ¬ ∀ y : BitString a, g (Fin.append x.val y) = true := by
    intro hall
    exact x.property (by simpa only [trueSet, Set.mem_ofPred_eq, forallGuess, decide_eq_true_eq]
      using hall)
  exact not_forall.mp h

private noncomputable def rejectingAuxiliary (x : ↥((trueSet (forallGuess g))ᶜ)) : BitString a :=
  Classical.choose (exists_rejectingAuxiliary g x)

private noncomputable def counterexampleMap (x : ↥((trueSet (forallGuess g))ᶜ)) :
    BitString (n + a) :=
  Fin.append x.val (rejectingAuxiliary g x)

private noncomputable def fusedAuxiliary (w : Witness g) : BitString a :=
  fun i => @decide (w.filter {x | rejectingAuxiliary g x i = true}) (Classical.propDecidable _)

private noncomputable def referencePoint (w : Witness g) : trueSet g :=
  ⟨Fin.append w.point.val (fusedAuxiliary g w), by
    have h := w.point.property
    simp only [trueSet, Set.mem_ofPred_eq, forallGuess, decide_eq_true_eq] at h
    exact h _⟩

private theorem auxiliary_sound (w : Witness g) (i : Fin a) (b : Bool)
    (hb : fusedAuxiliary g w i = b) : w.filter {x | rejectingAuxiliary g x i = b} := by
  classical
  cases b
  · have hn : ¬ w.filter {x | rejectingAuxiliary g x i = true} := by
      simpa only [fusedAuxiliary, decide_eq_false_iff_not] using hb
    have h := (w.admissible_filter {x | rejectingAuxiliary g x i = true}).resolve_left hn
    convert h using 1
    ext x
    simp
  · simpa only [fusedAuxiliary, decide_eq_true_eq] using hb

private theorem input_sound (w : Witness g) (i : Fin ((n + a) + (n + a))) :
    (referencePoint g w).val ∈ literalSets (n + a) i →
      w.filter (counterexampleMap g ⁻¹' literalSets (n + a) i) := by
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [literalSets, AltFormula.literals, Fin.append_left, Set.mem_ofPred_eq,
      referencePoint]
    refine Fin.addCases (fun k hk => ?_) (fun k hk => ?_) j
    · have hw := w.above (Fin.castAdd n k)
      simp only [literalSets, AltFormula.literals, Fin.append_left, Set.mem_ofPred_eq,
        Set.preimage_ofPred_eq] at hw
      simpa only [counterexampleMap, Fin.append_left, Set.preimage_ofPred_eq] using
        hw (by simpa only [Fin.append_left] using hk)
    · simpa only [counterexampleMap, Fin.append_right, Set.preimage_ofPred_eq] using
        auxiliary_sound g w k true (by simpa only [Fin.append_right] using hk)
  · simp only [literalSets, AltFormula.literals, Fin.append_right, Set.mem_ofPred_eq,
      Bool.not_eq_true_eq_eq_false, referencePoint]
    refine Fin.addCases (fun k hk => ?_) (fun k hk => ?_) j
    · have hw := w.above (Fin.natAdd n k)
      simp only [literalSets, AltFormula.literals, Fin.append_right, Set.mem_ofPred_eq,
        Set.preimage_ofPred_eq, Bool.not_eq_true_eq_eq_false] at hw
      simpa only [counterexampleMap, Fin.append_left, Set.preimage_ofPred_eq,
        Bool.not_eq_true_eq_eq_false] using
        hw (by simpa only [Fin.append_left] using hk)
    · simpa only [counterexampleMap, Fin.append_right, Set.preimage_ofPred_eq,
        Bool.not_eq_true_eq_eq_false] using
        auxiliary_sound g w k false (by simpa only [Fin.append_right] using hk)

/-- A universally quantified verifier gives a cover of exactly the same AND cost. -/
theorem exists_pairCover_forallGuess
    (c : Circuit Monotone.signature ((n + a) + (n + a)) 1)
    (hc : c.ComputesFrom Monotone.interpretation (single g) AltFormula.literals) :
    ∃ cover : PairCover {x | forallGuess g x = true}
      (fun i => {x | AltFormula.literals x i = true}) Semifilter.IsUltra,
      cover.pairs.length = c.program.cost Monotone.andCost := by
  let cover := PairCover.ofCircuitPullback c (literalSets (n + a)) 0
    (congrFun ((Monotone.eval_setOf_iff_computesFrom c AltFormula.literals (single g)).mpr hc) 0)
    (counterexampleMap g) (referencePoint g) (input_sound g)
    (fun x => Classical.choose_spec (exists_rejectingAuxiliary g x))
  exact ⟨cover, PairCover.length_ofCircuitPullback ..⟩

/-- Semi-ultrafilter cover bounds apply to native universally quantified verifiers, with no
loss in the number of AND gates and any number of auxiliary bits. -/
theorem pairCoverComplexity_forallGuess_le_cost
    (c : Circuit Monotone.signature ((n + a) + (n + a)) 1)
    (hc : c.ComputesFrom Monotone.interpretation (single g) AltFormula.literals) :
    pairCoverComplexity {x | forallGuess g x = true}
      (fun i => {x | AltFormula.literals x i = true}) Semifilter.IsUltra ≤
      c.program.cost Monotone.andCost := by
  obtain ⟨cover, hcover⟩ := exists_pairCover_forallGuess g c hc
  simpa only [hcover] using pairCoverComplexity_le cover

/-- The cover lower bound also holds for the minimum AND cost of implementing the verifier. -/
theorem pairCoverComplexity_forallGuess_le_ecomplexityFrom :
    pairCoverComplexity {x | forallGuess g x = true}
      (fun i => {x | AltFormula.literals x i = true}) Semifilter.IsUltra ≤
      ecomplexityFrom Monotone.interpretation Monotone.andCost (single g) AltFormula.literals :=
  le_ecomplexityFrom_iff.mpr (pairCoverComplexity_forallGuess_le_cost g)

end Cslib.Circuits.Fusion
