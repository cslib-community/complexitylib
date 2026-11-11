/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Fusion.Semifilter

/-!
# Pulling circuit covers back to counterexamples

A map from counterexamples of one problem into the ambient space of a circuit, together with
reference points for each witness, transports its AND pairs to a cover. Each reference point
must belong to the circuit's target, every mapped counterexample must avoid that target, and
reference-true inputs must be accepted by the pulled-back observation.

## Main definitions

* `Cslib.Circuits.Fusion.PairCover.ofCircuitPullback`: pull a circuit's AND pairs back.

## Main results

* `Cslib.Circuits.Fusion.PairCover.length_ofCircuitPullback`: exact preservation of AND count.

## References

* Adapted from LowerBound/Fusion/Pullback.lean in
  [S. Schlesinger, *Algebraic circuit formalizations in Complexitylib*][Schlesinger2026Algebraic].
-/

@[expose] public section

namespace Cslib.Circuits.Fusion

variable {U V : Type*} {n k m : ℕ} {target : Set U} {input : Fin n → Set U}
  {admissible : Semifilter ↥(targetᶜ) → Prop} {target' : Set V}

/-- A circuit whose accepting references and rejecting counterexamples transport the input
observations yields a pair cover of the original problem. No injectivity of the map is needed. -/
def PairCover.ofCircuitPullback (c : Circuit Monotone.signature k m) (input' : Fin k → Set V)
    (o : Fin m) (hc : c.eval (Monotone.setInterpretation V) input' o = target')
    (f : ↥(targetᶜ) → V) (reference : SemifilterWitness target input admissible → target')
    (hin : ∀ w i, (reference w).val ∈ input' i → w.filter (f ⁻¹' input' i))
    (hout : ∀ x, f x ∉ target') : PairCover target input admissible where
  pairs := (List.ofFn (programAtoms c.program (Monotone.setInterpretation V) input')).filterMap
    (fun a => a.andPair? f)
  isCover w hp := by
    let P (w : SemifilterWitness target input admissible) (s : Set V) :=
      (reference w).val ∈ s → w.filter (f ⁻¹' s)
    have hfail (w : SemifilterWitness target input admissible) : ¬ P w target' := by
      intro h
      have accepted := h (reference w).property
      exact w.filter.not_apply_empty (w.filter.monotone (fun x hx => (hout x hx).elim) accepted)
    have cover := programAtoms_isCover c.program (Monotone.setInterpretation V) P input'
      hin (fun w => ⟨c.outputs o, by
        change ¬ P w (c.eval (Monotone.setInterpretation V) input' o)
        rw [hc]
        exact hfail w⟩)
    apply cover w
    intro i
    apply Atom.preserves_semifilter _ f (reference w).val w.filter
    intro p heq
    apply hp p
    exact List.mem_filterMap.mpr ⟨_, List.mem_ofFn.mpr ⟨i, rfl⟩, heq⟩

/-- Pullback retains one pair for every AND gate, including repeated or unused gates. -/
@[simp] theorem PairCover.length_ofCircuitPullback
    (c : Circuit Monotone.signature k m) (input' : Fin k → Set V) (o : Fin m)
    (hc : c.eval (Monotone.setInterpretation V) input' o = target')
    (f : ↥(targetᶜ) → V) (reference : SemifilterWitness target input admissible → target')
    (hin : ∀ w i, (reference w).val ∈ input' i → w.filter (f ⁻¹' input' i))
    (hout : ∀ x, f x ∉ target') :
    (ofCircuitPullback c input' o hc f reference hin hout).pairs.length =
      c.program.cost Monotone.andCost := by
  rw [ofCircuitPullback, length_andPairs, List.map_ofFn, List.sum_ofFn, Program.cost_eq_sum]
  rfl

end Cslib.Circuits.Fusion
