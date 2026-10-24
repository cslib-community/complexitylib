/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Cyclic
public import Complexity.Computability.Circuit.Fusion.Semifilter

/-!
# Semifilter bounds for cyclic set circuits

The AND pairs at a cyclic circuit's least solution form a semifilter cover of each designated
output. The proof uses fixed-point induction: reference membership at an intermediate state
implies observation of the corresponding final value. This predicate is closed under arbitrary
unions, while the final AND pairs provide its induction step. Leastness prevents unsupported
feedback from manufacturing target points.

Extraction charges every AND equation exactly once, including unused cycles and repeated gates.
Constants and OR equations contribute no pairs. Outputs may share a gate or read inputs directly.
The bounds support any admissible class of semifilters and transfer to minimum cyclic complexity
from arbitrary supplied source functions. This is a semantic construction over sets, with no
execution or convergence-time claim. A converse construction from covers is not asserted here.

## Main results

* `Cslib.Circuits.Fusion.PairCover.ofCyclicCircuit`: a cover from a least-fixed-point construction.
* `Cslib.Circuits.Fusion.PairCover.length_ofCyclicCircuit`: exact preservation of AND cost.
* `Cslib.Circuits.Fusion.pairCoverComplexity_le_cyclic_ecomplexityFrom`: the minimum-cost bound.

## References

* Adapted from LowerBound/Fusion/Cyclic.lean in
  [S. Schlesinger, *Algebraic circuit formalizations in Complexitylib*][Schlesinger2026Algebraic].
-/

@[expose] public section

namespace Cslib.Circuits.Fusion

universe u v

variable {σ : Signature.{u}} {U : Type v} {n m : ℕ}

/-- The semantic atoms of the equations at a proposed state. -/
def cyclicAtoms (c : CyclicCircuit σ n m) (input : Fin n → U)
    (state : Fin c.size → U) (i : Fin c.size) : Atom σ U where
  op := (c.lines i).op
  arguments := Wire.elim input state ∘ (c.lines i).wires

/-- The AND pairs at the least solution defeat every admissible semifilter witness. -/
def PairCover.ofCyclicCircuit (c : CyclicCircuit Monotone.signature n m)
    (input : Fin n → Set U) (o : Fin m) {target : Set U}
    (hc : c.eval (Monotone.setInterpretation U) Monotone.setInterpretation_mono input o = target)
    (admissible : Semifilter ↥(targetᶜ) → Prop := fun _ => True) :
    PairCover target input admissible where
  pairs := (List.ofFn (cyclicAtoms c input
    (c.evalGates (Monotone.setInterpretation U) Monotone.setInterpretation_mono input))).filterMap
      (fun a => a.andPair? Subtype.val)
  isCover w hp := by
    let values := c.evalGates (Monotone.setInterpretation U) Monotone.setInterpretation_mono input
    have hgate : ∀ i, w.predicate (values i) := by
      apply (c.step (Monotone.setInterpretation U)
        Monotone.setInterpretation_mono input).lfp_induction
        (p := fun state => ∀ i, w.point.val ∈ state i → w.filter (Subtype.val ⁻¹' values i))
      · intro state hs _ i hx
        rw [show values i = (c.lines i).eval (Monotone.setInterpretation U) input values from
          (c.evalGates_fixed _ Monotone.setInterpretation_mono input i).symm]
        apply (cyclicAtoms c input values i).semifilter_of_mem Subtype.val w.point.val w.filter
          ?_ (Wire.elim input state ∘ (c.lines i).wires) ?_ hx
        · intro p heq
          exact hp p (List.mem_filterMap.mpr ⟨_, List.mem_ofFn.mpr ⟨i, rfl⟩, heq⟩)
        · intro a
          change w.point.val ∈ Wire.elim input state ((c.lines i).wires a) →
            w.filter (Subtype.val ⁻¹' Wire.elim input values ((c.lines i).wires a))
          cases (c.lines i).wires a with
          | input j => exact w.above j
          | gate j => exact hs j
      · intro S hS i hx
        rw [sSup_apply_eq_sSup_image] at hx
        obtain ⟨_, ⟨state, hstate, rfl⟩, hx⟩ := hx
        exact hS state hstate i hx
    have hout : w.predicate (c.eval (Monotone.setInterpretation U)
        Monotone.setInterpretation_mono input o) := by
      change w.predicate (Wire.elim input values (c.outputs o))
      cases c.outputs o with
      | input j => exact w.above j
      | gate j => exact hgate j
    exact w.not_predicate_target (by simpa only [hc] using hout)

/-- Extraction retains the exact AND count, including unused cyclic components. -/
@[simp] theorem PairCover.length_ofCyclicCircuit (c : CyclicCircuit Monotone.signature n m)
    (input : Fin n → Set U) (o : Fin m) {target : Set U}
    (hc : c.eval (Monotone.setInterpretation U) Monotone.setInterpretation_mono input o = target)
    (admissible : Semifilter ↥(targetᶜ) → Prop := fun _ => True) :
    (PairCover.ofCyclicCircuit c input o hc admissible).pairs.length =
      c.cost Monotone.andCost := by
  rw [PairCover.ofCyclicCircuit, length_andPairs, List.map_ofFn, List.sum_ofFn]
  rfl

/-- A combinatorial pair-cover bound applies to every cyclic construction of the target. -/
theorem pairCover_lowerBound_cyclic {target : Set U} {input : Fin n → Set U}
    {admissible : Semifilter ↥(targetᶜ) → Prop} {k : ℕ}
    (hbound : ∀ c : PairCover target input admissible, k ≤ c.pairs.length)
    (c : CyclicCircuit Monotone.signature n m) (o : Fin m)
    (hc : c.eval (Monotone.setInterpretation U) Monotone.setInterpretation_mono input o = target) :
    k ≤ c.cost Monotone.andCost := by
  simpa only [PairCover.length_ofCyclicCircuit] using
    hbound (PairCover.ofCyclicCircuit c input o hc admissible)

/-- The minimum pair-cover length bounds the AND cost of any cyclic construction. -/
private theorem pairCoverComplexity_le_cyclic_cost {target : Set U}
    (c : CyclicCircuit Monotone.signature n m) (input : Fin n → Set U) (o : Fin m)
    (hc : c.eval (Monotone.setInterpretation U) Monotone.setInterpretation_mono input o = target)
    (admissible : Semifilter ↥(targetᶜ) → Prop := fun _ => True) :
    pairCoverComplexity target input admissible ≤ c.cost Monotone.andCost := by
  simpa only [PairCover.length_ofCyclicCircuit] using
    pairCoverComplexity_le (PairCover.ofCyclicCircuit c input o hc admissible)

/-- A cover bound at a supplied source assignment bounds minimum cyclic source complexity. -/
theorem pairCoverComplexity_le_cyclic_ecomplexityFrom {X : Type*}
    (sources : X → Fin n → Set U) (target : X → Fin m → Set U) (x : X) (o : Fin m)
    (admissible : Semifilter ↥((target x o)ᶜ) → Prop := fun _ => True) :
    pairCoverComplexity (target x o) (sources x) admissible ≤
      CyclicCircuit.ecomplexityFrom (Monotone.setInterpretation U)
        Monotone.setInterpretation_mono Monotone.andCost target sources :=
  CyclicCircuit.le_ecomplexityFrom_iff.mpr fun c hc =>
    pairCoverComplexity_le_cyclic_cost c (sources x) o (congrFun (hc x) o) admissible

end Cslib.Circuits.Fusion
