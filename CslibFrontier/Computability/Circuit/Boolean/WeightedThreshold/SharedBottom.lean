/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.WeightedThreshold.ThresholdCounting

/-!
# Restricting depth-two threshold circuits with several outputs

A weighted threshold circuit `c : Circuit signature n t` of depth at most two is a family of `t`
depth-two circuits (`THR ∘ THR`) that share their bottom gates. The *bottom gates*
(`circuitBottomGates`) are the gates read with nonzero weight by the gate of some designated
output; they have depth at most one. Feeding the `t` outputs into one more unweighted threshold
gate gives the `MAJ ∘ THR ∘ THR` circuits of [KaneWilliams2016], `arXiv:1511.07860v1`, Section 6.

Fix every input outside `univ.image emb`, for an injective `emb : κ → Fin n`, to the values of
`w`. Every output then collapses to a function in `IsDepthTwoOverWeights (circuitBottomWeights c
emb) q` (`isDepthTwoOverWeights_eval_embedUpdate_circuitBottom`). Here `circuitBottomWeights c emb`
are the weight vectors of the bottom gates on the live coordinates, which do not depend on `w`, and
`q` is the number of bottom gates of the whole circuit that the restriction does not force to a
function of at most one input (`circuitBottomUnforcedAtMostOneCount`). The same `q` serves all
outputs at once. Since a bottom gate forced to a constant is forced to at most one input, `q` may
also be the number of bottom gates not forced to a constant (`circuitBottomUnforcedConstCount`,
`isDepthTwoOverWeights_eval_embedUpdate_circuitBottom_const`).

Averaged over the block-partition restrictions `blockLiveSet blockVar σ` and all `w`, these counts
are at most `4 * (1 / |τ|) * c.size * √n` and `4 * c.wireCount * (1 / |τ|) * √(1 / |τ|)`
(`sum_circuitBottomUnforcedConstCount_blockLiveSet_le`,
`sum_circuitBottomUnforcedAtMostOneCount_blockLiveSet_le`), by the repaired gate and wire
restriction lemmas ([KaneWilliams2016], Lemmas 1.1 and 3.1). For a single output these are the
statements of `ThresholdCounting.lean` with every bottom gate of the circuit counted.

## Main definitions

* `Cslib.Circuits.Boolean.WeightedThreshold.outputBottomGates`: the gates read by the gate of
  one output.
* `Cslib.Circuits.Boolean.WeightedThreshold.circuitBottomGates`: the gates read by output gates,
  the union of `outputBottomGates` (`circuitBottomGates_eq_biUnion`).
* `Cslib.Circuits.Boolean.WeightedThreshold.circuitBottomWeights`: their live weight vectors.
* `Cslib.Circuits.Boolean.WeightedThreshold.circuitBottomUnforcedConstCount`,
  `Cslib.Circuits.Boolean.WeightedThreshold.circuitBottomUnforcedAtMostOneCount`: the bottom gates
  surviving a restriction.

## Main results

* `Cslib.Circuits.Boolean.WeightedThreshold.card_outputBottomGates_lt_size`: an output gate has
  fewer bottom gates than the circuit has gates.
* `Cslib.Circuits.Boolean.WeightedThreshold.card_circuitBottomGates_le_size`,
  `Cslib.Circuits.Boolean.WeightedThreshold.card_circuitBottomGates_le_wireCount`: there are at
  most `c.size` and at most `c.wireCount` bottom gates.
* `WeightedThreshold.isDepthTwoOverWeights_eval_embedUpdate_circuitBottom`,
  `WeightedThreshold.isDepthTwoOverWeights_eval_embedUpdate_circuitBottom_const`: restricted
  outputs over the fixed bottom weights, with one survivor count for all outputs.
* Expected survivors under block-partition restrictions:
  `Cslib.Circuits.Boolean.WeightedThreshold.sum_circuitBottomUnforcedConstCount_blockLiveSet_le`,
  `Cslib.Circuits.Boolean.WeightedThreshold.sum_circuitBottomUnforcedAtMostOneCount_blockLiveSet_le`

## References

* [D. M. Kane and R. Williams, *Super-Linear Gate and Super-Quadratic Wire Lower Bounds for
  Depth-Two and Depth-Three Threshold Circuits*][KaneWilliams2016], `arXiv:1511.07860v1`,
  Lemmas 1.1 and 3.1 and Section 6
-/

public section

namespace Cslib.Circuits.Boolean.WeightedThreshold

open Finset Cslib.Combinatorics.LittlewoodOfford

variable {n t : ℕ}

/-! ### Bottom gates and their live weight vectors -/

/-- The **bottom gates of one output** `o`: the gates with nonzero weight in the gate of `o`, or
none if `o` is an input wire. -/
noncomputable def outputBottomGates (c : Circuit signature n t) (o : Fin t) :
    Finset (Fin c.size) :=
  (c.outputs o).elim (fun _ => ∅) (gateSupport c.program)

/-- An output that is the gate `top` has the gates read by `top` as its bottom gates. -/
theorem outputBottomGates_of_gate {c : Circuit signature n t} {o : Fin t} {top : Fin c.size}
    (h : c.outputs o = .gate top) : outputBottomGates c o = gateSupport c.program top := by
  rw [outputBottomGates, h]; rfl

/-- An output that is an input wire has no bottom gates. -/
theorem outputBottomGates_of_input {c : Circuit signature n t} {o : Fin t} {i : Fin n}
    (h : c.outputs o = .input i) : outputBottomGates c o = ∅ := by
  rw [outputBottomGates, h]; rfl

/-- The output gate is not among its own bottom gates, so an output gate has fewer bottom gates
than the circuit has gates. -/
theorem card_outputBottomGates_lt_size {c : Circuit signature n t} {o : Fin t} {top : Fin c.size}
    (h : c.outputs o = .gate top) : #(outputBottomGates c o) < c.size := by
  classical
  rw [outputBottomGates_of_gate h]
  have htop : top ∉ gateSupport c.program top := by
    rw [mem_gateSupport, not_not]; exact gateWeight_eq_zero_of_le _ _ _ le_rfl
  calc #(gateSupport c.program top) < #(univ : Finset (Fin c.size)) :=
        card_lt_card ⟨subset_univ _, fun hsub => htop (hsub (mem_univ top))⟩
    _ = c.size := by rw [card_univ, Fintype.card_fin]

/-- The **bottom gates** of a weighted threshold circuit: the gates with nonzero weight in the gate
of some designated output, i.e. the union of `outputBottomGates c o` over the outputs `o`. -/
noncomputable def circuitBottomGates (c : Circuit signature n t) : Finset (Fin c.size) :=
  univ.biUnion (outputBottomGates c)

/-- The bottom gates of the circuit are the union of the bottom gates of its outputs. -/
theorem circuitBottomGates_eq_biUnion (c : Circuit signature n t) :
    circuitBottomGates c = univ.biUnion (outputBottomGates c) := by
  unfold circuitBottomGates; rfl

/-- The bottom gates of an output are bottom gates of the circuit. -/
theorem outputBottomGates_subset_circuitBottomGates (c : Circuit signature n t) (o : Fin t) :
    outputBottomGates c o ⊆ circuitBottomGates c := fun _ hk =>
  mem_biUnion.mpr ⟨o, mem_univ o, hk⟩

/-- The gates read by the gate of an output are bottom gates. -/
theorem gateSupport_subset_circuitBottomGates (c : Circuit signature n t) {o : Fin t}
    {top : Fin c.size} (h : c.outputs o = .gate top) :
    gateSupport c.program top ⊆ circuitBottomGates c :=
  outputBottomGates_of_gate h ▸ outputBottomGates_subset_circuitBottomGates c o

/-- A bottom gate is read by the gate of some designated output. -/
theorem exists_mem_gateSupport_of_mem_circuitBottomGates (c : Circuit signature n t)
    {k : Fin c.size} (hk : k ∈ circuitBottomGates c) :
    ∃ o top, c.outputs o = .gate top ∧ k ∈ gateSupport c.program top := by
  obtain ⟨o, -, ho⟩ := mem_biUnion.mp hk
  cases h : c.outputs o with
  | input _ => rw [outputBottomGates_of_input h] at ho; exact absurd ho (notMem_empty k)
  | gate top => rw [outputBottomGates_of_gate h] at ho; exact ⟨o, top, h, ho⟩

/-- A single-output circuit has the bottom gates of its output. -/
theorem circuitBottomGates_eq_outputBottomGates (c : Circuit signature n 1) (o : Fin 1) :
    circuitBottomGates c = outputBottomGates c o := by
  rw [circuitBottomGates_eq_biUnion, univ_unique, singleton_biUnion, Subsingleton.elim default o]

/-- A circuit has at most `c.size` bottom gates. -/
theorem card_circuitBottomGates_le_size (c : Circuit signature n t) :
    #(circuitBottomGates c) ≤ c.size :=
  (card_le_univ _).trans_eq (Fintype.card_fin _)

/-- A circuit has at most `c.wireCount` bottom gates: every bottom gate has an active wire into a
gate. -/
theorem card_circuitBottomGates_le_wireCount (c : Circuit signature n t) :
    #(circuitBottomGates c) ≤ c.wireCount := by
  classical
  have hsub : circuitBottomGates c ⊆ univ.biUnion (gateSupport c.program) := fun k hk => by
    obtain ⟨o, top, -, hk⟩ := exists_mem_gateSupport_of_mem_circuitBottomGates c hk
    exact mem_biUnion.mpr ⟨top, mem_univ top, hk⟩
  calc #(circuitBottomGates c) ≤ ∑ gate, #(gateSupport c.program gate) :=
        (card_le_card hsub).trans card_biUnion_le
    _ ≤ c.wireCount := by
        rw [Circuit.wireCount, wireCount_eq_inputWireCount_add]
        exact Nat.le_add_left _ _

/-- The **live weight vectors** of the bottom gates along `emb : κ → Fin n`: the restrictions
`fun j => inputWeight c.program k (emb j)` of their input weight vectors. They depend on `emb` but
not on the values of the fixed inputs. -/
noncomputable def circuitBottomWeights {κ : Type*} [Fintype κ] (c : Circuit signature n t)
    (emb : κ → Fin n) : Finset (κ → ℝ) :=
  (circuitBottomGates c).image fun k j => inputWeight c.program k (emb j)

/-- There are at most as many live weight vectors as bottom gates. -/
theorem card_circuitBottomWeights_le {κ : Type*} [Fintype κ] (c : Circuit signature n t)
    (emb : κ → Fin n) : #(circuitBottomWeights c emb) ≤ #(circuitBottomGates c) :=
  card_image_le

/-! ### Surviving bottom gates -/

/-- The number of bottom gates whose linear threshold function is not forced to a constant outside
`B` by `w`. -/
noncomputable def circuitBottomUnforcedConstCount (c : Circuit signature n t)
    (B : Finset (Fin n)) (w : Fin n → Bool) : ℕ :=
  #{k ∈ circuitBottomGates c |
    ¬ ForcedToConst (ltfEval (inputWeight c.program k) (c.program.lines k).op.threshold) B w}

/-- The number of bottom gates whose linear threshold function is not forced to a function of at
most one input outside `B` by `w`. -/
noncomputable def circuitBottomUnforcedAtMostOneCount (c : Circuit signature n t)
    (B : Finset (Fin n)) (w : Fin n → Bool) : ℕ :=
  #{k ∈ circuitBottomGates c |
    ¬ ForcedToAtMostOne (ltfEval (inputWeight c.program k) (c.program.lines k).op.threshold) B w}

/-- Fewer bottom gates survive as functions of two or more inputs than as nonconstant functions. -/
theorem circuitBottomUnforcedAtMostOneCount_le_circuitBottomUnforcedConstCount
    (c : Circuit signature n t) (B : Finset (Fin n)) (w : Fin n → Bool) :
    circuitBottomUnforcedAtMostOneCount c B w ≤ circuitBottomUnforcedConstCount c B w :=
  card_le_card fun _ hk => mem_filter.mpr
    ⟨(mem_filter.mp hk).1, fun h => (mem_filter.mp hk).2 h.forcedToAtMostOne⟩

/-! ### Collapse of every output over the shared bottom weights -/

/-- The single-output circuit with the program of `c` and output `o`. -/
private def outputCircuit (c : Circuit signature n t) (o : Fin t) : Circuit signature n 1 :=
  ⟨c.program, fun _ => c.outputs o⟩

private theorem depth_outputCircuit_le (c : Circuit signature n t) (o : Fin t) :
    (outputCircuit c o).depth ≤ c.depth :=
  (Circuit.depth_le_iff _).mpr fun _ => c.outputDepths_le_depth o

private theorem circuitLiveWeights_outputCircuit_subset {κ : Type*} [Fintype κ]
    (c : Circuit signature n t) (o : Fin t) (emb : κ → Fin n) :
    circuitLiveWeights (outputCircuit c o) 0 emb ⊆ circuitBottomWeights c emb := by
  classical
  unfold circuitLiveWeights circuitBottomWeights outputCircuit
  dsimp only
  cases h : c.outputs o with
  | input _ => exact empty_subset _
  | gate top => exact image_subset_image (gateSupport_subset_circuitBottomGates c h)

private theorem circuitUnforcedAtMostOneCount_outputCircuit_le (c : Circuit signature n t)
    (o : Fin t) (B : Finset (Fin n)) (w : Fin n → Bool) :
    circuitUnforcedAtMostOneCount (outputCircuit c o) 0 B w ≤
      circuitBottomUnforcedAtMostOneCount c B w := by
  classical
  unfold circuitUnforcedAtMostOneCount outputCircuit
  dsimp only
  cases h : c.outputs o with
  | input _ => exact Nat.zero_le _
  | gate top =>
    exact card_le_card (filter_subset_filter _ (gateSupport_subset_circuitBottomGates c h))

/-- **Depth-two collapse over shared bottom weights**: for a weighted threshold circuit `c` of
depth at most `2` with any number of outputs and an injective `emb : κ → Fin n`, restricting
outside `univ.image emb` to `w` turns every output into a function in
`IsDepthTwoOverWeights (circuitBottomWeights c emb) q` with
`q = circuitBottomUnforcedAtMostOneCount c (univ.image emb) w`, the same for all outputs. -/
theorem isDepthTwoOverWeights_eval_embedUpdate_circuitBottom {κ : Type*} [Fintype κ]
    (c : Circuit signature n t) (hd : c.depth ≤ 2) {emb : κ → Fin n}
    (hinj : Function.Injective emb) (w : Fin n → Bool) (o : Fin t) :
    IsDepthTwoOverWeights (circuitBottomWeights c emb)
      (circuitBottomUnforcedAtMostOneCount c (univ.image emb) w)
      (fun u : κ → Bool => c.eval interpretation (embedUpdate emb w u) o) :=
  ((isDepthTwoOverWeights_eval_embedUpdate (outputCircuit c o)
    ((depth_outputCircuit_le c o).trans hd) 0 hinj w).mono_weights
      (circuitLiveWeights_outputCircuit_subset c o emb)).mono
    (circuitUnforcedAtMostOneCount_outputCircuit_le c o _ w)

/-- Variant of `isDepthTwoOverWeights_eval_embedUpdate_circuitBottom` counting the bottom gates
not forced to a constant. -/
theorem isDepthTwoOverWeights_eval_embedUpdate_circuitBottom_const {κ : Type*} [Fintype κ]
    (c : Circuit signature n t) (hd : c.depth ≤ 2) {emb : κ → Fin n}
    (hinj : Function.Injective emb) (w : Fin n → Bool) (o : Fin t) :
    IsDepthTwoOverWeights (circuitBottomWeights c emb)
      (circuitBottomUnforcedConstCount c (univ.image emb) w)
      (fun u : κ → Bool => c.eval interpretation (embedUpdate emb w u) o) :=
  (isDepthTwoOverWeights_eval_embedUpdate_circuitBottom c hd hinj w o).mono
    (circuitBottomUnforcedAtMostOneCount_le_circuitBottomUnforcedConstCount c _ w)

/-! ### Expected survivors under block-partition restrictions -/

/-- Averaging `circuitBottomUnforcedConstCount c (blockLiveSet blockVar σ) w` over all block
selections `σ : κ → τ` and assignments `w : Fin n → Bool` gives at most
`|κ → τ| * 2 ^ n * (4 * (1 / |τ|) * c.size * √n)`. -/
theorem sum_circuitBottomUnforcedConstCount_blockLiveSet_le {κ τ : Type*}
    [Fintype κ] [DecidableEq κ] [Fintype τ] (c : Circuit signature n t)
    (blockVar : κ → τ → Fin n)
    (hinj : ∀ j₁ t₁ j₂ t₂, blockVar j₁ t₁ = blockVar j₂ t₂ → j₁ = j₂ ∧ t₁ = t₂) :
    (∑ σ : κ → τ, ∑ w : Fin n → Bool,
      (circuitBottomUnforcedConstCount c (blockLiveSet blockVar σ) w : ℝ)) ≤
      (Fintype.card (κ → τ) : ℝ) * (2 : ℝ) ^ n *
        (4 * (1 / (Fintype.card τ : ℝ)) * (c.size : ℝ) * Real.sqrt (n : ℝ)) :=
  sum_card_filter_not_forcedToConst_blockLiveSet_le c (circuitBottomGates c) blockVar hinj

/-- Averaging `circuitBottomUnforcedAtMostOneCount c (blockLiveSet blockVar σ) w` over all block
selections `σ : κ → τ` and assignments `w : Fin n → Bool` gives at most
`|κ → τ| * 2 ^ n * (4 * c.wireCount * (1 / |τ|) * √(1 / |τ|))`. -/
theorem sum_circuitBottomUnforcedAtMostOneCount_blockLiveSet_le {κ τ : Type*}
    [Fintype κ] [DecidableEq κ] [Fintype τ] (c : Circuit signature n t)
    (blockVar : κ → τ → Fin n)
    (hinj : ∀ j₁ t₁ j₂ t₂, blockVar j₁ t₁ = blockVar j₂ t₂ → j₁ = j₂ ∧ t₁ = t₂) :
    (∑ σ : κ → τ, ∑ w : Fin n → Bool,
      (circuitBottomUnforcedAtMostOneCount c (blockLiveSet blockVar σ) w : ℝ)) ≤
      (Fintype.card (κ → τ) : ℝ) * (2 : ℝ) ^ n * (4 * (c.wireCount : ℝ) *
        (1 / (Fintype.card τ : ℝ)) * Real.sqrt (1 / (Fintype.card τ : ℝ))) :=
  sum_card_filter_not_forcedToAtMostOne_blockLiveSet_le c (circuitBottomGates c) blockVar hinj

end Cslib.Circuits.Boolean.WeightedThreshold
