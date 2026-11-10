/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Replication
public import CslibFrontier.Probability.IID
import CslibFrontier.Probability.PMF

/-!
# Output distributions of circuits

A circuit with `n` inputs and `m` outputs is a **sampler**: evaluated on uniformly random inputs, it
produces a distribution on `BitString m`, its output distribution (`Circuit.outputDist`). This is
how circuits encode distributions in the Statistical Difference problem [SahaiVadhan2003, §2.2 and
§3.1]. Running the circuit on the outputs of another samples the image of the first output
distribution (`Circuit.outputDist_comp`), and `k` independent copies on disjoint input blocks sample
`k` independent outputs, laid out in consecutive blocks (`Circuit.outputDist_replicate`).

## Main definitions

* `Cslib.Circuits.Circuit.outputDist`: the output distribution of a circuit on uniform inputs.

## Main results

* `Cslib.Circuits.Circuit.outputDist_comp`: composition maps the output distribution.
* `Cslib.Circuits.Circuit.outputDist_replicate`: independent copies sample independent outputs.

## References

* [A. Sahai, S. Vadhan, *A complete problem for statistical zero knowledge*][SahaiVadhan2003]
-/

@[expose] public section

namespace Cslib.Circuits

open Cslib.Probability.PMF

universe v

variable {σ : Signature.{v}} {n m p : ℕ}

/-- The **output distribution** of a circuit: its outputs on a uniformly random input. -/
noncomputable def Circuit.outputDist (I : Interpretation σ Bool) (C : Circuit σ n m) :
    PMF (BitString m) :=
  (uniformOfFintype (BitString n)).map (C.eval I)

/-- Running `C` on the outputs of `D` samples the image of the output distribution of `D` under
`C`. -/
theorem Circuit.outputDist_comp (I : Interpretation σ Bool) (C : Circuit σ m p)
    (D : Circuit σ n m) : (C.comp D).outputDist I = (D.outputDist I).map (C.eval I) := by
  rw [outputDist, outputDist, PMF.map_comp]
  congr 1 with x : 1
  exact Circuit.eval_comp C D x

/-- **Independent copies of a circuit sample independent copies of its output**, with the `k`
outputs in consecutive blocks (`Cslib.BitString.blocksEquiv`). -/
theorem Circuit.outputDist_replicate (I : Interpretation σ Bool) (C : Circuit σ n m) (k : ℕ) :
    (C.replicate k).outputDist I =
      (iid (C.outputDist I) k).map (BitString.blocksEquiv (m := k) (k := m) (α := Bool)).symm := by
  rw [outputDist, outputDist, iid_map, iid_uniformOfFintype, PMF.map_comp,
    ← uniformOfFintype_map_equiv (BitString.blocksEquiv (m := k) (k := n) (α := Bool)),
    PMF.map_comp]
  congr 1 with x : 1
  apply BitString.blocksEquiv.injective
  simp only [Function.comp_apply, Equiv.apply_symm_apply, eval_replicate,
    BitString.blocksEquiv_apply]
  exact block_blockMap _ _

end Cslib.Circuits
