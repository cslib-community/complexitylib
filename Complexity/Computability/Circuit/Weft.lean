/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Depth

/-!
# The weft of a circuit

A gate is *large* when it has more than two arguments. The weft of a circuit is the largest number
of large gates on a path to an output [Cygan et al., Section 13.3][CyganEtAl2015]. It is the depth
with costs (`Cslib.Circuits.Circuit.depthWith`) in which a large gate costs one and every other gate
costs nothing. Weft and depth bound the circuits of the classes `W[t]` of the W-hierarchy
(`Cslib.Complexity.W`).

## Main definitions

* `Cslib.Circuits.largeGateCost`: cost one for a gate with more than two arguments.
* `Cslib.Circuits.Circuit.weft`: the largest number of large gates on a path to an output.

## Main results

* `Cslib.Circuits.Circuit.weft_le_depth`: the weft is at most the depth.
* `Cslib.Circuits.Circuit.weft_le_iff`: a bound on the weft is a bound on every output.

## References

* [M. Cygan et al., *Parameterized Algorithms*, Section 13.3][CyganEtAl2015]
-/

@[expose] public section

namespace Cslib.Circuits

variable {σ : Signature} {n m : ℕ}

/-- The cost of a gate for the weft: one for a large gate, of more than two arguments, and zero
otherwise. -/
def largeGateCost (σ : Signature) (op : σ.Op) : ℕ :=
  if 2 < σ.Arity op then 1 else 0

/-- A gate costs at most one for the weft. -/
theorem largeGateCost_le_one (op : σ.Op) : largeGateCost σ op ≤ 1 := by
  unfold largeGateCost
  split <;> omega

/-- **The weft of a circuit**: the largest number of large gates, of more than two arguments, on a
path to an output [Cygan et al., Section 13.3][CyganEtAl2015]. -/
def Circuit.weft (c : Circuit σ n m) : ℕ :=
  c.depthWith (largeGateCost σ)

/-- The weft of a circuit is at most its depth. -/
theorem Circuit.weft_le_depth (c : Circuit σ n m) : c.weft ≤ c.depth :=
  c.depthWith_le_depth largeGateCost_le_one

/-- A circuit has weft at most `t` exactly when all its outputs do. -/
theorem Circuit.weft_le_iff (c : Circuit σ n m) {t : ℕ} :
    c.weft ≤ t ↔ ∀ j, c.program.wireDepthsWith (largeGateCost σ) (c.outputs j) ≤ t :=
  c.depthWith_le_iff _

end Cslib.Circuits
