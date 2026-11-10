/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.DepthFive.Params

/-!
# The balanced layer schedule

The rank lower bound for `IMM_{n,n}` differentiates in `k` of the `n` matrix layers and
multiplies in the other `m = k + s`. The layers are ordered by the word
`V U^{ℓ₁} V U^{ℓ₂} ⋯ V U^{ℓ_k}` with `ℓᵢ = 1 + ⌊i s / k⌋ - ⌊(i - 1) s / k⌋`
[OpenAI, (4.1)][OpenAI2026DepthFive]: the `i`-th differentiated layer, counting from zero, is
layer `2 i + ⌊i s / k⌋`. No two differentiated layers are adjacent, the first layer is
differentiated and the last is multiplied, and every interval of layers is balanced up to a
bounded discrepancy.

## Main definitions

* `Params.isV`: whether a layer is differentiated.
* `Params.layerVar`: the variables of the differentiated layers of `IMM_{n,n}`.

## References

* [OpenAI, *Homogeneous depth-five lower bounds for iterated matrix
  multiplication*][OpenAI2026DepthFive], §4 and (5.6) (unrefereed preprint)
-/

@[expose] public section

namespace Cslib.Circuits.DepthFive.Params

variable (p : Params)

/-- Whether layer `t` is differentiated in the balanced schedule: the `i`-th differentiated layer
is layer `2 * i + i * s / k`. -/
def isV (t : Fin p.n) : Bool :=
  decide (∃ i < p.k, (t : ℕ) = 2 * i + i * p.s / p.k)

/-- The variables of `IMM_{n,n}` that belong to a differentiated layer. Every layer keeps all
its `n ^ 2` variables. -/
def layerVar (x : Fin p.n × Fin p.n × Fin p.n) : Prop := p.isV x.1

instance : DecidablePred p.layerVar := fun x => inferInstanceAs (Decidable (p.isV x.1 = true))

end Cslib.Circuits.DepthFive.Params
