/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.DepthFive.Schedule

/-!
# The sum over type words

The second trace moment of the `IMM_{n,n}` operator is bounded by a sum over words
`τ : Fin n → Bool` that give every layer a type, `true` for type `𝒟` and `false` for type `𝒩`
[OpenAI, §4][OpenAI2026DepthFive]. The weight of a word is

`n ^ (-w τ) * α ^ (-d_V τ) * β ^ (d_U τ) * ∏ t ∈ N_V τ, (1 + α⁻¹ * n ^ (-h_t))`,

where `w τ` counts the switches of type between consecutive layers, `d_V τ` and `d_U τ` count
the layers of type `𝒟` that are differentiated and multiplied, `N_V τ` is the set of
differentiated layers of type `𝒩`, and `h_t` counts the neighbours of layer `t` of type `𝒩`.

## Main definitions

* `Params.wordWeight`: the weight of a type word.

## References

* [OpenAI, *Homogeneous depth-five lower bounds for iterated matrix
  multiplication*][OpenAI2026DepthFive], §5, word-sum lemma (unrefereed preprint)
-/

@[expose] public section

namespace Cslib.Circuits.DepthFive.Params

variable (p : Params) (τ : Fin p.n → Bool)

/-- The number of switches of a type word: positions whose type differs from the previous one. -/
def switches : ℕ :=
  (Finset.univ.filter fun j : Fin p.n => ∃ i : Fin p.n, (i : ℕ) + 1 = j ∧ τ i ≠ τ j).card

/-- The number of differentiated layers of type `𝒟`. -/
def dV : ℕ := (Finset.univ.filter fun t : Fin p.n => p.isV t ∧ τ t).card

/-- The number of multiplied layers of type `𝒟`. -/
def dU : ℕ := (Finset.univ.filter fun t : Fin p.n => ¬ p.isV t ∧ τ t).card

/-- The number of layers adjacent to layer `t` that have type `𝒩`. For a layer `t` of type `𝒩`
this is the number of internal vertices of `t` whose two incident layers have type `𝒩`. -/
def nbrN (t : Fin p.n) : ℕ :=
  (Finset.univ.filter fun i : Fin p.n =>
    ((i : ℕ) + 1 = t ∨ (t : ℕ) + 1 = i) ∧ τ i = false).card

/-- The weight of a type word [OpenAI, §5][OpenAI2026DepthFive]. -/
noncomputable def wordWeight : ℝ :=
  ((p.n : ℝ)⁻¹) ^ p.switches τ * (p.α⁻¹) ^ p.dV τ * p.β ^ p.dU τ *
    ∏ t ∈ Finset.univ.filter fun t : Fin p.n => p.isV t ∧ τ t = false,
      (1 + p.α⁻¹ * ((p.n : ℝ)⁻¹) ^ p.nbrN τ t)

end Cslib.Circuits.DepthFive.Params
