/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Parameterized

/-!
# Hardness under fpt-reductions

A parameterized problem `B` is hard for a parameterized class `𝒞` when every problem of `𝒞`, with
any encoding and parameter, fpt-reduces to `B` (`FPTReducible`). This is the parameterized
counterpart of `PolyTimeHard`. `W[t]`-hardness (`WHard t`) and `W[P]`-hardness (`WPHard`) are its
instances, so the lemmas below apply to them through dot notation.

`FPTHard` is stated directly rather than as an instance of `HardUnder`, whose class and
reducibility are indexed by the encoding alone. Expressing it through `HardUnder` would mean pairing
each problem with its parameter (problem type `(α → ℕ) × Set α`), and every statement would then
carry the pair instead of separate parameter and problem arguments.

## Main definitions

* `Cslib.Complexity.FPTHard`: hardness for a parameterized class under fpt-reductions.

## Main results

* `Cslib.Complexity.FPTHard.trans`: hardness transfers along fpt-reductions.
* `Cslib.Complexity.FPTHard.mono`: hardness for a class gives hardness for each subclass.
* `Cslib.Complexity.FPTHard.subset_FPT`: a `𝒞`-hard problem in `FPT` puts `𝒞` in `FPT`.

## References

* [M. Cygan et al., *Parameterized Algorithms*, Chapter 13][CyganEtAl2015]
-/

@[expose] public section

namespace Cslib.Complexity

/-- `B` is **hard for the parameterized class `𝒞` under fpt-reductions**: every problem of `𝒞`,
with any encoding `encA` and parameter `κA`, fpt-reduces to `B`. -/
def FPTHard (𝒞 : ∀ {α : Type}, (α ↪ List Bool) → (α → ℕ) → Set (Set α)) {β : Type}
    (enc : β ↪ List Bool) (κ : β → ℕ) (B : Set β) : Prop :=
  ∀ ⦃α : Type⦄ (encA : α ↪ List Bool) (κA : α → ℕ) (A : Set α), A ∈ 𝒞 encA κA →
    FPTReducible encA enc κA κ A B

namespace FPTHard

variable {𝒞 𝒟 : ∀ {α : Type}, (α ↪ List Bool) → (α → ℕ) → Set (Set α)} {α β : Type}
  {encA : α ↪ List Bool} {encB : β ↪ List Bool} {κA : α → ℕ} {κB : β → ℕ} {A : Set α} {B : Set β}

/-- Hardness transfers along fpt-reductions. -/
theorem trans (hB : FPTHard 𝒞 encB κB B) (h : FPTReducible encB encA κB κA B A) :
    FPTHard 𝒞 encA κA A :=
  fun _ _ _ _ hC => (hB _ _ _ hC).trans h

/-- Hardness for a class gives hardness for each of its subclasses. -/
theorem mono (h𝒟𝒞 : ∀ {γ : Type} (enc : γ ↪ List Bool) (κ : γ → ℕ), 𝒟 enc κ ⊆ 𝒞 enc κ)
    (hB : FPTHard 𝒞 encB κB B) : FPTHard 𝒟 encB κB B :=
  fun _ encC κC _ hC => hB _ _ _ (h𝒟𝒞 encC κC hC)

/-- **A `𝒞`-hard problem in `FPT` puts `𝒞` in `FPT`.** -/
theorem subset_FPT (hB : FPTHard 𝒞 encB κB B) (hFPT : B ∈ FPT encB κB) :
    𝒞 encA κA ⊆ FPT encA κA :=
  fun _ hA => (hB _ _ _ hA).mem_FPT hFPT

end FPTHard

end Cslib.Complexity
