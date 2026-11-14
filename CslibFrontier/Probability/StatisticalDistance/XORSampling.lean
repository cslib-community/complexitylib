/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.BitString.Parity
public import CslibFrontier.Probability.StatisticalDistance.XOR
import CslibFrontier.Probability.PMF
import CslibFrontier.Probability.PMF.Uniform

/-!
# Sampling the XOR construction from uniform bits

The XOR construction `xorMix p₀ p₁ k c` draws its selector uniformly among the bit strings of
parity `c`. A sampler that only has uniform bits draws `k - 1` of them, `r`, and completes them to
`parityComplete c r = Fin.snoc r (c ⊕ parity r)`, the unique string of parity `c` extending `r`.
This is a bijection between `BitString (k - 1)` and the selectors of parity `c`
(`parityCompleteEquiv`), so the completed selector is uniform among them
(`uniformOfFintype_map_parityComplete`). When `p₀` and `p₁` are themselves images of uniform seeds
under `f₀` and `f₁`, the whole construction is the image of uniform selector bits and seeds
(`xorMix_map_uniform`). This is the form in which a circuit computes the XOR construction of two
samplers [SahaiVadhan2003, Lemma 3.5]. The XOR construction also commutes with images
(`xorMix_map`).

## Main definitions

* `Cslib.BitString.parityComplete` and `Cslib.BitString.parityCompleteEquiv`, used below, are
  defined in `CslibFrontier/Foundations/Data/BitString/Parity/Complete.lean`.

## Main results

* `Cslib.Probability.PMF.xorMix_map`: naturality of the XOR construction.
* `Cslib.Probability.PMF.uniformOfFintype_map_parityComplete`, used below, is proved in
  `CslibFrontier/Probability/BitString/Parity.lean`.
* `Cslib.Probability.PMF.xorMix_map_uniform`: the XOR construction of two images of uniform seeds is
  an image of uniform selector bits and seeds.

## References

* [A. Sahai, S. Vadhan, *A complete problem for statistical zero knowledge*][SahaiVadhan2003]
-/

public section

namespace Cslib.Probability.PMF

open BitString

/-- **Naturality of the XOR construction**: mapping both distributions by `g` maps every
coordinate of the construction by `g`. -/
theorem xorMix_map {α β : Type*} [Fintype α] [Fintype β] (p₀ p₁ : PMF α) (g : α → β) (k : ℕ)
    (c : Bool) :
    xorMix (p₀.map g) (p₁.map g) k c = (xorMix p₀ p₁ k c).map (fun x i => g (x i)) := by
  unfold xorMix
  split_ifs with h
  · rw [PMF.map_bind]
    congr 1 with b : 1
    rw [← pi_map]
    congr 1 with i : 1
    cases b i <;> rfl
  · rw [← pi_map]

/-- **The XOR construction from uniform bits**: on `j + 1` coordinates, the XOR construction of
the images of a uniform seed under `f₀` and `f₁` is the image of `j` uniform selector bits `r` and
`j + 1` uniform seeds `s` under `i ↦ f_{b i} (s i)`, where `b = parityComplete c r`. -/
theorem xorMix_map_uniform {γ α : Type*} [Fintype γ] [Nonempty γ] [Fintype α]
    (f₀ f₁ : γ → α) (j : ℕ) (c : Bool) :
    xorMix ((uniformOfFintype γ).map f₀) ((uniformOfFintype γ).map f₁) (j + 1) c =
      (uniformOfFintype (BitString j × (Fin (j + 1) → γ))).map
        (fun p i => bif parityComplete c p.1 i then f₁ (p.2 i) else f₀ (p.2 i)) := by
  have hne : ({b : BitString (j + 1) | parity (j + 1) b = c} : Finset _).Nonempty :=
    parity_fiber_nonempty (Nat.succ_pos j) c
  rw [xorMix, dite_eq_left hne, ← uniformOfFintype_map_parityComplete c j hne, PMF.bind_map,
    ← uniformOfFintype_prod, PMF.map_bind]
  congr 1 with r : 1
  have hsel : (fun i => bif parityComplete c r i then (uniformOfFintype γ).map f₁
      else (uniformOfFintype γ).map f₀) =
      fun i => (uniformOfFintype γ).map
        (fun y => bif parityComplete c r i then f₁ y else f₀ y) := by
    funext i
    cases parityComplete c r i <;> rfl
  rw [Function.comp_apply, hsel, pi_map, pi_uniformOfFintype, PMF.map_comp]
  rfl

end Cslib.Probability.PMF
