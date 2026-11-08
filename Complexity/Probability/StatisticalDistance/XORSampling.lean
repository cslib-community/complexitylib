/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Probability.StatisticalDistance.XOR
import Complexity.Probability.PMF
import Complexity.Probability.PMF.Uniform

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
samplers [SahaiVadhan2003, §3]. The XOR construction also commutes with images (`xorMix_map`).

## Main definitions

* `Cslib.BitString.parityComplete`: the completion of `j` bits to `j + 1` bits of parity `c`.
* `Cslib.BitString.parityCompleteEquiv`: completion as an equivalence onto the selectors of
  parity `c`.

## Main results

* `Cslib.Probability.PMF.xorMix_map`: naturality of the XOR construction.
* `Cslib.Probability.PMF.uniformOfFintype_map_parityComplete`: completed uniform bits are uniform
  among the selectors of parity `c`.
* `Cslib.Probability.PMF.xorMix_map_uniform`: the XOR construction of two images of uniform seeds is
  an image of uniform selector bits and seeds.

## References

* [A. Sahai, S. Vadhan, *A complete problem for statistical zero knowledge*][SahaiVadhan2003]
-/

@[expose] public section

namespace Cslib.BitString

/-- The completion of `j` bits `r` to the `j + 1` bits of parity `c` extending them: the last bit
is `c ⊕ parity r`. -/
def parityComplete (c : Bool) {j : ℕ} (r : BitString j) : BitString (j + 1) :=
  Fin.snoc r (c ^^ parity j r)

/-- The completion of `r` to parity `c` has parity `c`. -/
theorem parity_parityComplete (c : Bool) {j : ℕ} (r : BitString j) :
    parity (j + 1) (parityComplete c r) = c := by
  rw [parityComplete, parity_snoc]
  cases c <;> cases parity j r <;> rfl

/-- Completion to parity `c` is an equivalence onto the bit strings of parity `c`; the inverse
drops the last bit. -/
def parityCompleteEquiv (c : Bool) (j : ℕ) :
    BitString j ≃ {b : BitString (j + 1) // b ∈ ({b | parity (j + 1) b = c} : Finset _)} where
  toFun r := ⟨parityComplete c r, by simp [parity_parityComplete]⟩
  invFun b := Fin.init b.1
  left_inv r := by simp [parityComplete]
  right_inv b := by
    obtain ⟨b, hb⟩ := b
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
    apply Subtype.ext
    simp only [parityComplete]
    conv_rhs => rw [← Fin.snoc_init_self b]
    congr 1
    rw [← Fin.snoc_init_self b, parity_snoc] at hb
    rw [← hb]
    cases parity j (Fin.init b) <;> cases b (Fin.last j) <;> rfl

end Cslib.BitString

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
    congr 1
    funext b
    rw [← pi_map]
    congr 1
    funext i
    cases b i <;> rfl
  · rw [← pi_map]

/-- Completing uniform bits to parity `c` gives a uniform bit string of parity `c`. -/
theorem uniformOfFintype_map_parityComplete (c : Bool) (j : ℕ)
    (h : ({b : BitString (j + 1) | parity (j + 1) b = c} : Finset _).Nonempty) :
    (uniformOfFintype (BitString j)).map (parityComplete c) = uniformOfFinset _ h := by
  have : Nonempty {b : BitString (j + 1) // b ∈ ({b | parity (j + 1) b = c} : Finset _)} :=
    h.coe_sort
  rw [← uniformOfFintype_finset_map_val, ← uniformOfFintype_map_equiv (parityCompleteEquiv c j),
    PMF.map_comp]
  rfl

/-- **The XOR construction from uniform bits**: on `j + 1` coordinates, the XOR construction of
the images of a uniform seed under `f₀` and `f₁` is the image of `j` uniform selector bits `r` and
`j + 1` uniform seeds `s` under `i ↦ f_{b i} (s i)`, where `b = parityComplete c r`. -/
theorem xorMix_map_uniform {γ α : Type*} [Fintype γ] [Nonempty γ] [Fintype α]
    (f₀ f₁ : γ → α) (j : ℕ) (c : Bool) :
    xorMix ((uniformOfFintype γ).map f₀) ((uniformOfFintype γ).map f₁) (j + 1) c =
      (uniformOfFintype (BitString j × (Fin (j + 1) → γ))).map
        (fun p i => bif parityComplete c p.1 i then f₁ (p.2 i) else f₀ (p.2 i)) := by
  have hne : ({b : BitString (j + 1) | parity (j + 1) b = c} : Finset _).Nonempty :=
    ⟨parityComplete c (fun _ => false), by simp [parity_parityComplete]⟩
  rw [xorMix, dite_eq_left hne, ← uniformOfFintype_map_parityComplete c j hne, PMF.bind_map,
    ← uniformOfFintype_prod, PMF.map_bind]
  congr 1
  funext r
  have hsel : (fun i => bif parityComplete c r i then (uniformOfFintype γ).map f₁
      else (uniformOfFintype γ).map f₀) =
      fun i => (uniformOfFintype γ).map
        (fun y => bif parityComplete c r i then f₁ y else f₀ y) := by
    funext i
    cases parityComplete c r i <;> rfl
  rw [Function.comp_apply, hsel, pi_map, pi_uniformOfFintype, PMF.map_comp]
  rfl

end Cslib.Probability.PMF
