/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.BPP.Derandomization
public import CslibFrontier.Computability.Complexity.HardnessEncoding.PolyTime
import CslibFrontier.Computability.Complexity.Classes.BPP

/-!
# `P = BPP` from exponential worst-case circuit lower bounds

**Impagliazzo–Wigderson** [ImpagliazzoWigderson1997]: if some problem in `E`, decidable in time
`2 ^ O(n)`, needs De Morgan circuits of size `2 ^ (γ n)` for some `γ > 0` at all large lengths
`n`, then `P = BPP`. The proof here follows the route of Sudan, Trevisan and Vadhan
[SudanTrevisanVadhan2001], replacing the XOR lemma by local list decoding:

* the encoded language `Cslib.HardnessEncoding.encodedLanguage L M`, with `M = ⌈40 / γ⌉ + 1`
  (`Cslib.HardnessEncoding.blockFactor`), is the concatenation of a Reed–Muller code over an
  explicit binary field with the Hadamard code, applied to the slices of `L`;
* it is in `E` (`Cslib.HardnessEncoding.encodedLanguage_mem_E`), by a program certified in the
  tidy machine calculus;
* by the reconstruction theorem along a concrete schedule of parameters, it is average-case hard
  for circuits of size `2 ^ ⌊N / c⌋` at all large lengths `N`, with `c = 200 (M + 1)`
  (`Cslib.HardnessEncoding.eventually_isAverageCaseHard_encodedSlice`);
* the Nisan–Wigderson generator then derandomizes `BPP`
  (`Cslib.Complexity.P_eq_BPP_of_isAverageCaseHard`).

The hardness hypothesis is *eventual*: the slices of `L` at all sufficiently large lengths need
`2 ^ (γ n)` gates. The schedule only uses the hard lengths `M b`, multiples of `M`. With a suitable
modification of the schedule, hardness at infinitely many lengths makes the encoded language
average-case hard at infinitely many lengths, and the generator then gives deterministic
simulations of `BPP` that are correct for infinitely many input lengths; that infinitely-often
variant is not formalized here.

## Main results

* `Cslib.Complexity.BPP_subset_P_of_eventually_two_pow_le_complexity`: `BPP ⊆ P` from
  exponential worst-case hardness in `E`.
* `Cslib.Complexity.P_eq_BPP_of_eventually_two_pow_le_complexity`: **`P = BPP` from exponential
  worst-case hardness in `E`**.

## References

* [R. Impagliazzo, A. Wigderson, *P = BPP if E requires exponential circuits: Derandomizing the
  XOR lemma*][ImpagliazzoWigderson1997]
* [M. Sudan, L. Trevisan, S. Vadhan, *Pseudorandom generators without the XOR lemma*]
  [SudanTrevisanVadhan2001]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09], Chapters 19
  and 20
-/

@[expose] public section

namespace Cslib.Complexity

open Filter Turing.MultiTapeTM Cslib.Circuits Cslib.Circuits.Boolean Cslib.HardnessEncoding

/-- **`BPP ⊆ P` from exponential worst-case hardness in `E`.** If some problem `L` in `E` has
slices that need De Morgan circuits of size `2 ^ (γ n)` at all large lengths `n`, for some
`γ > 0`, then every problem in `BPP enc` is in `P enc`, for every encoding `enc` of instances. -/
theorem BPP_subset_P_of_eventually_two_pow_le_complexity {L : Language Bool}
    (hL : (L : Set (List Bool)) ∈ E encBits) {γ : ℝ} (hγ : 0 < γ)
    (hard : ∀ᶠ n : ℕ in atTop,
      (2 : ℝ) ^ (γ * n) ≤ complexity interpretation (single (L.slice n)))
    {α : Type} (enc : α ↪ List Bool) : BPP enc ⊆ P enc :=
  BPP_subset_P_of_isAverageCaseHard (HardnessEncoding.encodedLanguage_mem_E hL (blockFactor γ))
    (c := hardnessDivisor γ) (by unfold hardnessDivisor; positivity)
    (by simpa only [slice_encodedLanguage] using eventually_isAverageCaseHard_encodedSlice hγ hard)
    enc

/-- **`P = BPP` from exponential worst-case hardness in `E`** [ImpagliazzoWigderson1997],
[SudanTrevisanVadhan2001]. If some problem `L` in `E` has slices that need De Morgan circuits of
size `2 ^ (γ n)` at all large lengths `n`, for some `γ > 0`, then `P enc = BPP enc` for every
encoding `enc` of instances. -/
theorem P_eq_BPP_of_eventually_two_pow_le_complexity {L : Language Bool}
    (hL : (L : Set (List Bool)) ∈ E encBits) {γ : ℝ} (hγ : 0 < γ)
    (hard : ∀ᶠ n : ℕ in atTop,
      (2 : ℝ) ^ (γ * n) ≤ complexity interpretation (single (L.slice n)))
    {α : Type} (enc : α ↪ List Bool) : P enc = BPP enc :=
  P_subset_BPP.antisymm (BPP_subset_P_of_eventually_two_pow_le_complexity hL hγ hard enc)

end Cslib.Complexity
