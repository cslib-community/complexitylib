/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.Circuit.Boolean.AffineDisperser
public import Complexity.Computability.Complexity.Classes.P.Slices
public import Complexity.Computability.Complexity.AffineDisperser.PolyTime
public import Complexity.Foundations.Combinatorics.AffineDisperser.Threshold
public import Cslib.Computability.Languages.Slice

/-!
# A function in `P` with `B₂` circuit complexity `3.5 N - O(N / log N)`

Mishra and Santhanam prove that every circuit over the full binary basis `B₂` computing an affine
disperser for dimension `d` on `N` bits has at least `3.5 N - 7 d` gates
[MishraSanthanam2026, Theorem 4.1]
(`Cslib.Circuits.Boolean.AffineDisperser.seven_mul_le_two_mul_size_add`).
The explicit disperser of Ben-Sasson and Kopparty's construction
(`Cslib.AffineDisperser.explicitDisperser`) is an affine disperser for dimension
`explicitThreshold N + 1` (`Cslib.AffineDisperser.isAffineDisperser_explicitDisperser`) and is
computable in polynomial time (`Cslib.AffineDisperser.setOf_explicitDisperser_mem_P`). Together:

* every `B₂` circuit computing `explicitDisperser N` has at least `3.5 N - 7 (d(N) + 1)` gates,
  for every `N`, where `d(N) = explicitThreshold N` is
  `N - r n + r * max (r + 1) s + r * (r + 1) + n t + ⌊n r / t⌋`
  (`Cslib.AffineDisperser.seven_mul_le_two_mul_size_add_explicitThreshold`);
* since `(⌊log₂ N⌋ + 1) d(N) ≤ 6 N` for all large `N`, every such circuit has at least
  `3.5 N - 42 N / (⌊log₂ N⌋ + 1) - 7` gates for all large `N`
  (`Cslib.AffineDisperser.eventually_le_size_of_computes_explicitDisperser`);
* hence the language `Cslib.AffineDisperser.explicitDisperserLanguage`, whose slice at length `N`
  is `explicitDisperser N`, is in `P` and needs `3.5 N - O(N / log N)` gates over `B₂`
  (`Cslib.AffineDisperser.exists_mem_P_eventually_le_size`).

The circuits are cslib's `Circuit (fullSignature 2 Bool) N 1`: every gate applies an arbitrary
binary Boolean operation or is a constant, and the size counts gates, constants included, but not
inputs. Mishra and Santhanam let circuits read constants for free, so the bound holds here a
fortiori.

The lower-order term is far from the best known. Our threshold is only `O(N / log N)`
(`Cslib.AffineDisperser.isBigO_explicitThreshold`), because the field degree is a product of small
primes so that the irreducible polynomials can be found by exhaustive search. Li's explicit
affine dispersers work for dimension `O(log N)` [Li2023], and with them the same theorem gives
`3.5 N - O(log N)`. The bound here exceeds `3 N` only once the lower-order term `7 (d(N) + 1)`
is below `N / 2`, as it is for instance at `N = 2 ^ 70`.

## Main definitions

* `Cslib.AffineDisperser.explicitDisperserLanguage`: the language of the explicit disperser.

## Main results

* `Cslib.AffineDisperser.seven_mul_le_two_mul_size_add_explicitThreshold`: the bound
  `7 N ≤ 2 |C| + 14 (explicitThreshold N + 1)`, for every `N`.
* `Cslib.AffineDisperser.eventually_le_size_of_computes_explicitDisperser`: the bound
  `3.5 N - 42 N / (⌊log₂ N⌋ + 1) - 7 ≤ |C|`, for all large `N`.
* `Cslib.AffineDisperser.explicitDisperserLanguage_mem_P`: the language is in `P`.
* `Cslib.AffineDisperser.exists_mem_P_eventually_le_size`: some language in `P` needs
  `3.5 N - 42 N / (⌊log₂ N⌋ + 1) - 7` gates over `B₂` at all large lengths `N`.

## References

* [O. S. Mishra and R. Santhanam, *An Explicit 3.5n − o(n) Size Lower Bound against General
  Boolean Circuits*][MishraSanthanam2026]
* [E. Ben-Sasson, S. Kopparty, *Affine dispersers from subspace polynomials*][BenSassonKopparty2012]
* [X. Li, *Two source extractors for asymptotically optimal entropy, and (many) more*][Li2023]
-/

@[expose] public section

namespace Cslib.AffineDisperser

open Cslib.Circuits Filter Turing.MultiTapeTM

/-- **Mishra and Santhanam's bound for the explicit disperser**
[MishraSanthanam2026, Theorem 4.1], with the exact lower-order term: every circuit over the full
binary basis `B₂` computing `explicitDisperser N` has at least `3.5 N - 7 (explicitThreshold N + 1)`
gates, stated without subtraction. -/
theorem seven_mul_le_two_mul_size_add_explicitThreshold {N : ℕ}
    (C : Circuit (fullSignature 2 Bool) N 1)
    (hC : C.Computes fullInterpretation (single (explicitDisperser N))) :
    7 * N ≤ 2 * C.size + 14 * (explicitThreshold N + 1) :=
  Boolean.AffineDisperser.seven_mul_le_two_mul_size_add (isAffineDisperser_explicitDisperser N) C
    hC

/-- **The explicit disperser needs `3.5 N - O(N / log N)` gates over `B₂`**: for all large `N`,
every circuit over the full binary basis computing `explicitDisperser N` has at least
`3.5 N - 42 N / (⌊log₂ N⌋ + 1) - 7` gates. -/
theorem eventually_le_size_of_computes_explicitDisperser :
    ∀ᶠ N in atTop, ∀ C : Circuit (fullSignature 2 Bool) N 1,
      C.Computes fullInterpretation (single (explicitDisperser N)) →
        7 / 2 * (N : ℝ) - 42 * N / (Nat.log 2 N + 1) - 7 ≤ C.size := by
  filter_upwards [eventually_explicitThreshold_le] with N hN C hC
  have h : (7 * N : ℝ) ≤ 2 * C.size + 14 * (explicitThreshold N + 1) := by
    exact_mod_cast seven_mul_le_two_mul_size_add_explicitThreshold C hC
  have hl : (0 : ℝ) < Nat.log 2 N + 1 := by positivity
  have hT : (explicitThreshold N : ℝ) ≤ 6 * N / (Nat.log 2 N + 1) := by
    rw [le_div_iff₀ hl, mul_comm]
    exact_mod_cast hN
  have h42 : 42 * (N : ℝ) / (Nat.log 2 N + 1) = 7 * (6 * N / (Nat.log 2 N + 1)) := by ring
  linarith

/-- The language of the explicit disperser: the bit lists `x` with
`explicitDisperser x.length x = true`. Its slice at length `N` is `explicitDisperser N`. -/
noncomputable def explicitDisperserLanguage : Language Bool :=
  Language.ofSlices explicitDisperser

@[simp]
theorem slice_explicitDisperserLanguage (N : ℕ) :
    explicitDisperserLanguage.slice N = explicitDisperser N :=
  Language.slice_ofSlices _ N

/-- **The language of the explicit disperser is in `P`**, with words encoded as themselves. -/
theorem explicitDisperserLanguage_mem_P :
    (explicitDisperserLanguage : Set (List Bool)) ∈ Complexity.P encBits :=
  Complexity.ofSlices_mem_P computableInPolyTime_explicitDisperser

/-- **An explicit function in `P` with `B₂` circuit complexity `3.5 N - O(N / log N)`**, after
[MishraSanthanam2026]: some language over `Bool` in `P` (the language of the explicit disperser)
has, at every large length `N`, no circuit over the full binary basis with fewer than
`3.5 N - 42 N / (⌊log₂ N⌋ + 1) - 7` gates. -/
theorem exists_mem_P_eventually_le_size :
    ∃ L : Language Bool, (L : Set (List Bool)) ∈ Complexity.P encBits ∧
      ∀ᶠ N in atTop, ∀ C : Circuit (fullSignature 2 Bool) N 1,
        C.Computes fullInterpretation (single (L.slice N)) →
          7 / 2 * (N : ℝ) - 42 * N / (Nat.log 2 N + 1) - 7 ≤ C.size :=
  ⟨explicitDisperserLanguage, explicitDisperserLanguage_mem_P, by
    simpa only [slice_explicitDisperserLanguage] using
      eventually_le_size_of_computes_explicitDisperser⟩

end Cslib.AffineDisperser
