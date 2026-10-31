/-
Copyright (c) 2026 András Z. Salamon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: András Z. Salamon
-/

module
-- upstream: candidate

public import Complexity.Computability.Communication.Functions
public import Complexity.Foundations.BooleanAnalysis.HadamardRectangles
public import Complexity.Foundations.Data.Code.Hadamard
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
public import Complexity.Computability.Communication.Nondeterministic.Basic

/-!
# Nondeterministic complexity of equality, disjointness and inner product

Bounds on `Nondeterministic.ecomplexityFun` for the standard functions on `v`-bit strings:

* equality: `N¹(EQ_v) = v` [Kushilevitz and Nisan, Example 2.5][KushilevitzNisan1997], where the
  lower bound is the fooling set of diagonal pairs of their Example 1.21; the upper bound here is
  the cover by the `2^v` diagonal singletons. Deterministically one more bit is needed, to announce
  the answer: `Cslib.Communication.ecomplexityFun_equality` gives `v + 1` for `v ≥ 1` (see the
  module `Nondeterministic.Basic` on conventions);
* disjointness: `N¹(DISJ_v) = v`, from the fooling set of complementary pairs
  [Kushilevitz and Nisan, Example 1.23][KushilevitzNisan1997] and the cover by the rectangles
  `{x ⊆ w} × {y ⊆ wᶜ}`, so `N⁰(NDISJ_v) = v` for its negation;
* inner product modulo two: `N¹(IP_v) ≥ v - 1` and `N⁰(IP_v) ≥ v`. A rectangle on which the inner
  product is constant has at most `2^v` pairs. The matrix `(-1)^(x ⬝ᵥ y)` is a `2^v × 2^v` Hadamard
  matrix, and the inner product is constant on a rectangle exactly when this matrix is, so this is
  the final statement of Lindsey's lemma [Jukna, Appendix A, p. 579][Jukna2012]: no `a × b`
  submatrix of an `n × n` Hadamard matrix with `a b > n` is monochromatic
  (`BitString.card_mul_le_two_pow_of_dotProduct_eq`; this is the formal proof, via the bound on
  signed sums). Alternatively, for the value `0` the bound is
  [Kushilevitz and Nisan, Example 1.25][KushilevitzNisan1997], by linear algebra over `𝔽₂`, and the
  value `1` reduces to it by translating the two sides of the rectangle by one of their elements,
  after which the inner product is `0` on it; this argument is not formalised here. Meanwhile the
  inner product is `1` on `(4^v - 2^v)/2` pairs and `0` on `(4^v + 2^v)/2` pairs. So
  `C¹(IP_v) ≥ (2^v - 1)/2` and `C⁰(IP_v) ≥ (2^v + 1)/2`, which in the unrounded convention of
  Kushilevitz and Nisan give, for `v ≥ 1`, `N¹(IP_v) ≥ log₂ (2^v - 1) - 1` and `N⁰(IP_v) > v - 1`.

The deterministic `Cslib.Communication.ecomplexityFun_equality` has the same final name as
`Cslib.Communication.Nondeterministic.ecomplexityFun_equality`; with both namespaces open, write
`Nondeterministic.ecomplexityFun_equality` to avoid an ambiguous name.

## Main results

* `Cslib.Communication.Nondeterministic.ecomplexityFun_equality`
* `Cslib.Communication.Nondeterministic.ecomplexityFun_disjointness`
* `Cslib.Communication.Nondeterministic.ecomplexityFun_not_disjointness`
* `Cslib.Communication.Nondeterministic.HasCover.card_dotProduct_le`
* `Cslib.Communication.Nondeterministic.le_ecomplexityFun_true_dotProduct`
* `Cslib.Communication.Nondeterministic.le_ecomplexityFun_false_dotProduct`

## References

* [S. Jukna, *Boolean Function Complexity: Advances and Frontiers*][Jukna2012]
* [E. Kushilevitz, N. Nisan, *Communication Complexity*][KushilevitzNisan1997]
-/

@[expose] public section

namespace Cslib.Communication

namespace Nondeterministic

open Finset

variable {v : ℕ}

/-! ### Equality and disjointness -/

/-- `N¹(EQ_v) = v`: the `2 ^ v` diagonal pairs form a fooling set, and the `2 ^ v` diagonal
singletons `{w} × {w}` form a `1`-cover. -/
theorem ecomplexityFun_equality (v : ℕ) :
    ecomplexityFun true (equality : BitString v → BitString v → Bool) Set.univ Set.univ = v := by
  refine le_antisymm (ecomplexityFun_le_iff.mpr
    ⟨fun w => ({w}, {w}), isCover_fun_iff.mpr ⟨fun w x _ hx y _ hy => ?_, fun x _ y _ h => ?_⟩⟩) ?_
  · simp only [Set.mem_singleton_iff] at hx hy
    simp [equality, hx, hy]
  · simp only [equality, decide_eq_true_eq] at h
    exact ⟨x, rfl, h.symm⟩
  · exact le_ecomplexityFun_of_isFoolingSet (isFoolingSet_equality univ) (by simp)
      (by rw [card_image_of_injective _ fun x y h => congrArg Prod.fst h, card_univ,
        BitString.card])

/-- `N¹(DISJ_v) = v`: the `2 ^ v` complementary pairs form a fooling set, and the rectangles
`{x ⊆ w} × {y ⊆ wᶜ}` for the `2 ^ v` sets `w` form a `1`-cover. -/
theorem ecomplexityFun_disjointness (v : ℕ) :
    ecomplexityFun true (disjointness : BitString v → BitString v → Bool) Set.univ Set.univ =
      v := by
  refine le_antisymm (ecomplexityFun_le_iff.mpr
    ⟨fun w => ({x | ∀ i, x i = true → w i = true}, {y | ∀ i, y i = true → w i = false}),
      isCover_fun_iff.mpr ⟨fun w x _ hx y _ hy => ?_, fun x _ y _ h => ?_⟩⟩) ?_
  · simp only [Set.mem_ofPred_eq] at hx hy
    simp only [disjointness, decide_eq_true_eq, Bool.and_eq_false_iff]
    intro i
    cases hxi : x i
    · simp
    · cases hyi : y i
      · simp
      · simpa [hx i hxi] using hy i hyi
  · simp only [disjointness, decide_eq_true_eq, Bool.and_eq_false_iff] at h
    refine ⟨x, fun i hi => hi, fun i hi => ?_⟩
    simpa [hi] using h i
  · exact le_ecomplexityFun_of_isFoolingSet (isFoolingSet_disjointness univ) (by simp)
      (by rw [card_image_of_injective _ fun x y h => congrArg Prod.fst h, card_univ,
        BitString.card])

/-- `N⁰(NDISJ_v) = N¹(DISJ_v) = v`. -/
theorem ecomplexityFun_not_disjointness (v : ℕ) :
    ecomplexityFun false (fun a b : BitString v => !disjointness a b) Set.univ Set.univ = v := by
  rw [ecomplexityFun_not, Bool.not_false, ecomplexityFun_disjointness]

/-! ### Inner product -/

/-- A `z`-cover of the inner product by `2 ^ k` rectangles covers at most `2 ^ k * 2 ^ v` pairs. -/
theorem HasCover.card_dotProduct_le {k : ℕ} {z : Bool}
    (hk : HasCover z (fun (x y : BitString v) b => x ⬝ᵥ y = b) Set.univ Set.univ k) :
    #{q : BitString v × BitString v | q.1 ⬝ᵥ q.2 = z} ≤ 2 ^ k * 2 ^ v := by
  have h : #{q ∈ (univ : Finset (BitString v)) ×ˢ univ | q.1 ⬝ᵥ q.2 = z} ≤ 2 ^ k * 2 ^ v :=
    HasCover.card_le_two_pow_mul
      (fun S _ T _ h => by simpa using BitString.card_mul_le_two_pow_of_dotProduct_eq S T z h)
      (by simpa only [coe_univ] using hk)
  rwa [univ_product_univ] at h

/-- The inner product is `1` on `(4^v - 2^v)/2` pairs. -/
private theorem two_mul_card_dotProduct_eq_true_add_two_pow :
    2 * #{q : BitString v × BitString v | q.1 ⬝ᵥ q.2 = true} + 2 ^ v = 2 ^ v * 2 ^ v := by
  simpa using BitString.two_mul_card_dotProduct_eq_true_add_two_pow (ι := Fin v)

/-- The inner product is `1` or `0` on all `4^v` pairs. -/
private theorem card_dotProduct_eq_true_add_card_dotProduct_eq_false :
    #{q : BitString v × BitString v | q.1 ⬝ᵥ q.2 = true} +
      #{q : BitString v × BitString v | q.1 ⬝ᵥ q.2 = false} = 2 ^ v * 2 ^ v := by
  have := card_filter_add_card_filter_not (s := univ)
    fun q : BitString v × BitString v => q.1 ⬝ᵥ q.2 = true
  simpa [Fintype.card_fun, BitString] using this

/-- `N¹(IP_v) ≥ v - 1`: for `v ≥ 2`, more than `2^(v-2)` rectangles are needed, and for `v ≤ 1`
the bound is `0`. -/
theorem le_ecomplexityFun_true_dotProduct (v : ℕ) :
    ((v - 1 : ℕ) : ℕ∞) ≤
      ecomplexityFun true (fun x y : BitString v => x ⬝ᵥ y) Set.univ Set.univ := by
  rcases Nat.lt_or_ge v 2 with hv | hv
  · simp [show v - 1 = 0 by omega]
  refine le_ecomplexityFun_iff.mpr fun k hk => ?_
  have hT := hk.card_dotProduct_le
  have hcount := two_mul_card_dotProduct_eq_true_add_two_pow (v := v)
  norm_cast
  by_contra! hlt
  have hk4 : 2 ^ k * 4 ≤ 2 ^ v := by
    rw [show 2 ^ k * 4 = 2 ^ (k + 2) by ring]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hN : 4 ≤ 2 ^ v := (Nat.pow_le_pow_right (by norm_num) hv : 2 ^ 2 ≤ 2 ^ v)
  nlinarith

/-- `N⁰(IP_v) ≥ v`: more than `2^(v-1)` rectangles are needed. -/
theorem le_ecomplexityFun_false_dotProduct (v : ℕ) :
    (v : ℕ∞) ≤ ecomplexityFun false (fun x y : BitString v => x ⬝ᵥ y) Set.univ Set.univ := by
  refine le_ecomplexityFun_iff.mpr fun k hk => ?_
  have hF := hk.card_dotProduct_le
  have hcount := two_mul_card_dotProduct_eq_true_add_two_pow (v := v)
  have hsum := card_dotProduct_eq_true_add_card_dotProduct_eq_false (v := v)
  norm_cast
  by_contra! hlt
  have hk2 : 2 ^ k * 2 ≤ 2 ^ v := by
    rw [← pow_succ]
    exact Nat.pow_le_pow_right (by norm_num) hlt
  have hN : 0 < 2 ^ v := by positivity
  nlinarith

end Nondeterministic

end Cslib.Communication
