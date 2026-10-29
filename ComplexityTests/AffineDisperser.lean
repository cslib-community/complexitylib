/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Foundations.Combinatorics.AffineDisperser
import Complexity.Foundations.Combinatorics.AffineDisperser.Threshold
import Complexity.Foundations.FieldTheory.Finite.Subfield
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Tactic.NormNum.Prime

/-!
# Affine dispersers from subspace polynomials: clients

These clients instantiate the cube-sum identities, the Moore finite-difference formula and the
covering lemma at small sizes, and apply the independent-sources theorem and the disperser theorem
to concrete Galois fields. The disperser instance takes `F = GF(2 ^ 400)`, whose proper subfields
have at most `2 ^ 200` elements, `r = 100` blocks and `t = 10`; the dimension bound is then
`38100`, below `40000`, the `𝔽₂`-dimension of `F ^ 100`, so the whole space is a non-vacuous
instance.

The explicit disperser is exercised through its ingredients (codes of binary polynomials, the least
irreducible polynomial of degree `1`, the monomial basis of `GF(2 ^ 6)`, the subfield bound in
`GF(2 ^ 35)`, the greedy choice of primes) and at `N = 2 ^ 60`, where it computes the parameters:
`L = 20`, the field degree `23 · 29 · 31 · 37 · 41 · 43 · 47 · 53 · 59` and a threshold below
`N / 10`, so the explicit function is nonconstant on the whole cube. The threshold bound gives the
same for all large `N`.
-/

namespace ComplexityTests.AffineDisperser

open Cslib Cslib.AffineDisperser Cslib.AffineDisperser.Explicit Module

/-! ### Small identities -/

-- One affine form in one Boolean variable, the first Moore determinant, and determinant = permanent
-- in characteristic two on an explicit 3×3 matrix.
example (a b : ZMod 2) (a' u : GaloisField 2 3) :
    (∑ c : Fin 1 → ZMod 2, ∏ _p : Fin 1, (a + ∑ v, c v • b)) = b ∧
      (∑ c : Fin 1 → ZMod 2, (a' + ∑ l, c l • (fun _ => u) l) ^ (2 ^ 1 - 1)) = u ∧
      (!![(1 : ZMod 2), 1, 0; 0, 1, 1; 1, 0, 1]).det =
        (!![(1 : ZMod 2), 1, 0; 0, 1, 1; 1, 0, 1]).permanent :=
  ⟨by rw [sum_cube_prod_affine_eq_permanent (κ := Fin 1) (fun _ => a) (fun _ _ => b)]
      simp [Matrix.permanent_unique],
    by rw [sum_cube_pow_eq_det_mooreMatrix]; simp [mooreMatrix, Matrix.det_unique],
    (!![(1 : ZMod 2), 1, 0; 0, 1, 1; 1, 0, 1]).det_eq_permanent_of_charTwo⟩

theorem strictAnti_three_sub : StrictAnti fun i : Fin 3 => 3 - (i : ℕ) := fun i j hij =>
  show 3 - (j : ℕ) < 3 - (i : ℕ) by have := j.2; have : (i : ℕ) < j := hij; omega

-- The hypotheses of the covering lemma are satisfiable: the identity covers a block set.
example : ∃ ℓ : (Σ j : ({0, 2} : Finset (Fin 3)), Fin (3 - j)) →
      Option (Σ i : ({0, 2} : Finset (Fin 3)), Fin (3 - i)),
    (∀ v, ∃ p, ℓ p = some v) ∧ ∀ p v, ℓ p = some v → (v.1 : Fin 3) ≤ p.1 :=
  ⟨some, fun v => ⟨v, rfl⟩, fun _p _v h => Option.some_injective _ h ▸ le_rfl⟩

-- Counting slots does not exclude `J = {0, 2}` covering `I = {1, 2}` (four slots against three),
-- but the weights do: block `0` cannot serve higher blocks.
example (ℓ : (Σ j : ({0, 2} : Finset (Fin 3)), Fin (3 - j)) →
      Option (Σ i : ({1, 2} : Finset (Fin 3)), Fin (3 - i)))
    (hcov : ∀ v, ∃ p, ℓ p = some v) (hmono : ∀ p v, ℓ p = some v → (v.1 : Fin 3) ≤ p.1) :
    False :=
  absurd (eq_of_covering (fun i => 3 - i) strictAnti_three_sub
    (fun i => show 0 < 3 - (i : ℕ) by have := i.2; omega) {1, 2} {0, 2} rfl ℓ hcov hmono)
    (by decide)

-- Pivot spaces of the whole space `(ZMod 2) ^ 2` add up to its dimension.
example : ∑ i, finrank (ZMod 2) (pivotSpace (⊤ : Submodule (ZMod 2) (Fin 2 → ZMod 2)) i) = 2 := by
  rw [sum_finrank_pivotSpace, finrank_top, Module.finrank_fin_fun]

/-! ### Subfields of `GF(2 ^ n)` -/

theorem finrank_galoisField (n : ℕ) (hn : n ≠ 0) : finrank (ZMod 2) (GaloisField 2 n) = n :=
  GaloisField.finrank 2 hn

-- Proper subfields of `GF(2 ^ 400)` have at most `2 ^ 200` elements.
theorem card_subfield_galoisField_le (K : Subfield (GaloisField 2 400)) (hK : K ≠ ⊤) :
    Nat.card K ≤ 2 ^ 200 :=
  card_subfield_le (finrank_galoisField 400 (by norm_num)) K hK

/-! ### The independent-sources theorem on `GF(2 ^ 5)` -/

-- The whole field (dimension `5`), Moore pairs (`k = 2`): `5 < 5 + (5 - 2)`.
example : ∃ u : Fin 1 → Fin 2 → GaloisField 2 5, (∀ i l, u i l ∈ (⊤ : Submodule (ZMod 2) _)) ∧
    Algebra.trace (ZMod 2) (GaloisField 2 5) (1 * ∏ i, (mooreMatrix (u i)).det) ≠ 0 := by
  have hn := finrank_galoisField 5 (by norm_num)
  refine exists_trace_mul_prod_det_mooreMatrix_ne_zero hn
    (fun K hK => card_subfield_le hn K hK) (fun _ => ⊤) (fun _ => 2) (fun _ => le_rfl)
    (fun _ => ?_) (fun _ => ?_) 0 ?_ one_ne_zero <;>
    simp [finrank_top, hn]

/-! ### The disperser theorem on `GF(2 ^ 400) ^ 100` -/

/-- With `n = 400`, `s = 200`, `r = 100` and `t = 10` the dimension bound is
`100 * 200 + 100 * 101 + 400 * 10 + 400 * 100 / 10 = 38100`, below the dimension `40000` of the
whole space. -/
theorem exists_traceSym_ne_top :
    ∃ x ∈ (⊤ : AffineSubspace (ZMod 2) (Fin 100 → GaloisField 2 400)),
      ∃ y ∈ (⊤ : AffineSubspace (ZMod 2) (Fin 100 → GaloisField 2 400)),
        traceSym (1 : GaloisField 2 400) 100 10 x ≠ traceSym 1 100 10 y := by
  have hn := finrank_galoisField 400 (by norm_num)
  refine exists_traceSym_ne (s := 200) hn card_subfield_galoisField_le one_ne_zero
    (by norm_num) ⊤ ?_
  rw [AffineSubspace.direction_top, finrank_top, Module.finrank_pi_fintype]
  simp [hn]

/-! ### Explicit binary fields -/

theorem polyOfCode_one : polyOfCode 1 = 1 := by
  simpa [polyOfCode_zero, ZMod.val_one] using polyOfCode_two_mul_add 0 1

theorem polyOfCode_two : polyOfCode 2 = Polynomial.X := by
  simpa [polyOfCode_one] using polyOfCode_two_mul_add 1 0

-- The code `3 = 11₂` gives `1 + X`, and the least irreducible polynomial of degree `1` is `X`.
example : polyOfCode 3 = 1 + Polynomial.X ∧ leastIrreducible 1 = Polynomial.X := by
  refine ⟨by simpa [polyOfCode_one, ZMod.val_one] using polyOfCode_two_mul_add 1 1, ?_⟩
  obtain ⟨m, h1, h2, heq, hmin⟩ := exists_code_leastIrreducible one_ne_zero
  have hm : m = 2 := by
    by_contra hm
    exact hmin 2 (by omega) ⟨polyOfCode_two ▸ Polynomial.irreducible_X,
      polyOfCode_two ▸ Polynomial.natDegree_X⟩
  rw [heq, hm, polyOfCode_two]

-- The monomial basis of `GF(2 ^ (2 · 3))` in roots of the least irreducible polynomials of degrees
-- `2` and `3`.
noncomputable example :
    Basis ((i : Fin 2) → Fin (![2, 3] i)) (ZMod 2) (GaloisField 2 (∏ i, ![2, 3] i)) :=
  compositeBasis ![2, 3] (fun i => by fin_cases i <;> norm_num) (by decide)

-- Every prime factor of `35` exceeds `4`, so proper subfields of `GF(2 ^ 35)` have at most
-- `2 ^ (35 / 5) = 2 ^ 7` elements.
example (K : Subfield (GaloisField 2 35)) (hK : K ≠ ⊤) : Nat.card K ≤ 2 ^ 7 :=
  card_subfield_le_of_lt_prime (L := 4) (finrank_galoisField 35 (by norm_num)) (fun q hq hq35 => by
    have : q ∣ 5 * 7 := hq35
    rcases (Nat.Prime.dvd_mul hq).1 this with h | h
    · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).1 h]; norm_num
    · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).1 h]; norm_num) K hK

/-! ### Choosing the primes -/

-- Primes in `(20, 80]` and greedy prime selection with budget `100`.
example :
    primesIoc 20 80 = [23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ∧
      selectBelow 100 [5, 7, 11, 13] = [5, 7] := by
  decide

/-! ### The explicit disperser on `2 ^ 60` bits -/

theorem log_two_pow_sixty : Nat.log 2 (2 ^ 60) = 60 :=
  Nat.log_pow (by norm_num) 60

theorem degreePrimes_two_pow_sixty :
    degreePrimes (2 ^ 60) = [23, 29, 31, 37, 41, 43, 47, 53, 59] := by
  rw [degreePrimes, primeBound, log_two_pow_sixty]
  decide

theorem fieldDegree_two_pow_sixty :
    fieldDegree (2 ^ 60) = 23 * 29 * 31 * 37 * 41 * 43 * 47 * 53 * 59 := by
  rw [fieldDegree_eq_prod, degreePrimes_two_pow_sixty]
  rfl

/-- At `N = 2 ^ 60` the threshold is below `N / 10`. -/
theorem explicitThreshold_two_pow_sixty_lt : explicitThreshold (2 ^ 60) < 2 ^ 60 / 10 := by
  simp only [explicitThreshold, numBlocks, subfieldExp, symDegree, primeBound, log_two_pow_sixty,
    fieldDegree_two_pow_sixty]
  norm_num

theorem finrank_direction_top (N : ℕ) :
    finrank Bool (⊤ : AffineSubspace Bool (BitString N)).direction = N := by
  rw [AffineSubspace.direction_top, finrank_top]
  exact Module.finrank_fin_fun Bool

/-- The explicit function on `2 ^ 60` bits is not constant. -/
theorem exists_explicitDisperser_two_pow_sixty_ne :
    ∃ x y : BitString (2 ^ 60), explicitDisperser (2 ^ 60) x ≠ explicitDisperser (2 ^ 60) y := by
  obtain ⟨x, -, y, -, h⟩ := exists_explicitDisperser_ne (N := 2 ^ 60) ⊤ (by
    rw [finrank_direction_top]
    exact explicitThreshold_two_pow_sixty_lt.trans_le (Nat.div_le_self _ _))
  exact ⟨x, y, h⟩

/-- For all large `N` the explicit function on `N` bits is not constant. -/
theorem eventually_exists_explicitDisperser_ne :
    ∀ᶠ N in Filter.atTop, ∃ x y : BitString N, explicitDisperser N x ≠ explicitDisperser N y := by
  filter_upwards [eventually_explicitThreshold_lt] with N hN
  obtain ⟨x, -, y, -, h⟩ := exists_explicitDisperser_ne ⊤ (by rwa [finrank_direction_top])
  exact ⟨x, y, h⟩

end ComplexityTests.AffineDisperser
