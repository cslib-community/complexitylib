/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.AffineDisperser

/-!
# A function in `P` with `B₂` circuit complexity `3.5 N - O(N / log N)`: clients

The bridge from affine subspaces to `Cslib.BitString.IsAffineDisperser` is exercised on the
zero extension `BitString d → BitString d'`, whose image has dimension `d`. The explicit disperser
on `2 ^ 70` bits is an affine disperser for a dimension below `N / 14`, so it is nonconstant on the
image of the zero extension, and every circuit over `B₂` computing it, and one exists, has more
than `3 · 2 ^ 70` gates. The asymptotic bound and the language in `P` are restated through their
headline theorems.

The multiplication table of the explicit field at `N = 5915`, the least length whose field degree
is a product of two primes (`35 = 5 · 7`), is checked by evaluation: the least-code irreducible
polynomials of degrees `5` and `7` are `X ^ 5 + X ^ 2 + 1` and `X ^ 7 + X + 1`, `1` is a unit,
multiplication is commutative and associative on pseudorandom elements, `a ^ (2 ^ 35 - 1) = 1` for
a pseudorandom `a ≠ 0` while `a ^ (2 ^ 5 - 1) ≠ 1`, and the trace of `1` is `35 mod 2 = 1`.
-/

namespace ComplexityTests.AffineDisperserCorollary

open Cslib Cslib.AffineDisperser Cslib.AffineDisperser.Explicit Cslib.Circuits Module
  Turing.MultiTapeTM

/-! ### Affine maps and affine subspaces -/

-- The image of the zero extension `BitString 2 → BitString 5` is an affine subspace of
-- dimension `2`, and its linear part is the zero extension itself.
example (x : BitString 2) :
    finrank Bool ((⊤ : AffineSubspace Bool (BitString 2)).map
      (BitString.isAffine_zeroExtend (d := 2) (d' := 5)).toAffineMap).direction = 2 ∧
    (BitString.isAffine_zeroExtend (d := 2) (d' := 5)).linearMap x = BitString.zeroExtend x := by
  refine ⟨?_, ?_⟩
  · rw [BitString.IsAffine.finrank_direction_map_top _
      (BitString.zeroExtend_injective (by norm_num)), Module.finrank_fin_fun]
  · rw [BitString.IsAffine.linearMap_apply,
      show (BitString.zeroExtend (0 : BitString 2) : BitString 5) = 0 by
        funext i; simp [BitString.zeroExtend], add_zero]

/-! ### The explicit disperser on `2 ^ 70` bits -/

theorem log_two_pow_seventy : Nat.log 2 (2 ^ 70) = 70 :=
  Nat.log_pow (by norm_num) 70

theorem degreePrimes_two_pow_seventy :
    degreePrimes (2 ^ 70) = [29, 31, 37, 41, 43, 47, 53, 59, 61, 67] := by
  rw [degreePrimes, primeBound, log_two_pow_seventy]
  decide

theorem fieldDegree_two_pow_seventy :
    fieldDegree (2 ^ 70) = 29 * 31 * 37 * 41 * 43 * 47 * 53 * 59 * 61 * 67 := by
  rw [fieldDegree_eq_prod, degreePrimes_two_pow_seventy]
  rfl

/-- At `N = 2 ^ 70` the lower-order term `14 (explicitThreshold N + 1)` is below `N`. -/
theorem fourteen_mul_explicitThreshold_two_pow_seventy_lt :
    14 * (explicitThreshold (2 ^ 70) + 1) < 2 ^ 70 := by
  simp only [explicitThreshold, numBlocks, subfieldExp, symDegree, primeBound, log_two_pow_seventy,
    fieldDegree_two_pow_seventy]
  norm_num

/-- The disperser property is not vacuous at `N = 2 ^ 70`: the zero extension is an injective
affine map from `BitString (explicitThreshold N + 1)`, and the explicit function is nonconstant on
its image. -/
theorem exists_explicitDisperser_zeroExtend_ne :
    ∃ x y : BitString (explicitThreshold (2 ^ 70) + 1),
      explicitDisperser (2 ^ 70) (BitString.zeroExtend x) ≠
        explicitDisperser (2 ^ 70) (BitString.zeroExtend y) :=
  isAffineDisperser_explicitDisperser (2 ^ 70) _ BitString.isAffine_zeroExtend
    (BitString.zeroExtend_injective (by
      have := fourteen_mul_explicitThreshold_two_pow_seventy_lt
      omega))

/-- **More than `3 N` gates at `N = 2 ^ 70`**: every circuit over the full binary basis computing
the explicit disperser on `2 ^ 70` bits has more than `3 · 2 ^ 70` gates. -/
theorem three_mul_lt_size_two_pow_seventy (C : Circuit (fullSignature 2 Bool) (2 ^ 70) 1)
    (hC : C.Computes fullInterpretation (single (explicitDisperser (2 ^ 70)))) :
    3 * 2 ^ 70 < C.size := by
  have h := seven_mul_le_two_mul_size_add_explicitThreshold C hC
  have := fourteen_mul_explicitThreshold_two_pow_seventy_lt
  omega

/-- Such circuits exist, since the full binary basis is complete, so the bound is not vacuous. -/
theorem exists_circuit_three_mul_lt_size :
    ∃ C : Circuit (fullSignature 2 Bool) (2 ^ 70) 1,
      C.Computes fullInterpretation (single (explicitDisperser (2 ^ 70))) ∧
        3 * 2 ^ 70 < C.size := by
  obtain ⟨C, hC⟩ := Interpretation.IsComplete.exists_computes_single
    (I := fullInterpretation (k := 2) (Carrier := Bool)) (explicitDisperser (2 ^ 70))
  exact ⟨C, hC, three_mul_lt_size_two_pow_seventy C hC⟩

/-! ### The language in `P` -/

-- `explicitDisperserLanguage` agrees with `explicitDisperser` on each slice, lies in `P`, and
-- satisfies the `3.5 N - O(N / log N)` circuit lower bound for all large `N`.
example :
    (∀ N, explicitDisperserLanguage.slice N = explicitDisperser N) ∧
      (explicitDisperserLanguage : Set (List Bool)) ∈ Complexity.P encBits ∧
      ∀ᶠ N in Filter.atTop, ∀ C : Circuit (fullSignature 2 Bool) N 1,
        C.Computes fullInterpretation (single (explicitDisperserLanguage.slice N)) →
          7 / 2 * (N : ℝ) - 42 * N / (Nat.log 2 N + 1) - 7 ≤ C.size :=
  ⟨(fun N => slice_explicitDisperserLanguage N),
    explicitDisperserLanguage_mem_P,
    by simpa only [slice_explicitDisperserLanguage] using
      eventually_le_size_of_computes_explicitDisperser⟩

/-! ### The explicit field with two prime factors -/

example : degreePrimes 5915 = [5, 7] ∧ fieldDegree 5915 = 35 := by decide

/-- Pseudorandom bits from the linear congruential generator `s ↦ 1103515245 s + 12345` modulo
`2 ^ 31`, reading bit `16` of each state. -/
def lcgBits (N seed : ℕ) : List Bool :=
  ((List.range N).foldl (fun (state : ℕ × List Bool) _ =>
    let s := (state.1 * 1103515245 + 12345) % 2 ^ 31
    (s, state.2 ++ [s / 2 ^ 16 % 2 == 1])) (seed, [])).2

/-- The unit of the explicit field at `N = 5915`, in coordinates. -/
def one : List Bool := true :: List.replicate 34 false

-- The least-code irreducible polynomials of degrees `5` and `7`: `X ^ 5 + X ^ 2 + 1` (code `37`)
-- and `X ^ 7 + X + 1` (code `131`).
/-- info: [37, 131] -/
#guard_msgs in
#eval (degreePrimes 5915).map (leastIrreducibleCode (codeBound 5915))

-- The table of `𝔽_{2 ^ 35} = 𝔽_{2 ^ 5} ⊗ 𝔽_{2 ^ 7}`: `35` rows, `1` is a unit, commutativity and
-- associativity, `a ^ (2 ^ 35 - 1) = 1` but `a ^ (2 ^ 5 - 1) ≠ 1`, and `Tr 1 = 1`.
/-- info: (35, true, true, true, true, false, true) -/
#guard_msgs in
#eval
  let tab := explicitTable 5915
  let a := lcgBits 35 1
  let b := lcgBits 35 2
  let c := lcgBits 35 3
  (tab.length, fieldMul tab one a == a, fieldMul tab a b == fieldMul tab b a,
    fieldMul tab (fieldMul tab a b) c == fieldMul tab a (fieldMul tab b c),
    powerPred tab a 34 == one, powerPred tab a 4 == one, traceBit (traceVector tab) one)

end ComplexityTests.AffineDisperserCorollary
