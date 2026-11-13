/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Computability.Circuit.Boolean.ACC0
public import CslibFrontier.Computability.Circuit.Boolean.Razborov.MiddleSlice
public import CslibFrontier.Computability.Circuit.Boolean.Razborov.Useful
public import CslibFrontier.Computability.Circuit.Boolean.Smolensky.Majority

/-!
# Tests for Razborov's rank property against AC⁰[2]

Non-vacuity witnesses for the rank test of
`CslibFrontier.Computability.Circuit.Boolean.Razborov.RankProperty`, concrete values of the middle
slice of `CslibFrontier.Computability.Circuit.Boolean.Razborov.MiddleSlice`, the constructive and
large half of `CslibFrontier.Computability.Circuit.Boolean.Razborov.Natural` along the middle level,
its usefulness against AC⁰[2] from `CslibFrontier.Computability.Circuit.Boolean.Razborov.Useful`,
and the separations `P ⊄ AC⁰[p]` and `AC⁰[p] ⊊ TC⁰` at `p = 2`, which go through the middle slice.
-/

public section

namespace CslibFrontierTests.Computability.Circuit.Boolean.Razborov

open Cslib Cslib.Circuits Cslib.Circuits.Boolean Cslib.Circuits.Boolean.Razborov Cslib.Complexity
  Turing.MultiTapeTM BitString

/-! ### The rank test -/

-- The identity witness passes the rank test.
example : exactWeight 2 ∈ rankTest 3 1 := exactWeight_mem_rankTest 1

-- The constant-false function has zero matrix, so it fails the rank test at level `1` on three
-- inputs: the test is not trivially true.
example : (fun _ => false : BooleanFunction 3) ∉ rankTest 3 1 := by
  rw [mem_rankTest]
  have h : (zeroSumMatrix 1 fun x => bitVal (ZMod 2) ((fun _ => false : BooleanFunction 3) x)) =
      0 := by
    ext I J
    simp only [zeroSumMatrix_apply, bitVal_false, Finset.sum_const_zero, Matrix.zero_apply]
  rw [h, Matrix.rank_zero]
  decide

-- Largeness at a concrete size: at least half of the `2 ^ 2 ^ 3` functions pass.
example : 2 ^ 2 ^ 3 ≤ 2 * (rankTest 3 1).ncard := two_pow_two_pow_le_two_mul_ncard_rankTest 3 1

/-! ### The middle slice -/

-- At length `3` the gap is `0`: the slice is the strings with exactly two zeros.
example : middleSlice 3 ![true, false, false] = true := by
  rw [middleSlice_eq_true_iff, sliceLevel_eq, show (3 + 1 : ℕ) = 2 ^ 2 by norm_num, Nat.sqrt_eq']
  decide

example : middleSlice 3 ![true, true, false] = false := by
  rw [Bool.eq_false_iff, ne_eq, middleSlice_eq_true_iff, sliceLevel_eq,
    show (3 + 1 : ℕ) = 2 ^ 2 by norm_num, Nat.sqrt_eq']
  decide

-- `99` is the first length with a positive gap: the level is `50 - 1`.
example : sliceLevel 99 = 49 := by
  rw [sliceLevel_eq, show (99 + 1 : ℕ) = 10 ^ 2 by norm_num, Nat.sqrt_eq']
  norm_num

/-! ### Constructivity and naturalness -/

-- The rank test on three inputs at level `1`, from its truth table of length `8`, within
-- `173 · 8 ^ 3` gates.
example : complexity interpretation (single (truthTableTest (rankTest 3 1))) ≤ 173 * 8 ^ 3 :=
  complexity_truthTableTest_rankTest_le 3 1

-- The identity witness has the rank property along the middle level.
example (n : ℕ) : exactWeight (n - sliceLevel n) ∈ rankProperty sliceLevel n := by
  rw [rankProperty_apply]
  exact exactWeight_mem_rankTest _

-- Along the middle level the rank property is `P/poly`-natural.
example : NaturalProof.IsNatural PPoly (rankProperty sliceLevel) :=
  isNatural_PPoly_rankProperty sliceLevel

/-! ### Usefulness against AC⁰[2] -/

-- The rank property along the middle level is useful against AC⁰[2] ...
example : NaturalProof.IsUseful (AC0Mod 2) (rankProperty sliceLevel) :=
  isUseful_AC0Mod_two_rankProperty

-- ... so it is a natural property useful against AC⁰[2].
example : NaturalProof.IsNatural PPoly (rankProperty sliceLevel) ∧
    NaturalProof.IsUseful (AC0Mod 2) (rankProperty sliceLevel) :=
  isNatural_PPoly_and_isUseful_AC0Mod_two_rankProperty

-- Since AC⁰[2] is nonempty, usefulness against it is exactly eventual depth–size lower bounds.
example {C : ∀ n, Set (BooleanFunction n)} :
    NaturalProof.IsUseful (AC0Mod 2) C ↔ ∀ (d : ℕ) (s : ℕ → ℕ), PolynomiallyBounded s →
      ∀ᶠ n in Filter.atTop, ∀ (Cn : Circuit Unbounded.extSignature n 1), Cn.depth ≤ d →
        Cn.size ≤ s n → ∀ f ∈ C n,
          ¬ Cn.Computes (Unbounded.extInterpretation (modGate 2)) (single f) :=
  ⟨fun h => h.eventually_constDepth (I := Unbounded.extInterpretation (modGate 2))
      ⟨_, modGate_mem_AC0Mod 2⟩,
    NaturalProof.IsUseful.of_eventually_constDepth⟩

-- So the qualitative usefulness of the rank property gives back its lower bounds: eventually no
-- depth-`d` circuit with at most `n ^ k` gates computes a function passing the rank test.
example (d k : ℕ) :
    ∀ᶠ n in Filter.atTop, ∀ (Cn : Circuit Unbounded.extSignature n 1), Cn.depth ≤ d →
      Cn.size ≤ n ^ k → ∀ f ∈ rankProperty sliceLevel n,
        ¬ Cn.Computes (Unbounded.extInterpretation (modGate 2)) (single f) :=
  isUseful_AC0Mod_two_rankProperty.eventually_constDepth
    (I := Unbounded.extInterpretation (modGate 2)) ⟨_, modGate_mem_AC0Mod 2⟩ d _ (by fun_prop)

-- Every language in AC⁰[2] eventually has slices failing the rank test; the middle slice passes
-- it everywhere, which recovers `middleSlice_notMem_AC0Mod_two`.
example : Language.ofSlices middleSlice ∉ AC0Mod 2 := fun h => by
  obtain ⟨n, hn⟩ := (isUseful_AC0Mod_two_rankProperty _ h).exists
  rw [Language.slice_ofSlices, rankProperty_apply] at hn
  exact hn (middleSlice_mem_rankTest n)

-- Explicit usefulness: at the length `rankLength 2 x`, no depth-2 circuit with at most `2 ^ x`
-- gates computes a function passing the rank test.
example (x : ℕ) {C : Circuit Unbounded.extSignature (rankLength 2 x) 1} (hCd : C.depth ≤ 2)
    (hCs : C.size ≤ 2 ^ x) {f : BooleanFunction (rankLength 2 x)}
    (hC : C.Computes (Unbounded.extInterpretation (modGate 2)) (single f)) :
    f ∉ rankProperty sliceLevel (rankLength 2 x) :=
  notMem_rankProperty_rankLength_of_computes hCd hCs hC

-- At depth `1` the length is quadratic in `x`.
example {x : ℕ} (hx : 1 ≤ x) : rankLength 1 x + 1 ≤ 401 * 2 ^ 18 * x ^ 2 :=
  rankLength_add_one_le (d := 1) hx

/-! ### Separations for every prime `p`, including `p = 2` -/

example {p : ℕ} [Fact p.Prime] :
    ∃ L : Language Bool, (L : Set (List Bool)) ∈ P encBits ∧ L ∉ AC0Mod p :=
  exists_mem_P_notMem_AC0Mod

example : Language.ofSlices majority ∉ AC0Mod 2 := Smolensky.majority_notMem_AC0Mod

example : AC0Mod 2 ⊂ TC0 := Smolensky.AC0Mod_ssubset_TC0

end CslibFrontierTests.Computability.Circuit.Boolean.Razborov
