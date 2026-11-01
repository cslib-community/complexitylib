/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.Algorithms.Lean.CuckooHashing
public import Complexity.Foundations.Data.BitString.Sum
public import Complexity.Foundations.Data.Nat.Power
public import Complexity.Foundations.Data.Nat.SummationByParts
public import Complexity.Init
public import Complexity.Probability.KWiseIndependent.DoubleTabulation

/-!
# Tests for Double Tabulation (`[Thorup2013]`) and Regime-Switched Cuckoo Hashing

Non-vacuity and decidability tests for `Complexity.Probability.KWiseIndependent.DoubleTabulation`
and the high-probability conditioning extensions in `Complexity.Algorithms.Lean.CuckooHashing`:
* Concrete `decide` checks showing `charDigits 2 1 (U := 4) : Fin 4 → Fin 2 → Fin 2` is `3`-unique
  (`IsKUnique 3`) on `{0, 1}²` by pigeonhole, but fails `4`-uniqueness (`¬ IsKUnique 4`) on the full
  `2 × 2` combinatorial rectangle `{(0, 0), (0, 1), (1, 0), (1, 1)}`.
* Concrete instantiation of Siegel's peeling lemma (`isKWiseIndependentHash_of_isKUnique`) producing
  a `3`-wise independent hash family `Fin 4 → Fin 4` from `charDigits 2 1`.
* Concrete non-vacuity instances of `isCuckooHashPair_doubleTabHash` and
  `isCuckooHashPair_provableFamily` in both the small (`n_max < doubleTabThreshold 4`) and large
  (`n_max = doubleTabThreshold 4`) capacity regimes.
-/

public section

namespace ComplexityTests.DoubleTabulation

open Cslib.Probability
open Cslib.Algorithms.Lean.CuckooHashing
open Cslib.Algorithms.WordRAM.Dictionary.CuckooHashing

/-- Every subset of `{0, 1}²` of size at most `3` has a unique coordinate value (`3`-uniqueness). -/
example : IsKUnique 3 (charDigits 2 1 (U := 4)) := by decide

/-- The full `2 × 2` rectangle `{0, 1}²` has every coordinate value shared by two elements, so
`charDigits 2 1 (U := 4)` is not `4`-unique. -/
example : ¬ IsKUnique 4 (charDigits 2 1 (U := 4)) := by decide

/-- Composing `charDigits 2 1 (U := 4)` with a `2 × 2` simple tabulation table yields a `3`-wise
independent hash family `Fin 4 → Fin (2 ^ 2)`. -/
example :
    IsKWiseIndependentHash 3
      (fun (r : Fin 2 → Fin (2 ^ 1) → Fin (2 ^ 2)) (u : Fin 4) =>
        simpleTabEval r (charDigits 2 1 u)) :=
  isKWiseIndependentHash_of_isKUnique (by decide : IsKUnique 3 (charDigits 2 1 (U := 4)))

/-- Concrete non-vacuity instance of `isCuckooHashPair_doubleTabHash` at `c = 1`, `b = 30`,
`U = 256 ≤ 2 ^ 30`, `M = 7`, `n_max = 0`, `MaxLoop = 18`. -/
example :
    IsCuckooHashPair
      (PMF.uniformOfFintype
        ((DoubleTabTopSeed 1 8 30 × DoubleTabBotSeed 8 30 7) ×
         (DoubleTabTopSeed 1 8 30 × DoubleTabBotSeed 8 30 7)))
      (fun ((top₁, bottom₁), _) => doubleTabHash 1 8 30 256 7 top₁ bottom₁)
      (fun (_, (top₂, bottom₂)) => doubleTabHash 1 8 30 256 7 top₂ bottom₂)
      0 18 3 4 :=
  isCuckooHashPair_doubleTabHash (c := 1) (b := 30) (U := 256) (M := 7)
    (by decide) (by decide) 0 18 (by decide) (by decide) (by decide) (by decide)

/-- Concrete non-vacuity instance of `isCuckooHashPair_provableFamily` at `n_max = 0`, `c_exp = 4`,
`U = 256 ≤ 4 ^ 4`, `M = 7` (`2 ^ 7 = 128 ≥ 32 * 4`). -/
example :
    IsCuckooHashPair
      (PMF.uniformOfFintype (Seed 4 0 256 7))
      (evalHash1 (c_exp := 4) (n_max := 0) (U := 256) (M := 7))
      (evalHash2 (c_exp := 4) (n_max := 0) (U := 256) (M := 7))
      0 (maxEvictions 0) 3 4 :=
  isCuckooHashPair_provableFamily (c_exp := 4) (n_max := 0) (U := 256) (M := 7)
    (by decide) (by decide)

/-- Concrete non-vacuity instance of `isCuckooHashPair_provableFamily` at `n_max = 10`, `c_exp = 4`,
`U = 10000 ≤ 10 ^ 4`, `M = 9` (`2 ^ 9 = 512 ≥ 32 * 10`). -/
example :
    IsCuckooHashPair
      (PMF.uniformOfFintype (Seed 4 10 10000 9))
      (evalHash1 (c_exp := 4) (n_max := 10) (U := 10000) (M := 9))
      (evalHash2 (c_exp := 4) (n_max := 10) (U := 10000) (M := 9))
      10 (maxEvictions 10) 3 4 :=
  isCuckooHashPair_provableFamily (c_exp := 4) (n_max := 10) (U := 10000) (M := 9)
    (by decide) (by decide)

/-- Concrete non-vacuity instance of `isCuckooHashPair_provableFamily` in the large
double-tabulation regime `n_max = doubleTabThreshold c_exp`,
`U = doubleTabThreshold c_exp ^ c_exp`, `M = 2 * doubleTabMinB c_exp + 5`. -/
example (c_exp : ℕ) :
    let N := doubleTabThreshold c_exp
    let M := 2 * doubleTabMinB c_exp + 5
    IsCuckooHashPair
      (PMF.uniformOfFintype (Seed c_exp N (N ^ c_exp) M))
      (evalHash1 (c_exp := c_exp) (n_max := N) (U := N ^ c_exp) (M := M))
      (evalHash2 (c_exp := c_exp) (n_max := N) (U := N ^ c_exp) (M := M))
      N (maxEvictions N) 3 4 := by
  intro N M
  have hmax : max N 4 = N := max_eq_left (four_le_doubleTabThreshold c_exp)
  have hU : N ^ c_exp ≤ max N 4 ^ c_exp := by rw [hmax]
  have hm : 32 * max N 4 ≤ 2 ^ M := by
    rw [hmax]
    dsimp only [N, M]
    rw [doubleTabThreshold_eq, Nat.pow_add, Nat.mul_comm]
  exact isCuckooHashPair_provableFamily hU hm

/-- Concrete check of `BitString.val_equivFin_add` on `3`-bit strings (`5 + 3 = 6`). -/
example :
    let a := (Cslib.BitString.equivFin 3).symm ⟨5, by decide⟩
    let b := (Cslib.BitString.equivFin 3).symm ⟨3, by decide⟩
    (Cslib.BitString.equivFin 3 (a + b)).val = 6 := by
  intro a b
  rw [Cslib.BitString.val_equivFin_add, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  decide

/-- Concrete check of `BitString.sum_bitString_eq_iff_sum_symmDiff_eq_zero` on `{0, 1}` and
`{1, 2}` in `Fin 3`. -/
example (g : Fin 3 → Cslib.BitString 4) (h : g 0 + g 2 = 0) :
    ∑ i ∈ ({0, 1} : Finset (Fin 3)), g i = ∑ i ∈ ({1, 2} : Finset (Fin 3)), g i := by
  rw [Cslib.BitString.sum_bitString_eq_iff_sum_symmDiff_eq_zero]
  have hsymm : symmDiff ({0, 1} : Finset (Fin 3)) ({1, 2} : Finset (Fin 3)) = {0, 2} := by decide
  rw [hsymm, Finset.sum_pair (by decide), h]

/-- Concrete check of `Nat.sq_le_two_pow` and `Nat.pow_le_two_pow` (`16 ^ 2 ≤ 2 ^ 16`). -/
example : 16 ^ 2 ≤ 2 ^ 16 ∧ 5 ^ 2 ≤ 2 ^ 5 :=
  ⟨Nat.pow_le_two_pow (by decide) (by decide), Nat.sq_le_two_pow (by decide)⟩

/-- Concrete check of `Nat.sum_mul_eq_sum_prefix_sub` for `m = 2`. -/
example (a : ℕ → ℕ) :
    ∑ i ∈ Finset.range 3, a i * (3 - i) =
      (∑ i ∈ Finset.range 2, (∑ j ∈ Finset.range (i + 1), a j) * ((3 - i) - (3 - (i + 1)))) +
        (∑ j ∈ Finset.range 3, a j) * (3 - 2) :=
  Nat.sum_mul_eq_sum_prefix_sub a (fun i => 3 - i) 2 (by omega)

/-- Concrete check of `IsCuckooHashPair.mono_consts` widening `(3, 4)` to `(5, 6)`. -/
example :
    IsCuckooHashPair
      (PMF.uniformOfFintype (Seed 4 0 256 7))
      (evalHash1 (c_exp := 4) (n_max := 0) (U := 256) (M := 7))
      (evalHash2 (c_exp := 4) (n_max := 0) (U := 256) (M := 7))
      0 (maxEvictions 0) 5 6 :=
  (isCuckooHashPair_provableFamily (c_exp := 4) (n_max := 0) (U := 256) (M := 7)
    (by decide) (by decide)).mono_consts (by decide) (by decide)

end ComplexityTests.DoubleTabulation
