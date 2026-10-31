/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.Algorithms.Lean.CuckooHashing
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
      (fun θ => doubleTabHash 1 8 30 256 7 θ.1.1 θ.1.2)
      (fun θ => doubleTabHash 1 8 30 256 7 θ.2.1 θ.2.2)
      0 18 3 4 :=
  isCuckooHashPair_doubleTabHash (c := 1) (b := 30) (U := 256) (M := 7)
    (by decide) (by decide) 0 18 (by decide) (by decide) (by decide) (by decide)

/-- Concrete non-vacuity instance of `isCuckooHashPair_provableFamily` at `n_max = 0`, `c_exp = 4`,
`U = 256 ≤ 4 ^ 4`, `M = 7` (`2 ^ 7 = 128 ≥ 32 * 4`). -/
example :
    IsCuckooHashPair
      (PMF.uniformOfFintype (ProvableHashSeed 4 0 256 7))
      (provableHash1 4 0 256 7)
      (provableHash2 4 0 256 7)
      0 (maxEvictions 0) 3 4 :=
  isCuckooHashPair_provableFamily (c_exp := 4) (n_max := 0) (U := 256) (M := 7)
    (by decide) (by decide)

/-- Concrete non-vacuity instance of `isCuckooHashPair_provableFamily` at `n_max = 10`, `c_exp = 4`,
`U = 10000 ≤ 10 ^ 4`, `M = 9` (`2 ^ 9 = 512 ≥ 32 * 10`). -/
example :
    IsCuckooHashPair
      (PMF.uniformOfFintype (ProvableHashSeed 4 10 10000 9))
      (provableHash1 4 10 10000 9)
      (provableHash2 4 10 10000 9)
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
      (PMF.uniformOfFintype (ProvableHashSeed c_exp N (N ^ c_exp) M))
      (provableHash1 c_exp N (N ^ c_exp) M)
      (provableHash2 c_exp N (N ^ c_exp) M)
      N (maxEvictions N) 3 4 := by
  intro N M
  have hmax : max N 4 = N := max_eq_left (four_le_doubleTabThreshold c_exp)
  have hU : N ^ c_exp ≤ max N 4 ^ c_exp := by rw [hmax]
  have hm : 32 * max N 4 ≤ 2 ^ M := by
    rw [hmax]
    dsimp only [N, M]
    rw [doubleTabThreshold_eq, Nat.pow_add, Nat.mul_comm]
  exact isCuckooHashPair_provableFamily hU hm

end ComplexityTests.DoubleTabulation
