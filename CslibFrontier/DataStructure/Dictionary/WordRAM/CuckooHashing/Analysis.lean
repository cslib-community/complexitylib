/-
Copyright (c) 2026 Renfei Zhou, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Dictionary.CuckooHashing
public import CslibFrontier.DataStructure.Dictionary.WordRAM.CuckooHashing.HashFamily
import CslibFrontier.Probability.KWiseIndependent.DoubleTabulation.Parameters

/-!
# Cuckoo analysis for the regime-switched Word-RAM hash family

This bridge applies the machine-independent cuckoo graph analysis to the concrete hash pair
from `WordRAM.CuckooHashing.HashFamily`. It combines the trinomial-polynomial instance in the
small-capacity regime with Thorup's double-tabulation instance in the large-capacity regime.

## Main results

* `isCuckooHashPair_provableFamily`: for every capacity `n_max`, under
  `U ≤ max n_max 4 ^ c_exp` and `32 * max n_max 4 ≤ 2 ^ M`, the concrete seed law satisfies
  `IsCuckooHashPair` with `C_walk = 3`, `C_reh = 4`, and cap `maxEvictions n_max`.

This is a specialization of the sufficient cuckoo interface; it retains the graph analysis's
uniformity over valid placements and insertion orders, and the Word-RAM implementation's
polynomial-universe and table-load conditions.

## References

* [R. Pagh and F. F. Rodler, "Cuckoo hashing"][PaghRodler2004] (8 December 2003 author manuscript,
  Section 2.3, pp. 6–10).
* [M. Thorup, "Simple Tabulation, Fast Expanders, Double Tabulation, and High
  Independence"][Thorup2013] (FOCS 2013, Theorem 1(a), pp. 4–5 of `arXiv:1311.3121v2`).
-/

public section

namespace Cslib.DataStructure.Dictionary.WordRAM.CuckooHashing

open Cslib.Probability
open Cslib.DataStructure.Dictionary.CuckooHashing

private theorem isCuckooHashPair_seedAux (reg : Bool) {c_exp n_max U M : ℕ}
    (hreg : reg = decide (n_max < doubleTabThreshold c_exp))
    (hU : U ≤ max n_max 4 ^ c_exp) (hm : 32 * max n_max 4 ≤ 2 ^ M) :
    IsCuckooHashPair
      (PMF.uniformOfFintype (SeedAux reg c_exp n_max U M))
      (evalHash1Aux reg c_exp n_max U M)
      (evalHash2Aux reg c_exp n_max U M)
      n_max (maxEvictions n_max) 3 4 := by
  have hloop_le : maxEvictions n_max ≤ 2 ^ M :=
    (maxEvictions_le_thirtyTwo_mul_max n_max).trans hm
  cases reg
  · dsimp only [SeedAux, SingleSeedAux, evalHash1Aux, evalHash2Aux, evalSingleAux,
      Cslib.DataStructure.HashFamily.WordRAM.DoubleTabulation.provableC,
      Cslib.DataStructure.HashFamily.WordRAM.DoubleTabulation.provableD,
      Cslib.DataStructure.HashFamily.WordRAM.DoubleTabulation.provableB]
    have hge : doubleTabThreshold c_exp ≤ n_max :=
      not_lt.mp (of_decide_eq_false hreg.symm)
    let c := 2 * max c_exp 1
    let b := (1 + Nat.clog 2 (max n_max 4)) / 2
    have hc2 : 2 ≤ c := by omega
    obtain ⟨hU_cb, hb_ge, hmax_le_2b⟩ : U ≤ 2 ^ (c * b) ∧ doubleTabMinB c_exp ≤ b ∧
        max n_max 4 ≤ 2 ^ (2 * b) := doubleTab_canonical_params hge hU
    have hb_min_def : doubleTabMinB c_exp = 4 * (24 * c + 8) ^ 2 := doubleTabMinB_eq c_exp
    have hb_64 : 64 ≤ b := by nlinarith
    have hclog2_le : Nat.clog 2 (max n_max 2) ≤ 2 * b :=
      (Nat.clog_le_iff_le_pow (by decide)).mpr
        ((by omega : max n_max 2 ≤ max n_max 4).trans hmax_le_2b)
    have hev_le : maxEvictions n_max ≤ 12 * b + 12 := by grind [maxEvictions]
    have h18_ev : 18 ≤ maxEvictions n_max := eighteen_le_maxEvictions n_max
    have h2ev_sq : 2 * max (maxEvictions n_max) 1 ≤ b ^ 2 := by
      have : max (maxEvictions n_max) 1 = maxEvictions n_max := by omega
      nlinarith
    have h2ev2 : 2 * maxEvictions n_max + 2 ≤ b ^ 2 := by nlinarith
    have hload_le : 2 * (max n_max 1 * max (maxEvictions n_max) 1) ≤ 2 ^ (2 * b) * b ^ 2 := by
      have hmax1_le : max n_max 1 ≤ 2 ^ (2 * b) :=
        (by omega : max n_max 1 ≤ max n_max 4).trans hmax_le_2b
      calc 2 * (max n_max 1 * max (maxEvictions n_max) 1)
          = max n_max 1 * (2 * max (maxEvictions n_max) 1) := by ring
        _ ≤ 2 ^ (2 * b) * b ^ 2 := Nat.mul_le_mul hmax1_le h2ev_sq
    have hprod_le : 2 * (max n_max 1 * max (maxEvictions n_max) 1) *
        doubleTabCodeBound c (8 * c) 4 (2 * maxEvictions n_max + 2) ≤ 2 ^ (3 * b) :=
      mul_doubleTabCodeBound_le hb_ge h2ev2 hload_le
    exact isCuckooHashPair_doubleTabHash (by omega) hU_cb n_max (maxEvictions n_max)
      hm le_rfl hloop_le hprod_le
  · dsimp only [SeedAux, SingleSeedAux, evalHash1Aux, evalHash2Aux, evalSingleAux,
      cuckooK, trinomialDeg]
    exact (isCuckooHashPair_trinomialPolyHash (le_two_pow_trinomialDeg U M) (le_trinomialDeg U M)
      n_max (maxEvictions n_max) le_rfl hm le_rfl hloop_le).mono_consts (by decide) (by decide)

/-- **Unconditional `IsCuckooHashPair` for the regime-switched Word-RAM hash family
(`trinomialPolyHash` + `doubleTabHash`) across all capacities `n_max : ℕ` and polynomial universes
`U ≤ max n_max 4 ^ c_exp`**:
Whenever `U ≤ max n_max 4 ^ c_exp` and `32 * max n_max 4 ≤ 2 ^ M`, the uniform distribution
`seedLaw c_exp n_max U M` on `Seed c_exp n_max U M` with `(evalHash1, evalHash2)` satisfies
`IsCuckooHashPair (seedLaw c_exp n_max U M) evalHash1 evalHash2 n_max (maxEvictions n_max) 3 4`. -/
theorem isCuckooHashPair_provableFamily {c_exp n_max U M : ℕ}
    (hU : U ≤ max n_max 4 ^ c_exp) (hm : 32 * max n_max 4 ≤ 2 ^ M) :
    IsCuckooHashPair (seedLaw c_exp n_max U M) evalHash1 evalHash2
      n_max (maxEvictions n_max) 3 4 :=
  isCuckooHashPair_seedAux (decide (n_max < doubleTabThreshold c_exp)) rfl hU hm

end Cslib.DataStructure.Dictionary.WordRAM.CuckooHashing
