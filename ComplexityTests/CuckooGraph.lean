/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Algorithms.Lean.CuckooHashing

/-!
# Pagh–Rodler Cuckoo Graph & Walk Tail Bounds — Test Suite

Verifies concrete decidable instances of the cuckoo walk dichotomy (`HasAltPath`,
`HasBicyclicPrefix`, `HasExcessSubset`, `cuckooWalk_dichotomy`) and non-vacuity of
`IsCuckooHashPair` in `Cslib.Algorithms.Lean.CuckooHashing`:
* a 3-key colliding configuration (`constH : Fin 3 → Fin 2 := fun _ => 0`) where two keys place
  validly (`pureReplay ... [0, 1]`), inserting the third key fails (`pureEvict ... = none`), and
  both `HasBicyclicPrefix` and `HasExcessSubset ... 3` hold by `decide`;
* a contrasting 3-key alternating-path configuration where 1 eviction round does not halt,
  `HasAltPath ... 2` holds by `decide`, and `HasExcessSubset ... 3` fails by `decide`;
* a contrasting injective hash pair (`id : Fin 3 → Fin 3`) where `HasExcessSubset` and `HasAltPath`
  both fail and `pureReplay` succeeds in 1 round;
* concrete `IsCuckooHashPair` instances at `n_max = 4` and `n_max = 16` for both uniform random
  hash pairs (`isCuckooHashPair_uniform`) and explicit trinomial-field polynomial hashing
  (`isCuckooHashPair_trinomialPolyHash`).
-/

@[expose] public section

namespace ComplexityTests.CuckooGraph

open Cslib Cslib.Probability
open Cslib.Algorithms.WordRAM.Dictionary.CuckooHashing
open Cslib.Algorithms.Lean.CuckooHashing

/-! ## 1. Concrete decidable checks of the walk dichotomy (Case A, Case B, injective contrast) -/

/-- Constant hash function on `Fin 3 → Fin 2` mapping all 3 keys to bucket `0`. -/
def constH : Fin 3 → Fin 2 := fun _ => 0

/-- Valid placement of `{0, 1}` under `(constH, constH)`: key `1` in `T₁[0]` and key `0` in
`T₂[0]`. -/
def twoKeyCollidingTable : PureTable 3 2 :=
  ⟨fun b => if b = 0 then some ⟨1, 1⟩ else none,
   fun b => if b = 0 then some ⟨0, 0⟩ else none⟩

theorem pureReplay_constH_two_keys :
    pureReplay constH constH 2 [0, 1] = some twoKeyCollidingTable := by
  change (some ⟨_, _⟩ : Option (PureTable 3 2)) = some ⟨_, _⟩
  congr 2 <;> (ext b : 1; fin_cases b <;> rfl)

theorem pureEvict_constH_third_key_eq_none :
    pureEvict constH constH 2 twoKeyCollidingTable ⟨2, 2⟩ = none := by decide

theorem hasBicyclicPrefix_constH :
    HasBicyclicPrefix constH constH ({0, 1} : Finset (Fin 3)) 2 2 := by decide

theorem hasExcessSubset_constH :
    HasExcessSubset constH constH ({0, 1} : Finset (Fin 3)) 2 3 := by decide

/-- Contrasting injective hash pair `id : Fin 3 → Fin 3`, for which `HasExcessSubset` and
`HasAltPath` both fail and 3-key replay succeeds in 1 round. -/
theorem not_hasExcessSubset_id :
    ¬ HasExcessSubset (id : Fin 3 → Fin 3) id ({0, 1} : Finset (Fin 3)) 2 3 := by decide

theorem not_hasAltPath_id :
    ¬ HasAltPath (id : Fin 3 → Fin 3) id ({0, 1} : Finset (Fin 3)) 2 1 := by decide

theorem pureReplay_id_three_keys_isSome :
    (pureReplay (id : Fin 3 → Fin 3) id 1 [0, 1, 2]).isSome = true := by decide

/-- Hash pair on `Fin 3 → Fin 2` creating a length-2 alternating path `0 → 1 → 2` without any
excess-`≥ 1` subset: `h₁ 0 = h₁ 1 = 0`, `h₁ 2 = 1` and `h₂ 1 = h₂ 2 = 1`, `h₂ 0 = 0`. -/
def altH₁ : Fin 3 → Fin 2 := fun k => if k = 2 then 1 else 0
def altH₂ : Fin 3 → Fin 2 := fun k => if k = 0 then 0 else 1

/-- Valid placement of `{1, 2}` under `(altH₁, altH₂)`: key `1` in `T₁[0]` and key `2` in
`T₂[1]`. -/
def twoKeyAltTable : PureTable 3 2 :=
  ⟨fun b => if b = 0 then some ⟨1, 0⟩ else none,
   fun b => if b = 1 then some ⟨2, 1⟩ else none⟩

theorem pureEvict_altH_one_round_eq_none :
    pureEvict altH₁ altH₂ 1 twoKeyAltTable ⟨0, 2⟩ = none := by decide

theorem pureEvict_altH_two_rounds_isSome :
    (pureEvict altH₁ altH₂ 2 twoKeyAltTable ⟨0, 2⟩).isSome = true := by decide

theorem hasAltPath_altH :
    HasAltPath altH₁ altH₂ ({1, 2} : Finset (Fin 3)) 0 2 := by decide

theorem not_hasExcessSubset_altH :
    ¬ HasExcessSubset altH₁ altH₂ ({1, 2} : Finset (Fin 3)) 0 3 := by decide

/-! ## 2. Concrete non-vacuity instances of `IsCuckooHashPair` at `n_max = 4` and `n_max = 16` -/

/-- Concrete `IsCuckooHashPair` instance for uniform random hash pairs at `n_max = 4`, `U = 256`,
`m = 128`, `MaxLoop = maxEvictions 4 = 24` (`C_walk = 2`, `C_reh = 3`). -/
theorem instUniform_4 :
    IsCuckooHashPair
      (PMF.uniformOfFintype ((Fin 256 → Fin 128) × (Fin 256 → Fin 128)))
      Prod.fst Prod.snd 4 (maxEvictions 4) 2 3 :=
  isCuckooHashPair_uniform 4 (maxEvictions 4) (by decide) (le_refl _) (by decide)

/-- Concrete `IsCuckooHashPair` instance for uniform random hash pairs at `n_max = 16`, `U = 1024`,
`m = 512`, `MaxLoop = maxEvictions 16 = 36` (`C_walk = 2`, `C_reh = 3`). -/
theorem instUniform_16 :
    IsCuckooHashPair
      (PMF.uniformOfFintype ((Fin 1024 → Fin 512) × (Fin 1024 → Fin 512)))
      Prod.fst Prod.snd 16 (maxEvictions 16) 2 3 :=
  isCuckooHashPair_uniform 16 (maxEvictions 16) (by decide) (le_refl _) (by decide)

/-- Concrete `IsCuckooHashPair` instance for explicit trinomial-field polynomial hashing
(`trinomialPolyHash`) at `n_max = 4`, `U = 256`, `M = 7` (`m = 128`), `t = 2` (`2 * 3 ^ 2 = 18`),
`k = 50 = 2 * maxEvictions 4 + 2` (`C_walk = 2`, `C_reh = 3`). -/
theorem instTrinomial_4 :
    IsCuckooHashPair
      (PMF.uniformOfFintype
        ((Fin 50 → Fin (2 ^ (2 * 3 ^ 2))) × (Fin 50 → Fin (2 ^ (2 * 3 ^ 2)))))
      (fun θ => trinomialPolyHash 2 50 256 7 θ.1)
      (fun θ => trinomialPolyHash 2 50 256 7 θ.2)
      4 (maxEvictions 4) 2 3 :=
  isCuckooHashPair_trinomialPolyHash (by decide) (by decide) 4 (maxEvictions 4)
    (by decide) (by decide) (le_refl _) (by decide)

/-- Concrete `IsCuckooHashPair` instance for explicit trinomial-field polynomial hashing
(`trinomialPolyHash`) at `n_max = 16`, `U = 1024`, `M = 9` (`m = 512`), `t = 2` (`2 * 3 ^ 2 = 18`),
`k = 74 = 2 * maxEvictions 16 + 2` (`C_walk = 2`, `C_reh = 3`). -/
theorem instTrinomial_16 :
    IsCuckooHashPair
      (PMF.uniformOfFintype
        ((Fin 74 → Fin (2 ^ (2 * 3 ^ 2))) × (Fin 74 → Fin (2 ^ (2 * 3 ^ 2)))))
      (fun θ => trinomialPolyHash 2 74 1024 9 θ.1)
      (fun θ => trinomialPolyHash 2 74 1024 9 θ.2)
      16 (maxEvictions 16) 2 3 :=
  isCuckooHashPair_trinomialPolyHash (by decide) (by decide) 16 (maxEvictions 16)
    (by decide) (by decide) (le_refl _) (by decide)

end ComplexityTests.CuckooGraph
