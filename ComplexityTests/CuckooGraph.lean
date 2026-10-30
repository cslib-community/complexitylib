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

Verifies the API surface and non-vacuity of `Cslib.Algorithms.Lean.CuckooHashing`, including:
* `cuckooWalk_dichotomy` and `cuckooWalk_dichotomy_bicyclic` (Pagh & Rodler 2004, Section 2.3,
  Lemma 1);
* `isCuckooHashPair_of_kWiseIndependent` for all `n_max : ℕ`;
* concrete `IsCuckooHashPair` instances at `n_max = 4` and `n_max = 16` for both explicit
  trinomial-field polynomial hashing (`isCuckooHashPair_trinomialPolyHash`) and uniform random hash
  pairs (`isCuckooHashPair_uniform`);
* `uniform_interpret_eq_lazy_hashPair` connecting the eager uniform hash pair to lazy random-oracle
  evaluation.
-/

@[expose] public section

namespace ComplexityTests.CuckooGraph

open Cslib Cslib.Probability
open Cslib.Algorithms.WordRAM.Dictionary.CuckooHashing
open Cslib.Algorithms.Lean.CuckooHashing

/-! ## 1. Walk dichotomy and `k`-wise independent `IsCuckooHashPair` API checks -/

example := @cuckooWalk_dichotomy
example := @cuckooWalk_dichotomy_bicyclic
example := @isCuckooHashPair_of_kWiseIndependent
example := @isCuckooHashPair_trinomialPolyHash
example := @isCuckooHashPair_uniform
example := @uniform_interpret_eq_lazy_hashPair

example : maxEvictions 4 = 24 := by decide
example : maxEvictions 16 = 36 := by decide

/-! ## 2. Concrete non-vacuity instances at `n_max = 4` and `n_max = 16` -/

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

/-! ## 3. Lazy random-oracle equivalence check -/

/-- Concrete check of `uniform_interpret_eq_lazy_hashPair` for a two-table cuckoo query program on
`U = 256`, `m = 128`. -/
example (prog : OracleComp (fun _ : Bool × Fin 256 => Fin 128) Bool) :
    (do
      let p ← PMF.uniformOfFintype ((Fin 256 → Fin 128) × (Fin 256 → Fin 128))
      OracleComp.interpret (fun q : Bool × Fin 256 => PMF.pure (if q.1 then p.2 q.2 else p.1 q.2))
        prog) =
      ((OracleComp.interpret (RandomOracle.answer (fun _ => PMF.uniformOfFintype (Fin 128)))
        prog).run (fun _ => none)).map Prod.fst :=
  uniform_interpret_eq_lazy_hashPair prog

end ComplexityTests.CuckooGraph
