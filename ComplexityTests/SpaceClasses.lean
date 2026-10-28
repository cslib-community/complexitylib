/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Classes.Constructible
import Complexity.Computability.Complexity.Classes.LogSpace
import Complexity.Computability.Complexity.Classes.Space.Time
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Streaming
import Cslib.Computability.Machines.Turing.MultiTape.Combinators.AlmostConstant

/-! Generic space-class and constructibility clients, without hierarchy imports.
The concrete zero-space instances (every word, and the words with an odd number of ones) and
constructible bounds exercise satisfiable hypotheses. -/

namespace ComplexityTests.SpaceClasses

open Cslib Cslib.Complexity Turing Turing.MultiTapeTM

/-! ### A problem in constant space -/

/-- Every word is accepted in zero space. -/
private theorem univ_mem_DSPACE : (Set.univ : Set (List Bool)) ∈ DSPACE encBits fun _ => 0 := by
  obtain ⟨c, h⟩ := computableInTimeAndSpace_of_const (α := List Bool) (encIn := encBits)
    (encOut := encBool) true
  exact mem_DSPACE_iff.mpr ⟨0, 0, _, decidableInTimeAndSpace_iff.mpr
    ⟨_, h.mono (fun _ => le_rfl) fun _ => le_rfl, fun _ => by simp⟩⟩

/-- It is decided within time `O((n + 2) * 2 ^ (c * 0))`, by counting configurations. -/
example : ∃ c, (Set.univ : Set (List Bool)) ∈ DTIME encBits fun n => (n + 2) * 2 ^ (c * 0) :=
  exists_mem_DTIME_of_mem_DSPACE univ_mem_DSPACE

/-! ### A nontrivial problem in constant space: odd parity -/

/-- Whether a word has an odd number of ones. -/
private def oddOnes (word : List Bool) : Bool := word.foldl (fun b x => b ^^ x) false

example : oddOnes [true, false, true, true] = true ∧ oddOnes [true, true] = false := by decide

/-- The words with an odd number of ones are decided in constant space, by streaming the parity
bit. -/
private theorem setOf_oddOnes_mem_DSPACE :
    {w | oddOnes w = true} ∈ DSPACE encBits fun _ => 0 := by
  obtain ⟨c, h, -⟩ := ComputableTidilyInO.foldl_bits_finite encBool (fun b x => b ^^ x) false
  exact mem_DSPACE_iff.mpr ⟨0, c, _, decidableInTimeAndSpace_iff.mpr
    ⟨oddOnes, h.computableInTimeAndSpace.mono (fun _ => le_rfl) fun _ => by simp,
      fun _ => Iff.rfl⟩⟩

example : ∃ c, {w | oddOnes w = true} ∈ DTIME encBits fun n => (n + 2) * 2 ^ (c * 0) :=
  exists_mem_DTIME_of_mem_DSPACE setOf_oddOnes_mem_DSPACE

/-- Constant space is within logarithmic space. -/
example : {w | oddOnes w = true} ∈ L encBits :=
  mem_L_iff_mem_DSPACE.mpr (DSPACE_mono (fun _ => Nat.zero_le _) setOf_oddOnes_mem_DSPACE)

example : {w | oddOnes w = true} ∈ PSPACE encBits :=
  DSPACE_subset_PSPACE (by fun_prop) setOf_oddOnes_mem_DSPACE

/-! ### Space-constructible bounds -/

example : ∃ T, ComputableInO (fun x : List Bool => x.length) encBits encNat T
    fun x => x.length :=
  spaceConstructible_id.computableInO

example : ∃ T, ComputableInO (fun x : List Bool => x.length + 1) encBits encNat T
    fun x => x.length + 1 :=
  spaceConstructible_succ.computableInO

example : ∃ T, ComputableInO (fun x : List Bool => (x.length + 1) ^ 3) encBits encNat T
    fun x => (x.length + 1) ^ 3 :=
  (spaceConstructible_succ_pow 3).computableInO

example : ∃ T, ComputableInO (fun _ : List Bool => 5) encBits encNat T fun _ => 5 :=
  (spaceConstructible_const 5).computableInO

example : ∃ T, ComputableInO (fun x : List Bool => 2 ^ x.length) encBits encNat T
    fun x => 2 ^ x.length :=
  spaceConstructible_two_pow.computableInO

/-- `L` and `PSPACE` through `DSPACE`, instantiated on `oddOnes`. -/
example : {w | oddOnes w = true} ∈ DSPACE encBits Nat.log2 ∧
    ∃ k, {w | oddOnes w = true} ∈ DSPACE encBits (· ^ k) :=
  ⟨mem_L_iff_mem_DSPACE.mp
     (mem_L_iff_mem_DSPACE.mpr (DSPACE_mono (fun _ => Nat.zero_le _) setOf_oddOnes_mem_DSPACE)),
   mem_PSPACE_iff_exists_mem_DSPACE.mp
     (DSPACE_subset_PSPACE (by fun_prop) setOf_oddOnes_mem_DSPACE)⟩

end ComplexityTests.SpaceClasses
