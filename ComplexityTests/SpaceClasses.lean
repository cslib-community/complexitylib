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

/-- Constant space is within linear time (by counting configurations), logarithmic space, and
polynomial space. -/
example :
    (∃ c, {w | oddOnes w = true} ∈ DTIME encBits fun n => (n + 2) * 2 ^ (c * 0)) ∧
    {w | oddOnes w = true} ∈ L encBits ∧
    {w | oddOnes w = true} ∈ PSPACE encBits :=
  ⟨exists_mem_DTIME_of_mem_DSPACE setOf_oddOnes_mem_DSPACE,
    mem_L_iff_mem_DSPACE.mpr (DSPACE_mono (fun _ => Nat.zero_le _) setOf_oddOnes_mem_DSPACE),
    DSPACE_subset_PSPACE (by fun_prop) setOf_oddOnes_mem_DSPACE⟩

/-! ### Space-constructible bounds -/

example :
    SpaceConstructible (fun n => (n + 1) * 2 ^ n) ∧
    ComputableInO (fun x : List Bool => (x.length + 1) * (x.length + 1) ^ 2) encBits encNat
      (fun x => (x.length + 1) * (x.length + 1) ^ 2)
      (fun x => (x.length + 1) * (x.length + 1) ^ 2) :=
  ⟨(timeConstructible_two_pow.succ_mul fun _ => Nat.lt_two_pow_self.le).spaceConstructible,
    ((timeConstructible_succ_pow (k := 2) (by decide)).succ_mul fun n =>
      (Nat.le_succ n).trans (Nat.le_self_pow (by decide) _)).computableInO⟩

/-- `L` and `PSPACE` through `DSPACE`, instantiated on `Set.univ` and `oddOnes`. -/
example : (Set.univ : Set (List Bool)) ∈ DSPACE encBits Nat.log2 ∧
    ∃ k, {w | oddOnes w = true} ∈ DSPACE encBits (· ^ k) :=
  ⟨mem_L_iff_mem_DSPACE.mp ⟨fun _ => true, .const true, fun _ => by simp⟩,
   mem_PSPACE_iff_exists_mem_DSPACE.mp
     (DSPACE_subset_PSPACE (by fun_prop) setOf_oddOnes_mem_DSPACE)⟩

end ComplexityTests.SpaceClasses
