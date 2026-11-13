/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

-- upstream: candidate
import CslibFrontier.Computability.Circuit.Boolean.NonuniformSeparation
import CslibFrontier.Computability.Complexity.Classes.EXP.Decidable
import CslibFrontier.Computability.Complexity.Classes.P.Finite

/-! # Applying nonuniform separation and checking its domain restriction

The undecidable circuit-language witness lies outside every deterministic time bound. On a
finite instance domain, in contrast, every problem is in P, so BPP and P/poly agree there.
-/

open Cslib Cslib.Circuits.Boolean Cslib.Complexity Turing.MultiTapeTM

example : ∃ A ∈ PPoly, ∀ t : ℕ → ℕ, A ∉ DTIME encBits t := by
  obtain ⟨A, hA, hdec⟩ := exists_mem_PPoly_not_isDecidable
  exact ⟨A, hA, fun _ ht => hdec (isDecidable_of_mem_DTIME ht)⟩

-- A checked counterexample to extending strict containment to arbitrary finite encodings.
example (enc : Bool ↪ List Bool) : BPP enc = PPolyOn enc := by
  ext A
  constructor
  · exact fun hA => BPP_subset_PPolyOn hA
  · intro _
    exact P_subset_BPP (Set.toFinite A).mem_P
