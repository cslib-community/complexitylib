/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

import CslibFrontier.Computability.Complexity.Classes.Padding.Tally

/-! Clients of tally padding and of Arora–Barak 2007 Exercise 2.23. -/

open Cslib.Complexity Turing.MultiTapeTM

/-- Arora–Barak 2007 Exercise 2.23, in its native form, for any encoding. -/
example {α : Type} (enc : α ↪ List Bool)
    (h : ∀ L ∈ TALLY, L ∈ NP encBits → L ∈ P encBits) : EXP enc = NEXP enc :=
  EXP_eq_NEXP_of_tally h

-- The encoder and decoder are inverse on exponentially padded words.
example (u : List Bool) (m : ℕ) (hm : 2 ^ u.length ≤ m) :
    tallyDecode (tallyEncode (frame u ++ List.replicate m true)) =
      frame u ++ List.replicate m true := by
  rw [tallyEncode_frame_append hm, tallyDecode_pair_tallyCode]

-- A concrete word: `[false]` padded with two ones.
example : tallyEncode (frame [false] ++ List.replicate 2 true) = Nat.pair (tallyCode [false]) 2 :=
  tallyEncode_frame_append (by norm_num)

-- The tally problem of an `NP` problem is a tally language in `NP`.
example (B : Set (List Bool)) (hB : B ∈ NP encBits) :
    tallyOf B ∈ TALLY ∧ tallyOf B ∈ NP encBits :=
  ⟨tallyOf_mem_TALLY B, tallyOf_mem_NP hB⟩
