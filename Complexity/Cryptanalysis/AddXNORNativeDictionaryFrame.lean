/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Cryptanalysis.AddXNORNativeDictionary
import all Complexity.Cryptanalysis.AddXNORNativeDictionary

/-!
# Framing sparse dictionary contents

Insertion into a sparse full-state table depends only on its own region.
`filledMemory_congr_above` lets a client construct an independent arena below
the table without assuming dictionary contents as a semantic oracle.
-/

public section

namespace Cslib.Cryptanalysis.AddXNOR.Native.Dictionary

/-- Dictionary insertion depends only on memory at or above the table base.
This allows independent work below the table to be included in its base memory. -/
theorem filledMemory_congr_above (D : ℕ) (es : List Entry) (mem mem' : ℕ → ℕ)
    (t : ℕ) (hm : ∀ a, D ≤ a → mem a = mem' a) :
    ∀ a, D ≤ a → filledMemory D es mem t a = filledMemory D es mem' t a := by
  induction es generalizing mem mem' t with
  | nil => exact hm
  | cons e es ih =>
    have hs : D ≤ slot D e.state := by simp only [slot]; omega
    simp only [filledMemory, hm _ hs]
    apply ih
    intro a ha
    simp only [putMemory, hm _ hs, Function.update_apply]
    split_ifs <;> try simp only [Function.update_apply]
    all_goals first | exact hm a ha | (split_ifs <;> first | rfl | exact hm a ha)

end Cslib.Cryptanalysis.AddXNOR.Native.Dictionary

