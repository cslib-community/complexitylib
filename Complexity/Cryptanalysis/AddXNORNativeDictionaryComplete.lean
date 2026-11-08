/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Cryptanalysis.AddXNORNativeDictionaryFrame
import all Complexity.Cryptanalysis.AddXNORNativeDictionary

/-!
# Exact presence and composition of native dictionary insertions

Sequential insertion streams compose by append. Every inserted full state remains
present despite replacement collisions, so absence is equivalent to absence from
the entire insertion stream when the initial tag was zero.
-/

public section

namespace Cslib.Cryptanalysis.AddXNOR.Native.Dictionary

/-- Two insertion streams have exactly the same effect as their concatenation. -/
theorem filled_append (D : ℕ) (es fs : List Entry) (mem : ℕ → ℕ) (t : ℕ) :
    filledMemory D (es ++ fs) mem t =
        filledMemory D fs (filledMemory D es mem t) (filledTop D es mem t) ∧
      filledTop D (es ++ fs) mem t =
        filledTop D fs (filledMemory D es mem t) (filledTop D es mem t) := by
  induction es generalizing mem t with
  | nil => exact ⟨rfl, rfl⟩
  | cons e es ih =>
    simpa only [List.cons_append, filledMemory, filledTop] using
      (ih (putMemory mem D t e.state e.first e.second)
        (if mem (slot D e.state) = 0 then e.state + 1 else t))

/-- Replacement never removes an inserted state. This is an exact physical tag
contract; payload provenance is supplied separately by `filledMemory_provenance`. -/
theorem filledMemory_present (D : ℕ) (es : List Entry) (mem : ℕ → ℕ) (t q : ℕ) :
    filledMemory D es mem t (slot D q) ≠ 0 ↔
      mem (slot D q) ≠ 0 ∨ ∃ e ∈ es, e.state = q := by
  induction es generalizing mem t with
  | nil => simp [filledMemory]
  | cons e es ih =>
    rw [filledMemory, ih, (putMemory_read mem D t e.state e.first e.second q).1]
    by_cases hq : q = e.state
    · simp [hq]
    · simp [hq, Ne.symm hq, List.mem_cons]

/-- Starting from an empty tag, membership of the insertion stream is equivalent
to presence, including zero witnesses and repeated full-state collisions. -/
theorem filledMemory_present_iff (D : ℕ) (es : List Entry) (mem : ℕ → ℕ) (t q : ℕ)
    (hzero : mem (slot D q) = 0) :
    filledMemory D es mem t (slot D q) ≠ 0 ↔ ∃ e ∈ es, e.state = q := by
  simp only [filledMemory_present, hzero, ne_eq, not_true_eq_false, false_or]

end Cslib.Cryptanalysis.AddXNOR.Native.Dictionary
