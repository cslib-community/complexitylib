/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.MemoryWindow

/-!
# Static properties of memory-window register normalization

The normalizer has exactly one remainder per source register and one closing self-copy.
These properties let callers account for a whole fixed register bank without unfolding the
finite register enumeration, and preserve width-independent execution.
-/

public section

namespace Cslib.WordRAM.MemoryWindow

private theorem size_normalizeBankList {r : ℕ} (is : List (Fin r)) :
    (normalizeBankList is).size = is.length + 1 := by
  induction is with
  | nil => rfl
  | cons i is ih => simp only [normalizeBankList, Code.size, List.length_cons, ih]; omega

/-- The fixed register normalizer uses one real operation per source register, plus one. -/
theorem size_normalizeRegisters (r : ℕ) : (normalizeRegisters r).size = r + 1 := by
  simpa only [normalizeRegisters, List.length_finRange] using
    size_normalizeBankList (List.finRange r)

private theorem normalizeBankList_not_readsWidth {r : ℕ} (is : List (Fin r)) :
    ¬(normalizeBankList is).ReadsWidth := by
  induction is with
  | nil => simp [normalizeBankList, Code.ReadsWidth, Op.ReadsWidth]
  | cons i is ih =>
    simpa only [normalizeBankList, Code.ReadsWidth, Op.ReadsWidth, Op.bin,
      reduceCtorEq, false_or] using ih

/-- Register normalization uses the runtime modulus and never reads the physical width. -/
theorem normalizeRegisters_not_readsWidth (r : ℕ) : ¬(normalizeRegisters r).ReadsWidth :=
  normalizeBankList_not_readsWidth _

end Cslib.WordRAM.MemoryWindow
