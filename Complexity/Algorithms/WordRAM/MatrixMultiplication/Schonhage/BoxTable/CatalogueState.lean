/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxTable.Digits

/-!
# Readback invariants for computed box geometry

Every slot is assigned its actual prefix-count rank plus one, or zero when invalid.
Valid slots also append their three scalar descriptors. These are memory predicates
and descriptions of actual stores, not execution or time certificates.
-/

public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxTable

/-- A slot denotes a canonical box when its star count fits its completion's P0 population. -/
@[expose] def Eligible (L H s : ℕ) : Prop :=
  s / 10 ^ L ≤ population (s % 10 ^ L) L ∧ population (s % 10 ^ L) L ≤ H

instance (L H s : ℕ) : Decidable (Eligible L H s) :=
  inferInstanceAs (Decidable (s / 10 ^ L ≤ population (s % 10 ^ L) L ∧
    population (s % 10 ^ L) L ≤ H))

/-- Offset-one compact index, leaving zero for invalid slots. -/
@[expose] def directoryWord (L H s : ℕ) : ℕ :=
  if Eligible L H s then Nat.count (Eligible L H) s + 1 else 0

/-- The completed leaf code stored in a compact record. -/
@[expose] def recordCode (L s : ℕ) : ℕ := s % 10 ^ L

/-- The exact star count stored in a compact record. -/
@[expose] def recordStars (L s : ℕ) : ℕ := s / 10 ^ L

/-- The place value used by actual ten-child native lookups. -/
@[expose] def recordStride (L s : ℕ) : ℕ :=
  starStride (recordCode L s) (recordStars L s) L

/-- The four stores made for a valid slot, or the one zero store for an invalid slot. -/
@[expose] def catalogueWrite (L H D R s : ℕ) (μ : ℕ → ℕ) : ℕ → ℕ :=
  let ν := Function.update μ (D + s) (directoryWord L H s)
  if Eligible L H s then
    let p := R + 3 * Nat.count (Eligible L H) s
    Function.update (Function.update (Function.update ν p (recordCode L s))
      (p + 1) (recordStars L s)) (p + 2) (recordStride L s)
  else ν

/-- Readback of every completed slot and compact record, with the exact written-prefix frame. -/
structure CataloguePrefix (L H D R s : ℕ) (initial current : ℕ → ℕ) : Prop where
  /-- All visited directory slots have been assigned, even when invalid. -/
  directory : ∀ i < s, current (D + i) = directoryWord L H i
  /-- Every emitted record contains the original completed leaf index. -/
  code : ∀ i < s, Eligible L H i →
    current (R + 3 * Nat.count (Eligible L H) i) = recordCode L i
  /-- Every emitted record contains its exact star count. -/
  stars : ∀ i < s, Eligible L H i →
    current (R + 3 * Nat.count (Eligible L H) i + 1) = recordStars L i
  /-- Every emitted record contains the computed highest-star place value. -/
  stride : ∀ i < s, Eligible L H i →
    current (R + 3 * Nat.count (Eligible L H) i + 2) = recordStride L i
  /-- No word outside the actually written prefixes has changed. -/
  frame : ∀ a, ¬(D ≤ a ∧ a < D + s) →
    ¬(R ≤ a ∧ a < R + 3 * Nat.count (Eligible L H) s) → current a = initial a

/-- No initial zero-memory premise is needed at the empty prefix. -/
theorem CataloguePrefix.zero (L H D R : ℕ) (μ : ℕ → ℕ) :
    CataloguePrefix L H D R 0 μ μ := by
  constructor <;> simp

/-- The actual slot and descriptor writes extend the readback invariant by one slot. -/
theorem CataloguePrefix.step {L H D R s : ℕ} {μ ν : ℕ → ℕ}
    (h : CataloguePrefix L H D R s μ ν)
    (hs : s < (H + 1) * 10 ^ L) (hsep : D + (H + 1) * 10 ^ L ≤ R) :
    CataloguePrefix L H D R (s + 1) μ (catalogueWrite L H D R s ν) := by
  have hcount : Nat.count (Eligible L H) s ≤ s := Nat.count_le _
  have hold (i : ℕ) (hi : i < s) (hp : Eligible L H i) :
      Nat.count (Eligible L H) i < Nat.count (Eligible L H) s :=
    Nat.count_strict_mono hp hi
  by_cases hv : Eligible L H s
  · have hn := Nat.count_succ_eq_succ_count hv
    constructor
    · intro i hi
      by_cases his : i = s
      · subst i
        simp [catalogueWrite, hv, Function.update_of_ne (by omega : D + s ≠
          R + 3 * Nat.count (Eligible L H) s),
          Function.update_of_ne (by omega : D + s ≠ R + 3 * Nat.count (Eligible L H) s + 1),
          Function.update_of_ne (by omega : D + s ≠ R + 3 * Nat.count (Eligible L H) s + 2)]
      · have hiold : i < s := by omega
        simp only [catalogueWrite, hv, ↓reduceIte]
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
        exact h.directory i hiold
    · intro i hi hp
      by_cases his : i = s
      · subst i
        simp [catalogueWrite, hv]
      · have hr := hold i (by omega) hp
        simp only [catalogueWrite, hv, ↓reduceIte]
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
        exact h.code i (by omega) hp
    · intro i hi hp
      by_cases his : i = s
      · subst i
        simp [catalogueWrite, hv]
      · have hr := hold i (by omega) hp
        simp only [catalogueWrite, hv, ↓reduceIte]
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
        exact h.stars i (by omega) hp
    · intro i hi hp
      by_cases his : i = s
      · subst i
        simp [catalogueWrite, hv]
      · have hr := hold i (by omega) hp
        simp only [catalogueWrite, hv, ↓reduceIte]
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
        exact h.stride i (by omega) hp
    · intro a hd hr
      simp only [hn] at hr
      simp only [catalogueWrite, hv, ↓reduceIte]
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      exact h.frame a (by omega) (by omega)
  · have hn := Nat.count_succ_eq_count hv
    constructor
    · intro i hi
      by_cases his : i = s
      · subst i
        simp [catalogueWrite, hv]
      · rw [catalogueWrite, ite_eq_right hv, Function.update_of_ne (by omega)]
        exact h.directory i (by omega)
    · intro i hi hp
      have hne : i ≠ s := fun heq => hv (heq ▸ hp)
      have hiold : i < s := by omega
      rw [catalogueWrite, ite_eq_right hv, Function.update_of_ne (by omega)]
      exact h.code i hiold hp
    · intro i hi hp
      have hne : i ≠ s := fun heq => hv (heq ▸ hp)
      have hiold : i < s := by omega
      rw [catalogueWrite, ite_eq_right hv, Function.update_of_ne (by omega)]
      exact h.stars i hiold hp
    · intro i hi hp
      have hne : i ≠ s := fun heq => hv (heq ▸ hp)
      have hiold : i < s := by omega
      rw [catalogueWrite, ite_eq_right hv, Function.update_of_ne (by omega)]
      exact h.stride i hiold hp
    · intro a hd hr
      rw [catalogueWrite, ite_eq_right hv, Function.update_of_ne (by omega)]
      exact h.frame a (by omega) (by simpa only [hn] using hr)

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxTable
