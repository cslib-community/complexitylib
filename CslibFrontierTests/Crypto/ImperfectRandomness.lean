/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.SecretSharing.ImperfectRandomnessBinary
import Mathlib.Data.ZMod.Basic

/-!
# Nonvacuity and boundary sources for imperfect-randomness sharing

The four-element Galois field gives an actual two-bit-message instance. The empty and full
source choices attain the two cardinality endpoints. The sharing functions also expose their
concrete algebraic rules to clients.
-/

open Cslib.Probability
open Cslib.Crypto.Protocols.SecretSharing.ImperfectRandomness
open scoped Cslib.Probability.PMF

namespace CslibFrontierTests.ImperfectRandomness

public abbrev V4 := GaloisField 2 2
noncomputable local instance : Fintype V4 := Fintype.ofFinite _
noncomputable local instance : DecidableEq V4 := Classical.decEq _

private theorem card_v4 : Fintype.card V4 = 4 := by
  rw [← Nat.card_eq_fintype_card, GaloisField.card 2 2 (by decide)]
  norm_num

example : (keys (∅ : Finset V4)).card = 8 := by
  classical
  rw [card_keys, Finset.card_empty, card_v4]

example : (keys (Finset.univ : Finset V4)).card = 4 := by
  classical
  rw [card_keys, Finset.card_univ, card_v4]

example (i m : V4) : first m (.central, i) = Sum.inl (i + m) := rfl
example (α i m : V4) : second α m (.central, i) = Sum.inl (α * i + m) := rfl
example (α x i : V4) : reconstruct α (Sum.inl x) (Sum.inr i) = x - i := rfl

/-- The main hypotheses hold at the smallest admitted binary message size. -/
example : ∃ α : V4, ∀ m k,
    reconstruct α (paddedFirst m k) (paddedSecond α m k) = m := by
  classical
  obtain ⟨_, _, α, hcorrect, _, _, _⟩ := binary_field_separation 2 (by decide)
  exact ⟨α, hcorrect⟩

example : Fintype.card (PaddedKey V4) = 16 ∧ Fintype.card (Share V4) = 8 := by
  exact alphabet_cardinalities (b := 2) card_v4

/-- No restriction is placed on the candidate extractor, even in the smallest instance. -/
example (ext : PaddedKey V4 → Bool) : ∃ T : Finset V4,
    (1 : ℝ) / 6 ≤ dist ((paddedSource T).map ext) (PMF.uniformOfFintype Bool) := by
  classical
  exact padded_no_bit_extractor ext

/-- The two-element field cannot supply the required third slope. -/
example : ¬∃ α : ZMod 2, α ≠ 0 ∧ α ≠ 1 := by decide

/-- One two-bit scheme works for all sixteen dealer inputs, hides every message,
and defeats every three-bit extractor on one of its flat high-entropy sources. -/
example : ∃ (sources : Finset V4 → PMF (Fin 4 → Bool))
    (shr₁ shr₂ : (Fin 2 → Bool) → (Fin 4 → Bool) → (Fin 3 → Bool))
    (rec : (Fin 3 → Bool) → (Fin 3 → Bool) → (Fin 2 → Bool)),
    (∀ m k, rec (shr₁ m k) (shr₂ m k) = m) ∧
    (∀ T m m', (sources T).map (shr₁ m) = (sources T).map (shr₁ m') ∧
      (sources T).map (shr₂ m) = (sources T).map (shr₂ m')) ∧
    (∀ T, (2 : ℝ) ≤ PMF.minEntropy (sources T)) ∧
    (∀ ext : (Fin 4 → Bool) → (Fin 3 → Bool), ∃ T,
      (1 : ℝ) / 6 ≤ dist ((sources T).map ext) (PMF.uniformOfFintype (Fin 3 → Bool))) := by
  obtain ⟨sources, shr₁, shr₂, rec, hc, hp, _, he, hx⟩ :=
    binary_string_separation 2 (by decide)
  exact ⟨sources, shr₁, shr₂, rec, hc, hp, he, hx 3 (by decide)⟩

/-- The field-operation guarantee applies to the entire padded key alphabet. -/
example (α m : V4) (k : PaddedKey V4) :
    (shareWithFieldCost α m (k.1.getD .central, k.2)).ret =
        (paddedFirst m k, paddedSecond α m k) ∧
      (shareWithFieldCost α m (k.1.getD .central, k.2)).time ≤ 3 :=
  shareWithFieldCost_padded_spec α m k

example (α : V4) (s t : Share V4) :
    (reconstructWithFieldCost α s t).ret = reconstruct α s t ∧
      (reconstructWithFieldCost α s t).time ≤ 4 :=
  reconstructWithFieldCost_spec α s t

end CslibFrontierTests.ImperfectRandomness
