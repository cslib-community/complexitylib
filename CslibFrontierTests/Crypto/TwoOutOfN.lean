/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.SecretSharing.ImperfectRandomness.TwoOutOfN
import Mathlib.Tactic

/-!
# Two-out-of-n regression clients

Boundary message sizes, actual source choices and authorized/unauthorized coalitions for
STOC submission 886, Section 4. Slopes are obtained from the proved existence theorem.
-/

open Cslib.Crypto.Protocols.SecretSharing.ImperfectRandomness
open Cslib.Crypto.Protocols.SecretSharing.ImperfectRandomness.TwoOutOfN
open Cslib.Probability Finset
open scoped Cslib.Probability.PMF

namespace TwoOutOfNTests

/-- The four-element binary field used by the boundary clients. -/
public abbrev V := GaloisField 2 2
noncomputable local instance : Fintype V := Fintype.ofFinite _
noncomputable local instance : DecidableEq V := Classical.decEq _

private theorem field_card : Fintype.card V = 4 := by
  rw [← Nat.card_eq_fintype_card, GaloisField.card 2 2 (by decide)]
  norm_num

private theorem slope_exists : ∃ α : Fin 3 → V, Function.Injective α ∧ ∀ j, α j ≠ 0 :=
  exists_slopes (by rw [field_card]; decide)

private noncomputable def α : Fin 3 → V := Classical.choose slope_exists
private theorem slope_injective : Function.Injective α := (Classical.choose_spec slope_exists).1
private theorem slope_nonzero : ∀ j, α j ≠ 0 := (Classical.choose_spec slope_exists).2

-- Both n=2 and n=3 have actual literal-bit schemes at their smallest allowed b=2.
example : ∃ (_em : V ≃ (Fin 2 → Bool)) (_es : Share V ≃ (Fin 3 → Bool))
    (a : Fin 2 → V), Function.Injective a ∧ ∀ m k,
    reconstruct (a 0) (a 1) (share a 0 m k) (share a 1 m k) = m := by
  obtain ⟨em, es, a, ha, _, _, _⟩ := binary_construction 2 2 (by decide) (by decide)
  exact ⟨em, es, a, ha, fun m k => reconstruct_share ha (by decide) m k⟩

example : ∃ (em : V ≃ (Fin 2 → Bool)) (es : Share V ≃ (Fin 3 → Bool))
    (a : Fin 3 → V), Function.Injective a ∧ ∀ m k,
    (∃ rec : (({0, 2} : Finset (Fin 3)) → (Fin 3 → Bool)) → (Fin 2 → Bool),
      rec (bitView a em es {0, 2} m k) = m) := by
  obtain ⟨em, es, a, ha, _, _, hrec, _⟩ := binary_construction 3 2 (by decide) (by decide)
  obtain ⟨rec, hr⟩ := hrec {0, 2} (by decide)
  exact ⟨em, es, a, ha, fun m k => ⟨rec, hr m k⟩⟩

-- n=2,b=1 and n=3,b=1 lie outside the construction's field-size hypothesis.
example : ¬ (2 < 2 ^ 1) ∧ ¬ (3 < 2 ^ 1) := by decide

-- Only the owning side party sees a tag; both other parties receive ordinary shares.
example (m i : V) : share α 1 m (.inr 1, i) = .inr i ∧
    share α 0 m (.inr 1, i) = .inl (α 0 * i + m) ∧
    share α 2 m (.inr 1, i) = .inl (α 2 * i + m) := by
  simp [share]

-- The duplicated central branches are distinct keys with identical complete sharing outputs.
example (m i : V) : ((Sum.inl (0 : Fin 2), i) : Key 3 V) ≠ (Sum.inl (1 : Fin 2), i) ∧
    view α univ m (.inl 0, i) = view α univ m (.inl 1, i) := by
  constructor
  · simp
  · rfl

example (m : V) (k : Key 3 V) :
    reconstruct (α 0) (α 2) (share α 0 m k) (share α 2 m k) = m :=
  reconstruct_share slope_injective (by decide) m k

-- A real unauthorized singleton and the empty coalition have message-independent joint laws.
example (T : Finset V) :
    (source (by decide : 2 ≤ 3) T).map (view α {1} 0) =
      (source (by decide : 2 ≤ 3) T).map (view α {1} 1) ∧
    (source (by decide : 2 ≤ 3) T).map (view α ∅ 0) =
      (source (by decide : 2 ≤ 3) T).map (view α ∅ 1) := by
  exact ⟨unauthorized_privacy (by decide) α slope_nonzero {1} (by decide) T 0 1,
    unauthorized_privacy (by decide) α slope_nonzero ∅ (by decide) T 0 1⟩

-- The full authorized coalition is not private: its reconstruction separates 0 and 1.
example (T : Finset V) :
    (source (by decide : 2 ≤ 3) T).map (view α univ 0) ≠
      (source (by decide : 2 ≤ 3) T).map (view α univ 1) := by
  obtain ⟨rec, hr⟩ := authorized_correctness slope_injective univ (by decide)
  intro h
  have hh := congrArg (fun p => PMF.map rec p) h
  have hc (m : V) : rec ∘ view α univ m = Function.const _ m := funext (hr m)
  rw [PMF.map_comp, PMF.map_comp, hc, hc, PMF.map_const, PMF.map_const] at hh
  have he := congrArg (fun p : PMF V => p 0) hh
  simp at he

-- Extremal source choices attain both support bounds, without dropping any branch choices.
example : (OddSources.keys (central 3) (∅ : Finset V)).card = 12 ∧
    (OddSources.keys (central 3) (univ : Finset V)).card = 8 ∧
    Fintype.card (Key 3 V) = 20 := by
  simp [card_keys (by decide : 2 ≤ 3), field_card, card_key (by decide : 2 ≤ 3)]

example (T : Finset V) : 8 ≤ (OddSources.keys (central 3) T).card ∧
    (OddSources.keys (central 3) T).card ≤ 12 := by
  simpa only [field_card, Nat.reduceSub, Nat.reduceMul] using
    card_keys_bounds (by decide : 2 ≤ 3) T

example (T : Finset V) : (3 : ℝ) ≤ PMF.minEntropy (source (by decide : 2 ≤ 3) T) := by
  have he := source_minEntropy (by decide : 2 ≤ 3) T
  norm_num only [field_card, Nat.reduceSub, Nat.reduceMul, Nat.cast_ofNat] at he
  have hl : Real.logb 2 (8 : ℝ) = 3 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.logb_pow,
      Real.logb_self_eq_one (by norm_num)]
    norm_num
  rwa [hl] at he

-- The tag probabilities also check the actual PMF laws at both extremal choices.
example : (((source (by decide : 2 ≤ 3) (∅ : Finset V)).map (share α 1 0))
    (.inr 0)).toReal = 1 / 12 := by
  rw [share_apply_inr (by decide) α slope_nonzero]
  norm_num [card_keys (by decide : 2 ≤ 3), field_card]

example : (((source (by decide : 2 ≤ 3) (univ : Finset V)).map (share α 1 0))
    (.inr 0)).toReal = 0 := by
  rw [share_apply_inr (by decide) α slope_nonzero]
  simp

example : (((source (by decide : 2 ≤ 3) (univ : Finset V)).map (share α 1 0))
    (.inl 0)).toReal = 1 / 4 := by
  rw [share_apply_inl (by decide) α slope_nonzero]
  norm_num [card_keys (by decide : 2 ≤ 3), field_card]

example : ¬ (central 1).Nonempty := by simp [central]

-- The full endpoint supplies both arbitrary three-bit failure and an actual tight index map.
example : ∃ g : V → Bool,
    (∀ T, dist ((source (by decide : 2 ≤ 3) T).map (fun k => g k.2))
      (PMF.uniformOfFintype Bool) ≤ 1 / 10) ∧
    (∃ T, dist ((source (by decide : 2 ≤ 3) T).map (fun k => g k.2))
      (PMF.uniformOfFintype Bool) = 1 / 10) ∧
    (∀ ext : Key 3 V → (Fin 3 → Bool), ∃ T,
      1 / 10 ≤ dist ((source (by decide : 2 ≤ 3) T).map ext)
        (PMF.uniformOfFintype (Fin 3 → Bool))) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hlow, g, hu, ht⟩ :=
    binary_theorem4_1 3 2 (by decide) (by decide)
  norm_num at hlow hu ht
  exact ⟨g, hu, ht, fun ext => hlow 3 (by decide) ext⟩

-- At n=2 the same actual constructor attains the paper's 1/6 boundary constant.
example : ∃ g : V → Bool,
    (∀ T, dist ((source (by decide : 2 ≤ 2) T).map (fun k => g k.2))
      (PMF.uniformOfFintype Bool) ≤ 1 / 6) ∧
    (∃ T, dist ((source (by decide : 2 ≤ 2) T).map (fun k => g k.2))
      (PMF.uniformOfFintype Bool) = 1 / 6) := by
  have hev : Even (Fintype.card V) := by rw [field_card]; decide
  obtain ⟨g, _, hu, ht⟩ := exists_tight_index_extractor (by decide : 2 ≤ 2) hev
  norm_num at hu ht
  exact ⟨g, hu, ht⟩

end TwoOutOfNTests
