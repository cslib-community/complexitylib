/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Crypto.Protocols.SecretSharing.ImperfectRandomness.AllOutOfR
import Mathlib.Data.ZMod.Basic

/-!
# Actual all-out-of-r constructions and coalition boundaries

Two- and three-party instances use the actual binary Galois fields. The two-party
case has three branches, the three-party case seven; the latter checks joint
privacy for a two-party coalition rather than only single-party marginals.
-/

open scoped Cslib.Probability.PMF
open Finset Cslib.Probability
open Cslib.Crypto.Protocols.SecretSharing.ImperfectRandomness
open AllOutOfR

namespace ComplexityTests.AllOutOfR

public abbrev V := GaloisField 2 3
noncomputable local instance : Fintype V := Fintype.ofFinite _
noncomputable local instance : DecidableEq V := Classical.decEq _

private theorem card_v : Fintype.card V = 8 := by
  rw [← Nat.card_eq_fintype_card, GaloisField.card 2 3 (by decide)]
  norm_num

example : Fintype.card (AllOutOfR.Branch 1) = 3 ∧
    (oddBranches 1).card = 2 ∧ (univ \ oddBranches 1).card = 1 := by
  norm_num [card_branch, card_oddBranches, card_evenBranches]

example : Fintype.card (AllOutOfR.Branch 2) = 7 ∧
    (oddBranches 2).card = 4 ∧ (univ \ oddBranches 2).card = 3 := by
  norm_num [card_branch, card_oddBranches, card_evenBranches]

/-- At `r=2,b=2`, coefficients and bit encodings really exist and reconstruct all keys. -/
example : ∃ (γ : Fin 2 → GaloisField 2 2)
    (em : GaloisField 2 2 ≃ (Fin 2 → Bool))
    (es : AllOutOfR.Share (GaloisField 2 2) ≃ (Fin 3 → Bool)),
    ∀ m k, encodedReconstruct em es γ (encodedShare em es γ m k) = m := by
  obtain ⟨γ, em, es, _, _, hc, _, _⟩ := binary_construction 1 2 (by decide) (by decide)
  exact ⟨γ, em, es, hc⟩

/-- At `r=3,b=3`, the same constructor produces a genuine three-party scheme. -/
example : ∃ (γ : Fin 3 → V) (em : V ≃ (Fin 3 → Bool))
    (es : AllOutOfR.Share V ≃ (Fin 4 → Bool)),
    ∀ m k, encodedReconstruct em es γ (encodedShare em es γ m k) = m := by
  obtain ⟨γ, em, es, _, _, hc, _, _⟩ := binary_construction 2 3 (by decide) (by decide)
  exact ⟨γ, em, es, hc⟩

example : Fintype.card (AllOutOfR.Key V 2) = 448 := by
  norm_num [card_key, card_branch, card_v]

/-- Empty and full index sets attain the exact support-size endpoints. -/
example : (OddSources.keys (oddBranches 2) (∅ : Finset (Index V 2))).card = 192 := by
  rw [AllOutOfR.card_keys]
  simp [Index, card_v]

example : (OddSources.keys (oddBranches 2) (univ : Finset (Index V 2))).card = 256 := by
  rw [AllOutOfR.card_keys]
  simp [Index, card_v]

example (u : Index V 2) : pad u 0 = u 0 ∧ pad u 1 = u 1 ∧
    pad u 2 = u 0 + u 1 := by
  change pad u (0 : Fin 2).castSucc = u 0 ∧
    pad u (1 : Fin 2).castSucc = u 1 ∧ pad u (Fin.last 2) = u 0 + u 1
  refine ⟨Fin.lastCases_castSucc _, Fin.lastCases_castSucc _, ?_⟩
  rw [pad_last, Fin.sum_univ_two]

example (j : Fin 3) : Function.Bijective (padProjection (V := V) j) :=
  padProjection_bijective j

/-- Real joint privacy for the largest unauthorized coalition in a three-party scheme. -/
example (γ : Fin 3 → V) (T : Finset (Index V 2)) (m m' : V) :
    (AllOutOfR.source (by decide : 1 ≤ 2) T).map (coalitionView γ m {0, 1}) =
      (AllOutOfR.source (by decide : 1 ≤ 2) T).map (coalitionView γ m' {0, 1}) := by
  exact coalition_privacy (by decide) γ T {0, 1} (by decide) m m'

example (γ : Fin 3 → V) (T : Finset (Index V 2)) (m m' : V) :
    (AllOutOfR.source (by decide : 1 ≤ 2) T).map (coalitionView γ m {2}) =
      (AllOutOfR.source (by decide : 1 ≤ 2) T).map (coalitionView γ m' {2}) := by
  exact coalition_privacy (by decide) γ T {2} (by decide) m m'

example (γ : Fin 3 → V) (T : Finset (Index V 2)) (m m' : V) :
    (AllOutOfR.source (by decide : 1 ≤ 2) T).map (coalitionView γ m ∅) =
      (AllOutOfR.source (by decide : 1 ≤ 2) T).map (coalitionView γ m' ∅) := by
  exact coalition_privacy (by decide) γ T ∅ (by decide) m m'

/-- Equation (9) concerns the actual uniform law of the complete joint view. -/
example (γ : Fin 3 → V) (T : Finset (Index V 2)) (m : V) :
    (AllOutOfR.source (by decide : 1 ≤ 2) T).map (view γ m 2) =
      PMF.uniformOfFinset (viewKeys 2 T) (viewKeys_nonempty (by decide) 2 T) :=
  view_law (by decide) γ m 2 T

/-- One party has no nonempty even branch: the threshold assumption is essential. -/
example : univ \ oddBranches 0 = ∅ := by
  apply card_eq_zero.mp
  norm_num [card_evenBranches]

/-- For coefficients supplied by the actual basis construction, the full joint view
of distinct messages is different, including on the smallest source. -/
example : ∃ γ : Fin 3 → V, ∀ T : Finset (Index V 2),
    (AllOutOfR.source (by decide : 1 ≤ 2) T).map (share γ 0) ≠
      (AllOutOfR.source (by decide : 1 ≤ 2) T).map (share γ 1) := by
  obtain ⟨γ, hγ⟩ := exists_coefficients (n := 2) (b := 3) (by decide)
  exact ⟨γ, fun T => full_view_not_private hγ _ zero_ne_one⟩

example (T : Finset (Index V 2)) :
    (6 : ℝ) + Real.logb 2 3 ≤ PMF.minEntropy (AllOutOfR.source (by decide : 1 ≤ 2) T) := by
  simpa using source_minEntropy_at_bit_size (by decide : 1 ≤ 2)
    (b := 3) (by simpa using card_v) T

/-- All positive output lengths are obstructed on the actual three-party source family. -/
example (ℓ : ℕ) (hℓ : 0 < ℓ) (ext : AllOutOfR.Key V 2 → (Fin ℓ → Bool)) :
    ∃ T, (1 : ℝ) / 14 ≤ dist
      ((AllOutOfR.source (by decide : 1 ≤ 2) T).map ext)
      (PMF.uniformOfFintype (Fin ℓ → Bool)) := by
  have h := AllOutOfR.no_string_extractor (by decide : 1 ≤ 2) ℓ hℓ ext
  norm_num at h
  exact h

/-- The actual three-party pad index admits an extractor with attained error exactly 1/14. -/
example : ∃ g : Index V 2 → Bool,
    (∀ T, dist ((AllOutOfR.source (by decide : 1 ≤ 2) T).map (fun k => g k.2))
      (PMF.uniformOfFintype Bool) ≤ (1 : ℝ) / 14) ∧
    (∃ T, dist ((AllOutOfR.source (by decide : 1 ≤ 2) T).map (fun k => g k.2))
      (PMF.uniformOfFintype Bool) = (1 : ℝ) / 14) := by
  obtain ⟨g, _, hu, ht⟩ := AllOutOfR.exists_tight_index_extractor
    (by decide : 1 ≤ 2) (b := 3) (by decide) (by simpa using card_v)
  exact ⟨g, by norm_num at hu; exact hu, by norm_num at ht; exact ht⟩

/-- The full bundle's same coefficients/encodings reconstruct and have sharp extraction
bounds, with no leftover source, coefficient or pad assumptions. -/
example : ∃ (γ : Fin 3 → V) (em : V ≃ (Fin 3 → Bool))
    (es : AllOutOfR.Share V ≃ (Fin 4 → Bool)),
    (∀ m k, encodedReconstruct em es γ (encodedShare em es γ m k) = m) ∧
    (∀ ext : AllOutOfR.Key V 2 → (Fin 2 → Bool), ∃ T,
      (1 : ℝ) / 14 ≤ dist ((AllOutOfR.source (by decide : 1 ≤ 2) T).map ext)
        (PMF.uniformOfFintype (Fin 2 → Bool))) ∧
    (∃ g : Index V 2 → (Fin 1 → Bool),
      (∀ T, dist ((AllOutOfR.source (by decide : 1 ≤ 2) T).map (fun k => g k.2))
        (PMF.uniformOfFintype (Fin 1 → Bool)) ≤ (1 : ℝ) / 14) ∧
      (∃ T, dist ((AllOutOfR.source (by decide : 1 ≤ 2) T).map (fun k => g k.2))
        (PMF.uniformOfFintype (Fin 1 → Bool)) = (1 : ℝ) / 14)) := by
  obtain ⟨γ, em, es, _, _, hc, _, _, _, hl, g, _, hu, ht⟩ :=
    binary_separation 2 3 (by decide) (by decide)
  exact ⟨γ, em, es, hc, by have h := hl 2 (by decide); norm_num at h; exact h,
    g, by norm_num at hu; exact hu, by norm_num at ht; exact ht⟩

open scoped Classical in
/-- The r=2 specialization has the paper's sharp 1/6 constant as well. -/
example :
    let W := GaloisField 2 2
    let : Fintype W := Fintype.ofFinite _
    ∃ g : Index W 1 → (Fin 1 → Bool),
      (∀ T, dist ((AllOutOfR.source (by decide : 1 ≤ 1) T).map (fun k => g k.2))
        (PMF.uniformOfFintype (Fin 1 → Bool)) ≤ (1 : ℝ) / 6) ∧
      (∃ T, dist ((AllOutOfR.source (by decide : 1 ≤ 1) T).map (fun k => g k.2))
        (PMF.uniformOfFintype (Fin 1 → Bool)) = (1 : ℝ) / 6) := by
  classical
  obtain ⟨_, _, _, _, _, _, _, _, _, _, g, _, hu, ht⟩ :=
    binary_separation 1 2 (by decide) (by decide)
  exact ⟨g, by norm_num at hu; exact hu, by norm_num at ht; exact ht⟩

end ComplexityTests.AllOutOfR
