/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Analysis.RowCompression.Reference
import Mathlib.Tactic.Linarith

/-!
# Persistent closure of the rank gate

A marked collection whose actual raw first coordinates stay above `3 * G` has two possible
behaviors. As long as the default remains below `G`, every marked entry stays in the identity
region of compression and follows its raw prefix exactly. Once a threshold reaches `G`, the
new default reaches `G` and can never fall below it. With at least `K` marked retained entries,
the actual default-padded first rank is therefore at least `G` throughout the calculation.

This is the large-heavy-set branch in [OpenAI2026LogSpace, Section 8.3, Lemma 8.3]. The raw
lower bound is an explicit hypothesis here; the concrete polynomial-row client derives it
from small clipped-prefix errors and large true first entries. Neither an upper bound on the
thresholds nor agreement of exception lists is required.

## Main results

* `Cslib.RowCompression.gate_le_default_or_iterate_row_eq`: either the default closes the
  gate, or every marked compressed entry still equals its raw prefix.
* `Cslib.RowCompression.le_iterate_firstRank_of_raw_large`: enough such entries force the
  actual padded rank above the gate threshold.

## References

* [OpenAI, *Exact Derandomization of Logarithmic Space: L = RL = BPL*][OpenAI2026LogSpace],
  Section 8.3, proof of Lemma 8.3, the branch with at least `K` entries above `L₀`
  (23 September 2026, revision `7ef5c0cc`, not peer reviewed).
-/

public section

namespace Cslib.RowCompression

open Finset

variable {ι : Type*} {s D : Finset ι} {n K : ℕ → ℕ} {ρ : ℕ → ℝ}
  {Δ : ℕ → ι → Fin 2 → ℝ} {a : State ι} {G : ℝ}

/-- A large raw entry is preserved until a threshold raises the default to the gate level.
Both channels are preserved, even when the second channel is signed. -/
theorem gate_le_default_or_iterate_row_eq (m : ℕ)
    (hraw : ∀ i ≤ m, ∀ y ∈ D, 3 * G ≤ uncompressedRow Δ a.row i y 0) :
    G ≤ (iterate s n K ρ Δ a m).defaultValue ∨
      ∀ y ∈ D, (iterate s n K ρ Δ a m).row y = uncompressedRow Δ a.row m y := by
  induction m with
  | zero => exact Or.inr fun _ _ => (congrFun uncompressedRow_zero _).symm
  | succ m ih =>
    by_cases hu : G ≤ stepThreshold s n K ρ Δ a m
    · exact Or.inl (hu.trans threshold_le_newDefault)
    · have hprevious : ∀ y ∈ D, (iterate s n K ρ Δ a m).row y =
          uncompressedRow Δ a.row m y := by
        rcases ih (fun i hi => hraw i (hi.trans (Nat.le_succ m))) with hz | hw
        · exact False.elim (hu (hz.trans le_threshold))
        · exact hw
      refine Or.inr fun y hy => ?_
      have hinput : inputRow s n K ρ Δ a m y = uncompressedRow Δ a.row (m + 1) y := by
        funext ν
        rw [uncompressedRow_succ]
        change (iterate s n K ρ Δ a m).row y ν + Δ m y ν = _
        rw [hprevious y hy]
      have hlarge : 3 * stepThreshold s n K ρ Δ a m ≤
          entrySize (inputRow s n K ρ Δ a m y) := by
        have hr := hraw (m + 1) (le_refl _) y hy
        have hv := (le_abs_self (inputRow s n K ρ Δ a m y 0)).trans
          (abs_apply_le_entrySize (inputRow s n K ρ Δ a m y) 0)
        rw [hinput]
        rw [hinput] at hv
        linarith [not_le.mp hu]
      change update s (n m) (K m) (ρ m) (iterate s n K ρ Δ a m).defaultValue
        (inputRow s n K ρ Δ a m) y = _
      rw [update_eq_self_of_three_mul_le hlarge]
      exact hinput

/-- At least `k` large raw first entries close the actual padded rank gate. The compression
capacities may vary independently; no threshold upper bound is assumed. -/
theorem le_iterate_firstRank_of_raw_large {k : ℕ} (hG : 0 < G) (hk : 0 < k)
    (hDs : D ⊆ s) (hcard : k ≤ #D) (m : ℕ)
    (hraw : ∀ i ≤ m, ∀ y ∈ D, 3 * G ≤ uncompressedRow Δ a.row i y 0) :
    G ≤ firstRank s k (iterate s n K ρ Δ a m).defaultValue
      (iterate s n K ρ Δ a m).row := by
  classical
  rcases gate_le_default_or_iterate_row_eq m hraw with hz | hw
  · exact hz.trans default_le_firstRank
  · apply le_trans _ kthLargest_le_firstRank
    apply (le_kthLargest_iff hk hG).mpr
    apply hcard.trans (card_le_card ?_)
    intro y hy
    apply mem_filter.mpr ⟨hDs hy, ?_⟩
    rw [hw y hy]
    linarith [hraw m (le_refl _) y hy]

end Cslib.RowCompression
