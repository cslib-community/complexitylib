/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Crypto.Computational.Rompel
import Complexity.Tactic.PPT

/-!
# Tests for Rompel target collision-resistant hashing and digital signatures

Checks concrete schedule identities, unconditional pigeonhole step-collision extraction for
`rompelCandidateEval` (`exists_rompelCascadeInput_collision`), plain `IsPPT` certification and
concrete loss bounds for `rompelCompressionInverter` and `rompelCompression`, unrestricted digest
widths for `rompelHash`, and the full signature sufficiency and equivalence endpoints in
`Complexity.Crypto.Computational.Rompel` (`OneWay.exists_indexedEUFCMA_two`,
`OneWay.exists_counterEUFCMA_two`, `OneWay.exists_eufCMA`, `exists_oneWay_iff_exists_signature`,
`exists_oneTimeSignature_iff_exists_signature`).
-/

namespace ComplexityTests.Crypto.Rompel

open Cslib Cslib.Crypto Cslib.Probability Turing.MultiTapeTM
open scoped NNReal

/-! ### 1. Schedule, block-width, and key-width checks -/

example (G : ShrinkingCollisionGrid) (n : ℕ) :
    1 ≤ rompelCascadeSteps G n ∧
      G.outLen n + rompelCascadeSteps G n = 2 * rompelBlockLen G n ∧
      n ≤ rompelBlockLen G n :=
  ⟨rompelCascadeSteps_pos G n, outLen_add_rompelCascadeSteps G n, le_rompelBlockLen G n⟩

/-- Concrete parameter check when `G.gridCount n = 2` and `G.outLen n = 3` (`G.inLen n = 4`):
each candidate folds `3 * 3 = 9` shifted `4 → 3` steps, compressing `12` bits to `3` bits, and
concatenating both candidates yields a `12 → 6` `KeyedCompressionFamily` with `36`-bit key. -/
theorem rompel_schedule_two_three (G : ShrinkingCollisionGrid) {n : ℕ}
    (hk : G.gridCount n = 2) (hout : G.outLen n = 3) :
    rompelCascadeSteps G n = 9 ∧ rompelBlockLen G n = 6 ∧ rompelKeyLen G n = 36 := by
  have hin : G.inLen n = 4 := by
    have h1 := G.outLen_add_one n
    omega
  simp only [rompelCascadeSteps, rompelBlockLen, rompelKeyLen, hk, hout, hin]
  decide

example (G : ShrinkingCollisionGrid) (n : ℕ) (K msg : List Bool)
    (hK : K.length = (rompelHash G).keyLen n) :
    ((rompelHash G).eval n K msg).length = rompelBlockLen G n :=
  (rompelHash G).length_eq n K msg hK

/-! ### 2. Unconditional pigeonhole non-vacuity of `exists_rompelCascadeInput_collision` -/

/-- For every `ShrinkingCollisionGrid` `G`, security parameter `n`, candidate `q`, and key `K`,
strict compression `G.outLen n < 2 * rompelBlockLen G n` guarantees distinct
`2 * rompelBlockLen G n`-bit inputs `x₀ ≠ x₁` colliding under `rompelCandidateEval G n q K`, from
which `exists_rompelCascadeInput_collision` extracts an in-range step collision
`i < rompelCascadeSteps G n` under `rompelShiftedStep`. -/
theorem exists_rompelCandidateEval_step_collision (G : ShrinkingCollisionGrid)
    (n q : ℕ) (K : List Bool) :
    ∃ (x₀ x₁ : List Bool) (i : ℕ),
      x₀.length = 2 * rompelBlockLen G n ∧
      x₁.length = 2 * rompelBlockLen G n ∧
      x₀ ≠ x₁ ∧
      i < rompelCascadeSteps G n ∧
      rompelCascadeInput G n q i K x₀ ≠ rompelCascadeInput G n q i K x₁ ∧
      rompelShiftedStep G n q (BitString.listRow (G.inLen n) i K)
          (rompelCascadeInput G n q i K x₀) =
        rompelShiftedStep G n q (BitString.listRow (G.inLen n) i K)
          (rompelCascadeInput G n q i K x₁) := by
  let M := 2 * rompelBlockLen G n
  let L := G.outLen n
  have hlt : L < M := by
    have hpos := rompelCascadeSteps_pos G n
    have hsum := outLen_add_rompelCascadeSteps G n
    omega
  let evalFin : BitString M → BitString L :=
    fun b => BitString.ofList L (rompelCandidateEval G n q K (List.ofFn b))
  have hcard : Fintype.card (BitString L) < Fintype.card (BitString M) := by
    simp only [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]
    exact Nat.pow_lt_pow_right (by decide : 1 < 2) hlt
  obtain ⟨b₀, b₁, hb_ne, hmap⟩ := Fintype.exists_ne_map_eq_of_card_lt evalFin hcard
  let x₀ := List.ofFn b₀
  let x₁ := List.ofFn b₁
  have hx₀ : x₀.length = M := List.length_ofFn
  have hx₁ : x₁.length = M := List.length_ofFn
  have hne : x₀ ≠ x₁ := fun h => hb_ne (List.ofFn_injective h)
  have hcol : rompelCandidateEval G n q K x₀ = rompelCandidateEval G n q K x₁ := by
    rw [← BitString.ofFn_ofList (length_rompelCandidateEval G n q K x₀),
      ← BitString.ofFn_ofList (length_rompelCandidateEval G n q K x₁)]
    exact congrArg List.ofFn hmap
  obtain ⟨i, hi, hw_ne, hw_col⟩ := exists_rompelCascadeInput_collision G hx₀ hx₁ hne hcol
  exact ⟨x₀, x₁, i, hx₀, hx₁, hne, hi, hw_ne, hw_col⟩

/-! ### 3. Concrete strict-PPT adversary and `rompelCompressionInverter` checks -/

/-- Explicit two-stage strict-PPT `TargetCollisionFinder` against `rompelCompression G`: Stage 1
commits to `0^{2 * rompelBlockLen G n}` and Stage 2 outputs `1 0^{2 * rompelBlockLen G n - 1}`. -/
def zeroFlipFinder (G : ShrinkingCollisionGrid) : TargetCollisionFinder where
  choose n := pure (List.replicate (2 * rompelBlockLen G n) false, [])
  find n _ _ := pure ([true] ++ List.replicate (2 * rompelBlockLen G n - 1) false)

theorem isPPT_zeroFlipFinder (G : ShrinkingCollisionGrid) : (zeroFlipFinder G).IsPPT where
  choose := by
    dsimp only [zeroFlipFinder]
    ppt
  find := by
    dsimp only [zeroFlipFinder]
    ppt

example (G : ShrinkingCollisionGrid) :
    IsPPT encBits (rompelCompressionInverter G (zeroFlipFinder G)) :=
  isPPT_rompelCompressionInverter G (isPPT_zeroFlipFinder G)

example (G : ShrinkingCollisionGrid) (n : ℕ) :
    Game.succProbability
      (ProbComp.eval
        (targetCollisionGame (rompelCompression G).keyLen (rompelCompression G).eval
          (rompelCompression G).validInput (zeroFlipFinder G) n)) ≤
      (dyadicSize (G.gridCount n) * dyadicSize (rompelCascadeSteps G n) : ℝ≥0) *
        Game.succProbability
          (ProbComp.eval
            (randomCollisionGame (fun k => G.evalGrid k 0) G.inLen
              (rompelCompressionInverter G (zeroFlipFinder G)) n)) :=
  succProbability_targetCollisionGame_rompelCompression_le G (zeroFlipFinder G) (G.gridCount_pos n)

/-! ### 4. Target collision-resistant hashing and Rompel signature endpoints -/

example (G : ShrinkingCollisionGrid) :
    (rompelCompression G).TargetCollisionResistant ∧ (rompelHash G).TargetCollisionResistant :=
  ⟨G.targetCollisionResistant_rompelCompression, G.targetCollisionResistant_rompelHash⟩

example {f : List Bool → List Bool} (hf : OneWay f) :
    (∃ C : KeyedCompressionFamily, C.TargetCollisionResistant) ∧
      ∃ H : KeyedHashFamily, H.TargetCollisionResistant :=
  ⟨hf.exists_targetCollisionResistant_keyedCompressionFamily,
    hf.exists_targetCollisionResistant_keyedHashFamily⟩

example {f : List Bool → List Bool} (hf : OneWay f) :
    (∃ S : IndexedSignatureScheme, (∀ n, S.capacity n = 2) ∧ S.IndexedEUFCMA) ∧
      ∃ S : IndexedSignatureScheme, (∀ n, S.capacity n = 2) ∧ S.CounterEUFCMA :=
  ⟨hf.exists_indexedEUFCMA_two, hf.exists_counterEUFCMA_two⟩

example {f : List Bool → List Bool} (hf : OneWay f) :
    ∃ S : SignatureScheme, S.EUFCMA :=
  hf.exists_eufCMA

example : (∃ f, OneWay f) ↔ ∃ S : SignatureScheme, S.EUFCMA :=
  exists_oneWay_iff_exists_signature

example : (∃ S : SignatureScheme, S.OneTimeEUFCMA) ↔ ∃ S : SignatureScheme, S.EUFCMA :=
  exists_oneTimeSignature_iff_exists_signature

/-- Converse non-vacuity check: if no uniform `OneWay` function exists, no `SignatureScheme` can
satisfy `EUFCMA`. -/
theorem not_exists_eufCMA_of_forall_not_oneWay (hno : ∀ f, ¬ OneWay f)
    (S : SignatureScheme) : ¬ S.EUFCMA := by
  intro hS
  obtain ⟨f, hf⟩ := exists_oneWay_iff_exists_signature.mpr ⟨S, hS⟩
  exact hno f hf

end ComplexityTests.Crypto.Rompel
