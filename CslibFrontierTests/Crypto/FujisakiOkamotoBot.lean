/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import CslibFrontier.Crypto.Protocols.KEM.FujisakiOkamoto.SpreadNecessity
public import CslibFrontierTests.Crypto.FujisakiOkamotoNotBot

/-!
# Tests for the ROM IND-CCA theorem and `γ`-spreadness necessity of `FO^⊥`

Exercises `CslibFrontier.Crypto.Protocols.KEM.FujisakiOkamoto.Bot` and
`CslibFrontier.Crypto.Protocols.KEM.FujisakiOkamoto.SpreadNecessity` on concrete schemes:
1. `pairCoinScheme` (`pairCoinPKE` with uniform `Fin 16` messages and coins, uniform `Fin 2` keys,
   `DeltaCorrect 0`, `GammaSpread 4`) against `probeZeroKeyAdv` (`qG = 0`, `qH = 1`, `qD = 0`),
   where `Scheme.indCcaBotAdvantage_le` yields the tighter bound `indCcaBotAdvantage ≤ 1 / 4`
   (versus `3 / 8` for `FO-notbot`, since `FO^⊥` has no `2 qH / |M|` fallback seed-guessing term).
2. `unspreadPointPKE pairCoinPKE 0` and `unspreadScheme pairCoinPKE 0`: `0`-correct, preserves
   IND-CPA advantages away from `0`, fails `4`-spreadness, and lets the 1-query decapsulation probe
   `probeDecapsAdv` (`qG = 0`, `qH = 0`, `qD = 1`) distinguish `eagerIndCcaBotGame` from
   `simBotGame` with advantage `15 / 16`.
-/

public section

open Cslib Cslib.Crypto Cslib.Crypto.Protocols Cslib.Crypto.Protocols.FujisakiOkamoto
open Cslib.Probability
open CslibFrontierTests.Crypto.FujisakiOkamoto
open CslibFrontierTests.Crypto.FujisakiOkamotoNotBot
open scoped ENNReal NNReal

namespace CslibFrontierTests.Crypto.FujisakiOkamotoBot

/-- `probeZeroKeyAdv` makes `0` queries to `G`, `1` query to `H`, and `0` queries to `decaps`. -/
theorem probeZeroKeyAdv_fullBounds : ROFullQueryBounds probeZeroKeyAdv 0 1 0 := by
  refine ⟨probeZeroKeyAdv_bounds, fun ⟨_, cStar, _⟩ => ?_⟩
  exact OracleComp.IsCostBounded.liftBind (ROQuery.H (false, 0, cStar)) _ 0
    fun _ => OracleComp.IsCostBounded.pure _ 0

/-- Because `probeZeroKeyAdv` makes no decapsulation queries, `romBotCpaReduction` and
`romCpaReduction` are equal on `probeZeroKeyAdv`. -/
theorem romBotCpaReduction_probeZeroKeyAdv_eq (m₀ m₁ : Fin 16) :
    pairCoinScheme.romBotCpaReduction probeZeroKeyAdv m₀ m₁ =
      pairCoinScheme.romCpaReduction probeZeroKeyAdv m₀ m₁ := by
  funext pk cStar
  simp [Scheme.romBotCpaReduction, Scheme.romFilterCpaReduction, Scheme.romCpaReduction,
    Scheme.simFilterHandler, Scheme.simFilterDispatch, probeZeroKeyAdv, OracleComp.interpret_query,
    ROQuery.dispatch]

/-- The two-message IND-CPA advantage of `romBotCpaReduction probeZeroKeyAdv` on `pairCoinPKE` is
`0` for every pair `(m₀, m₁)`. -/
theorem pairCoinScheme_indCpaAdvantage_romBotCpaReduction_probeZeroKeyAdv (m₀ m₁ : Fin 16) :
    pairCoinScheme.pke.indCpaAdvantage m₀ m₁
      (pairCoinScheme.romBotCpaReduction probeZeroKeyAdv m₀ m₁) = 0 := by
  rw [romBotCpaReduction_probeZeroKeyAdv_eq]
  exact pairCoinScheme_indCpaAdvantage_probeZeroKeyAdv m₀ m₁

/-- **Informative `FO^⊥` security bound (`≤ 1 / 4`)**: with `qG = 0`, `qH = 1`, `qD = 0`, `δ = 0`,
`γ = 4`, and `|M| = 16`, `Scheme.indCcaBotAdvantage_le` bounds the ROM IND-CCA advantage of
`probeZeroKeyAdv` against `FO^⊥` by `1 / 4`. -/
theorem pairCoinScheme_indCcaBotAdvantage_probeZeroKeyAdv_le :
    (pairCoinScheme.indCcaBotAdvantage probeZeroKeyAdv : ℝ) ≤ 1 / 4 := by
  obtain ⟨m₀, m₁, _, h⟩ := pairCoinScheme.indCcaBotAdvantage_le probeZeroKeyAdv
    probeZeroKeyAdv_fullBounds (by decide) pairCoinScheme_sampleMsg_uniform
    pairCoinPKE_deltaCorrect_zero pairCoinPKE_gammaSpread_four
  rw [pairCoinScheme_indCpaAdvantage_romBotCpaReduction_probeZeroKeyAdv] at h
  refine h.trans (le_of_eq ?_)
  simp only [Fintype.card_fin, NNReal.coe_zero]
  norm_num

/-! ### Concrete checks for `unspreadPointPKE` and `probeDecapsAdv` -/

/-- `unspreadPointPKE pairCoinPKE 0` remains perfectly correct (`DeltaCorrect 0`). -/
example : (unspreadPointPKE pairCoinPKE 0).DeltaCorrect 0 :=
  unspreadPointPKE_deltaCorrect pairCoinPKE 0 pairCoinPKE_deltaCorrect_zero

/-- `unspreadPointPKE pairCoinPKE 0` preserves IND-CPA advantage on `1 ≠ 0` and `2 ≠ 0`. -/
example (A : Unit → Option (Fin 16 × Fin 16) → ProbComp Bool) :
    (unspreadPointPKE pairCoinPKE 0).indCpaAdvantage 1 2 A =
      pairCoinPKE.indCpaAdvantage 1 2 (fun pk c => A pk (some c)) :=
  unspreadPointPKE_indCpaAdvantage pairCoinPKE 0 1 2 (by decide) (by decide) A

/-- `unspreadPointPKE pairCoinPKE 0` is not `4`-spread. -/
example : ¬ (unspreadPointPKE pairCoinPKE 0).GammaSpread 4 :=
  unspreadPointPKE_not_gammaSpread_of_pos pairCoinPKE 0 (by norm_num)

/-- Over `unspreadScheme pairCoinPKE 0` with uniform `Fin 16` messages, the 1-query decapsulation
probe `probeDecapsAdv` (`qG = 0, qH = 0, qD = 1`) distinguishes `eagerIndCcaBotGame` from
`simBotGame` with exact advantage `15 / 16`. -/
example (b : Bool) :
    (Game.advantage
      ((unspreadScheme pairCoinPKE 0 (ProbComp.unifFin 15) (ProbComp.unifFin 1)).eagerIndCcaBotGame
        probeDecapsAdv b)
      (ProbComp.eval ((unspreadScheme pairCoinPKE 0 (ProbComp.unifFin 15)
        (ProbComp.unifFin 1)).simBotGame probeDecapsAdv b)) : ℝ) = 15 / 16 := by
  rw [advantage_eagerIndCcaBotGame_simBotGame_probeDecapsAdv pairCoinPKE 0
    (ProbComp.unifFin 15) (ProbComp.unifFin 1) (by simp) b]
  simp only [Fintype.card_fin]
  norm_num

end CslibFrontierTests.Crypto.FujisakiOkamotoBot
