/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import CslibFrontier.Crypto.Protocols.KEM.FujisakiOkamoto.NotBot
public import CslibFrontierTests.Crypto.FujisakiOkamoto

/-!
# Tests for the ROM IND-CCA theorem of `FO-notbot`

The hypotheses of `Scheme.indCcaRomAdvantage_le` are met by the perfectly correct test scheme
`notBotScheme` (`identityPKE` with uniform `Fin 4` messages, `DeltaCorrect 0`, `GammaSpread 0`)
against the query-bounded adversary `queryCiphertextGAdv`, and the theorem then yields an explicit
numeric bound.
-/

public section

open Cslib Cslib.Crypto Cslib.Crypto.Protocols Cslib.Crypto.Protocols.FujisakiOkamoto
open Cslib.Probability
open CslibFrontierTests.Crypto.FujisakiOkamoto

namespace CslibFrontierTests.Crypto.FujisakiOkamotoNotBot

/-- The FO parameter bundle of `identityScheme`: `identityPKE` with uniform `Fin 4` messages and
constant keys. -/
def notBotScheme : Scheme Unit Unit (Fin 4) Unit (Fin 4) (Fin 2) where
  pke := identityPKE
  sampleMsg := ProbComp.unifFin 3
  sampleKey := pure 0

/-- `notBotScheme` samples messages uniformly from `Fin 4`. -/
theorem notBotScheme_sampleMsg_uniform :
    ProbComp.eval notBotScheme.sampleMsg = PMF.uniformOfFintype (Fin 4) := by
  simp [notBotScheme]

/-- Instantiating `Scheme.indCcaRomAdvantage_le` with `qG = 1`, `qH = 0`, `δ = 0` and `γ = 0`:
the IND-CCA advantage of `queryCiphertextGAdv` is at most twice an IND-CPA advantage of the
reduction plus `1 / 2 + 2`. -/
example : ∃ m₀ m₁ : Fin 4, m₀ ≠ m₁ ∧
    (notBotScheme.indCcaRomAdvantage queryCiphertextGAdv : ℝ) ≤
      2 * (notBotScheme.pke.indCpaAdvantage m₀ m₁
        (notBotScheme.romCpaReduction queryCiphertextGAdv m₀ m₁) : ℝ) + (1 / 2 + 2) := by
  obtain ⟨m₀, m₁, hne, h⟩ := notBotScheme.indCcaRomAdvantage_le queryCiphertextGAdv
    queryCiphertextGAdv_bounds (by decide) notBotScheme_sampleMsg_uniform
    identityPKE_deltaCorrect_zero identityPKE_gammaSpread_zero
  refine ⟨m₀, m₁, hne, h.trans (le_of_eq ?_)⟩
  simp only [Fintype.card_fin]
  norm_num
  ring

end CslibFrontierTests.Crypto.FujisakiOkamotoNotBot
