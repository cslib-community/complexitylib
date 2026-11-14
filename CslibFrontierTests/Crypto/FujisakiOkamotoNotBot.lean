/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import CslibFrontier.Crypto.Protocols.KEM.FujisakiOkamoto.NotBot
public import CslibFrontierTests.Crypto.FujisakiOkamoto
import CslibFrontier.Probability.PMF.Bind

/-!
# Tests for the ROM IND-CCA theorem of `FO-notbot`

Exercises `Scheme.indCcaRomAdvantage_le` on two concrete schemes:
1. `notBotScheme` (`identityPKE` with uniform `Fin 4` messages, `DeltaCorrect 0`, `GammaSpread 0`)
   against the query-bounded adversary `queryCiphertextGAdv`.
2. `pairCoinScheme` (`pairCoinPKE` with uniform `Fin 16` messages and coins, uniform `Fin 2` keys,
   `DeltaCorrect 0`, `GammaSpread 4`) against `probeZeroKeyAdv` (`qG = 0`, `qH = 1`), where the
   two-stage IND-CPA reduction has advantage `0` and `Scheme.indCcaRomAdvantage_le` yields the
   non-trivial bound `indCcaRomAdvantage ≤ 3 / 8`.
-/

@[expose] public section

open Cslib Cslib.Crypto Cslib.Crypto.Protocols Cslib.Crypto.Protocols.FujisakiOkamoto
open Cslib.Probability
open CslibFrontierTests.Crypto.FujisakiOkamoto
open scoped ENNReal NNReal

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
the IND-CCA advantage of `queryCiphertextGAdv` is at most twice the IND-CPA advantage of the one
reduction `romCpaReduction` plus `1 / 2 + 2`. -/
example :
    (notBotScheme.indCcaRomAdvantage (.ofDeterministic queryCiphertextGAdv) : ℝ) ≤
      2 * (notBotScheme.pke.cpaAdvantage
        (notBotScheme.romCpaReduction (.ofDeterministic queryCiphertextGAdv)) : ℝ) +
        (1 / 2 + 2) := by
  refine (notBotScheme.indCcaRomAdvantage_le (.ofDeterministic queryCiphertextGAdv)
    (fun _ => queryCiphertextGAdv_bounds) notBotScheme_sampleMsg_uniform
    identityPKE_deltaCorrect_zero identityPKE_gammaSpread_zero).trans (le_of_eq ?_)
  simp only [Fintype.card_fin]
  norm_num
  ring

/-! ### Informative `3 / 8` security-bound client with `γ = 4` and uniform keys -/

/-- Explicit-coin PKE over `Fin 16` with uniform coins `r ← Fin 16`, `Enc(m; r) = (m, r)`, and
`Dec((m, r)) = some m`. -/
def pairCoinPKE : ExplicitCoinPKE Unit Unit (Fin 16) (Fin 16) (Fin 16 × Fin 16) where
  keyGen := pure ((), ())
  sampleCoins := ProbComp.unifFin 15
  encDet _ m r := (m, r)
  dec _ c := some c.1

/-- `pairCoinPKE` is perfectly correct (`DeltaCorrect 0`). -/
theorem pairCoinPKE_deltaCorrect_zero : pairCoinPKE.DeltaCorrect 0 :=
  pairCoinPKE.deltaCorrect_zero_of_perfect fun _ _ _ _ _ _ => rfl

/-- `pairCoinPKE` is `4`-spread (`2 ^ (-4) = 1 / 16`) because each ciphertext `(m', r')` is hit by
at most one coin `r = r'` in `Fin 16`. -/
theorem pairCoinPKE_gammaSpread_four : pairCoinPKE.GammaSpread 4 := by
  intro pk sk _ m c
  have hsub : {r : Fin 16 | pairCoinPKE.encDet pk m r = c} ⊆ {c.2} := by
    intro r hr
    exact congrArg Prod.snd hr
  have hle : (ProbComp.eval pairCoinPKE.sampleCoins).toOuterMeasure
      {r : Fin 16 | pairCoinPKE.encDet pk m r = c} ≤ (16 : ℝ≥0∞)⁻¹ := by
    refine ((ProbComp.eval pairCoinPKE.sampleCoins).toOuterMeasure.mono hsub).trans ?_
    simp [pairCoinPKE, ProbComp.eval_unifFin, PMF.uniformOfFintype_apply]
  refine (ENNReal.toReal_mono (by simp) hle).trans (le_of_eq ?_)
  rw [ENNReal.toReal_inv, ENNReal.toReal_ofNat]
  norm_num

/-- `FO-notbot` parameter bundle over `pairCoinPKE` with uniform `Fin 16` messages and uniform
`Fin 2` keys. -/
def pairCoinScheme : Scheme Unit Unit (Fin 16) (Fin 16) (Fin 16 × Fin 16) (Fin 2) where
  pke := pairCoinPKE
  sampleMsg := ProbComp.unifFin 15
  sampleKey := ProbComp.unifFin 1

/-- `pairCoinScheme` samples messages uniformly from `Fin 16`. -/
theorem pairCoinScheme_sampleMsg_uniform :
    ProbComp.eval pairCoinScheme.sampleMsg = PMF.uniformOfFintype (Fin 16) := by
  simp [pairCoinScheme]

/-- ROM adversary that queries `H(false, 0, c*)` once (`qG = 0`, `qH = 1`) and tests whether the
reply equals the challenge key `k*`. -/
def probeZeroKeyAdv : ROAdversary Unit (Fin 16) (Fin 16) (Fin 16 × Fin 16) (Fin 2) :=
  fun ch => do
    let k ← OracleComp.query (ROQuery.H (false, 0, ch.ct))
    return decide (k = ch.key)

/-- `probeZeroKeyAdv` makes `0` queries to `G` and `1` query to `H`. -/
theorem probeZeroKeyAdv_bounds : ROQueryBounds probeZeroKeyAdv 0 1 := by
  intro ⟨_, cStar, kStar⟩
  refine ⟨?_, ?_⟩
  · exact (OracleComp.IsCostBounded.query (ROQuery.H (false, 0, cStar))).bind
      fun _ => OracleComp.IsCostBounded.pure _ 0
  · exact (OracleComp.IsCostBounded.query (ROQuery.H (false, 0, cStar))).bind
      fun _ => OracleComp.IsCostBounded.pure _ 0

/-- In the simulator run of the IND-CPA reduction, `probeZeroKeyAdv` always queries `simHashG` at
`0` and never at any other message, so `(st.gCache.lookup m₁).isSome` is constantly `0 == m₁`.
This holds for every decapsulation filter, since the adversary makes no decapsulation query. -/
theorem eval_simFilterHit_probeZeroKeyAdv
    (d : Unit → List (Fin 16 × Fin 16) → Fin 16 × Fin 16 → Bool) (pk : Unit) (m₁ : Fin 16)
    (cStar : Fin 16 × Fin 16) :
    ProbComp.eval (pairCoinScheme.simFilterHit d probeZeroKeyAdv pk m₁ cStar) =
      PMF.pure (decide (m₁ = 0)) := by
  simp only [Scheme.simFilterHit, probeZeroKeyAdv,
    Scheme.simFilterHandler, Scheme.simFilterDispatch,
    Scheme.simHashH, OracleComp.interpret_bind, OracleComp.interpret_query,
    OracleComp.interpret_pure, StateT.run_bind, StateT.run_pure, ProbComp.eval_bind,
    ProbComp.eval_pure, ROQuery.dispatch]
  refine (PMF.bind_congr_on_support _ _ (fun _ => PMF.pure (decide (m₁ = 0)))
    fun kStar _ => ?_).trans (PMF.bind_const _ _)
  simp only [PMF.bind_bind]
  refine (PMF.bind_congr_on_support _ _ (fun _ => PMF.pure (decide (m₁ = 0)))
    fun z hz => ?_).trans (PMF.bind_const _ _)
  have hzca : z.2.gCache = [(0, z.1)] := by
    simp only [StateT.run, simHashG, RandomOracle.eval_zoomStateT_memoize,
      PMF.mem_support_map_iff] at hz
    obtain ⟨⟨r, c'⟩, hc', rfl⟩ := hz
    rcases (RandomOracle.mem_support_memoize_iff _ _ _ _).mp hc' with ⟨h, _⟩ | ⟨_, _, h⟩
    · simp at h
    · exact h
  refine (PMF.bind_congr_on_support _ _ (fun _ => PMF.pure (decide (m₁ = 0)))
    fun y hy => ?_).trans (PMF.bind_const _ _)
  have hyg : y.2.gCache = z.2.gCache := by
    by_cases henc : pairCoinScheme.pke.encDet pk 0 z.fst = cStar
    · simp only [StateT.run, henc, ↓reduceIte] at hy
      exact Scheme.simHashHq_gCache_eq _ _ _ _ hy
    · simp only [StateT.run, henc, ↓reduceIte] at hy
      exact Scheme.simHashHRaw_gCache_eq _ _ _ _ hy
  by_cases hm : m₁ = 0 <;> simp [hyg, hzca, hm]

/-- Because the simulator run of `probeZeroKeyAdv` ignores the challenge ciphertext, every IND-CPA
reduction `romFilterCpaReduction d` built from it has two-stage IND-CPA advantage `0` on
`pairCoinPKE`. -/
theorem pairCoinScheme_cpaAdvantage_probeZeroKeyAdv
    (d : Unit → List (Fin 16 × Fin 16) → Fin 16 × Fin 16 → Bool) :
    pairCoinScheme.pke.cpaAdvantage
      (pairCoinScheme.romFilterCpaReduction d (.ofDeterministic probeZeroKeyAdv)) = 0 := by
  have heq : ProbComp.eval (pairCoinScheme.pke.toPKE.cpaExperiment (fun _ _ _ => true)
      (pairCoinScheme.romFilterCpaReduction d (.ofDeterministic probeZeroKeyAdv)) false) =
      ProbComp.eval (pairCoinScheme.pke.toPKE.cpaExperiment (fun _ _ _ => true)
        (pairCoinScheme.romFilterCpaReduction d (.ofDeterministic probeZeroKeyAdv)) true) := by
    simp only [PKE.cpaExperiment, ProbComp.eval_bind, eval_lrExperiment,
      Scheme.romFilterCpaReduction, RandomizedROAdversary.ofDeterministic, ProbComp.eval_pure,
      PMF.bind_bind, PMF.pure_bind, eval_simFilterHit_probeZeroKeyAdv, PMF.bind_const]
  rw [ExplicitCoinPKE.cpaAdvantage, Experiment.advantage, heq]
  exact nndist_self _

/-- **Informative security bound (`≤ 3 / 8`)**: with `qG = 0`, `qH = 1`, `δ = 0`, `γ = 4`, and
`|M| = 16`, `Scheme.indCcaRomAdvantage_le` and `pairCoinScheme_cpaAdvantage_probeZeroKeyAdv`
bound the ROM IND-CCA advantage of `probeZeroKeyAdv` by `3 / 8`. -/
theorem pairCoinScheme_indCcaRomAdvantage_probeZeroKeyAdv_le :
    (pairCoinScheme.indCcaRomAdvantage (.ofDeterministic probeZeroKeyAdv) : ℝ) ≤ 3 / 8 := by
  have h := pairCoinScheme.indCcaRomAdvantage_le (.ofDeterministic probeZeroKeyAdv)
    (fun _ => probeZeroKeyAdv_bounds) pairCoinScheme_sampleMsg_uniform
    pairCoinPKE_deltaCorrect_zero pairCoinPKE_gammaSpread_four
  rw [Scheme.romCpaReduction, pairCoinScheme_cpaAdvantage_probeZeroKeyAdv] at h
  refine h.trans (le_of_eq ?_)
  simp only [Fintype.card_fin, NNReal.coe_zero]
  norm_num

end CslibFrontierTests.Crypto.FujisakiOkamotoNotBot
