/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.KEM.FujisakiOkamoto.Bot
import CslibFrontier.Languages.Probabilistic.Norm
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.ToReal

/-!
# The `γ`-spreadness hypothesis of `FO^⊥` is load-bearing

In the ROM IND-CCA security theorem for the explicit-rejection Fujisaki–Okamoto transform
`FO^⊥ = U^⊥ ∘ T` (`Scheme.indCcaBotAdvantage_le` and
`Scheme.advantage_eagerIndCcaBotGame_simBotGame_le` in
`CslibFrontier.Crypto.Protocols.KEM.FujisakiOkamoto.Bot`), replacing the real decapsulation
oracle `decapsBot` by the keyless simulator `simBotHandler` incurs a `qD · 2^{-γ}` term bounding the
probability that an unqueried message `m'` re-encrypts to a queried ciphertext `c` under
`T[PKE, G]` ([HofheinzHoevelmannsKiltz2017], IACR ePrint 2017/604, full version dated
2 November 2021, §3.1 and §3.2.1). This module shows that the `qD · 2^{-γ}` spreadness term cannot
be omitted.

For any explicit-coin PKE `P` and designated message `m₀ : M`, `unspreadPointPKE P m₀` has
ciphertext space `Option CT`:
* At `m = m₀`, `encDet pk m₀ r = none` deterministically (ignoring the coins `r`), and
  `dec sk none = some m₀`.
* At `m ≠ m₀`, `encDet pk m r = some (P.encDet pk m r)`, and `dec sk (some c)` returns `some m`
  when `P.dec sk c = some m` with `m ≠ m₀`, and `none` otherwise.

The modified PKE preserves `δ`-correctness (`unspreadPointPKE_deltaCorrect`) and preserves
fixed-message IND-CPA advantages (`indCpaAdvantage`) on all message pairs away from `m₀`
(`unspreadPointPKE_indCpaAdvantage`); it is not two-stage IND-CPA secure (`cpaAdvantage`), since
an adversary may choose `m₀`. It fails `γ`-spreadness for every `γ > 0`
(`unspreadPointPKE_gammaSpread_zero`, `unspreadPointPKE_not_gammaSpread_of_pos`).

The 1-query adversary `probeDecapsAdv` makes zero queries to `G`, zero queries to `H`, and a single
decapsulation query `ROQuery.decaps none` (`roFullQueryBounds_probeDecapsAdv`), outputting whether
the decapsulation oracle returns `some k`.
* In the keyless simulator game `simBotGame` (`eval_simBotGame_probeDecapsAdv`), when `m* = m₀`
  the challenge ciphertext is `c* = none` so the punctured decapsulation oracle returns `none`;
  when `m* ≠ m₀`, the only entry in `gCache` is `(m*, r*)` whose encryption is `some _ ≠ none`, so
  `simBotCheck` returns `false` and the simulator again returns `none`. Hence `simBotGame` outputs
  `false` with probability `1`.
* In the real `FO^⊥` game `roIndCcaBotGame` / `eagerIndCcaBotGame`
  (`eval_roIndCcaBotGame_probeDecapsAdv`), whenever `m* ≠ m₀` we have `c* = some _ ≠ none`, and
  `decapsBot` on `none` decrypts `none` to `some m₀` and checks `encDet pk m₀ (G m₀) = none`, which
  holds deterministically even though `m₀` was never queried to `G`. Thus `probeDecapsAdv` outputs
  `true` whenever `m* ≠ m₀`.

For a uniform message sampler on a finite message space `M`, the distinguishing advantage between
`eagerIndCcaBotGame` and `simBotGame` on `probeDecapsAdv` is therefore `1 - 1 / |M|`
(`advantage_eagerIndCcaBotGame_simBotGame_probeDecapsAdv`), matching the `qD · 2^{-γ}` term of
`advantage_eagerIndCcaBotGame_simBotGame_le` at `δ = 0, qG = 0, qH = 0, qD = 1, γ = 0`.

## Main definitions

* `Cslib.Crypto.Protocols.FujisakiOkamoto.unspreadPointPKE`: point-deterministic PKE variant
  encrypting `m₀` to `none` and `m ≠ m₀` to `some (P.encDet pk m r)`.
* `Cslib.Crypto.Protocols.FujisakiOkamoto.unspreadScheme`: `Scheme` wrapper around
  `unspreadPointPKE P m₀`.
* `Cslib.Crypto.Protocols.FujisakiOkamoto.probeDecapsAdv`: 1-query adversary querying
  `ROQuery.decaps none` and testing `Option.isSome`.

## Main results

* `Cslib.Crypto.Protocols.FujisakiOkamoto.unspreadPointPKE_deltaCorrect`,
  `Cslib.Crypto.Protocols.FujisakiOkamoto.unspreadPointPKE_indCpaAdvantage`,
  `Cslib.Crypto.Protocols.FujisakiOkamoto.unspreadPointPKE_gammaSpread_zero`,
  `Cslib.Crypto.Protocols.FujisakiOkamoto.unspreadPointPKE_not_gammaSpread_of_pos`:
  `unspreadPointPKE P m₀` preserves `δ`-correctness and fixed-message IND-CPA advantages
  (`indCpaAdvantage`) away from `m₀`, is
  `0`-spread, and is not `γ`-spread for any `γ > 0`.
* `Cslib.Crypto.Protocols.FujisakiOkamoto.roFullQueryBounds_probeDecapsAdv`: `probeDecapsAdv`
  satisfies `ROFullQueryBounds probeDecapsAdv 0 0 1`.
* `Cslib.Crypto.Protocols.FujisakiOkamoto.eval_simBotGame_probeDecapsAdv`,
  `Cslib.Crypto.Protocols.FujisakiOkamoto.eval_roIndCcaBotGame_probeDecapsAdv`: exact output
  distributions of `simBotGame` and `roIndCcaBotGame` on `probeDecapsAdv`.
* `Cslib.Crypto.Protocols.FujisakiOkamoto.advantage_eagerIndCcaBotGame_simBotGame_probeDecapsAdv`:
  for uniform messages, `probeDecapsAdv` distinguishes `eagerIndCcaBotGame` from `simBotGame` with
  advantage `1 - 1 / |M|` using `qG = 0, qH = 0, qD = 1`.

## References

* [D. Hofheinz, K. Hövelmanns, E. Kiltz, *A Modular Analysis of the Fujisaki–Okamoto
  Transformation*][HofheinzHoevelmannsKiltz2017] (IACR ePrint 2017/604, full version dated
  2 November 2021, §3.1 and §3.2.1).
-/

public section

namespace Cslib.Crypto.Protocols.FujisakiOkamoto

open Probability
open Probability.PMF
open scoped ENNReal NNReal

variable {PK SK M R CT K : Type}

section UnspreadPKE

variable [DecidableEq M]

/-- Point-deterministic variant of `P` at `m₀ : M`: encrypts `m₀` deterministically to `none`
(ignoring coins) and every `m ≠ m₀` to `some (P.encDet pk m r)`. Decryption maps `none` to
`some m₀` and `some c` to `P.dec sk c` filtered by `· ≠ m₀`. -/
@[expose] def unspreadPointPKE (P : ExplicitCoinPKE PK SK M R CT) (m₀ : M) :
    ExplicitCoinPKE PK SK M R (Option CT) where
  keyGen := P.keyGen
  sampleCoins := P.sampleCoins
  encDet pk m r := if m = m₀ then none else some (P.encDet pk m r)
  dec sk
    | none => some m₀
    | some c =>
      match P.dec sk c with
      | none => none
      | some m => if m = m₀ then none else some m

/-- `unspreadPointPKE P m₀` has per-message decryption failure probability at most that of `P`. -/
theorem unspreadPointPKE_msgFailProb_le (P : ExplicitCoinPKE PK SK M R CT) (m₀ : M)
    (pk : PK) (sk : SK) (m : M) :
    (unspreadPointPKE P m₀).msgFailProb pk sk m ≤ P.msgFailProb pk sk m := by
  by_cases hm : m = m₀
  · subst hm
    have h0 : (unspreadPointPKE P m).msgFailProb pk sk m = 0 := by
      simp [ExplicitCoinPKE.msgFailProb, unspreadPointPKE]
    rw [h0]
    exact P.msgFailProb_nonneg pk sk m
  · have hset : {r : R | (unspreadPointPKE P m₀).dec sk
        ((unspreadPointPKE P m₀).encDet pk m r) ≠ some m} =
        {r : R | P.dec sk (P.encDet pk m r) ≠ some m} := by
      ext r
      simp only [unspreadPointPKE, hm, ↓reduceIte, Set.mem_ofPred_eq]
      cases hdec : P.dec sk (P.encDet pk m r) with
      | none => simp
      | some m' =>
        by_cases hm' : m' = m₀
        · subst hm'; simp [Ne.symm hm]
        · simp [hm']
    rw [ExplicitCoinPKE.msgFailProb, ExplicitCoinPKE.msgFailProb, hset]
    rfl

/-- `unspreadPointPKE P m₀` is `δ`-correct whenever `P` is. -/
theorem unspreadPointPKE_deltaCorrect [Fintype M] [Nonempty M]
    (P : ExplicitCoinPKE PK SK M R CT) (m₀ : M) {δ : ℝ}
    (hδ : P.DeltaCorrect δ) : (unspreadPointPKE P m₀).DeltaCorrect δ := by
  unfold ExplicitCoinPKE.DeltaCorrect at hδ ⊢
  refine le_trans (ENNReal.toReal_mono ?_ ?_) hδ
  · refine ne_top_of_le_ne_top ENNReal.one_ne_top ?_
    rw [ProbComp.expect]
    calc ∑' x, ProbComp.eval P.keyGen x * ENNReal.ofReal (P.keyPairMaxFailProb x.1 x.2)
        ≤ ∑' x, ProbComp.eval P.keyGen x * 1 := by
          gcongr with x
          exact ENNReal.ofReal_le_one.mpr (P.keyPairMaxFailProb_le_one x.1 x.2)
      _ = 1 := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
  · simp only [ProbComp.expect, unspreadPointPKE]
    gcongr with x
    rw [ExplicitCoinPKE.keyPairMaxFailProb, Finset.sup'_le_iff]
    intro m _
    exact le_trans (unspreadPointPKE_msgFailProb_le P m₀ x.1 x.2 m)
      (P.msgFailProb_le_keyPairMaxFailProb x.1 x.2 m)

/-- On any pair of challenge messages `m₁ ≠ m₀` and `m₂ ≠ m₀`, `unspreadPointPKE P m₀` has the exact
same fixed-message IND-CPA advantages (`indCpaAdvantage`) as `P`. It is not two-stage IND-CPA
secure (`cpaAdvantage`), since a two-stage adversary may choose `m₀`. -/
theorem unspreadPointPKE_indCpaAdvantage (P : ExplicitCoinPKE PK SK M R CT) (m₀ m₁ m₂ : M)
    (hm₁ : m₁ ≠ m₀) (hm₂ : m₂ ≠ m₀) (A : PK → Option CT → ProbComp Bool) :
    (unspreadPointPKE P m₀).indCpaAdvantage m₁ m₂ A =
      P.indCpaAdvantage m₁ m₂ (fun pk c => A pk (some c)) := by
  simp [ExplicitCoinPKE.indCpaAdvantage, ExplicitCoinPKE.indCpaGame, ExplicitCoinPKE.encrypt,
    unspreadPointPKE, hm₁, hm₂]

/-- Every explicit-coin PKE (and in particular `unspreadPointPKE P m₀`) is trivially `0`-spread. -/
theorem unspreadPointPKE_gammaSpread_zero (P : ExplicitCoinPKE PK SK M R CT) (m₀ : M) :
    (unspreadPointPKE P m₀).GammaSpread 0 := by
  intro _ _ _ _ _
  rw [neg_zero, Real.rpow_zero]
  exact toOuterMeasure_toReal_le_one _ _

/-- Because `unspreadPointPKE P m₀` encrypts `m₀` deterministically to `none`, the coin-collision
probability at `(m₀, none)` is `1`. -/
theorem unspreadPointPKE_coinMass_m₀_none (P : ExplicitCoinPKE PK SK M R CT) (m₀ : M)
    (pk : PK) :
    ((ProbComp.eval (unspreadPointPKE P m₀).sampleCoins).toOuterMeasure
      {r : R | (unspreadPointPKE P m₀).encDet pk m₀ r = none}).toReal = 1 := by
  rw [_root_.PMF.toOuterMeasure_apply]
  simp [unspreadPointPKE, Set.indicator]

/-- `unspreadPointPKE P m₀` is not `γ`-spread for any `γ > 0`. -/
theorem unspreadPointPKE_not_gammaSpread_of_pos (P : ExplicitCoinPKE PK SK M R CT) (m₀ : M)
    {γ : ℝ} (hγ : 0 < γ) : ¬ (unspreadPointPKE P m₀).GammaSpread γ := by
  intro hspread
  obtain ⟨⟨pk, sk⟩, hkeys⟩ := (ProbComp.eval P.keyGen).support_nonempty
  have hle := hspread pk sk hkeys m₀ none
  rw [unspreadPointPKE_coinMass_m₀_none] at hle
  have hlt : (2 : ℝ) ^ (-γ) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (neg_lt_zero.mpr hγ)
  linarith

/-- `Scheme` wrapper around `unspreadPointPKE P m₀`. -/
@[expose] def unspreadScheme (P : ExplicitCoinPKE PK SK M R CT) (m₀ : M)
    (sampleMsg : ProbComp M) (sampleKey : ProbComp K) :
    Scheme PK SK M R (Option CT) K :=
  ⟨unspreadPointPKE P m₀, sampleMsg, sampleKey⟩

end UnspreadPKE

/-! ### The 1-Query Decapsulation Probe Adversary -/

/-- The 1-query decapsulation probe adversary: ignores the challenge, queries the decapsulation
oracle once on `none : Option CT`, and outputs `true` iff the oracle returns `some k`. -/
@[expose] def probeDecapsAdv : ROAdversary PK M R (Option CT) K :=
  fun _ => do
    let res ← OracleComp.query (spec := ROResp (M := M) (CT := Option CT) R K)
      (ROQuery.decaps none)
    return res.isSome

/-- `probeDecapsAdv` makes `0` queries to `G`, `0` queries to `H`, and `1` query to `decaps`. -/
theorem roFullQueryBounds_probeDecapsAdv :
    ROFullQueryBounds (probeDecapsAdv (PK := PK) (M := M) (R := R) (CT := CT) (K := K)) 0 0 1 := by
  refine ⟨fun _ => ⟨?_, ?_⟩, fun _ => ?_⟩ <;>
    exact OracleComp.IsCostBounded.liftBind _ _ 0 fun _ => OracleComp.IsCostBounded.pure _ 0

section Evaluation

variable [DecidableEq M] [DecidableEq CT]

/-- Running `simHashH` on the challenge tuple `(false, mStar, cStar)` from the singleton cache
`{ gCache := [(mStar, rStar)] }` leaves `gCache` equal to `[(mStar, rStar)]`. -/
private theorem gCache_eq_of_mem_support_simHashH_singleton (S : Scheme PK SK M R (Option CT) K)
    (pk : PK) (mStar : M) (rStar : R) (cStar : Option CT)
    (z : K × SimState M R (Option CT) K)
    (hz : z ∈ (ProbComp.eval ((S.simHashH pk (false, mStar, cStar)).run
      { gCache := [(mStar, rStar)] })).support) :
    z.2.gCache = [(mStar, rStar)] := by
  dsimp only [Scheme.simHashH] at hz
  change z ∈ (ProbComp.eval (simHashG S.pke.sampleCoins mStar { gCache := [(mStar, rStar)] } >>=
    fun a => (if S.pke.encDet pk mStar a.1 = cStar then simHashHq S.sampleKey cStar
      else simHashHRaw S.sampleKey (false, mStar, cStar)) a.2)).support at hz
  rw [ProbComp.eval_bind, PMF.mem_support_bind_iff] at hz
  obtain ⟨⟨r, st₁⟩, hr, hz⟩ := hz
  have hlookup : ([(mStar, rStar)] : List (M × R)).lookup mStar = some rStar := by simp
  rw [simHashG, RandomOracle.eval_zoomStateT_memoize, memoize_of_some _ _ _ _ hlookup,
    PMF.monad_pure_eq_pure, PMF.pure_map, PMF.mem_support_pure_iff] at hr
  cases hr
  by_cases henc : S.pke.encDet pk mStar rStar = cStar
  · simp only [henc, ↓reduceIte] at hz
    exact Scheme.simHashHq_gCache_eq S.sampleKey cStar _ z hz
  · simp only [henc, ↓reduceIte] at hz
    exact Scheme.simHashHRaw_gCache_eq S.sampleKey (false, mStar, cStar) _ z hz

/-- In the keyless simulator game `simBotGame`, `probeDecapsAdv` outputs `false` with probability
`1`: when `m* = m₀` the query `none` equals `c*` and is rejected; when `m* ≠ m₀` the only cached
message in `gCache` is `m*`, whose encryption under `unspreadPointPKE P m₀` is `some _ ≠ none`. -/
theorem eval_simBotGame_probeDecapsAdv (P : ExplicitCoinPKE PK SK M R CT) (m₀ : M)
    (sampleMsg : ProbComp M) (sampleKey : ProbComp K) (b : Bool) :
    ProbComp.eval ((unspreadScheme P m₀ sampleMsg sampleKey).simBotGame probeDecapsAdv b) =
      PMF.pure false := by
  let S := unspreadScheme P m₀ sampleMsg sampleKey
  change ProbComp.eval (S.simBotGame probeDecapsAdv b) = PMF.pure false
  dsimp only [Scheme.simBotGame, Scheme.simFilterGame, probeDecapsAdv]
  simp only [OracleComp.interpret_bind, OracleComp.interpret_query, OracleComp.interpret_pure,
    StateT.run_bind, StateT.run_pure, ProbComp.eval_bind, ProbComp.eval_pure]
  rw [← PMF.bind_const (ProbComp.eval S.pke.keyGen) (PMF.pure false)]
  congr 1 with ⟨pk, sk⟩ : 1
  rw [← PMF.bind_const (ProbComp.eval S.sampleMsg) (PMF.pure false)]
  congr 1 with mStar : 1
  rw [← PMF.bind_const (ProbComp.eval S.pke.sampleCoins) (PMF.pure false)]
  congr 1 with rStar : 1
  refine (bind_congr_on_support _ _ (fun _ => PMF.pure false) fun z hz => ?_).trans
    (PMF.bind_const _ _)
  have hg : z.2.gCache = [(mStar, rStar)] :=
    gCache_eq_of_mem_support_simHashH_singleton S pk mStar rStar
      (S.pke.encDet pk mStar rStar) z hz
  rw [← PMF.bind_const (ProbComp.eval S.sampleKey) (PMF.pure false)]
  congr 1 with kRand : 1
  dsimp only [Scheme.simFilterHandler, Scheme.simFilterDispatch, ROQuery.dispatch]
  by_cases hm : mStar = m₀
  · have hc : (none : Option CT) = S.pke.encDet pk mStar rStar := by
      simp [S, unspreadScheme, unspreadPointPKE, hm]
    simp [hc]
  · have hc : (none : Option CT) ≠ S.pke.encDet pk mStar rStar := by
      simp [S, unspreadScheme, unspreadPointPKE, hm]
    have hcheck : Scheme.simBotCheck S.pke pk z.2.gCache none = false := by
      simp [Scheme.simBotCheck, hg, S, unspreadScheme, unspreadPointPKE, hm]
    simp only [StateT.run, hc, ↓reduceIte, filterDecaps, hcheck, Bool.cond_false]
    change (((pure (none, z.2) : ProbComp (Option K × SimState M R (Option CT) K)).eval.bind
      fun a => PMF.pure (Option.isSome a.1, a.2)).bind fun a => PMF.pure a.1) = PMF.pure false
    simp

/-- In the real `FO^⊥` game `roIndCcaBotGame`, `probeDecapsAdv` outputs `decide (m* ≠ m₀)` for
each sampled challenge message `m* ← sampleMsg`. -/
theorem eval_roIndCcaBotGame_probeDecapsAdv (P : ExplicitCoinPKE PK SK M R CT) (m₀ : M)
    (sampleMsg : ProbComp M) (sampleKey : ProbComp K) (b : Bool) :
    ProbComp.eval ((unspreadScheme P m₀ sampleMsg sampleKey).roIndCcaBotGame probeDecapsAdv b) =
      (ProbComp.eval sampleMsg).map (fun mStar => decide (mStar ≠ m₀)) := by
  let S := unspreadScheme P m₀ sampleMsg sampleKey
  change ProbComp.eval (S.roIndCcaBotGame probeDecapsAdv b) =
    (ProbComp.eval S.sampleMsg).map (fun mStar => decide (mStar ≠ m₀))
  dsimp only [Scheme.roIndCcaBotGame, probeDecapsAdv]
  simp only [OracleComp.interpret_bind, OracleComp.interpret_query, OracleComp.interpret_pure,
    StateT.run_bind, StateT.run_pure, pmf_norm]
  rw [← PMF.bind_const (ProbComp.eval S.pke.keyGen)
    ((ProbComp.eval S.sampleMsg).map (fun mStar => decide (mStar ≠ m₀)))]
  congr 1 with ⟨pk, sk⟩ : 1
  dsimp only [PMF.map, Function.comp_def]
  congr 1 with mStar : 1
  rw [← PMF.bind_const (ProbComp.eval S.pke.sampleCoins) (PMF.pure (decide (mStar ≠ m₀)))]
  congr 1 with rStar : 1
  rw [← PMF.bind_const (ProbComp.eval S.sampleKey) (PMF.pure (decide (mStar ≠ m₀)))]
  congr 1 with kReal : 1
  rw [← PMF.bind_const (ProbComp.eval S.sampleKey) (PMF.pure (decide (mStar ≠ m₀)))]
  congr 1 with kRand : 1
  dsimp only [Scheme.roBotHandler, ROQuery.dispatch]
  by_cases hm : mStar = m₀
  · have hc : (none : Option CT) = S.pke.encDet pk mStar rStar := by
      simp [S, unspreadScheme, unspreadPointPKE, hm]
    simp [hc, hm]
  · have hc : (none : Option CT) ≠ S.pke.encDet pk mStar rStar := by
      simp [S, unspreadScheme, unspreadPointPKE, hm]
    have hdec : S.pke.dec sk none = some m₀ := rfl
    have henc (r' : R) : S.pke.encDet pk m₀ r' = none := by
      simp [S, unspreadScheme, unspreadPointPKE]
    simp [StateT.run_bind, hc, hdec, henc, hm, pmf_norm, Scheme.decapsBotM_eq]

/-- **Necessity of the `qD · 2^{-γ}` spreadness term in `FO^⊥`**: for a uniform message sampler on a
finite message space `M`, the 1-query adversary `probeDecapsAdv` (`qG = 0, qH = 0, qD = 1`)
distinguishes `eagerIndCcaBotGame` from `simBotGame` over `unspreadScheme P m₀` with advantage
`1 - 1 / |M|`. -/
theorem advantage_eagerIndCcaBotGame_simBotGame_probeDecapsAdv
    [Fintype M] [Nonempty M] [Finite R] [Fintype CT] [Finite K]
    (P : ExplicitCoinPKE PK SK M R CT) (m₀ : M)
    (sampleMsg : ProbComp M) (sampleKey : ProbComp K)
    (hmsg : ProbComp.eval sampleMsg = PMF.uniformOfFintype M) (b : Bool) :
    (Game.advantage
      ((unspreadScheme P m₀ sampleMsg sampleKey).eagerIndCcaBotGame probeDecapsAdv b)
      (ProbComp.eval ((unspreadScheme P m₀ sampleMsg sampleKey).simBotGame probeDecapsAdv b)) :
        ℝ) = 1 - 1 / Fintype.card M := by
  let S := unspreadScheme P m₀ sampleMsg sampleKey
  rw [← S.eval_roIndCcaBotGame_eq_eagerIndCcaBotGame probeDecapsAdv b,
    eval_roIndCcaBotGame_probeDecapsAdv, eval_simBotGame_probeDecapsAdv, hmsg,
    Game.advantage_pure_false]
  have hcoe : (Game.succProbability
      ((PMF.uniformOfFintype M).map (fun mStar => decide (mStar ≠ m₀))) : ℝ) =
      (((PMF.uniformOfFintype M).map (fun mStar => decide (mStar ≠ m₀))) true).toReal := rfl
  rw [hcoe]
  have hmap : (PMF.uniformOfFintype M).map (fun mStar => decide (mStar ≠ m₀)) true =
      (Finset.univ.filter (fun mStar : M => mStar ≠ m₀)).card / (Fintype.card M : ℝ≥0∞) := by
    rw [PMF.map_apply]
    simp only [PMF.uniformOfFintype_apply, true_eq_decide_iff, div_eq_mul_inv]
    rw [tsum_fintype, ← Finset.sum_filter]
    simp
  have hcard : (Finset.univ.filter (fun mStar : M => mStar ≠ m₀)).card = Fintype.card M - 1 := by
    rw [Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ m₀), Finset.card_univ]
  have hpos : 1 ≤ Fintype.card M := Fintype.card_pos
  rw [hmap, hcard, ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_natCast,
    Nat.cast_sub hpos, Nat.cast_one]
  have hne : (Fintype.card M : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [sub_div, div_self hne]

end Evaluation

end Cslib.Crypto.Protocols.FujisakiOkamoto
