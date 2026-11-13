/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Game.CloseTo
public import CslibFrontier.Crypto.Protocols.KEM.FujisakiOkamoto.NotBot.Hybrids
import CslibFrontier.Crypto.Game.CloseTo.UntilBad
import CslibFrontier.Crypto.Game.Hybrid
import CslibFrontier.Crypto.Protocols.KEM.FujisakiOkamoto.NotBot.Challenge
import CslibFrontier.Crypto.Protocols.KEM.FujisakiOkamoto.NotBot.Correctness
import CslibFrontier.Crypto.Protocols.KEM.FujisakiOkamoto.NotBot.Lazy
import CslibFrontier.Crypto.Protocols.KEM.FujisakiOkamoto.NotBot.Pushforward
import CslibFrontier.Languages.Probabilistic.Norm
import CslibFrontier.Languages.Probabilistic.RandomOracle.Represented
import CslibFrontier.Languages.Probabilistic.Simulation
import CslibFrontier.Languages.Probabilistic.Simulation.CloseTo
import CslibFrontier.Tactic.PMFSwap

/-!
# ROM IND-CCA security of `FO^⊥`

The explicit-rejection Fujisaki–Okamoto transform `FO^⊥ = U^⊥ ∘ T` of
[HofheinzHoevelmannsKiltz2017] (IACR ePrint 2017/604, full version dated 2 November 2021, §3.1
Fig. 5 and §3.2.1 Fig. 9) is IND-CCA secure in the random oracle model when the underlying
explicit-coin PKE is IND-CPA secure, `δ`-correct and `γ`-spread, and messages are uniform
(`Scheme.indCcaBotAdvantage_le`). For an adversary making at most `qG` queries to `G`, `qH` queries
to `H`, and `qD` queries to the punctured decapsulation oracle (`ROFullQueryBounds A qG qH qD`),

`Adv^{IND-CCA}_{FO^⊥}(A) ≤ 2 · Adv^{IND-CPA}(B) + 2 (qG + qH) / |M| + 2 (qG + qH + 1) δ
  + 2 (qG + qH + qD) 2^{-γ}`,

where `B = romBotCpaReduction A m₀ m₁` for some distinct messages `m₀ ≠ m₁`. Unlike the
implicit-rejection transform `FO-notbot` (module
`CslibFrontier.Crypto.Protocols.KEM.FujisakiOkamoto.NotBot`), `FO^⊥` has no secret fallback seed
and therefore no `2 qH / |M|` seed-guessing term; conversely, because `decapsBot` explicitly
outputs `none` when `decT` rejects (exposing the §3.1 ciphertext-validity oracle `CVO` of
`T[PKE, G]`), simulating decapsulation from cached `G`-queries alone incurs an additional
`2 qD 2^{-γ}` spreadness term.

The proof composes four game hops for each challenge bit `b : Bool`:

1. `eval_roIndCcaBotGame_eq_eagerIndCcaBotGame` and
   `eagerCoupledBotGame_eq_eagerIndCcaBotGame`: lazy/eager equivalence for `roIndCcaBotGame` and
   oracle re-indexing via `coupledH` (`bind_keyTable_coupledH`), so that valid decapsulations read
   the ciphertext key table `Hq c` while invalid ciphertexts return `none`. Both games are the
   `FO^⊥` instance of the shared ROM IND-CCA experiment (`romIndCcaExperiment_bot`,
   `eagerRomIndCcaExperiment_bot`), so the lazy/eager step is
   `Scheme.eval_romIndCcaExperiment_eq_eager`.
2. `closeTo_cachedCoupledBotGame_eagerCoupledBotGame`: lazy-sampling simulation with `CloseTo`
   error `qD · 2^{-γ}` (the §3.1 ciphertext-validity hop for `T[PKE, G]`), replacing `decT`'s check
   on `G(m')` by a lookup in the cached `G`-queries `gCache`. The hop applies the approximate
   simulation `OracleComp.closeTo_run_interpret_simulation_readOnly` to the joined cache
   `SimState.coupledCache` of `CslibFrontier.Crypto.Protocols.KEM.FujisakiOkamoto.NotBot.Lazy`,
   on which `G` and `H` are exact (`RandomOracle.eval_run_interpret_bind_complete`); only
   decapsulation needs spreadness.
3. `advantage_cachedCoupledBotGame_simBotGame_le`: dropping the secret-key decryption test from
   both `H` and `decaps` via `NotBot.Correctness.advantage_coupledFilterGame_simFilterGame_le` costs
   `(qG + qH + 1) δ`.
4. `advantage_simBotGame_le`: in the keyless `FO^⊥` simulator `simBotGame`, the programmed
   challenge entry `(m*, r*)` never matches a punctured decapsulation query `c ≠ c*`, so
   `NotBot.Challenge.advantage_simFilterGame_le` reduces distinguishing the real and random
   challenge keys to `romBotCpaReduction`.

Steps 1–3 are applied to both challenge bits, which accounts for the factor `2` on their terms.
In `roIndCcaBotGame` and `eagerIndCcaBotGame`, both real `H` replies and the independent ideal
challenge key are drawn from the arbitrary sampler `S.sampleKey : ProbComp K` (distinct from
`S.pke.keyGen`), and the proof holds for any `S.sampleKey`; taking `S.sampleKey` uniform on `K`
recovers the standard uniform-ideal-key experiment of [HofheinzHoevelmannsKiltz2017], §2.2,
Def. 2.4 / Fig. 4.

## Main definitions

* `Cslib.Crypto.Protocols.FujisakiOkamoto.Scheme.roBotHandler`,
  `Cslib.Crypto.Protocols.FujisakiOkamoto.Scheme.roIndCcaBotGame`,
  `Cslib.Crypto.Protocols.FujisakiOkamoto.Scheme.indCcaBotAdvantage`: executable lazy-cached ROM
  IND-CCA game and advantage for `FO^⊥`.
* `Cslib.Crypto.Protocols.FujisakiOkamoto.Scheme.eagerBotHandler`,
  `Cslib.Crypto.Protocols.FujisakiOkamoto.Scheme.eagerIndCcaBotGame`: eager random-oracle IND-CCA
  game for `FO^⊥`, defined directly from `Scheme.encapsBot` and `Scheme.decapsBot`.
* `Cslib.Crypto.Protocols.FujisakiOkamoto.Scheme.botDecaps`: the `FO^⊥` decapsulation program,
  whose instance of `Scheme.romIndCcaExperiment` is `roIndCcaBotGame`.
* `Cslib.Crypto.Protocols.FujisakiOkamoto.Scheme.simBotCheck`,
  `Cslib.Crypto.Protocols.FujisakiOkamoto.Scheme.simBotHandler`,
  `Cslib.Crypto.Protocols.FujisakiOkamoto.Scheme.simBotGame`,
  `Cslib.Crypto.Protocols.FujisakiOkamoto.Scheme.romBotCpaReduction`: keyless ROM simulator and
  IND-CPA reduction for `FO^⊥`.

## Main results

* `Cslib.Crypto.Protocols.FujisakiOkamoto.Scheme.romIndCcaExperiment_bot`,
  `Cslib.Crypto.Protocols.FujisakiOkamoto.Scheme.eagerRomIndCcaExperiment_bot`: the `FO^⊥`
  instance of the shared ROM IND-CCA experiment is `roIndCcaBotGame`, and its eager form is
  `eagerIndCcaBotGame`.
* `Cslib.Crypto.Protocols.FujisakiOkamoto.Scheme.eval_roIndCcaBotGame_eq_eagerIndCcaBotGame`,
  `Cslib.Crypto.Protocols.FujisakiOkamoto.Scheme.indCcaBotAdvantage_eq_eager`: exact eager/lazy
  equivalence for `FO^⊥`.
* `Cslib.Crypto.Protocols.FujisakiOkamoto.Scheme.advantage_eagerIndCcaBotGame_simBotGame_le`: the
  eager `FO^⊥` IND-CCA game and the keyless simulator game `simBotGame` differ by at most
  `(qG + qH + 1) δ + qD · 2^{-γ}`.
* `Cslib.Crypto.Protocols.FujisakiOkamoto.Scheme.indCcaBotAdvantage_le`: ROM IND-CCA security of
  `FO^⊥` from IND-CPA security, `δ`-correctness and `γ`-spreadness.

## References

* [D. Hofheinz, K. Hövelmanns, E. Kiltz, *A Modular Analysis of the Fujisaki–Okamoto
  Transformation*][HofheinzHoevelmannsKiltz2017] (IACR ePrint 2017/604, full version dated
  2 November 2021).
-/

@[expose] public section

namespace Cslib.Crypto.Protocols.FujisakiOkamoto

open Probability
open Probability.PMF
open scoped ENNReal NNReal

variable {PK SK M R CT K : Type}

namespace Scheme

variable [DecidableEq M] [DecidableEq CT]

/-! ### Section 1: Executable and Eager ROM IND-CCA Games for `FO^⊥ = U^⊥ ∘ T` -/

/-- Stateful oracle handler for the executable ROM IND-CCA game of `FO^⊥`
([HofheinzHoevelmannsKiltz2017], §3.2.1, Fig. 9). Queries to the challenge ciphertext `cStar` are
rejected with `none`; other decapsulation queries run the scheme's decapsulation `decapsBotM`
against the lazy random oracles `G` and `H`. -/
def roBotHandler (S : Scheme PK SK M R CT K) (pk : PK) (sk : SK) (cStar : CT)
    (q : ROQuery M CT) : StateT (ROCache M R CT K) ProbComp (ROResp R K q) :=
  ROQuery.dispatch (roHashG S.pke.sampleCoins) (roHashH S.sampleKey)
    (S.decapsBotM (roHashG S.pke.sampleCoins) (roHashH S.sampleKey) pk sk) cStar q

/-- The executable ROM IND-CCA security game for `FO^⊥ = U^⊥ ∘ T` with bit `b : Bool`. When
`b = false`, the adversary receives the real encapsulated key `kReal = H(false, m*, c*)`; when
`b = true`, it receives an independent key `kRand ← S.sampleKey`. -/
def roIndCcaBotGame (S : Scheme PK SK M R CT K)
    (A : ROAdversary PK M R CT K) (b : Bool) : ProbComp Bool := do
  let (pk, sk) ← S.pke.keyGen
  let mStar ← S.sampleMsg
  let rStar ← S.pke.sampleCoins
  let cStar := S.pke.encDet pk mStar rStar
  let kReal ← S.sampleKey
  let kRand ← S.sampleKey
  let kStar := if b then kRand else kReal
  let st₀ : ROCache M R CT K :=
    { gCache := [(mStar, rStar)], hCache := [((false, mStar, cStar), kReal)] }
  let (guess, _) ←
    (OracleComp.interpret (S.roBotHandler pk sk cStar) (A ⟨pk, cStar, kStar⟩)).run st₀
  return guess

/-- The ROM IND-CCA advantage of an adversary `A` against `FO^⊥`. -/
noncomputable def indCcaBotAdvantage (S : Scheme PK SK M R CT K)
    (A : ROAdversary PK M R CT K) : ℝ≥0 :=
  Game.advantage
    (ProbComp.eval (S.roIndCcaBotGame A false))
    (ProbComp.eval (S.roIndCcaBotGame A true))

/-- Stateless handler for `S.eagerIndCcaBotGame`: `G` and `H` are complete functions and
decapsulation queries for `c ≠ cStar` evaluate `S.decapsBot G H pk sk c`. -/
noncomputable def eagerBotHandler (S : Scheme PK SK M R CT K) (G : M → R)
    (H : Bool × M × CT → K) (pk : PK) (sk : SK) (cStar : CT) (q : ROQuery M CT) :
    PMF (ROResp R K q) :=
  ROQuery.dispatch (PMF.pure ∘ G) (PMF.pure ∘ H) (fun c => PMF.pure (S.decapsBot G H pk sk c))
    cStar q

/-- The eager random-oracle IND-CCA game for `FO^⊥`, defined directly from `S.pke.keyGen`,
`S.encapsBot`, and `S.decapsBot` over eager random oracles `G ← S.coinTable` and
`H ← S.keyTable (Bool × M × CT)`. -/
noncomputable def eagerIndCcaBotGame [Fintype M] [Finite R] [Fintype CT] [Finite K]
    (S : Scheme PK SK M R CT K) (A : ROAdversary PK M R CT K) (b : Bool) : Game := do
  let (pk, sk) ← ProbComp.eval S.pke.keyGen
  let G ← S.coinTable
  let H ← S.keyTable (Bool × M × CT)
  let (cStar, kReal) ← ProbComp.eval (S.encapsBot G H pk)
  let kRand ← ProbComp.eval S.sampleKey
  let kStar := if b then kRand else kReal
  OracleComp.interpret (S.eagerBotHandler G H pk sk cStar) (A ⟨pk, cStar, kStar⟩)

omit [DecidableEq M] in
/-- `FO^⊥` decapsulation `decapsBotM` as a program over the random oracles. -/
def botDecaps (S : Scheme PK SK M R CT K) (pk : PK) (sk : SK) (c : CT) :
    OracleComp (ROSpec M R CT K) (Option K) :=
  S.decapsBotM (fun m => OracleComp.query (spec := ROSpec M R CT K) (Sum.inl m))
    (fun x => OracleComp.query (spec := ROSpec M R CT K) (Sum.inr x)) pk sk c

/-- `roBotHandler` is the lazy handler of `romProgram` with `FO^⊥` decapsulation. -/
theorem roBotHandler_eq_romHandler (S : Scheme PK SK M R CT K) (pk : PK) (sk : SK) (cStar : CT) :
    S.roBotHandler pk sk cStar = S.romHandler (S.botDecaps pk sk) cStar := by
  funext q
  refine Eq.trans ?_ (dispatch_eq_interpret_romProgram _ _ cStar q)
  simp only [roBotHandler, botDecaps, interpret_decapsBotM, OracleComp.interpret_query]

omit [DecidableEq M] in
/-- `eagerBotHandler` is the eager handler of `romProgram` with `FO^⊥` decapsulation. -/
theorem eagerBotHandler_eq_romEagerHandler (S : Scheme PK SK M R CT K) (G : M → R)
    (H : Bool × M × CT → K) (pk : PK) (sk : SK) (cStar : CT) :
    S.eagerBotHandler G H pk sk cStar = romEagerHandler G H (S.botDecaps pk sk) cStar := by
  have hd (c : CT) : PMF.pure (S.decapsBot G H pk sk c) = OracleComp.interpret
      (OracleComp.sumHandler (fun m => PMF.pure (G m)) (fun x => PMF.pure (H x)))
      (S.botDecaps pk sk c) := by
    simp only [botDecaps, interpret_decapsBotM, OracleComp.interpret_query]
    change _ = S.decapsBotM (m := PMF) (pure ∘ G) (pure ∘ H) pk sk c
    rw [decapsBotM_pure]
    rfl
  funext q
  refine Eq.trans ?_ (dispatch_eq_interpret_romProgram _ _ cStar q)
  simp only [eagerBotHandler, hd]
  rfl

/-- `roIndCcaBotGame` is the ROM IND-CCA experiment of `FO^⊥`. -/
@[simp] theorem romIndCcaExperiment_bot (S : Scheme PK SK M R CT K)
    (A : ROAdversary PK M R CT K) (b : Bool) :
    S.romIndCcaExperiment S.pke.keyGen S.botDecaps A b = S.roIndCcaBotGame A b := by
  simp only [romIndCcaExperiment, roIndCcaBotGame, roBotHandler_eq_romHandler]

omit [DecidableEq M] in
/-- `eagerIndCcaBotGame` is the eager ROM IND-CCA experiment of `FO^⊥`. -/
@[simp] theorem eagerRomIndCcaExperiment_bot [Fintype M] [Finite R] [Fintype CT] [Finite K]
    (S : Scheme PK SK M R CT K) (A : ROAdversary PK M R CT K) (b : Bool) :
    S.eagerRomIndCcaExperiment S.pke.keyGen S.botDecaps A b = S.eagerIndCcaBotGame A b := by
  simp only [eagerRomIndCcaExperiment, eagerIndCcaBotGame, eagerBotHandler_eq_romEagerHandler]

/-- **Eager/lazy equivalence for the `FO^⊥` ROM IND-CCA game**: evaluating the executable
lazy-cached game `S.roIndCcaBotGame A b` yields the exact same output distribution as the eager
random-oracle game `S.eagerIndCcaBotGame A b`. -/
theorem eval_roIndCcaBotGame_eq_eagerIndCcaBotGame [Fintype M] [Finite R] [Fintype CT] [Finite K]
    (S : Scheme PK SK M R CT K) (A : ROAdversary PK M R CT K) (b : Bool) :
    ProbComp.eval (S.roIndCcaBotGame A b) = S.eagerIndCcaBotGame A b := by
  rw [← romIndCcaExperiment_bot, ← eagerRomIndCcaExperiment_bot]
  exact S.eval_romIndCcaExperiment_eq_eager _ _ A b

/-- The ROM IND-CCA advantage of `A` against `FO^⊥` equals the distinguishing advantage between
`S.eagerIndCcaBotGame A false` and `S.eagerIndCcaBotGame A true`. -/
theorem indCcaBotAdvantage_eq_eager [Fintype M] [Finite R] [Fintype CT] [Finite K]
    (S : Scheme PK SK M R CT K) (A : ROAdversary PK M R CT K) :
    S.indCcaBotAdvantage A =
      Game.advantage (S.eagerIndCcaBotGame A false) (S.eagerIndCcaBotGame A true) := by
  simp [indCcaBotAdvantage, eval_roIndCcaBotGame_eq_eagerIndCcaBotGame]

/-! ### Section 2: Oracle Re-indexing and Lazy + Spreadness CVO Hop -/

/-- Stateless oracle of `eagerCoupledBotGame`: `G` reads `G`, `H` reads `coupledH`, and
decapsulation queries `c ≠ cStar` return `some (Hq c)` when `decT` accepts `c` and `none` when
`decT` rejects `c`. -/
noncomputable def eagerCoupledBotHandler (S : Scheme PK SK M R CT K) (G : M → R)
    (Hq : CT → K) (Hraw : Bool × M × CT → K) (pk : PK) (sk : SK) (cStar : CT) (q : ROQuery M CT) :
    PMF (ROResp R K q) :=
  ROQuery.dispatch (PMF.pure ∘ G) (PMF.pure ∘ S.coupledH G Hq Hraw pk sk)
    (fun c =>
      PMF.pure
        (match decT S.pke G pk sk c with
        | some _ => some (Hq c)
        | none => none))
    cStar q

/-- The eager coupled game for `FO^⊥`: independent tables `G`, `Hq`, `Hraw`, challenge
`c* = Enc(pk, m*; G(m*))` with real key `coupledH (false, m*, c*)`, and decapsulation gated by
`decT`. -/
noncomputable def eagerCoupledBotGame [Fintype M] [Finite R] [Fintype CT] [Finite K]
    (S : Scheme PK SK M R CT K) (A : ROAdversary PK M R CT K) (b : Bool) : Game := do
  let (pk, sk) ← ProbComp.eval S.pke.keyGen
  let G ← S.coinTable
  let Hq ← S.keyTable CT
  let Hraw ← S.keyTable (Bool × M × CT)
  let mStar ← ProbComp.eval S.sampleMsg
  let cStar := encT S.pke G pk mStar
  let kRand ← ProbComp.eval S.sampleKey
  let kReal := S.coupledH G Hq Hraw pk sk (false, mStar, cStar)
  OracleComp.interpret (S.eagerCoupledBotHandler G Hq Hraw pk sk cStar)
    (A ⟨pk, cStar, if b then kRand else kReal⟩)

private theorem eagerBotHandler_coupledH (S : Scheme PK SK M R CT K) (G : M → R) (Hq : CT → K)
    (Hraw : Bool × M × CT → K) (pk : PK) (sk : SK) (cStar : CT) (q : ROQuery M CT) :
    S.eagerBotHandler G (S.coupledH G Hq Hraw pk sk) pk sk cStar q =
      S.eagerCoupledBotHandler G Hq Hraw pk sk cStar q := by
  cases q with
  | G m => rfl
  | H x => rfl
  | decaps c =>
    simp only [eagerBotHandler, eagerCoupledBotHandler, decapsBot_eq, ROQuery.dispatch]
    by_cases hc : c = cStar
    · simp [hc]
    · simp only [hc, ↓reduceIte]
      cases hd : decT S.pke G pk sk c with
      | none => rfl
      | some m' =>
        have henc := encT_of_decT_eq_some hd
        have hdec := dec_of_decT_eq_some hd
        simp only [encT] at henc
        simp [coupledH, henc, hdec]

/-- **Re-indexing the random oracle `H` of `FO^⊥`**: `eagerCoupledBotGame` and
`eagerIndCcaBotGame` have the exact same output distribution. -/
theorem eagerCoupledBotGame_eq_eagerIndCcaBotGame [Fintype M] [Finite R] [Fintype CT] [Finite K]
    (S : Scheme PK SK M R CT K) (A : ROAdversary PK M R CT K) (b : Bool) :
    S.eagerCoupledBotGame A b = S.eagerIndCcaBotGame A b := by
  simp only [eagerCoupledBotGame, eagerIndCcaBotGame, encapsBot,
    Probability.PMF.monad_bind_eq_bind, ProbComp.eval_bind, ProbComp.eval_pure, PMF.bind_bind,
    PMF.pure_bind]
  congr 1 with ⟨pk, sk⟩ : 1
  congr 1 with G : 1
  symm
  rw [S.bind_keyTable_coupledH G pk sk]
  congr 1 with Hq : 1
  congr 1 with Hraw : 1
  congr 1 with mStar : 1
  congr 1 with kRand : 1
  congr 1
  funext q
  exact S.eagerBotHandler_coupledH G Hq Hraw pk sk _ q

/-- Decapsulation filter of `cachedCoupledBotGame`: decrypts `c` under `sk` to `m'` and accepts
only when `m'` is already cached in `gCache` with a coin `r'` satisfying `Enc(pk, m'; r') = c`. -/
def cachedCoupledBotCheck (P : ExplicitCoinPKE PK SK M R CT) (pk : PK) (sk : SK)
    (gCache : List (M × R)) (c : CT) : Bool :=
  match P.dec sk c with
  | none => false
  | some m' =>
    match gCache.lookup m' with
    | none => false
    | some r' => decide (P.encDet pk m' r' = c)

/-- Lazy coupled game for `FO^⊥` where decapsulation only checks coins already cached in `gCache`
from `mStar`, `G`, or `H` queries. -/
def cachedCoupledBotGame (S : Scheme PK SK M R CT K) (A : ROAdversary PK M R CT K)
    (b : Bool) : ProbComp Bool :=
  S.coupledFilterGame (cachedCoupledBotCheck S.pke) A b

section CompleteBot

variable [Fintype M] [Finite R] [Fintype CT] [Finite K]

/-- One step of the lazy and `γ`-spreadness CVO hop: answering a query of `cachedCoupledBotGame`
and then completing the joined cache is within `q.dCost · 2^{-γ}` of completing the cache first
and answering from the tables as `eagerCoupledBotHandler` does. Only decapsulation of `c` with
`Dec(sk, c) = some m'` and `m'` uncached can differ, when the fresh coin `G m'` re-encrypts `m'`
to `c`. -/
private theorem closeTo_coupledCache_cachedCoupledBotHandler (S : Scheme PK SK M R CT K) {γ : ℝ}
    (hγ : S.pke.GammaSpread γ) {pk : PK} {sk : SK}
    (hpk : (pk, sk) ∈ (ProbComp.eval S.pke.keyGen).support) (cStar : CT)
    (q : ROQuery M CT) (st : SimState M R CT K) :
    CloseTo
      ((ProbComp.eval (S.coupledFilterHandler (cachedCoupledBotCheck S.pke pk sk) pk sk cStar q
        st)).bind fun x =>
          (RandomOracle.complete S.coupledDistribution x.2.coupledCache).map (x.1, ·))
      ((RandomOracle.complete S.coupledDistribution st.coupledCache).bind fun T =>
        (S.eagerCoupledBotHandler (fun m => T (.inl (.inl m))) (fun c => T (.inr c))
          (fun x => T (.inl (.inr x))) pk sk cStar q).map (·, T))
      (q.dCost * ENNReal.ofReal ((2 : ℝ) ^ (-γ))) := by
  rw [coupledFilterHandler_eq_interpret, RandomOracle.eval_run_interpret_bind_complete
    S.coupledDistribution S.coupledLazyOracle SimState.coupledCache
    S.eval_coupledLazyOracle_map_coupledCache]
  simp only [interpret_coupledProgram]
  cases q with
  | G m => exact (CloseTo.refl _).mono zero_le
  | H x => exact (CloseTo.refl _).mono zero_le
  | decaps c =>
    simp only [ROQuery.dCost, Nat.cast_one, one_mul]
    dsimp only [eagerCoupledBotHandler, ROQuery.dispatch]
    by_cases hc : c = cStar
    · simp only [hc, ↓reduceIte]
      exact (CloseTo.refl _).mono zero_le
    simp only [hc, ↓reduceIte, cachedCoupledBotCheck, decT_eq]
    cases hdec : S.pke.dec sk c with
    | none => exact (CloseTo.refl _).mono zero_le
    | some m' =>
      dsimp only
      cases hlook : st.gCache.lookup m' with
      | some r' =>
        -- A cached coin is the completed table's coin, so both sides agree.
        refine (Interactive.CloseTo.bind_of_eq_on _ _ _ ∅ fun T hT _ => ?_).mono (by simp)
        have hT' : T (.inl (.inl m')) = r' :=
          RandomOracle.complete_agrees _ _ T hT (.inl (.inl m')) r'
            (by simp [SimState.coupledCache, RandomOracle.ofList, hlook])
        by_cases henc : S.pke.encDet pk m' r' = c <;> simp [encT, hT', henc]
      | none =>
        -- An uncached coin is fresh, so the sides differ only when it re-encrypts `m'` to `c`.
        refine (Interactive.CloseTo.bind_of_eq_on
          (RandomOracle.complete S.coupledDistribution st.coupledCache) _ _
          {T | S.pke.encDet pk m' (T (.inl (.inl m'))) = c} fun T _ hT => ?_).mono ?_
        · have hT' : S.pke.encDet pk m' (T (.inl (.inl m'))) ≠ c := hT
          simp [encT, hT']
        · have hmap : (RandomOracle.complete S.coupledDistribution st.coupledCache).map
              (fun T => T (.inl (.inl m'))) = ProbComp.eval S.pke.sampleCoins := by
            rw [RandomOracle.complete, PMF.pi_map_eval]
            simp only [SimState.coupledCache, RandomOracle.Cache.sum_inl, RandomOracle.ofList,
              hlook, Option.elim_none]
          have hmeas : (RandomOracle.complete S.coupledDistribution st.coupledCache).toOuterMeasure
              {T | S.pke.encDet pk m' (T (.inl (.inl m'))) = c} =
              (ProbComp.eval S.pke.sampleCoins).toOuterMeasure {r | S.pke.encDet pk m' r = c} := by
            rw [← hmap, PMF.toOuterMeasure_map_apply]
            rfl
          rw [hmeas]
          exact (ENNReal.le_ofReal_iff_toReal_le (PMF.toOuterMeasure_ne_top _ _)
            (by positivity)).mpr (hγ pk sk hpk m' c)

/-- Running a decapsulation-bounded program under the handler of `cachedCoupledBotGame` is within
`d · 2^{-γ}` of completing the three caches into tables `G`, `Hraw` and `Hq` and running it under
`eagerCoupledBotHandler`. -/
private theorem closeTo_run_cachedCoupledBotHandler_eager (S : Scheme PK SK M R CT K) {γ : ℝ}
    (hγ : S.pke.GammaSpread γ) {pk : PK} {sk : SK}
    (hpk : (pk, sk) ∈ (ProbComp.eval S.pke.keyGen).support) (cStar : CT) {α : Type}
    (prog : OracleComp (ROResp (M := M) (CT := CT) R K) α) {d : ℕ}
    (hd : OracleComp.IsCostBounded ROQuery.dCost prog d) (st : SimState M R CT K) :
    CloseTo
      ((ProbComp.eval ((OracleComp.interpret
        (S.coupledFilterHandler (cachedCoupledBotCheck S.pke pk sk) pk sk cStar)
        prog).run st)).map Prod.fst)
      ((RandomOracle.complete (fun _ => ProbComp.eval S.pke.sampleCoins)
          (RandomOracle.ofList st.gCache)).bind fun G =>
        (RandomOracle.complete (fun _ => ProbComp.eval S.sampleKey)
            (RandomOracle.ofList st.hCache)).bind fun Hraw =>
          (RandomOracle.complete (fun _ => ProbComp.eval S.sampleKey)
              (RandomOracle.ofList st.hqCache)).bind fun Hq =>
            OracleComp.interpret (S.eagerCoupledBotHandler G Hq Hraw pk sk cStar) prog)
      (d * ENNReal.ofReal ((2 : ℝ) ^ (-γ))) := by
  have h := OracleComp.closeTo_run_interpret_simulation_readOnly ROQuery.dCost
    (fun q s => ProbComp.eval
      (S.coupledFilterHandler (cachedCoupledBotCheck S.pke pk sk) pk sk cStar q s))
    (fun (T : (q : (M ⊕ (Bool × M × CT)) ⊕ CT) → CoupledSpec M R CT K q) =>
      S.eagerCoupledBotHandler (fun m => T (.inl (.inl m))) (fun c => T (.inr c))
        (fun x => T (.inl (.inr x))) pk sk cStar)
    (fun st => RandomOracle.complete S.coupledDistribution st.coupledCache)
    (ENNReal.ofReal ((2 : ℝ) ^ (-γ)))
    (S.closeTo_coupledCache_cachedCoupledBotHandler hγ hpk cStar) prog hd st
  rw [OracleComp.map_run_interpret ProbComp.isMonadHom_eval, ← RandomOracle.bind_complete_sum,
    ← RandomOracle.bind_complete_sum]
  exact h

/-- **Lazy and `γ`-spreadness CVO hop for `FO^⊥`** ([HofheinzHoevelmannsKiltz2017], §3.1):
replacing `eagerCoupledBotGame` (where decapsulation evaluates `decT` on the full table `G`) by
`cachedCoupledBotGame` (where decapsulation only checks coins already cached in `gCache` from
`mStar`, `G`, or `H`) changes the output distribution by at most `qD · 2^{-γ}`. -/
theorem closeTo_cachedCoupledBotGame_eagerCoupledBotGame
    (S : Scheme PK SK M R CT K) (A : ROAdversary PK M R CT K) {qG qH qD : ℕ}
    (hq : ROFullQueryBounds A qG qH qD) {γ : ℝ} (hγ : S.pke.GammaSpread γ) (b : Bool) :
    CloseTo (ProbComp.eval (S.cachedCoupledBotGame A b)) (S.eagerCoupledBotGame A b)
      (qD * ENNReal.ofReal ((2 : ℝ) ^ (-γ))) := by
  set ε := (qD : ℝ≥0∞) * ENNReal.ofReal ((2 : ℝ) ^ (-γ))
  have hconst {α : Type} (μ : PMF α) : ∑' a, μ a * ε = ε := by
    rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
  have hL : ProbComp.eval (S.cachedCoupledBotGame A b) =
      (ProbComp.eval S.pke.keyGen).bind fun keys =>
      (ProbComp.eval S.sampleMsg).bind fun mStar =>
      (ProbComp.eval S.pke.sampleCoins).bind fun rStar =>
      (ProbComp.eval S.sampleKey).bind fun kRand =>
        let cStar := S.pke.encDet keys.1 mStar rStar
        (ProbComp.eval ((OracleComp.interpret
          (S.coupledFilterHandler (cachedCoupledBotCheck S.pke keys.1 keys.2) keys.1 keys.2 cStar)
          (OracleComp.query (spec := ROResp (M := M) (CT := CT) R K)
            (ROQuery.H (false, mStar, cStar)) >>= fun k =>
              A ⟨keys.1, cStar, if b then kRand else k⟩)).run
          { gCache := [(mStar, rStar)] })).map Prod.fst := by
    dsimp only [cachedCoupledBotGame, coupledFilterGame]
    simp only [pmf_norm]
    congr 1 with ⟨pk, sk⟩ : 1
    congr 1 with mStar : 1
    congr 1 with rStar : 1
    set cStar := S.pke.encDet pk mStar rStar
    have hP (kRand : K) :
        (ProbComp.eval ((OracleComp.interpret
          (S.coupledFilterHandler (cachedCoupledBotCheck S.pke pk sk) pk sk cStar)
          (OracleComp.query (spec := ROResp (M := M) (CT := CT) R K)
            (ROQuery.H (false, mStar, cStar)) >>= fun k =>
              A ⟨pk, cStar, if b then kRand else k⟩)).run
          { gCache := [(mStar, rStar)] })).map Prod.fst =
        (ProbComp.eval ((S.coupledHashH pk sk (false, mStar, cStar)).run
          { gCache := [(mStar, rStar)] })).bind (fun z =>
          (ProbComp.eval ((OracleComp.interpret
            (S.coupledFilterHandler (cachedCoupledBotCheck S.pke pk sk) pk sk cStar)
            (A ⟨pk, cStar, if b then kRand else z.1⟩)).run z.2)).bind fun a => PMF.pure a.1) := by
      rw [OracleComp.run_interpret_bind, OracleComp.run_interpret_query]
      simp only [pmf_norm]
      rfl
    rw [PMF.bind_comm]
    simp only [← hP]
  have hR : S.eagerCoupledBotGame A b =
      (ProbComp.eval S.pke.keyGen).bind fun keys =>
      (ProbComp.eval S.sampleMsg).bind fun mStar =>
      (ProbComp.eval S.pke.sampleCoins).bind fun rStar =>
      (ProbComp.eval S.sampleKey).bind fun kRand =>
        let cStar := S.pke.encDet keys.1 mStar rStar
        (RandomOracle.complete (fun _ => ProbComp.eval S.pke.sampleCoins)
            (RandomOracle.ofList [(mStar, rStar)])).bind fun G =>
          (RandomOracle.complete (fun _ => ProbComp.eval S.sampleKey)
              (RandomOracle.ofList ([] : List ((Bool × M × CT) × K)))).bind fun Hraw =>
            (RandomOracle.complete (fun _ => ProbComp.eval S.sampleKey)
                (RandomOracle.ofList ([] : List (CT × K)))).bind fun Hq =>
              OracleComp.interpret (S.eagerCoupledBotHandler G Hq Hraw keys.1 keys.2 cStar)
                (OracleComp.query (spec := ROResp (M := M) (CT := CT) R K)
                  (ROQuery.H (false, mStar, cStar)) >>= fun k =>
                    A ⟨keys.1, cStar, if b then kRand else k⟩) := by
    dsimp only [eagerCoupledBotGame]
    simp only [RandomOracle.complete_ofList_singleton,
      RandomOracle.ofList_nil, RandomOracle.complete_empty, OracleComp.interpret_bind,
      OracleComp.interpret_query, eagerCoupledBotHandler, pmf_norm, encT, ROQuery.dispatch]
    congr 1 with ⟨pk, sk⟩ : 1
    dsimp only
    pmf_hoist (ProbComp.eval S.sampleMsg)
    congr 1 with mStar : 1
    refine Eq.symm (Eq.trans ?_
      (bind_pi_update (fun _ : M => ProbComp.eval S.pke.sampleCoins) mStar
        (fun rStar G =>
          (S.keyTable CT).bind fun Hq =>
          (S.keyTable (Bool × M × CT)).bind
            fun Hraw =>
          (ProbComp.eval S.sampleKey).bind fun kRand =>
            OracleComp.interpret
              (S.eagerCoupledBotHandler G Hq Hraw pk sk (S.pke.encDet pk mStar rStar))
              (A ⟨pk, S.pke.encDet pk mStar rStar, if b then kRand else
                S.coupledH G Hq Hraw pk sk (false, mStar, S.pke.encDet pk mStar rStar)⟩))))
    congr 1 with rStar : 1
    unfold keyTable
    pmf_swap
  rw [hL, hR]
  refine (CloseTo.bind_right_tsum _ (err := fun _ => ε) fun keys hkeys => ?_).mono
    (le_of_eq (hconst _))
  refine (CloseTo.bind_right_tsum _ (err := fun _ => ε) fun mStar _ => ?_).mono
    (le_of_eq (hconst _))
  refine (CloseTo.bind_right_tsum _ (err := fun _ => ε) fun rStar _ => ?_).mono
    (le_of_eq (hconst _))
  refine (CloseTo.bind_right_tsum _ (err := fun _ => ε) fun kRand _ => ?_).mono
    (le_of_eq (hconst _))
  set cStar := S.pke.encDet keys.1 mStar rStar
  have hd : OracleComp.IsCostBounded ROQuery.dCost
      (OracleComp.query (spec := ROResp (M := M) (CT := CT) R K)
        (ROQuery.H (false, mStar, cStar)) >>= fun k =>
          A ⟨keys.1, cStar, if b then kRand else k⟩) qD :=
    OracleComp.IsCostBounded.liftBind (ROQuery.H (false, mStar, cStar)) _ qD fun k =>
      hq.2 ⟨keys.1, cStar, if b then kRand else k⟩
  exact S.closeTo_run_cachedCoupledBotHandler_eager hγ hkeys cStar _ hd _

end CompleteBot

/-! ### Section 3: Keyless Simulator, Correctness Hop, Challenge Hop, and Main Theorem -/

/-- Decapsulation filter of the keyless `FO^⊥` simulator `simBotHandler`: accepts `c` when some
message `p.1` in `gCache` has active cached coin `gCache.lookup p.1 = some r` satisfying
`Enc(pk, p.1; r) = c`. -/
def simBotCheck (P : ExplicitCoinPKE PK SK M R CT) (pk : PK)
    (gCache : List (M × R)) (c : CT) : Bool :=
  gCache.any fun p =>
    match gCache.lookup p.1 with
    | none => false
    | some r => decide (P.encDet pk p.1 r = c)

/-- Stateful oracle handler for the keyless ROM simulator of the `FO^⊥` IND-CCA game: answers
`G` and `H` as in `simHandler`, and answers punctured decapsulation queries `c ≠ cStar` with
`some (H_q(c))` when `simBotCheck S.pke pk st.gCache c = true` and `none` otherwise. -/
def simBotHandler (S : Scheme PK SK M R CT K) (pk : PK) (cStar : CT) (q : ROQuery M CT) :
    StateT (SimState M R CT K) ProbComp (ROResp R K q) :=
  S.simFilterHandler (simBotCheck S.pke pk) pk cStar q

/-- The lazy keyless simulator game for `FO^⊥` with challenge coin `G(m*)` programmed. -/
def simBotGame (S : Scheme PK SK M R CT K) (A : ROAdversary PK M R CT K) (b : Bool) :
    ProbComp Bool :=
  S.simFilterGame (simBotCheck S.pke) A b

/-- IND-CPA adversary built from a ROM IND-CCA adversary `A` against `FO^⊥`: runs
`A ⟨pk, cStar, kStar⟩` against `S.simBotHandler pk cStar` from empty caches and outputs whether `m1`
was queried to `G`. -/
def romBotCpaReduction (S : Scheme PK SK M R CT K)
    (A : ROAdversary PK M R CT K) (m0 m1 : M) : PK → CT → ProbComp Bool :=
  S.romFilterCpaReduction (simBotCheck S.pke) A m0 m1

private theorem simBotCheck_eq_true_iff (P : ExplicitCoinPKE PK SK M R CT) (pk : PK)
    (L : List (M × R)) (c : CT) :
    simBotCheck P pk L c = true ↔
      ∃ m r, L.lookup m = some r ∧ P.encDet pk m r = c := by
  simp only [simBotCheck, List.any_eq_true, Prod.exists]
  constructor
  · rintro ⟨m, _, -, h⟩
    cases hlook : L.lookup m with
    | none => simp [hlook] at h
    | some r => exact ⟨m, r, hlook, by simpa [hlook] using h⟩
  · rintro ⟨m, r, hlook, henc⟩
    obtain ⟨l₁, l₂, hlist, -⟩ := List.lookup_eq_some_iff.mp hlook
    exact ⟨m, r, by simp [hlist], by simp [hlook, henc]⟩

/-- On any state satisfying `GoodCache`, the secret-key decapsulation check
`cachedCoupledBotCheck` agrees with the keyless check `simBotCheck`. -/
private theorem cachedCoupledBotCheck_eq_simBotCheck_of_goodCache (S : Scheme PK SK M R CT K)
    (pk : PK) (sk : SK) (st : SimState M R CT K) (c : CT)
    (hgood : GoodCache S.pke pk sk st) :
    cachedCoupledBotCheck S.pke pk sk st.gCache c = simBotCheck S.pke pk st.gCache c := by
  apply Bool.eq_iff_iff.mpr
  rw [simBotCheck_eq_true_iff]
  simp only [cachedCoupledBotCheck]
  constructor
  · intro h
    cases hdec : S.pke.dec sk c with
    | none => simp [hdec] at h
    | some m' =>
      simp only [hdec] at h
      cases hlook : st.gCache.lookup m' with
      | none => simp [hlook] at h
      | some r' => exact ⟨m', r', hlook, by simpa [hlook] using h⟩
  · rintro ⟨m', r', hlook, henc⟩
    obtain ⟨l₁, l₂, hlist, -⟩ := List.lookup_eq_some_iff.mp hlook
    have hdec : S.pke.dec sk c = some m' := henc ▸ hgood (m', r') (by simp [hlist])
    simp [hdec, hlook, henc]

/-- **Correctness hop for `FO^⊥`**: for an adversary making at most `qG` queries to `G` and `qH`
queries to `H` against a `δ`-correct PKE, `cachedCoupledBotGame` and `simBotGame` have
distinguishing advantage at most `(qG + qH + 1) δ`. -/
theorem advantage_cachedCoupledBotGame_simBotGame_le [Fintype M] [Nonempty M]
    (S : Scheme PK SK M R CT K) (A : ROAdversary PK M R CT K) {qG qH : ℕ}
    (hq : ROQueryBounds A qG qH) {δ : ℝ} (hδ : S.pke.DeltaCorrect δ) (b : Bool) :
    (Game.advantage (ProbComp.eval (S.cachedCoupledBotGame A b))
        (ProbComp.eval (S.simBotGame A b)) : ℝ) ≤
      ((qG + qH + 1 : ℕ) : ℝ) * δ :=
  S.advantage_coupledFilterGame_simFilterGame_le (cachedCoupledBotCheck S.pke) (simBotCheck S.pke)
    S.cachedCoupledBotCheck_eq_simBotCheck_of_goodCache A hq hδ b

/-- At any punctured ciphertext `c ≠ Enc(pk, mStar; rStar)`, programming `(mStar, rStar)` via `ens`
leaves `simBotCheck` unchanged whenever `LookupNoneOr mStar rStar L` holds. -/
private theorem simBotCheck_ens (S : Scheme PK SK M R CT K) (pk : PK) (mStar : M) (rStar : R)
    (L : List (M × R)) (c : CT) (hc : c ≠ S.pke.encDet pk mStar rStar)
    (hL : LookupNoneOr mStar rStar L) :
    simBotCheck S.pke pk (ens mStar rStar L) c = simBotCheck S.pke pk L c := by
  apply Bool.eq_iff_iff.mpr
  simp only [simBotCheck_eq_true_iff, lookup_ens]
  constructor
  · rintro ⟨m, r, hlook, henc⟩
    by_cases hm : m = mStar
    · subst hm
      simp only [↓reduceIte, Option.some.injEq] at hlook
      exact absurd (hlook ▸ henc).symm hc
    · simp only [hm, ↓reduceIte] at hlook
      exact ⟨m, r, hlook, henc⟩
  · rintro ⟨m, r, hlook, henc⟩
    have hm : m ≠ mStar := by
      rintro rfl
      rcases hL with hnone | hsome
      · rw [hnone] at hlook; cases hlook
      · rw [hsome] at hlook; cases hlook; exact hc henc.symm
    exact ⟨m, r, by simp [hm, hlook], henc⟩

/-- **Challenge hop for `FO^⊥`**: if the message sampler is uniform on a message space with at
least two elements and the PKE is `γ`-spread, then for every adversary making at most `qG` queries
to `G` and `qH` queries to `H`, some distinct messages `m₀ ≠ m₁` bound the advantage between
`simBotGame A false` and `simBotGame A true` by
`2 Adv_CPA(romBotCpaReduction A m₀ m₁) + 2 (qG + qH)/|M| + 2 (qG + qH) 2^(-γ)`. -/
theorem advantage_simBotGame_le [Fintype M] [Nonempty M]
    (S : Scheme PK SK M R CT K) (A : ROAdversary PK M R CT K) {qG qH : ℕ}
    (hq : ROQueryBounds A qG qH) (hM : 2 ≤ Fintype.card M)
    (hmsg : ProbComp.eval S.sampleMsg = PMF.uniformOfFintype M) {γ : ℝ}
    (hγ : S.pke.GammaSpread γ) :
    ∃ m₀ m₁ : M, m₀ ≠ m₁ ∧
      (Game.advantage (ProbComp.eval (S.simBotGame A false))
          (ProbComp.eval (S.simBotGame A true)) : ℝ) ≤
        2 * (S.pke.indCpaAdvantage m₀ m₁ (S.romBotCpaReduction A m₀ m₁) : ℝ) +
          2 * (((qG : ℝ) + qH) / Fintype.card M) +
            2 * (((qG : ℝ) + qH) * (2 : ℝ) ^ (-γ)) :=
  S.advantage_simFilterGame_le (simBotCheck S.pke) S.simBotCheck_ens A hq hM hmsg hγ

/-- **Hybrid chain for one challenge bit of `FO^⊥`**: for a `δ`-correct and `γ`-spread PKE and an
adversary satisfying `ROFullQueryBounds A qG qH qD`, the eager IND-CCA game of `FO^⊥` and the
keyless simulator game `simBotGame` differ by at most `(qG + qH + 1) δ + qD · 2^{-γ}`. -/
theorem advantage_eagerIndCcaBotGame_simBotGame_le [Fintype M] [Nonempty M] [Finite R]
    [Fintype CT] [Finite K] (S : Scheme PK SK M R CT K) (A : ROAdversary PK M R CT K)
    {qG qH qD : ℕ} (hq : ROFullQueryBounds A qG qH qD) {δ γ : ℝ}
    (hδ : S.pke.DeltaCorrect δ) (hγ : S.pke.GammaSpread γ) (b : Bool) :
    (Game.advantage (S.eagerIndCcaBotGame A b) (ProbComp.eval (S.simBotGame A b)) : ℝ) ≤
      ((qG + qH + 1 : ℕ) : ℝ) * δ + qD * (2 : ℝ) ^ (-γ) := by
  have hclose := (S.closeTo_cachedCoupledBotGame_eagerCoupledBotGame A hq hγ b).symm
  rw [eagerCoupledBotGame_eq_eagerIndCcaBotGame] at hclose
  have hadv₁ : (Game.advantage (S.eagerIndCcaBotGame A b)
      (ProbComp.eval (S.cachedCoupledBotGame A b)) : ℝ≥0∞) ≤
      (qD : ℝ≥0∞) * ENNReal.ofReal ((2 : ℝ) ^ (-γ)) :=
    Game.closeTo_iff_coe_advantage_le.mp hclose
  have htop : ((qD : ℝ≥0∞) * ENNReal.ofReal ((2 : ℝ) ^ (-γ))) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) ENNReal.ofReal_ne_top
  have h₁ : (Game.advantage (S.eagerIndCcaBotGame A b)
      (ProbComp.eval (S.cachedCoupledBotGame A b)) : ℝ) ≤ qD * (2 : ℝ) ^ (-γ) := by
    have hr := ENNReal.toReal_mono htop hadv₁
    rwa [ENNReal.coe_toReal, ENNReal.toReal_mul, ENNReal.toReal_natCast,
      ENNReal.toReal_ofReal (Real.rpow_nonneg (by norm_num) _)] at hr
  have h₂ := S.advantage_cachedCoupledBotGame_simBotGame_le A hq.1 hδ b
  calc (Game.advantage (S.eagerIndCcaBotGame A b) (ProbComp.eval (S.simBotGame A b)) : ℝ)
      ≤ Game.advantage (S.eagerIndCcaBotGame A b) (ProbComp.eval (S.cachedCoupledBotGame A b)) +
          Game.advantage (ProbComp.eval (S.cachedCoupledBotGame A b))
            (ProbComp.eval (S.simBotGame A b)) := by
        exact_mod_cast Game.advantage_triangle _ _ _
    _ ≤ qD * (2 : ℝ) ^ (-γ) + ((qG + qH + 1 : ℕ) : ℝ) * δ := add_le_add h₁ h₂
    _ = ((qG + qH + 1 : ℕ) : ℝ) * δ + qD * (2 : ℝ) ^ (-γ) := add_comm _ _

/-- **ROM IND-CCA security of `FO^⊥ = U^⊥ ∘ T`** ([HofheinzHoevelmannsKiltz2017], §3.1 and §3.2.1,
composed directly): for uniform messages, a `δ`-correct and `γ`-spread PKE, and an adversary making
at most `qG` queries to `G`, `qH` queries to `H`, and `qD` queries to `decaps`, there are distinct
messages `m₀ ≠ m₁` with
`Adv^{IND-CCA}_{FO^⊥}(A) ≤ 2 · Adv^{IND-CPA}_{m₀, m₁}(romBotCpaReduction A m₀ m₁)
  + 2 (qG + qH) / |M| + 2 (qG + qH + 1) δ + 2 (qG + qH + qD) 2^{-γ}`.
Both real `H` replies and the independent ideal challenge key in `roIndCcaBotGame` and
`eagerIndCcaBotGame` are drawn from the arbitrary key sampler `S.sampleKey : ProbComp K`; taking
`S.sampleKey` uniform on `K` recovers the standard uniform-ideal-key experiment of
[HofheinzHoevelmannsKiltz2017], §2.2, Def. 2.4 / Fig. 4. -/
theorem indCcaBotAdvantage_le [Fintype M] [Nonempty M] [Finite R] [Finite CT] [Finite K]
    (S : Scheme PK SK M R CT K) (A : ROAdversary PK M R CT K) {qG qH qD : ℕ}
    (hq : ROFullQueryBounds A qG qH qD) (hM : 2 ≤ Fintype.card M)
    (hmsg : ProbComp.eval S.sampleMsg = PMF.uniformOfFintype M)
    {δ γ : ℝ} (hδ : S.pke.DeltaCorrect δ) (hγ : S.pke.GammaSpread γ) :
    ∃ m₀ m₁ : M, m₀ ≠ m₁ ∧
      (S.indCcaBotAdvantage A : ℝ) ≤
        2 * (S.pke.indCpaAdvantage m₀ m₁ (S.romBotCpaReduction A m₀ m₁) : ℝ) +
          2 * (qG + qH) / Fintype.card M + 2 * ((qG + qH + 1 : ℕ) : ℝ) * δ +
          2 * ((qG + qH + qD) * (2 : ℝ) ^ (-γ)) := by
  have : Fintype CT := Fintype.ofFinite CT
  obtain ⟨m₀, m₁, hne, hsim⟩ := S.advantage_simBotGame_le A hq.1 hM hmsg hγ
  refine ⟨m₀, m₁, hne, ?_⟩
  have hF := S.advantage_eagerIndCcaBotGame_simBotGame_le A hq hδ hγ false
  have hT := S.advantage_eagerIndCcaBotGame_simBotGame_le A hq hδ hγ true
  rw [indCcaBotAdvantage_eq_eager]
  have hcard : (0 : ℝ) < Fintype.card M := by exact_mod_cast Fintype.card_pos
  calc _ ≤ _ :=
        Game.advantage_four_le (S.eagerIndCcaBotGame A) (fun b => ProbComp.eval (S.simBotGame A b))
          hF hsim hT
    _ = _ := by field_simp; ring

end Scheme

end Cslib.Crypto.Protocols.FujisakiOkamoto
