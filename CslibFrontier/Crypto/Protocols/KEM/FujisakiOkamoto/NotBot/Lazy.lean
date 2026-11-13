/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.KEM.FujisakiOkamoto.NotBot.Hybrids
import CslibFrontier.Languages.Probabilistic.Norm
import CslibFrontier.Languages.Probabilistic.RandomOracle.Probabilistic
import CslibFrontier.Languages.Probabilistic.RandomOracle.Represented
import CslibFrontier.Tactic.PMFSwap

/-!
# Lazy/eager equivalence of the coupled `FO-notbot` game

The lazy coupled game `Scheme.coupledGame` of
`CslibFrontier.Crypto.Protocols.KEM.FujisakiOkamoto.NotBot.Hybrids` answers `G`, the ciphertext
table `Hq` and the raw table `Hraw` lazily on the three caches of `SimState`. This module proves
that it has the same output distribution as the eager coupled game `Scheme.eagerCoupledGame`, a
step in the IND-CCA proof for `FO-notbot` of [HofheinzHoevelmannsKiltz2017] (IACR ePrint 2017/604,
full version dated 2 November 2021, §3.1 and §3.2.2).

The three lazy tables are one lazy random oracle on the joined interface `CoupledSpec`, and every
query of the coupled game is the oracle program `coupledProgram` over it. So
`RandomOracle.eval_run_interpret_eq_complete_bind` replaces the three caches by complete tables in
one step, and `RandomOracle.bind_complete_sum` splits the completed table into `G`, `Hraw` and
`Hq`.

## Main results

* `Cslib.Crypto.Protocols.FujisakiOkamoto.Scheme.eval_coupledGame_eq_eagerCoupledGame`: the lazy
  coupled game and the eager coupled game have the same output distribution.

## References

* [D. Hofheinz, K. Hövelmanns, E. Kiltz, *A Modular Analysis of the Fujisaki–Okamoto
  Transformation*][HofheinzHoevelmannsKiltz2017] (IACR ePrint 2017/604, full version dated
  2 November 2021).
-/

public section

namespace Cslib.Crypto.Protocols.FujisakiOkamoto

open Probability
open Probability.PMF
open scoped Cslib

variable {PK SK M R CT K : Type}

namespace Scheme

variable [DecidableEq M] [DecidableEq CT]

/-- The random oracles `G : M → R`, `Hraw : Bool × M × CT → K` and `Hq : CT → K` of the coupled
game as one interface. -/
private abbrev CoupledSpec (M R CT K : Type) :=
  ((fun _ : M => R) ⊕ₒ (fun _ : Bool × M × CT => K)) ⊕ₒ (fun _ : CT => K)

/-- Each query of the coupled game as a program over its random oracles: `G` is forwarded, `H`
runs the coupled key derivation `coupledH`, and decapsulation reads `Hq`. -/
private def coupledProgram (S : Scheme PK SK M R CT K) (pk : PK) (sk : SK) (cStar : CT) :
    (q : ROQuery M CT) → OracleComp (CoupledSpec M R CT K) (ROResp R K q) :=
  ROQuery.dispatch (fun m => OracleComp.query (spec := CoupledSpec M R CT K) (.inl (.inl m)))
    (fun
      | (false, m, c) => do
        let r : R ← OracleComp.query (spec := CoupledSpec M R CT K) (.inl (.inl m))
        if S.pke.encDet pk m r = c ∧ S.pke.dec sk c = some m then
          OracleComp.query (spec := CoupledSpec M R CT K) (.inr c)
        else
          OracleComp.query (spec := CoupledSpec M R CT K) (.inl (.inr (false, m, c)))
      | (true, m, c) => OracleComp.query (spec := CoupledSpec M R CT K) (.inl (.inr (true, m, c))))
    (fun c => do
      let k ← OracleComp.query (spec := CoupledSpec M R CT K) (.inr c)
      return some k)
    cStar

/-- The lazy oracles of the coupled game on the caches of `SimState`. -/
private abbrev lazyOracle (S : Scheme PK SK M R CT K) :
    (q : (M ⊕ (Bool × M × CT)) ⊕ CT) →
      StateT (SimState M R CT K) ProbComp (CoupledSpec M R CT K q) :=
  OracleComp.sumHandler
    (OracleComp.sumHandler (simHashG S.pke.sampleCoins) (simHashHRaw S.sampleKey))
    (simHashHq S.sampleKey)

/-- The sampling distributions of the coupled game's random oracles. -/
private noncomputable abbrev coupledDistribution (S : Scheme PK SK M R CT K) :
    (q : (M ⊕ (Bool × M × CT)) ⊕ CT) → PMF (CoupledSpec M R CT K q) :=
  OracleComp.sumHandler
    (OracleComp.sumHandler (fun _ => ProbComp.eval S.pke.sampleCoins)
      (fun _ => ProbComp.eval S.sampleKey))
    (fun _ => ProbComp.eval S.sampleKey)

/-- The coupled game's oracles answered from complete tables `G`, `Hraw` and `Hq`. -/
private noncomputable abbrev tableOracle (G : M → R) (Hraw : Bool × M × CT → K) (Hq : CT → K) :
    (q : (M ⊕ (Bool × M × CT)) ⊕ CT) → PMF (CoupledSpec M R CT K q) :=
  OracleComp.sumHandler
    (OracleComp.sumHandler (fun m => PMF.pure (G m)) (fun x => PMF.pure (Hraw x)))
    (fun c => PMF.pure (Hq c))

/-- The joined cache represented by the three list caches of a `SimState`. -/
private abbrev coupledCache (st : SimState M R CT K) : RandomOracle.Cache (CoupledSpec M R CT K) :=
  RandomOracle.Cache.sum
    (RandomOracle.Cache.sum (RandomOracle.ofList st.gCache) (RandomOracle.ofList st.hCache))
    (RandomOracle.ofList st.hqCache)

/-- Each lazy oracle call, read on the joined cache, is a lazy call of the joined oracle. -/
private theorem eval_lazyOracle_map_coupledCache (S : Scheme PK SK M R CT K)
    (q : (M ⊕ (Bool × M × CT)) ⊕ CT) (st : SimState M R CT K) :
    (ProbComp.eval (S.lazyOracle q st)).map (fun z => (z.1, coupledCache z.2)) =
      RandomOracle.answer S.coupledDistribution q (coupledCache st) := by
  rcases q with (m | x) | c
  · rw [coupledCache, RandomOracle.answer_sum_inl, RandomOracle.answer_sum_inl, PMF.map_comp]
    exact RandomOracle.eval_zoom_memoize_map (fun st : SimState M R CT K => st.gCache)
      (fun st g => { st with gCache := g }) S.pke.sampleCoins m st (fun r => r) coupledCache
      (fun g => RandomOracle.Cache.sum
        (RandomOracle.Cache.sum g (RandomOracle.ofList st.hCache))
        (RandomOracle.ofList st.hqCache)) (fun _ => rfl)
  · rw [coupledCache, RandomOracle.answer_sum_inl, RandomOracle.answer_sum_inr, PMF.map_comp]
    exact RandomOracle.eval_zoom_memoize_map (fun st : SimState M R CT K => st.hCache)
      (fun st h => { st with hCache := h }) S.sampleKey x st (fun k => k) coupledCache
      (fun h => RandomOracle.Cache.sum
        (RandomOracle.Cache.sum (RandomOracle.ofList st.gCache) h)
        (RandomOracle.ofList st.hqCache)) (fun _ => rfl)
  · rw [coupledCache, RandomOracle.answer_sum_inr]
    exact RandomOracle.eval_zoom_memoize_map SimState.hqCache
      (fun st q => { st with hqCache := q }) S.sampleKey c st (fun k => k) coupledCache
      (fun q => RandomOracle.Cache.sum
        (RandomOracle.Cache.sum (RandomOracle.ofList st.gCache) (RandomOracle.ofList st.hCache))
        q) (fun _ => rfl)

/-- `coupledHandler` interprets `coupledProgram` with the lazy oracles on `SimState`. -/
private theorem coupledHandler_eq_interpret (S : Scheme PK SK M R CT K) (pk : PK) (sk : SK)
    (cStar : CT) (q : ROQuery M CT) :
    S.coupledHandler pk sk cStar q =
      OracleComp.interpret S.lazyOracle (S.coupledProgram pk sk cStar q) := by
  cases q with
  | G m => exact (OracleComp.interpret_query S.lazyOracle (.inl (.inl m))).symm
  | H x =>
    rcases x with ⟨_ | _, m, c⟩
    · simp only [coupledHandler, coupledFilterHandler, simFilterDispatch, coupledHashH,
        coupledProgram, ROQuery.dispatch, OracleComp.interpret_bind, OracleComp.interpret_query]
      refine congrArg (simHashG S.pke.sampleCoins m >>= ·) (funext fun r => ?_)
      split_ifs <;> exact (OracleComp.interpret_query _ _).symm
    · exact (OracleComp.interpret_query S.lazyOracle (.inl (.inr (true, m, c)))).symm
  | decaps c =>
    by_cases hc : c = cStar
    · simp [coupledHandler, coupledFilterHandler, simFilterDispatch, coupledProgram, hc]
    · simp only [coupledHandler, coupledFilterHandler, simFilterDispatch, coupledProgram,
        ROQuery.dispatch, hc, ↓reduceIte, OracleComp.interpret_bind, OracleComp.interpret_query,
        OracleComp.interpret_pure]
      rfl

/-- `eagerCoupledHandler` interprets `coupledProgram` with the complete tables. -/
private theorem eagerCoupledHandler_eq_interpret (S : Scheme PK SK M R CT K) (G : M → R)
    (Hq : CT → K) (Hraw : Bool × M × CT → K) (pk : PK) (sk : SK) (cStar : CT)
    (q : ROQuery M CT) :
    S.eagerCoupledHandler G Hq Hraw pk sk cStar q =
      OracleComp.interpret (tableOracle G Hraw Hq) (S.coupledProgram pk sk cStar q) := by
  cases q with
  | G m => exact (OracleComp.interpret_query (tableOracle G Hraw Hq) (.inl (.inl m))).symm
  | H x =>
    rcases x with ⟨_ | _, m, c⟩
    · simp only [eagerCoupledHandler, coupledH, coupledProgram, ROQuery.dispatch,
        OracleComp.interpret_bind, OracleComp.interpret_query, Function.comp_apply,
        PMF.monad_bind_eq_bind, PMF.pure_bind]
      split_ifs <;> exact (OracleComp.interpret_query _ _).symm
    · exact (OracleComp.interpret_query (tableOracle G Hraw Hq) (.inl (.inr (true, m, c)))).symm
  | decaps c =>
    by_cases hc : c = cStar
    · simp [eagerCoupledHandler, coupledProgram, hc]
    · simp only [eagerCoupledHandler, coupledProgram, ROQuery.dispatch, hc, ↓reduceIte,
        OracleComp.interpret_bind, OracleComp.interpret_query, OracleComp.interpret_pure,
        PMF.monad_bind_eq_bind, PMF.pure_bind]
      rfl

/-- Running a program under `coupledHandler` has the law of completing the three caches into
tables `G`, `Hraw` and `Hq` and running it under `eagerCoupledHandler`. -/
private theorem eval_run_coupledHandler_eq_eager [Fintype M] [Finite R] [Fintype CT] [Finite K]
    (S : Scheme PK SK M R CT K) (pk : PK) (sk : SK) (cStar : CT) {α : Type}
    (prog : OracleComp (ROResp (M := M) (CT := CT) R K) α) (st : SimState M R CT K) :
    (ProbComp.eval ((OracleComp.interpret (S.coupledHandler pk sk cStar) prog).run st)).map
        Prod.fst =
      (RandomOracle.complete (fun _ => ProbComp.eval S.pke.sampleCoins)
          (RandomOracle.ofList st.gCache)).bind fun G =>
        (RandomOracle.complete (fun _ => ProbComp.eval S.sampleKey)
            (RandomOracle.ofList st.hCache)).bind fun Hraw =>
          (RandomOracle.complete (fun _ => ProbComp.eval S.sampleKey)
              (RandomOracle.ofList st.hqCache)).bind fun Hq =>
            OracleComp.interpret (S.eagerCoupledHandler G Hq Hraw pk sk cStar) prog := by
  have himpl : S.coupledHandler pk sk cStar = fun q =>
      OracleComp.interpret S.lazyOracle (S.coupledProgram pk sk cStar q) :=
    funext (S.coupledHandler_eq_interpret pk sk cStar)
  have heager (G : M → R) (Hq : CT → K) (Hraw : Bool × M × CT → K) :
      S.eagerCoupledHandler G Hq Hraw pk sk cStar = fun q =>
        OracleComp.interpret (tableOracle G Hraw Hq) (S.coupledProgram pk sk cStar q) :=
    funext (S.eagerCoupledHandler_eq_interpret G Hq Hraw pk sk cStar)
  simp only [heager, himpl, ← OracleComp.interpret_interpret]
  rw [RandomOracle.eval_run_interpret_eq_complete_bind S.coupledDistribution S.lazyOracle
      coupledCache S.eval_lazyOracle_map_coupledCache,
    ← RandomOracle.bind_complete_sum, ← RandomOracle.bind_complete_sum]
  congr 1 with T : 1
  congr 1 with q : 1
  rcases q with (m | x) | c <;> rfl

/-- **Lazy/eager equivalence of the coupled game**: the lazy coupled game `S.coupledGame A b`
has the output distribution of the eager coupled game `S.eagerCoupledGame A b`. -/
theorem eval_coupledGame_eq_eagerCoupledGame [Fintype M] [Finite R] [Fintype CT] [Finite K]
    (S : Scheme PK SK M R CT K) (A : ROAdversary PK M R CT K) (b : Bool) :
    ProbComp.eval (S.coupledGame A b) = S.eagerCoupledGame A b := by
  dsimp only [coupledGame, coupledFilterGame, eagerCoupledGame]
  simp only [show S.coupledFilterHandler (fun _ _ => true) = S.coupledHandler from rfl,
    pmf_norm, encT]
  congr 1 with ⟨pk, sk⟩ : 1
  have hstep (mStar : M) (rStar : R) :
      (ProbComp.eval ((S.coupledHashH pk sk (false, mStar, S.pke.encDet pk mStar rStar)).run
          { gCache := [(mStar, rStar)] })).bind (fun z =>
        (ProbComp.eval S.sampleKey).bind fun kRand =>
          (ProbComp.eval ((OracleComp.interpret
            (S.coupledHandler pk sk (S.pke.encDet pk mStar rStar))
            (A ⟨pk, S.pke.encDet pk mStar rStar, if b then kRand else z.1⟩)).run z.2)).bind
            fun a => PMF.pure a.1) =
      (pi (Function.update (fun _ : M => ProbComp.eval S.pke.sampleCoins) mStar
          (PMF.pure rStar))).bind fun G =>
        (ProbComp.eval S.sampleKey).bind fun kRand =>
        (pi (α := fun _ : Bool × M × CT => K) (fun _ => ProbComp.eval S.sampleKey)).bind fun H =>
        (pi (α := fun _ : CT => K) (fun _ => ProbComp.eval S.sampleKey)).bind fun Q =>
          OracleComp.interpret (S.eagerCoupledHandler G Q H pk sk (S.pke.encDet pk mStar rStar))
            (A ⟨pk, S.pke.encDet pk mStar rStar, if b then kRand else
              S.coupledH G Q H pk sk (false, mStar, S.pke.encDet pk mStar rStar)⟩) := by
    set cStar := S.pke.encDet pk mStar rStar
    have hP (kRand : K) :
        (ProbComp.eval ((OracleComp.interpret (S.coupledHandler pk sk cStar)
          (OracleComp.query (spec := ROResp (M := M) (CT := CT) R K)
            (ROQuery.H (false, mStar, cStar)) >>= fun k =>
              A ⟨pk, cStar, if b then kRand else k⟩)).run
          { gCache := [(mStar, rStar)] })).map Prod.fst =
        (ProbComp.eval ((S.coupledHashH pk sk (false, mStar, cStar)).run
          { gCache := [(mStar, rStar)] })).bind (fun z =>
          (ProbComp.eval ((OracleComp.interpret (S.coupledHandler pk sk cStar)
            (A ⟨pk, cStar, if b then kRand else z.1⟩)).run z.2)).bind fun a => PMF.pure a.1) := by
      rw [OracleComp.run_interpret_bind, OracleComp.run_interpret_query]
      simp only [pmf_norm]
      rfl
    rw [PMF.bind_comm]
    simp only [← hP]
    simp only [eval_run_coupledHandler_eq_eager]
    simp only [RandomOracle.complete_ofList_singleton, RandomOracle.ofList_nil,
      RandomOracle.complete_empty, OracleComp.interpret_bind, OracleComp.interpret_query,
      eagerCoupledHandler, pmf_norm, ROQuery.dispatch]
    pmf_swap
  simp only [hstep]
  pmf_hoist (ProbComp.eval S.sampleMsg)
  congr 1 with mStar : 1
  refine (bind_pi_update (fun _ : M => ProbComp.eval S.pke.sampleCoins) mStar _).trans ?_
  pmf_swap

end Scheme

end Cslib.Crypto.Protocols.FujisakiOkamoto
