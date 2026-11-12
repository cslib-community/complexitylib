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
import CslibFrontier.Languages.Probabilistic.Simulation
import CslibFrontier.Tactic.PMFSwap

/-!
# Lazy/eager equivalence of the coupled `FO-notbot` game

The lazy coupled game `Scheme.coupledGame` of
`CslibFrontier.Crypto.Protocols.KEM.FujisakiOkamoto.NotBot.Hybrids` answers `G`, the ciphertext
table `Hq` and the raw table `Hraw` lazily on the three caches of `SimState`. This module proves
that it has the same output distribution as the eager coupled game `Scheme.eagerCoupledGame`, a
step in the IND-CCA proof for `FO-notbot` of [HofheinzHoevelmannsKiltz2017] (IACR ePrint 2017/604,
full version dated 2 November 2021, §3.1 and §3.2.2).

The proof follows the eager/lazy argument of
`CslibFrontier.Crypto.Protocols.KEM.FujisakiOkamoto.Security`: the list caches are mapped to
`RandomOracle.Cache` tables with `RandomOracle.ofList`, and the three tables are then completed
at once with `RandomOracle.complete`; each oracle call commutes with completion by
`RandomOracle.answer_complete`.

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
open RandomOracle (eval_zoom_memoize_map eval_zoom_memoize_bind
  answer_bind_complete answer_bind_complete₁ answer_bind_complete₂)

variable {PK SK M R CT K : Type}

namespace Scheme

variable [DecidableEq M] [DecidableEq CT]

/-- The three partial tables `(G, Hraw, Hq)` of the coupled game. -/
abbrev Tables (M R CT K : Type) : Type :=
  RandomOracle.Cache (fun _ : M => R) × RandomOracle.Cache (fun _ : Bool × M × CT => K) ×
    RandomOracle.Cache (fun _ : CT => K)

/-- The represented tables of a `SimState`. -/
@[expose] def tablesOf (st : SimState M R CT K) : Tables M R CT K :=
  (RandomOracle.ofList st.gCache, RandomOracle.ofList st.hCache, RandomOracle.ofList st.hqCache)

/-- `coupledHashH` on represented tables, answered with `RandomOracle.answer`. -/
@[expose] noncomputable def answerHashH (S : Scheme PK SK M R CT K) (pk : PK) (sk : SK)
    (x : Bool × M × CT) : StateT (Tables M R CT K) PMF K := fun (tG, tH, tQ) =>
  match x with
  | (false, m, c) =>
    (RandomOracle.answer (fun _ => ProbComp.eval S.pke.sampleCoins) m tG).bind fun y =>
      if S.pke.encDet pk m y.1 = c ∧ S.pke.dec sk c = some m then
        (RandomOracle.answer (fun _ => ProbComp.eval S.sampleKey) c tQ).map
          fun z => (z.1, (y.2, tH, z.2))
      else
        (RandomOracle.answer (fun _ => ProbComp.eval S.sampleKey) (false, m, c) tH).map
          fun z => (z.1, (y.2, z.2, tQ))
  | (true, m, c) =>
    (RandomOracle.answer (fun _ => ProbComp.eval S.sampleKey) (true, m, c) tH).map
      fun z => (z.1, (tG, z.2, tQ))

/-- `coupledHandler` on represented tables, answered with `RandomOracle.answer`. -/
private noncomputable def answerHandler (S : Scheme PK SK M R CT K) (pk : PK) (sk : SK)
    (cStar : CT) (q : ROQuery M CT) : StateT (Tables M R CT K) PMF (ROResp R K q) := fun t =>
  match q with
  | .G m =>
    (RandomOracle.answer (fun _ => ProbComp.eval S.pke.sampleCoins) m t.1).map
      fun z => (z.1, (z.2, t.2.1, t.2.2))
  | .H x => S.answerHashH pk sk x t
  | .decaps c =>
    if c = cStar then PMF.pure (none, t)
    else
      (RandomOracle.answer (fun _ => ProbComp.eval S.sampleKey) c t.2.2).map
        fun z => (some z.1, (t.1, t.2.1, z.2))

/-- Mapping `SimState` to its represented tables turns `coupledHashH` into `answerHashH`. -/
theorem coupledHashH_map_tablesOf (S : Scheme PK SK M R CT K) (pk : PK) (sk : SK)
    (x : Bool × M × CT) (st : SimState M R CT K) :
    (ProbComp.eval (S.coupledHashH pk sk x st)).map (fun z => (z.1, tablesOf z.2)) =
      S.answerHashH pk sk x (tablesOf st) := by
  rcases x with ⟨_ | _, m, c⟩
  · change (ProbComp.eval (simHashG S.pke.sampleCoins m st >>= fun vs =>
        (if S.pke.encDet pk m vs.1 = c ∧ S.pke.dec sk c = some m then
          simHashHq S.sampleKey c else simHashHRaw S.sampleKey (false, m, c)) vs.2)).map _ = _
    dsimp only [answerHashH, simHashG]
    refine eval_zoom_memoize_bind (fun st : SimState M R CT K => st.gCache)
      (fun st g => { st with gCache := g }) S.pke.sampleCoins m st
      (fun r st' => (if S.pke.encDet pk m r = c ∧ S.pke.dec sk c = some m then
          simHashHq S.sampleKey c else simHashHRaw S.sampleKey (false, m, c)) st')
      tablesOf _ (fun r gC => ?_)
    by_cases h : S.pke.encDet pk m r = c ∧ S.pke.dec sk c = some m
    · simp only [h, and_self, ↓reduceIte]
      exact eval_zoom_memoize_map SimState.hqCache (fun st q => { st with hqCache := q })
        S.sampleKey c _ (fun k => k) tablesOf
        (fun q => (RandomOracle.ofList gC, RandomOracle.ofList st.hCache, q)) (fun _ => rfl)
    · simp only [h, ↓reduceIte]
      exact eval_zoom_memoize_map (fun st : SimState M R CT K => st.hCache)
        (fun st h => { st with hCache := h }) S.sampleKey (false, m, c) _ (fun k => k) tablesOf
        (fun h => (RandomOracle.ofList gC, h, RandomOracle.ofList st.hqCache)) (fun _ => rfl)
  · exact eval_zoom_memoize_map (fun st : SimState M R CT K => st.hCache)
      (fun st h => { st with hCache := h }) S.sampleKey (true, m, c) st (fun k => k) tablesOf
      (fun h => (RandomOracle.ofList st.gCache, h, RandomOracle.ofList st.hqCache)) (fun _ => rfl)

/-- Mapping `SimState` to its represented tables turns `coupledHandler` into `answerHandler`. -/
private theorem coupledHandler_map_tablesOf (S : Scheme PK SK M R CT K) (pk : PK) (sk : SK)
    (cStar : CT) (q : ROQuery M CT) (st : SimState M R CT K) :
    (ProbComp.eval (S.coupledHandler pk sk cStar q st)).map (fun z => (z.1, tablesOf z.2)) =
      S.answerHandler pk sk cStar q (tablesOf st) := by
  cases q with
  | G m =>
    exact eval_zoom_memoize_map (fun st : SimState M R CT K => st.gCache)
      (fun st g => { st with gCache := g }) S.pke.sampleCoins m st (fun r => r) tablesOf
      (fun g => (g, RandomOracle.ofList st.hCache, RandomOracle.ofList st.hqCache))
      (fun _ => rfl)
  | H x => exact S.coupledHashH_map_tablesOf pk sk x st
  | decaps c =>
    by_cases hc : c = cStar
    · simp only [coupledHandler, coupledFilterHandler, simFilterDispatch, answerHandler, hc,
        ↓reduceIte]
      exact PMF.pure_map _ _
    · simp only [coupledHandler, coupledFilterHandler, simFilterDispatch, answerHandler, hc,
        ↓reduceIte, Bool.cond_true]
      change (ProbComp.eval (simHashHq S.sampleKey c st >>= fun vs =>
        pure (some vs.1, vs.2))).map _ = _
      refine Eq.trans ?_ (eval_zoom_memoize_map SimState.hqCache
        (fun st q => { st with hqCache := q }) S.sampleKey c st some tablesOf
        (fun q => (RandomOracle.ofList st.gCache, RandomOracle.ofList st.hCache, q))
        (fun _ => rfl))
      rw [ProbComp.eval_bind, PMF.map_bind]
      simp only [ProbComp.eval_pure, PMF.pure_map]
      rfl

section Complete

variable [Fintype M] [Finite R] [Fintype CT] [Finite K]

/-- Full tables `(G, Hraw, Hq)` of the eager coupled game. -/
abbrev FullTables (M R CT K : Type) : Type :=
  (M → R) × (Bool × M × CT → K) × (CT → K)

/-- Complete the three represented tables independently. -/
@[expose] noncomputable def completeTables (S : Scheme PK SK M R CT K) :
    Tables M R CT K → PMF (FullTables M R CT K)
  | (tG, tH, tQ) =>
    (RandomOracle.complete (fun _ => ProbComp.eval S.pke.sampleCoins) tG).bind fun G =>
    (RandomOracle.complete (fun _ => ProbComp.eval S.sampleKey) tH).bind fun H =>
    (RandomOracle.complete (fun _ => ProbComp.eval S.sampleKey) tQ).map fun Q => (G, H, Q)

/-- `eagerCoupledHandler` reading its tables from the state. -/
private noncomputable def eagerStateHandler (S : Scheme PK SK M R CT K) (pk : PK) (sk : SK)
    (cStar : CT) (q : ROQuery M CT) : StateT (FullTables M R CT K) PMF (ROResp R K q) :=
  fun T => (S.eagerCoupledHandler T.1 T.2.2 T.2.1 pk sk cStar q).map (·, T)

/-- Single-step simulation from `answerHandler` to `eagerStateHandler` via
`RandomOracle.answer_complete`. -/
private theorem answerHandler_sim (S : Scheme PK SK M R CT K) (pk : PK) (sk : SK) (cStar : CT)
    (q : ROQuery M CT) (t : Tables M R CT K) :
    (S.answerHandler pk sk cStar q t).bind (fun x => (S.completeTables x.2).map (x.1, ·)) =
      (S.completeTables t).bind (S.eagerStateHandler pk sk cStar q) := by
  rcases t with ⟨tG, tH, tQ⟩
  cases q with
  | G m =>
    simp only [answerHandler, completeTables, eagerStateHandler, eagerCoupledHandler, pmf_norm]
    rw [answer_bind_complete]
    · rfl
    · intros; rfl
  | H x =>
    rcases x with ⟨_ | _, m, c⟩
    · simp only [answerHandler, answerHashH, completeTables, eagerStateHandler,
        eagerCoupledHandler, coupledH, pmf_norm]
      refine Eq.trans ?_ (answer_bind_complete _ tG m
        (fun x G => (RandomOracle.complete (fun _ => ProbComp.eval S.sampleKey) tH).bind fun H =>
          (RandomOracle.complete (fun _ => ProbComp.eval S.sampleKey) tQ).bind fun Q =>
            PMF.pure (if S.pke.encDet pk m x.1 = c ∧ S.pke.dec sk c = some m then Q c
              else H (false, m, c), G, H, Q)) (fun _ _ _ => rfl))
      congr 1 with y : 1
      by_cases h : S.pke.encDet pk m y.1 = c ∧ S.pke.dec sk c = some m
      · simp only [h, and_self, ↓reduceIte, pmf_norm, PMF.map]
        rw [answer_bind_complete₂]
        · pmf_swap
        · intros; rfl
      · simp only [h, ↓reduceIte, pmf_norm, PMF.map]
        rw [answer_bind_complete₁]
        · pmf_swap
        · intros; rfl
    · simp only [answerHandler, answerHashH, completeTables, eagerStateHandler,
        eagerCoupledHandler, coupledH, pmf_norm, PMF.map]
      rw [answer_bind_complete₁]
      · pmf_swap
      · intros; rfl
  | decaps c =>
    by_cases hc : c = cStar
    · simp only [answerHandler, completeTables, eagerStateHandler, eagerCoupledHandler, hc,
        ↓reduceIte, pmf_norm, PMF.map]
    · simp only [answerHandler, completeTables, eagerStateHandler, eagerCoupledHandler, hc,
        ↓reduceIte, pmf_norm, PMF.map]
      rw [answer_bind_complete₂]
      · pmf_swap
      · intros; rfl

/-- Running `prog` under `coupledHandler` from `st` has the output distribution of completing the
represented tables of `st` and interpreting `prog` under `eagerCoupledHandler`. -/
private theorem eval_run_coupledHandler_eq_eager (S : Scheme PK SK M R CT K) (pk : PK) (sk : SK)
    (cStar : CT) {α : Type} (prog : OracleComp (ROResp (M := M) (CT := CT) R K) α)
    (st : SimState M R CT K) :
    (ProbComp.eval ((OracleComp.interpret (S.coupledHandler pk sk cStar) prog).run st)).map
        Prod.fst =
      (S.completeTables (tablesOf st)).bind fun T =>
        OracleComp.interpret (S.eagerCoupledHandler T.1 T.2.2 T.2.1 pk sk cStar) prog := by
  rw [OracleComp.map_run_interpret ProbComp.isMonadHom_eval]
  have hmap := congrArg (PMF.map Prod.fst)
    (OracleComp.run_interpret_map_state
      (fun q s => ProbComp.eval (S.coupledHandler pk sk cStar q s))
      (S.answerHandler pk sk cStar) tablesOf
      (fun q s => S.coupledHandler_map_tablesOf pk sk cStar q s) prog st)
  simp only [PMF.map_comp, Function.comp_def] at hmap
  rw [hmap, OracleComp.run_interpret_simulation_fst _ (S.eagerStateHandler pk sk cStar) _
    (fun q t => S.answerHandler_sim pk sk cStar q t)]
  congr 1 with T : 1
  have hro := congrArg (PMF.map Prod.fst)
    (OracleComp.run_interpret_readOnly
      (fun q T' => S.eagerCoupledHandler T'.1 T'.2.2 T'.2.1 pk sk cStar q) prog T)
  change ((OracleComp.interpret (S.eagerStateHandler pk sk cStar) prog).run T).map Prod.fst =
    ((OracleComp.interpret (fun q => S.eagerCoupledHandler T.1 T.2.2 T.2.1 pk sk cStar q)
      prog).map (fun a => (a, T))).map Prod.fst at hro
  rw [PMF.map_comp] at hro
  exact hro.trans (PMF.map_id _)

end Complete

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
            (A (pk, S.pke.encDet pk mStar rStar, if b then kRand else z.1))).run z.2)).bind
            fun a => PMF.pure a.1) =
      (pi (Function.update (fun _ : M => ProbComp.eval S.pke.sampleCoins) mStar
          (PMF.pure rStar))).bind fun G =>
        (ProbComp.eval S.sampleKey).bind fun kRand =>
        (pi (α := fun _ : Bool × M × CT => K) (fun _ => ProbComp.eval S.sampleKey)).bind fun H =>
        (pi (α := fun _ : CT => K) (fun _ => ProbComp.eval S.sampleKey)).bind fun Q =>
          OracleComp.interpret (S.eagerCoupledHandler G Q H pk sk (S.pke.encDet pk mStar rStar))
            (A (pk, S.pke.encDet pk mStar rStar, if b then kRand else
              S.coupledH G Q H pk sk (false, mStar, S.pke.encDet pk mStar rStar))) := by
    set cStar := S.pke.encDet pk mStar rStar
    have hP (kRand : K) :
        (ProbComp.eval ((OracleComp.interpret (S.coupledHandler pk sk cStar)
          (OracleComp.query (spec := ROResp (M := M) (CT := CT) R K)
            (ROQuery.H (false, mStar, cStar)) >>= fun k =>
              A (pk, cStar, if b then kRand else k))).run
          { gCache := [(mStar, rStar)] })).map Prod.fst =
        (ProbComp.eval ((S.coupledHashH pk sk (false, mStar, cStar)).run
          { gCache := [(mStar, rStar)] })).bind (fun z =>
          (ProbComp.eval ((OracleComp.interpret (S.coupledHandler pk sk cStar)
            (A (pk, cStar, if b then kRand else z.1))).run z.2)).bind fun a => PMF.pure a.1) := by
      rw [OracleComp.run_interpret_bind, OracleComp.run_interpret_query]
      simp only [pmf_norm]
      rfl
    rw [PMF.bind_comm]
    simp only [← hP]
    simp only [eval_run_coupledHandler_eq_eager]
    simp only [completeTables, tablesOf,
      RandomOracle.complete_ofList_singleton, RandomOracle.ofList_nil,
      RandomOracle.complete_empty, OracleComp.interpret_bind, OracleComp.interpret_query,
      eagerCoupledHandler, pmf_norm]
    pmf_swap
  simp only [hstep]
  pmf_hoist (ProbComp.eval S.sampleMsg)
  congr 1 with mStar : 1
  refine (bind_pi_update (fun _ : M => ProbComp.eval S.pke.sampleCoins) mStar _).trans ?_
  pmf_swap

end Scheme

end Cslib.Crypto.Protocols.FujisakiOkamoto
