/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.KEM.FujisakiOkamoto.NotBot.Hybrids
import CslibFrontier.Languages.Probabilistic.Norm
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

variable {PK SK M R CT K : Type}

namespace Scheme

variable [DecidableEq M] [DecidableEq CT]

/-- The three partial tables `(G, Hraw, Hq)` of the coupled game. -/
private abbrev Tables (M R CT K : Type) : Type :=
  RandomOracle.Cache (fun _ : M => R) × RandomOracle.Cache (fun _ : Bool × M × CT => K) ×
    RandomOracle.Cache (fun _ : CT => K)

/-- The represented tables of a `SimState`. -/
private def tablesOf (st : SimState M R CT K) : Tables M R CT K :=
  (RandomOracle.ofList st.gCache, RandomOracle.ofList st.hCache, RandomOracle.ofList st.hqCache)

/-- `coupledHashH` on represented tables, answered with `RandomOracle.answer`. -/
private noncomputable def answerHashH (S : Scheme PK SK M R CT K) (pk : PK) (sk : SK)
    (x : Bool × M × CT) : StateT (Tables M R CT K) PMF K := fun t =>
  match x with
  | (false, m, c) =>
    (RandomOracle.answer (fun _ => ProbComp.eval S.pke.sampleCoins) m t.1).bind fun y =>
      if S.pke.encDet pk m y.1 = c ∧ S.pke.dec sk c = some m then
        (RandomOracle.answer (fun _ => ProbComp.eval S.sampleKey) c t.2.2).map
          fun z => (z.1, (y.2, t.2.1, z.2))
      else
        (RandomOracle.answer (fun _ => ProbComp.eval S.sampleKey) (false, m, c) t.2.1).map
          fun z => (z.1, (y.2, z.2, t.2.2))
  | (true, m, c) =>
    (RandomOracle.answer (fun _ => ProbComp.eval S.sampleKey) (true, m, c) t.2.1).map
      fun z => (z.1, (t.1, z.2, t.2.2))

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

omit [DecidableEq M] [DecidableEq CT] in
/-- One lazy call on a component cache, with its result and represented state, is
`RandomOracle.answer` on the represented component. -/
private theorem eval_zoom_memoize_map {Key Value St T β : Type} [DecidableEq Key]
    (get : St → List (Key × Value)) (set : St → List (Key × Value) → St) (d : ProbComp Value)
    (q : Key) (s : St) (g : Value → β) (rep : St → T)
    (F : RandomOracle.Cache (fun _ : Key => Value) → T)
    (hrep : ∀ c, rep (set s c) = F (RandomOracle.ofList c)) :
    (ProbComp.eval (RandomOracle.zoomStateT get set (memoize (fun _ => d) q) s)).map
        (fun z => (g z.1, rep z.2)) =
      (RandomOracle.answer (fun _ => ProbComp.eval d) q (RandomOracle.ofList (get s))).map
        (fun z => (g z.1, F z.2)) := by
  rw [RandomOracle.eval_zoomStateT_memoize, ← RandomOracle.memoize_map_ofList]
  simp only [PMF.map_comp, Function.comp_def, hrep]

omit [DecidableEq M] [DecidableEq CT] in
/-- One lazy call on a component cache followed by a continuation, on represented states. -/
private theorem eval_zoom_memoize_bind {Key Value St T β : Type} [DecidableEq Key]
    (get : St → List (Key × Value)) (set : St → List (Key × Value) → St) (d : ProbComp Value)
    (q : Key) (s : St) (f : Value → St → ProbComp (β × St)) (rep : St → T)
    (Φ : Value × RandomOracle.Cache (fun _ : Key => Value) → PMF (β × T))
    (hf : ∀ v c, (ProbComp.eval (f v (set s c))).map (fun z => (z.1, rep z.2)) =
      Φ (v, RandomOracle.ofList c)) :
    (ProbComp.eval (RandomOracle.zoomStateT get set (memoize (fun _ => d) q) s >>=
        fun vs => f vs.1 vs.2)).map (fun z => (z.1, rep z.2)) =
      (RandomOracle.answer (fun _ => ProbComp.eval d) q (RandomOracle.ofList (get s))).bind Φ := by
  rw [ProbComp.eval_bind, RandomOracle.eval_zoomStateT_memoize,
    ← RandomOracle.memoize_map_ofList, PMF.map_bind, PMF.bind_map, PMF.bind_map]
  congr 1 with ⟨v, c⟩ : 1
  exact hf v c

/-- Mapping `SimState` to its represented tables turns `coupledHashH` into `answerHashH`. -/
private theorem coupledHashH_map_tablesOf (S : Scheme PK SK M R CT K) (pk : PK) (sk : SK)
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
    · simp only [coupledHandler, answerHandler, hc, ↓reduceIte]
      exact PMF.pure_map _ _
    · simp only [coupledHandler, answerHandler, hc, ↓reduceIte]
      change (ProbComp.eval (simHashHq S.sampleKey c st >>= fun vs =>
        pure (some vs.1, vs.2))).map _ = _
      refine Eq.trans ?_ (eval_zoom_memoize_map SimState.hqCache
        (fun st q => { st with hqCache := q }) S.sampleKey c st some tablesOf
        (fun q => (RandomOracle.ofList st.gCache, RandomOracle.ofList st.hCache, q))
        (fun _ => rfl))
      rw [ProbComp.eval_bind, PMF.map_bind]
      simp only [ProbComp.eval_pure, PMF.pure_map]
      rfl

section Answer

variable {Q V α α' β : Type} [Fintype Q] [Finite V] [DecidableEq Q]

omit [DecidableEq M] [DecidableEq CT]

/-- Answering one query and completing its table is completing the table and reading it,
followed by any continuation `F` that ignores the intermediate cache. -/
private theorem answer_bind_complete (d : Q → PMF V) (c : RandomOracle.Cache (fun _ : Q => V))
    (q : Q) (F : V × RandomOracle.Cache (fun _ : Q => V) → (Q → V) → PMF β)
    (hF : ∀ v c₁ c₂, F (v, c₁) = F (v, c₂)) :
    (RandomOracle.answer d q c).bind (fun x => (RandomOracle.complete d x.2).bind (F x)) =
      (RandomOracle.complete d c).bind (fun T => F (T q, c) T) := by
  have h := congrArg (fun p => p.bind (fun x => F (x.1, c) x.2))
    (RandomOracle.answer_complete d c q)
  simp only [Probability.PMF.monad_bind_eq_bind, PMF.bind_bind, PMF.bind_map,
    Function.comp_def] at h
  rw [← h]
  congr 1 with ⟨v, c'⟩ : 1
  rw [hF v c' c]

/-- `answer_bind_complete` past one independent sample `p`. -/
private theorem answer_bind_complete₁ (d : Q → PMF V) (c : RandomOracle.Cache (fun _ : Q => V))
    (q : Q) (p : PMF α) (F : V × RandomOracle.Cache (fun _ : Q => V) → α → (Q → V) → PMF β)
    (hF : ∀ v c₁ c₂, F (v, c₁) = F (v, c₂)) :
    (RandomOracle.answer d q c).bind (fun x => p.bind fun a =>
        (RandomOracle.complete d x.2).bind (F x a)) =
      (RandomOracle.complete d c).bind (fun T => p.bind fun a => F (T q, c) a T) := by
  simp only [PMF.bind_comm p]
  exact answer_bind_complete d c q (fun x T => p.bind fun a => F x a T)
    (fun v c₁ c₂ => by rw [hF v c₁ c₂])

/-- `answer_bind_complete` past two independent samples `p` and `p'`. -/
private theorem answer_bind_complete₂ (d : Q → PMF V) (c : RandomOracle.Cache (fun _ : Q => V))
    (q : Q) (p : PMF α) (p' : PMF α')
    (F : V × RandomOracle.Cache (fun _ : Q => V) → α → α' → (Q → V) → PMF β)
    (hF : ∀ v c₁ c₂, F (v, c₁) = F (v, c₂)) :
    (RandomOracle.answer d q c).bind (fun x => p.bind fun a => p'.bind fun b =>
        (RandomOracle.complete d x.2).bind (F x a b)) =
      (RandomOracle.complete d c).bind (fun T => p.bind fun a => p'.bind fun b =>
        F (T q, c) a b T) := by
  have h : (fun x : V × RandomOracle.Cache (fun _ : Q => V) => p.bind fun a => p'.bind fun b =>
      (RandomOracle.complete d x.2).bind (F x a b)) = fun x =>
      (RandomOracle.complete d x.2).bind fun T => p.bind fun a => p'.bind fun b => F x a b T :=
    funext fun x => by pmf_swap
  rw [h]
  exact answer_bind_complete d c q (fun x T => p.bind fun a => p'.bind fun b => F x a b T)
    (fun v c₁ c₂ => by rw [hF v c₁ c₂])

end Answer

section Complete

variable [Fintype M] [Finite R] [Fintype CT] [Finite K]

/-- Full tables `(G, Hraw, Hq)` of the eager coupled game. -/
private abbrev FullTables (M R CT K : Type) : Type :=
  (M → R) × (Bool × M × CT → K) × (CT → K)

/-- Complete the three represented tables independently. -/
private noncomputable def completeTables (S : Scheme PK SK M R CT K) (t : Tables M R CT K) :
    PMF (FullTables M R CT K) :=
  (RandomOracle.complete (fun _ => ProbComp.eval S.pke.sampleCoins) t.1).bind fun G =>
  (RandomOracle.complete (fun _ => ProbComp.eval S.sampleKey) t.2.1).bind fun H =>
  (RandomOracle.complete (fun _ => ProbComp.eval S.sampleKey) t.2.2).map fun Q => (G, H, Q)

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
  dsimp only [coupledGame, eagerCoupledGame]
  simp only [pmf_norm, encT]
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
