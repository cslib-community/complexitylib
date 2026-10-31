/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Languages.Probabilistic.Repeat
public import Complexity.Languages.Probabilistic.Oracle.QueryCount

/-!
# Saved samples in adaptive oracle interactions

An external handler can consume one saved sample per call while the client continues drawing
independent private randomness. For a program making at most `n` external queries, `n`
independent samples drawn in advance give exactly the online joint law of the result and the
handler's state (`ProbOracleComp.IsQueryBounded.run_interpret_presample`). Unused samples are
discarded in this equality; they need not be independent of the final state or the client's
stopping time. The handler's fallback value is never used, so a run on a sufficient list of
samples is a function of those samples.

This is the library's presampling theorem. A program without private coins is the special case
`OracleComp.IsQueryBounded.run_interpret_presample`, and closed `ProbComp` handlers the special
case `ProbOracleComp.IsQueryBounded.eval_presample`.

## Main definitions

* `Cslib.OracleComp.withSampleList`: supply a list's head to a handler and retain its tail.

## Main results

* `Cslib.ProbOracleComp.IsQueryBounded.run_interpret_presample`: presampling preserves the joint
  law of result and state.
* `Cslib.ProbOracleComp.IsQueryBounded.eval_presample`: the same for closed probabilistic handlers.
* `Cslib.OracleComp.IsQueryBounded.run_interpret_presample`: the same without private coins.

## References

Adapted from Languages/Probabilistic/Presample.lean on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`, using the typed sum of private and external calls.
-/

@[expose] public section

namespace Cslib

namespace OracleComp

universe u v w

/-- Supply the next saved sample to a stateful handler. The fallback makes short lists total;
the ordinary state and unused suffix are retained. -/
def withSampleList {Query : Type u} {spec : Query → Type v} {State Value : Type v}
    {m : Type v → Type w} [Functor m] (fallback : Value)
    (oracle : Value → (q : Query) → StateT State m (spec q))
    (q : Query) : StateT (State × List Value) m (spec q) := fun (state, values) =>
  (fun (answer, next) => (answer, next, values.tail)) <$> oracle (values.headD fallback) q state

end OracleComp

namespace ProbOracleComp

open OracleComp Probability

variable {Query α State Value : Type} {spec : Query → Type}

/-- **Presampling.** A program makes at most `n` external queries, and a handler draws one sample
from `source` per external query. Answering from `n` independent samples drawn in advance instead
gives the same joint law of the result and the handler's state. Private samples are drawn online
in both runs. The statement is exact and independent of the efficiency of the program, the
handler and the source. -/
theorem IsQueryBounded.run_interpret_presample {program : ProbOracleComp spec α} {n : ℕ}
    (h : program.IsQueryBounded n) (source : PMF Value) (fallback : Value)
    (oracle : Value → (q : Query) → StateT State PMF (spec q)) (s : State) :
    ((PMF.iid source n).map List.ofFn).bind (fun values =>
      ((interpret (handler (fun k => StateT.lift (ProbComp.unifOracle k))
        (withSampleList fallback oracle)) program).run (s, values)).map
          fun result => (result.1, Prod.fst result.2)) =
      (interpret (handler (fun k => StateT.lift (ProbComp.unifOracle k))
        (fun q state => source.bind fun value => oracle value q state)) program).run s := by
  induction h generalizing s with
  | pure a n =>
    simp only [run_interpret_pure, PMF.monad_pure_eq_pure, PMF.pure_map, PMF.bind_const]
  | liftBind q cont n _ ih =>
    cases q with
    | inl k =>
      simp only [Sum.elim_inl, Nat.add_zero, run_interpret_bind, run_interpret_query, handler,
        StateT.lift, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.bind_bind,
        PMF.pure_bind, PMF.map_bind]
      rw [PMF.bind_comm]
      exact congrArg ((ProbComp.unifOracle k).bind ·) (funext fun a => ih a s)
    | inr q =>
      simp only [Sum.elim_inr, run_interpret_bind, run_interpret_query, handler, PMF.iid,
        withSampleList, PMF.monad_bind_eq_bind, PMF.monad_map_eq_map, PMF.map_bind, PMF.bind_bind,
        PMF.bind_map, PMF.map_comp, Function.comp_def, List.ofFn_succ, Fin.cons_zero,
        Fin.cons_succ, List.headD_cons, List.tail_cons]
      refine congrArg (source.bind ·) (funext fun value => ?_)
      rw [PMF.bind_comm]
      refine congrArg ((oracle value q s).bind ·) (funext fun result => ?_)
      rw [← ih result.1 result.2, PMF.bind_map]
      rfl

/-- **Presampling with closed probabilistic handlers.** The `ProbComp` form of
`IsQueryBounded.run_interpret_presample`: `n` saved samples from `source` give the online joint law
of the result and the handler's state. -/
theorem IsQueryBounded.eval_presample {program : ProbOracleComp spec α} {count : ℕ}
    (h : program.IsQueryBounded count) (source : ProbComp Value) (fallback : Value)
    (oracle : Value → (q : Query) → StateT State ProbComp (spec q)) (s : State) :
    ProbComp.eval (do
      let values ← replicate count source
      (fun (result, next, _) => (result, next)) <$> (interpret
        (handler (fun n => StateT.lift (ProbComp.unifFin n))
          (withSampleList fallback oracle)) program).run (s, values)) =
      ProbComp.eval ((interpret (handler (fun n => StateT.lift (ProbComp.unifFin n))
        (fun q s => do
          let value ← source
          oracle value q s)) program).run s) := by
  have hrun := h.run_interpret_presample (ProbComp.eval source) fallback
    (fun value q s => ProbComp.eval (oracle value q s)) s
  have hstep (q : Query) (state : State × List Value) :
      ProbComp.eval (withSampleList fallback oracle q state) =
        withSampleList fallback (fun value q s => ProbComp.eval (oracle value q s)) q state := by
    simp [withSampleList, PMF.monad_map_eq_map]
  simpa only [ProbComp.eval_bind, ProbComp.eval_map, eval_run_interpret, hstep,
    ProbComp.eval_replicate_iid] using hrun

end ProbOracleComp

/-- **Presampling without private coins.** A program makes at most `n` calls, and a handler draws
one sample from `source` per call. Answering from `n` independent samples drawn in advance gives
the same joint law of the result and the handler's state. -/
theorem OracleComp.IsQueryBounded.run_interpret_presample {Query State Value γ : Type}
    {spec : Query → Type} {program : OracleComp spec γ} {n : ℕ} (h : program.IsQueryBounded n)
    (source : PMF Value) (fallback : Value)
    (oracle : Value → (q : Query) → StateT State PMF (spec q)) (s : State) :
    ((Probability.PMF.iid source n).map List.ofFn).bind (fun values =>
      ((interpret (withSampleList fallback oracle) program).run (s, values)).map
        fun result => (result.1, Prod.fst result.2)) =
      (interpret (m := StateT State PMF)
        (fun q state => source.bind fun value => oracle value q state) program).run s := by
  simpa only [interpret_interpret, ProbOracleComp.interpret_query] using
    h.probOracleComp.run_interpret_presample source fallback oracle s

end Cslib
