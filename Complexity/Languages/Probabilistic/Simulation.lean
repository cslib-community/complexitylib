/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Languages.Probabilistic.Basic
import Complexity.Probability.PMF.Bind
import Complexity.Foundations.Control.Monad.IsMonadHom.StateT

/-!
# Stateful oracle simulation

Local simulation identities lift to arbitrary adaptive programs, retaining both the result and
the oracle's final private state. A simulation may randomly complete hidden state, as in the
lazy-sampling proof for a random function. The local identity only needs to hold at states
satisfying a preserved invariant.

These rules adapt Languages/Probabilistic/Simulation.lean from the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8` to the common `OracleComp.interpret` interface.
There is one oracle specification and one interpreter; stateful execution uses `StateT`.

## Main results

* `Cslib.OracleComp.induction`: structural induction with the step case
  `OracleComp.query q >>= cont`.
* `Cslib.OracleComp.run_interpret_pure`, `Cslib.OracleComp.run_interpret_bind`,
  `Cslib.OracleComp.run_interpret_map`, `Cslib.OracleComp.run_interpret_query`: stateful
  interpretation of `pure`, `>>=`, `<$>`, and `query`.
* `Cslib.OracleComp.run_interpret_invariant`: invariants of each call hold after execution.
* `Cslib.OracleComp.run_interpret_simulation_of_invariant`: probabilistic state simulation.
* `Cslib.OracleComp.run_interpret_map_state_of_invariant`: deterministic state representation.
* `Cslib.OracleComp.run_interpret_map_response_state`: represent both replies and private state.
* `Cslib.OracleComp.map_run_interpret`: a monad morphism commutes with stateful interpretation.
* `Cslib.OracleComp.run_interpret_lift`: lifted effects preserve the complete private state.
* `Cslib.OracleComp.run_interpret_run_interpret`: a stateful handler whose effects are oracle
  calls, followed by a stateful oracle for those calls, is one handler on the joint state.
-/

@[expose] public section

namespace Cslib.OracleComp

universe u v w

variable {ι : Type u} {spec : OracleSpec.{u, v} ι} {α State State' : Type v}

/-- Structural induction on an oracle program, presenting the step case as
`OracleComp.query q >>= cont`. -/
@[elab_as_elim] theorem induction {motive : OracleComp spec α → Prop}
    (pure : ∀ a, motive (pure a))
    (query_bind : ∀ q (cont : spec q → OracleComp spec α),
      (∀ a, motive (cont a)) → motive (query q >>= cont))
    (program : OracleComp spec α) : motive program := by
  induction program with
  | pure a => exact pure a
  | liftBind q cont ih => exact query_bind q cont ih

section RunInterpret

variable {β : Type v} {m : Type v → Type w} [Monad m]

/-- A pure program returns its value and leaves the state unchanged. -/
@[simp] theorem run_interpret_pure (oracle : (q : ι) → StateT State m (spec q)) (a : α)
    (s : State) : (interpret oracle (pure a)).run s = pure (a, s) := rfl

variable [LawfulMonad m]

/-- Running `program >>= next` runs `program`, then runs `next` at its result from the state it
reached. -/
theorem run_interpret_bind (oracle : (q : ι) → StateT State m (spec q))
    (program : OracleComp spec α) (next : α → OracleComp spec β) (s : State) :
    (interpret oracle (program >>= next)).run s =
      (interpret oracle program).run s >>= fun x => (interpret oracle (next x.1)).run x.2 := by
  rw [interpret_bind, StateT.run_bind]

/-- Mapping `f` over a program maps it over the result and keeps the final state. -/
theorem run_interpret_map (oracle : (q : ι) → StateT State m (spec q)) (f : α → β)
    (program : OracleComp spec α) (s : State) :
    (interpret oracle (f <$> program)).run s =
      Prod.map f id <$> (interpret oracle program).run s := by
  simp only [interpret_map, StateT.run_map]
  rfl

/-- A single call is answered by the stateful oracle from the current state. -/
theorem run_interpret_query (oracle : (q : ι) → StateT State m (spec q)) (q : ι)
    (s : State) : (interpret oracle (query q)).run s = oracle q s := by
  simp only [interpret_query]
  rfl

end RunInterpret

/-- Lifting every oracle action into state retains the original state beside its result. -/
theorem run_interpret_lift {m : Type v → Type*} [Monad m] [LawfulMonad m]
    (oracle : (q : ι) → m (spec q)) (program : OracleComp spec α) (s : State) :
    (interpret (fun q => StateT.lift (oracle q)) program).run s =
      (fun a => (a, s)) <$> interpret oracle program := by
  have hlift : (fun q => StateT.lift (σ := State) (oracle q)) =
      (fun q s => (fun a => (a, s)) <$> oracle q) := by
    funext q s
    simp only [StateT.lift, bind_pure_comp]
  rw [hlift, run_interpret_stateless]

/-- An invariant preserved by supported oracle transitions holds after every adaptive program. -/
theorem run_interpret_invariant
    (oracle : (q : ι) → StateT State PMF (spec q)) (invariant : State → Prop)
    (step : ∀ q s, invariant s → ∀ a s', (a, s') ∈ (oracle q s).support → invariant s')
    (program : OracleComp spec α) (s : State) (hs : invariant s)
    (result : α) (s' : State)
    (h : (result, s') ∈ ((interpret oracle program).run s).support) : invariant s' := by
  induction program using OracleComp.induction generalizing s with
  | pure a =>
    simp only [interpret_pure, StateT.run_pure, Probability.PMF.monad_pure_eq_pure,
      PMF.mem_support_pure_iff, Prod.mk.injEq] at h
    rwa [h.2]
  | query_bind q cont ih =>
    simp only [interpret_bind, interpret_query, StateT.run_bind,
      Probability.PMF.monad_bind_eq_bind, PMF.mem_support_bind_iff] at h
    obtain ⟨⟨a, next⟩, ha, h⟩ := h
    exact ih a next (step q s hs a next ha) h

/-- A probabilistic change of private state that commutes with calls on invariant states
commutes with an entire adaptive computation. Only supported transitions must preserve the
invariant, and the equality retains the joint result and final state. -/
theorem run_interpret_simulation_of_invariant
    (oracle : (q : ι) → StateT State PMF (spec q))
    (oracle' : (q : ι) → StateT State' PMF (spec q))
    (relate : State → PMF State') (invariant : State → Prop)
    (preserve : ∀ q s, invariant s → ∀ a s', (a, s') ∈ (oracle q s).support → invariant s')
    (step : ∀ q s, invariant s →
      (oracle q s).bind (fun (a, s') => (relate s').map (a, ·)) =
        (relate s).bind (oracle' q))
    (program : OracleComp spec α) (s : State) (hs : invariant s) :
    ((interpret oracle program).run s).bind (fun (a, s') => (relate s').map (a, ·)) =
      (relate s).bind (fun t => (interpret oracle' program).run t) := by
  induction program using OracleComp.induction generalizing s with
  | pure a => simp [PMF.map, Function.comp_def]
  | query_bind q cont ih =>
    simp only [interpret_bind, interpret_query, StateT.run_bind,
      Probability.PMF.monad_bind_eq_bind, PMF.bind_bind]
    calc
      _ = (oracle q s).bind (fun (a, s') =>
          (relate s').bind (fun t => (interpret oracle' (cont a)).run t)) := by
        apply Probability.PMF.bind_congr_on_support
        rintro ⟨a, s'⟩ hnext
        exact ih a s' (preserve q s hs a s' hnext)
      _ = ((oracle q s).bind (fun (a, s') => (relate s').map (a, ·))).bind
          (fun (a, t) => (interpret oracle' (cont a)).run t) := by
        simp only [PMF.bind_bind, PMF.bind_map, Function.comp_def]
      _ = _ := by
        rw [step q s hs, PMF.bind_bind]
        rfl

/-- A local probabilistic simulation lifts to every adaptive computation. -/
theorem run_interpret_simulation
    (oracle : (q : ι) → StateT State PMF (spec q))
    (oracle' : (q : ι) → StateT State' PMF (spec q))
    (relate : State → PMF State')
    (step : ∀ q s, (oracle q s).bind (fun (a, s') => (relate s').map (a, ·)) =
      (relate s).bind (oracle' q)) (program : OracleComp spec α) (s : State) :
    ((interpret oracle program).run s).bind (fun (a, s') => (relate s').map (a, ·)) =
      (relate s).bind (fun t => (interpret oracle' program).run t) :=
  run_interpret_simulation_of_invariant oracle oracle' relate (fun _ => True)
    (by simp) (fun q s _ => step q s) program s trivial

/-- Re-encoding private state preserves adaptive execution when calls agree on invariant states. -/
theorem run_interpret_map_state_of_invariant
    (oracle : (q : ι) → StateT State PMF (spec q))
    (oracle' : (q : ι) → StateT State' PMF (spec q))
    (represent : State → State') (invariant : State → Prop)
    (preserve : ∀ q s, invariant s → ∀ a s', (a, s') ∈ (oracle q s).support → invariant s')
    (step : ∀ q s, invariant s →
      (oracle q s).map (fun (a, s') => (a, represent s')) = oracle' q (represent s))
    (program : OracleComp spec α) (s : State) (hs : invariant s) :
    ((interpret oracle program).run s).map (fun (a, s') => (a, represent s')) =
      (interpret oracle' program).run (represent s) := by
  simpa only [PMF.pure_map, PMF.pure_bind, PMF.map, Function.comp_def] using
    run_interpret_simulation_of_invariant oracle oracle' (fun s => PMF.pure (represent s))
      invariant preserve
      (by simpa only [PMF.pure_map, PMF.pure_bind, PMF.map, Function.comp_def] using step)
      program s hs

/-- A deterministic representation commuting with each call preserves the complete execution. -/
theorem run_interpret_map_state
    (oracle : (q : ι) → StateT State PMF (spec q))
    (oracle' : (q : ι) → StateT State' PMF (spec q)) (represent : State → State')
    (step : ∀ q s, (oracle q s).map (fun (a, s') => (a, represent s')) =
      oracle' q (represent s)) (program : OracleComp spec α) (s : State) :
    ((interpret oracle program).run s).map (fun (a, s') => (a, represent s')) =
      (interpret oracle' program).run (represent s) :=
  run_interpret_map_state_of_invariant oracle oracle' represent (fun _ => True)
    (by simp) (fun q s _ => step q s) program s trivial

/-- Representing replies and private state commutes with adaptive execution. Oracle substitution
supplies each target reply by mapping a source reply, including to adaptive continuations.
This corollary of state simulation retains the joint result and represented final state. -/
theorem run_interpret_map_response_state {spec' : OracleSpec.{u, v} ι}
    (response : (q : ι) → spec q → spec' q)
    (oracle : (q : ι) → StateT State PMF (spec q))
    (oracle' : (q : ι) → StateT State' PMF (spec' q)) (represent : State → State')
    (step : ∀ q s, (oracle q s).map (fun (a, s') => (response q a, represent s')) =
      oracle' q (represent s)) (program : OracleComp spec' α) (s : State) :
    ((interpret oracle (interpret (fun q => response q <$> query q) program)).run s).map
        (fun (a, s') => (a, represent s')) =
      (interpret oracle' program).run (represent s) := by
  rw [interpret_interpret]
  apply run_interpret_map_state
  intro q state
  change ((oracle q state).map (fun (a, next) => (response q a, next))).map
    (fun (a, next) => (a, represent next)) = oracle' q (represent state)
  simpa only [PMF.map_comp, Function.comp_def] using step q state

/-- Transforming the underlying monad commutes with stateful program interpretation, retaining
the joint result and private state. -/
theorem map_run_interpret {m n : Type v → Type*} [Monad m] [Monad n]
    [LawfulMonad m] [LawfulMonad n] {f : ∀ {β}, m β → n β}
    (hf : IsMonadHom m n f) (oracle : (q : ι) → StateT State m (spec q))
    (program : OracleComp spec α) (s : State) :
    f ((interpret oracle program).run s) =
      (interpret (m := StateT State n) (fun q state => f (oracle q state)) program).run s :=
  congrFun ((hf.stateT State).map_pfunctorFreeMLiftM (P := ⟨ι, spec⟩) oracle program) s

/-- Running a program against a stateful handler whose own effects are oracle calls, and then
running those calls against a stateful oracle, is one stateful execution on the joint state. The
result, the handler's final state and the oracle's final state are retained jointly. -/
theorem run_interpret_run_interpret {κ : Type w} {target : OracleSpec.{w, v} κ}
    {Hidden External : Type v} {m : Type v → Type*} [Monad m] [LawfulMonad m]
    (handler : (q : ι) → StateT Hidden (OracleComp target) (spec q))
    (oracle : (q : κ) → StateT External m (target q))
    (program : OracleComp spec α) (hidden : Hidden) (external : External) :
    (interpret oracle ((interpret handler program).run hidden)).run external =
      (fun ⟨a, b, c⟩ => ((a, b), c)) <$>
        (interpret (m := StateT (Hidden × External) m) (fun q state =>
          (fun ⟨⟨a, b⟩, c⟩ => (a, b, c)) <$>
            (interpret oracle ((handler q).run state.1)).run state.2) program).run
          (hidden, external) := by
  induction program using OracleComp.induction generalizing hidden external with
  | pure a => simp
  | query_bind q cont ih =>
    simp only [interpret_bind, interpret_query, StateT.run_bind, map_bind]
    simp only [StateT.run, bind_map_left]
    exact bind_congr fun (result : (spec q × Hidden) × External) =>
      ih result.1.1 result.1.2 result.2

end OracleComp

end Cslib
