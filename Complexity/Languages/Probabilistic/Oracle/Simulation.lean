/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Languages.Probabilistic.Oracle

/-!
# Stateful simulation with private randomness

An external oracle's invariant or state simulation remains valid when clients also draw private
randomness. Private draws leave oracle state untouched, and independent sampling commutes with
the distribution relating two state representations. These are specializations of the existing
`OracleComp` rules to the disjoint-sum interface, with no additional program induction.

## Main results

* `Cslib.ProbOracleComp.run_interpret_invariant`: external invariants survive private sampling.
* `Cslib.ProbOracleComp.run_interpret_simulation`: local joint-state simulation suffices.
* `Cslib.ProbOracleComp.run_interpret_map_state_of_invariant`: state representation on an invariant.
* `Cslib.ProbOracleComp.run_interpret_map_state`: deterministic representation of oracle state.
* `Cslib.ProbOracleComp.run_interpret_map_response_state`: represent replies and oracle state,
  leaving private samples unchanged.
* `Cslib.ProbOracleComp.run_interpret_readOnly`: preserve a fixed external environment.
* `Cslib.ProbOracleComp.run_interpret_run_interpret`: a handler with private coins and external
  calls, followed by the external oracle, is one stateful handler on the joint state.

## References

Adapts the cslib `crypto` branch's state simulation API at
`5ff69ca93402e7c947208dc56396d6d86203ccd8` to the typed sum of sampling and external calls.
-/

@[expose] public section

namespace Cslib.ProbOracleComp

open Probability
open OracleComp (sumHandler)

variable {Query α State State' : Type} {spec : Query → Type}

/-- Reading a fixed external environment retains it, independently of the client's private draws. -/
theorem run_interpret_readOnly (oracle : (q : Query) → State → PMF (spec q))
    (program : ProbOracleComp spec α) (s : State) :
    (OracleComp.interpret
      (sumHandler (fun n => StateT.lift (ProbComp.unifOracle n))
        (fun q state => (oracle q state).map (·, state))) program).run s =
      (OracleComp.interpret
        (sumHandler ProbComp.unifOracle (fun q => oracle q s)) program).map (·, s) := by
  have hhandler : sumHandler (fun n => StateT.lift (ProbComp.unifOracle n))
      (fun q state => (oracle q state).map (·, state)) =
      fun q state =>
        (sumHandler ProbComp.unifOracle (fun q => oracle q state) q).map (·, state) := by
    funext q state
    cases q <;> rfl
  rw [hhandler]
  exact OracleComp.run_interpret_readOnly
    (fun q state => sumHandler ProbComp.unifOracle (fun q => oracle q state) q) program s

/-- An external oracle's invariant is unaffected by the client's private sampling. -/
theorem run_interpret_invariant (oracle : (q : Query) → StateT State PMF (spec q))
    (invariant : State → Prop)
    (step : ∀ q s, invariant s → ∀ a s', (a, s') ∈ (oracle q s).support → invariant s')
    (program : ProbOracleComp spec α) (s : State) (hs : invariant s) (result : α) (s' : State)
    (h : (result, s') ∈ ((OracleComp.interpret
      (sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle) program).run s).support) :
    invariant s' := by
  apply OracleComp.run_interpret_invariant _ invariant ?_ program s hs result s' h
  intro q state hstate value next hnext
  cases q with
  | inl n =>
    change (value, next) ∈ ((ProbComp.unifOracle n).map (·, state)).support at hnext
    obtain ⟨_, _, heq⟩ := (PMF.mem_support_map_iff _ _ _).mp hnext
    exact (Prod.mk.inj heq).2 ▸ hstate
  | inr q => exact step q state hstate value next hnext

/-- A local probabilistic state simulation extends to clients with fresh private samples. -/
theorem run_interpret_simulation (oracle : (q : Query) → StateT State PMF (spec q))
    (oracle' : (q : Query) → StateT State' PMF (spec q)) (relate : State → PMF State')
    (step : ∀ q s, (oracle q s).bind (fun (a, s') => (relate s').map (a, ·)) =
      (relate s).bind (oracle' q)) (program : ProbOracleComp spec α) (s : State) :
    ((OracleComp.interpret
      (sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle) program).run s).bind
        (fun (a, s') => (relate s').map (a, ·)) =
      (relate s).bind (fun state => (OracleComp.interpret
        (sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle') program).run
          state) := by
  apply OracleComp.run_interpret_simulation
  intro q state
  cases q with
  | inl n =>
    change ((ProbComp.unifOracle n).map (·, state)).bind
      (fun (a, next) => (relate next).map (a, ·)) =
        (relate state).bind (fun next => (ProbComp.unifOracle n).map (·, next))
    simp only [PMF.map, Function.comp_def, PMF.bind_bind, PMF.pure_bind]
    exact PMF.bind_comm _ _ _
  | inr q => exact step q state

/-- Re-encode private state on invariant states while retaining independent private samples. -/
theorem run_interpret_map_state_of_invariant
    (oracle : (q : Query) → StateT State PMF (spec q))
    (oracle' : (q : Query) → StateT State' PMF (spec q))
    (represent : State → State') (invariant : State → Prop)
    (preserve : ∀ q s, invariant s → ∀ a s', (a, s') ∈ (oracle q s).support → invariant s')
    (step : ∀ q s, invariant s →
      (oracle q s).map (fun (a, s') => (a, represent s')) = oracle' q (represent s))
    (program : ProbOracleComp spec α) (s : State) (hs : invariant s) :
    ((OracleComp.interpret
      (sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle) program).run s).map
        (fun (a, s') => (a, represent s')) =
      (OracleComp.interpret
        (sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle') program).run
          (represent s) := by
  apply OracleComp.run_interpret_map_state_of_invariant _ _ represent invariant ?_ ?_ program s hs
  · intro q state hstate value next hnext
    cases q with
    | inl n =>
      change (value, next) ∈ ((ProbComp.unifOracle n).map (·, state)).support at hnext
      obtain ⟨_, _, heq⟩ := (PMF.mem_support_map_iff _ _ _).mp hnext
      exact (Prod.mk.inj heq).2 ▸ hstate
    | inr q => exact preserve q state hstate value next hnext
  · intro q state hstate
    cases q with
    | inl n =>
      change ((ProbComp.unifOracle n).map (·, state)).map
        (fun (a, next) => (a, represent next)) = (ProbComp.unifOracle n).map (·, represent state)
      simp only [PMF.map_comp, Function.comp_def]
    | inr q => exact step q state hstate

/-- A deterministic state representation commuting with external calls commutes with the whole
randomized adaptive program, retaining the result and represented private state. -/
theorem run_interpret_map_state (oracle : (q : Query) → StateT State PMF (spec q))
    (oracle' : (q : Query) → StateT State' PMF (spec q)) (represent : State → State')
    (step : ∀ q s, (oracle q s).map (fun (a, s') => (a, represent s')) =
      oracle' q (represent s)) (program : ProbOracleComp spec α) (s : State) :
    ((OracleComp.interpret
      (sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle) program).run s).map
        (fun (a, s') => (a, represent s')) =
      (OracleComp.interpret
        (sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle') program).run
          (represent s) := by
  exact run_interpret_map_state_of_invariant oracle oracle' represent (fun _ => True)
    (by simp) (fun q state _ => step q state) program s trivial

/-- Reply and state representations preserve randomized adaptive execution. Private samples
are forwarded unchanged; only external replies and the oracle's state are represented. -/
theorem run_interpret_map_response_state {spec' : Query → Type}
    (response : (q : Query) → spec q → spec' q)
    (oracle : (q : Query) → StateT State PMF (spec q))
    (oracle' : (q : Query) → StateT State' PMF (spec' q)) (represent : State → State')
    (step : ∀ q s, (oracle q s).map (fun (a, s') => (response q a, represent s')) =
      oracle' q (represent s)) (program : ProbOracleComp spec' α) (s : State) :
    ((OracleComp.interpret
      (sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
      (OracleComp.interpret (sumHandler (fun n => sample (ProbComp.unifFin n))
        (fun q => response q <$> query q)) program)).run s).map
        (fun (a, s') => (a, represent s')) =
      (OracleComp.interpret
        (sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle') program).run
          (represent s) := by
  let response' : (q : ℕ ⊕ Query) → probOracleSpec spec q → probOracleSpec spec' q
    | .inl _ => id
    | .inr q => response q
  have hadapter : (fun q => response' q <$> OracleComp.query q) =
      sumHandler (fun n => sample (ProbComp.unifFin n)) (fun q => response q <$> query q) := by
    funext q
    cases q with
    | inl n => simp [response', sumHandler, sample, ProbComp.unifFin]
    | inr q => rfl
  rw [← hadapter]
  apply OracleComp.run_interpret_map_response_state
  intro q state
  cases q with
  | inl n =>
    change ((ProbComp.unifOracle n).map (·, state)).map
      (fun (a, next) => (a, represent next)) = (ProbComp.unifOracle n).map (·, represent state)
    simp only [PMF.map_comp, Function.comp_def]
  | inr q => exact step q state

/-- A stateful handler that draws private coins and calls an external oracle, followed by that
oracle, is one stateful handler on the joint state. Private draws stay fresh, and the result, the
handler's state and the external oracle's state are retained jointly. -/
theorem run_interpret_run_interpret {Query' : Type} {spec' : Query' → Type}
    {Hidden External : Type}
    (inner : (q : Query) → StateT Hidden (ProbOracleComp spec') (spec q))
    (oracle : (q : Query') → StateT External PMF (spec' q))
    (program : ProbOracleComp spec α) (hidden : Hidden) (external : External) :
    (OracleComp.interpret (sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
      ((OracleComp.interpret (sumHandler (fun n => StateT.lift (sample (ProbComp.unifFin n))) inner)
        program).run hidden)).run external =
    ((OracleComp.interpret (sumHandler (fun n => StateT.lift (ProbComp.unifOracle n))
      (fun q state => ((OracleComp.interpret
        (sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
          ((inner q).run state.1)).run state.2).map
            (fun ⟨⟨a, b⟩, c⟩ => (a, b, c)))) program).run
        (hidden, external)).map
          (fun ⟨a, b, c⟩ => ((a, b), c)) := by
  rw [OracleComp.run_interpret_run_interpret, _root_.PMF.monad_map_eq_map]
  congr 3
  funext q state
  cases q with
  | inl n =>
    change PMF.map _ ((OracleComp.interpret (m := StateT External PMF) _
      ((StateT.lift (sample (ProbComp.unifFin n))).run state.1)).run state.2) = _
    simp only [StateT.run_lift, OracleComp.interpret_bind, OracleComp.interpret_pure,
      StateT.run_bind, StateT.run_pure, interpret_sample, ProbComp.unifFin,
      OracleComp.interpret_query]
    simp [sumHandler, StateT.lift, PMF.map, Function.comp_def]
  | inr q => rfl

end Cslib.ProbOracleComp
