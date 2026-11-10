/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Machine.Program
import CslibFrontier.Probability.PMF.Bind

/-!
# Halting bounds for effectful machines

A halting bound concerns the control state of every supported run, rather than merely its
externally stopped output. Once the machine has halted, extra fuel preserves the whole joint
distribution of machine configuration and interpreter state.

The choice and query programs are explicit parameters, as in `runConfigFrom`. `HaltsWithin`
quantifies over every stateful interpretation of those programs; it does not assert efficiency
of either handler.

## Main definitions

* `Turing.MultiTapeMachine.HaltsWithin`: all supported runs halt within the given clock.

## Main results

* `Turing.MultiTapeMachine.run_interpret_runConfigFrom_add_of_halted`: extra fuel has no effect
  once every supported run has halted.
* `Turing.MultiTapeMachine.interpret_runConfigFrom_add_of_halted_list`: the corresponding
  occurrence-preserving equality for List interpretation.
* `Turing.MultiTapeMachine.HaltsWithin.mono`: a halting bound remains valid when increased.

## References

Adapted from MultiTape/Oracle/Halting.lean on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8` to the common machine and typed program interface.
-/

@[expose] public section

namespace Turing.MultiTapeMachine

open Cslib

universe u v

variable {k : ℕ} {Symbol State Oracle : Type} {Query : Type u}
  {Choose : Type → Type v} {spec : OracleSpec.{u, 0} Query}
  [DecidableEq Oracle]
  (machine : MultiTapeMachine k Symbol State Oracle Choose)
  (choose : Choose (Action k Symbol State Oracle) → OracleComp spec (Action k Symbol State Oracle))
  (query : Oracle → List Symbol → OracleComp spec (List Symbol))

/-- Every supported execution halts within `fuel`, against every stateful interpreter. -/
def HaltsWithin (fuel : ℕ) (input : List Symbol) : Prop :=
  ∀ (OracleState : Type) (oracle : (q : Query) → StateT OracleState PMF (spec q))
    (s : OracleState) (final : Config k Symbol State Oracle input) (s' : OracleState),
    (final, s') ∈ ((OracleComp.interpret oracle
      (machine.runConfigFrom choose query fuel (machine.initialConfig input))).run s).support →
    final.tapes.state = none

/-- Once every supported execution has halted, extra time preserves the complete distribution. -/
theorem run_interpret_runConfigFrom_add_of_halted {OracleState : Type} {input : List Symbol}
    (oracle : (q : Query) → StateT OracleState PMF (spec q))
    (cfg : Config k Symbol State Oracle input) (fuel padding : ℕ) (s : OracleState)
    (hhalt : ∀ result ∈
      ((OracleComp.interpret oracle (machine.runConfigFrom choose query fuel cfg)).run s).support,
      result.1.tapes.state = none) :
    (OracleComp.interpret oracle
      (machine.runConfigFrom choose query (fuel + padding) cfg)).run s =
      (OracleComp.interpret oracle (machine.runConfigFrom choose query fuel cfg)).run s := by
  rw [runConfigFrom_add, OracleComp.interpret_bind, StateT.run_bind,
    Probability.PMF.monad_bind_eq_bind]
  conv_rhs => rw [← PMF.bind_pure
    ((OracleComp.interpret oracle (machine.runConfigFrom choose query fuel cfg)).run s)]
  apply Probability.PMF.bind_congr_on_support
  rintro ⟨final, s'⟩ hfinal
  simp [runConfigFrom_halted machine choose query _ final (hhalt _ hfinal)]

/-- Enumerating finite responses preserves every endpoint occurrence after halting.
Unlike a probability interpretation, a List interpreter may have no outcomes; this equality
does not itself assert that the machine cannot get stuck. -/
theorem interpret_runConfigFrom_add_of_halted_list {input : List Symbol}
    (oracle : (q : Query) → List (spec q))
    (cfg : Config k Symbol State Oracle input) (fuel padding : ℕ)
    (hhalt : ∀ final ∈ OracleComp.interpret oracle
      (machine.runConfigFrom choose query fuel cfg), final.tapes.state = none) :
    OracleComp.interpret oracle (machine.runConfigFrom choose query (fuel + padding) cfg) =
      OracleComp.interpret oracle (machine.runConfigFrom choose query fuel cfg) := by
  rw [runConfigFrom_add, OracleComp.interpret_bind]
  change List.flatMap _ _ = _
  calc
    _ = (OracleComp.interpret oracle
        (machine.runConfigFrom choose query fuel cfg)).flatMap (fun final => [final]) := by
      apply List.flatMap_congr
      intro final hfinal
      simp [runConfigFrom_halted machine choose query _ final (hhalt final hfinal)]
    _ = _ := by simp

variable {machine choose query}

/-- Any larger clock gives the same joint distribution once a halting bound is known. -/
theorem HaltsWithin.run_interpret_runConfigFrom_eq {fuel : ℕ} {input : List Symbol}
    (h : machine.HaltsWithin choose query fuel input) {OracleState : Type}
    (oracle : (q : Query) → StateT OracleState PMF (spec q))
    (larger : ℕ) (s : OracleState) (hle : fuel ≤ larger) :
    (OracleComp.interpret oracle
      (machine.runConfigFrom choose query larger (machine.initialConfig input))).run s =
      (OracleComp.interpret oracle
        (machine.runConfigFrom choose query fuel (machine.initialConfig input))).run s := by
  simpa only [Nat.add_sub_of_le hle] using
    machine.run_interpret_runConfigFrom_add_of_halted choose query oracle
      (machine.initialConfig input) fuel (larger - fuel) s
      (fun result hresult => h _ oracle s result.1 result.2 hresult)

/-- A halting bound remains valid when increased. -/
theorem HaltsWithin.mono {fuel larger : ℕ} {input : List Symbol}
    (h : machine.HaltsWithin choose query fuel input) (hle : fuel ≤ larger) :
    machine.HaltsWithin choose query larger input := by
  intro OracleState oracle s final s' hfinal
  rw [h.run_interpret_runConfigFrom_eq oracle larger s hle] at hfinal
  exact h OracleState oracle s final s' hfinal

/-- Padding a halting run also preserves its output and the final private state. -/
theorem HaltsWithin.run_interpret_run_eq {fuel : ℕ} {input : List Symbol}
    (h : machine.HaltsWithin choose query fuel input) {OracleState : Type}
    (oracle : (q : Query) → StateT OracleState PMF (spec q))
    (larger : ℕ) (s : OracleState) (hle : fuel ≤ larger) :
    (OracleComp.interpret oracle (machine.run choose query larger input)).run s =
      (OracleComp.interpret oracle (machine.run choose query fuel input)).run s := by
  simp only [run, runFrom, OracleComp.interpret_map, StateT.run_map,
    h.run_interpret_runConfigFrom_eq oracle larger s hle]

end Turing.MultiTapeMachine
