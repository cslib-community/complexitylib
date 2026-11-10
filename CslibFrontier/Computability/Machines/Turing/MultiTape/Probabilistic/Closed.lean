/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.Deterministic
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.Sequential
import CslibFrontier.Probability.PMF.Bind

/-!
# Configuration laws for closed fair-coin programs

Closed machines have no oracle channels and draw fresh fair bits through `ProbComp.uniform Bool`.
These specializations of the common machine laws let probabilistic realizations work directly
with configuration distributions. Actual halting is required when padding or sequencing clocks.

## Main definitions

* `Turing.MultiTapePTM.runClosedConfigFrom`: retain the configuration of a closed fair-coin run.

## Main results

* `Turing.MultiTapePTM.eval_runClosedConfigFrom_seq`: add two halting bounds.
* `Turing.MultiTapePTM.eval_runClosedConfigFrom_add_of_halted`: padding preserves halted runs.
* `Turing.MultiTapePTM.eval_runClosedConfigFrom_ofDeterministic`: deterministic run distributions.

## References

Specializations of the common halting, sequencing and deterministic embedding rules, adapted
from the cslib `crypto` branch at `5ff69ca93402e7c947208dc56396d6d86203ccd8`.
-/

@[expose] public section

namespace Turing.MultiTapePTM

open Cslib MultiTapeMachine MultiTapeMachine.Sequential

variable {k : ℕ} {Symbol State State₀ State₁ : Type} {input : List Symbol}

/-- Retain the complete configuration of a closed run with fresh fair coins. -/
noncomputable def runClosedConfigFrom (machine : MultiTapePTM k Symbol State) (fuel : ℕ)
    (cfg : Config k Symbol State Empty input) : ProbComp (Config k Symbol State Empty input) :=
  machine.runConfigFrom (ProbComp.uniform Bool) Empty.elim fuel cfg

/-- The closed output is the projection of the final configuration program. -/
theorem runClosed_eq_map (machine : MultiTapePTM k Symbol State) (fuel : ℕ)
    (input : List Symbol) :
    machine.runClosed fuel input =
      (fun final => final.tapes.output) <$>
        machine.runClosedConfigFrom fuel (machine.initialConfig input) := rfl

/-- Padding a halting run preserves the complete configuration distribution. -/
theorem eval_runClosedConfigFrom_add_of_halted (machine : MultiTapePTM k Symbol State)
    (cfg : Config k Symbol State Empty input) (fuel padding : ℕ)
    (hhalt : ∀ final ∈ (ProbComp.eval (machine.runClosedConfigFrom fuel cfg)).support,
      final.tapes.state = none) :
    ProbComp.eval (machine.runClosedConfigFrom (fuel + padding) cfg) =
      ProbComp.eval (machine.runClosedConfigFrom fuel cfg) := by
  conv_rhs => rw [← PMF.bind_pure
    (ProbComp.eval (machine.runClosedConfigFrom fuel cfg))]
  unfold runClosedConfigFrom runConfigFrom
  rw [MultiTapeMachine.runConfigFrom_add, ProbComp.eval_bind]
  apply Probability.PMF.bind_congr_on_support
  intro final hfinal
  rw [MultiTapeMachine.runConfigFrom_halted _ _ _ _ _ (hhalt final hfinal)]
  rfl

/-- Any larger clock gives the same configuration distribution after a halting bound. -/
theorem eval_runClosedConfigFrom_eq_of_halted (machine : MultiTapePTM k Symbol State)
    (cfg : Config k Symbol State Empty input) {fuel larger : ℕ} (hle : fuel ≤ larger)
    (hhalt : ∀ final ∈ (ProbComp.eval (machine.runClosedConfigFrom fuel cfg)).support,
      final.tapes.state = none) :
    ProbComp.eval (machine.runClosedConfigFrom larger cfg) =
      ProbComp.eval (machine.runClosedConfigFrom fuel cfg) := by
  simpa only [Nat.add_sub_of_le hle] using
    eval_runClosedConfigFrom_add_of_halted machine cfg fuel (larger - fuel) hhalt

/-- Padding a halting bound preserves the closed output distribution. -/
theorem eval_runClosed_eq_of_halted (machine : MultiTapePTM k Symbol State) (input : List Symbol)
    {fuel larger : ℕ} (hle : fuel ≤ larger)
    (hhalt : ∀ final ∈ (ProbComp.eval
      (machine.runClosedConfigFrom fuel (machine.initialConfig input))).support,
      final.tapes.state = none) :
    ProbComp.eval (machine.runClosed larger input) =
      ProbComp.eval (machine.runClosed fuel input) := by
  simp only [runClosed_eq_map, ProbComp.eval_map,
    eval_runClosedConfigFrom_eq_of_halted machine _ hle hhalt]

/-- Shared-tape sequencing preserves distributions once both phases have actually halted. -/
theorem eval_runClosedConfigFrom_seq (first : MultiTapePTM k Symbol State₀)
    (second : MultiTapePTM k Symbol State₁) (cfg : Config k Symbol State₀ Empty input)
    (firstTime secondTime : ℕ)
    (hfirst : ∀ result ∈ (ProbComp.eval (first.runClosedConfigFrom firstTime cfg)).support,
      result.tapes.state = none)
    (hsecond : ∀ result ∈ (ProbComp.eval (first.runClosedConfigFrom firstTime cfg)).support,
      ∀ final ∈ (ProbComp.eval
        (second.runClosedConfigFrom secondTime (start second result))).support,
        final.tapes.state = none) :
    ProbComp.eval ((first.seq second).runClosedConfigFrom
      (firstTime + secondTime) (left second cfg)) =
      (do
        let result ← ProbComp.eval (first.runClosedConfigFrom firstTime cfg)
        (ProbComp.eval
          (second.runClosedConfigFrom secondTime (start second result))).map right) := by
  have h := run_interpret_runConfigFrom_seq first second (ProbComp.uniform Bool) Empty.elim
    (fun q (s : Unit) => (fun a => (a, s)) <$> ProbComp.unifOracle q)
    cfg firstTime secondTime () (by
      intro result hresult
      rw [OracleComp.run_interpret_stateless, PMF.monad_map_eq_map] at hresult
      obtain ⟨final, hfinal, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hresult
      exact hfirst final hfinal) (by
      intro result hresult final hfinal
      rw [OracleComp.run_interpret_stateless, PMF.monad_map_eq_map] at hresult hfinal
      obtain ⟨source, hsource, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hresult
      obtain ⟨target, htarget, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hfinal
      exact hsecond source hsource target htarget)
  simp only [OracleComp.run_interpret_stateless] at h
  have hout := congrArg (PMF.map Prod.fst) h
  simp only [PMF.monad_map_eq_map, PMF.map_bind,
    PMF.bind_map, PMF.map_comp, Function.comp_def] at hout
  change PMF.map id _ = _ at hout
  rw [PMF.map_id] at hout
  exact hout

/-- A deterministic embedding has a point-mass configuration distribution. -/
theorem eval_runClosedConfigFrom_ofDeterministic (machine : MultiTapeTM k Symbol State)
    (fuel : ℕ) (cfg : Config k Symbol State Empty input) :
    ProbComp.eval ((ofDeterministic machine).runClosedConfigFrom fuel cfg) =
      PMF.pure { cfg with tapes := machine.runFrom cfg.tapes fuel } := by
  have h := run_interpret_runConfigFrom_ofDeterministic machine (ProbComp.uniform Bool) Empty.elim
    (fun q (s : Unit) => (fun a => (a, s)) <$> ProbComp.unifOracle q)
    (Probability.PMF.uniformOfFintype Bool)
    (fun s => by
      rw [OracleComp.run_interpret_stateless]
      exact congrArg (PMF.map (fun bit => (bit, s))) (ProbComp.eval_uniform Bool)) fuel cfg ()
  rw [OracleComp.run_interpret_stateless] at h
  have hout := congrArg (PMF.map Prod.fst) h
  simp only [PMF.monad_map_eq_map, PMF.map_comp,
    PMF.pure_map] at hout
  change PMF.map id _ = _ at hout
  rw [PMF.map_id] at hout
  exact hout

end Turing.MultiTapePTM
