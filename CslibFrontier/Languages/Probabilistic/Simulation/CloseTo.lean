/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Languages.Probabilistic.QueryCount
public import CslibFrontier.Probability.StatisticalDistance.CloseTo
import CslibFrontier.Languages.Probabilistic.Simulation

/-!
# Approximate stateful oracle simulation

`OracleComp.run_interpret_simulation` lifts an exact local simulation, relating each call of one
stateful oracle to a call of another through a probabilistic change of state, to every adaptive
program. This module lifts an approximate local simulation in the same way: when each call `q`
commutes with the change of state up to statistical distance `cost q * ε`, a program whose calls
cost at most `d` in total commutes with it up to `d * ε`.

The typical use is a lazy-to-eager hop in which one kind of call is answered from partial
information (a cache) on the lazy side and from the completed table on the eager side, so that
the two disagree on an event of small probability; calls of other kinds cost nothing.

## Main results

* `Cslib.OracleComp.closeTo_run_interpret_simulation`: an approximate local simulation lifts to
  every cost-bounded program, retaining the result and the final state.
* `Cslib.OracleComp.closeTo_run_interpret_simulation_readOnly`: its marginal on the result when
  the target oracle only reads its state, as an eager table.
-/

public section

namespace Cslib.OracleComp

open Probability
open scoped ENNReal

variable {ι State State' α : Type} {spec : OracleSpec ι}

/-- **Approximate stateful simulation.** If each call `q` of `oracle` commutes with the change of
state `relate` up to statistical distance `cost q * ε`, then running any program `prog` with
`IsCostBounded cost prog d` commutes with `relate` up to statistical distance `d * ε`. -/
theorem closeTo_run_interpret_simulation (cost : ι → ℕ)
    (oracle : (q : ι) → StateT State PMF (spec q))
    (oracle' : (q : ι) → StateT State' PMF (spec q)) (relate : State → PMF State') (ε : ℝ≥0∞)
    (step : ∀ q s, CloseTo
      ((oracle q s).bind fun x => (relate x.2).map (x.1, ·))
      ((relate s).bind (oracle' q))
      (cost q * ε))
    (prog : OracleComp spec α) {d : ℕ} (hd : IsCostBounded cost prog d) (s : State) :
    CloseTo
      (((interpret oracle prog).run s).bind fun x => (relate x.2).map (x.1, ·))
      ((relate s).bind fun t => (interpret oracle' prog).run t)
      (d * ε) := by
  induction hd generalizing s with
  | pure a n =>
    simp only [run_interpret_pure, Probability.PMF.monad_pure_eq_pure, PMF.pure_bind, PMF.map,
      Function.comp_def]
    exact (CloseTo.refl _).mono zero_le
  | liftBind q cont n _ ih =>
    rw [run_interpret_bind, run_interpret_query]
    simp only [interpret_bind, interpret_query, StateT.run_bind,
      Probability.PMF.monad_bind_eq_bind, PMF.bind_bind]
    have h₁ : CloseTo
        ((oracle q s).bind fun x =>
          ((interpret oracle (cont x.1)).run x.2).bind fun y => (relate y.2).map (y.1, ·))
        ((oracle q s).bind fun x =>
          (relate x.2).bind fun t => (interpret oracle' (cont x.1)).run t)
        ((n : ℝ≥0∞) * ε) :=
      CloseTo.bind_right _ fun x _ => ih x.1 x.2
    have h₂ : CloseTo
        (((oracle q s).bind fun x => (relate x.2).map (x.1, ·)).bind fun y =>
          (interpret oracle' (cont y.1)).run y.2)
        (((relate s).bind (oracle' q)).bind fun y =>
          (interpret oracle' (cont y.1)).run y.2)
        (cost q * ε) :=
      (step q s).bind_left _
    simp only [PMF.bind_bind, PMF.bind_map, Function.comp_def] at h₂
    refine (h₁.trans h₂).mono (le_of_eq ?_)
    rw [← add_mul, Nat.cast_add]

/-- **Approximate simulation by a read-only oracle.** If each call `q` of `oracle` commutes up to
statistical distance `cost q * ε` with answering it by `oracle' t q` from a state `t ← relate s`
that the call leaves unchanged, then the result of running any program `prog` with
`IsCostBounded cost prog d` is within `d * ε` of sampling `t ← relate s` and interpreting `prog`
against `oracle' t`. -/
theorem closeTo_run_interpret_simulation_readOnly (cost : ι → ℕ)
    (oracle : (q : ι) → StateT State PMF (spec q))
    (oracle' : State' → (q : ι) → PMF (spec q)) (relate : State → PMF State') (ε : ℝ≥0∞)
    (step : ∀ q s, CloseTo
      ((oracle q s).bind fun x => (relate x.2).map (x.1, ·))
      ((relate s).bind fun t => (oracle' t q).map (·, t))
      (cost q * ε))
    (prog : OracleComp spec α) {d : ℕ} (hd : IsCostBounded cost prog d) (s : State) :
    CloseTo (((interpret oracle prog).run s).map Prod.fst)
      ((relate s).bind fun t => interpret (oracle' t) prog) (d * ε) := by
  have h := (closeTo_run_interpret_simulation cost oracle
    (fun q t => (oracle' t q).map (·, t)) relate ε step prog hd s).map Prod.fst
  have hL : (((interpret oracle prog).run s).bind fun x => (relate x.2).map (x.1, ·)).map
      Prod.fst = ((interpret oracle prog).run s).map Prod.fst := by
    simp only [PMF.map, PMF.bind_bind, PMF.pure_bind, Function.comp_def, PMF.bind_const]
  have hR : ((relate s).bind fun t =>
      (interpret (m := StateT State' PMF) (fun q t => (oracle' t q).map (·, t)) prog).run t).map
        Prod.fst = (relate s).bind fun t => interpret (oracle' t) prog := by
    rw [PMF.map_bind]
    congr 1 with t : 1
    have hro := congrArg (PMF.map Prod.fst)
      (run_interpret_readOnly (fun q t => oracle' t q) prog t)
    simp only [PMF.monad_map_eq_map, PMF.map_comp] at hro
    exact hro.trans (PMF.map_id _)
  rwa [hL, hR] at h

end Cslib.OracleComp
