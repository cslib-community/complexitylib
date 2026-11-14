/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

import CslibFrontier.Crypto.Protocols.SSP.Hybrid

/-!
# Tests for the state-separating proofs package calculus

The closed package `bitPkg b` answers every query with the bit `b`; the adversary `askBit` queries
it once and outputs the reply, so it tells `bitPkg true` from `bitPkg false` with advantage `1`
(`advantage_askBit`). Against `m` independent sessions of `bitPkg b`, the adversary `askSession j`
reaches the session `j` and again sees `b` (`eval_run_askSession`), so the hybrid bound
`advantage_parFin_le_sum` splits the multi-session advantage `1` into single-session advantages
whose sum is at least `1`. With a global package, two forwarding sessions `Machine.id` reach the
global package `bitPkg true`, while two sessions of `falsePkg` answer `false` without consulting
it; the global hybrid bound `advantage_globalWorld_le_sum` then splits the advantage `1` of
`askGlobal` into single-session advantages in the presence of the global package.
-/

namespace CslibFrontierTests.Crypto.SSP

open Cslib Cslib.Crypto Cslib.Crypto.Protocols.SSP
open Cslib.Crypto.Protocols.UC (Machine)
open scoped NNReal

/-- The interface with a single query, answered by a bit. -/
abbrev bitSpec : Unit → Type := fun _ => Bool

/-- The closed package answering every query with the bit `b`. -/
def bitPkg (b : Bool) : Machine OracleSpec.empty bitSpec where
  State := Unit
  init := pure ()
  handle _ := pure b

/-- Query the package once and output its reply. -/
def askBit : ProbOracleComp bitSpec Bool :=
  ProbOracleComp.query (spec := bitSpec) ()

/-- Mapping a distribution to a constant gives the point mass at that constant. -/
private theorem pmf_map_fun_const {α β : Type} (p : PMF α) (b : β) :
    PMF.map (fun _ => b) p = PMF.pure b :=
  PMF.map_const p b

/-- An activation that returns `a` without touching the state, applied to the state `s`. -/
private theorem stateT_pure_apply {σ α : Type} {m : Type → Type} [Monad m] (a : α) (s : σ) :
    (pure a : StateT σ m α) s = pure (a, s) :=
  rfl

/-- `askBit` sees the bit of the package. -/
theorem eval_run_askBit (b : Bool) : ((bitPkg b).run askBit).eval = PMF.pure b := by
  simp [Machine.run, Machine.link, askBit, bitPkg]

/-- `askBit` tells the two packages apart with certainty. -/
theorem advantage_askBit : advantage askBit (bitPkg true) (bitPkg false) = 1 := by
  rw [advantage, Experiment.advantage, eval_run_askBit, eval_run_askBit,
    Game.advantage_pure_false]
  simp [Game.succProbability, PMF.pure_apply]

/-- Query the session `j` once and output its reply. -/
def askSession {m : ℕ} (j : Fin m) : ProbOracleComp (sessionSpec m bitSpec) Bool :=
  ProbOracleComp.query (spec := sessionSpec m bitSpec) (j, ())

/-- Every session of `bitPkg b` answers with `b`. -/
theorem eval_run_askSession {m : ℕ} (b : Bool) (j : Fin m) :
    ((parFin fun _ : Fin m => bitPkg b).run (askSession j)).eval = PMF.pure b := by
  simp [Machine.run, Machine.link, askSession, parFin_handle, bitPkg, pmf_map_fun_const]

/-- `askSession 0` tells two sessions of `bitPkg true` from two of `bitPkg false` with
certainty. -/
theorem advantage_askSession :
    advantage (askSession 0) (parFin fun _ : Fin 2 => bitPkg true)
      (parFin fun _ => bitPkg false) = 1 := by
  rw [advantage, Experiment.advantage, eval_run_askSession, eval_run_askSession,
    Game.advantage_pure_false]
  simp [Game.succProbability, PMF.pure_apply]

/-- The multi-session hybrid bound splits the advantage `1` of `askSession 0` between the
single-session distinguishers of its two hops. -/
example : (1 : ℝ≥0) ≤ ∑ j : Fin 2, advantage
    (hybridDistinguisher (fun _ => bitPkg true) (fun _ => bitPkg false) (askSession 0) j)
    (bitPkg true) (bitPkg false) :=
  advantage_askSession.symm.trans_le (advantage_parFin_le_sum _ _ _)

/-- The session package that answers `false` without consulting the global package. -/
def falsePkg : Machine bitSpec bitSpec where
  State := Unit
  init := pure ()
  handle _ := pure false

/-- Query the session `0` of two sessions sharing a global package and output its reply. -/
def askGlobal : ProbOracleComp (sessionSpec 2 bitSpec ⊕ₒ bitSpec) Bool :=
  ProbOracleComp.query (spec := sessionSpec 2 bitSpec ⊕ₒ bitSpec) (Sum.inl (0, ()))

/-- The forwarding sessions reach the global package, which answers `true`. -/
theorem eval_run_askGlobal_id :
    ((globalWorld (fun _ : Fin 2 => Machine.id bitSpec) (bitPkg true)).run askGlobal).eval =
      PMF.pure true := by
  rw [globalWorld, Machine.run_comp]
  simp [Machine.run, Machine.link, askGlobal, par, parFin, Machine.id, bitPkg, StateT.run,
    stateT_pure_apply]

/-- The sessions of `falsePkg` answer `false` without consulting the global package. -/
theorem eval_run_askGlobal_false :
    ((globalWorld (fun _ : Fin 2 => falsePkg) (bitPkg true)).run askGlobal).eval =
      PMF.pure false := by
  rw [globalWorld, Machine.run_comp]
  simp [Machine.run, Machine.link, askGlobal, par, parFin, falsePkg, bitPkg, StateT.run,
    pmf_map_fun_const, PMF.bind_const]

/-- `askGlobal` tells the forwarding sessions from the sessions of `falsePkg` with certainty. -/
theorem advantage_askGlobal :
    advantage askGlobal (globalWorld (fun _ : Fin 2 => Machine.id bitSpec) (bitPkg true))
      (globalWorld (fun _ => falsePkg) (bitPkg true)) = 1 := by
  rw [advantage, Experiment.advantage, eval_run_askGlobal_id, eval_run_askGlobal_false,
    Game.advantage_pure_false]
  simp [Game.succProbability, PMF.pure_apply]

/-- The global hybrid bound splits the advantage `1` of `askGlobal` between the single-session
distinguishers of its two hops, each of which also queries the global package directly. -/
example : (1 : ℝ≥0) ≤ ∑ j : Fin 2, advantage
    (globalDistinguisher (fun _ => Machine.id bitSpec) (fun _ => falsePkg) askGlobal j)
    (eucWorld (Machine.id bitSpec) (bitPkg true)) (eucWorld falsePkg (bitPkg true)) :=
  advantage_askGlobal.symm.trans_le (advantage_globalWorld_le_sum _ _ _ _)

end CslibFrontierTests.Crypto.SSP
