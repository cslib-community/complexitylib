/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Machine.OutputPrefix
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.Closed
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.WordsCfg

/-!
# Writing a prefix before a probabilistic computation

A deterministic preparation restores the input head and blank work tapes after writing a prefix.
Shared-tape sequencing then runs the probabilistic source on its original input. Both phases
actually halt within the sum of their bounds; every instruction of preparation is charged.

## Main results

* `Turing.MultiTapePTM.eval_runClosedConfigFrom_seq_prependOutput`: retain a prepared prefix.
* `Turing.MultiTapePTM.seq_prependOutput_halted`: add the two actual halting bounds.

## References

Adapted from Computability/Probabilistic/Realization/Composition.lean on the cslib `crypto`
branch at `5ff69ca93402e7c947208dc56396d6d86203ccd8`, using the shared sequencing compiler.
-/

public section

namespace Turing.MultiTapePTM

open Cslib MultiTapeMachine

variable {k : ℕ} {Symbol State State₀ State₁ : Type} {input : List Symbol}

/-- An unreadable output prefix preserves the entire closed execution program. -/
theorem runClosedConfigFrom_prependOutput (machine : MultiTapePTM k Symbol State)
    (fuel : ℕ) (cfg : Config k Symbol State Empty input) (pre : List Symbol) :
    machine.runClosedConfigFrom fuel (cfg.prependOutput pre) =
      (fun final => final.prependOutput pre) <$> machine.runClosedConfigFrom fuel cfg :=
  MultiTapeMachine.runConfigFrom_prependOutput machine _ _ fuel cfg pre

variable (prepare : MultiTapeTM k Symbol State₀) (source : MultiTapePTM k Symbol State₁)
  (input pre : List Symbol) (prepareTime runTime : ℕ)
  (hprepare : prepare.runFrom (prepare.initCfg input) prepareTime =
    wordsCfg input none (fun _ => []) pre)
  (hsource : ∀ final ∈ (ProbComp.eval
    (source.runClosedConfigFrom runTime (source.initialConfig input))).support,
    final.tapes.state = none)

include hprepare hsource

/-- A workspace-restoring preparation retains the prefix and the source distribution. -/
theorem eval_runClosedConfigFrom_seq_prependOutput :
    ProbComp.eval (((ofDeterministic prepare).seq source).runClosedConfigFrom
      (prepareTime + runTime) (((ofDeterministic prepare).seq source).initialConfig input)) =
      (ProbComp.eval (source.runClosedConfigFrom runTime (source.initialConfig input))).map
        (fun final => Sequential.right (final.prependOutput pre)) := by
  let cfg : Config k Symbol State₀ Empty input := (ofDeterministic prepare).initialConfig input
  let ready : Config k Symbol State₀ Empty input :=
    { tapes := wordsCfg input none (fun _ => []) pre }
  have hfirst : ProbComp.eval ((ofDeterministic prepare).runClosedConfigFrom prepareTime cfg) =
      PMF.pure ready := by
    rw [eval_runClosedConfigFrom_ofDeterministic]
    change PMF.pure ({ tapes := prepare.runFrom (prepare.initCfg input) prepareTime } :
      Config k Symbol State₀ Empty input) = _
    rw [hprepare]
  have hstart : Sequential.start source ready = (source.initialConfig input).prependOutput pre := by
    simp [Sequential.start, ready, initialConfig, Config.prependOutput,
      Cfg.prependOutput, wordsCfg, Cfg.withState]
  have hsecond : ∀ final ∈ (ProbComp.eval
      (source.runClosedConfigFrom runTime (Sequential.start source ready))).support,
      final.tapes.state = none := by
    intro final hfinal
    rw [hstart, runClosedConfigFrom_prependOutput, ProbComp.eval_map] at hfinal
    obtain ⟨original, horiginal, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hfinal
    exact hsource original horiginal
  change ProbComp.eval (((ofDeterministic prepare).seq source).runClosedConfigFrom
    _ (Sequential.left source cfg)) = _
  rw [eval_runClosedConfigFrom_seq _ _ _ prepareTime runTime
    (by simp [hfirst, ready]) (by simpa [hfirst] using hsecond),
    Probability.PMF.monad_bind_eq_bind, hfirst, PMF.pure_bind, hstart,
    runClosedConfigFrom_prependOutput, ProbComp.eval_map,
    PMF.map_comp]
  rfl

/-- The prepared-prefix computation actually halts within the sum of the phase bounds. -/
theorem seq_prependOutput_halted :
    ∀ final ∈ (ProbComp.eval (((ofDeterministic prepare).seq source).runClosedConfigFrom
      (prepareTime + runTime)
      (((ofDeterministic prepare).seq source).initialConfig input))).support,
      final.tapes.state = none := by
  intro final hfinal
  rw [eval_runClosedConfigFrom_seq_prependOutput prepare source input pre prepareTime runTime
    hprepare hsource] at hfinal
  obtain ⟨original, horiginal, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hfinal
  change original.tapes.state.map Sum.inr = none
  rw [hsource original horiginal]
  rfl

/-- The final output consists of the prepared prefix followed by the sampled source output. -/
theorem eval_seq_prependOutput :
    ProbComp.eval (((ofDeterministic prepare).seq source).runClosed
      (prepareTime + runTime) input) =
      (ProbComp.eval (source.runClosed runTime input)).map (pre ++ ·) := by
  simp only [runClosed_eq_map, ProbComp.eval_map,
    eval_runClosedConfigFrom_seq_prependOutput prepare source input pre prepareTime runTime
      hprepare hsource, PMF.map_comp]
  rfl

end Turing.MultiTapePTM
