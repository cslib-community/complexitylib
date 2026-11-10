/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.FineGrained.IndependentDominationWitness

/-!
# Native execution of ascending minimum independent domination

The native iterator retains the original graph, next unary size and first successful binary
value/word. `trajectory` identifies this actual machine traversal with the approved recursive
search. `certificate` charges all solver calls, retained frames, loop control and output.
The polynomial workspace and sharp closed-form time bounds are separate obligations; the
exact trajectory-max resource certificate here does not assume those bounds. This implements
the native-execution clause toward [ChenJiangZhu2027], Corollary 7.4 / Appendix D.5
(PDF pp.26,37), without claiming the full quantitative endpoint.

## Main results

* `trajectory`, `execute_eq_run`: actual iterator/search correspondence.
* `certificate`: finite native machine certificate for the actual ascending search.
* `exists_native_optimal_search`: actual production machine and attained optimum correctness.
-/

public section

namespace Cslib.Logic.PL.IndependentDominationInterval.Signed.Witness.Minimum

open Turing.MultiTapeTM Cslib.GenericRAM

/-- Binary minimum value, framed before the original raw vertex word. -/
abbrev encValue : (ℕ × List Bool) ↪ List Bool := encPair encNat encBits
/-- Standard option tag, then the framed binary value and raw original vertex word. -/
abbrev encOutput : Option (ℕ × List Bool) ↪ List Bool := encOption encValue
/-- Original graph, unary next size, and retained first successful value/word. -/
abbrev State := IndependentDomination.Input × ℕ × Option (ℕ × List Bool)
/-- Frame the original graph, then the unary next size, followed by tagged binary output. -/
abbrev encState : State ↪ List Bool :=
  encPair IndependentDomination.encInput (encPair encUnary encOutput)
/-- Original graph retained by every round. -/
@[expose] def original (s : State) : IndependentDomination.Input := s.1
/-- Next exact cardinality to test. -/
@[expose] def next : State → ℕ | (_, j, _) => j
/-- Retained first successful original word and its value. -/
@[expose] def stored : State → Option (ℕ × List Bool) | (_, _, out) => out
/-- Actual signed binary exact-size query, with no optimum supplied. -/
@[expose] def request (s : State) : Signed.Input := (original s, next s, next s)
/-- Frame the full retained state, followed by the actual optional solver word. -/
abbrev encFinish : (State × TwoBoundary.BinaryFrontend.Witness.Output) ↪ List Bool :=
  encPair encState TwoBoundary.BinaryFrontend.Witness.encOutput
/-- Retain the first success and advance the unary size. The solver is still charged on later
rounds; these extra polynomially many calls change neither the returned minimum nor word. -/
@[expose] def finish (p : State × TwoBoundary.BinaryFrontend.Witness.Output) : State :=
  let (s, bits) := p
  (original s, next s + 1, if (stored s).isSome then stored s else
    bits.map (fun word => (next s, word)))
/-- One actual solver call and retained-output update. -/
@[expose] def step (solver : Signed.Input → TwoBoundary.BinaryFrontend.Witness.Output)
    (s : State) : State := finish (s, solver (request s))
/-- Original graph with zero next size and no retained result. -/
@[expose] def initial (g : IndependentDomination.Input) : State := (g, 0, none)
/-- Test each possible original cardinality, including zero. -/
@[expose] def rounds (g : IndependentDomination.Input) : ℕ := IndependentDomination.order g + 1
/-- Actual bounded iterator followed by binary value/vertex-word output. -/
@[expose] def execute (solver : Signed.Input → TwoBoundary.BinaryFrontend.Witness.Output)
    (g : IndependentDomination.Input) : Option (ℕ × List Bool) :=
  stored ((step solver)^[rounds g] (initial g))

/-- Full actual state, with the same first success as the approved recursive search. -/
theorem trajectory (solver : Signed.Input → TwoBoundary.BinaryFrontend.Witness.Output)
    (g : IndependentDomination.Input) (j : ℕ) :
    (step solver)^[j + 1] (initial g) = (g, j + 1, seek solver g j) := by
  induction j with
  | zero => simp [step, finish, request, initial, original, next, stored, seek]
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih]
    cases h : seek solver g j <;>
      simp [step, finish, request, original, next, stored, seek, h]

/-- The iterator computes exactly the already proved minimum-value/actual-word search. -/
theorem execute_eq_run (solver : Signed.Input → TwoBoundary.BinaryFrontend.Witness.Output)
    (g : IndependentDomination.Input) : execute solver g = run solver g := by
  rw [execute, rounds, trajectory]
  rfl

private theorem request_polytime : ComputableInPolyTime request encState Signed.encInput := by
  have hn : ComputableInPolyTime next encState encUnary := by unfold next encState; fun_prop
  have hb := ComputableInPolyTime.intBin_natCast.comp
    (ComputableInPolyTime.unary_to_binary.comp hn)
  have hg : ComputableInPolyTime original encState IndependentDomination.encInput := by
    unfold original encState; fun_prop
  exact hg.prod (hb.prod hb)

private theorem finish_polytime : ComputableInPolyTime finish encFinish encState := by
  have hm : ComputableInPolyTime
      (fun p : State × TwoBoundary.BinaryFrontend.Witness.Output =>
        p.2.map (fun word => (next p.1, word))) encFinish encOutput := by
    unfold encFinish encOutput
    apply ComputableInPolyTime.optionMapWithInput (by fun_prop)
    have hn : ComputableInPolyTime (fun p : (State ×
        TwoBoundary.BinaryFrontend.Witness.Output) × List Bool => next p.1.1)
        (encPair encFinish encBits) encUnary := by unfold next encFinish encState; fun_prop
    exact (ComputableInPolyTime.unary_to_binary.comp hn).prod (by fun_prop)
  unfold finish
  have hs : ComputableInPolyTime (fun p : State × TwoBoundary.BinaryFrontend.Witness.Output =>
      stored p.1) encFinish encOutput := by unfold stored encFinish encState; fun_prop
  have ho := hs.optionIsSome.ite' hs hm
  have hg : ComputableInPolyTime (fun p : State × TwoBoundary.BinaryFrontend.Witness.Output =>
      original p.1) encFinish IndependentDomination.encInput := by
    unfold original encFinish encState; fun_prop
  have hn : ComputableInPolyTime (fun p : State × TwoBoundary.BinaryFrontend.Witness.Output =>
      next p.1 + 1) encFinish encUnary := by unfold next encFinish encState; fun_prop
  exact hg.prod (hn.prod ho)

private theorem initial_polytime : ComputableInPolyTime initial IndependentDomination.encInput
    encState := by unfold initial encState encOutput encValue; fun_prop

private theorem rounds_polytime : ComputableInPolyTime rounds IndependentDomination.encInput
    encNat := by
  have hu : ComputableInPolyTime rounds IndependentDomination.encInput encUnary := by
    unfold rounds IndependentDomination.order IndependentDomination.encInput; fun_prop
  exact ComputableInPolyTime.unary_to_binary.comp hu

private theorem stored_polytime : ComputableInPolyTime stored encState encOutput := by
  unfold stored encState; fun_prop

/-- Derive an actual finite native machine for the approved search from the solver's actual
machine, charging trajectory maxima via the native iterator calculus. No desired resource
bound is a premise. Closed polynomial-space/sharp-time estimates still need to be proved. -/
noncomputable def certificate
    (solver : Signed.Input → TwoBoundary.BinaryFrontend.Witness.Output)
    (cs : NativeCertificate solver Signed.encInput TwoBoundary.BinaryFrontend.Witness.encOutput) :
    NativeCertificate (run solver) IndependentDomination.encInput encOutput :=
  let cq := NativeCertificate.ofPolyTime request_polytime
  let ci : NativeCertificate (fun s : State => s) encState encState :=
    NativeCertificate.linear (ComputableInO.of_eq fun _ => rfl)
  let cf := NativeCertificate.ofPolyTime finish_polytime
  let cb : NativeCertificate (step solver) encState encState :=
    (cf.comp (ci.prod (cs.comp cq))).congr (fun _ => rfl)
  let loop := NativeCertificate.iterate (NativeCertificate.ofPolyTime rounds_polytime)
    (NativeCertificate.ofPolyTime initial_polytime) cb
  ((NativeCertificate.ofPolyTime stored_polytime).comp loop).congr
    (fun g => execute_eq_run solver g)

open Classical in
/-- Instantiate the proved production size solver, its native machine and its correctness.
The resulting finite machine returns the attained global minimum and original vertex word;
its exact iterator resources still require closed polynomial/sharp estimates. -/
theorem exists_native_optimal_search :
    ∃ optimize : IndependentDomination.Input → Option (ℕ × List Bool),
      ∃ _cs : NativeCertificate optimize IndependentDomination.encInput encOutput,
      ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
        ∃ k bits, optimize (IndependentDomination.ofGraph G) = some (k, bits) ∧
          bits.length = n ∧ Feasible G k k (fun u => bits.getD u.val false) ∧
            ∀ σ : Fin n → Bool, G.IsIndepSet {u | σ u = true} →
              G.IsDominatingSet {u | σ u = true} → k ≤ Cslib.BitString.weight σ := by
  obtain ⟨solver, cp, C, e, A, hs, h⟩ := exists_solver_realEta_certificate
  exact ⟨run solver, certificate solver cp,
    run_attained solver (fun G _ lo hi => (h G lo hi).1) (fun G _ lo hi => (h G lo hi).2.1)⟩

end Cslib.Logic.PL.IndependentDominationInterval.Signed.Witness.Minimum
