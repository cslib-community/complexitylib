/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Languages.Probabilistic.Selection
public import Complexity.Computability.Probabilistic.PPT
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import Complexity.Computability.Probabilistic.Oracle.Composition
import Complexity.Computability.Probabilistic.Repeat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Complexity.Tactic.PPT

/-!
# Strict PPT empirical selection

Candidate selection composes an efficient indexed trial with polynomial candidate and repetition
counts. The common adaptive-loop certificate charges for both indices and the running success
count. Their bounds hold on every execution, independently of the statistical accuracy theorem.

## Main results

* `Cslib.Probability.IsPPTOn.selectBest`: certify a complete indexed search.
* `Cslib.Probability.IsPPTOn.selectFrom`: charge the input list, lookup and validation.
* `Cslib.Probability.IsPPTOn.sampleBest`: compose candidate generation and selection.

## References

Adapted from the cslib `crypto` branch at `5ff69ca93402e7c947208dc56396d6d86203ccd8`.
-/

@[expose] public section

namespace Cslib.Probability

open Turing.MultiTapeTM

/-- Selecting among polynomially many efficient tests using polynomially many trials is strict
PPT. The test may capture the complete original input. -/
@[program_certificate]
theorem IsPPTOn.selectBest {α : Type} {input : α ↪ List Bool}
    {count trials : α → ℕ} {test : α → ℕ → ProbComp Bool}
    (htest : IsPPTOn (encPair input encUnary) encBool (fun pair => test pair.1 pair.2))
    (hcount : ComputableInPolyTime count input encUnary)
    (htrials : ComputableInPolyTime trials input encUnary) :
    IsPPTOn input encUnary (fun a => OracleComp.selectBest (count a) (trials a) (test a)) := by
  let stateEncoding := encPair encUnary (encPair encUnary encUnary)
  have htest' : IsPPTOn (encPair input stateEncoding) encBool
      (fun pair => test pair.1 pair.2.1) :=
    htest.preprocess (prepare := fun pair : α × (ℕ × ℕ × ℕ) => (pair.1, pair.2.1))
      (by dsimp only [stateEncoding]; fun_prop)
  have htrials' : ComputableInPolyTime (fun pair : α × (ℕ × ℕ × ℕ) => trials pair.1)
      (encPair input stateEncoding) encUnary := by fun_prop
  have hstep : IsPPTOn (encPair input stateEncoding) stateEncoding
      (fun pair => OracleComp.selectStep (trials pair.1) (test pair.1) pair.2) := by
    unfold OracleComp.selectStep
    apply (htest'.countTrue htrials').map_with
    dsimp only [OracleComp.selectUpdate, stateEncoding]
    apply ComputableInPolyTime.prod
    · exact ComputableInPolyTime.unary_succ.comp (by fun_prop)
    · have hc := ComputableInPolyTime.unary_le'
        (by fun_prop : ComputableInPolyTime
          (fun pair : (α × (ℕ × ℕ × ℕ)) × ℕ => pair.1.2.2.2)
          (encPair (encPair input (encPair encUnary (encPair encUnary encUnary))) encUnary)
          encUnary)
        (by fun_prop : ComputableInPolyTime
          (fun pair : (α × (ℕ × ℕ × ℕ)) × ℕ => pair.2)
          (encPair (encPair input (encPair encUnary (encPair encUnary encUnary))) encUnary)
          encUnary)
      simpa only [decide_eq_true_eq] using hc.ite (by fun_prop) (by fun_prop)
  have horacle := IsOraclePPTOn.iterateWith_spec' (Operation := Empty)
    (stateEncoding := stateEncoding) (initial := fun _ => (0, 0, 0))
    (step := fun a s => ProbOracleComp.sample (OracleComp.selectStep (trials a) (test a) s))
    hcount (by dsimp only [stateEncoding]; fun_prop)
    (hstep.isOraclePPTOn (Operation := Empty))
    (fun a i state => state.1 = i ∧ state.2.1 ≤ i ∧ state.2.2 ≤ trials a)
    (by simp) (fun a i state _ hstate next hnext =>
      ProbComp.selectStep_bounded (trials a) (test a) i state hstate next
        ((ProbOracleComp.support_sample _).subset hnext))
    (size := fun a => 4 * count a + trials a + 2)
    (ComputableInPolyTime.polyBounded (by fun_prop)) (by
      intro a i state hi hstate
      dsimp only [stateEncoding]
      simp only [length_encPair, encUnary_apply, List.length_replicate]
      lia)
  have hloop : IsPPTOn input stateEncoding
      (fun a => OracleComp.iterate (count a)
        (OracleComp.selectStep (trials a) (test a)) (0, 0, 0)) := by
    apply IsOraclePPTOn.isPPTOn
    simpa only [ProbOracleComp.sample, OracleComp.interpret_iterate] using horacle.1
  exact hloop.map (by dsimp only [stateEncoding]; fun_prop)

/-- Selecting from an efficiently computed list charges for the whole list and each test. -/
@[program_certificate]
theorem IsPPTOn.selectFrom {α β : Type} {input : α ↪ List Bool} {output : β ↪ List Bool}
    {values : α → List β} {trials : α → ℕ} {test : α → β → ProbComp Bool} (fallback : β)
    (hvalues : ComputableInPolyTime values input (encList output))
    (htrials : ComputableInPolyTime trials input encUnary)
    (htest : IsPPTOn (encPair input output) encBool (fun pair => test pair.1 pair.2)) :
    IsPPTOn input output
      (fun a => OracleComp.selectFrom (values a) (trials a) (test a) fallback) := by
  have hget : ComputableInPolyTime
      (fun p : α × ℕ => ((values p.1)[p.2]?).getD fallback)
      (encPair input encUnary) output := by
    simpa only [List.getD_eq_getElem?_getD, Function.comp_def] using
      (ComputableInPolyTime.listGetD (encA := output) fallback).comp
        ((hvalues.comp (ComputableInPolyTime.fst input encUnary)).prod
          (ComputableInPolyTime.snd input encUnary))
  have htest' := htest.preprocess
    ((ComputableInPolyTime.fst input encUnary).prod hget)
  have hlength := (ComputableInPolyTime.length_list output).comp hvalues
  simpa only [OracleComp.selectFrom, bind_pure_comp, Function.comp_def] using
    (IsPPTOn.selectBest htest' hlength htrials).map_with hget

/-- Sampling a polynomial candidate pool and selecting empirically is a uniform strict PPT
program. Both the generator and the validation test may capture the original input. -/
@[program_certificate]
theorem IsPPTOn.sampleBest {α β : Type} {input : α ↪ List Bool} {output : β ↪ List Bool}
    {source : α → ProbComp β} {test : α → β → ProbComp Bool} {count trials : α → ℕ}
    (fallback : β) (hsource : IsPPTOn input output source)
    (htest : IsPPTOn (encPair input output) encBool (fun pair => test pair.1 pair.2))
    (hcount : ComputableInPolyTime count input encUnary)
    (htrials : ComputableInPolyTime trials input encUnary) :
    IsPPTOn input output (fun a =>
      OracleComp.sampleBest (count a) (trials a) (source a) (test a) fallback) := by
  have htest' : IsPPTOn (encPair (encPair input (encList output)) output) encBool
      (fun p => test p.1.1 p.2) := htest.preprocess
    (prepare := fun p : (α × List β) × β => (p.1.1, p.2)) (by fun_prop)
  have hselect := IsPPTOn.selectFrom (test := fun p : α × List β => test p.1) fallback
    (ComputableInPolyTime.snd input (encList output))
    (htrials.comp (ComputableInPolyTime.fst input (encList output))) htest'
  exact (hsource.replicate hcount).bind_with hselect

end Cslib.Probability
