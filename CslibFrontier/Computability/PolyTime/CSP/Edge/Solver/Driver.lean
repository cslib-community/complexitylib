/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PolyTime.CSP.Edge.Solver.Native
import CslibFrontier.Computability.PolyTime.CSP.Edge.Solver.GuardPolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Iteration
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Length

/-!
# Native list-funded improvement driver

The full model/label/width guard is evaluated internally. False guards retain the raw initial
state; true guards derive the concrete stack invariant and full bit-storage bound. The machine
certificate therefore applies to every raw framed input, with no runtime validity premise.
The bounds and representation bookkeeping here are original.
-/

public section

namespace Cslib.Complexity.CSP.EdgeSolver.Program

open Cslib.Logic.PL Cslib.Logic.PL.CSP Turing.MultiTapeTM

private def start (input : EdgeForest.Input) : State :=
  ⟨input, [], (CSP.occurrences input.body).length + 1, none⟩
private def clock (input : EdgeForest.Input) : ℕ := 2 * (CSP.occurrences input.body).length + 3
private def loop (input : EdgeForest.Input) (state : State) : State :=
  if inputGuard input then step state else state
private def output (state : State) : Option (List Bool) :=
  if state.frames.isEmpty then state.status.elim none id else none

private theorem poly_guard : ComputableInPolyTime inputGuard EdgeForest.encInput encBool := by
  unfold inputGuard
  have hb := EdgeForest.encInput_body_deg.computableInPolyTime
  have hl := EdgeForest.encInput_labels_deg.computableInPolyTime
  have hr := EdgeAugmenting.poly_records
  have hm := computableInPolyTime_checkModel
  have hvalid := EdgeAugmenting.poly_validWith hb hl
  fun_prop

attribute [local fun_prop] poly_guard computableInPolyTime_step

private theorem poly_start : ComputableInPolyTime start EdgeForest.encInput encState := by
  unfold start
  have hb := EdgeForest.encInput_body_deg.computableInPolyTime
  have hr := EdgeAugmenting.poly_records
  have hm := encState_mk_deg.computableInPolyTime
  fun_prop

private theorem poly_clock : ComputableInPolyTime clock EdgeForest.encInput encUnary := by
  unfold clock
  have hb := EdgeForest.encInput_body_deg.computableInPolyTime
  have hr := EdgeAugmenting.poly_records
  fun_prop

private theorem poly_loop : ComputableInPolyTime
    (fun p : EdgeForest.Input × State => loop p.1 p.2)
    (encPair EdgeForest.encInput encState) encState := by
  unfold loop
  fun_prop

private theorem poly_output : ComputableInPolyTime output encState
    (encOption (encList encBool)) := by
  unfold output
  have hf := encState_frames_deg.computableInPolyTime
  have hs := encState_status_deg.computableInPolyTime
  have hj := ComputableInPolyTime.optionElimWithInput
    (body := fun (_ : State) (bits : Option (List Bool)) => bits) hs
    (ComputableInPolyTime.const none)
    (ComputableInPolyTime.snd encState (encOption (encList encBool)))
  exact (show ComputableInPolyTime (fun state : State => state.frames.isEmpty)
    encState encBool from by fun_prop).ite' hj (ComputableInPolyTime.const none)

private theorem start_good (input : EdgeForest.Input) (h : inputGuard input = true) :
    StateGood input.body (defects (EdgeAugmenting.labeling input.body input.labels)).card
      (start input) := by
  have hg := inputGuard_spec input h
  have hi := StateGood.initial input.body (EdgeAugmenting.labeling input.body input.labels)
    hg.2.2.1 hg.2.1
  simpa only [start, buffer, ← EdgeAugmenting.buffer_eq input.labels hg.2.2.2] using hi

private theorem loop_states (input : EdgeForest.Input) (n : ℕ) :
    (encState ((loop input)^[n] (start input))).length ≤
      stateBudget input.body + (encState (start input)).length := by
  by_cases hg : inputGuard input = true
  · have he : loop input = step := by funext state; simp only [loop, hg, ↓reduceIte]
    rw [he]
    have good := StateGood.iterate (inputGuard_spec input hg).1 (start_good input hg) n
    exact (good.encoded_le (inputGuard_spec input hg).1).trans (Nat.le_add_right _ _)
  · have he : loop input = id := by funext state; simp [loop, hg]
    simp only [he, Function.iterate_id, id_eq]
    omega

/-- The complete guarded one-improvement solver is ordinary native polynomial-time on all
raw explicit-table inputs. The proof constructs its full model checks, actual stack bound and
list-funded unary clock internally; no optimizer, rank or runtime certificate is input. -/
theorem computableInPolyTime_safeImprove : ComputableInPolyTime safeImprove EdgeForest.encInput
    (encOption (encList encBool)) := by
  have hb := computableInPolyTime_stateBudget.comp
    EdgeForest.encInput_body_deg.computableInPolyTime
  have hbudget : PolyBounded (fun input => (EdgeForest.encInput input).length)
      (fun input => stateBudget input.body + (encState (start input)).length) := by
    have hb' : PolyBounded (fun input => (EdgeForest.encInput input).length)
        (fun input => stateBudget input.body) := by
      simpa only [encUnary_apply, List.length_replicate, Function.comp_def] using
        hb.polyBounded_length
    exact hb'.add poly_start.polyBounded_length
  have hiter : ComputableInPolyTime (fun input => (loop input)^[clock input] (start input))
      EdgeForest.encInput encState := (ComputableInPolyTime.iterateWith
      (ComputableInPolyTime.id' (encIn := EdgeForest.encInput)) poly_clock
      poly_start poly_loop hbudget (fun input n _ => loop_states input n))
  have hresult := poly_guard.ite' (poly_output.comp hiter) (ComputableInPolyTime.const none)
  apply hresult.of_enc_eq
  intro input
  by_cases hg : inputGuard input = true
  · have he : loop input = step := by funext state; simp only [loop, hg, ↓reduceIte]
    simp only [safeImprove, hg, ↓reduceIte, Function.comp_def, he]
    unfold improve output clock start
    generalize step^[2 * (CSP.occurrences input.body).length + 3]
      (⟨input, [], (CSP.occurrences input.body).length + 1, none⟩ : State) = final
    dsimp only
    apply congrArg (encOption (encList encBool))
    by_cases hf : final.frames.isEmpty = true
    · simp only [hf, ↓reduceIte]
      cases final.status <;> rfl
    · simp only [hf, Bool.false_eq_true, ↓reduceIte]
  · simp [safeImprove, hg]

end Cslib.Complexity.CSP.EdgeSolver.Program
