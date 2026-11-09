/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PolyTime.CSP.Edge.Solver.Program
import CslibFrontier.Computability.PolyTime.CSP.Edge.Solver.LiftingAgreement
import Mathlib.Tactic.SplitIfs

/-!
# Exact agreement of the finite improvement stack

The stack implements the recursive one-improvement program, rather than a recursive child
optimizer. The explicit unary budget gives agreement on all raw states, independently of any
edge or width hypotheses. A decreasing operational potential pays for every descent, terminal
search and lift. The mathematical contraction measure supplies enough budget on valid models.
-/

public section

namespace Cslib.Complexity.CSP.EdgeSolver.Program

open Cslib.Logic.PL Cslib.Logic.PL.CSP

/-- Recursive view of the finite program. It recurses once per blossom and returns immediately
after one lift. Depth exhaustion is defined on arbitrary malformed raw states as well. -/
@[expose] def recurse : ℕ → EdgeForest.Input → Option (List Bool)
  | 0, _ => none
  | depth + 1, input =>
    match EdgeForest.run input with
    | none => none
    | some (.inl _) => none
    | some (.inr (.inl event)) => augment input event
    | some (.inr (.inr event)) =>
      match push input event with
      | none => none
      | some (frame, child) => (recurse depth child).bind (lift frame)

private def resume : List Frame → Option (List Bool) → Option (List Bool)
  | [], result => result
  | frame :: frames, result => resume frames (result.bind (lift frame))

private theorem resume_none (frames : List Frame) : resume frames none = none := by
  induction frames with
  | nil => rfl
  | cons frame frames ih => exact ih

private def evaluate (state : State) : Option (List Bool) :=
  resume state.frames (state.status.getD (recurse state.budget state.current))

private def potential (state : State) : ℕ :=
  if state.status.isSome then state.frames.length
  else 2 * state.budget + state.frames.length + 1

private theorem evaluate_step (state : State) : evaluate (step state) = evaluate state := by
  rcases state with ⟨input, frames, budget, status⟩
  cases status with
  | some result =>
    cases result with
    | none => simp [step, evaluate, resume_none]
    | some bits =>
      cases frames with
      | nil => rfl
      | cons frame frames => rfl
  | none =>
    cases budget with
    | zero => simp [step, evaluate, recurse, resume_none]
    | succ budget =>
      cases hr : EdgeForest.run input with
      | none => simp [step, evaluate, recurse, hr, resume_none]
      | some result =>
        rcases result with log | (event | event)
        · simp [step, evaluate, recurse, hr, resume_none]
        · simp [step, evaluate, recurse, hr]
        · cases hp : push input event with
          | none => simp [step, evaluate, recurse, hr, hp, resume_none]
          | some pair =>
            rcases pair with ⟨frame, child⟩
            simp [step, evaluate, recurse, hr, hp, resume]

private theorem potential_step (state : State) : potential (step state) ≤ potential state - 1 := by
  rcases state with ⟨input, frames, budget, status⟩
  cases status with
  | some result =>
    cases result with
    | none => simp [step, potential]
    | some bits =>
      cases frames <;> simp [step, potential]
  | none =>
    cases budget with
    | zero => simp [step, potential]
    | succ budget =>
      cases hr : EdgeForest.run input with
      | none => simp [step, potential, hr]
      | some result =>
        rcases result with log | (event | event)
        · simp [step, potential, hr]
        · simp [step, potential, hr]
        · cases hp : push input event with
          | none => simp [step, potential, hr, hp]
          | some pair =>
            rcases pair with ⟨frame, child⟩
            simp only [step, hr, hp, potential, Option.isSome_none, Bool.false_eq_true,
              ↓reduceIte, List.length_cons]
            omega

private theorem potential_iterate (state : State) (n : ℕ) :
    potential (step^[n] state) ≤ potential state - n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    have hs := potential_step (step^[n] state)
    omega

private theorem evaluate_iterate (state : State) (n : ℕ) :
    evaluate (step^[n] state) = evaluate state := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', evaluate_step, ih]

/-- The finite native-search stack agrees exactly with the one-child recursive program on
every raw input, including malformed widths. Its entire operational clock is list-funded. -/
theorem improve_eq_recurse (input : EdgeForest.Input) :
    improve input = recurse ((CSP.occurrences input.body).length + 1) input := by
  let initial : State := ⟨input, [], (CSP.occurrences input.body).length + 1, none⟩
  let final := step^[2 * (CSP.occurrences input.body).length + 3] initial
  have hp : potential final = 0 := by
    have hb := potential_iterate initial (2 * (CSP.occurrences input.body).length + 3)
    simp only [initial, potential, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
      List.length_nil] at hb
    change potential final ≤ _ at hb
    omega
  have he := evaluate_iterate initial (2 * (CSP.occurrences input.body).length + 3)
  change evaluate final = recurse ((CSP.occurrences input.body).length + 1) input at he
  have hframes : final.frames = [] := by
    have hb : final.frames.length ≤ potential final := by
      unfold potential
      split <;> omega
    simpa only [List.length_eq_zero_iff] using (show final.frames.length = 0 by omega)
  have hstatus : final.status.isSome = true := by
    by_contra hn
    simp only [potential, hn, ↓reduceIte] at hp
    omega
  change (if final.frames.isEmpty then final.status.join else none) = _
  rw [hframes]
  cases hs : final.status with
  | none => simp [hs] at hstatus
  | some result => simpa only [evaluate, hframes, hs, Option.getD_some, resume,
      List.isEmpty_nil, ↓reduceIte, Option.join_some] using he

/-- One frame executes the actual arbitrary-comparison lifting construction exactly. -/
theorem lift_eq {F : CSP Table ℕ} (f : OccurrenceLabeling F Bool) (w : Walk F)
    (g : OccurrenceLabeling (Blossom.contract f (Blossom.internal w)) Bool) :
    lift ⟨⟨F, buffer f⟩, EdgeAugmenting.code w⟩ (buffer g) =
      (Blossom.liftComparison f w g).map buffer := by
  simpa only [lift, buffer] using NativeLifting.liftComparison_code f w g

/-- Finite preparation and contraction agree exactly with the complete source constructor. -/
theorem push_code (F : CSP Table ℕ) (f : OccurrenceLabeling F Bool) (m : Forest.Meeting F) :
    push ⟨F, buffer f⟩ (EdgeForest.codeMeeting m) = m.blossomData.map (fun b =>
      let prepared := b.prepare.flip f
      let vs := Blossom.internal b.cycle
      (⟨⟨F, buffer prepared⟩, EdgeAugmenting.code b.cycle⟩,
        ⟨Blossom.contract prepared vs, buffer (Blossom.reference prepared vs)⟩)) := by
  cases hb : m.blossomData with
  | none => simp [push, NativeForest.blossom_code, hb]
  | some b =>
    have hflip := NativeWalk.flip_code f b.prepare
    have hi := NativeWalk.internal_code b.cycle
    simp only [push, buffer, NativeForest.blossom_code, hb, hflip, hi,
      Contraction.contract_eq, Contraction.referenceRows_eq, Contraction.flatten_referenceRows,
      Option.map_some]
    rw [hflip, hi, EdgeAugmenting.labeling_map]

/-- The finite augmentation returns the exact actual source walk's positional flip. -/
theorem augment_code (F : CSP Table ℕ) (f : OccurrenceLabeling F Bool) (m : Forest.Meeting F) :
    augment ⟨F, buffer f⟩ (EdgeForest.codeMeeting m) = some (buffer (m.walk.flip f)) := by
  simp [augment, NativeForest.meetingWalk_code, NativeWalk.flip_code]

/-- Exact source agreement of the recursive finite-buffer program at every depth.
No edge-instance, valid-labeling or evenness premise is needed for this representation bridge. -/
theorem recurse_eq (depth : ℕ) (F : CSP Table ℕ) (f : OccurrenceLabeling F Bool) :
    recurse depth ⟨F, buffer f⟩ = (Solver.improve depth F f).map buffer := by
  induction depth generalizing F with
  | zero => rfl
  | succ depth ih =>
    have hr := EdgeForest.run_eq (⟨F, buffer f⟩ : EdgeForest.Input) (List.length_map f)
    simp only [buffer, EdgeAugmenting.labeling_map] at hr
    cases hs : Forest.search Table.sem f with
    | exhausted log => simp [recurse, hr, hs, EdgeForest.code, Solver.improve]
    | augment m =>
      simp [recurse, hr, hs, EdgeForest.code, augment,
        NativeForest.meetingWalk_code, NativeWalk.flip_code, Solver.improve]
    | blossom m =>
      cases hb : m.blossomData with
      | none =>
        simp [recurse, hr, hs, EdgeForest.code, push,
          NativeForest.blossom_code, hb, Solver.improve]
      | some b =>
        simp only [recurse, hr, hs, EdgeForest.code, push,
          NativeForest.blossom_code, hb, Option.bind_eq_bind, Option.bind_some,
          Solver.improve, Option.map_some, NativeWalk.internal_code]
        simp only [buffer, NativeWalk.flip_code, Contraction.contract_eq,
          Contraction.referenceRows_eq, EdgeAugmenting.labeling_map,
          Contraction.flatten_referenceRows]
        rw [ih]
        cases hc : Solver.improve depth (Blossom.contract (b.prepare.flip f)
            (Blossom.internal b.cycle)) (Blossom.reference (b.prepare.flip f)
              (Blossom.internal b.cycle)) with
        | none => rfl
        | some g => simp only [Option.map_some, Option.bind_some, lift_eq]

/-- Exact stack/source agreement on every exact-width raw input. The buffer round trip is
the shared `EdgeAugmenting.buffer_eq` API, available through an ordinary `Buffer` import. -/
theorem improve_eq (input : EdgeForest.Input)
    (hw : input.labels.length = (incidenceList input.body).length) :
    improve input = (Solver.improve ((CSP.occurrences input.body).length + 1) input.body
      (EdgeAugmenting.labeling input.body input.labels)).map buffer := by
  rw [improve_eq_recurse]
  have he := recurse_eq ((CSP.occurrences input.body).length + 1) input.body
    (EdgeAugmenting.labeling input.body input.labels)
  simpa only [buffer, ← EdgeAugmenting.buffer_eq input.labels hw] using he

/-- The actual occurrence list funds more than the concrete contraction measure on every
edge instance, including nullaries and contractions that leave the variable count unchanged. -/
theorem contractionMeasure_lt_clock (F : CSP Table ℕ) (hF : EdgeInstance F) :
    F.contractionMeasure < (CSP.occurrences F).length + 1 := by
  have he : (CSP.occurrences F).length = F.vars.length := by
    rw [CSP.length_occurrences]
    simp [vars, List.length_flatMap]
  have := hF.length_vars_eq_two_mul_numVars
  unfold contractionMeasure
  rw [he]
  omega

/-- On the actual model the list-funded program gives exactly the deterministic mathematical
improvement with its canonical sufficient contraction budget. -/
theorem improve_eq_source (F : CSP Table ℕ) (f : OccurrenceLabeling F Bool)
    (hF : EdgeInstance F) (hf : ValidLabeling Table.sem f)
    (hM : EdgeInstance.EvenConstraints Table.sem F) :
    improve ⟨F, buffer f⟩ = (Solver.improve (F.contractionMeasure + 1) F f).map buffer := by
  rw [improve_eq ⟨F, buffer f⟩ (List.length_map f), EdgeAugmenting.labeling_map]
  rw [Solver.improve_depth_eq F f hF hf hM
    ((CSP.occurrences F).length + 1) (F.contractionMeasure + 1)
    (contractionMeasure_lt_clock F hF) (by omega)]

end Cslib.Complexity.CSP.EdgeSolver.Program
