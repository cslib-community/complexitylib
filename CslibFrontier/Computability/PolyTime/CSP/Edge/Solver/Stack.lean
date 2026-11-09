/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PolyTime.CSP.Edge.Solver.Agreement
public import CslibFrontier.Computability.PolyTime.CSP.Edge.Solver.Size

/-!
# Actual contraction histories of the running solver stack

The stored baseline labelings all have the original defect count: preparation and honest
reference contraction preserve that count. An improving status has exactly two fewer defects.
The stack links each current body to its actual prepared parent, so an arbitrary changed-outside
comparison is in the domain of the existing lifting theorem. All invariants below are derived
from the original guarded model and actual execution, never supplied as runtime certificates.
This bookkeeping is original.
-/

public section

namespace Cslib.Complexity.CSP.EdgeSolver.Program

open Cslib.Logic.PL Cslib.Logic.PL.CSP

/-- An actual valid baseline in the original problem's concrete contraction history. -/
@[expose] def InputGood (F : CSP Table ℕ) (D : ℕ) (input : EdgeForest.Input) : Prop :=
  ∃ k, ∃ f : OccurrenceLabeling input.body Bool,
    Size.Chain F k input.body ∧ ValidLabeling Table.sem f ∧
      EdgeInstance.EvenConstraints Table.sem input.body ∧ input.labels = buffer f ∧
        (defects f).card = D

/-- Actual parent/child body links of a solver stack. Relabeling the current baseline is
allowed; every frame still records its own exact prepared labeling and cycle. -/
inductive Stack (F : CSP Table ℕ) (D : ℕ) : EdgeForest.Input → List Frame → Prop where
  /-- A current problem without stored parents. -/
  | nil {input : EdgeForest.Input} (good : InputGood F D input) : Stack F D input []
  /-- An actual contracted child over an actual stored prepared parent. -/
  | cons {G : CSP Table ℕ} (f : OccurrenceLabeling G Bool) (w : Walk G)
      (blossom : w.IsBlossom Table.sem f) {frames : List Frame}
      (parents : Stack F D ⟨G, buffer f⟩ frames) (bits : List Bool)
      (good : InputGood F D ⟨Blossom.contract f (Blossom.internal w), bits⟩) :
      Stack F D ⟨Blossom.contract f (Blossom.internal w), bits⟩
        (⟨⟨G, buffer f⟩, EdgeAugmenting.code w⟩ :: frames)

/-- The current baseline is a valid actual member of the contraction history. -/
theorem Stack.current {F : CSP Table ℕ} {D : ℕ} {input : EdgeForest.Input}
    {frames : List Frame} (h : Stack F D input frames) : InputGood F D input := by
  cases h with
  | nil good => exact good
  | cons f w blossom parents bits good => exact good

/-- Preparation changes only the current baseline. It preserves the actual parent/body links. -/
theorem Stack.relabel {F : CSP Table ℕ} {D : ℕ} {input : EdgeForest.Input}
    {frames : List Frame} (h : Stack F D input frames)
    (f : OccurrenceLabeling input.body Bool) (hf : ValidLabeling Table.sem f)
    (hd : (defects f).card = D) : Stack F D ⟨input.body, buffer f⟩ frames := by
  obtain ⟨k, baseline, chain, _, even, _, _⟩ := h.current
  have good : InputGood F D ⟨input.body, buffer f⟩ := ⟨k, f, chain, hf, even, rfl, hd⟩
  cases h with
  | nil _ => exact .nil good
  | cons parent w blossom parents bits _ => exact .cons parent w blossom parents _ good

/-- A returned finite comparison is valid and removes exactly two original baseline defects. -/
@[expose] def StatusGood (D : ℕ) (input : EdgeForest.Input) : Option (Option (List Bool)) → Prop
  | some (some bits) => ∃ g : OccurrenceLabeling input.body Bool,
      bits = buffer g ∧ ValidLabeling Table.sem g ∧ (defects g).card + 2 = D
  | _ => True

/-- The stack's mathematical history, returned-buffer invariant and actual unary clock bound. -/
structure StateGood (F : CSP Table ℕ) (D : ℕ) (state : State) : Prop where
  /-- Every stored frame is an actual prepared parent of the next body. -/
  stack : Stack F D state.current state.frames
  /-- Improving status bits are an actual valid comparison with two fewer original defects. -/
  result : StatusGood D state.current state.status
  /-- Every pushed frame spends one actual original occurrence-funded depth unit. -/
  clock : state.frames.length + state.budget ≤ F.vars.length + 1

/-- Recover the actual baseline properties when an input is materialized from a labeling. -/
theorem InputGood.materialized {F G : CSP Table ℕ} {D : ℕ} (f : OccurrenceLabeling G Bool)
    (h : InputGood F D ⟨G, buffer f⟩) :
    ∃ k, Size.Chain F k G ∧ ValidLabeling Table.sem f ∧
      EdgeInstance.EvenConstraints Table.sem G ∧ (defects f).card = D := by
  obtain ⟨k, g, chain, valid, even, heq, count⟩ := h
  have he : f = g := by
    have hh := congrArg (EdgeAugmenting.labeling G) heq
    simpa only [buffer, EdgeAugmenting.labeling_map] using hh
  cases he
  exact ⟨k, chain, valid, even, count⟩

/-- Every real stack transition preserves its actual contraction history, valid comparisons
and occurrence-funded clock. All model obligations come from fresh source search and lifting. -/
theorem StateGood.step {F : CSP Table ℕ} {D : ℕ} {state : State}
    (hF : EdgeInstance F) (h : StateGood F D state) : StateGood F D (step state) := by
  rcases state with ⟨input, frames, budget, status⟩
  have hclock : frames.length + budget ≤ F.vars.length + 1 := h.clock
  cases status with
  | some result =>
    cases result with
    | none =>
      change StateGood F D ⟨input, [], budget, some none⟩
      refine ⟨.nil h.stack.current, trivial, ?_⟩
      have := hclock
      dsimp only at this ⊢
      simp only [List.length_nil]
      omega
    | some bits =>
      cases hstack : h.stack with
      | nil good => simpa only [Program.step] using h
      | @cons G f w blossom frames parents oldbits good =>
        obtain ⟨k, chain, valid, even, count⟩ := InputGood.materialized f parents.current
        obtain ⟨g, hg, hv, hn⟩ := h.result
        have href := Blossom.card_defects_reference_blossom (chain.edge hF) blossom
        obtain ⟨out, ho, hout, hcount⟩ := Blossom.liftComparison_spec
          (chain.edge hF) blossom valid even g hv (by omega)
        change StateGood F D
          ⟨⟨G, buffer f⟩, frames, budget,
            some (lift ⟨⟨G, buffer f⟩, EdgeAugmenting.code w⟩ bits)⟩
        rw [hg, lift_eq, ho]
        simp only [Option.map_some]
        refine ⟨parents, ⟨out, rfl, hout, by omega⟩, ?_⟩
        have := hclock
        dsimp only at this ⊢
        simp only [List.length_cons] at this
        omega
  | none =>
    cases budget with
    | zero =>
      change StateGood F D ⟨input, [], 0, some none⟩
      exact ⟨.nil h.stack.current, trivial, by simp⟩
    | succ budget =>
      rcases input with ⟨G, bits⟩
      obtain ⟨k, f, chain, valid, even, hbits, count⟩ := h.stack.current
      dsimp only at f chain valid even hbits count
      subst bits
      have hr := EdgeForest.run_eq (⟨G, buffer f⟩ : EdgeForest.Input) (List.length_map f)
      simp only [buffer, EdgeAugmenting.labeling_map] at hr
      have edge := chain.edge hF
      cases hs : Forest.search Table.sem f with
      | exhausted es =>
        have hh : StateGood F D ⟨⟨G, buffer f⟩, [], budget, some none⟩ :=
          ⟨.nil h.stack.current, trivial, by dsimp only; simp only [List.length_nil]; omega⟩
        simpa only [Program.step, hr, hs, EdgeForest.code] using hh
      | augment m =>
        have ha := (Forest.search_augment_correct Table.sem f edge valid even hs).2
        have hh : StateGood F D
            ⟨⟨G, buffer f⟩, frames, budget, some (some (buffer (m.walk.flip f)))⟩ :=
          ⟨h.stack, ⟨m.walk.flip f, rfl, ha.1, by omega⟩, by dsimp only; omega⟩
        simpa only [Program.step, hr, hs, EdgeForest.code, augment_code] using hh
      | blossom m =>
        obtain ⟨b, hb, blossom, preparedValid, preparedCount⟩ :=
          Forest.search_blossom_correct Table.sem f edge valid even hs
        let prepared := b.prepare.flip f
        let vs := Blossom.internal b.cycle
        have nonempty := Blossom.touched_ne_nil b.cycle blossom.steps_ne_nil
        have newparents := h.stack.relabel prepared preparedValid (preparedCount.trans count)
        have childGood : InputGood F D
            ⟨Blossom.contract prepared vs, buffer (Blossom.reference prepared vs)⟩ := by
          refine ⟨k + 1, Blossom.reference prepared vs,
            .step chain prepared b.cycle preparedValid blossom,
            Blossom.valid_reference preparedValid vs nonempty,
            Blossom.even_contract preparedValid even vs nonempty, rfl, ?_⟩
          exact (Blossom.card_defects_reference_blossom edge blossom).trans
            (preparedCount.trans count)
        have newstack := Stack.cons prepared b.cycle blossom newparents _ childGood
        have hh : StateGood F D
            ⟨⟨Blossom.contract prepared vs, buffer (Blossom.reference prepared vs)⟩,
              ⟨⟨G, buffer prepared⟩, EdgeAugmenting.code b.cycle⟩ :: frames, budget, none⟩ :=
          ⟨newstack, trivial, by dsimp only; simp only [List.length_cons]; omega⟩
        simpa only [Program.step, hr, hs, EdgeForest.code, push_code, hb, Option.map_some] using hh

/-- The original valid model internally supplies the initial stack invariant. -/
theorem StateGood.initial (F : CSP Table ℕ) (f : OccurrenceLabeling F Bool)
    (hf : ValidLabeling Table.sem f) (hM : EdgeInstance.EvenConstraints Table.sem F) :
    StateGood F (defects f).card
      ⟨⟨F, buffer f⟩, [], (CSP.occurrences F).length + 1, none⟩ := by
  refine ⟨.nil ⟨0, f, .nil, hf, hM, rfl, rfl⟩, trivial, ?_⟩
  dsimp only
  simp only [List.length_nil, Nat.zero_add, CSP.length_occurrences]
  simp [vars, List.length_flatMap]

/-- Every actual iteration internally retains the derived stack invariant. -/
theorem StateGood.iterate {F : CSP Table ℕ} {D : ℕ} {state : State}
    (hF : EdgeInstance F) (h : StateGood F D state) (n : ℕ) :
    StateGood F D (Program.step^[n] state) := by
  induction n with
  | zero => exact h
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact StateGood.step hF ih

end Cslib.Complexity.CSP.EdgeSolver.Program
