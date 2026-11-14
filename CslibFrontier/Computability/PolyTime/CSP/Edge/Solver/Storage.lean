/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PolyTime.CSP.Edge.Solver.Stack
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Length
import CslibFrontier.Tactic.EncLen

/-!
# Full framed storage of the running edge-CSP solver

The bounds include every stored prepared parent, all explicit relation rows and binary names,
every binary step position, every list/pair/option frame, and the actual unary depth budget.
They apply to the actual contraction histories derived by `StateGood.step`. They are original
bookkeeping, and do not replace encoded bit length by unit-cost graph access.
-/

public section

namespace Cslib.Complexity.CSP.EdgeSolver.Program

open Cslib.Logic.PL Cslib.Logic.PL.CSP Turing.MultiTapeTM

/-- Full framed occurrence input budget for every actual descended body. -/
@[expose] def inputBudget (F : CSP Table ℕ) : ℕ :=
  2 * Size.bodyBudget F + 1 + 6 * F.vars.length

/-- Binary start and all framed step-position pairs of every actual blossom cycle. -/
@[expose] def walkBudget (F : CSP Table ℕ) : ℕ :=
  2 * Size.nameBudget F + 1 + 2 * F.vars.length * (12 * F.vars.length + 3)

/-- A prepared parent is framed, followed by its full binary-position cycle. -/
@[expose] def frameBudget (F : CSP Table ℕ) : ℕ := 2 * inputBudget F + 1 + walkBudget F

/-- All current fields and at most one frame per spent original occurrence. -/
@[expose] def stateBudget (F : CSP Table ℕ) : ℕ :=
  2 * inputBudget F + 1 + 2 * ((F.vars.length + 1) * (2 * frameBudget F + 1)) + 1 +
    2 * (F.vars.length + 1) + 1 + (6 * F.vars.length + 2)

/-- Baseline buffers charge their actual incidence width and complete descended body. -/
theorem InputGood.encoded_le {F : CSP Table ℕ} {D : ℕ} {input : EdgeForest.Input}
    (h : InputGood F D input) (hF : EdgeInstance F) :
    (EdgeForest.encInput input).length ≤ inputBudget F := by
  obtain ⟨k, f, chain, valid, _, hbits, _⟩ := h
  have hb := chain.body_budget hF f valid
  have hw := chain.width_le hF
  have hlen : (encList encBool input.labels).length = 3 * (incidenceList input.body).length := by
    rw [hbits]
    simp [length_encList, encBool_apply, List.map_map, Function.comp_def, Nat.mul_comm]
  enc_len [EdgeForest.encInput_apply, EdgeForest.encInputFields, hlen, inputBudget]

private theorem cycle_budget {F G : CSP Table ℕ} {D : ℕ} (f : OccurrenceLabeling G Bool)
    (w : Walk G) (good : InputGood F D ⟨G, buffer f⟩)
    (hb : w.IsBlossom Table.sem f) (hF : EdgeInstance F) :
    (EdgeAugmenting.encWalkCode (EdgeAugmenting.code w)).length ≤ walkBudget F := by
  obtain ⟨k, chain, _, _, _⟩ := good.materialized f
  obtain ⟨o, _, ho⟩ := List.mem_map.mp (hb.1.start_mem_vars hb.steps_ne_nil)
  have hname : (encNat w.start).length ≤ Size.nameBudget F :=
    chain.name_budget hF _ (ho ▸ o.var_mem)
  have hw := chain.width_le hF
  refine (Size.encoded_walk_le w hb.1 _ hname).trans ?_
  calc
    _ ≤ 2 * Size.nameBudget F + 1 + 2 * F.vars.length * (6 * (2 * F.vars.length) + 3) := by
      gcongr
    _ = walkBudget F := by unfold walkBudget; ring

/-- Every stored frame has the same complete polynomial original-input storage budget. -/
theorem Stack.frame_encoded_le {F : CSP Table ℕ} {D : ℕ} {input : EdgeForest.Input}
    {frames : List Frame} (h : Stack F D input frames) (hF : EdgeInstance F) :
    ∀ frame ∈ frames, (encFrame frame).length ≤ frameBudget F := by
  induction h with
  | nil good => simp
  | cons f w blossom parents bits good ih =>
    intro frame hf
    rcases List.mem_cons.mp hf with rfl | hf
    · have hp := parents.current.encoded_le hF
      have hw := cycle_budget f w parents.current blossom hF
      enc_len [encFrame_apply, encFrameFields, frameBudget]
    · exact ih frame hf

/-- Full encoded storage of every actual running stack, including all tags and unary clocks. -/
theorem StateGood.encoded_le {F : CSP Table ℕ} {D : ℕ} {state : State}
    (h : StateGood F D state) (hF : EdgeInstance F) :
    (encState state).length ≤ stateBudget F := by
  have hi := h.stack.current.encoded_le hF
  obtain ⟨k, f, chain, _, _, _, _⟩ := h.stack.current
  have hw := chain.width_le hF
  have hc := h.clock
  have hframes : (encList encFrame state.frames).length ≤
      (F.vars.length + 1) * (2 * frameBudget F + 1) := by
    rw [length_encList]
    calc
      _ ≤ (state.frames.map fun _ => 2 * frameBudget F + 1).sum := by
        apply List.sum_le_sum
        intro frame hf
        have := h.stack.frame_encoded_le hF frame hf
        omega
      _ = state.frames.length * (2 * frameBudget F + 1) := by simp
      _ ≤ _ := Nat.mul_le_mul_right _ (by omega)
  have hs : (encOption (encOption (encList encBool)) state.status).length ≤
      6 * F.vars.length + 2 := by
    cases he : state.status with
    | none => simp
    | some result =>
      cases result with
      | none => simp
      | some bits =>
        have hg : ∃ g : OccurrenceLabeling state.current.body Bool,
            bits = buffer g ∧ ValidLabeling Table.sem g ∧ (defects g).card + 2 = D := by
          simpa only [StatusGood, he] using h.result
        obtain ⟨g, rfl, _, _⟩ := hg
        simp only [encOption_some, List.length_cons]
        have hl : (encList encBool (buffer g)).length =
            3 * (incidenceList state.current.body).length := by
          simp [buffer, length_encList, encBool_apply, List.map_map, Function.comp_def,
            Nat.mul_comm]
        rw [hl]
        omega
  enc_len [encState_apply, encStateFields, stateBudget]

end Cslib.Complexity.CSP.EdgeSolver.Program
