/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.CarrySaveStream

namespace CslibFrontierTests.CarrySaveStream

open Turing Turing.MultiTapeATM Turing.MultiTapeATM.CarrySaveStream
open Cslib.Circuits.Boolean Cslib.Circuits.Boolean.CarrySaveQuery Cslib.BitString

private noncomputable def leaf (answer : Bool) (_carry claim : Bool) : MultiTapeATM 6 Bool Unit :=
  ofTMs (fun _ => MultiTapeTM.ofTr () (fun _ _ _ =>
    ⟨0, fun _ => (none, 0), some (answer == claim), none⟩)) (fun _ => false)

private theorem next_leaf {T : Type} {input : List Bool} (cfg : Cfg 6 Bool T input)
    (answer carry claim move : Bool) :
    (leaf answer carry claim).next move (cfg.withState (some ())) =
      { cfg.withState none with output := cfg.output ++ [answer == claim] } := by
  rw [leaf, next_ofTMs, MultiTapeTM.step_of_state rfl, MultiTapeTM.tr_ofTr]
  simp [Action.apply, Cfg.withState]

private theorem leaf_bound (answer : Bool) (sizeBudget : ℕ) :
    LeafBound (leaf answer) 1 sizeBudget [] := by
  intro height bits path unary frontier status carry claim _ _
  apply haltsWithin_succ.mpr
  intro move
  rw [show (leaf answer carry claim).toPTM.toNTM.q₀ = () from rfl, next_leaf]
  apply haltsWithin_of_halted
  rfl

private theorem leaf_correct (answer : Bool) (sizeBudget : ℕ) :
    LeafCorrect (w := 4) (fun _ _ => answer) (leaf answer) 1 sizeBudget [] := by
  intro height bits path unary frontier status carry claim _ _ hbits
  rw [acceptsWithin_succ_of_existential _ rfl rfl]
  simp only [show (leaf answer carry claim).toPTM.toNTM.q₀ = () from rfl, next_leaf]
  cases answer <;> cases carry <;> cases claim <;>
    simp [AcceptsWithin, Cfg.withState, value, component, tree, hbits,
      fstBits, sndBits, Fin.appendEquiv]

private theorem frontier_three : Frontier [true, true, true] 0 3 := by
  intro j
  rw [zero_add, tapeOfList_ofNat]
  cases j with
  | zero => rfl
  | succ j => cases j with
    | zero => rfl
    | succ j => cases j <;> simp

private theorem tree_zero (depth : ℕ) (path : List Bool) :
    tree (w := 4) (fun _ _ => false) depth path = fun _ => false := by
  induction depth generalizing path with
  | zero => rfl
  | succ depth ih =>
    rw [tree, ih, ih]
    have he := CarrySaveLocal.eval_compressor (w := 4)
      (fun _ => false) (fun _ => false) (fun _ => false) (fun _ => false)
    have hi : Fin.append (Fin.append (fun _ : Fin 4 => false) (fun _ : Fin 4 => false))
        (Fin.append (fun _ : Fin 4 => false) (fun _ : Fin 4 => false)) =
        Fin.append (fun _ : Fin 8 => false) (fun _ : Fin 8 => false) := by
      funext i
      fin_cases i <;> rfl
    rw [hi] at he
    rw [he]
    funext i
    fin_cases i <;> rfl

/-- Three actual cyclic compressor layers over an arbitrary persistent address answer both
claims and both sum/carry components. Index two exercises nontrivial bit decrements. -/
example (path : List Bool) (carry claim : Bool) :
    (machine (leaf false) carry claim).AcceptsWithin 124
      ((config (input := []) [true, true] [false, true] path [true, true, true] 0 false).withState
        (some (.header carry claim))) ↔ claim = false := by
  have h := acceptsWithin_budget (w := 4) (fun _ _ => false) (leaf false) 1
    (path.length + 7) (leaf_bound false _) (leaf_correct false _)
    3 [true, true] [false, true] path [true, true, true] 0 false carry claim
    frontier_three (by simp; omega) (by decide) (by decide)
  have hz : value (w := 4) (fun _ _ => false) ⟨path, 3, carry, 2⟩ = false := by
    cases carry <;> simp [value, tree_zero, component, fstBits, sndBits, Fin.appendEquiv]
  simpa [budget, lsbValue, hz, eq_comm] using h

/-- Every existential guess and universal port is included in the same linear native bound. -/
example (path : List Bool) (carry claim : Bool) :
    (machine (leaf false) carry claim).HaltsWithin 124
      ((config (input := []) [true, true] [false, true] path [true, true, true] 0 false).withState
        (some (.header carry claim))) := by
  simpa [budget] using haltsWithin_budget (leaf false) 1 (path.length + 7)
    (leaf_bound false _) 3 [true, true] [false, true]
    path [true, true, true] 0 false carry claim frontier_three (by simp; omega)

private theorem value_true_one (path : List Bool) (carry : Bool) :
    value (w := 4) (fun _ _ => true) ⟨path, 1, carry, 1⟩ = true := by
  rw [value_layer (fun _ _ => true) path 0 carry ⟨1, by decide⟩]
  cases carry <;> simp [CarrySaveLocal.eval_formula, descend, CarrySaveLocal.source,
    value, component, tree, fstBits, sndBits, Fin.appendEquiv, maj3]

/-- A positive-depth all-ones tree has a true sum bit and a true carry bit at index one.
Both claims are checked, so this also tests rejection when a true internal value is denied. -/
example (path : List Bool) (carry claim : Bool) :
    (machine (leaf true) carry claim).AcceptsWithin 42
      ((config (input := []) [true] [true] path [true] 0 false).withState
        (some (.header carry claim))) ↔ claim = true := by
  have hf : Frontier [true] 0 1 := by
    intro j
    rw [zero_add, tapeOfList_ofNat]
    cases j <;> simp
  have h := acceptsWithin_budget (w := 4) (fun _ _ => true) (leaf true) 1
    (path.length + 3) (leaf_bound true _) (leaf_correct true _)
    1 [true] [true] path [true] 0 false carry claim hf (by simp; omega) (by decide) (by decide)
  have hv := value_true_one path carry
  simpa [budget, lsbValue, hv, eq_comm] using h

private noncomputable def sentinelLeaf (_carry claim : Bool) : MultiTapeATM 7 Bool Unit :=
  ofTMs (fun _ => MultiTapeTM.ofTr () (fun _ _ work =>
    ⟨0, fun _ => (none, 0), some ((work 6 == some true) == claim), none⟩)) (fun _ => false)

private theorem next_sentinel {T : Type} {input : List Bool} (cfg : Cfg 7 Bool T input)
    (carry claim move : Bool) (h : cfg.workTapes 6 (cfg.workTapePos 6) = some true) :
    (sentinelLeaf carry claim).next move (cfg.withState (some ())) =
      { cfg.withState none with output := cfg.output ++ [claim] } := by
  rw [sentinelLeaf, next_ofTMs, MultiTapeTM.step_of_state rfl, MultiTapeTM.tr_ofTr]
  cases claim <;> simp [Action.apply, Cfg.withState, Cfg.workTapeSymbols, h]

private theorem sentinel_bound (scratch : Scratch 1)
    (h : scratch.tapes 6 (scratch.positions 6) = some true) (sizeBudget : ℕ) :
    LeafBound sentinelLeaf 1 sizeBudget [] scratch := by
  intro height bits path unary frontier status carry claim _ _
  apply haltsWithin_succ.mpr
  intro move
  rw [show (sentinelLeaf carry claim).toPTM.toNTM.q₀ = () from rfl,
    next_sentinel _ carry claim move (by simpa using h)]
  apply haltsWithin_of_halted
  rfl

private theorem sentinel_correct (scratch : Scratch 1)
    (h : scratch.tapes 6 (scratch.positions 6) = some true) (sizeBudget : ℕ) :
    LeafCorrect (w := 4) (fun _ _ => true) sentinelLeaf 1 sizeBudget [] scratch := by
  intro height bits path unary frontier status carry claim _ _ hbits
  rw [acceptsWithin_succ_of_existential _ rfl rfl]
  simp only [show (sentinelLeaf carry claim).toPTM.toNTM.q₀ = () from rfl]
  have hn (move : Bool) := next_sentinel
    (config (input := []) height bits path unary frontier status scratch) carry claim move
    (by simpa using h)
  simp only [hn]
  cases carry <;> cases claim <;>
    simp [AcceptsWithin, Cfg.withState, value, component, tree, hbits,
      fstBits, sndBits, Fin.appendEquiv]

/-- A genuine seven-tape leaf reads a true sentinel at an arbitrary private cursor after the
cyclic controller has run. The private tape's other cells are unrestricted. Both possible claims
and both compressor outputs are verified within the unchanged forty-two-step bound. -/
example (scratch : Scratch 1) (h : scratch.tapes 6 (scratch.positions 6) = some true)
    (path : List Bool) (carry claim : Bool) :
    ((machine sentinelLeaf carry claim).AcceptsWithin 42
      ((config (input := []) [true] [true] path [true] 0 false scratch).withState
        (some (.header carry claim))) ↔ claim = true) ∧
    (machine sentinelLeaf carry claim).HaltsWithin 42
      ((config (input := []) [true] [true] path [true] 0 false scratch).withState
        (some (.header carry claim))) := by
  have hf : Frontier [true] 0 1 := by
    intro j
    rw [zero_add, tapeOfList_ofNat]
    cases j <;> simp
  constructor
  · have ha := acceptsWithin_budget (w := 4) (fun _ _ => true) sentinelLeaf 1
      (path.length + 3) (sentinel_bound scratch h _) (sentinel_correct scratch h _)
      1 [true] [true] path [true] 0 false carry claim hf (by simp; omega) (by decide) (by decide)
    have hv := value_true_one path carry
    simpa [budget, lsbValue, hv, eq_comm] using ha
  · simpa [budget] using haltsWithin_budget sentinelLeaf 1 (path.length + 3)
      (sentinel_bound scratch h _) 1 [true] [true] path [true] 0 false carry claim hf
      (by simp; omega)

end CslibFrontierTests.CarrySaveStream
