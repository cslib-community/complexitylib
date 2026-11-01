/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests of explicit Boolean HPV trees)

public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.EncodedTree
public import ComplexityTests.Machines.Turing.MultiTape.BlockComputation

/-!
# Explicit Boolean block-computation trees

The codec separates FAIL, blank and written zero, and a nontrivial view round-trips at the
claimed width. A native halted accepting machine instantiates the complete encoded-tree
acceptance theorem. Source padding and invalid paths are checked independently of that machine.
-/

@[expose] public section

namespace ComplexityTests.EncodedBlockTree

open Turing MultiTapePTM.BlockComputation Cslib.TreeEval
open MultiTapeNTM.ChoiceTable

noncomputable def controlEquiv : Unit ≃ Fin 1 := Fintype.equivFin Unit

/-- The window contains blanks, written zeros and written ones. -/
def view : View 1 Unit 2 :=
  ((some (), fun _ => 1, .accept), fun _ port residue =>
    if port = 0 then none else if residue = 0 then some false else some true)

example : Encoding.width 1 1 2 = 21 := by
  rw [Encoding.width_eq]
  decide

example : Encoding.decode controlEquiv (Encoding.encode controlEquiv (some view)) = some view :=
  Encoding.decode_encode _ _

example : Encoding.decode (k := 1) (b := 2) controlEquiv (Encoding.encode controlEquiv none) =
    none := Encoding.decode_encode _ _

example : Encoding.encodeCell none ≠ Encoding.encodeCell (some false) := by
  intro h
  have hd := congrArg Encoding.decodeCell h
  simp only [Encoding.decodeCell_encodeCell] at hd
  cases hd

private theorem emitted :
    let cfg := BlockComputation.emit.runFrom (Cfg.init () []) 2
    cfg.state = none ∧ cfg.output = [true] := by
  have hh : (BlockComputation.emit.step (Cfg.init () [])).state = none := by
    rw [MultiTapeTM.step_of_state (q := ()) rfl]
    simp [BlockComputation.emit, Action.apply]
  have ho : (BlockComputation.emit.step (Cfg.init () [])).output = [true] := by
    rw [MultiTapeTM.step_of_state (q := ()) rfl]
    simp [BlockComputation.emit, Action.apply]
  change (BlockComputation.emit.step (BlockComputation.emit.step (Cfg.init () []))).state =
    none ∧ (BlockComputation.emit.step (BlockComputation.emit.step (Cfg.init () []))).output = _
  rw [MultiTapeTM.step_of_halt hh]
  exact ⟨hh, ho⟩

/-- The actual schedule gives a halted accepting decoded root of an existing Ary.Tree. -/
example :
    (Encoding.decode controlEquiv
      (encodedTree BlockComputation.machine [] 1 BlockComputation.actual controlEquiv).eval).elim
        false acceptingView = true := by
  change (Encoding.decode controlEquiv
    (encodedTree (MultiTapePTM.ofDeterministic BlockComputation.emit) [] 1
      BlockComputation.actual controlEquiv).eval).elim false acceptingView = true
  rw [accepting_eval_encodedTree_ofDeterministic_iff]
  exact ⟨rfl, emitted⟩

private def source : Fin 1 → Bool := fun _ => false
private def child (i : ℕ) (_ : Fin 2) : ℕ := i - 1
private def gates (_ : ℕ) : Ary.Gate 2 1 := fun values _ => !(values 0 0)

example : (Ary.Descending.tree source child gates 4 2).eval = source := rfl

-- The computation reaches its source after two edges and pads to height four.
example : (Ary.Descending.tree source child gates 4 2).nodeAt [1, 0] =
    .gate (fun _ => source) := rfl

example : (Ary.Descending.tree source child gates 4 2).nodeAt [1, 0, 1, 0] =
    .leaf source := rfl

example : (Ary.Descending.tree source child gates 4 2).nodeAt [1, 0, 1, 0, 0] =
    .none := rfl

end ComplexityTests.EncodedBlockTree
