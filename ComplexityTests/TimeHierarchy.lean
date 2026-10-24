/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Classes.Hierarchy
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.Plain

/-! Decoding descriptions from malformed, empty and padded words, the binary clock, the diagonal
on the padded descriptions of concrete accepting and rejecting machines, and the exponential
certificate. -/

namespace ComplexityTests.TimeHierarchy

open Cslib Cslib.Complexity Turing Turing.MultiTapeTM Turing.MultiTapeTM.Universal

/-! ### Framed words and decoding -/

example : frames [] = [] := frames_nil

/-- Two framed words, the first holding `false`. -/
example : frames (frame [false] ++ frame []) = [[false], []] := by
  rw [frames_frame_append, ← List.append_nil (frame []), frames_frame_append, frames_nil]

/-- A final incomplete frame is closed. -/
example : frames [true, true] = [[true]] := by
  rw [frames_of_ne_nil (by simp)]
  simp [unframe, dropFrame]

/-- The encoded list of framed words splits back into its elements. -/
example (l : List (List Bool)) : frames (encList encBits l) = l :=
  (frames_encList encBits l).trans (List.map_id l)

/-- A description, padded arbitrarily, is recovered. -/
example (d : Desc) (pad : List Bool) : decodeDesc (unframe (frame (eDesc d) ++ pad)) = d :=
  decodeDesc_unframe_frame_append d pad

/-- The empty word decodes to the description without work tapes or transitions. -/
example : decodeDesc [] = ⟨0, 0, []⟩ := by
  simp [decodeDesc, descDecoder, Decoder.map, Decoder.pair, Decoder.list, Decoder.unary,
    unframe, dropFrame]

/-- Malformed words: a lone marker, and a unary number missing its closing symbol. -/
example : decodeDesc [true] = ⟨0, 0, []⟩ := by
  simp [decodeDesc, descDecoder, Decoder.map, Decoder.pair, Decoder.list, Decoder.unary,
    unframe, dropFrame]

example : decodeDesc [false, true, true] = ⟨0, 1, []⟩ := by
  simp [decodeDesc, descDecoder, Decoder.map, Decoder.pair, Decoder.list, Decoder.unary,
    unframe, dropFrame]

/-- Every word decodes to a description of polynomial encoded length. -/
example : ∃ e c : ℕ, ∀ w : List Bool, (eDesc (decodeDesc w)).length ≤ c * (w.length + 1) ^ e := by
  obtain ⟨_d, e, h⟩ := exists_computableTidilyInDegree_decodeDesc
  obtain ⟨c, hc⟩ := h.2
  exact ⟨e, c, fun w => hc w⟩

/-! ### The clock -/

example : encNat (2 ^ 3) = [false, false, false, true] := encNat_two_pow 3

example : ComputableTidilyInDegree (fun x : List Bool => 2 ^ x.length) encBits encNat 1 1 :=
  ComputableTidilyInDegree.two_pow_length encBits

/-! ### The diagonal on concrete machines -/

/-- Halt at once with output `[b]`. -/
private def answer (b : Bool) : MultiTapeTM 0 Bool Unit :=
  MultiTapeTM.ofTr () fun _ _ _ =>
    { inputTape := 0, workTapes := Fin.elim0, output := some b, state := none }

/-- After its first step, the answering machine has halted with output `[b]`. -/
private theorem runFrom_answer (b : Bool) (x : List Bool) {t : ℕ} (ht : 1 ≤ t) :
    ((answer b).runFrom ((answer b).initCfg x) t).Halted ∧
      ((answer b).runFrom ((answer b).initCfg x) t).output = [b] := by
  have h1 : ((answer b).runFrom ((answer b).initCfg x) 1).state = none ∧
      ((answer b).runFrom ((answer b).initCfg x) 1).output = [b] := by
    change ((answer b).step _).state = none ∧ ((answer b).step _).output = [b]
    rw [MultiTapeTM.step_of_state (q := ()) rfl]
    simp [answer, Action.apply]
  rw [MultiTapeTM.runFrom_eq_of_halt _ _ ht h1.1]
  exact h1

/-- The numbering of the single state. -/
private def unitNum : Unit ↪ ℕ := ⟨fun _ => 0, fun _ _ _ => rfl⟩

/-- On the padded description of a machine answering `b`, the diagonal answers `!b`, so the
diagonal problem is neither empty nor everything. -/
example (b : Bool) (pad : List Bool) :
    diagonal (frame (eDesc (desc unitNum eBit (answer b))) ++ pad) = !b := by
  obtain ⟨hhalt, hout⟩ := runFrom_answer b (frame (eDesc (desc unitNum eBit (answer b))) ++ pad)
    (t := 2 ^ (frame (eDesc (desc unitNum eBit (answer b))) ++ pad).length) Nat.one_le_two_pow
  exact diagonal_desc unitNum (answer b) pad hhalt hout

/-! ### The separation -/

/-- The diagonal is computed in exponential time, up to a constant factor. -/
example : ∃ c, ComputableTidilyInTimeAndSpace diagonal encBits encBool
    (fun x => c * (2 ^ (4 * x.length) + 1)) fun x => c * (2 ^ (2 * x.length) + 1) := by
  obtain ⟨c, h, -⟩ := computableInO_diagonal.tidy
  exact ⟨c, h⟩

example : {x | diagonal x = true} ∉ P encBits := diagonal_notMem_P

/-- Plain machines do not compute the diagonal within a polynomial time bound either. -/
example (c d : ℕ) (s : List Bool → ℕ) :
    ¬ComputableInTimeAndSpace diagonal encBits encBool (fun x => c * (x.length + 1) ^ d) s :=
  not_computableInTimeAndSpace_diagonal (.of_forall_le c d fun _ => le_rfl)

/-! ### Axioms -/

/--
info: 'Cslib.Complexity.diagonal_notMem_P' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.diagonal_notMem_P

/--
info: 'Cslib.Complexity.not_computableInTimeAndSpace_diagonal' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.not_computableInTimeAndSpace_diagonal

/--
info: 'Cslib.Complexity.computableInO_diagonal' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.computableInO_diagonal

/--
info: 'Turing.MultiTapeTM.Universal.exists_computableTidilyInDegree_decodeDesc' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.Universal.exists_computableTidilyInDegree_decodeDesc

/--
info: 'Turing.MultiTapeTM.Universal.decodeDesc_unframe_frame_append' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.Universal.decodeDesc_unframe_frame_append

/--
info: 'Turing.MultiTapeTM.frames_encList' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.frames_encList

end ComplexityTests.TimeHierarchy
