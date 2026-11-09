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

/-- Framing and splitting: two framed words, an incomplete final frame, and round-trip encoding of
framed lists and padded descriptions. -/
example (l : List (List Bool)) :
    frames (frame [false] ++ frame []) = [[false], []] ∧
    frames [true, true] = [[true]] ∧
    frames (encList encBits l) = l ∧
    (decodeDesc (unframe (frame (eDesc ⟨2, 3, []⟩) ++ [true, false]))).q₀ = 3 :=
  ⟨by rw [frames_frame_append, ← List.append_nil (frame []), frames_frame_append, frames_nil],
   by rw [frames_of_ne_nil (by simp)]; simp [unframe, dropFrame],
   (frames_encList encBits l).trans (List.map_id l),
   by rw [decodeDesc_unframe_frame_append]⟩

/-- Decoding malformed and empty words: `[]`, a lone marker `[true]`, and an unclosed unary number
`[false, true, true]`. -/
example :
    decodeDesc [] = ⟨0, 0, []⟩ ∧
    decodeDesc [true] = ⟨0, 0, []⟩ ∧
    decodeDesc [false, true, true] = ⟨0, 1, []⟩ := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [decodeDesc, descDecoder, Decoder.map, Decoder.pair, Decoder.list, Decoder.unary,
      unframe, dropFrame]

/-- Every word decodes to a description of polynomial encoded length. -/
example : ∃ e c : ℕ, ∀ w : List Bool, (eDesc (decodeDesc w)).length ≤ c * (w.length + 1) ^ e := by
  obtain ⟨_d, e, h⟩ := exists_computableInDegree_decodeDesc
  obtain ⟨c, hc⟩ := h.2
  exact ⟨e, c, fun w => hc w⟩

/-- Plain automation composes description decoding with framing of its input. -/
example : ComputableInPolyTime (fun w : List Bool => (decodeDesc w, frame w)) encBits
    (encPair eDesc encBits) := by
  fun_prop

/-! ### The clock -/

example :
    (encNat (2 ^ 5)).length = 6 ∧
    ComputableInPolyTime (fun x : List Bool => 2 ^ x.length) encBits encNat :=
  ⟨by rw [encNat_two_pow]; decide,
   (ComputableTidilyInDegree.two_pow_length
     encBits).computableTidilyInPolyTime.computableInPolyTime⟩

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

/-- The diagonal is computed in exponential time (up to a constant factor), is not computable in
polynomial time, and cannot be computed by any plain machine within a polynomial time bound. -/
example (c d : ℕ) (s : List Bool → ℕ) :
    (∃ c₀, ComputableTidilyInTimeAndSpace diagonal encBits encBool
      (fun x => c₀ * (2 ^ (4 * x.length) + 1)) fun x => c₀ * (2 ^ (2 * x.length) + 1)) ∧
    ¬ComputableInPolyTime diagonal encBits encBool ∧
    ¬ComputableInTimeAndSpace diagonal encBits encBool (fun x => c * (x.length + 1) ^ d) s := by
  obtain ⟨c₀, h, -⟩ := computableInO_diagonal.tidy
  exact ⟨⟨c₀, h⟩,
    fun hp => diagonal_notMem_P ⟨diagonal, hp, fun _ => Iff.rfl⟩,
    not_computableInTimeAndSpace_diagonal (.of_forall_le c d fun _ => le_rfl)⟩

end ComplexityTests.TimeHierarchy
