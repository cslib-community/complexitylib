/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.CarryLookahead.Query.Routing
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.WordGameHeader
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryLog

/-!
# Preparing a finishing-adder query from binary parameters

The runtime input contains only the binary width, binary bit index, and claimed Boolean value.
Its native initializer computes the ceiling logarithm of `width + 1` in unary and writes the
canonical sum-wire metadata. No round count or carry-save operand is supplied as an input.
The control header has the same layout used by the native word-game controller.

The certificates charge polynomial time in the binary parameter encoding. Installing the
resulting words on the evaluator's work tapes is a separate native composition.
-/

public section

namespace Cslib.Circuits.Boolean.CarryLookahead.Query.Initial

open Turing Turing.MultiTapeTM ComputableInPolyTime

/-- The binary parameters of one ordinary count-bit claim. -/
structure Input where
  /-- Binary operand width. -/
  width : ℕ
  /-- Binary sum-bit index; semantic evaluation requires this to be below the width. -/
  bit : ℕ
  /-- Claimed value of that sum bit. -/
  claim : Bool
  deriving DecidableEq

/-- Framed binary width and bit index, followed by the claimed Boolean. -/
enc_structure encInput : Input where width : encNat, bit : encNat, claim : encBool

/-- The exact word assembled from the two binary source words and the raw claimed bit. -/
theorem encInput_eq (a : Input) :
    encInput a = frame (encNat a.width) ++ frame (encNat a.bit) ++ [a.claim] := by
  simp [encInput_apply, encInputFields, encPair_apply, encBool_apply, List.append_assoc]

/-- The parameter word contains no unary width or precomputed round count. -/
theorem length_encInput (a : Input) :
    (encInput a).length = 2 * a.width.size + 2 * a.bit.size + 3 := by
  simp only [encInput_apply, encInputFields, length_encPair, encNat_apply,
    Nat.size_eq_bits_len, encBool_apply, List.length_singleton]
  omega

/-- For a valid bit index, preparation is charged only to the binary width's length. -/
theorem length_encInput_le (a : Input) (hbit : a.bit < a.width) :
    (encInput a).length ≤ 4 * a.width.size + 3 := by
  rw [length_encInput]
  have hsize := Nat.size_le_size hbit.le
  omega

/-- The initial sum-wire position, computing its unary round count from the binary width. -/
@[expose] def position (a : Input) : Routing.Position :=
  Routing.ofClaim a.width (Nat.clog 2 (a.width + 1)) ⟨.sum a.bit, a.claim⟩

/-- A native polynomial-time initializer computes every field, including the unary logarithm. -/
theorem position_polyTime : ComputableInPolyTime position encInput Routing.encPosition := by
  unfold position Routing.ofClaim Address.toData
  apply Routing.encPosition_mk_polyTime
  · fun_prop
  · exact binary_clog_two.comp (binary_add' (by fun_prop) (const 1))
  · apply encAddressData_mk_polyTime <;> fun_prop
  · fun_prop

/-- The sum wire's first player is its claimed value. -/
theorem player_position (a : Input) : Routing.player (position a) = some a.claim := by
  unfold position Routing.player
  rw [Routing.operation_ofClaim]
  rfl

/-- The physical initializer writes the claim followed by the controller's blank move cell. -/
theorem header_position (a : Input) :
    wordGameHeader (Routing.player (position a)) = [a.claim, false] := by
  rw [player_position]
  rfl

/-- Valid initial metadata fits the same short bound used by every routing round. -/
theorem length_position_le (a : Input) (hbit : a.bit < a.width) :
    (Routing.encPosition (position a)).length ≤
      4 * a.width.size + 6 * Nat.clog 2 (a.width + 1) + 26 :=
  Routing.length_ofClaim_le ⟨.sum a.bit, a.claim⟩ hbit

end Cslib.Circuits.Boolean.CarryLookahead.Query.Initial
