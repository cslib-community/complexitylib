/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation
public import Complexity.Foundations.Data.BitString.Binary
public import Complexity.Foundations.Data.BitString.Block
public import Complexity.Foundations.Data.Nat.BinarySize

/-!
# Fixed-width binary block-computation values

An outer bit distinguishes FAIL from a valid leaving view. The payload stores the finite control
state by a binary rank, each of the `k+1` head residues in `b.size` bits, the output track in two
bits, and every cell of the three work-tape windows in two bits. Window cells use canonical
row-major blocks: tape, window port, residue, then cell bit. No rank of the whole view or unary
encoding of window contents is used.

The supplied equivalence enumerates only the fixed machine's finite control states. The width
is `1 + (s+1).size + (k+1)*b.size + 2 + 6*k*b`. The positive block-width assumption is essential:
`ZMod 0` is infinite. Unused state/cell/track words decode to a halted state, blank cell or
`other` output track respectively; a false outer bit always decodes to FAIL.

These are explicit semantic codecs, not native runtime codec certificates.

## Main results

* `Turing.MultiTapePTM.BlockComputation.Encoding.decode_encode`: encoding then decoding is exact.
* `Turing.MultiTapePTM.BlockComputation.Encoding.width_eq`: the precise width calculation.
* `Turing.MultiTapePTM.BlockComputation.Encoding.width_le`: a linear bound for fixed machine data.
-/

public section

namespace Turing.MultiTapePTM.BlockComputation.Encoding

open Cslib Cslib.BitString MultiTapeNTM.ChoiceTable

variable {k s b : ℕ} {State : Type}

/-- Width of the three two-bit-cell windows on every work tape. -/
@[expose] def windowBits (k b : ℕ) : ℕ := k * (3 * (b * 2))

/-- Width of the payload before the outer FAIL tag. -/
@[expose] def payloadBits (k s b : ℕ) : ℕ :=
  (s + 1).size + ((k + 1) * b.size + (2 + windowBits k b))

/-- Width of one optionally failing block-computation value. -/
@[expose] def width (k s b : ℕ) : ℕ := payloadBits k s b + 1

theorem width_pos (k s b : ℕ) : 0 < width k s b := Nat.succ_pos _

/-- Only the optional finite control state is numbered, independently of the windows. -/
@[expose] def stateIndex (e : State ≃ Fin s) : Option State ≃ Fin (s + 1) :=
  (Equiv.optionCongr e).trans (finSuccEquiv s).symm

/-- Fixed-width binary code of the optional control state. -/
@[expose] def encodeState (e : State ≃ Fin s) (state : Option State) :
    BitString (s + 1).size :=
  (equivFin (s + 1).size).symm
    ⟨stateIndex e state, (stateIndex e state).isLt.trans (Nat.lt_size_self (s + 1))⟩

/-- An unused state rank represents the halted control state. -/
@[expose] def decodeState (e : State ≃ Fin s) (bits : BitString (s + 1).size) : Option State :=
  let rank := equivFin (s + 1).size bits
  if h : rank.val < s + 1 then (stateIndex e).symm ⟨rank.val, h⟩ else none

@[simp] theorem decodeState_encodeState (e : State ≃ Fin s) (state : Option State) :
    decodeState e (encodeState e state) = state := by
  simp only [decodeState, encodeState, Equiv.apply_symm_apply]
  rw [dite_eq_left (stateIndex e state).isLt]
  exact (stateIndex e).symm_apply_apply state

variable [NeZero b]

/-- The binary value of a head residue, padded to the runtime block-width bit length. -/
@[expose] def encodeResidue (r : ZMod b) : BitString b.size :=
  (equivFin b.size).symm ⟨r.val, (ZMod.val_lt r).trans (Nat.lt_size_self b)⟩

/-- Read the binary value and reduce modulo the positive block width. -/
@[expose] def decodeResidue (bits : BitString b.size) : ZMod b :=
  (equivFin b.size bits).val

@[simp] theorem decodeResidue_encodeResidue (r : ZMod b) :
    decodeResidue (encodeResidue r) = r := by
  simp only [decodeResidue, encodeResidue, Equiv.apply_symm_apply, ZMod.natCast_zmod_val]

/-- Residues in canonical `Option (Fin k)` order, with the input head included. -/
@[expose] def encodeHeads (heads : Option (Fin k) → ZMod b) :
    BitString ((k + 1) * b.size) :=
  blocksEquiv.symm fun i : Fin (k + 1) => encodeResidue (heads (finSuccEquiv k i))

/-- Read the fixed-width residues of all work heads and the input head. -/
@[expose] def decodeHeads (bits : BitString ((k + 1) * b.size)) :
    Option (Fin k) → ZMod b :=
  fun head => decodeResidue (blocksEquiv bits ((finSuccEquiv k).symm head))

@[simp] theorem decodeHeads_encodeHeads (heads : Option (Fin k) → ZMod b) :
    decodeHeads (encodeHeads heads) = heads := by
  funext head
  simp only [decodeHeads, encodeHeads, Equiv.apply_symm_apply, decodeResidue_encodeResidue]

/-- Two bits separate blank, written zero and written one. The fourth word is unused. -/
@[expose] def encodeCell : Option Bool → BitString 2
  | none => ![false, false]
  | some bit => ![true, bit]

/-- Decode a cell tag, treating both words with a false first bit as blank. -/
@[expose] def decodeCell (bits : BitString 2) : Option Bool :=
  if bits 0 then some (bits 1) else none

@[simp] theorem decodeCell_encodeCell (cell : Option Bool) :
    decodeCell (encodeCell cell) = cell := by
  cases cell <;> rfl

/-- The source output track has three cases: empty, exactly `[true]`, and other. -/
@[expose] def encodeTrack : OutputTrack → BitString 2
  | .empty => ![false, false]
  | .accept => ![true, false]
  | .other => ![false, true]

/-- Decode the output summary, assigning the unused word to `other`. -/
@[expose] def decodeTrack (bits : BitString 2) : OutputTrack :=
  if bits 1 then .other else if bits 0 then .accept else .empty

@[simp] theorem decodeTrack_encodeTrack (track : OutputTrack) :
    decodeTrack (encodeTrack track) = track := by
  cases track <;> rfl

/-- The explicit row-major two-bit encoding of all three windows on all work tapes. -/
@[expose] def encodeWindows (windows : Fin k → Fin 3 → ZMod b → Option Bool) :
    BitString (windowBits k b) :=
  blocksEquiv.symm fun tape : Fin k =>
    blocksEquiv.symm fun port : Fin 3 =>
      blocksEquiv.symm fun residue : Fin b =>
        encodeCell (windows tape port (residue.val : ZMod b))

/-- Read all window cells in the same tape/port/residue order as the encoder. -/
@[expose] def decodeWindows (bits : BitString (windowBits k b)) :
    Fin k → Fin 3 → ZMod b → Option Bool :=
  fun tape port residue =>
    decodeCell (blocksEquiv (blocksEquiv (blocksEquiv bits tape) port)
      ⟨residue.val, ZMod.val_lt residue⟩)

@[simp] theorem decodeWindows_encodeWindows
    (windows : Fin k → Fin 3 → ZMod b → Option Bool) :
    decodeWindows (encodeWindows windows) = windows := by
  funext tape port residue
  simp only [decodeWindows, encodeWindows, Equiv.apply_symm_apply,
    decodeCell_encodeCell, ZMod.natCast_zmod_val]

/-- Encode the control record and all window cells with fixed field boundaries. -/
@[expose] def encodePayload (e : State ≃ Fin s) (view : View k State b) :
    BitString (payloadBits k s b) :=
  Fin.append (encodeState e view.1.1)
    (Fin.append (encodeHeads view.1.2.1)
      (Fin.append (encodeTrack view.1.2.2) (encodeWindows view.2)))

/-- Read the control fields and window cells at their fixed field boundaries. -/
@[expose] def decodePayload (e : State ≃ Fin s) (bits : BitString (payloadBits k s b)) :
    View k State b :=
  ((decodeState e (fstBits bits), decodeHeads (fstBits (sndBits bits)),
    decodeTrack (fstBits (sndBits (sndBits bits)))),
    decodeWindows (sndBits (sndBits (sndBits bits))))

@[simp] theorem decodePayload_encodePayload (e : State ≃ Fin s) (view : View k State b) :
    decodePayload e (encodePayload e view) = view := by
  rcases view with ⟨⟨state, heads, track⟩, windows⟩
  simp only [decodePayload, encodePayload, fstBits_append, sndBits_append,
    decodeState_encodeState, decodeHeads_encodeHeads, decodeTrack_encodeTrack,
    decodeWindows_encodeWindows]

/-- A false tag is FAIL; a true tag is followed by the explicit payload. -/
@[expose] def encode (e : State ≃ Fin s) : Option (View k State b) → BitString (width k s b)
  | none => Fin.cons false (fun _ => false)
  | some view => Fin.cons true (encodePayload e view)

/-- Read the outer FAIL bit before decoding a valid-view payload. -/
@[expose] def decode (e : State ≃ Fin s) (bits : BitString (width k s b)) :
    Option (View k State b) :=
  if bits ⟨0, width_pos k s b⟩ then some (decodePayload e (Fin.tail bits)) else none

/-- Every genuine view, including FAIL, round-trips without identifying blank and written zero. -/
@[simp] theorem decode_encode (e : State ≃ Fin s) (value : Option (View k State b)) :
    decode e (encode e value) = value := by
  cases value with
  | none => rfl
  | some view =>
    change some (decodePayload e (encodePayload e view)) = some view
    rw [decodePayload_encodePayload]

/-- The explicit codec is injective; no enumeration of all possible views is involved. -/
theorem encode_injective (e : State ≃ Fin s) : Function.Injective (encode (k := k) (b := b) e) :=
  Function.LeftInverse.injective (decode_encode e)

/-- The exact width charges all head residues, every cell, output track and FAIL. -/
theorem width_eq (k s b : ℕ) :
    width k s b = 1 + (s + 1).size + (k + 1) * b.size + 2 + 6 * k * b := by
  unfold width payloadBits windowBits
  ring

/-- For fixed control and work-tape counts the full payload is linear in the block width. -/
theorem width_le (k s b : ℕ) :
    width k s b ≤ (7 * k + 1) * b + (s + 1).size + 3 := by
  have hsize : b.size ≤ b := Nat.size_le.mpr (Nat.lt_two_pow_self (n := b))
  have hmul := Nat.mul_le_mul_left (k + 1) hsize
  rw [width_eq]
  nlinarith

end Turing.MultiTapePTM.BlockComputation.Encoding
