/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.TreeEval.Ary.Packed.RawControllerCorrect
public import Complexity.Computability.TreeEval.Ary.IterativeEncoding
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LinearSpaceArith

/-!
# Uniform binary encoding of the raw packed controller

One raw state type serves all runtime moduli, fan-ins and register widths. All natural fields
are binary, the bank is one flat framed list, and each continuation frame stores only its five
control fields. Cells are stored as `p + residue`; the padding is charged explicitly.

The size bounds below apply to the physical raw state and its runtime parameters, rather than
using a separate typed representation as a substitute for an encoded machine state.
-/

public section

namespace Cslib.TreeEval.Ary.Packed.RawController

open Turing.MultiTapeTM

/-- Binary runtime modulus, fan-in and register width. -/
abbrev encParams : Params ↪ List Bool := encPair encNat (encPair encNat encNat)

/-- Binary round, child, phase, coefficient and target. -/
abbrev encFrame : Frame ↪ List Bool :=
  encPair encNat (encPair encNat (encPair encBool (encPair encNat encNat)))

/-- One framed bank, one framed continuation stack and the optional call mode. -/
abbrev encState : State ↪ List Bool :=
  encPair (encList encNat) (encPair (encList encFrame) (encOption (encPair encNat encNat)))

/-- Runtime parameters stored beside their state, with all framing charged. -/
abbrev encFullState : Params × State ↪ List Bool := encPair encParams encState

variable {p d r b H : ℕ}

/-- Padding a field residue by its modulus costs at most twice the modulus's bit length. -/
theorem length_paddedResidue_le [NeZero p] (x : ZMod p) :
    (encNat (p + x.val)).length ≤ 2 * p.size := by
  have hp : 0 < p.size := Nat.size_pos.mpr (NeZero.pos p)
  have hx := ZMod.val_lt x
  have hpow := Nat.lt_size_self p
  have hfit : p + x.val < 2 ^ (p.size + 1) := by
    rw [pow_succ]
    omega
  rw [length_encNat_eq_size]
  exact (Nat.size_le.mpr hfit).trans (by omega)

/-- All padded bank entries and their framing are charged once. -/
theorem length_encBank_ofRegs_le [NeZero p] (S : Ary.State (ZMod p) d r) :
    (encList encNat (ofRegs S)).length ≤ (d + 1) * r * (4 * p.size + 1) := by
  have hlist := length_encList_le encNat (ofRegs S) (fun v hv => by
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hv
    exact length_paddedResidue_le _)
  have heq : 2 * (2 * p.size) + 1 = 4 * p.size + 1 := by omega
  simpa only [length_ofRegs, heq] using hlist

/-- Bits reserved for a single round-bounded frame, independent of register width. -/
@[expose] def frameSpace (p d : ℕ) : ℕ :=
  4 * p.size + 2 * d.size + (d + 1).size + 6

/-- The raw frame's binary encoding is exactly the typed frame's binary representation. -/
theorem encFrame_ofFrame [NeZero p] (fr : Ary.Iter.Frame (ZMod p) d) :
    encFrame (ofFrame fr) = Ary.Iter.encFrame (Ary.Iter.encField p) fr := rfl

theorem length_encFrame_ofFrame_le [NeZero p] (fr : Ary.Iter.Frame (ZMod p) d)
    (hr : fr.round < p - 1) :
    (encFrame (ofFrame fr)).length ≤ frameSpace p d := by
  rw [encFrame_ofFrame]
  have hbound := Ary.Iter.length_encFrame_le (Ary.Iter.encField p) fr
    (Ary.Iter.length_encField_le p) (show fr.round < p from by omega)
  simp only [Ary.Iter.frameBits] at hbound
  unfold frameSpace
  omega

private theorem encMode_ofMode [NeZero p] (mode : Ary.Iter.Mode (ZMod p) d) :
    encOption (encPair encNat encNat) (ofMode mode) =
      Ary.Iter.encMode (Ary.Iter.encField p) mode := by
  cases mode <;> rfl

/-- The binary parameter header is stored once beside the bank and control. -/
@[expose] def fullSpaceBound (p d r H : ℕ) : ℕ :=
  2 * ((d + 1) * r * (4 * p.size + 1)) +
    2 * (H * (2 * frameSpace p d + 1)) +
    2 * (encParams (p, d, r)).length + 2 * p.size + (d + 1).size + 5

/-- The raw encoding charges the padded physical bank and every continuation separator. -/
theorem length_encFullState_ofCfg_le [NeZero p] (q : Ary.Iter.Cfg (ZMod p) d r)
    (hq : Ary.Iter.ControlBounds H (p - 1) q) :
    (encFullState ((p, d, r), ofCfg q)).length ≤ fullSpaceBound p d r H := by
  have hbank := length_encBank_ofRegs_le q.regs
  have hstack := length_encList_le encFrame (q.stack.map ofFrame) (fun raw hraw => by
    obtain ⟨fr, hfr, heq⟩ := List.mem_map.mp hraw
    rw [← heq]
    exact length_encFrame_ofFrame_le fr (hq.2 fr hfr))
  have hmul := Nat.mul_le_mul_right (2 * frameSpace p d + 1) hq.1
  have hmode := Ary.Iter.length_encMode_le (Ary.Iter.encField p) q.mode
    (Ary.Iter.length_encField_le p)
  rw [← encMode_ofMode] at hmode
  simp only [encFullState, encState, ofCfg, length_encPair, List.length_map] at *
  unfold fullSpaceBound
  simp only [encParams, length_encPair, length_encNat_eq_size]
  omega

/-- Every physical raw prefix has the bound when its actual external replies meet the
controller's explicit contracts. No unit enumeration is stored in the raw state. -/
theorem length_encFullState_iterate_root_le [Fact p.Prime] (hd : 0 < d)
    (e : (Fin b → Bool) → Fin r → ZMod p)
    (E : Gate d b → (Fin d → Fin r → ZMod p) → Fin r → ZMod p)
    (T : Tree d b H) (S : Ary.State (ZMod p) d r) (c : ZMod p) (t : Fin (d + 1))
    (answer : State → Reply)
    (hanswer : ∀ n, ReplyCorrect e E T.nodeAt
      (Ary.Iter.runFrom hd e E (units p) T.nodeAt (Ary.Iter.initialCfg S c t) n)
      (answer (ofCfg
        (Ary.Iter.runFrom hd e E (units p) T.nodeAt (Ary.Iter.initialCfg S c t) n))))
    (n : ℕ) :
    (encFullState ((p, d, r),
      (fun raw => step p d r (answer raw) raw)^[n]
        (ofCfg (Ary.Iter.initialCfg S c t)))).length ≤ fullSpaceBound p d r H := by
  have hbounds (j : ℕ) : Ary.Iter.ControlBounds H (p - 1)
      (Ary.Iter.runFrom hd e E (units p) T.nodeAt (Ary.Iter.initialCfg S c t) j) := by
    simpa only [units, List.length_map, List.length_range] using
      Ary.Iter.runFrom_initial_bounds T hd e E (units p) S c t j
  rw [iterate_step_ofCfg hd e E T.nodeAt (Ary.Iter.initialCfg S c t) answer hanswer
    (fun j => (hbounds j).2)]
  exact length_encFullState_ofCfg_le _ (hbounds n)

/-- The padded physical bank still has linear storage for the selected packed parameters. -/
theorem length_encBank_packed_le (hd : 0 < d) (hb : 0 < b)
    (S : Ary.State (ZMod (fieldModulus d b)) d (chunkCount d b)) :
    (encList encNat (ofRegs S)).length ≤ 17 * (d + 1) * (b + chunkWidth d b) := by
  let : NeZero (fieldModulus d b) := ⟨(fieldModulus_prime d b).ne_zero⟩
  have hbank := length_encBank_ofRegs_le S
  have hprod := chunkCount_mul_fieldModulus_size_le hd hb
  have hr := chunkCount_le hd hb
  have hscalar : chunkCount d b * (4 * (fieldModulus d b).size + 1) ≤
      17 * (b + chunkWidth d b) := by nlinarith
  calc
    _ ≤ (d + 1) * chunkCount d b * (4 * (fieldModulus d b).size + 1) := hbank
    _ = (d + 1) * (chunkCount d b * (4 * (fieldModulus d b).size + 1)) := Nat.mul_assoc ..
    _ ≤ (d + 1) * (17 * (b + chunkWidth d b)) := Nat.mul_le_mul_left _ hscalar
    _ = _ := by ring

private theorem selected_parameter_sizes (hd : 0 < d) (hb : 0 < b) :
    d.size ≤ chunkWidth d b ∧ (chunkCount d b).size ≤ chunkWidth d b ∧
      (d + 1).size ≤ chunkWidth d b + 2 := by
  have hdle : d ≤ d * b := Nat.le_mul_of_pos_right d hb
  have hble : b ≤ d * b := by nlinarith
  have hdsize := Nat.size_le_size hdle
  have hrsize := Nat.size_le_size ((chunkCount_le hd hb).trans hble)
  have hsucc := Turing.MultiTapeTM.length_encNat_add_le_add d 1
  have hone : (encNat 1).length = 1 := rfl
  simp only [hone, length_encNat_eq_size, chunkWidth] at *
  omega

/-- Explicit selected-parameter accounting for the runtime header, padded bank and stack. -/
theorem fullSpaceBound_packed_le (hd : 0 < d) (hb : 0 < b) :
    fullSpaceBound (fieldModulus d b) d (chunkCount d b) H ≤
      34 * (d + 1) * (b + chunkWidth d b) +
        2 * (H * (22 * chunkWidth d b + 33)) + 20 * chunkWidth d b + 30 := by
  have hp := fieldModulus_size_le hd hb
  obtain ⟨hdsize, hrsize, htarget⟩ := selected_parameter_sizes hd hb
  have hprod := chunkCount_mul_fieldModulus_size_le hd hb
  have hr := chunkCount_le hd hb
  have hscalar : chunkCount d b * (4 * (fieldModulus d b).size + 1) ≤
      17 * (b + chunkWidth d b) := by nlinarith
  have hbank := Nat.mul_le_mul_left (d + 1) hscalar
  have hframe : 2 * frameSpace (fieldModulus d b) d + 1 ≤ 22 * chunkWidth d b + 33 := by
    unfold frameSpace
    omega
  have hstack := Nat.mul_le_mul_left H hframe
  have hmeta : 2 * (encParams (fieldModulus d b, d, chunkCount d b)).length +
      2 * (fieldModulus d b).size + (d + 1).size + 5 ≤ 20 * chunkWidth d b + 30 := by
    simp only [encParams, length_encPair, length_encNat_eq_size]
    omega
  unfold fullSpaceBound
  calc
    _ ≤ 2 * ((d + 1) * (17 * (b + chunkWidth d b))) +
        2 * (H * (22 * chunkWidth d b + 33)) + 20 * chunkWidth d b + 30 := by
      rw [Nat.mul_assoc] at ⊢
      omega
    _ = _ := by ring

/-- In the usual fixed-fan-in form, the raw storage is `O(b + H*log b)`.
The displayed constant is uniform; fan-in is charged explicitly. -/
theorem fullSpaceBound_packed_le_linear (hd : 0 < d) (hb : 0 < b) :
    fullSpaceBound (fieldModulus d b) d (chunkCount d b) H ≤
      100 * (d + 1) * (b + H * (chunkWidth d b + 1) + d.size + 1) := by
  have h := fullSpaceBound_packed_le (H := H) hd hb
  have hm := chunkWidth_le d b
  have hframe : 2 * (H * (22 * chunkWidth d b + 33)) ≤
      66 * (d + 1) * (H * (chunkWidth d b + 1)) := by
    calc
      _ ≤ 66 * (H * (chunkWidth d b + 1)) := by nlinarith
      _ ≤ 66 * ((d + 1) * (H * (chunkWidth d b + 1))) :=
        Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ (Nat.succ_pos d))
      _ = _ := by ring
  have hwidth := Nat.mul_le_mul_left (34 * (d + 1)) hm
  have hmeta : 20 * chunkWidth d b + 30 ≤
      30 * (d + 1) * (b + d.size + 1) := by
    calc
      _ ≤ 30 * (b + d.size + 1) := by omega
      _ ≤ 30 * ((d + 1) * (b + d.size + 1)) :=
        Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ (Nat.succ_pos d))
      _ = _ := by ring
  nlinarith

end Cslib.TreeEval.Ary.Packed.RawController
