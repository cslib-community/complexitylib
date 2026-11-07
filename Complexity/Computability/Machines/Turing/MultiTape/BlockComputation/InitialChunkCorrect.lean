/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.InitialChunk
public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputationTree
public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.QueryReplayChunkBits
import Mathlib.Tactic.FinCases

/-!
# Correct initial-source packed chunks

The fixed control prefix followed by zero bits is the existing Boolean encoding of the initial
view. Numeric reads ignore appended zero suffixes, so the native headerWord reader gives exactly
the existing packed encoding, including a final partial chunk.
-/

public section

namespace Turing.MultiTapePTM.BlockComputation.InitialChunk

open MultiTapeTM Cslib.BitString Cslib.TreeEval.Ary

variable {k s : ℕ} {Q : Type}

private theorem ofBits_replicate_false (n : ℕ) : ofBits (List.replicate n false) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ, ofBits, List.foldr_cons, ← ofBits, ih]
    rfl

private theorem readNat_append_false (word : List Bool) (n offset count : ℕ) :
    Encoding.NativeDecode.readNat (word ++ List.replicate n false) offset count =
      Encoding.NativeDecode.readNat word offset count := by
  induction word generalizing offset count with
  | nil =>
    simp only [List.nil_append, Encoding.NativeDecode.readNat, List.drop_replicate,
      List.take_replicate, ofBits_replicate_false, List.drop_nil, List.take_nil]
    rfl
  | cons bit word ih =>
    cases offset with
    | succ offset =>
      simpa only [Encoding.NativeDecode.readNat, List.cons_append, List.drop_succ_cons] using
        ih offset count
    | zero =>
      cases count with
      | zero => rfl
      | succ count =>
        change Nat.bit bit (Encoding.NativeDecode.readNat
          (word ++ List.replicate n false) 0 count) =
          Nat.bit bit (Encoding.NativeDecode.readNat word 0 count)
        rw [ih 0 count]

/-- The source's full semantic word is its fixed prefix followed by blank bits. This identity
is a specification only; the native implementation never allocates this suffix. -/
theorem encoded_initial_eq (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s) (b : ℕ) [NeZero b] :
    List.ofFn (Encoding.encode e (some (initialView (MultiTapePTM.ofDeterministic M) b))) =
      headerWord M e ++
        List.replicate ((k + 1) * b.size + (2 + Encoding.windowBits k b)) false := by
  have hresidue : Encoding.encodeResidue (0 : ZMod b) = fun _ => false := by
    funext j
    simp [Encoding.encodeResidue, equivFin_symm_apply]
  have hheads : Encoding.encodeHeads (fun _ : Option (Fin k) => (0 : ZMod b)) =
      fun _ => false := by
    simp only [Encoding.encodeHeads, hresidue]
    rfl
  have htrack : Encoding.encodeTrack .empty = fun _ => false := by
    funext j
    fin_cases j <;> rfl
  have hcell : Encoding.encodeCell none = fun _ => false := by
    funext j
    fin_cases j <;> rfl
  have hwindows : Encoding.encodeWindows (fun (_ : Fin k) (_ : Fin 3) (_ : ZMod b) => none) =
      fun _ => false := by
    simp only [Encoding.encodeWindows, hcell]
    rfl
  change @List.ofFn Bool
    ((s + 1).size + ((k + 1) * b.size + (2 + Encoding.windowBits k b)) + 1)
    (Fin.cons true (Fin.append (Encoding.encodeState e (some M.q₀))
      (Fin.append (Encoding.encodeHeads (fun _ : Option (Fin k) => (0 : ZMod b)))
        (Fin.append (Encoding.encodeTrack .empty)
          (Encoding.encodeWindows (fun (_ : Fin k) (_ : Fin 3) (_ : ZMod b) => none)))))) = _
  rw [List.ofFn_cons]
  simp only [List.ofFn_fin_append, hheads, htrack, hwindows,
    List.ofFn_const, headerWord, ← List.replicate_add, List.cons_append]


/-- The native fixed-prefix reader returns the existing packed initial-source value. -/
theorem chunk_eq_packBits {r m : ℕ} (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s)
    (b : ℕ) [NeZero b] (hb : Encoding.width k s b ≤ r * m) (j : Fin r) :
    chunk M e (m, j) =
      (Packed.packBits hb
        (Encoding.encode e (some (initialView (MultiTapePTM.ofDeterministic M) b))) j).val := by
  rw [← QueryReplay.SupplierChunk.readNat_ofFn_eq_packBits hb _ j, encoded_initial_eq,
    readNat_append_false]
  rfl

/-- Source padding is the same constant Boolean gate already used by the implicit tree. -/
theorem chunk_eq_codeGate_zero {q r m : ℕ} (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s)
    (w : List Bool) (b : ℕ) [NeZero b] (σ : Schedule k q)
    (hb : Encoding.width k s b ≤ r * m) (j : Fin r)
    (children : Fin (k * 3 + 1) → Fin (Encoding.width k s b) → Bool) :
    chunk M e (m, j) = (Packed.packBits hb
      (codeGate (MultiTapePTM.ofDeterministic M) w b σ
        (Encoding.encode e) (Encoding.decode e) 0 children) j).val := by
  simpa only [codeGate, intervalGate] using chunk_eq_packBits M e b hb j

end Turing.MultiTapePTM.BlockComputation.InitialChunk
