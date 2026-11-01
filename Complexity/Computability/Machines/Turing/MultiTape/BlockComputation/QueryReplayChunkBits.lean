/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.Encoding.NativeDecode
public import Complexity.Computability.TreeEval.Ary.Packed
public import Complexity.Foundations.Data.BitString.List
import Complexity.Foundations.Data.BitString.Binary
import Complexity.Foundations.Data.List.Lookup

/-!
# Numeric chunks of an explicitly stored gate label

The native numeric reader truncates its slice at the end of the actual word. Reading that
short slice as a little-endian number agrees with the existing packed bit-string encoder,
which fills the final partial chunk with zero bits. This is an equality of specifications;
no padded word or runtime power is added to the implementation.
-/

public section

namespace Turing.MultiTapePTM.BlockComputation.QueryReplay.SupplierChunk

open MultiTapeTM Cslib.BitString Cslib.TreeEval.Ary

private theorem ofBits_replicate_false (n : ℕ) :
    ofBits (List.replicate n false) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ, ofBits, List.foldr_cons, ← ofBits, ih]
    rfl

private theorem ofBits_ofFn_ofList (word : List Bool) (n : ℕ) (h : word.length ≤ n) :
    ofBits (List.ofFn (ofList n word)) = ofBits word := by
  induction word generalizing n with
  | nil =>
    have hz : ofList n ([] : List Bool) = fun _ => false := by
      funext i
      simp [ofList]
    rw [hz, List.ofFn_const]
    exact ofBits_replicate_false n
  | cons bit word ih =>
    cases n with
    | zero => simp at h
    | succ n =>
      rw [List.ofFn_succ]
      change Nat.bit bit (ofBits (List.ofFn (ofList n word))) = Nat.bit bit (ofBits word)
      rw [ih n (by simpa using h)]

private theorem ofBits_ofFn {n : ℕ} (bits : Cslib.BitString n) :
    ofBits (List.ofFn bits) = (equivFin n bits).val := by
  rw [← lsbValue_ofFn]
  exact (lsbValue_eq_foldr_bit _).symm

/-- Numeric reads of a complete or partial label chunk agree with the packed encoder.
Missing high-order bits are zero, including when the chunk width itself is zero. -/
theorem readNat_ofFn_eq_packBits {b r m : ℕ} (hb : b ≤ r * m)
    (bits : Fin b → Bool) (j : Fin r) :
    Encoding.NativeDecode.readNat (List.ofFn bits) (j.val * m) m =
      (Packed.packBits hb bits j).val := by
  let slice := ((List.ofFn bits).drop (j.val * m)).take m
  have hlength : slice.length ≤ m := by
    simp only [slice, List.length_take]
    exact Nat.min_le_left _ _
  have hview : ofList m slice = block (zeroExtend (d' := r * m) bits) j := by
    funext i
    change slice.getD i.val false = _
    rw [List.getD_take_drop _ _ i.isLt]
    have hindex : (finProdFinEquiv (j, i) : ℕ) = j.val * m + i.val := by
      simp only [finProdFinEquiv_apply_val]
      ac_rfl
    simp only [block, zeroExtend, hindex]
    by_cases hi : j.val * m + i.val < b
    · simp only [hi, ↓reduceDIte]
      exact List.getD_ofFn_of_lt bits hi false
    · simp only [hi, ↓reduceDIte]
      exact List.getD_eq_default _ _ (by simp only [List.length_ofFn]; omega)
  change ofBits slice = (Packed.packBits hb bits j).val
  rw [← ofBits_ofFn_ofList slice m hlength, hview, ofBits_ofFn]
  rfl

end Turing.MultiTapePTM.BlockComputation.QueryReplay.SupplierChunk
