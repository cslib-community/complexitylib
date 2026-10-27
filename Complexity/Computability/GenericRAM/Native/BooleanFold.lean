/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.GenericRAM.Native.IndexFold
public import Complexity.Foundations.Data.BitString.Binary
public import Complexity.Foundations.Data.BitString.Enumeration
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListMap
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeNatFrontends
import Mathlib.Data.List.Fold

/-!
# Streaming local Boolean assignments

The runtime dimension is unary and the current index is binary. The existing `lowBits` decoder
returns exactly that many bits, padding or truncating on arbitrary indices. Its certificate below
is derived from direct native list/bit primitives; no legacy polynomial-time bridge is used.
The assignment list in the correctness specification is not constructed by the streaming loop.

This is the local Boolean-vector component of the enumeration in [OpenAI2026ETH], Lemma 3.2 and
Proposition 3.4, pp. 22–26. It is not a mixed-radix or subset-pair enumerator, and gives no
polynomial-time bound for a whole loop with exponentially many rounds.
-/

@[expose] public section

namespace Cslib.GenericRAM.BooleanFold

open Turing.MultiTapeTM
open Cslib.BitString

private theorem unframeBits :
    ComputableInPolyTime (fun l : List Bool => l) (encList encBool) encBits := by
  have hstep : ComputableInPolyTime (fun p : List Bool × Bool => p.2 :: p.1)
      (encPair encBits encBool) encBits :=
    ComputableInPolyTime.bitsCons (ComputableInPolyTime.snd encBits encBool)
      (ComputableInPolyTime.fst encBits encBool)
  have hfold := ComputableInPolyTime.foldl' (encA := encBool) (encL := encList encBool)
    (encB := encBits) (list := id) (init := fun _ => []) (step := fun acc bit => bit :: acc)
    ComputableInPolyTime.id' (ComputableInPolyTime.const []) hstep
    (B := fun l => (encList encBool l).length) .self (by
      intro l i _
      change ((l.take i).foldl (flip List.cons) []).length ≤ _
      rw [List.foldl_cons_nil, List.length_reverse]
      exact (List.length_take_le' _ _).trans
        (SizedListEncoding.length_le (encA := encBool) (encL := encList encBool) l))
  have h := ComputableInPolyTime.bitsReverse.comp hfold
  simpa only [Function.comp_def, List.reverse_foldl, id_eq] using h

/-- The fixed decoder reads its runtime width in unary and its runtime index in binary.
The actual machine has polynomial time and charged workspace in their complete pair encoding. -/
theorem decoder_polyTime :
    ComputableInPolyTime (fun p : ℕ × ℕ => lowBits p.1 p.2)
      (encPair encUnary encNat) encBits := by
  have hw := ComputableInPolyTime.fst encUnary encNat
  have hv := ComputableInPolyTime.snd encUnary encNat
  have hl := ComputableInPolyTime.range.comp hw
  have hf : ComputableInPolyTime (fun p : (ℕ × ℕ) × ℕ => p.1.2.testBit p.2)
      (encPair (encPair encUnary encNat) encUnary) encBool :=
    ComputableInPolyTime.binary_testBit
      (hv.comp (ComputableInPolyTime.fst (encPair encUnary encNat) encUnary))
      (ComputableInPolyTime.snd (encPair encUnary encNat) encUnary)
  have hm := ComputableInPolyTime.mapWithInput (f := fun p i => p.2.testBit i)
    (encB := encBool) hl hf
  simpa only [lowBits, Function.comp_def] using unframeBits.comp hm

/-- Bounds selected from the direct fixed decoder machine; the machine is uniform in both
runtime width and index. This is not a separate finite machine for every width. -/
noncomputable def decoder :
    NativeCertificate (fun p : ℕ × ℕ => lowBits p.1 p.2)
      (encPair encUnary encNat) encBits :=
  NativeCertificate.ofPolyTime decoder_polyTime

/-- Both selected decoder resource bounds are polynomial in the full encoded input length. -/
theorem decoder_isPolynomial : decoder.IsPolynomial :=
  NativeCertificate.ofPolyTime_isPolynomial decoder_polyTime

/-- Each valid binary index decodes to its word in the existing finite enumeration order. -/
theorem lowBits_eq_word (n : ℕ) (j : Fin (2 ^ n)) :
    lowBits n j = List.ofFn ((equivFin n).symm j) := by
  rw [lowBits_eq_ofFn]
  congr 1
  funext i
  exact (equivFin_symm_apply j i).symm

/-- The conceptual sequence of decoded indices is exactly the old materializing enumeration.
Only this specification uses the list of all indices. -/
theorem decoded_range_eq_enumList (n : ℕ) :
    (List.range (2 ^ n)).map (lowBits n) = enumList n := by
  apply List.ext_getElem (by simp)
  intro i hi hi'
  simp only [List.getElem_map, List.getElem_range, enumList_eq_ofFn, List.getElem_ofFn]
  exact lowBits_eq_word n ⟨i, by simpa using hi⟩

end Cslib.GenericRAM.BooleanFold
