/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Karn Seth
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Nat.Subtraction
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Nat.Division
public import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeBinaryPrimitives
public import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListMap
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Decoder.Nat

/-!
# Direct certificates for the existing binary subtraction and division algorithms

The word programs and their arithmetic laws are unchanged. Certificates use direct bit, pair,
append and full-prefix fold primitives, retaining binary magnitudes throughout.
-/

@[expose] public section
namespace Turing.MultiTapeTM.ComputableInPolyTime

private theorem digitPairs_polyTime :
    ComputableInPolyTime BinarySub.digitPairs (encPair encNat encNat)
      (encList (encPair encBool encBool)) := by
  have hbits : ComputableInPolyTime Nat.bits encNat encBits := of_eq fun _ => rfl
  have hl := Internal.DecoderWords.unary_degree.computableInPolyTime.comp
    (hbits.comp (fst encNat encNat))
  have hr := Internal.DecoderWords.unary_degree.computableInPolyTime.comp
    (hbits.comp (snd encNat encNat))
  have hadd : ComputableInDegree (fun p : ℕ × ℕ => p.1 + p.2)
      (encPair encUnary encUnary) encUnary 1 1 :=
    (ComputableInDegree.fst encUnary encUnary).append
      (ComputableInDegree.snd encUnary encUnary) (encOut := encUnary)
      (fun _ => by simp only [encUnary_apply, List.replicate_add])
  have hwidth := hadd.computableInPolyTime.comp (hl.prod hr)
  have hi := snd (encPair encNat encNat) encUnary
  have hp := fst (encPair encNat encNat) encUnary
  have hd := (binary_testBit ((fst encNat encNat).comp hp) hi).prod
    (binary_testBit ((snd encNat encNat).comp hp) hi)
  have hmap := mapWithInput (f := fun p i => (p.1.testBit i, p.2.testBit i))
    (range.comp hwidth) hd
  convert hmap using 1
  funext p
  simp only [BinarySub.digitPairs, BinarySub.bits_getD, Function.comp_def]

private theorem subStep_polyTime :
    ComputableInPolyTime (fun p : (Bool × List Bool) × (Bool × Bool) =>
      BinarySub.subStep p.1 p.2)
      (encPair (encPair encBool encBits) (encPair encBool encBool))
      (encPair encBool encBits) := by
  have hs := fst (encPair encBool encBits) (encPair encBool encBool)
  have hd := snd (encPair encBool encBits) (encPair encBool encBool)
  have flags := (of_finite (encIn := encPair encBool (encPair encBool encBool))
    (encOut := encPair encBool encBool) fun p : Bool × (Bool × Bool) =>
      (BinarySub.borrow p.1 p.2.1 p.2.2, p.1 ^^ p.2.1 ^^ p.2.2)).comp (hs.fst'.prod hd)
  have hsnoc : ComputableInDegree (fun p : List Bool × Bool => p.1 ++ [p.2])
      (encPair encBits encBool) encBits 1 1 :=
    (ComputableInDegree.fst encBits encBool).append
      (ComputableInDegree.snd encBits encBool) (encOut := encBits) (fun _ => rfl)
  exact flags.fst'.prod (hsnoc.computableInPolyTime.comp (hs.snd'.prod flags.snd'))

/-- Truncated binary subtraction by the original borrow/digit-pair algorithm. -/
theorem binary_sub : ComputableInPolyTime (fun p : ℕ × ℕ => p.1 - p.2)
    (encPair encNat encNat) encNat := by
  have hfold := foldl' (encA := encPair encBool encBool)
    (encL := encList (encPair encBool encBool)) (encB := encPair encBool encBits)
    (list := BinarySub.digitPairs) (init := fun _ => (false, [])) (step := BinarySub.subStep)
    digitPairs_polyTime (const (false, [])) subStep_polyTime
    (B := fun p => 3 + (encList (encPair encBool encBool) (BinarySub.digitPairs p)).length)
    ((PolyBounded.const 3).add digitPairs_polyTime.polyBounded_length) (by
      intro p i _
      obtain ⟨ds, hout, hlen, _⟩ :=
        BinarySub.foldl_subStep ((BinarySub.digitPairs p).take i) false []
      simp only [length_encPair, encBool_apply, List.length_singleton, encBits_apply,
        hout, List.nil_append, hlen]
      have hl := (List.length_take_le' i (BinarySub.digitPairs p)).trans
        (SizedListEncoding.length_le (encA := encPair encBool encBool)
          (encL := encList (encPair encBool encBool)) (BinarySub.digitPairs p))
      omega)
  have h := ((fst encBool encBits).comp hfold).ite (const 0)
    (bitsToNat.comp ((snd encBool encBits).comp hfold))
  convert h using 1
  funext p
  exact BinarySub.sub_eq p

private theorem divModStep_polyTime :
    ComputableInPolyTime (fun p : (ℕ × (ℕ × ℕ)) × Bool =>
      BinaryDiv.divModStep p.1.1 p.1.2 p.2)
      (encPair (encPair encNat (encPair encNat encNat)) encBool) (encPair encNat encNat) := by
  have hs := fst (encPair encNat (encPair encNat encNat)) encBool
  have hb := hs.fst'
  have hq := hs.snd'.fst'
  have hr := hs.snd'.snd'
  have hd := (of_finite (encIn := encBool) (encOut := encNat)
    fun bit : Bool => if bit then 1 else 0).comp
      (snd (encPair encNat (encPair encNat encNat)) encBool)
  have hr' := binary_add.comp ((binary_add.comp (hr.prod hr)).prod hd)
  have hq' := binary_add.comp (hq.prod hq)
  have hz : ComputableInPolyTime
      (fun p : (ℕ × (ℕ × ℕ)) × Bool => decide (p.1.1 = 0))
      (encPair (encPair encNat (encPair encNat encNat)) encBool) encBool := by
    convert binary_le.comp (hb.prod (const 0)) using 1
    funext p
    simp
  have hle := binary_le.comp (hb.prod hr')
  have hfit := (binary_add.comp (hq'.prod (const 1))).prod
    (binary_sub.comp (hr'.prod hb))
  have h := hz.ite ((const 0).prod hr') (hle.ite hfit (hq'.prod hr'))
  convert h using 1
  funext p
  simp only [BinaryDiv.divModStep, Function.comp_def, two_mul, decide_eq_true_eq]

/-- Quotient and remainder by the original shift-and-subtract binary long division.
The zero-divisor branch is retained; both outputs stay binary. -/
theorem binary_divMod : ComputableInPolyTime (fun p : ℕ × ℕ => (p.1 / p.2, p.1 % p.2))
    (encPair encNat encNat) (encPair encNat encNat) := by
  have hbits : ComputableInPolyTime Nat.bits encNat encBits := of_eq fun _ => rfl
  have hlist := bitsReverse.comp (hbits.comp (fst encNat encNat))
  have hfold := foldlWith (encP := encNat) (encA := encBool) (encL := encBits)
    (encB := encPair encNat encNat) (par := Prod.snd) (list := fun p : ℕ × ℕ => p.1.bits.reverse)
    (init := fun _ => (0, 0)) (step := BinaryDiv.divModStep)
    (snd encNat encNat) hlist (const (0, 0)) divModStep_polyTime
    (B := fun p => 3 * (encPair encNat encNat p).length + 1)
    (((PolyBounded.const 3).mul .self).add (.const 1)) (by
      intro p i _
      have hlen := BinaryDiv.length_encPair_foldl_divModStep_le p.2 (p.1.bits.reverse.take i)
      have htake : (p.1.bits.reverse.take i).length ≤ (encPair encNat encNat p).length := by
        calc (p.1.bits.reverse.take i).length
            ≤ p.1.bits.reverse.length := List.length_take_le' _ _
          _ = (encNat p.1).length := by simp
          _ ≤ (encPair encNat encNat p).length := length_le_encPair_left encNat encNat p
      omega)
  simpa only [BinaryDiv.divMod_eq] using hfold

/-- Binary quotient, with `a / 0 = 0`. This named rule adds no encoding-search alternative. -/
theorem binary_div : ComputableInPolyTime (fun p : ℕ × ℕ => p.1 / p.2)
    (encPair encNat encNat) encNat := binary_divMod.fst'

/-- Binary remainder, with `a % 0 = a`. This named rule adds no encoding-search alternative. -/
theorem binary_mod : ComputableInPolyTime (fun p : ℕ × ℕ => p.1 % p.2)
    (encPair encNat encNat) encNat := binary_divMod.snd'

end Turing.MultiTapeTM.ComputableInPolyTime
