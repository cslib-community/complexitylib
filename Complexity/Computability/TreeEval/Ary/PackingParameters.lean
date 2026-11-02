/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Foundations.Data.Nat.BinarySize
public import Complexity.Foundations.Data.Nat.CeilDiv
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Nat.Bits
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.List.Size
public import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.Bertrand

/-!
# Field parameters and encoded storage for packed Cook–Mertz

For positive fan-in `d` and Boolean value length `b`, choose chunk width `m = (d*b).size`,
chunk count `r = ⌈b/m⌉`, and the least prime `p ≥ d*r*(2^m-1)+2`. The chunk alphabet embeds
in `ZMod p`, and the packed gate's degree is strictly below `p-1`.

Bertrand's postulate bounds the bit length of `p` by `2m+2`. The framed binary list encoding
of `(d+1)*r` residues therefore has length at most `9*(d+1)*(b+m)`. For fixed fan-in this is
affine in `b`; no uniform constant independent of `d` is asserted.

## Main definitions

* `Cslib.TreeEval.Ary.Packed.chunkWidth`, `Cslib.TreeEval.Ary.Packed.chunkCount`: chunk sizes.
* `Cslib.TreeEval.Ary.Packed.gateDegree`: the packed interpolation degree bound.
* `Cslib.TreeEval.Ary.Packed.fieldModulus`: a sufficient prime modulus.
* `Cslib.TreeEval.Ary.Packed.alphabetEmbedding`: the chunk alphabet in that prime field.

## Main results

* `Cslib.TreeEval.Ary.Packed.gateDegree_lt`: the strict unmasking threshold.
* `Cslib.TreeEval.Ary.Packed.fieldModulus_size_le`: field elements use at most `2m+2` bits.
* `Cslib.TreeEval.Ary.Packed.length_encList_residues_le`: encoded global-register storage.

## References

* [R. Williams, *Simulating Time With Square-Root Space*][Williams2025], Appendix A,
  equation (6) and the final storage calculation. The source uses characteristic-two fields;
  this prime-field parameter choice is an original variant for the signed unmasking identity.

These are parameter and representation-length bounds. No native prime-search, arithmetic,
packed evaluator or implicit gate-query space certificate is proved here.
-/

public section

namespace Cslib.TreeEval.Ary.Packed

/-- Bits per chunk: the binary length of the total Boolean input width of a gate. -/
@[expose] def chunkWidth (d b : ℕ) : ℕ := (d * b).size

/-- Number of chunks, with a possibly incomplete final chunk. -/
@[expose] def chunkCount (d b : ℕ) : ℕ := b ⌈/⌉ chunkWidth d b

/-- Total-degree bound for interpolation on the chunk alphabet. -/
@[expose] def gateDegree (d b : ℕ) : ℕ := d * chunkCount d b * (2 ^ chunkWidth d b - 1)

/-- The least prime strictly above the packed degree plus one. Its search cost is not certified. -/
@[expose] def fieldModulus (d b : ℕ) : ℕ :=
  Nat.find (Nat.exists_infinite_primes (gateDegree d b + 2))

/-- The chosen modulus is prime. -/
theorem fieldModulus_prime (d b : ℕ) : (fieldModulus d b).Prime :=
  (Nat.find_spec (Nat.exists_infinite_primes (gateDegree d b + 2))).2

/-- Two units of slack keep the degree strictly below the unit-group order. -/
theorem gateDegree_add_two_le (d b : ℕ) : gateDegree d b + 2 ≤ fieldModulus d b :=
  (Nat.find_spec (Nat.exists_infinite_primes (gateDegree d b + 2))).1

/-- The sufficient degree threshold is strict, including the smallest parameters. -/
theorem gateDegree_lt (d b : ℕ) : gateDegree d b < fieldModulus d b - 1 := by
  have := gateDegree_add_two_le d b
  omega

/-- Bertrand's postulate bounds the least sufficient prime. -/
theorem fieldModulus_le (d b : ℕ) : fieldModulus d b ≤ 2 * (gateDegree d b + 1) := by
  obtain ⟨q, hq, hlo, hhi⟩ :=
    Nat.exists_prime_lt_and_le_two_mul (gateDegree d b + 1) (by omega)
  have hmin := Nat.find_min' (Nat.exists_infinite_primes (gateDegree d b + 2))
    (show gateDegree d b + 2 ≤ q ∧ q.Prime from ⟨by omega, hq⟩)
  exact hmin.trans hhi

variable {d b : ℕ}

/-- Nonempty gates and values have positive chunk width. -/
theorem chunkWidth_pos (hd : 0 < d) (hb : 0 < b) : 0 < chunkWidth d b :=
  Nat.size_pos.mpr (Nat.mul_pos hd hb)

/-- The chunks cover all bits of the value. -/
theorem le_chunkCount_mul (hd : 0 < d) (hb : 0 < b) :
    b ≤ chunkCount d b * chunkWidth d b :=
  Nat.le_ceilDiv_mul (chunkWidth_pos hd hb)

/-- Padding adds less than one chunk. -/
theorem chunkCount_mul_lt (hd : 0 < d) (hb : 0 < b) :
    chunkCount d b * chunkWidth d b < b + chunkWidth d b :=
  Nat.ceilDiv_mul_lt (chunkWidth_pos hd hb)

/-- Positive-width chunks are no more numerous than the original bits. -/
theorem chunkCount_le (hd : 0 < d) (hb : 0 < b) : chunkCount d b ≤ b := by
  apply (Nat.ceilDiv_le_iff (chunkWidth_pos hd hb)).mpr
  have := chunkWidth_pos hd hb
  nlinarith

/-- A nonempty value occupies at least one chunk. -/
theorem chunkCount_pos (hd : 0 < d) (hb : 0 < b) : 0 < chunkCount d b := by
  have := le_chunkCount_mul hd hb
  by_contra hn
  have hz : chunkCount d b = 0 := by omega
  rw [hz, Nat.zero_mul] at this
  omega

/-- The whole chunk alphabet fits below the modulus, not just the encoded Boolean values. -/
theorem alphabetSize_lt (hd : 0 < d) (hb : 0 < b) :
    2 ^ chunkWidth d b < fieldModulus d b := by
  have hprod : 1 ≤ d * chunkCount d b := Nat.mul_pos hd (chunkCount_pos hd hb)
  have hpow : 1 ≤ 2 ^ chunkWidth d b := Nat.one_le_pow _ _ (by decide)
  have hdeg := Nat.mul_le_mul_right (2 ^ chunkWidth d b - 1) hprod
  have hp := gateDegree_add_two_le d b
  simp only [Nat.one_mul] at hdeg
  change 2 ^ chunkWidth d b - 1 ≤ gateDegree d b at hdeg
  omega

/-- Embed a chunk as its unsigned value in the selected prime field. -/
@[expose] def alphabetEmbedding (hd : 0 < d) (hb : 0 < b) :
    Fin (2 ^ chunkWidth d b) ↪ ZMod (fieldModulus d b) where
  toFun a := a.val
  inj' := by
    have : NeZero (fieldModulus d b) := ⟨(fieldModulus_prime d b).ne_zero⟩
    intro a a' heq
    have heq' := congrArg ZMod.val heq
    have ha := a.isLt.trans (alphabetSize_lt hd hb)
    have ha' := a'.isLt.trans (alphabetSize_lt hd hb)
    simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt ha', Fin.val_inj]
      using heq'

/-- The prime field has at most twice the chunk width plus two bits per residue. -/
theorem fieldModulus_size_le (hd : 0 < d) (hb : 0 < b) :
    (fieldModulus d b).size ≤ 2 * chunkWidth d b + 2 := by
  have hr := chunkCount_le hd hb
  have hlt : d * b < 2 ^ chunkWidth d b := Nat.lt_size_self (d * b)
  have hdegree : gateDegree d b < (2 ^ chunkWidth d b) ^ 2 := by
    have hpow : 0 < 2 ^ chunkWidth d b := Nat.two_pow_pos _
    have hmul := Nat.mul_le_mul_left d hr
    calc
      gateDegree d b ≤ (d * chunkCount d b) * 2 ^ chunkWidth d b :=
        Nat.mul_le_mul_left _ (Nat.sub_le _ _)
      _ < 2 ^ chunkWidth d b * 2 ^ chunkWidth d b :=
        Nat.mul_lt_mul_of_pos_right (hmul.trans_lt hlt) hpow
      _ = (2 ^ chunkWidth d b) ^ 2 := (pow_two _).symm
  have hp := fieldModulus_le d b
  apply Nat.size_le.mpr
  rw [Nat.mul_comm 2 (chunkWidth d b), pow_add, pow_mul]
  norm_num only [Nat.reducePow]
  nlinarith

/-- One packed register has linear payload size, including a partial final chunk. -/
theorem chunkCount_mul_fieldModulus_size_le (hd : 0 < d) (hb : 0 < b) :
    chunkCount d b * (fieldModulus d b).size ≤ 4 * (b + chunkWidth d b) := by
  have hm := chunkWidth_pos hd hb
  have hp := fieldModulus_size_le hd hb
  have hr := chunkCount_mul_lt hd hb
  calc
    chunkCount d b * (fieldModulus d b).size ≤
        chunkCount d b * (4 * chunkWidth d b) := Nat.mul_le_mul_left _ (by omega)
    _ ≤ 4 * (b + chunkWidth d b) := by nlinarith

/-- Actual framed binary storage for the `d+1` global registers. All residues, including zero,
and their list framing are charged. Any list with at most the full register count is allowed. -/
theorem length_encList_residues_le (hd : 0 < d) (hb : 0 < b) (values : List ℕ)
    (hlen : values.length ≤ (d + 1) * chunkCount d b)
    (hres : ∀ v ∈ values, v < fieldModulus d b) :
    (Turing.MultiTapeTM.encList Turing.MultiTapeTM.encNat values).length ≤
      9 * (d + 1) * (b + chunkWidth d b) := by
  have hsize (v : ℕ) (hv : v ∈ values) :
      (Turing.MultiTapeTM.encNat v).length ≤ (fieldModulus d b).size := by
    rw [Turing.MultiTapeTM.encNat_apply, Nat.size_eq_bits_len]
    exact Nat.size_le_size (hres v hv).le
  have hlist := Turing.MultiTapeTM.length_encList_le Turing.MultiTapeTM.encNat values hsize
  have hp := fieldModulus_size_le hd hb
  have hm := chunkWidth_pos hd hb
  have hr := chunkCount_mul_lt hd hb
  calc
    _ ≤ values.length * (2 * (fieldModulus d b).size + 1) := hlist
    _ ≤ ((d + 1) * chunkCount d b) * (9 * chunkWidth d b) :=
      Nat.mul_le_mul hlen (by omega)
    _ ≤ 9 * (d + 1) * (b + chunkWidth d b) := by nlinarith

/-- For a fixed machine's fan-in, the width term is affine in the value length. -/
theorem chunkWidth_le (d b : ℕ) : chunkWidth d b ≤ d.size + b := by
  have hb : b.size ≤ b := Nat.size_le.mpr (Nat.lt_two_pow_self (n := b))
  exact (Nat.size_mul_le d b).trans (by omega)

/-- An explicit affine bound on the encoded global registers when the fan-in is fixed. -/
theorem length_encList_residues_le_affine (hd : 0 < d) (hb : 0 < b) (values : List ℕ)
    (hlen : values.length ≤ (d + 1) * chunkCount d b)
    (hres : ∀ v ∈ values, v < fieldModulus d b) :
    (Turing.MultiTapeTM.encList Turing.MultiTapeTM.encNat values).length ≤
      18 * (d + 1) * b + 9 * (d + 1) * d.size := by
  have h := length_encList_residues_le hd hb values hlen hres
  have hm := chunkWidth_le d b
  nlinarith

end Cslib.TreeEval.Ary.Packed
