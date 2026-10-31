/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.TreeEval.Ary.CookMertz
public import Complexity.Foundations.Data.BitString.Block
public import Complexity.Foundations.Data.BitString.Prefix
public import Complexity.Foundations.Data.Code.LowDegreeExtension.UnitSum

/-!
# Packed gate extensions for Cook–Mertz

Bit strings are grouped into chunks and embedded in a finite field, so one register coordinate
can hold several bits. A final partial chunk is zero-padded. The gate extension interpolates on
the chunk alphabet rather than separately on each bit.

This is the algebraic packing step of [Williams2025], Appendix A, equation (6). The field may
have arbitrary characteristic: signed recursive calls and unit sums replace the source's
characteristic-two cancellations. With `r` chunks and alphabet `H`, the strict degree condition
is `d * r * (|H| - 1) < |K| - 1`.

## Main definitions

* `Cslib.TreeEval.Ary.Packed.packBits`, `Cslib.TreeEval.Ary.Packed.unpackBits`: packing and
  decoding a bit string, allowing a final partial chunk.
* `Cslib.TreeEval.Ary.Packed.gateExtension`: interpolation on the packed alphabet.

## Main results

* `Cslib.TreeEval.Ary.Packed.unpackBits_packBits`: decoding recovers the original bits.
* `Cslib.TreeEval.Ary.Packed.sum_units_gateExtension`: packed gates satisfy unmasking.
* `Cslib.TreeEval.Ary.Packed.procWith_gateExtension_eq`: packed procedure correctness.

## Scope

The results here establish algebraic correctness only. They do not certify native packing,
implicit gate queries, the refined space bound, or Williams's time-to-space simulation.
-/

public section

namespace Cslib.TreeEval.Ary.Packed

open Cslib.BitString

/-- Read an exactly aligned bit string as `r` chunks of `m` bits. -/
@[expose] def pack {r m : ℕ} (v : Fin (r * m) → Bool) : Fin r → Fin (2 ^ m) :=
  fun j => equivFin m (block v j)

/-- Concatenate the binary representations of the chunks. -/
@[expose] def unpack {r m : ℕ} (v : Fin r → Fin (2 ^ m)) : Fin (r * m) → Bool :=
  blocksEquiv.symm fun j => (equivFin m).symm (v j)

/-- Chunking preserves every bit, including zero-valued chunks. -/
@[simp] theorem unpack_pack {r m : ℕ} (v : Fin (r * m) → Bool) : unpack (pack v) = v := by
  simp only [unpack, pack, Equiv.symm_apply_apply]
  exact blocksEquiv.symm_apply_apply v

/-- All tuples of chunks are valid aligned encodings. -/
@[simp] theorem pack_unpack {r m : ℕ} (v : Fin r → Fin (2 ^ m)) : pack (unpack v) = v := by
  funext j
  simp [pack, unpack]

/-- Pack a bit string after zero-padding a final partial chunk. -/
@[expose] def packBits {b r m : ℕ} (_hb : b ≤ r * m) (v : Fin b → Bool) :
    Fin r → Fin (2 ^ m) := pack (zeroExtend v)

/-- Decode the original prefix of a padded chunk tuple. -/
@[expose] def unpackBits {b r m : ℕ} (hb : b ≤ r * m) (v : Fin r → Fin (2 ^ m)) :
    Fin b → Bool := restrictBitsAddHom hb (unpack v)

/-- Decoding padded chunks recovers the original bit string. -/
@[simp] theorem unpackBits_packBits {b r m : ℕ} (hb : b ≤ r * m) (v : Fin b → Bool) :
    unpackBits hb (packBits hb v) = v := by
  simp [unpackBits, packBits]

variable {K H : Type*} [Field K] [Fintype H] [DecidableEq H] {b d r : ℕ}

/-- Extend a Boolean gate after encoding each value in `r` alphabet symbols. On symbols outside
the encoding's image, the caller's decoder determines a total table. -/
noncomputable def gateExtension (h : H ↪ K) (encode : (Fin b → Bool) → Fin r → H)
    (decode : (Fin r → H) → Fin b → Bool) (f : Gate d b)
    (x : Fin d → Fin r → K) (i : Fin r) : K :=
  Code.lowDegreeExtension h
    (fun z => h (encode (f fun j => decode (blocksEquiv z j)) i))
    (blocksEquiv.symm x)

/-- On encoded child values the gate extension agrees with the encoded gate output. -/
theorem gateExtension_embed (h : H ↪ K) (encode : (Fin b → Bool) → Fin r → H)
    (decode : (Fin r → H) → Fin b → Bool) (hdecode : Function.LeftInverse decode encode)
    (f : Gate d b) (v : Fin d → Fin b → Bool) (i : Fin r) :
    gateExtension h encode decode f (fun j k => h (encode (v j) k)) i =
      h (encode (f v) i) := by
  change Code.lowDegreeExtension h _
    (fun p => h (blocksEquiv.symm (fun j => encode (v j)) p)) = _
  rw [Code.lowDegreeExtension_apply_embed]
  simp only [Equiv.apply_symm_apply]
  exact congrArg (fun w => h (encode (f w) i)) (funext fun j => hdecode (v j))

variable [Fintype K]

/-- Packed interpolation satisfies the signed unmasking law needed by Cook–Mertz, with only
`d*r` field coordinates and degree at most `d*r*(|H|-1)`. -/
theorem sum_units_gateExtension [DecidableEq K] (h : H ↪ K) (encode : (Fin b → Bool) → Fin r → H)
    (decode : (Fin r → H) → Fin b → Bool) (hdecode : Function.LeftInverse decode encode)
    (hD : d * r * (Fintype.card H - 1) < Fintype.card K - 1)
    (f : Gate d b) (τ : Fin d → Fin r → K) (v : Fin d → Fin b → Bool) (i : Fin r) :
    ∑ u : Kˣ, gateExtension h encode decode f
      (fun j k => (u : K) * τ j k + h (encode (v j) k)) i =
        -h (encode (f v) i) := by
  classical
  have hs := Code.sum_units_lowDegreeExtension_mul_add h
    (fun z => h (encode (f fun j => decode (blocksEquiv z j)) i)) hD
    (blocksEquiv.symm τ) (blocksEquiv.symm fun j => encode (v j))
  change (∑ u : Kˣ, Code.lowDegreeExtension h
    (fun z => h (encode (f fun j => decode (blocksEquiv z j)) i))
    (fun p => (u : K) * blocksEquiv.symm τ p +
      h (blocksEquiv.symm (fun j => encode (v j)) p))) = _
  rw [hs]
  simp only [Equiv.apply_symm_apply]
  exact congrArg (fun w => -h (encode (f w) i)) (funext fun j => hdecode (v j))

/-- The Cook–Mertz procedure on packed registers adds the encoded root value and restores every
other register. The representation need only have a left inverse, so a partial last chunk is
allowed. This is an algebraic specification, without a native-machine space claim. -/
theorem procWith_gateExtension_eq (h : H ↪ K)
    (encode : (Fin b → Bool) → Fin r → H)
    (decode : (Fin r → H) → Fin b → Bool) (hdecode : Function.LeftInverse decode encode)
    (hD : d * r * (Fintype.card H - 1) < Fintype.card K - 1)
    {us : List Kˣ} (hnd : us.Nodup) (hmem : ∀ u, u ∈ us)
    {height : ℕ} (T : Tree d b height) (c : K) (t : Fin (d + 1)) (S : State K d r) :
    procWith (fun v i => h (encode v i)) (gateExtension h encode decode) us T c t S =
      Function.update S t (S t + c • fun i => h (encode T.eval i)) := by
  classical
  exact procWith_eq _ _ (fun f v τ i => sum_units_gateExtension h encode decode hdecode hD f τ v i)
    hnd hmem T c t S

end Cslib.TreeEval.Ary.Packed
