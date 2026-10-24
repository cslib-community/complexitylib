/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Combinatorics.LineCode.Basic
public import Cslib.Foundations.Data.BitString
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Ring.BooleanRing
public import Mathlib.Data.Fintype.Prod
import Complexity.Foundations.Data.BitString.Basic
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.Group.Equiv.Basic

/-!
# Packing a Boolean function into line-parity codes

Split the inputs of `f : BooleanFunction (p + w)` into a prefix `a` of `p` bits and a suffix `z`
of `w` bits. An injection `place` assigns every prefix a code copy `c`, an information point `u`
and a bit position `r`. For each copy and suffix, the information symbol at `u` is the field
element whose bit `r` is `f (Fin.append a z)` for the prefix `a` placed at `(c, u, r)`, and false
at unplaced bits (`packedBit`). The line-parity code extends these symbols to a codeword
(`codeword`), and every bit of every codeword value is a Boolean function of the suffix alone
(`resource`).

Summing the resources of a request along any punctured line through its information point
recovers the requested value (`sum_resource`): the codeword value at the point is the sum along
the line, `bits` is additive, and the code is systematic on its information set. A request is
therefore answered from `s = Fintype.card K - 1` resource values (`succ_eq_card`), where
`Fintype.card K = 2 ^ b` (`card_eq_two_pow`).

## Main definitions

* `Cslib.Circuits.Boolean.MassProduction.Pipeline.packedBit`: the packed information bits.
* `Cslib.Circuits.Boolean.MassProduction.Pipeline.codeword`: the codeword of a copy and suffix.
* `Cslib.Circuits.Boolean.MassProduction.Pipeline.resource`: a codeword bit as a function of the
  suffix.

## Main results

* `Cslib.Circuits.Boolean.MassProduction.Pipeline.sum_resource`: recovery along a line.
* `Cslib.Circuits.Boolean.MassProduction.Pipeline.succ_eq_two_pow`: `s + 1 = 2 ^ b` when the
  nonzero scalars are numbered by `Fin s` and the field elements are bit strings of length `b`.

## References

* Adapted from MassProduction/HighRate/BooleanRecovery.lean in
  [S. Schlesinger, *Boolean circuit mass production formalization*][Schlesinger2026MassProduction].
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.MassProduction.Pipeline

open Finset LineCode

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K] {ℓ b s p w copies : ℕ}

/-- Bit `r` of the information symbol at `u` in copy `c` for the suffix `z`: the value of `f` at
the prefix placed at `(c, u, r)`, and `false` if no prefix is placed there. -/
def packedBit (C : LineCode K ℓ) (place : BitString p ↪ Fin copies × C.info × Fin b)
    (f : BooleanFunction (p + w)) (z : BitString w) (c : Fin copies) (u : Fin ℓ → K)
    (r : Fin b) : Bool :=
  decide (∃ a, (place a).1 = c ∧ ((place a).2.1 : Fin ℓ → K) = u ∧ (place a).2.2 = r ∧
    f (Fin.append a z) = true)

/-- The codeword of copy `c` for the suffix `z`, extending the packed information symbols. -/
def codeword (bits : K ≃+ BitString b) (C : LineCode K ℓ)
    (place : BitString p ↪ Fin copies × C.info × Fin b) (f : BooleanFunction (p + w))
    (z : BitString w) (c : Fin copies) : (Fin ℓ → K) → K :=
  C.extend fun u => bits.symm (packedBit C place f z c u)

/-- The resource of copy `c`, point `y` and bit `r`: bit `r` of the codeword value at `y`, as a
function of the suffix. -/
def resource (bits : K ≃+ BitString b) (C : LineCode K ℓ)
    (place : BitString p ↪ Fin copies × C.info × Fin b) (f : BooleanFunction (p + w))
    (c : Fin copies) (y : Fin ℓ → K) (r : Fin b) : BooleanFunction w :=
  fun z => bits (codeword bits C place f z c y) r

variable {C : LineCode K ℓ} {place : BitString p ↪ Fin copies × C.info × Fin b}
  {f : BooleanFunction (p + w)}

/-- The packed bit at a placed prefix is the value of `f` there. -/
private theorem packedBit_place (a : BitString p) (z : BitString w) :
    packedBit C place f z (place a).1 (place a).2.1 (place a).2.2 = f (Fin.append a z) := by
  apply Bool.eq_iff_iff.mpr
  rw [packedBit, decide_eq_true_iff]
  constructor
  · rintro ⟨a', hc, hu, hr, hf⟩
    have : place a' = place a := Prod.ext hc (Prod.ext (Subtype.ext hu) hr)
    rwa [← place.injective this]
  · exact fun hf => ⟨a, rfl, rfl, rfl, hf⟩

/-- Numbering the nonzero scalars by `scalar` sums over the punctured line. -/
private theorem sum_scalar {M : Type*} [AddCommMonoid M] (scalar : Fin s ≃ {c : K // c ≠ 0})
    (g : K → M) : ∑ j, g (scalar j : K) = ∑ c ∈ (univ : Finset K).erase 0, g c := by
  rw [Finset.sum_subtype ((univ : Finset K).erase 0) (p := fun c => c ≠ 0)
    (fun c => by simp only [Finset.mem_erase, Finset.mem_univ, and_true]) g]
  exact Equiv.sum_comp scalar (fun c => g c)

/-- **Recovery along a line.** The resources of the request `(a, z)`, at the points
`u + scalar j • v` of a punctured line through its information point `u`, sum to
`f (Fin.append a z)`. -/
theorem sum_resource (bits : K ≃+ BitString b) (scalar : Fin s ≃ {c : K // c ≠ 0})
    (a : BitString p) (z : BitString w) {v : Fin ℓ → K} (hv : v ≠ 0) :
    ∑ j, resource bits C place f (place a).1 ((place a).2.1 + (scalar j : K) • v)
      (place a).2.2 z = f (Fin.append a z) := by
  simp only [resource]
  rw [← Finset.sum_apply, ← map_sum, sum_scalar scalar
      (fun c => codeword bits C place f z (place a).1 ((place a).2.1 + c • v)),
    codeword, C.sum_extend _ _ _ hv, C.extend_eq _ _ (place a).2.1.2, AddEquiv.apply_symm_apply]
  exact packedBit_place a z

section Card

variable {K : Type*}

/-- A type whose elements are the bit strings of length `b` has `2 ^ b` elements. -/
theorem card_eq_two_pow [Add K] [Fintype K] (bits : K ≃+ BitString b) :
    Fintype.card K = 2 ^ b := by
  rw [Fintype.card_congr bits.toEquiv, BitString.card]

/-- Numbering the nonzero elements by `Fin s` leaves `s + 1` elements. -/
theorem succ_eq_card [Zero K] [Fintype K] (scalar : Fin s ≃ {c : K // c ≠ 0}) :
    s + 1 = Fintype.card K := by
  classical
  have h := Fintype.card_congr scalar
  rw [Fintype.card_fin, Fintype.card_subtype_compl, Fintype.card_subtype_eq] at h
  have : 0 < Fintype.card K := Fintype.card_pos_iff.mpr ⟨0⟩
  omega

/-- The sizes agree: `s + 1 = 2 ^ b`. -/
theorem succ_eq_two_pow [Add K] [Zero K] (bits : K ≃+ BitString b)
    (scalar : Fin s ≃ {c : K // c ≠ 0}) : s + 1 = 2 ^ b := by
  let := Fintype.ofEquiv _ bits.symm.toEquiv
  exact (succ_eq_card scalar).trans (card_eq_two_pow bits)

end Card

end Cslib.Circuits.Boolean.MassProduction.Pipeline
