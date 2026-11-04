/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Frontier.TensorNetwork.BinaryDigits
public import Complexity.Computability.Circuit.Frontier.TensorNetwork.DescribedContraction
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Polynomial
import Mathlib.Algebra.Order.BigOperators.Group.List

/-!
# Computing binary-digit tensor entries in polynomial time

The evaluator reads a natural table entry at the little-endian index of its port word and
returns its binary digits as natural coefficients. The table values and the index are in binary;
out-of-range indices return zero. Together with polynomial-time Horner evaluation at `2`, this
supplies the input and output maps for exact natural counting through truncated contraction.

## Main results

* `ExplicitTensorNetwork.binaryEntry_polyTime`: the uniform evaluator certificate.
* `ExplicitTensorNetwork.binaryTableBound`: a positive bit-length bound read from all tables.
* `ExplicitTensorNetwork.size_le_binaryTableBound`: every stored entry satisfies that bound.
* `ExplicitTensorNetwork.binaryTableBound_polyTime`: computing the bound in unary.
* `ExplicitTensorNetwork.binaryTableBound_le`: bounding it from table and entry lengths.
-/

public section

namespace Cslib.Circuits.Frontier.ExplicitTensorNetwork

open Turing.MultiTapeTM

/-- The binary-digit evaluator for an arbitrary natural table is polynomial-time. -/
theorem binaryEntry_polyTime :
    ComputableInPolyTime (fun q : List ℕ × List Bool => binaryEntry q.1 q.2)
      (encPair (encList encNat) encBits) (encList encNat) := by
  have hindex := ComputableInPolyTime.bitsBinaryValue.comp
    (ComputableInPolyTime.bitsReverse.comp (ComputableInPolyTime.snd (encList encNat) encBits))
  have hentry := ComputableInPolyTime.listGetD_binary (encA := encNat)
    (encL := encList encNat) 0 (ComputableInPolyTime.fst (encList encNat) encBits) hindex
  simpa only [binaryEntry, entry, BitString.lsbValue_eq_binaryValue_reverse,
    Function.comp_def] using
    ComputableInPolyTime.binary_digitCoeffs.comp hentry

/-- One more than the encoded length of all table entries. It is a positive uniform bound on
every entry's bit length, and can be computed from the explicit input. -/
@[expose] def binaryTableBound (G : ExplicitTensorNetwork ℕ) : ℕ :=
  (encList encNat (G.vertices.flatMap Prod.snd)).length + 1

/-- The automatic table bound is positive, including when there are no entries. -/
theorem binaryTableBound_pos (G : ExplicitTensorNetwork ℕ) : 0 < G.binaryTableBound :=
  Nat.zero_lt_succ _

/-- Every stored natural has bit length at most the automatic bound. -/
theorem size_le_binaryTableBound (G : ExplicitTensorNetwork ℕ)
    {v : List ℕ × List ℕ} (hv : v ∈ G.vertices) {n : ℕ} (hn : n ∈ v.2) :
    n.size ≤ G.binaryTableBound := by
  have h := length_le_encList_of_mem encNat (List.mem_flatMap.mpr ⟨v, hv, hn⟩)
  simp only [encNat_apply, Nat.size_eq_bits_len] at h
  exact h.trans (Nat.le_succ _)

/-- A table-length bound and an entry-bit bound control the entire encoded table list. -/
theorem binaryTableBound_le {G : ExplicitTensorNetwork ℕ} {M W : ℕ}
    (hM : ∀ v ∈ G.vertices, v.2.length ≤ M)
    (hW : ∀ v ∈ G.vertices, ∀ n ∈ v.2, n.size ≤ W) :
    G.binaryTableBound ≤ G.vertices.length * M * (2 * W + 1) + 1 := by
  have hlen : (G.vertices.flatMap Prod.snd).length ≤ G.vertices.length * M := by
    rw [List.length_flatMap]
    refine (List.sum_le_length_nsmul _ M fun n hn => ?_).trans_eq ?_
    · obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hn
      exact hM v hv
    · simp only [List.length_map, nsmul_eq_mul, Nat.cast_id]
  have henc := length_encList_le encNat (G.vertices.flatMap Prod.snd) (b := W) (by
    intro n hn
    obtain ⟨v, hv, hn⟩ := List.mem_flatMap.mp hn
    simpa only [encNat_apply, Nat.size_eq_bits_len] using hW v hv n hn)
  exact Nat.add_le_add_right
    (henc.trans (Nat.mul_le_mul_right _ hlen)) 1

/-- The automatic bound is computable in unary in polynomial time. -/
theorem binaryTableBound_polyTime :
    ComputableInPolyTime binaryTableBound (DescribedNetwork.encDescribed (encList encNat))
      encUnary := by
  have htables : ComputableInPolyTime
      (fun G : ExplicitTensorNetwork ℕ => G.vertices.flatMap Prod.snd)
      (DescribedNetwork.encDescribed (encList encNat)) (encList encNat) :=
    ComputableInPolyTime.flatMapWithInput DescribedNetwork.vertices_polyTime
      ((ComputableInPolyTime.snd (encList encNat) (encList encNat)).comp
        (ComputableInPolyTime.snd _ _))
  exact ComputableInPolyTime.unary_succ.comp
    ((ComputableInPolyTime.encoding_length (encList encNat)).comp htables)

/-- Using the automatic bit bound makes the exact recovery statement unconditional. -/
theorem evalCoeffList_truncContraction_binaryTableBound (G : ExplicitTensorNetwork ℕ) :
    Polynomial.evalCoeffList 2
      (G.truncContraction binaryEntry (G.binaryPrecision G.binaryTableBound)
        (G.binaryDegreeBound G.binaryTableBound + 1)) = G.contraction :=
  evalCoeffList_truncContraction_binaryEntry fun _ hv _ hn => G.size_le_binaryTableBound hv hn

end Cslib.Circuits.Frontier.ExplicitTensorNetwork
