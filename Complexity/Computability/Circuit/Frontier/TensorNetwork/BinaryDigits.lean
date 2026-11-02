/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Frontier.TensorNetwork.Truncated
public import Complexity.Foundations.Data.Polynomial.BinaryDigits
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.List.GetD

/-!
# Recovering natural tensor contractions from binary-digit polynomials

Replace each natural table entry by the polynomial of its binary digits. Its value at `2` is
the original entry, so evaluating the polynomial contraction at `2` recovers the natural
contraction. The coefficients of a local polynomial sum to at most the bit length of its entry.

If every entry has at most `B` bits, the polynomial contraction has degree at most
`(B - 1) * G.vertices.length` and coefficient sum at most
`2 ^ G.numEdges * B ^ G.vertices.length`. Thus precision
`G.numEdges + G.vertices.length * B.size + 1` suffices to recover every coefficient exactly.
The bounds apply to arbitrary explicit networks, including empty tables and isolated edges.

## Main definitions

* `ExplicitTensorNetwork.binaryEntry`: a table lookup returned as binary-digit coefficients.
* `ExplicitTensorNetwork.binaryDegreeBound`: the total degree bound.
* `ExplicitTensorNetwork.binaryPrecision`: a sufficient coefficient precision.

## Main results

* `ExplicitTensorNetwork.eval_two_polyContraction_binaryEntry`: evaluation recovers contraction.
* `ExplicitTensorNetwork.natDegree_polyContraction_binaryEntry_le`: the degree bound.
* `ExplicitTensorNetwork.eval_one_polyContraction_binaryEntry_le`: the coefficient-sum bound.
* `ExplicitTensorNetwork.evalCoeffList_truncContraction_binaryEntry`: exact recovery from the
  truncated contraction at the derived degree and precision.
-/

public section

namespace Cslib.Circuits.Frontier.ExplicitTensorNetwork

open Polynomial DescribedNetwork

/-- The binary digits of a table entry, least significant first, as natural coefficients. -/
@[expose] def binaryEntry (table : List ℕ) (bs : List Bool) : List ℕ :=
  (entry table bs).bits.map Bool.toNat

/-- The coefficient list has exactly the bit length of the entry. -/
@[simp] theorem length_binaryEntry (table : List ℕ) (bs : List Bool) :
    (binaryEntry table bs).length = (entry table bs).size := by
  simp only [binaryEntry, List.length_map, Nat.size_eq_bits_len]

/-- The degree bound when every table entry has at most `B` bits. -/
@[expose] def binaryDegreeBound (B : ℕ) (G : ExplicitTensorNetwork ℕ) : ℕ :=
  (B - 1) * G.vertices.length

/-- A coefficient precision for a network whose entries have at most `B` bits. -/
@[expose] def binaryPrecision (B : ℕ) (G : ExplicitTensorNetwork ℕ) : ℕ :=
  G.numEdges + G.vertices.length * B.size + 1

/-- A table entry satisfies any bit-length bound satisfied by every stored table value. -/
theorem size_entry_le {table : List ℕ} {B : ℕ}
    (h : ∀ n ∈ table, n.size ≤ B) (bs : List Bool) : (entry table bs).size ≤ B := by
  unfold entry
  rcases lt_or_ge (BitString.lsbValue bs) table.length with hi | hi
  · rw [List.getD_eq_getElem _ _ hi]
    exact h _ (List.getElem_mem hi)
  · rw [List.getD_eq_default _ _ hi, Nat.size_zero]
    exact Nat.zero_le _

/-- Evaluation of the binary-digit contraction at `2` is the original natural contraction. -/
@[simp] theorem eval_two_polyContraction_binaryEntry (G : ExplicitTensorNetwork ℕ) :
    (G.polyContraction binaryEntry).eval 2 = G.contraction := by
  change (evalRingHom 2) (DescribedNetwork.contraction
    (fun t bs => binaryDigits (entry t bs)) G) = _
  rw [map_contraction]
  simpa only [coe_evalRingHom, eval_two_binaryDigits] using contraction_entry G

variable {G : ExplicitTensorNetwork ℕ} {B : ℕ}

/-- The degree of the binary-digit contraction is bounded by the entry bit lengths. -/
theorem natDegree_polyContraction_binaryEntry_le
    (h : ∀ v ∈ G.vertices, ∀ n ∈ v.2, n.size ≤ B) :
    (G.polyContraction binaryEntry).natDegree ≤ G.binaryDegreeBound B := by
  refine natDegree_sum_le_of_forall_le _ _ fun x _ => (natDegree_list_prod_le _).trans ?_
  rw [List.map_map]
  refine (List.sum_le_length_nsmul _ (B - 1) fun d hd => ?_).trans ?_
  · obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hd
    exact (natDegree_binaryDigits_le _).trans
      (Nat.sub_le_sub_right (size_entry_le (h v hv) _) 1)
  · simp only [List.length_map, nsmul_eq_mul, Nat.cast_id, binaryDegreeBound, mul_comm, le_refl]

/-- The coefficient sum is at most the number of edge assignments times `B` per vertex. -/
theorem eval_one_polyContraction_binaryEntry_le
    (h : ∀ v ∈ G.vertices, ∀ n ∈ v.2, n.size ≤ B) :
    (G.polyContraction binaryEntry).eval 1 ≤ 2 ^ G.numEdges * B ^ G.vertices.length := by
  change (evalRingHom 1) (DescribedNetwork.contraction
    (fun t bs => binaryDigits (entry t bs)) G) ≤ _
  rw [map_contraction, DescribedNetwork.contraction]
  refine (Finset.sum_le_card_nsmul _ _ (B ^ G.vertices.length) fun x _ => ?_).trans_eq ?_
  · refine (List.prod_le_pow_length _ B fun n hn => ?_).trans_eq ?_
    · obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hn
      exact (eval_one_binaryDigits_le _).trans (size_entry_le (h v hv) _)
    · simp only [List.length_map]
  · simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
      nsmul_eq_mul, Nat.cast_id]

/-- The derived precision strictly exceeds every coefficient of the polynomial contraction. -/
theorem eval_one_polyContraction_binaryEntry_lt_two_pow
    (h : ∀ v ∈ G.vertices, ∀ n ∈ v.2, n.size ≤ B) :
    (G.polyContraction binaryEntry).eval 1 < 2 ^ G.binaryPrecision B := by
  calc (G.polyContraction binaryEntry).eval 1
      ≤ 2 ^ G.numEdges * B ^ G.vertices.length := eval_one_polyContraction_binaryEntry_le h
    _ ≤ 2 ^ G.numEdges * (2 ^ B.size) ^ G.vertices.length :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.lt_size_self B).le _)
    _ = 2 ^ (G.numEdges + G.vertices.length * B.size) := by
      rw [← pow_mul, mul_comm B.size, ← pow_add]
    _ < 2 ^ G.binaryPrecision B := Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self _)

/-- The truncated contraction at the derived parameters recovers the whole polynomial. -/
theorem ofCoeffList_truncContraction_binaryEntry
    (h : ∀ v ∈ G.vertices, ∀ n ∈ v.2, n.size ≤ B) :
    ofCoeffList (G.truncContraction binaryEntry (G.binaryPrecision B)
      (G.binaryDegreeBound B + 1)) = G.polyContraction binaryEntry :=
  ofCoeffList_coeffsBelow_mod
    (Nat.lt_succ_of_le (natDegree_polyContraction_binaryEntry_le h))
    (eval_one_polyContraction_binaryEntry_lt_two_pow h)

/-- Exact natural contraction by Horner evaluation of the recovered coefficient residues. -/
theorem evalCoeffList_truncContraction_binaryEntry
    (h : ∀ v ∈ G.vertices, ∀ n ∈ v.2, n.size ≤ B) :
    evalCoeffList 2 (G.truncContraction binaryEntry (G.binaryPrecision B)
      (G.binaryDegreeBound B + 1)) = G.contraction := by
  rw [← eval_ofCoeffList, ofCoeffList_truncContraction_binaryEntry h,
    eval_two_polyContraction_binaryEntry]

end Cslib.Circuits.Frontier.ExplicitTensorNetwork
