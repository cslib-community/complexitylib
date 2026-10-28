/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Classes.NP.Witness
import Complexity.Computability.Complexity.Classes.PH.Kannan
import Complexity.Computability.Complexity.Problems.Clique
import Complexity.Computability.Complexity.Problems.SAT.PolyTime
import Complexity.Computability.Complexity.Problems.ThreeSAT
import Complexity.Computability.Complexity.Problems.VertexCover
import Complexity.Tactic.PolyTime

/-!
# NP membership from witness relations

A toy witness relation through the builder with a total decoder (even numbers, witnessed by their
halves), a toy subset problem through the subset builder (lists with `k` distinct entries),
malformed and boundary certificates, the verifier of `VertexCover` as a subset verifier, unary
blocks, and closure under reductions.
-/

namespace ComplexityTests.NPWitness

open Cslib.Complexity Turing.MultiTapeTM

/-! ### Witnesses with a total decoder: even numbers -/

/-- Checks that `m` is half of `n`. -/
def isHalf (x : ℕ × ℕ) : Bool := decide (x.2 + x.2 = x.1)

theorem isHalf_iff (n m : ℕ) : isHalf (n, m) = true ↔ m + m = n := by
  simp [isHalf]

theorem computableInPolyTime_isHalf :
    ComputableInPolyTime isHalf (encPair encUnary encUnary) encBool := by
  unfold isHalf
  fun_prop

/-- Even numbers in unary are verified by framed unary halves, padded to length `2 * n + 1`. -/
theorem isVerifier_even : IsVerifier encUnary (2 * Polynomial.X + 1)
    (witnessVerifier Decoder.unary isHalf) {n | ∃ m, m + m = n} :=
  isVerifier_witnessVerifier Decoder.unary isHalf_iff fun _ m h => ⟨m, h, by simp; omega⟩

example : {n | ∃ m, m + m = n} ∈ NP encUnary :=
  mem_NP_of_witness Decoder.unary (p := Polynomial.X) computableInPolyTime_isHalf
    isHalf_iff
    fun _ m h => ⟨m, h, by simp; omega⟩

example : encUnary '' {n | ∃ m, m + m = n} ∈ NP encBits :=
  mem_NP_image Decoder.unary
    (mem_NP_of_witness Decoder.unary (p := Polynomial.X)
      computableInPolyTime_isHalf isHalf_iff fun _ m h => ⟨m, h, by simp; omega⟩)

-- In: the framed witness `2` for `4`, padded to the certificate length `2 * 4 + 1`; bits after
-- the framed witness are ignored.
example :
    (frame (encUnary 2) ++ List.replicate 4 false).length = 2 * 4 + 1 ∧
    witnessVerifier Decoder.unary isHalf (4, frame (encUnary 2) ++ List.replicate 4 false) = true ∧
    witnessVerifier Decoder.unary isHalf (4, frame (encUnary 2) ++ [true, true, false, true]) =
      true :=
  ⟨rfl, rfl, rfl⟩

-- Out: no certificate of any length is accepted for `3`.
example (w : List Bool) : witnessVerifier Decoder.unary isHalf (3, w) = false := by
  refine Bool.eq_false_iff.2 fun h => ?_
  obtain ⟨m, -, -, hm⟩ := witnessVerifier_eq_true_iff.1 h
  have := (isHalf_iff 3 m).1 hm
  omega

example : 3 ∉ {n | ∃ m, m + m = n} := by
  rintro ⟨m, hm⟩
  omega

-- Malformed certificates are rejected. The unterminated frame of nine `true` bits reads as the
-- witness `4` of `8`, but it is not a framed encoding followed by padding, so it is rejected.
example :
    unframe (List.replicate 9 true) = List.replicate 4 true ∧
    isHalf (8, 4) = true ∧
    witnessVerifier Decoder.unary isHalf (8, List.replicate 9 true) = false :=
  ⟨rfl, rfl, rfl⟩

-- In general a certificate is accepted only if it is a framed witness followed by any bits.
example (n : ℕ) (w : List Bool) (h : witnessVerifier Decoder.unary isHalf (n, w) = true) :
    ∃ m v, w = frame (encUnary m) ++ v ∧ m + m = n := by
  obtain ⟨m, v, hw, hm⟩ := witnessVerifier_eq_true_iff.1 h
  exact ⟨m, v, hw, (isHalf_iff n m).1 hm⟩

-- A certificate starting with the end marker frames the witness `0`, whatever follows; the
-- shortest certificate for `0` is `[false]`, while `[]` frames nothing and is rejected.
example :
    witnessVerifier Decoder.unary isHalf (4, false :: List.replicate 8 true) = false ∧
    witnessVerifier Decoder.unary isHalf (0, false :: List.replicate 8 true) = true ∧
    witnessVerifier Decoder.unary isHalf (0, [false]) = true ∧
    witnessVerifier Decoder.unary isHalf (0, []) = false :=
  ⟨rfl, rfl, rfl, rfl⟩

/-! ### Subset witnesses: distinct entries -/

/-- The lists with `k` distinct entries. -/
def DistinctEntries : Set (List ℕ × ℕ) :=
  {x | ∃ S : Finset ℕ, (∀ v ∈ S, v ∈ x.1) ∧ S.card = x.2}

/-- Checks that the selected list has `k` entries. -/
def hasCount (y : (List ℕ × ℕ) × List ℕ) : Bool := decide (y.2.length = y.1.2)

theorem isVerifier_distinctEntries : IsVerifier (encPair (encList encNat) encNat) Polynomial.X
    (subsetVerifier (fun x => x.1) hasCount) DistinctEntries := by
  refine isVerifier_subsetVerifier (fun x => ?_) fun x l hl _ => ?_
  · have := length_le_length_encList encNat x.1
    simp only [Polynomial.eval_X, length_encPair]
    omega
  · simp [hasCount, List.toFinset_card_of_nodup hl]

example : DistinctEntries ∈ NP (encPair (encList encNat) encNat) :=
  mem_NP_of_subsetWitness (check := hasCount) (ComputableInPolyTime.fst _ _)
    (by unfold hasCount; fun_prop)
    fun x l hl _ => by simp [hasCount, List.toFinset_card_of_nodup hl]

-- In: the mask `[true, false, true]` selects `1` and `2`, while a repeated entry is selected only
-- at its first occurrence (`[true, true, false]` selects only `[1]`).
example :
    subsetVerifier (fun x : List ℕ × ℕ => x.1) hasCount (([1, 1, 2], 2), [true, false, true]) =
      true ∧
    selectDistinct [1, 1, 2] [true, true, false] = [1] ∧
    subsetVerifier (fun x : List ℕ × ℕ => x.1) hasCount (([1, 1, 2], 2), [true, true, false]) =
      false :=
  ⟨rfl, rfl, rfl⟩

-- Missing mask bits are `false`, bits beyond the candidates are ignored, and the empty set of the
-- empty list is accepted.
example :
    selectDistinct [1, 1, 2] [false, false, true, true, true] = [2] ∧
    selectDistinct [1, 1, 2] [] = [] ∧
    subsetVerifier (fun x : List ℕ × ℕ => x.1) hasCount (([], 0), []) = true :=
  ⟨rfl, rfl, rfl⟩

-- Out: `[1, 1]` has a single distinct entry, so no certificate is accepted.
example : ¬∃ w : List Bool, w.length = Polynomial.X.eval (encPair (encList encNat) encNat
    ([1, 1], 2)).length ∧ subsetVerifier (fun x : List ℕ × ℕ => x.1) hasCount (([1, 1], 2), w) =
      true := by
  rw [← isVerifier_distinctEntries]
  rintro ⟨S, hS, hcard⟩
  have hsub : S ⊆ {1} := fun v hv => by simpa using hS v hv
  have := Finset.card_le_card hsub
  simp only [Finset.card_singleton] at this
  omega

/-! ### Full masks -/

-- The full mask selects each entry at its first occurrence, so its length counts the distinct
-- elements (`[3, 5, 3, 7].toFinset.card = 3`).
example :
    selectDistinct [3, 5, 3, 7] (List.replicate 4 true) = [3, 5, 7] ∧
    Graph.distinctVertices ([2, 1, 2, 1], []) = [2, 1] ∧
    [3, 5, 3, 7].toFinset.card = 3 :=
  ⟨rfl, rfl, (length_selectDistinct_replicate [3, 5, 3, 7]).symm.trans rfl⟩

/-! ### Vertex covers through the subset verifier -/

/-- The path `1 - 2 - 3`. -/
def path3 : Graph := ([1, 2, 3], [(1, 2), (2, 3)])

-- The middle vertex covers both edges; an end vertex or wrong size is rejected; a repeated
-- declared vertex is selected only at its first occurrence.
example :
    VertexCover.verifier ((path3, 1), [false, true, false]) = true ∧
    VertexCover.verifier ((path3, 1), [true, false, false]) = false ∧
    VertexCover.verifier ((path3, 1), [true, true, false]) = false ∧
    VertexCover.verifier (((([2, 2, 1, 3], [(1, 2), (2, 3)]) : Graph), 1),
      [true, true, false, false]) = true ∧
    VertexCover.verifier (((([2, 2, 1, 3], [(1, 2), (2, 3)]) : Graph), 1),
      [false, true, false, false]) = false :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-! ### Unary blocks -/

-- Blocks of width `3` writing `2` and `0`; counting the set bits of a block reads its number.
example : unaryBlocks 3 6 (fun a => [2, 0].getD a 0) = [true, true, false, false, false, false] :=
  rfl
example : ((List.range 3).countP fun c =>
    (unaryBlocks 3 6 (fun a => [2, 0].getD a 0)).getD (3 * 0 + c) false) = 2 :=
  countP_unaryBlocks (f := fun a => [2, 0].getD a 0) (by decide) (by decide)

/-! ### Closure under reductions -/

example : SAT ∈ NP encCNF := polyTimeReducible_SAT_ThreeSAT.mem_NP ThreeSAT.mem_NP

example : IndependentSet ∈ NP (encPair encGraph encNat) :=
  polyTimeReducible_IndependentSet_Clique.mem_NP Clique.mem_NP

end ComplexityTests.NPWitness
