/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Classes.NP.Witness
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
blocks, closure under reductions, and axiom guards.
-/

namespace ComplexityTests.NPWitness

open Cslib.Complexity Turing.MultiTapeTM

/-! ### Witnesses with a total decoder: even numbers -/

/-- Checks that `m` is half of `n`. -/
def isHalf (x : ℕ × ℕ) : Bool := decide (x.2 + x.2 = x.1)

theorem isHalf_iff (n m : ℕ) : isHalf (n, m) = true ↔ m + m = n := by
  simp [isHalf]

theorem computableTidilyInPolyTime_isHalf :
    ComputableTidilyInPolyTime isHalf (encPair encUnary encUnary) encBool := by
  unfold isHalf
  fun_prop

/-- Even numbers in unary are verified by framed unary halves, padded to length `2 * n + 1`. -/
theorem isVerifier_even : IsVerifier encUnary (2 * Polynomial.X + 1)
    (witnessVerifier Decoder.unary isHalf) {n | ∃ m, m + m = n} :=
  isVerifier_witnessVerifier Decoder.unary isHalf_iff fun _ m h => ⟨m, h, by simp; omega⟩

example : {n | ∃ m, m + m = n} ∈ NP encUnary :=
  mem_NP_of_witness Decoder.unary (p := Polynomial.X) (.of_tidy computableTidilyInPolyTime_isHalf)
    isHalf_iff
    fun _ m h => ⟨m, h, by simp; omega⟩

-- In: the framed witness `2` for `4`, padded to the certificate length `2 * 4 + 1`.
example : (frame (encUnary 2) ++ List.replicate 4 false).length = 2 * 4 + 1 := rfl
example : witnessVerifier Decoder.unary isHalf (4, frame (encUnary 2) ++ List.replicate 4 false) =
    true := rfl

-- Bits after the framed witness are ignored.
example :
    witnessVerifier Decoder.unary isHalf (4, frame (encUnary 2) ++ [true, true, false, true]) =
      true := rfl

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
example : unframe (List.replicate 9 true) = List.replicate 4 true := rfl
example : isHalf (8, 4) = true := rfl
example : witnessVerifier Decoder.unary isHalf (8, List.replicate 9 true) = false := rfl

-- In general a certificate is accepted only if it is a framed witness followed by any bits.
example (n : ℕ) (w : List Bool) (h : witnessVerifier Decoder.unary isHalf (n, w) = true) :
    ∃ m v, w = frame (encUnary m) ++ v ∧ m + m = n := by
  obtain ⟨m, v, hw, hm⟩ := witnessVerifier_eq_true_iff.1 h
  exact ⟨m, v, hw, (isHalf_iff n m).1 hm⟩

-- A certificate starting with the end marker frames the witness `0`, whatever follows.
example : witnessVerifier Decoder.unary isHalf (4, false :: List.replicate 8 true) = false := rfl
example : witnessVerifier Decoder.unary isHalf (0, false :: List.replicate 8 true) = true := rfl

-- Boundary: the shortest certificate for `0` is the empty frame `[false]`; the empty word frames
-- nothing and is rejected.
example : witnessVerifier Decoder.unary isHalf (0, [false]) = true := rfl
example : witnessVerifier Decoder.unary isHalf (0, []) = false := rfl

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
  mem_NP_of_subsetWitness (check := hasCount) (.of_tidy (ComputableTidilyInPolyTime.fst _ _))
    (.of_tidy ((ComputableTidilyInPolyTime.unary_to_binary.comp
      ((ComputableTidilyInPolyTime.length_list encNat).comp (ComputableTidilyInPolyTime.snd _ _))
      ).decide_eq' (by fun_prop)))
    fun x l hl _ => by simp [hasCount, List.toFinset_card_of_nodup hl]

-- In: the mask selects `1` and `2`.
example :
    subsetVerifier (fun x : List ℕ × ℕ => x.1) hasCount (([1, 1, 2], 2), [true, false, true]) =
      true := rfl

-- A repeated entry is selected only at its first occurrence.
example : selectDistinct [1, 1, 2] [true, true, false] = [1] := rfl
example :
    subsetVerifier (fun x : List ℕ × ℕ => x.1) hasCount (([1, 1, 2], 2), [true, true, false]) =
      false := rfl

-- Missing mask bits are `false`, and bits beyond the candidates are ignored.
example : selectDistinct [1, 1, 2] [false, false, true, true, true] = [2] := rfl
example : selectDistinct [1, 1, 2] [] = [] := rfl

-- Boundary: the empty set of the empty list.
example : subsetVerifier (fun x : List ℕ × ℕ => x.1) hasCount (([], 0), []) = true := rfl

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

-- The full mask selects each entry at its first occurrence.
example : selectDistinct [3, 5, 3, 7] (List.replicate 4 true) = [3, 5, 7] := rfl
example : Graph.distinctVertices ([2, 1, 2, 1], []) = [2, 1] := rfl
example :
    (selectDistinct [3, 5, 3, 7] (List.replicate 4 true)).length = [3, 5, 3, 7].toFinset.card :=
  length_selectDistinct_replicate _

/-! ### Vertex covers through the subset verifier -/

/-- The path `1 - 2 - 3`. -/
def path3 : Graph := ([1, 2, 3], [(1, 2), (2, 3)])

-- In: the middle vertex covers both edges.
example : VertexCover.verifier ((path3, 1), [false, true, false]) = true := rfl
-- Out: an end vertex leaves an edge uncovered, and a cover of the wrong size is rejected.
example : VertexCover.verifier ((path3, 1), [true, false, false]) = false := rfl
example : VertexCover.verifier ((path3, 1), [true, true, false]) = false := rfl
-- A repeated declared vertex is selected only at its first occurrence.
example : VertexCover.verifier (((([2, 2, 1, 3], [(1, 2), (2, 3)]) : Graph), 1),
    [true, true, false, false]) = true := rfl
example : VertexCover.verifier (((([2, 2, 1, 3], [(1, 2), (2, 3)]) : Graph), 1),
    [false, true, false, false]) = false := rfl

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

/-! ### Axioms -/

/--
info: 'Cslib.Complexity.IsVerifier.of_padding' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.IsVerifier.of_padding

/--
info: 'Cslib.Complexity.IsVerifier.guard' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.IsVerifier.guard

/--
info: 'Cslib.Complexity.witnessVerifier_eq_true_iff' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.witnessVerifier_eq_true_iff

/--
info: 'Cslib.Complexity.isVerifier_witnessVerifier' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.isVerifier_witnessVerifier

/--
info: 'Cslib.Complexity.mem_NP_of_witness' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.mem_NP_of_witness

/--
info: 'Cslib.Complexity.isVerifier_subsetVerifier' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.isVerifier_subsetVerifier

/--
info: 'Cslib.Complexity.mem_NP_of_subsetWitness' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.mem_NP_of_subsetWitness

/--
info: 'Cslib.Complexity.PolyTimeReducible.mem_NP' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.PolyTimeReducible.mem_NP

/-! ### Migrated problems -/

/--
info: 'Cslib.Complexity.SAT.isVerifier' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.SAT.isVerifier

/--
info: 'Cslib.Complexity.SAT.mem_NP' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.SAT.mem_NP

/--
info: 'Cslib.Complexity.Graph.isVerifier_verifySubset' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.Graph.isVerifier_verifySubset

/--
info: 'Cslib.Complexity.VertexCover.isVerifier' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.VertexCover.isVerifier

end ComplexityTests.NPWitness
