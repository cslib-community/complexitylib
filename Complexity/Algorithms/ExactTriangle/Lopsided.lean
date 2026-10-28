/-
Copyright (c) 2026 Anthropic, PBC, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Foundations.Data.Matrix.IntegerBits
public import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.Ring

/-!
# Finite lopsided triangle queries as matrix products

Two outer parts have `n` vertices each; the finite middle part embeds into `Fin D`.
The matrices count common neighbors at every outer pair. Only pairs in `W` are graph edges,
so only those counts are triangle counts. Answers outside `W` are unconstrained.

This mathematical interface gives no native program, preprocessing cost, sparsity bound,
fast solver or subquadratic running time.

## Main definitions

* `LopsidedGraph`: two adjacency relations, a finite middle part and queried outer edges.
* `LopsidedGraph.matX`, `LopsidedGraph.matY`: padded biadjacency matrices.
* `LopsidedGraph.signedBitInstance`: four sign choices for each pair of binary digits.

## Main results

* `LopsidedGraph.matX_mul_matY_apply`: entries count common middle neighbors.
* `LopsidedGraph.matX_mul_matY_apply_ne_zero_iff`: nonzero entries detect common neighbors.
* `LopsidedGraph.mul_apply_eq_commonNeighborCount_ofMatrices`: the converse for zero/one matrices.
* `LopsidedGraph.mul_apply_eq_sum_signedBitInstance_counts`: signed products from `4 * β²` counts.

## References

The lopsided matrix interface is used in [AlmanWilliams2026, Section 3].
Adapted from [Anthropic's MatrixLanguage.lean](https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/3sum-apsp/ThreeSumApsp/Sec3/MatrixLanguage.lean)
and the lopsided definitions in [PaperStatements.lean](https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/3sum-apsp/PaperStatements.lean#L798-L852).
The adaptation uses `Set.EqOn`, pointwise signed parts, and direct finite cardinalities.
-/

@[expose] public section

namespace Cslib.Algorithms.ExactTriangle

/-- An unweighted tripartite graph whose outer parts each have `n` vertices. -/
structure LopsidedGraph (n : ℕ) where
  /-- The middle vertices. -/
  M : Type
  /-- The middle part is finite. -/
  [fintypeM : Fintype M]
  /-- Edges from the first outer part to the middle. -/
  adjA : Fin n → M → Prop
  /-- Edges from the middle to the second outer part. -/
  adjB : M → Fin n → Prop
  /-- Queried outer edges. -/
  W : Finset (Fin n × Fin n)

attribute [instance] LopsidedGraph.fintypeM

namespace LopsidedGraph

/-- On a pair in `W`, a common middle neighbor closes a triangle.
For a pair outside `W`, this predicate does not assert an outer edge. -/
def HasCommonNeighbor {n : ℕ} (I : LopsidedGraph n) (a b : Fin n) : Prop :=
  ∃ v : I.M, I.adjA a v ∧ I.adjB v b

open Classical in
/-- Number of common middle neighbors. At pairs in `W` this is the triangle count. -/
noncomputable def commonNeighborCount {n : ℕ} (I : LopsidedGraph n) (a b : Fin n) : ℕ :=
  (Finset.univ.filter fun v : I.M => I.adjA a v ∧ I.adjB v b).card

/-- Two thin matrices describe adjacency where their entries equal one.
The theorem `mul_apply_eq_commonNeighborCount_ofMatrices` requires zero/one entries. -/
def ofMatrices {n D : ℕ} (X : Matrix (Fin n) (Fin D) ℤ)
    (Y : Matrix (Fin D) (Fin n) ℤ) (W : Finset (Fin n × Fin n)) : LopsidedGraph n where
  M := Fin D
  adjA a v := X a v = 1
  adjB v b := Y v b = 1
  W := W

open Classical in
/-- The count for a matrix-defined graph uses the ordinary finite middle indices. -/
theorem commonNeighborCount_ofMatrices {n D : ℕ} (X : Matrix (Fin n) (Fin D) ℤ)
    (Y : Matrix (Fin D) (Fin n) ℤ) (W : Finset (Fin n × Fin n)) (a b : Fin n) :
    (ofMatrices X Y W).commonNeighborCount a b =
      (Finset.univ.filter fun v : Fin D => X a v = 1 ∧ Y v b = 1).card := by
  unfold ofMatrices commonNeighborCount
  congr 1
  ext v
  simp

open Classical in
/-- The first biadjacency matrix, with zero columns outside the injection range. -/
noncomputable def matX {n D : ℕ} (I : LopsidedGraph n) (e : I.M ↪ Fin D) :
    Matrix (Fin n) (Fin D) ℤ :=
  Matrix.of fun a j => if ∃ v : I.M, e v = j ∧ I.adjA a v then 1 else 0

open Classical in
/-- The second biadjacency matrix, with zero rows outside the injection range. -/
noncomputable def matY {n D : ℕ} (I : LopsidedGraph n) (e : I.M ↪ Fin D) :
    Matrix (Fin D) (Fin n) ℤ :=
  Matrix.of fun j b => if ∃ v : I.M, e v = j ∧ I.adjB v b then 1 else 0

variable {n D : ℕ} (I : LopsidedGraph n) (e : I.M ↪ Fin D)

/-- Every first biadjacency entry is zero or one. -/
theorem matX_eq_zero_or_one (a : Fin n) (j : Fin D) :
    I.matX e a j = 0 ∨ I.matX e a j = 1 := by
  classical
  simp only [matX, Matrix.of_apply]
  split_ifs <;> simp

/-- Every second biadjacency entry is zero or one. -/
theorem matY_eq_zero_or_one (j : Fin D) (b : Fin n) :
    I.matY e j b = 0 ∨ I.matY e j b = 1 := by
  classical
  simp only [matY, Matrix.of_apply]
  split_ifs <;> simp

/-- A middle part of cardinality at most `D` admits the required numbering. -/
theorem nonempty_embedding (h : Fintype.card I.M ≤ D) : Nonempty (I.M ↪ Fin D) :=
  Function.Embedding.nonempty_of_card_le (by simpa using h)

open Classical in
/-- At a middle vertex, the first matrix records its adjacency. -/
theorem matX_apply_emb (a : Fin n) (v : I.M) :
    I.matX e a (e v) = if I.adjA a v then 1 else 0 := by
  simp [matX]

open Classical in
/-- At a middle vertex, the second matrix records its adjacency. -/
theorem matY_apply_emb (v : I.M) (b : Fin n) :
    I.matY e (e v) b = if I.adjB v b then 1 else 0 := by
  simp [matY]

/-- An unused column is zero. -/
theorem matX_apply_of_notMem_range (a : Fin n) {j : Fin D} (hj : j ∉ Set.range e) :
    I.matX e a j = 0 :=
  ite_eq_right fun ⟨v, hv, _⟩ => hj ⟨v, hv⟩

/-- An unused row is zero. -/
theorem matY_apply_of_notMem_range {j : Fin D} (hj : j ∉ Set.range e) (b : Fin n) :
    I.matY e j b = 0 :=
  ite_eq_right fun ⟨v, hv, _⟩ => hj ⟨v, hv⟩

/-- A pair has a common neighbor if and only if its count is nonzero. -/
theorem commonNeighborCount_ne_zero_iff (a b : Fin n) :
    I.commonNeighborCount a b ≠ 0 ↔ I.HasCommonNeighbor a b := by
  classical
  rw [commonNeighborCount, Finset.card_ne_zero, Finset.filter_nonempty_iff]
  simp [HasCommonNeighbor]

/-- Every product entry counts common middle neighbors, independently of the numbering. -/
theorem matX_mul_matY_apply (a b : Fin n) :
    (I.matX e * I.matY e) a b = (I.commonNeighborCount a b : ℤ) := by
  classical
  rw [Matrix.mul_apply, commonNeighborCount, Finset.card_filter, Nat.cast_sum]
  -- Only the columns of the middle vertices matter.
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.map e)) fun j _ hj => by
    rw [I.matX_apply_of_notMem_range e a (by simpa using hj), zero_mul], Finset.sum_map]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [I.matX_apply_emb, I.matY_apply_emb]
  by_cases hA : I.adjA a v <;> by_cases hB : I.adjB v b <;> simp [hA, hB]

/-- A nonzero product entry detects a common middle neighbor. -/
theorem matX_mul_matY_apply_ne_zero_iff (a b : Fin n) :
    (I.matX e * I.matY e) a b ≠ 0 ↔ I.HasCommonNeighbor a b := by
  rw [matX_mul_matY_apply, Ne, Nat.cast_eq_zero]
  exact I.commonNeighborCount_ne_zero_iff a b

/-- On queried outer edges, correct natural counts are exactly the integer product entries.
Ordinary `Set.EqOn` leaves all unqueried entries unconstrained. -/
theorem counting_eqOn_iff (ans : Fin n × Fin n → ℕ) :
    Set.EqOn ans (fun q => I.commonNeighborCount q.1 q.2) (I.W : Set _) ↔
      Set.EqOn (fun q => (ans q : ℤ)) (fun q => (I.matX e * I.matY e) q.1 q.2)
        (I.W : Set _) := by
  simp only [Set.EqOn, matX_mul_matY_apply, Nat.cast_inj]

/-- Counts on queried edges provide their detection answers. -/
theorem detection_iff_of_counting (ans : Fin n × Fin n → ℕ)
    (h : Set.EqOn ans (fun q => I.commonNeighborCount q.1 q.2) (I.W : Set _)) :
    ∀ q ∈ I.W, ans q ≠ 0 ↔ I.HasCommonNeighbor q.1 q.2 := by
  intro q hq
  rw [h hq, commonNeighborCount_ne_zero_iff]

/-- For zero/one matrices, each product entry is the count in the graph they describe. -/
theorem mul_apply_eq_commonNeighborCount_ofMatrices {n D : ℕ}
    (X : Matrix (Fin n) (Fin D) ℤ) (Y : Matrix (Fin D) (Fin n) ℤ)
    (W : Finset (Fin n × Fin n)) (hX : ∀ a j, X a j = 0 ∨ X a j = 1)
    (hY : ∀ j b, Y j b = 0 ∨ Y j b = 1) (a b : Fin n) :
    (X * Y) a b = ((ofMatrices X Y W).commonNeighborCount a b : ℤ) := by
  classical
  rw [Matrix.mul_apply, commonNeighborCount, Finset.card_filter, Nat.cast_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rcases hX a j with hx | hx <;> rcases hY j b with hy | hy <;>
    simp [ofMatrices, hx, hy]

/-- One of four sign choices for a pair of binary digits; `true` selects the negative part.
Every instance has exactly `D` middle vertices and the original queried edges `W`. -/
def signedBitInstance (X : Matrix (Fin n) (Fin D) ℤ) (Y : Matrix (Fin D) (Fin n) ℤ)
    (W : Finset (Fin n × Fin n)) (negativeX negativeY : Bool) (i j : ℕ) : LopsidedGraph n :=
  ofMatrices (Matrix.bit (if negativeX then (X.map negPart) else (X.map posPart)) i)
    (Matrix.bit (if negativeY then (Y.map negPart) else (Y.map posPart)) j) W

/-- The finite family of sign/digit instances for a magnitude width `β`.
Different slots may describe the same graph. -/
def signedBitInstances (X : Matrix (Fin n) (Fin D) ℤ) (Y : Matrix (Fin D) (Fin n) ℤ)
    (W : Finset (Fin n × Fin n)) (β : ℕ) :
    (Bool × Bool × Fin β × Fin β) → LopsidedGraph n :=
  fun q => signedBitInstance X Y W q.1 q.2.1 q.2.2.1.val q.2.2.2.val

/-- The indexed family has `4 * β²` slots, allowing repeated or zero instances. -/
theorem card_signedBit_indices (β : ℕ) :
    Fintype.card (Bool × Bool × Fin β × Fin β) = 4 * β ^ 2 := by
  simp [pow_two, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]

/-- Each nonnegative product entry is a weighted sum of digit-graph counts. -/
private theorem mul_apply_eq_sum_counts {n D : ℕ} (X : Matrix (Fin n) (Fin D) ℤ)
    (Y : Matrix (Fin D) (Fin n) ℤ) (W : Finset (Fin n × Fin n)) (β : ℕ)
    (hX : ∀ a j, 0 ≤ X a j ∧ X a j < 2 ^ β) (hY : ∀ j b, 0 ≤ Y j b ∧ Y j b < 2 ^ β) (a b : Fin n) :
    (X * Y) a b = ∑ i ∈ Finset.range β, ∑ j ∈ Finset.range β, (2 : ℤ) ^ (i + j) *
      ((ofMatrices (Matrix.bit X i) (Matrix.bit Y j) W).commonNeighborCount a b : ℤ) := by
  rw [Matrix.mul_eq_sum_two_pow_smul_bit_mul_bit X Y β hX hY, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.smul_apply, smul_eq_mul, mul_apply_eq_commonNeighborCount_ofMatrices _ _ W
    (Matrix.bit_eq_zero_or_one X i)
    (Matrix.bit_eq_zero_or_one Y j)]

/-- Signed bounded product entries are weighted sums of four count instances per digit
pair, with signs `+, −, −, +`. Only counts at the same queried edge are needed. The absolute
bounds are strict; `β = 0` therefore permits only zero entries. -/
theorem mul_apply_eq_sum_signedBitInstance_counts {n D : ℕ} (X : Matrix (Fin n) (Fin D) ℤ)
    (Y : Matrix (Fin D) (Fin n) ℤ) (W : Finset (Fin n × Fin n)) (β : ℕ)
    (hX : ∀ a j, |X a j| < 2 ^ β) (hY : ∀ j b, |Y j b| < 2 ^ β) (a b : Fin n) :
    (X * Y) a b = ∑ i ∈ Finset.range β, ∑ j ∈ Finset.range β, (2 : ℤ) ^ (i + j) *
      (((signedBitInstance X Y W false false i j).commonNeighborCount
          a b : ℤ)
        - ((signedBitInstance X Y W false true i j).commonNeighborCount
            a b : ℤ)
        - ((signedBitInstance X Y W true false i j).commonNeighborCount
            a b : ℤ)
        + ((signedBitInstance X Y W true true i j).commonNeighborCount
            a b : ℤ)) := by
  simp only [signedBitInstance, Bool.false_eq_true, ↓reduceIte]
  obtain ⟨hXpos, hXneg⟩ := Matrix.map_posPart_lt_and_map_negPart_lt X hX
  obtain ⟨hYpos, hYneg⟩ := Matrix.map_posPart_lt_and_map_negPart_lt Y hY
  -- `XY` is a signed sum of the four products of a part of `X` and a part of `Y`.
  conv_lhs => rw [Matrix.eq_map_posPart_sub_map_negPart X, Matrix.eq_map_posPart_sub_map_negPart Y]
  rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub]
  simp only [Matrix.sub_apply]
  rw [mul_apply_eq_sum_counts _ _ W β hXpos hYpos,
    mul_apply_eq_sum_counts _ _ W β hXpos hYneg,
    mul_apply_eq_sum_counts _ _ W β hXneg hYpos,
    mul_apply_eq_sum_counts _ _ W β hXneg hYneg]
  simp only [mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  ring

end LopsidedGraph

end Cslib.Algorithms.ExactTriangle
