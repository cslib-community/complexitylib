/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.ArthurMerlin.SetLowerBound
public import Complexity.Computability.Complexity.Problems.GraphIsomorphism
public import Complexity.Foundations.Data.BitString.Block
public import Mathlib.Data.Nat.Factorial.Basic

import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Factorial
import Complexity.Foundations.Data.BitString.Basic
import Mathlib.Data.List.GetD

/-!
# Graph non-isomorphism is in AM

The public-coin protocol of Goldwasser and Sipser for graph non-isomorphism
[GoldwasserSipser1986], [Arora and Barak, Section 8.2][AroraBarak09]. Let the two graphs have
`n` distinct vertices each, with adjacency matrices `A₀` and `A₁` on positions. Permutations `τ`
relabel matrices by `Matrix.reindex τ τ`, and the pairs `(M, σ)` of a relabelling `M` of `A₀` or
`A₁` and an automorphism `σ` of `M` form a set of
`2 n!` elements when the graphs are not isomorphic and `n!` when they are
(`Cslib.Complexity.GraphNonIsomorphism.PublicCoin.card_pairs_union`): by the orbit–stabilizer
count, each orbit contributes `n!` pairs
(`Cslib.Complexity.GraphNonIsomorphism.PublicCoin.card_pairs`), and the two orbits coincide or are
disjoint. Mathlib's action of permutations on functions, `arrowAction`, is a definition rather
than an instance and acts on uncurried functions, so the orbits are finite sets of matrices here,
and the orbit–stabilizer count, a sum of automorphism group sizes over an orbit, is proved by
partitioning the permutations into fibers.

Merlin can certify membership of a pair, by naming the graph and a relabelling of it. Pairs are
written as strings of `2 L² + 1` bits, `L` the length of the encoded instance
(`Cslib.Complexity.GraphNonIsomorphism.PublicCoin.code`): the matrix `M` and the matrix of `σ`,
row by row with entry `(i, j)` at `finProdFinEquiv (i, j)`, and `false` bits. When the graphs
have different numbers of vertices, every string is accepted. The set lower bound protocol with
threshold `2 n!` (`Cslib.Complexity.mem_AM_of_card_certifiedSet`) then gives
`GraphNonIsomorphism ∈ AM` (`Cslib.Complexity.GraphNonIsomorphism.mem_AM`). The private-coin
protocol in `Complexity.Computability.Complexity.Classes.IP.GraphNonIsomorphism` is not used.

## Main definitions

* `Cslib.Complexity.GraphNonIsomorphism.PublicCoin.orbit`,
  `Cslib.Complexity.GraphNonIsomorphism.PublicCoin.pairs`: relabellings, and relabellings with an
  automorphism.
* `Cslib.Complexity.GraphNonIsomorphism.PublicCoin.code`,
  `Cslib.Complexity.GraphNonIsomorphism.PublicCoin.test`: strings of pairs and their certificates.

## Main results

* `Cslib.Complexity.GraphNonIsomorphism.PublicCoin.card_pairs`: an orbit gives `n!` pairs.
* `Cslib.Complexity.GraphNonIsomorphism.PublicCoin.card_pairs_union`: `2 n!` or `n!` pairs.
* `Cslib.Complexity.GraphNonIsomorphism.PublicCoin.card_filter_check`: the certified strings
  correspond to the pairs.
* `Cslib.Complexity.GraphNonIsomorphism.mem_GraphIsomorphism_iff_mem_orbit`: isomorphism as
  relabelling of adjacency matrices.
* `Cslib.Complexity.GraphNonIsomorphism.mem_AM`: graph non-isomorphism is in `AM`.

## References

* [S. Goldwasser, M. Sipser, *Private coins versus public coins in interactive proof
  systems*][GoldwasserSipser1986]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity

open Finset Turing.MultiTapeTM

namespace GraphNonIsomorphism

namespace PublicCoin

/-! ### Relabelling matrices -/

variable {n : ℕ}

/-- Relabelling by a product of permutations is relabelling twice. -/
private theorem reindex_mul (σ τ : Equiv.Perm (Fin n)) (M : Matrix (Fin n) (Fin n) Bool) :
    Matrix.reindex (σ * τ) (σ * τ) M = Matrix.reindex σ σ (Matrix.reindex τ τ M) :=
  (DFunLike.congr_fun (Matrix.reindex_trans τ τ σ σ) M).symm

/-- Relabelling by the identity permutation does nothing. -/
private theorem reindex_one (M : Matrix (Fin n) (Fin n) Bool) : Matrix.reindex 1 1 M = M :=
  Matrix.reindex_refl_refl M

/-- `Matrix.reindex τ τ A = M` says that `τ` carries `A` to `M`. -/
theorem reindex_eq_iff {τ : Equiv.Perm (Fin n)} {A M : Matrix (Fin n) (Fin n) Bool} :
    Matrix.reindex τ τ A = M ↔ ∀ i j, M (τ i) (τ j) = A i j := by
  constructor
  · rintro rfl i j
    simp
  · intro h
    ext i j
    simpa using (h (τ.symm i) (τ.symm j)).symm

/-- The relabellings of a matrix by permutations of its rows and columns. -/
def orbit (A : Matrix (Fin n) (Fin n) Bool) : Finset (Matrix (Fin n) (Fin n) Bool) :=
  univ.image fun τ => Matrix.reindex τ τ A

private theorem mem_orbit {A M : Matrix (Fin n) (Fin n) Bool} :
    M ∈ orbit A ↔ ∃ τ, Matrix.reindex τ τ A = M := by
  simp [orbit]

theorem mem_orbit_trans {A B M : Matrix (Fin n) (Fin n) Bool} (hB : B ∈ orbit A)
    (hM : M ∈ orbit B) : M ∈ orbit A := by
  obtain ⟨τ, rfl⟩ := mem_orbit.1 hB
  obtain ⟨σ, rfl⟩ := mem_orbit.1 hM
  exact mem_orbit.2 ⟨σ * τ, reindex_mul σ τ A⟩

theorem mem_orbit_symm {A B : Matrix (Fin n) (Fin n) Bool} (hB : B ∈ orbit A) : A ∈ orbit B := by
  obtain ⟨τ, rfl⟩ := mem_orbit.1 hB
  refine mem_orbit.2 ⟨τ⁻¹, ?_⟩
  rw [← reindex_mul, inv_mul_cancel, reindex_one]

/-- The pairs of a relabelling of `A` and an automorphism of it. -/
def pairs (A : Matrix (Fin n) (Fin n) Bool) :
    Finset (Matrix (Fin n) (Fin n) Bool × Equiv.Perm (Fin n)) :=
  univ.filter fun p => p.1 ∈ orbit A ∧ Matrix.reindex p.2 p.2 p.1 = p.1

/-- A relabelling `M` of `A` has as many automorphisms as there are permutations carrying `A` to
`M`: composing with one permutation carrying `A` to `M` is a bijection. -/
private theorem card_filter_reindex_eq {A M : Matrix (Fin n) (Fin n) Bool} (hM : M ∈ orbit A) :
    #{σ : Equiv.Perm (Fin n) | Matrix.reindex σ σ M = M} =
      #{τ : Equiv.Perm (Fin n) | Matrix.reindex τ τ A = M} := by
  obtain ⟨τ₀, rfl⟩ := mem_orbit.1 hM
  refine card_equiv (Equiv.mulRight τ₀) fun σ => ?_
  simp only [mem_filter, mem_univ, true_and, Equiv.coe_mulRight, reindex_mul]

/-- **Orbit–stabilizer count**: the pairs of a relabelling of `A` and an automorphism of it are
`n!` many. The automorphism groups along the orbit have the sizes of the fibers of
`τ ↦ Matrix.reindex τ τ A` (`card_filter_reindex_eq`), which partition the `n!` permutations. -/
theorem card_pairs (A : Matrix (Fin n) (Fin n) Bool) : #(pairs A) = n.factorial := by
  have hsum : #(pairs A) = ∑ M : Matrix (Fin n) (Fin n) Bool,
      #{τ : Equiv.Perm (Fin n) | Matrix.reindex τ τ A = M} := by
    rw [pairs, card_filter, Fintype.sum_prod_type]
    refine sum_congr rfl fun M _ => ?_
    by_cases hM : M ∈ orbit A
    · simp only [hM, true_and, ← card_filter_reindex_eq hM, card_filter]
    · simp only [hM, false_and, ↓reduceIte, sum_const_zero]
      symm
      rw [card_eq_zero, filter_eq_empty_iff]
      exact fun τ _ h => hM (mem_orbit.2 ⟨τ, h⟩)
  rw [hsum, ← card_eq_sum_card_fiberwise (fun _ _ => mem_univ _), card_univ,
    Fintype.card_perm, Fintype.card_fin]

/-- The pairs of the two matrices are `n!` many if one is a relabelling of the other, and `2 n!`
many otherwise. -/
theorem card_pairs_union (A₀ A₁ : Matrix (Fin n) (Fin n) Bool) :
    #(pairs A₀ ∪ pairs A₁) = if A₁ ∈ orbit A₀ then n.factorial else 2 * n.factorial := by
  split_ifs with h
  · have heq : pairs A₁ = pairs A₀ := by
      ext p
      simp only [pairs, mem_filter, mem_univ, true_and]
      exact and_congr_left fun _ =>
        ⟨fun hp => mem_orbit_trans h hp, fun hp => mem_orbit_trans (mem_orbit_symm h) hp⟩
    rw [heq, union_self, card_pairs]
  · rw [card_union_of_disjoint, card_pairs, card_pairs, two_mul]
    refine disjoint_left.2 fun p hp₀ hp₁ => h ?_
    simp only [pairs, mem_filter, mem_univ, true_and] at hp₀ hp₁
    exact mem_orbit_trans hp₀.1 (mem_orbit_symm hp₁.1)

/-! ### Positions -/

/-- Entry `(i, j)` of a matrix of size `n`, read row by row, is at position `i * n + j`, the value
of `finProdFinEquiv (i, j)`. -/
private theorem val_finProdFinEquiv (i j : Fin n) : (finProdFinEquiv (i, j) : ℕ) = i * n + j := by
  rw [finProdFinEquiv_apply_val]
  ring

private theorem index_lt (i j : Fin n) : (i : ℕ) * n + j < n * n :=
  val_finProdFinEquiv i j ▸ (finProdFinEquiv (i, j)).isLt

/-- Every position below `n * n` is the position of its row and column. -/
private theorem index_symm {q : ℕ} (h : q < n * n) :
    ((finProdFinEquiv.symm ⟨q, h⟩).1 : ℕ) * n + (finProdFinEquiv.symm ⟨q, h⟩).2 = q := by
  rw [← val_finProdFinEquiv, Prod.mk.eta, Equiv.apply_symm_apply]

/-- The entry at position `q` of a matrix of size `n` read row by row, `false` beyond `n * n`. -/
def matrixBit (A : Matrix (Fin n) (Fin n) Bool) (q : ℕ) : Bool :=
  if h : q < n * n then BitString.blocksEquiv.symm (Matrix.of.symm A) ⟨q, h⟩ else false

private theorem matrixBit_index (A : Matrix (Fin n) (Fin n) Bool) (i j : Fin n) :
    matrixBit A (i * n + j) = A i j := by
  have hq : (⟨i * n + j, index_lt i j⟩ : Fin (n * n)) = finProdFinEquiv (i, j) :=
    Fin.ext (val_finProdFinEquiv i j).symm
  simp only [matrixBit, index_lt i j, ↓reduceDIte, hq, BitString.blocksEquiv_symm_apply,
    Matrix.of_symm_apply, Equiv.symm_apply_apply]

private theorem matrixBit_of_le (A : Matrix (Fin n) (Fin n) Bool) {q : ℕ} (h : n * n ≤ q) :
    matrixBit A q = false := by
  simp [matrixBit, Nat.not_lt.2 h]

/-! ### Codes of pairs and certificates -/

/-- Bit `p` of the code of a pair `(M, σ)`: the entries of `M`, then the entries of the matrix of
`σ`, row by row, then `false`. -/
def codeBit (M : Matrix (Fin n) (Fin n) Bool) (σ : Equiv.Perm (Fin n)) (p : ℕ) : Bool :=
  if p < n * n then matrixBit M p
  else matrixBit (Matrix.of fun i j => decide (σ i = j)) (p - n * n)

/-- The code of a pair `(M, σ)` of a matrix and a permutation, in `E` bits. -/
def code (E : ℕ) (M : Matrix (Fin n) (Fin n) Bool) (σ : Equiv.Perm (Fin n)) : BitString E :=
  fun p => codeBit M σ p

/-- Bit `q` of a certificate naming the graph `b` and a permutation `τ`: `b`, then the entries of
the matrix of `τ`, row by row, then `false`. -/
private def certBit (b : Bool) (τ : Equiv.Perm (Fin n)) (q : ℕ) : Bool :=
  if q = 0 then b else matrixBit (Matrix.of fun i j => decide (τ i = j)) (q - 1)

/-- A certificate naming the graph `b` and a permutation `τ`, in `C` bits. -/
private def cert (C : ℕ) (b : Bool) (τ : Equiv.Perm (Fin n)) : BitString C :=
  fun q => certBit b τ q

private theorem getD_ofFn {E : ℕ} (x : BitString E) {p : ℕ} (hp : p < E) :
    (List.ofFn x).getD p false = x ⟨p, hp⟩ := by
  rw [List.getD_eq_getElem _ _ (by simpa using hp), List.getElem_ofFn]

/-- The matrix read from the first `n * n` bits of a word. -/
private def decodeMatrix (n : ℕ) (u : List Bool) : Matrix (Fin n) (Fin n) Bool :=
  Matrix.of fun i j => u.getD (i * n + j) false

/-- The column selected by row `i` of a matrix of size `n` encoded row by row in `w`: the first
`j < n` with bit `i * n + j` of `w` set, or `0` when there is none. -/
def image (n : ℕ) (w : List Bool) (i : ℕ) : ℕ :=
  ((List.range n).filter fun j => w.getD (i * n + j) false).headD 0

private theorem image_lt {n : ℕ} (w : List Bool) (i : ℕ) (hn : 0 < n) : image n w i < n := by
  unfold image
  cases h : (List.range n).filter (fun j => w.getD (i * n + j) false) with
  | nil => exact hn
  | cons j l =>
    have : j ∈ (List.range n).filter (fun j => w.getD (i * n + j) false) :=
      h ▸ List.mem_cons_self
    simpa using (List.mem_filter.1 this).1

/-- A row with a single set bit selects its column. -/
private theorem image_eq {n : ℕ} {w : List Bool} {i c : ℕ} (hc : c < n)
    (hw : ∀ j < n, w.getD (i * n + j) false = decide (j = c)) : image n w i = c := by
  unfold image
  rw [List.filter_congr (fun j hj => hw j (List.mem_range.1 hj)), List.filter_eq,
    List.count_eq_one_of_mem List.nodup_range (List.mem_range.2 hc), List.replicate_one]
  rfl

private theorem computableTidilyInPolyTime_image {γ : Type} {input : γ ↪ List Bool} {n i : γ → ℕ}
    {w : γ → List Bool} (hn : ComputableTidilyInPolyTime n input encUnary)
    (hw : ComputableTidilyInPolyTime w input encBits)
    (hi : ComputableTidilyInPolyTime i input encUnary) :
    ComputableTidilyInPolyTime (fun x => image (n x) (w x) (i x)) input encUnary := by
  unfold image
  fun_prop

attribute [local fun_prop] computableTidilyInPolyTime_image

/-- The map read from the matrix starting after `k` bits of a word: row `i` selects its first set
bit (`image`). -/
private def decodeMap (n k : ℕ) (u : List Bool) (i : Fin n) : Fin n :=
  ⟨image n (u.drop k) i, image_lt _ _ i.pos⟩

private theorem decodeMatrix_code {E : ℕ} (hE : n * n ≤ E) (M : Matrix (Fin n) (Fin n) Bool)
    (σ : Equiv.Perm (Fin n)) : decodeMatrix n (List.ofFn (code E M σ)) = M := by
  ext i j
  rw [decodeMatrix, Matrix.of_apply, getD_ofFn _ ((index_lt i j).trans_le hE)]
  simp only [code, codeBit, index_lt i j, ↓reduceIte, matrixBit_index]

/-- In the matrix of a permutation `σ`, row `i` has its set bit at `σ i`. -/
private theorem decide_val_eq {σ : Equiv.Perm (Fin n)} {i : Fin n} {j : ℕ} (hj : j < n) :
    decide (σ i = ⟨j, hj⟩) = decide (j = σ i) :=
  decide_eq_decide.2 ⟨fun h => by rw [h], fun h => Fin.ext h.symm⟩

private theorem decodeMap_code {E : ℕ} (hE : 2 * (n * n) ≤ E) (M : Matrix (Fin n) (Fin n) Bool)
    (σ : Equiv.Perm (Fin n)) : decodeMap n (n * n) (List.ofFn (code E M σ)) = σ := by
  funext i
  refine Fin.ext (image_eq (σ i).2 fun j hj => ?_)
  have hlt : (i : ℕ) * n + j < n * n := index_lt i ⟨j, hj⟩
  rw [List.getD_eq_getElem?_getD, List.getElem?_drop, ← List.getD_eq_getElem?_getD,
    getD_ofFn _ (by omega)]
  simp only [code, codeBit, show ¬(n * n + (i * n + j) < n * n) by omega, ↓reduceIte,
    Nat.add_sub_cancel_left]
  rw [matrixBit_index _ i ⟨j, hj⟩, Matrix.of_apply, decide_val_eq hj]

private theorem getD_ofFn_cert_zero {C : ℕ} (hC : 0 < C) (b : Bool) (τ : Equiv.Perm (Fin n)) :
    (List.ofFn (cert C b τ)).getD 0 false = b := by
  rw [getD_ofFn _ hC]
  simp [cert, certBit]

private theorem decodeMap_cert {C : ℕ} (hC : n * n + 1 ≤ C) (b : Bool) (τ : Equiv.Perm (Fin n)) :
    decodeMap n 1 (List.ofFn (cert C b τ)) = τ := by
  funext i
  refine Fin.ext (image_eq (τ i).2 fun j hj => ?_)
  have hlt : (i : ℕ) * n + j < n * n := index_lt i ⟨j, hj⟩
  rw [List.getD_eq_getElem?_getD, List.getElem?_drop, ← List.getD_eq_getElem?_getD,
    getD_ofFn _ (by omega)]
  simp only [cert, certBit, show 1 + (i * n + j) ≠ 0 by omega, ↓reduceIte,
    Nat.add_sub_cancel_left]
  rw [matrixBit_index _ i ⟨j, hj⟩, Matrix.of_apply, decide_val_eq hj]

/-! ### The test -/

/-- The test of an element `u` and a certificate `v`, for matrices of size `n`, elements of `E` bits
and the adjacency `adj b i j` of graph `b`. Write `f` for the map selected by the second matrix of
`u` (`image`), `M` for the first matrix of `u`, `b` for the first
bit of `v` and `τ` for the map selected by the rest of `v`. The test accepts when the bits of `u`
after position `2 n²` are `false`, the second matrix of `u` is the matrix of `f`, `f` is an
injective automorphism of `M`, and `τ` is injective and carries the adjacency of graph `b` to
`M`. -/
def check (n E : ℕ) (adj : Bool → ℕ → ℕ → Bool) (u v : List Bool) : Bool :=
  let f := fun i => image n (u.drop (n * n)) i
  let τ := fun i => image n (v.drop 1) i
  ((List.range (E - 2 * (n * n))).all fun p => !u.getD (2 * (n * n) + p) false) &&
    (List.range n).all fun i => (List.range n).all fun j =>
      (u.getD (n * n + (i * n + j)) false == decide (f i = j)) &&
      (decide (i = j) || decide (f i ≠ f j)) &&
      (u.getD (f i * n + f j) false == u.getD (i * n + j) false) &&
      (decide (i = j) || decide (τ i ≠ τ j)) &&
      (u.getD (τ i * n + τ j) false == adj (v.getD 0 false) i j)

theorem check_eq_true_iff {n E : ℕ} {adj : Bool → ℕ → ℕ → Bool} {u v : List Bool} :
    check n E adj u v = true ↔
      (∀ p < E - 2 * (n * n), u.getD (2 * (n * n) + p) false = false) ∧
      ∀ i < n, ∀ j < n,
        u.getD (n * n + (i * n + j)) false =
          decide (image n (u.drop (n * n)) i = j) ∧
        (i = j ∨ image n (u.drop (n * n)) i ≠
          image n (u.drop (n * n)) j) ∧
        u.getD (image n (u.drop (n * n)) i * n +
          image n (u.drop (n * n)) j) false = u.getD (i * n + j) false ∧
        (i = j ∨ image n (v.drop 1) i ≠ image n (v.drop 1) j) ∧
        u.getD (image n (v.drop 1) i * n +
          image n (v.drop 1) j) false = adj (v.getD 0 false) i j := by
  simp only [check, Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.not_eq_eq_eq_not,
    Bool.not_true, beq_iff_eq, Bool.or_eq_true, decide_eq_true_eq, ne_eq, and_assoc]

/-- The test of the protocol for graph non-isomorphism, with elements of `N(L)` bits, `L` the
length of the encoded pair of graphs: graphs with different numbers of distinct vertices pass, and
otherwise the element and the certificate must pass `check`. -/
def test (N : Polynomial ℕ) (x : (Graph × Graph) × List Bool) : Bool :=
  decide (x.1.2.distinctVertices.length ≠ x.1.1.distinctVertices.length) ||
    check x.1.1.distinctVertices.length (N.eval (encPair encGraph encGraph x.1).length)
      (fun b i j => if b then x.1.2.adjIndex i j else x.1.1.adjIndex i j)
      (x.2.take (N.eval (encPair encGraph encGraph x.1).length))
      (x.2.drop (N.eval (encPair encGraph encGraph x.1).length))

@[local fun_prop]
private theorem computableTidilyInPolyTime_adjIndex
    {γ : Type} {input : γ ↪ List Bool} {G : γ → Graph}
    {i j : γ → ℕ} (hG : ComputableTidilyInPolyTime G input encGraph)
    (hi : ComputableTidilyInPolyTime i input encUnary)
    (hj : ComputableTidilyInPolyTime j input encUnary) :
    ComputableTidilyInPolyTime (fun x => (G x).adjIndex (i x) (j x)) input encBool :=
  (ComputableInPolyTime.tidy (Graph.computableInPolyTime_adjIndex (.of_tidy hG) (.of_tidy hi)
      (.of_tidy hj)))

@[local fun_prop]
private theorem computableTidilyInPolyTime_distinctVertices :
    ComputableTidilyInPolyTime Graph.distinctVertices encGraph (encList encNat) :=
  (ComputableInPolyTime.tidy (Graph.computableInPolyTime_distinctVertices))

/-- The test is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_test (N : Polynomial ℕ) :
    ComputableInPolyTime (test N) (encPair (encPair encGraph encGraph) encBits) encBool := by
  refine .of_tidy ?_
  unfold test check
  dsimp only
  fun_prop

/-! ### Counting the certified pairs -/

section Check

variable {E : ℕ} {adj : Bool → ℕ → ℕ → Bool} {u v : List Bool}

private theorem injective_decodeMap_left (h : check n E adj u v = true) :
    Function.Injective (decodeMap n (n * n) u) := by
  intro i j hij
  rcases ((check_eq_true_iff.1 h).2 i i.2 j j.2).2.1 with h' | h'
  · exact Fin.ext h'
  · exact absurd (congrArg Fin.val hij) h'

private theorem injective_decodeMap_right (h : check n E adj u v = true) :
    Function.Injective (decodeMap n 1 v) := by
  intro i j hij
  rcases ((check_eq_true_iff.1 h).2 i i.2 j j.2).2.2.2.1 with h' | h'
  · exact Fin.ext h'
  · exact absurd (congrArg Fin.val hij) h'

/-- The map selected by an accepted element is an automorphism of its matrix. -/
private theorem reindex_decodeMatrix (h : check n E adj u v = true) :
    Matrix.reindex
        (Equiv.ofBijective _ (Finite.injective_iff_bijective.1 (injective_decodeMap_left h)))
        (Equiv.ofBijective _ (Finite.injective_iff_bijective.1 (injective_decodeMap_left h)))
        (decodeMatrix n u) =
      decodeMatrix n u :=
  reindex_eq_iff.2 fun i j => ((check_eq_true_iff.1 h).2 i i.2 j j.2).2.2.1

/-- The matrix of an accepted element is a relabelling of the graph named by the certificate. -/
private theorem decodeMatrix_mem_orbit (h : check n E adj u v = true) :
    decodeMatrix n u ∈ orbit (Matrix.of fun i j : Fin n => adj (v.getD 0 false) i j) :=
  mem_orbit.2
    ⟨Equiv.ofBijective _ (Finite.injective_iff_bijective.1 (injective_decodeMap_right h)),
      reindex_eq_iff.2 fun i j => ((check_eq_true_iff.1 h).2 i i.2 j j.2).2.2.2.2⟩

end Check

/-- **The certified pairs**: the elements of `E` bits with a certificate of `C` bits that passes
`check` are as many as the pairs of a relabelling of one of the two adjacency matrices and an
automorphism of it. -/
theorem card_filter_check {E C : ℕ} (hE : 2 * (n * n) + 1 ≤ E) (hC : n * n + 1 ≤ C)
    (adj : Bool → ℕ → ℕ → Bool) :
    #{x : BitString E | ∃ z : BitString C, check n E adj (List.ofFn x) (List.ofFn z) = true} =
      #(pairs (Matrix.of fun i j : Fin n => adj false i j) ∪
        pairs (Matrix.of fun i j : Fin n => adj true i j)) := by
  refine card_bij'
    (fun x hx => (decodeMatrix n (List.ofFn x), Equiv.ofBijective _
      (Finite.injective_iff_bijective.1
        (injective_decodeMap_left (mem_filter.1 hx).2.choose_spec))))
    (fun t _ => code E t.1 t.2) (fun x hx => ?_) (fun t ht => ?_) (fun x hx => ?_)
    (fun t ht => ?_)
  · -- an accepted element gives a pair
    have hz := (mem_filter.1 hx).2.choose_spec
    have horb := decodeMatrix_mem_orbit hz
    refine mem_union.2 ?_
    cases hb : (List.ofFn (mem_filter.1 hx).2.choose).getD 0 false <;> rw [hb] at horb
    · exact Or.inl (mem_filter.2 ⟨mem_univ _, horb, reindex_decodeMatrix hz⟩)
    · exact Or.inr (mem_filter.2 ⟨mem_univ _, horb, reindex_decodeMatrix hz⟩)
  · -- a pair has an accepted code
    obtain ⟨M, σ⟩ := t
    obtain ⟨b, hb⟩ : ∃ b : Bool, (M, σ) ∈ pairs (Matrix.of fun i j : Fin n => adj b i j) := by
      rcases mem_union.1 ht with h | h
      · exact ⟨false, h⟩
      · exact ⟨true, h⟩
    obtain ⟨-, horb, haut⟩ := mem_filter.1 hb
    obtain ⟨τ, hτ⟩ := mem_orbit.1 horb
    refine mem_filter.2 ⟨mem_univ _, cert C b τ, check_eq_true_iff.2 ⟨fun p hp => ?_,
      fun i hi j hj => ?_⟩⟩
    · rw [getD_ofFn _ (by omega)]
      simp only [code, codeBit, show ¬(2 * (n * n) + p < n * n) by omega, ↓reduceIte]
      exact matrixBit_of_le _ (by omega)
    · have hf := congrArg Fin.val (congrFun (decodeMap_code (by omega : 2 * (n * n) ≤ E) M σ)
        ⟨i, hi⟩)
      have hg := congrArg Fin.val (congrFun (decodeMap_cert hC b τ) ⟨i, hi⟩)
      have hf' := congrArg Fin.val (congrFun (decodeMap_code (by omega : 2 * (n * n) ≤ E) M σ)
        ⟨j, hj⟩)
      have hg' := congrArg Fin.val (congrFun (decodeMap_cert hC b τ) ⟨j, hj⟩)
      simp only [decodeMap] at hf hg hf' hg'
      have hM (i' j' : Fin n) : (List.ofFn (code E M σ)).getD (i' * n + j') false = M i' j' := by
        simpa [decodeMatrix] using
          congrFun₂ (decodeMatrix_code (by omega : n * n ≤ E) M σ) i' j'
      rw [hf, hg, hf', hg', getD_ofFn_cert_zero (by omega)]
      have hlt : i * n + j < n * n := index_lt ⟨i, hi⟩ ⟨j, hj⟩
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · rw [getD_ofFn _ (by omega)]
        simp only [code, codeBit, show ¬(n * n + (i * n + j) < n * n) by omega, ↓reduceIte,
          Nat.add_sub_cancel_left]
        rw [matrixBit_index _ ⟨i, hi⟩ ⟨j, hj⟩, Matrix.of_apply]
        exact decide_eq_decide.2 Fin.ext_iff
      · by_cases hij : i = j
        · exact Or.inl hij
        · exact Or.inr fun h => hij (by simpa using σ.injective (Fin.ext h))
      · rw [hM, hM ⟨i, hi⟩ ⟨j, hj⟩]
        exact reindex_eq_iff.1 haut ⟨i, hi⟩ ⟨j, hj⟩
      · by_cases hij : i = j
        · exact Or.inl hij
        · exact Or.inr fun h => hij (by simpa using τ.injective (Fin.ext h))
      · rw [hM]
        exact reindex_eq_iff.1 hτ ⟨i, hi⟩ ⟨j, hj⟩
  · -- decoding an accepted element and coding it again gives it back
    have hz := (mem_filter.1 hx).2.choose_spec
    obtain ⟨hrest, hrows⟩ := check_eq_true_iff.1 hz
    funext p
    change codeBit _ _ p.1 = x p
    by_cases h₁ : p.1 < n * n
    · simp only [codeBit, h₁, ↓reduceIte, matrixBit, ↓reduceDIte, BitString.blocksEquiv_symm_apply,
        Matrix.of_symm_apply, decodeMatrix, Matrix.of_apply]
      rw [index_symm h₁, getD_ofFn _ p.2]
    · by_cases h₂ : p.1 - n * n < n * n
      · simp only [codeBit, h₁, ↓reduceIte, matrixBit, h₂, ↓reduceDIte,
          BitString.blocksEquiv_symm_apply, Matrix.of_symm_apply, Matrix.of_apply,
          Equiv.ofBijective_apply, decodeMap]
        have hrow := (hrows _ (finProdFinEquiv.symm ⟨p.1 - n * n, h₂⟩).1.2 _
          (finProdFinEquiv.symm ⟨p.1 - n * n, h₂⟩).2.2).1
        rw [index_symm h₂, Nat.add_sub_cancel' (by omega), getD_ofFn _ p.2] at hrow
        rw [hrow]
        exact decide_eq_decide.2 Fin.ext_iff
      · simp only [codeBit, h₁, ↓reduceIte, matrixBit_of_le _ (Nat.not_lt.1 h₂)]
        have := hrest (p.1 - 2 * (n * n)) (by omega)
        rw [Nat.add_sub_cancel' (by omega), getD_ofFn _ p.2] at this
        exact this.symm
  · -- coding a pair and decoding it gives it back
    refine Prod.ext (decodeMatrix_code (by omega) _ _) (Equiv.ext fun i => ?_)
    simp only [Equiv.ofBijective_apply]
    exact congrFun (decodeMap_code (by omega) _ _) i

end PublicCoin

open PublicCoin

/-- Graphs with equally many distinct vertices are isomorphic exactly when the adjacency matrix of
the second, on positions, is a relabelling of that of the first. -/
theorem mem_GraphIsomorphism_iff_mem_orbit {G₀ G₁ : Graph}
    (h : G₁.distinctVertices.length = G₀.distinctVertices.length) :
    (G₀, G₁) ∈ GraphIsomorphism ↔
      (Matrix.of fun i j : Fin G₀.distinctVertices.length => G₁.adjIndex i j) ∈
        orbit (Matrix.of fun i j : Fin G₀.distinctVertices.length => G₀.adjIndex i j) := by
  rw [mem_GraphIsomorphism_iff_exists_perm h, mem_orbit]
  refine exists_congr fun τ => ?_
  rw [reindex_eq_iff]
  simp only [Matrix.of_apply]

/-- **Graph non-isomorphism is in `AM`** [Goldwasser and Sipser][GoldwasserSipser1986],
[Arora and Barak, Section 8.2][AroraBarak09]: the set lower bound protocol applied to the pairs
of a relabelling of one of the graphs and an automorphism of it, which are `2 n!` many for
non-isomorphic graphs with `n` distinct vertices each and `n!` many for isomorphic graphs. -/
theorem mem_AM : GraphNonIsomorphism ∈ AM (encPair encGraph encGraph) := by
  set N : Polynomial ℕ := 2 * Polynomial.X ^ 2 + 1 with hN
  set c : Polynomial ℕ := Polynomial.X ^ 2 + 1 with hc
  have hK : ComputableTidilyInPolyTime
      (fun a : Graph × Graph => 2 * a.1.distinctVertices.length.factorial)
      (encPair encGraph encGraph) encNat :=
    (ComputableTidilyInPolyTime.const 2).binary_mul'
      (ComputableTidilyInPolyTime.binary_factorial.comp
        ((ComputableTidilyInPolyTime.length_list encNat).comp
          (Graph.computableInPolyTime_distinctVertices.tidy.comp
            (ComputableTidilyInPolyTime.fst encGraph encGraph))))
  -- the lengths
  have hlen (G₀ G₁ : Graph) :
      G₀.distinctVertices.length * G₀.distinctVertices.length ≤
        (encPair encGraph encGraph (G₀, G₁)).length ^ 2 := by
    have := G₀.length_distinctVertices_le
    have : G₀.distinctVertices.length ≤ (encPair encGraph encGraph (G₀, G₁)).length := by
      simp only [length_encPair]
      omega
    nlinarith
  have hE (L : ℕ) : N.eval L = 2 * L ^ 2 + 1 := by simp [hN]
  have hC (L : ℕ) : c.eval L = L ^ 2 + 1 := by simp [hc]
  -- with equally many vertices, the certified set has `n!` or `2 n!` elements
  have hpairs (G₀ G₁ : Graph) (h : G₁.distinctVertices.length = G₀.distinctVertices.length) :
      #(certifiedSet (encPair encGraph encGraph) N c (test N) (G₀, G₁)) =
        #(pairs (Matrix.of fun i j : Fin G₀.distinctVertices.length => G₀.adjIndex i j) ∪
          pairs (Matrix.of fun i j : Fin G₀.distinctVertices.length => G₁.adjIndex i j)) := by
    have hset : certifiedSet (encPair encGraph encGraph) N c (test N) (G₀, G₁) =
        univ.filter fun x : BitString (N.eval (encPair encGraph encGraph (G₀, G₁)).length) =>
          ∃ z : BitString (c.eval (encPair encGraph encGraph (G₀, G₁)).length),
            check G₀.distinctVertices.length (N.eval (encPair encGraph encGraph (G₀, G₁)).length)
              (fun b i j => if b then G₁.adjIndex i j else G₀.adjIndex i j)
              (List.ofFn x) (List.ofFn z) = true := by
      refine filter_congr fun x _ => exists_congr fun z => ?_
      simp only [test, h, ne_eq, not_true_eq_false, decide_false, Bool.false_or,
        List.take_left' List.length_ofFn, List.drop_left' List.length_ofFn]
    have hlen' := hlen G₀ G₁
    rw [hset, card_filter_check (by rw [hE]; omega) (by rw [hC]; omega)]
    rfl
  refine mem_AM_of_card_certifiedSet (N := N) (c := c) (R := test N)
    (computableInPolyTime_test N) (.of_tidy hK) (fun a => by positivity) (fun a ha => ?_)
    fun a ha => ?_
  · obtain ⟨G₀, G₁⟩ := a
    dsimp only
    by_cases h : G₁.distinctVertices.length = G₀.distinctVertices.length
    · rw [hpairs G₀ G₁ h, card_pairs_union,
        ite_eq_right fun hmem => ha ((mem_GraphIsomorphism_iff_mem_orbit h).2 hmem)]
    · -- with different numbers of vertices, every string is certified
      have hset : certifiedSet (encPair encGraph encGraph) N c (test N) (G₀, G₁) = univ := by
        refine filter_true_of_mem fun x _ => ⟨fun _ => false, ?_⟩
        simp only [test, h, ne_eq, not_false_eq_true, decide_true, Bool.true_or]
      have hlen' := hlen G₀ G₁
      rw [hset, card_univ, BitString.card, hE]
      have hfac : G₀.distinctVertices.length.factorial ≤
          2 ^ (2 * (encPair encGraph encGraph (G₀, G₁)).length ^ 2) :=
        calc G₀.distinctVertices.length.factorial
            ≤ G₀.distinctVertices.length ^ G₀.distinctVertices.length := Nat.factorial_le_pow _
          _ ≤ (2 ^ G₀.distinctVertices.length) ^ G₀.distinctVertices.length :=
            Nat.pow_le_pow_left (Nat.lt_two_pow_self).le _
          _ = 2 ^ (G₀.distinctVertices.length * G₀.distinctVertices.length) := by rw [← pow_mul]
          _ ≤ 2 ^ (2 * (encPair encGraph encGraph (G₀, G₁)).length ^ 2) :=
            Nat.pow_le_pow_right (by norm_num) (by omega)
      rw [pow_succ]
      omega
  · obtain ⟨G₀, G₁⟩ := a
    have hiso : (G₀, G₁) ∈ GraphIsomorphism := not_not.1 ha
    have h := length_distinctVertices_eq_of_mem_GraphIsomorphism hiso
    rw [hpairs G₀ G₁ h, card_pairs_union,
      ite_eq_left ((mem_GraphIsomorphism_iff_mem_orbit h).1 hiso)]

end GraphNonIsomorphism

end Cslib.Complexity
