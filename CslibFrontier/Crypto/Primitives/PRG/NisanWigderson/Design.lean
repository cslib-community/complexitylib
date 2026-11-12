/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Crypto.Primitives.PRG.NisanWigderson
public import CslibFrontier.Foundations.Combinatorics.Design.ReedSolomon
public import Mathlib.Algebra.IsPrimePow
public import Mathlib.Data.Fintype.EquivFin
import Mathlib.FieldTheory.Cardinality
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.NumberTheory.Bertrand

/-!
# Existence of Nisan–Wigderson designs

Nisan and Wigderson build designs from polynomials over a finite field `F` with `q` elements
[NisanWigderson1994]. The universe is the plane `F × F`, and each polynomial `P` of degree less than
`k` contributes its graph `{(x, P x) | x ∈ F}`, a set of `q` points. Two distinct such polynomials
agree on at most `k - 1` points, because their difference is a nonzero polynomial of degree less
than `k`, so two distinct graphs share at most `k - 1` points (`Cslib.polynomialBlock`,
`Cslib.card_polynomialBlock_inter_le`, shared with `Cslib.rsDesign`). There are `q ^ k` polynomials
of degree less than `k`, one for each list of `k` coefficients. Numbering the points of the plane
and the polynomials gives a `(q ^ 2, q, k - 1)`-design with `q ^ k` blocks. Since finite fields
exist in every prime power order, such a design exists whenever `q` is a prime power.

Designs can be adjusted: one may keep only some of the blocks, embed the universe in a larger
one, weaken the bound on intersections, or replace each block by a subset of a given size, since
intersections of subsets are no larger than intersections of the original blocks. Combined with
Bertrand's postulate, which yields a prime `p` with `n < p ≤ 2 n`, this gives for all `n` and `k`
a `(4 n ^ 2, n, k - 1)`-design with `(n + 1) ^ k` blocks.

Arora and Barak construct designs greedily instead [Arora and Barak, Chapter 20][AroraBarak09]; the
greedy construction is not formalized here.

## Main definitions

* `Cslib.Crypto.PRG.NisanWigderson.Design.ofFamily`: the design formed by a family of finite sets
  of equal size and small pairwise intersections, indexed by and living in arbitrary types.
* `Cslib.Crypto.PRG.NisanWigderson.Design.subfamily`, `Cslib.Crypto.PRG.NisanWigderson.Design.map`,
  `Cslib.Crypto.PRG.NisanWigderson.Design.weaken`,
  `Cslib.Crypto.PRG.NisanWigderson.Design.shrink`: fewer blocks, a larger universe, a weaker
  intersection bound, and smaller blocks; `Cslib.Crypto.PRG.NisanWigderson.Design.castLE` does
  all four at once.
* `Cslib.Crypto.PRG.NisanWigderson.Design.polynomial`: the Nisan–Wigderson design of the graphs of
  the polynomials of degree less than `k` over a finite field.

## Main results

* `Cslib.Crypto.PRG.NisanWigderson.Design.nonempty_of_isPrimePow`: for every prime power `q`
  and every `k`, there is a `(q ^ 2, q, k - 1)`-design with `q ^ k` blocks.
* `Cslib.Crypto.PRG.NisanWigderson.Design.nonempty_four_mul_sq`: for all `n` and `k`, there is a
  `(4 n ^ 2, n, k - 1)`-design with `(n + 1) ^ k` blocks.

## References

* [N. Nisan, A. Wigderson, *Hardness vs randomness*][NisanWigderson1994]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09], Chapter 20
-/

@[expose] public section

namespace Cslib.Crypto.PRG.NisanWigderson

open Finset Polynomial

variable {ℓ n a m ℓ' n' a' m' : ℕ}

namespace Design

/-! ### Building and adjusting designs -/

/-- The design formed by a family `B` of `n`-element subsets of a type `U`, any two distinct
members of which share at most `a` elements: its `i`-th block is the member `B (g i)` selected by
an injection `g : Fin m ↪ ι`, carried to `Fin ℓ` by an injection `e : U ↪ Fin ℓ`. -/
@[simps]
def ofFamily {ι U : Type*} [DecidableEq U] (B : ι → Finset U) (card_B : ∀ i, #(B i) = n)
    (card_B_inter_le : Pairwise fun i j => #(B i ∩ B j) ≤ a) (g : Fin m ↪ ι) (e : U ↪ Fin ℓ) :
    Design ℓ n a m where
  block i := (B (g i)).map e
  card_block i := by rw [card_map, card_B]
  card_inter_le hij := by
    rw [← map_inter, card_map]
    exact card_B_inter_le (g.injective.ne hij)

/-- The design formed by the blocks `D.block (g i)` of `D` selected by an injection
`g : Fin m' ↪ Fin m`. -/
@[simps]
def subfamily (D : Design ℓ n a m) (g : Fin m' ↪ Fin m) : Design ℓ n a m' where
  block i := D.block (g i)
  card_block i := D.card_block (g i)
  card_inter_le hij := D.card_inter_le (g.injective.ne hij)

/-- The design `D` carried to a larger universe `Fin ℓ'` by an injection `e : Fin ℓ ↪ Fin ℓ'`. -/
@[simps]
def map (D : Design ℓ n a m) (e : Fin ℓ ↪ Fin ℓ') : Design ℓ' n a m where
  block i := (D.block i).map e
  card_block i := by rw [card_map, D.card_block]
  card_inter_le hij := by
    rw [← map_inter, card_map]
    exact D.card_inter_le hij

/-- The design `D`, seen as a design with the weaker intersection bound `a' ≥ a`. -/
@[simps]
def weaken (D : Design ℓ n a m) (h : a ≤ a') : Design ℓ n a' m where
  block := D.block
  card_block := D.card_block
  card_inter_le hij := (D.card_inter_le hij).trans h

/-- The design whose blocks consist of the `n'` smallest elements of the blocks of `D`, for
`n' ≤ n`. Shrinking blocks does not enlarge their intersections, so the intersection bound `a`
is kept. -/
@[simps]
def shrink (D : Design ℓ n a m) (h : n' ≤ n) : Design ℓ n' a m where
  block i := univ.map <|
    (Fin.castLEEmb h).trans ((D.block i).orderEmbOfFin (D.card_block i)).toEmbedding
  card_block i := by rw [card_map, card_univ, Fintype.card_fin]
  card_inter_le {i j} hij := by
    have hsub (i : Fin m) : univ.map ((Fin.castLEEmb h).trans
        ((D.block i).orderEmbOfFin (D.card_block i)).toEmbedding) ⊆ D.block i := by
      intro x hx
      obtain ⟨k, -, rfl⟩ := mem_map.1 hx
      exact orderEmbOfFin_mem (D.block i) (D.card_block i) _
    exact (card_le_card (inter_subset_inter (hsub i) (hsub j))).trans (D.card_inter_le hij)

/-- The design `D` with fewer blocks (the first `m'`), smaller blocks (of size `n'`), a larger
universe (`Fin ℓ'`) and a weaker intersection bound (`a'`). -/
def castLE (D : Design ℓ n a m) (hℓ : ℓ ≤ ℓ') (hn : n' ≤ n) (ha : a ≤ a') (hm : m' ≤ m) :
    Design ℓ' n' a' m' :=
  (((D.subfamily (Fin.castLEEmb hm)).shrink hn).weaken ha).map (Fin.castLEEmb hℓ)

end Design

/-! ### The polynomial construction -/

section Polynomial

variable (F : Type*) [Field F] [Fintype F] (k : ℕ) [DecidableEq F]

/-- The Nisan–Wigderson design over a finite field `F` with `q` elements [NisanWigderson1994]: a
`(q ^ 2, q, k - 1)`-design with `q ^ k` blocks. Its blocks are the graphs
`Cslib.polynomialBlock F k c` of the polynomials of degree less than `k` over `F`, with the points
of the plane `F × F` and the coefficient vectors `c : Fin k → F` numbered in some order. -/
noncomputable def Design.polynomial :
    Design (Fintype.card F ^ 2) (Fintype.card F) (k - 1) (Fintype.card F ^ k) :=
  .ofFamily (polynomialBlock F k) card_polynomialBlock
    (fun _ _ => card_polynomialBlock_inter_le)
    (Fintype.equivFinOfCardEq (by simp)).symm.toEmbedding
    (Fintype.equivFinOfCardEq (by simp [sq])).toEmbedding

end Polynomial

/-- For every prime power `q` and every `k`, there is a `(q ^ 2, q, k - 1)`-design with `q ^ k`
blocks: the polynomial design `Design.polynomial` over a field with `q` elements
[NisanWigderson1994]. -/
theorem Design.nonempty_of_isPrimePow {q : ℕ} (hq : IsPrimePow q) (k : ℕ) :
    Nonempty (Design (q ^ 2) q (k - 1) (q ^ k)) := by
  obtain ⟨_⟩ := Fintype.nonempty_field_iff.2 (by rwa [Fintype.card_fin] : IsPrimePow
    (Fintype.card (Fin q)))
  rw [← Fintype.card_fin q]
  exact ⟨.polynomial (Fin q) k⟩

/-- For all `n` and `k`, there is a `(4 n ^ 2, n, k - 1)`-design with `(n + 1) ^ k` blocks. By
Bertrand's postulate there is a prime `p` with `n < p ≤ 2 n`; the polynomial design over the
field with `p` elements has `p ^ 2 ≤ 4 n ^ 2` points and `p ^ k ≥ (n + 1) ^ k` blocks of size
`p ≥ n`, and keeping the `n` smallest elements of each block keeps the intersection bound. -/
theorem Design.nonempty_four_mul_sq (n k : ℕ) :
    Nonempty (Design (4 * n ^ 2) n (k - 1) ((n + 1) ^ k)) := by
  rcases eq_or_ne n 0 with rfl | hn
  · exact ⟨⟨fun _ => ∅, fun _ => card_empty, fun _ => by simp⟩⟩
  obtain ⟨p, hp, hnp, hpn⟩ := Nat.exists_prime_lt_and_le_two_mul n hn
  obtain ⟨D⟩ := nonempty_of_isPrimePow hp.prime.isPrimePow k
  refine ⟨D.castLE ?_ hnp.le le_rfl (Nat.pow_le_pow_left hnp k)⟩
  calc p ^ 2 ≤ (2 * n) ^ 2 := Nat.pow_le_pow_left hpn 2
    _ = 4 * n ^ 2 := by ring

end Cslib.Crypto.PRG.NisanWigderson
