/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Combinatorics.Expander.BipartiteRotation
public import CslibFrontier.Foundations.Data.Code.ParityCheck
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# General regular bipartite Tanner codes: distance `δ (δ - λ)`, rate, and shortening

Given a `D`-regular bipartite multigraph `B : BipartiteRotationMap L R D` (retaining parallel
edges) and local codes `CL CR : Set (D → α)`, the **bipartite Tanner code**
`Cslib.BipartiteTanner.code B CL CR` consists of all edge-labelings `x : L × D → α` whose left and
right vertex neighborhoods belong to `CL` and `CR` respectively [SipserSpielman1996]. When `CL`
and `CR` are linear codes, `Cslib.BipartiteTanner.submodule B CL CR` is a linear subcode; when
defined by parity-check matrices `HL`, `HR`, `Cslib.BipartiteTanner.checkMatrix B HL HR` is its
explicit parity-check matrix with row weights at most `|D|`.

## Main definitions

* `Cslib.BipartiteTanner.leftWord`, `Cslib.BipartiteTanner.rightWord`: local edge views at left
  and right vertices.
* `Cslib.BipartiteTanner.code`, `Cslib.BipartiteTanner.submodule`: general and linear bipartite
  Tanner codes.
* `Cslib.BipartiteTanner.checkMatrix`: parity-check matrix of a bipartite Tanner code from local
  check matrices.

## Main results

* `Cslib.BipartiteTanner.parityCheckCode_checkMatrix`,
  `Cslib.BipartiteTanner.hammingNorm_checkMatrix_row_le`,
  `Cslib.BipartiteTanner.hammingNorm_submatrix_row_le`: parity-check equivalence and `|D|`-LDPC
  row-weight bounds (including under shortening).
* `Cslib.BipartiteTanner.rate_submodule_ge`,
  `Cslib.BipartiteTanner.one_sub_card_div_card_le_rate_parityCheck`: rate lower bounds
  `rate CL + rate CR - 1` and `1 - (|ιL| + |ιR|) / |D|`.
* `Cslib.BipartiteTanner.sqrt_mul_sub_card_le_of_hammingDist`,
  `Cslib.BipartiteTanner.mul_sub_card_le_of_hammingDist`,
  `Cslib.BipartiteTanner.relDist_mul_sub_le_hammingDist`,
  `Cslib.BipartiteTanner.le_minDist_of_relDist`: global distance `δ (δ - λ) (d N)` (and
  asymmetric `(kL, kR)` and integer-threshold generalizations) for arbitrary linear or nonlinear
  local codes.
* `Cslib.BipartiteTanner.relDist_mul_sub_le_hammingNorm_of_submatrix`: distance of shortened
  bipartite Tanner parity-check codes.

## References

* [M. Sipser, D. A. Spielman, *Expander codes*][SipserSpielman1996], IEEE Trans. Inf.
  Theory 42(6):1710–1722 (1996). Section VI Lemma 15 (pp. 1715–1716) provides the local-to-global
  distance formula. This formalization marks the two-code, asymmetric, arbitrary-alphabet, and
  finite-ring extensions as original adaptations.
* [S. Hoory, N. Linial, A. Wigderson, *Expander graphs and their applications*]
  [HooryLinialWigderson2006], May 3, 2006 draft (`expanderbookr1.pdf`). Section 2.4 (Lemma 2.5)
  covers the singular-value adaptation (separating the GV coding background in §12.3.1), mapping
  the adjacency-eigenvalue normalization to the normalized biadjacency singular value (including
  bipartite trivial modes) with `d = |D|`, `N = |L| = |R|`, and edge count `d * N`.
-/


public section

namespace Cslib.BipartiteTanner

open Finset Matrix

section LocalWords

variable {L R D α : Type*}

/-- The local word at left vertex `u`: its `D` incident edge labels. -/
@[expose]
def leftWord (x : L × D → α) (u : L) : D → α :=
  fun i => x (u, i)

/-- The local word at right vertex `v`: the `D` incident edge labels pulled back along
`B.toRight.symm`. -/
@[expose]
def rightWord (B : BipartiteRotationMap L R D) (x : L × D → α) (v : R) : D → α :=
  fun j => x (B.toRight.symm (v, j))

/-- Evaluating `rightWord B x` at the right dart `B.toRight (u, i)` recovers `x (u, i)`. -/
@[simp]
theorem rightWord_toRight (B : BipartiteRotationMap L R D) (x : L × D → α) (u : L) (i : D) :
    rightWord B x (B.toRight (u, i)).1 (B.toRight (u, i)).2 = x (u, i) := by
  simp [rightWord]

/-- Linear left-word projection at vertex `u`. -/
@[expose]
def leftWordLinear (S M : Type*) [Semiring S] [AddCommMonoid M] [Module S M] (u : L) :
    (L × D → M) →ₗ[S] (D → M) where
  toFun x := leftWord x u
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem leftWordLinear_apply (S M : Type*) [Semiring S] [AddCommMonoid M] [Module S M]
    (u : L) (x : L × D → M) : leftWordLinear S M u x = leftWord x u :=
  rfl

/-- Linear right-word projection at vertex `v`. -/
@[expose]
def rightWordLinear (S M : Type*) [Semiring S] [AddCommMonoid M] [Module S M]
    (B : BipartiteRotationMap L R D) (v : R) :
    (L × D → M) →ₗ[S] (D → M) where
  toFun x := rightWord B x v
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem rightWordLinear_apply (S M : Type*) [Semiring S] [AddCommMonoid M] [Module S M]
    (B : BipartiteRotationMap L R D) (v : R) (x : L × D → M) :
    rightWordLinear S M B v x = rightWord B x v :=
  rfl

/-- The **bipartite Tanner code** of `B` with local codes `CL` on the left and `CR` on the right.
-/
@[expose]
def code (B : BipartiteRotationMap L R D) (CL CR : Set (D → α)) : Set (L × D → α) :=
  {x | (∀ u, leftWord x u ∈ CL) ∧ (∀ v, rightWord B x v ∈ CR)}

/-- A word lies in `code B CL CR` iff every left neighborhood is in `CL` and every right
neighborhood is in `CR`. -/
@[simp]
theorem mem_code {B : BipartiteRotationMap L R D} {CL CR : Set (D → α)} {x : L × D → α} :
    x ∈ code B CL CR ↔ (∀ u, leftWord x u ∈ CL) ∧ (∀ v, rightWord B x v ∈ CR) :=
  Iff.rfl

/-- The **linear bipartite Tanner code** when `CL` and `CR` are submodules of `D → M`. -/
@[expose]
def submodule {S M : Type*} [Semiring S] [AddCommMonoid M] [Module S M]
    (B : BipartiteRotationMap L R D) (CL CR : Submodule S (D → M)) :
    Submodule S (L × D → M) where
  carrier := code B (CL : Set (D → M)) (CR : Set (D → M))
  zero_mem' := ⟨fun _ => CL.zero_mem, fun _ => CR.zero_mem⟩
  add_mem' hx hy :=
    ⟨fun u => CL.add_mem (hx.1 u) (hy.1 u), fun v => CR.add_mem (hx.2 v) (hy.2 v)⟩
  smul_mem' c _ hx :=
    ⟨fun u => CL.smul_mem c (hx.1 u), fun v => CR.smul_mem c (hx.2 v)⟩

/-- Coercing `submodule B CL CR` to a set yields `code B CL CR`. -/
@[simp]
theorem coe_submodule {S M : Type*} [Semiring S] [AddCommMonoid M] [Module S M]
    (B : BipartiteRotationMap L R D) (CL CR : Submodule S (D → M)) :
    (submodule B CL CR : Set (L × D → M)) = code B (CL : Set (D → M)) (CR : Set (D → M)) :=
  rfl

/-- Membership in `submodule B CL CR`. -/
theorem mem_submodule {S M : Type*} [Semiring S] [AddCommMonoid M] [Module S M]
    {B : BipartiteRotationMap L R D} {CL CR : Submodule S (D → M)} {x : L × D → M} :
    x ∈ submodule B CL CR ↔ (∀ u, leftWord x u ∈ CL) ∧ (∀ v, rightWord B x v ∈ CR) :=
  Iff.rfl

/-- Hamming distance decomposes by left vertices. -/
theorem hammingDist_eq_sum_left [Fintype L] [Fintype D] [DecidableEq α] (x y : L × D → α) :
    hammingDist x y = ∑ u : L, hammingDist (leftWord x u) (leftWord y u) := by
  rw [hammingDist, Finset.card_filter, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun u _ => by
    rw [hammingDist, Finset.card_filter]
    rfl

/-- Hamming distance decomposes by right vertices. -/
theorem hammingDist_eq_sum_right [Fintype L] [Fintype R] [Fintype D] [DecidableEq α]
    (B : BipartiteRotationMap L R D) (x y : L × D → α) :
    hammingDist x y = ∑ v : R, hammingDist (rightWord B x v) (rightWord B y v) := by
  rw [hammingDist, Finset.card_filter]
  rw [Fintype.sum_equiv B.toRight (fun p => if x p ≠ y p then (1 : ℕ) else 0)
    (fun q => if x (B.toRight.symm q) ≠ y (B.toRight.symm q) then 1 else 0)
    fun p => by simp only [Equiv.symm_apply_apply], Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun v _ => by
    rw [hammingDist, Finset.card_filter]
    rfl

/-- Hamming weight decomposes by left vertices. -/
theorem hammingNorm_eq_sum_left [Fintype L] [Fintype D] [Zero α] [DecidableEq α]
    (x : L × D → α) :
    hammingNorm x = ∑ u : L, hammingNorm (leftWord x u) := by
  rw [← hammingDist_zero_right, hammingDist_eq_sum_left]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [← hammingDist_zero_right]
  rfl

/-- Hamming weight decomposes by right vertices. -/
theorem hammingNorm_eq_sum_right [Fintype L] [Fintype R] [Fintype D] [Zero α] [DecidableEq α]
    (B : BipartiteRotationMap L R D) (x : L × D → α) :
    hammingNorm x = ∑ v : R, hammingNorm (rightWord B x v) := by
  rw [← hammingDist_zero_right, hammingDist_eq_sum_right B]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [← hammingDist_zero_right]
  rfl

end LocalWords

section ParityCheck

variable {L R D ιL ιR α : Type*}

/-- Parity-check matrix of a bipartite Tanner code from left check matrix `HL` and right check
matrix `HR`: rows `(u, i)` on `L × ιL` check `leftWord x u`, and rows `(v, i)` on `R × ιR`
check `rightWord B x v`. -/
@[expose]
def checkMatrix [DecidableEq L] [DecidableEq R] [Zero α]
    (B : BipartiteRotationMap L R D) (HL : Matrix ιL D α) (HR : Matrix ιR D α) :
    Matrix (L × ιL ⊕ R × ιR) (L × D) α :=
  Matrix.of fun
    | .inl (u, i), p => if p.1 = u then HL i p.2 else 0
    | .inr (v, i), p => if (B.toRight p).1 = v then HR i (B.toRight p).2 else 0

/-- Left rows of `checkMatrix B HL HR` compute `HL *ᵥ leftWord x u`. -/
theorem checkMatrix_mulVec_inl [Fintype L] [Fintype D] [DecidableEq L] [DecidableEq R]
    [NonUnitalNonAssocSemiring α] (B : BipartiteRotationMap L R D)
    (HL : Matrix ιL D α) (HR : Matrix ιR D α) (x : L × D → α) (u : L) (i : ιL) :
    (checkMatrix B HL HR *ᵥ x) (.inl (u, i)) = (HL *ᵥ leftWord x u) i := by
  simp only [Matrix.mulVec, dotProduct, checkMatrix, Matrix.of_apply, leftWord,
    Fintype.sum_prod_type]
  rw [Finset.sum_eq_single u (fun u' _ hu' => by simp [hu']) (fun hu => absurd (mem_univ u) hu)]
  simp only [ite_true]

/-- Right rows of `checkMatrix B HL HR` compute `HR *ᵥ rightWord B x v`. -/
theorem checkMatrix_mulVec_inr [Fintype L] [Finite R] [Fintype D] [DecidableEq L] [DecidableEq R]
    [NonUnitalNonAssocSemiring α] (B : BipartiteRotationMap L R D)
    (HL : Matrix ιL D α) (HR : Matrix ιR D α) (x : L × D → α) (v : R) (i : ιR) :
    (checkMatrix B HL HR *ᵥ x) (.inr (v, i)) = (HR *ᵥ rightWord B x v) i := by
  let := Fintype.ofFinite R
  simp only [Matrix.mulVec, dotProduct, checkMatrix, Matrix.of_apply, rightWord]
  rw [Fintype.sum_equiv B.toRight
    (fun p => (if (B.toRight p).1 = v then HR i (B.toRight p).2 else 0) * x p)
    (fun q => (if q.1 = v then HR i q.2 else 0) * x (B.toRight.symm q))
    fun p => by simp only [Equiv.symm_apply_apply],
    Fintype.sum_prod_type]
  rw [Finset.sum_eq_single v (fun v' _ hv' => by simp [hv']) (fun hv => absurd (mem_univ v) hv)]
  simp only [ite_true]

/-- The parity-check code of `checkMatrix B HL HR` is `submodule B (parityCheckCode HL)
(parityCheckCode HR)`. -/
theorem parityCheckCode_checkMatrix [Fintype L] [Finite R] [Fintype D]
    [DecidableEq L] [DecidableEq R] [CommRing α] (B : BipartiteRotationMap L R D)
    (HL : Matrix ιL D α) (HR : Matrix ιR D α) :
    Code.parityCheckCode (checkMatrix B HL HR) =
      submodule B (Code.parityCheckCode HL) (Code.parityCheckCode HR) := by
  ext x
  simp only [Code.mem_parityCheckCode, mem_submodule, funext_iff, Sum.forall, Prod.forall,
    checkMatrix_mulVec_inl, checkMatrix_mulVec_inr, Pi.zero_apply]

/-- Every row of `checkMatrix B HL HR` has Hamming weight at most `|D|`. -/
theorem hammingNorm_checkMatrix_row_le [Fintype L] [Fintype D]
    [DecidableEq L] [DecidableEq R] [Zero α] [DecidableEq α] (B : BipartiteRotationMap L R D)
    (HL : Matrix ιL D α) (HR : Matrix ιR D α) (r : L × ιL ⊕ R × ιR) :
    hammingNorm (checkMatrix B HL HR r) ≤ Fintype.card D := by
  rw [hammingNorm]
  rcases r with ⟨u, i⟩ | ⟨v, i⟩
  · refine (card_le_card_of_injOn (t := (univ : Finset D)) Prod.snd
      (fun _ _ => mem_univ _) ?_).trans (by simp)
    intro p hp p' hp' hpp'
    simp only [mem_coe, checkMatrix, Matrix.of_apply] at hp hp'
    have hpu : p.1 = u := by by_contra h; simp [h] at hp
    have hp'u : p'.1 = u := by by_contra h; simp [h] at hp'
    exact Prod.ext (hpu.trans hp'u.symm) hpp'
  · refine (card_le_card_of_injOn (t := (univ : Finset D)) (fun p => (B.toRight p).2)
      (fun _ _ => mem_univ _) ?_).trans (by simp)
    intro p hp p' hp' hpp'
    simp only [mem_coe, checkMatrix, Matrix.of_apply] at hp hp'
    have hpv : (B.toRight p).1 = v := by by_contra h; simp [h] at hp
    have hp'v : (B.toRight p').1 = v := by by_contra h; simp [h] at hp'
    exact B.toRight.injective (Prod.ext (hpv.trans hp'v.symm) hpp')

/-- Restricting columns along an embedding `emb : ι' ↪ ι` cannot increase any row's Hamming weight.
-/
theorem hammingNorm_submatrix_row_le {κ ι ι' : Type*} [Fintype ι] [Fintype ι'] [Zero α]
    [DecidableEq α] (H : Matrix κ ι α) (emb : ι' ↪ ι) (r : κ) :
    hammingNorm ((H.submatrix id emb) r) ≤ hammingNorm (H r) := by
  rw [hammingNorm, hammingNorm]
  refine card_le_card_of_injOn emb (fun e he => ?_) fun _ _ _ _ h => emb.injective h
  simp only [mem_coe, mem_filter, mem_univ, true_and] at he ⊢
  simpa only [Matrix.submatrix_apply, id_eq] using he

/-- Rate lower bound `rate CL + rate CR - 1 ≤ rate (submodule B CL CR)` for arbitrary finite
local linear codes `CL` and `CR` over a finite nontrivial commutative ring. -/
theorem rate_submodule_ge [Fintype L] [Finite R] [Fintype D] [CommRing α] [Fintype α]
    [Nontrivial α] (B : BipartiteRotationMap L R D) (hL : 0 < Fintype.card L)
    (hD : 0 < Fintype.card D) (CL CR : Submodule α (D → α)) :
    Code.rate (CL : Set (D → α)) + Code.rate (CR : Set (D → α)) - 1 ≤
      Code.rate (submodule B CL CR : Set (L × D → α)) := by
  let := Fintype.ofFinite R
  have _ : Nonempty D := Fintype.card_pos_iff.1 hD
  have hLR : Fintype.card L = Fintype.card R := B.card_left_eq_card_right
  let φ : (L × D → α) →ₗ[α] (L → (D → α) ⧸ CL) × (R → (D → α) ⧸ CR) :=
    LinearMap.prod
      (LinearMap.pi fun u => CL.mkQ.comp (leftWordLinear α α u))
      (LinearMap.pi fun v => CR.mkQ.comp (rightWordLinear α α B v))
  have hker : φ.ker = submodule B CL CR := by
    ext x
    simp [φ, LinearMap.mem_ker, funext_iff, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero, mem_submodule]
  have hcard := AddSubgroup.card_ker_mul_card_range φ.toAddMonoidHom
  have hker_card : Nat.card φ.toAddMonoidHom.ker = Nat.card (submodule B CL CR) := by
    rw [← hker]; rfl
  have _ : Finite ((D → α) ⧸ CL) := Finite.of_surjective _ CL.mkQ_surjective
  have _ : Finite ((D → α) ⧸ CR) := Finite.of_surjective _ CR.mkQ_surjective
  have hrange_le : Nat.card φ.toAddMonoidHom.range ≤
      Nat.card ((D → α) ⧸ CL) ^ Fintype.card L * Nat.card ((D → α) ⧸ CR) ^ Fintype.card R := by
    refine (Nat.card_le_card_of_injective _ Subtype.val_injective).trans_eq ?_
    rw [Nat.card_prod, Nat.card_fun, Nat.card_fun, Nat.card_eq_fintype_card (α := L),
      Nat.card_eq_fintype_card (α := R)]
  have hdom : Nat.card (L × D → α) = Fintype.card α ^ (Fintype.card L * Fintype.card D) := by
    rw [Nat.card_fun, Nat.card_eq_fintype_card (α := L × D),
      Nat.card_eq_fintype_card (α := α), Fintype.card_prod]
  have hqL : Nat.card CL * Nat.card ((D → α) ⧸ CL) = Fintype.card α ^ Fintype.card D := by
    simpa [Submodule.ker_mkQ, Nat.card_fun, Nat.card_eq_fintype_card] using
      AddSubgroup.card_ker_mul_card_of_surjective (f := CL.mkQ.toAddMonoidHom) CL.mkQ_surjective
  have hqR : Nat.card CR * Nat.card ((D → α) ⧸ CR) = Fintype.card α ^ Fintype.card D := by
    simpa [Submodule.ker_mkQ, Nat.card_fun, Nat.card_eq_fintype_card] using
      AddSubgroup.card_ker_mul_card_of_surjective (f := CR.mkQ.toAddMonoidHom) CR.mkQ_surjective
  have hpow_le :
      (Nat.card CL * Nat.card CR) ^ Fintype.card L ≤
        Nat.card (submodule B CL CR) * (Fintype.card α ^ Fintype.card D) ^ Fintype.card L := by
    have hmul : Fintype.card α ^ (Fintype.card L * Fintype.card D) ≤
        Nat.card (submodule B CL CR) *
          (Nat.card ((D → α) ⧸ CL) ^ Fintype.card L *
            Nat.card ((D → α) ⧸ CR) ^ Fintype.card R) := by
      rw [← hdom, ← hcard, hker_card]
      exact Nat.mul_le_mul_left _ hrange_le
    rw [← hLR] at hmul
    have hmul2 := Nat.mul_le_mul_right (Nat.card CL ^ Fintype.card L * Nat.card CR ^ Fintype.card L)
      hmul
    have hpos : 0 < (Fintype.card α ^ Fintype.card D) ^ Fintype.card L := by positivity
    have hrew : (Fintype.card α ^ Fintype.card D) ^ Fintype.card L =
        Fintype.card α ^ (Fintype.card L * Fintype.card D) := by
      rw [← pow_mul, mul_comm]
    have hpow2 :
        (Nat.card CL * Nat.card CR) ^ Fintype.card L *
            (Fintype.card α ^ Fintype.card D) ^ Fintype.card L ≤
          (Nat.card (submodule B CL CR) * (Fintype.card α ^ Fintype.card D) ^ Fintype.card L) *
            (Fintype.card α ^ Fintype.card D) ^ Fintype.card L := by
      calc
        (Nat.card CL * Nat.card CR) ^ Fintype.card L *
            (Fintype.card α ^ Fintype.card D) ^ Fintype.card L
          = Fintype.card α ^ (Fintype.card L * Fintype.card D) *
              (Nat.card CL ^ Fintype.card L * Nat.card CR ^ Fintype.card L) := by
            rw [mul_pow, hrew]; ring
        _ ≤ Nat.card (submodule B CL CR) *
              (Nat.card ((D → α) ⧸ CL) ^ Fintype.card L *
                Nat.card ((D → α) ⧸ CR) ^ Fintype.card L) *
              (Nat.card CL ^ Fintype.card L * Nat.card CR ^ Fintype.card L) := hmul2
        _ = Nat.card (submodule B CL CR) *
              ((Nat.card CL * Nat.card ((D → α) ⧸ CL)) ^ Fintype.card L *
                (Nat.card CR * Nat.card ((D → α) ⧸ CR)) ^ Fintype.card L) := by
            simp only [mul_pow]; ring
        _ = (Nat.card (submodule B CL CR) * (Fintype.card α ^ Fintype.card D) ^ Fintype.card L) *
              (Fintype.card α ^ Fintype.card D) ^ Fintype.card L := by
            rw [hqL, hqR]; ring
    exact Nat.le_of_mul_le_mul_right hpow2 hpos
  have hα : (1 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.one_lt_card
  have hα0 : (0 : ℝ) < Fintype.card α := by linarith
  have hCL_pos : (0 : ℝ) < Nat.card CL := by exact_mod_cast Nat.card_pos (α := CL)
  have hCR_pos : (0 : ℝ) < Nat.card CR := by exact_mod_cast Nat.card_pos (α := CR)
  have hSub_pos : (0 : ℝ) < Nat.card (submodule B CL CR) := by
    exact_mod_cast Nat.card_pos (α := submodule B CL CR)
  have hpow_r :
      ((Nat.card CL : ℝ) * Nat.card CR) ^ Fintype.card L ≤
        (Nat.card (submodule B CL CR) : ℝ) *
          ((Fintype.card α : ℝ) ^ Fintype.card D) ^ Fintype.card L := by
    exact_mod_cast hpow_le
  have hlog := Real.logb_le_logb_of_le hα (by positivity) hpow_r
  rw [Real.logb_pow, Real.logb_mul hCL_pos.ne' hCR_pos.ne',
    Real.logb_mul hSub_pos.ne' (by positivity), Real.logb_pow,
    show ((Fintype.card α : ℝ) ^ Fintype.card D) =
      (Fintype.card α : ℝ) ^ (Fintype.card D : ℝ) by rw [Real.rpow_natCast],
    Real.logb_rpow hα0 (by linarith)] at hlog
  have hL0 : (0 : ℝ) < Fintype.card L := by exact_mod_cast hL
  have hD0 : (0 : ℝ) < Fintype.card D := by exact_mod_cast hD
  have hcardL : Nat.card (CL : Set (D → α)) = Nat.card CL := rfl
  have hcardR : Nat.card (CR : Set (D → α)) = Nat.card CR := rfl
  have hcardS : Nat.card (submodule B CL CR : Set (L × D → α)) = Nat.card (submodule B CL CR) := rfl
  simp only [Code.rate, hcardL, hcardR, hcardS, Fintype.card_prod, Nat.cast_mul]
  refine le_of_mul_le_mul_right ?_ (mul_pos hL0 hD0)
  field_simp
  linarith

/-- Parity-check rate lower bound for bipartite Tanner codes: if `HL` has `|ιL|` checks and `HR`
has `|ιR|` checks over a finite nontrivial commutative ring `α`, then the Tanner code has rate at
least `1 - (|ιL| + |ιR|) / |D|`. -/
theorem one_sub_card_div_card_le_rate_parityCheck [Fintype L] [Finite R] [Fintype D]
    [Fintype ιL] [Fintype ιR] [CommRing α] [Fintype α] [Nontrivial α]
    (B : BipartiteRotationMap L R D) (hL : 0 < Fintype.card L) (hD : 0 < Fintype.card D)
    (HL : Matrix ιL D α) (HR : Matrix ιR D α) :
    1 - ((Fintype.card ιL : ℝ) + Fintype.card ιR) / Fintype.card D ≤
      Code.rate (code B (Code.parityCheckCode HL : Set (D → α))
        (Code.parityCheckCode HR : Set (D → α))) := by
  classical
  let := Fintype.ofFinite R
  have _ : Nonempty D := Fintype.card_pos_iff.1 hD
  have hLR : Fintype.card L = Fintype.card R := B.card_left_eq_card_right
  have h := Code.one_sub_card_div_card_le_rate_parityCheckCode
    (show 0 < Fintype.card (L × D) by rw [Fintype.card_prod]; exact Nat.mul_pos hL hD)
    (checkMatrix B HL HR)
  rw [parityCheckCode_checkMatrix, coe_submodule] at h
  have hcard_eq : (Fintype.card (L × ιL ⊕ R × ιR) : ℝ) / Fintype.card (L × D) =
      ((Fintype.card ιL : ℝ) + Fintype.card ιR) / Fintype.card D := by
    simp only [Fintype.card_sum, Fintype.card_prod, Nat.cast_add, Nat.cast_mul, hLR]
    have hR0 : (Fintype.card R : ℝ) ≠ 0 := by exact_mod_cast (hLR ▸ hL).ne'
    have hD0 : (Fintype.card D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
    field_simp
  linarith

end ParityCheck

section Distance

variable {L R D α : Type*}

private theorem core_tanner_bound {k lam d N W u v : ℝ} (hk : 0 ≤ k) (hlam : 0 ≤ lam)
    (hd : 0 ≤ d) (hN : 0 < N) (hW : 0 < W) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hk2 : k ^ 2 * (u * v) ≤ W ^ 2) (hup : W ≤ d * (u * v) / N + lam * d * √(u * v)) :
    k * (k - lam * d) * N ≤ d * W := by
  have hkt2 : (k * √(u * v)) ^ 2 ≤ W ^ 2 := by
    rwa [mul_pow, Real.sq_sqrt (mul_nonneg hu hv)]
  have hkt : k * √(u * v) ≤ W :=
    (pow_le_pow_iff_left₀ (by positivity) hW.le two_ne_zero).1 hkt2
  have hkW : k ^ 2 * W ≤ (d * W / N + k * lam * d) * W :=
    calc
      k ^ 2 * W ≤ k ^ 2 * (d * (u * v) / N + lam * d * √(u * v)) :=
          mul_le_mul_of_nonneg_left hup (sq_nonneg k)
      _ = d * (k ^ 2 * (u * v)) / N + (k * lam * d) * (k * √(u * v)) := by ring
      _ ≤ d * W ^ 2 / N + (k * lam * d) * W := by gcongr
      _ = (d * W / N + k * lam * d) * W := by ring
  have hk1 : k ^ 2 ≤ d * W / N + k * lam * d := le_of_mul_le_mul_right hkW hW
  have hkN := mul_le_mul_of_nonneg_right hk1 hN.le
  rw [add_mul, div_mul_cancel₀ _ hN.ne'] at hkN
  linarith

private theorem hammingDist_le_card_interedges [Fintype L] [Fintype R] [Fintype D]
    [DecidableEq R] [DecidableEq α] (B : BipartiteRotationMap L R D) (x y : L × D → α) :
    hammingDist x y ≤
      #(B.interedges {u | leftWord x u ≠ leftWord y u}
        {v | rightWord B x v ≠ rightWord B y v}) := by
  classical
  rw [hammingDist]
  refine card_le_card fun p hp => ?_
  rcases p with ⟨u, i⟩
  simp only [mem_filter, mem_univ, true_and] at hp
  rw [B.mem_interedges]
  refine ⟨?_, ?_⟩
  · simp only [mem_filter, mem_univ, true_and]
    intro h0
    exact hp (congrFun h0 i)
  · simp only [mem_filter, mem_univ, true_and, BipartiteRotationMap.neighborRight]
    intro h0
    have hval := congrFun h0 (B.toRight (u, i)).2
    simp only [rightWord_toRight] at hval
    exact hp hval

/-- **Asymmetric bipartite Tanner code distance bound**: if distinct words in `CL` are separated
by at least `kL ≥ 0` and distinct words in `CR` are separated by at least `kR ≥ 0`, and
`B.nontrivialSingularValue ≤ lam`, then any distinct `x, y ∈ code B CL CR` satisfy
`√(kL * kR) * (√(kL * kR) - lam * |D|) * |L| ≤ |D| * hammingDist x y`. -/
theorem sqrt_mul_sub_card_le_of_hammingDist [Fintype L] [Fintype R] [Fintype D]
    (B : BipartiteRotationMap L R D) [Nonempty D] [DecidableEq α]
    {CL CR : Set (D → α)} {kL kR lam : ℝ} (hkL : 0 ≤ kL) (hkR : 0 ≤ kR)
    (hCL : ∀ w₁ ∈ CL, ∀ w₂ ∈ CL, w₁ ≠ w₂ → kL ≤ hammingDist w₁ w₂)
    (hCR : ∀ w₁ ∈ CR, ∀ w₂ ∈ CR, w₁ ≠ w₂ → kR ≤ hammingDist w₁ w₂)
    (hlam : B.nontrivialSingularValue ≤ lam) {x y : L × D → α}
    (hx : x ∈ code B CL CR) (hy : y ∈ code B CL CR) (hxy : x ≠ y) :
    √(kL * kR) * (√(kL * kR) - lam * Fintype.card D) * Fintype.card L ≤
      Fintype.card D * hammingDist x y := by
  classical
  let U : Finset L := {u | leftWord x u ≠ leftWord y u}
  let W : Finset R := {v | rightWord B x v ≠ rightWord B y v}
  have hU : kL * #U ≤ hammingDist x y := by
    calc
      kL * #U = ∑ _u ∈ U, kL := by rw [sum_const, nsmul_eq_mul, mul_comm]
      _ ≤ ∑ u ∈ U, (hammingDist (leftWord x u) (leftWord y u) : ℝ) :=
          sum_le_sum fun u hu => hCL _ (hx.1 u) _ (hy.1 u) (mem_filter.mp hu).2
      _ ≤ hammingDist x y := by
          rw [hammingDist_eq_sum_left x y]
          exact_mod_cast sum_le_sum_of_subset (subset_univ U)
  have hW : kR * #W ≤ hammingDist x y := by
    calc
      kR * #W = ∑ _v ∈ W, kR := by rw [sum_const, nsmul_eq_mul, mul_comm]
      _ ≤ ∑ v ∈ W, (hammingDist (rightWord B x v) (rightWord B y v) : ℝ) :=
          sum_le_sum fun v hv => hCR _ (hx.2 v) _ (hy.2 v) (mem_filter.mp hv).2
      _ ≤ hammingDist x y := by
          rw [hammingDist_eq_sum_right B x y]
          exact_mod_cast sum_le_sum_of_subset (subset_univ W)
  have hpos : 0 < hammingDist x y := Nat.pos_of_ne_zero (mt hammingDist_eq_zero.1 hxy)
  have hWpos : (0 : ℝ) < hammingDist x y := by exact_mod_cast hpos
  obtain ⟨u₀, hu₀⟩ : ∃ u : L, u ∈ U := by
    obtain ⟨⟨u, i⟩, hne⟩ := Function.ne_iff.1 hxy
    exact ⟨u, mem_filter.2 ⟨mem_univ u, fun h => hne (congrFun h i)⟩⟩
  have hN : (0 : ℝ) < Fintype.card L := Nat.cast_pos.2 (Fintype.card_pos_iff.2 ⟨u₀⟩)
  have hWE : (hammingDist x y : ℝ) ≤ #(B.interedges U W) :=
    Nat.cast_le.2 (hammingDist_le_card_interedges B x y)
  have hmix := B.card_interedges_le_of_nontrivialSingularValue_le hlam U W
  have hup : (hammingDist x y : ℝ) ≤
      Fintype.card D * (#U * #W) / Fintype.card L + lam * Fintype.card D * √((#U : ℝ) * #W) := by
    have hmul_assoc : (Fintype.card D : ℝ) * (#U * #W) / Fintype.card L =
        Fintype.card D * #U * #W / Fintype.card L := by ring
    linarith
  have hk2 : √(kL * kR) ^ 2 * ((#U : ℝ) * #W) ≤ (hammingDist x y : ℝ) ^ 2 := by
    rw [Real.sq_sqrt (mul_nonneg hkL hkR)]
    calc
      kL * kR * ((#U : ℝ) * #W) = (kL * #U) * (kR * #W) := by ring
      _ ≤ (hammingDist x y : ℝ) * hammingDist x y :=
          mul_le_mul hU hW (mul_nonneg hkR (Nat.cast_nonneg _)) hWpos.le
      _ = (hammingDist x y : ℝ) ^ 2 := by ring
  exact core_tanner_bound (Real.sqrt_nonneg _) (B.nontrivialSingularValue_nonneg.trans hlam)
    (Nat.cast_nonneg _) hN hWpos (Nat.cast_nonneg _) (Nat.cast_nonneg _) hk2 hup

/-- **Bipartite Tanner code distance bound** (threshold form): if distinct local words in `CL` and
`CR` are separated by at least `k ≥ 0` and `B.nontrivialSingularValue ≤ lam`, then any distinct
`x, y ∈ code B CL CR` satisfy `k * (k - lam * |D|) * |L| ≤ |D| * hammingDist x y`. -/
theorem mul_sub_card_le_of_hammingDist [Fintype L] [Fintype R] [Fintype D]
    (B : BipartiteRotationMap L R D) [Nonempty D] [DecidableEq α]
    {CL CR : Set (D → α)} {k lam : ℝ} (hk : 0 ≤ k)
    (hCL : ∀ w₁ ∈ CL, ∀ w₂ ∈ CL, w₁ ≠ w₂ → k ≤ hammingDist w₁ w₂)
    (hCR : ∀ w₁ ∈ CR, ∀ w₂ ∈ CR, w₁ ≠ w₂ → k ≤ hammingDist w₁ w₂)
    (hlam : B.nontrivialSingularValue ≤ lam) {x y : L × D → α}
    (hx : x ∈ code B CL CR) (hy : y ∈ code B CL CR) (hxy : x ≠ y) :
    k * (k - lam * Fintype.card D) * Fintype.card L ≤ Fintype.card D * hammingDist x y := by
  simpa only [← mul_self_eq_mul_self_iff, Real.sqrt_mul_self hk] using
    sqrt_mul_sub_card_le_of_hammingDist B hk hk hCL hCR hlam hx hy hxy

/-- **Global relative distance `δ (δ - λ)` of general `d`-regular bipartite Tanner codes**: if
`CL` and `CR` have relative distance at least `δ ≥ 0` (`δ |D| ≤ hammingDist` on distinct local
codewords) and `B.nontrivialSingularValue ≤ lam`, then distinct global codewords satisfy
`δ * (δ - lam) * |L × D| ≤ hammingDist x y`. -/
theorem relDist_mul_sub_le_hammingDist [Fintype L] [Fintype R] [Fintype D]
    (B : BipartiteRotationMap L R D) [Nonempty D] [DecidableEq α]
    {CL CR : Set (D → α)} {δ lam : ℝ} (hδ : 0 ≤ δ)
    (hCL : ∀ w₁ ∈ CL, ∀ w₂ ∈ CL, w₁ ≠ w₂ → δ * Fintype.card D ≤ hammingDist w₁ w₂)
    (hCR : ∀ w₁ ∈ CR, ∀ w₂ ∈ CR, w₁ ≠ w₂ → δ * Fintype.card D ≤ hammingDist w₁ w₂)
    (hlam : B.nontrivialSingularValue ≤ lam) {x y : L × D → α}
    (hx : x ∈ code B CL CR) (hy : y ∈ code B CL CR) (hxy : x ≠ y) :
    δ * (δ - lam) * Fintype.card (L × D) ≤ hammingDist x y := by
  have hd : (0 : ℝ) < Fintype.card D := Nat.cast_pos.2 Fintype.card_pos
  have h := mul_sub_card_le_of_hammingDist B (mul_nonneg hδ hd.le) hCL hCR hlam hx hy hxy
  rw [Fintype.card_prod, Nat.cast_mul]
  refine le_of_mul_le_mul_left ?_ hd
  calc
    Fintype.card D * (δ * (δ - lam) * (Fintype.card L * Fintype.card D))
      = δ * Fintype.card D * (δ * Fintype.card D - lam * Fintype.card D) * Fintype.card L := by
        ring
    _ ≤ Fintype.card D * hammingDist x y := h

/-- Minimum distance `minDist (code B CL CR)` is at least any integer `n ≤ δ * (δ - lam) * |L × D|`.
-/
theorem le_minDist_of_relDist [Fintype L] [Fintype R] [Fintype D]
    (B : BipartiteRotationMap L R D) [Nonempty D] [DecidableEq α]
    {CL CR : Set (D → α)} {δ lam : ℝ} (hδ : 0 ≤ δ)
    (hCL : ∀ w₁ ∈ CL, ∀ w₂ ∈ CL, w₁ ≠ w₂ → δ * Fintype.card D ≤ hammingDist w₁ w₂)
    (hCR : ∀ w₁ ∈ CR, ∀ w₂ ∈ CR, w₁ ≠ w₂ → δ * Fintype.card D ≤ hammingDist w₁ w₂)
    (hlam : B.nontrivialSingularValue ≤ lam) {n : ℕ}
    (hn : (n : ℝ) ≤ δ * (δ - lam) * Fintype.card (L × D)) :
    (n : ℕ∞) ≤ Code.minDist (code B CL CR) := by
  refine Code.le_minDist_iff.2 fun x hx y hy hxy => Nat.cast_le.2 ?_
  have h := relDist_mul_sub_le_hammingDist B hδ hCL hCR hlam hx hy hxy
  exact Nat.cast_le.1 (hn.trans h)

/-- Minimum-weight bound `δ * (δ - lam) * |L × D| ≤ hammingNorm x` for nonzero words in a linear
bipartite Tanner code `submodule B CL CR`. -/
theorem relDist_mul_sub_le_hammingNorm_of_submodule [Fintype L] [Fintype R] [Fintype D]
    (B : BipartiteRotationMap L R D) [Nonempty D]
    {S : Type*} [Ring S] [AddCommGroup α] [Module S α] [DecidableEq α]
    {CL CR : Submodule S (D → α)} {δ lam : ℝ} (hδ : 0 ≤ δ)
    (hCL : ∀ w ∈ CL, w ≠ 0 → δ * Fintype.card D ≤ hammingNorm w)
    (hCR : ∀ w ∈ CR, w ≠ 0 → δ * Fintype.card D ≤ hammingNorm w)
    (hlam : B.nontrivialSingularValue ≤ lam) {x : L × D → α}
    (hx : x ∈ submodule B CL CR) (hx0 : x ≠ 0) :
    δ * (δ - lam) * Fintype.card (L × D) ≤ hammingNorm x := by
  have toDist : ∀ {C : Submodule S (D → α)},
      (∀ w ∈ C, w ≠ 0 → δ * Fintype.card D ≤ hammingNorm w) →
      ∀ w₁ ∈ (C : Set (D → α)), ∀ w₂ ∈ (C : Set (D → α)), w₁ ≠ w₂ →
        δ * Fintype.card D ≤ hammingDist w₁ w₂ := by
    intro C hC w₁ hw₁ w₂ hw₂ hne
    rw [hammingDist_eq_hammingNorm]
    exact hC _ (C.add_mem (C.neg_mem hw₁) hw₂) fun h0 => hne (neg_add_eq_zero.1 h0)
  rw [← hammingDist_zero_right x]
  exact relDist_mul_sub_le_hammingDist B hδ (toDist hCL) (toDist hCR) hlam
    hx (submodule B CL CR).zero_mem hx0

/-- Distance of a **shortened** bipartite Tanner parity-check code: every nonzero word `z` in the
kernel of `(checkMatrix B HL HR).submatrix id emb` has weight at least
`δ * (δ - lam) * |L × D|`. -/
theorem relDist_mul_sub_le_hammingNorm_of_submatrix {ιL ιR ι' : Type*}
    [Fintype L] [Fintype R] [Fintype D] [Fintype ι'] [DecidableEq L] [DecidableEq R]
    (B : BipartiteRotationMap L R D) [Nonempty D]
    [CommRing α] [DecidableEq α] (HL : Matrix ιL D α) (HR : Matrix ιR D α)
    {δ lam : ℝ} (hδ : 0 ≤ δ)
    (hHL : ∀ w : D → α, w ≠ 0 → HL *ᵥ w = 0 → δ * Fintype.card D ≤ hammingNorm w)
    (hHR : ∀ w : D → α, w ≠ 0 → HR *ᵥ w = 0 → δ * Fintype.card D ≤ hammingNorm w)
    (hlam : B.nontrivialSingularValue ≤ lam) (emb : ι' ↪ L × D)
    {z : ι' → α} (hz : (checkMatrix B HL HR).submatrix id emb *ᵥ z = 0) (hz0 : z ≠ 0) :
    δ * (δ - lam) * Fintype.card (L × D) ≤ hammingNorm z := by
  classical
  have hext :
      Code.extend emb z ∈ submodule B (Code.parityCheckCode HL) (Code.parityCheckCode HR) := by
    rw [← parityCheckCode_checkMatrix, Code.mem_parityCheckCode, Code.mulVec_extend]
    exact hz
  have hext0 : Code.extend emb z ≠ 0 := fun h0 =>
    hz0 (funext fun e => by simpa only [Code.extend_emb, Pi.zero_apply] using congrFun h0 (emb e))
  rw [← Code.hammingNorm_extend emb z]
  exact relDist_mul_sub_le_hammingNorm_of_submodule B hδ
    (fun w hw hw0 => hHL w hw0 (Code.mem_parityCheckCode.1 hw))
    (fun w hw hw0 => hHR w hw0 (Code.mem_parityCheckCode.1 hw))
    hlam hext hext0

/-- Minimum distance lower bound for the shortened parity-check code
`Code.shortenLinear (Code.parityCheckCode (checkMatrix B HL HR)) emb`. -/
theorem le_minDist_shortenLinear_checkMatrix {ιL ιR ι' : Type*}
    [Fintype L] [Fintype R] [Fintype D] [Fintype ι'] [DecidableEq L] [DecidableEq R]
    (B : BipartiteRotationMap L R D) [Nonempty D]
    [CommRing α] [DecidableEq α] (HL : Matrix ιL D α) (HR : Matrix ιR D α)
    {δ lam : ℝ} (hδ : 0 ≤ δ)
    (hHL : ∀ w : D → α, w ≠ 0 → HL *ᵥ w = 0 → δ * Fintype.card D ≤ hammingNorm w)
    (hHR : ∀ w : D → α, w ≠ 0 → HR *ᵥ w = 0 → δ * Fintype.card D ≤ hammingNorm w)
    (hlam : B.nontrivialSingularValue ≤ lam) (emb : ι' ↪ L × D) {n : ℕ}
    (hn : (n : ℝ) ≤ δ * (δ - lam) * Fintype.card (L × D)) :
    (n : ℕ∞) ≤ Code.minDist
      (Code.shortenLinear (Code.parityCheckCode (checkMatrix B HL HR)) emb : Set (ι' → α)) := by
  rw [Code.shortenLinear_parityCheckCode, Code.le_minDist_iff_hammingNorm]
  intro z hz hz0
  exact Nat.cast_le.2 (Nat.cast_le.1 (hn.trans
    (relDist_mul_sub_le_hammingNorm_of_submatrix B HL HR hδ hHL hHR hlam emb
      (Code.mem_parityCheckCode.1 hz) hz0)))

end Distance

end Cslib.BipartiteTanner
