/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.Homomorphic.GSW.Gadget
public import CslibFrontier.Crypto.Computational.LWE.Decoding
public import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Nat.Bitwise

/-!
# Micciancio–Peikert primitive gadget matrices, short bases, and gadget inversion

This module formalizes the power-of-two primitive gadget construction of
[Micciancio and Peikert, Section 4, Theorem 4.1 and Proposition 4.2][MicciancioPeikert2012]
at modulus `q = 2 ^ w`, reusing the binary decomposition and recomposition operations from
`Cslib.Crypto.Homomorphic.GSW` (`GSW.bitDecomp`, `GSW.bitCompose`, `GSW.powersOfTwo`) and the
half-modulus bit decoder `LWE.decode` from `Cslib.Crypto.LWE`:

1. **Primitive gadget vector and matrix (`gadgetVector`, `gadgetMatrix`):**
   The geometric vector `g = (1, 2, …, 2 ^ (w - 1)) ∈ (ZMod (2 ^ w)) ^ w` (Equation 4.1) and
   its block-diagonal tensor expansion `G = I_ι ⊗ gᵀ : Matrix ι (ι × Fin w) (ZMod (2 ^ w))`.
   Multiplication by `G` on the right is `GSW.bitCompose` (`gadgetMatrix_mulVec`), and
   multiplication on the left is `GSW.powersOfTwo` (`vecMul_gadgetMatrix`).
2. **Deterministic syndrome decomposition (`scalarDecomp`, `gadgetDecomp`, `gadgetDecompMatrix`):**
   Lifting `GSW.bitDecomp` to `{0, 1}`-valued integer vectors gives a right inverse to
   `f_G(x) = G x mod 2 ^ w` (`gadgetMatrix_mulVec_gadgetDecomp`,
   `gadgetMatrix_mul_gadgetDecompMatrix`), establishing that `G` is primitive
   (`gadgetMatrix_surjective`).
3. **Kernel lattice `Λ^⊥(gᵀ)` and `Λ^⊥(G)` and the explicit short matrix `S_w` (`scalarBasis`,
   `gadgetBasis`):**
   For `q = 2 ^ w`, the lower-bidiagonal integer matrix `S_w ∈ ℤ^{w × w}` with `2` on the diagonal
   and `-1` on the subdiagonal (Section 4.1, Proposition 4.2) has columns in `Λ^⊥(gᵀ)`
   (`gadgetVector_vecMul_scalarBasis`), determinant `2 ^ w` (`det_scalarBasis`), entry magnitudes
   at most `2` (`natAbs_scalarBasis_le_two`), and squared Euclidean column norm at most `5`
   (`sum_sq_scalarBasis_col_le_five`). Its block-diagonal sum `S = I_ι ⊗ S_w` (`gadgetBasis`)
   satisfies `G S ≡ 0 (mod 2 ^ w)` (`gadgetMatrix_mul_gadgetBasis`) with the same column norm
   bounds. The paper deduces that `S_w` is a basis of `Λ^⊥(gᵀ)` from these two facts and the
   index `|ℤ^w / Λ^⊥(gᵀ)| = q`; that lattice-index argument, and the Gram–Schmidt identity
   `S̃_w = 2 I`, are not formalized, so the generating-set property is not proved here.
4. **Deterministic `g_G`-inversion (`invertScalar`, `invertGadget`):**
   The iterative nearest-plane algorithm of Section 4.1 recovers `s` from
   `g_G(s, e) = sᵀ G + eᵀ mod 2 ^ w` whenever every integer error coordinate satisfies
   `4 * (e p).natAbs < 2 ^ w` (`invertScalar_correct`, `invertGadget_gadgetLWE`). The paper
   allows every `e_i ∈ [-q/4, q/4)`; the hypothesis here excludes only the endpoint `-q/4`.

General (non-power-of-two) moduli from Section 4.2 and randomized discrete-Gaussian preimage
sampling over cosets of `Λ^⊥(G)` are not formalized here.

## Main definitions

* `Cslib.Crypto.LWE.Trapdoor.gadgetVector`, `Cslib.Crypto.LWE.Trapdoor.gadgetMatrix`: the
  primitive gadget vector `g` and matrix `G = I_ι ⊗ gᵀ` over `ZMod (2 ^ w)`.
* `Cslib.Crypto.LWE.Trapdoor.scalarDecomp`, `Cslib.Crypto.LWE.Trapdoor.gadgetDecomp`,
  `Cslib.Crypto.LWE.Trapdoor.gadgetDecompMatrix`: binary `{0, 1}`-valued integer decompositions.
* `Cslib.Crypto.LWE.Trapdoor.InScalarKernel`, `Cslib.Crypto.LWE.Trapdoor.InKernelLattice`:
  membership in `Λ^⊥(gᵀ)` and `Λ^⊥(A)`.
* `Cslib.Crypto.LWE.Trapdoor.scalarBasis`, `Cslib.Crypto.LWE.Trapdoor.gadgetBasis`: the explicit
  short kernel matrix `S_w` in `Λ^⊥(gᵀ)` and block matrix `S = I_ι ⊗ S_w` in `Λ^⊥(G)` (shown to be
  bases in Section 4.1; kernel membership, `det S_w = 2 ^ w`, and norm bounds are proved here,
  not lattice generation).
* `Cslib.Crypto.LWE.Trapdoor.gadgetLWE`, `Cslib.Crypto.LWE.Trapdoor.invertScalarAux`,
  `Cslib.Crypto.LWE.Trapdoor.invertScalar`, `Cslib.Crypto.LWE.Trapdoor.invertGadget`: the
  gadget LWE map `g_G(s, e) = sᵀ G + eᵀ` and its iterative Section 4.1 inversion algorithm.

## Main results

* `Cslib.Crypto.LWE.Trapdoor.gadgetMatrix_mulVec`,
  `Cslib.Crypto.LWE.Trapdoor.vecMul_gadgetMatrix`: bridges to `GSW.bitCompose` and
  `GSW.powersOfTwo`.
* `Cslib.Crypto.LWE.Trapdoor.gadgetVector_dotProduct_scalarDecomp`,
  `Cslib.Crypto.LWE.Trapdoor.gadgetMatrix_mulVec_gadgetDecomp`,
  `Cslib.Crypto.LWE.Trapdoor.gadgetMatrix_mul_gadgetDecompMatrix`,
  `Cslib.Crypto.LWE.Trapdoor.gadgetMatrix_surjective`: deterministic right-inversion of `f_G`
  and primitivity of `G`.
* `Cslib.Crypto.LWE.Trapdoor.gadgetVector_vecMul_scalarBasis`,
  `Cslib.Crypto.LWE.Trapdoor.det_scalarBasis`,
  `Cslib.Crypto.LWE.Trapdoor.sum_sq_scalarBasis_col_le_five`,
  `Cslib.Crypto.LWE.Trapdoor.gadgetMatrix_mul_gadgetBasis`,
  `Cslib.Crypto.LWE.Trapdoor.sum_sq_gadgetBasis_col_le_five`: `det S_w = 2 ^ w` for `S_w`, and
  kernel membership and Euclidean column length `≤ √5` for both `S_w` and `S` (Theorem 4.1 /
  Proposition 4.2; the basis property itself is not proved).
* `Cslib.Crypto.LWE.Trapdoor.invertScalar_correct`,
  `Cslib.Crypto.LWE.Trapdoor.invertGadget_gadgetLWE`: exact inversion of `g_G(s, e)` under
  `4 * (e p).natAbs < 2 ^ w` (Theorem 4.1 / Section 4.1).

## References

* [D. Micciancio and C. Peikert, *Trapdoors for Lattices: Simpler, Tighter, Faster, Smaller*,
  Section 4][MicciancioPeikert2012]; numbering follows IACR ePrint 2011/501.
-/

@[expose] public section

namespace Cslib.Crypto.LWE.Trapdoor

open Cslib.Crypto.Homomorphic
open scoped BigOperators Matrix

variable {ι ρ κ : Type*}

/-! ### Primitive gadget vector and matrix -/

/-- The geometric gadget vector `g = (1, 2, 4, …, 2 ^ (w - 1))` over `ZMod (2 ^ w)`
([MicciancioPeikert2012], Equation 4.1). -/
def gadgetVector (w : ℕ) : Fin w → ZMod (2 ^ w) :=
  fun j => 2 ^ j.val

@[simp] theorem gadgetVector_apply (w : ℕ) (j : Fin w) :
    gadgetVector w j = 2 ^ j.val := rfl

/-- The primitive gadget matrix `G = I_ι ⊗ gᵀ` over `ZMod (2 ^ w)`
([MicciancioPeikert2012], Section 4): row `i` has `gadgetVector w` in block `i` and zeros
elsewhere. -/
def gadgetMatrix (w : ℕ) [DecidableEq ι] : Matrix ι (ι × Fin w) (ZMod (2 ^ w)) :=
  fun i p => if i = p.1 then gadgetVector w p.2 else 0

@[simp] theorem gadgetMatrix_apply (w : ℕ) [DecidableEq ι] (i : ι) (p : ι × Fin w) :
    gadgetMatrix w i p = if i = p.1 then 2 ^ p.2.val else 0 := rfl

theorem gadgetMatrix_apply_same (w : ℕ) [DecidableEq ι] (i : ι) (j : Fin w) :
    gadgetMatrix w i (i, j) = 2 ^ j.val := by
  simp

theorem gadgetMatrix_apply_ne (w : ℕ) [DecidableEq ι] {i i' : ι} (h : i ≠ i') (j : Fin w) :
    gadgetMatrix w i (i', j) = 0 := by
  simp [h]

/-- Right-multiplying `gadgetMatrix w` by a vector is `GSW.bitCompose w`. -/
theorem gadgetMatrix_mulVec [Fintype ι] [DecidableEq ι] (w : ℕ)
    (v : ι × Fin w → ZMod (2 ^ w)) :
    gadgetMatrix w *ᵥ v = GSW.bitCompose w v := by
  funext i
  simp only [Matrix.mulVec, dotProduct, gadgetMatrix_apply, GSW.bitCompose,
    Fintype.sum_prod_type, ite_mul, zero_mul, mul_comm]
  rw [Finset.sum_eq_single i
    (fun r _ hri => Finset.sum_eq_zero fun _ _ => by simp [hri.symm])
    (fun h => (h (Finset.mem_univ i)).elim)]
  simp

/-- Left-multiplying `gadgetMatrix w` by a row vector `s` is `GSW.powersOfTwo w s`. -/
theorem vecMul_gadgetMatrix [Fintype ι] [DecidableEq ι] (w : ℕ)
    (s : ι → ZMod (2 ^ w)) :
    s ᵥ* gadgetMatrix w = GSW.powersOfTwo w s := by
  funext ⟨i, j⟩
  simp only [Matrix.vecMul, dotProduct, gadgetMatrix_apply, GSW.powersOfTwo,
    mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, mul_comm]

/-- Multiplying a matrix on the right by `(gadgetMatrix w)ᵀ` recomposes its rows via
`GSW.recomposeMatrix w`. -/
theorem mul_gadgetMatrix_transpose [Fintype ι] [DecidableEq ι] (w : ℕ)
    (C : Matrix ρ (ι × Fin w) (ZMod (2 ^ w))) :
    C * (gadgetMatrix w)ᵀ = GSW.recomposeMatrix w C := by
  ext r i
  have h := congrFun (gadgetMatrix_mulVec w (C r)) i
  simpa only [Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.transpose_apply,
    mul_comm, GSW.recomposeMatrix] using h

/-! ### Deterministic gadget decomposition (`G⁻¹` for `f_G`) -/

/-- Binary decomposition of a single residue `u ∈ ZMod (2 ^ w)` into `{0, 1}` integer digits,
least significant bit first ([MicciancioPeikert2012], Section 4). -/
def scalarDecomp (w : ℕ) (u : ZMod (2 ^ w)) : Fin w → ℤ :=
  fun j => (u.val.testBit j.val).toNat

/-- Binary decomposition of a syndrome vector `u : ι → ZMod (2 ^ w)` into `{0, 1}` integer
digits, reusing `GSW.bitDecomp` ([MicciancioPeikert2012], Section 4). -/
def gadgetDecomp (w : ℕ) (u : ι → ZMod (2 ^ w)) : ι × Fin w → ℤ :=
  fun p => (GSW.bitDecomp w u p).toNat

/-- Binary decomposition of a matrix `U : Matrix ι κ (ZMod (2 ^ w))` column-by-column into a
`{0, 1}` integer matrix `W` satisfying `G * W ≡ U (mod 2 ^ w)`. -/
def gadgetDecompMatrix (w : ℕ) (U : Matrix ι κ (ZMod (2 ^ w))) : Matrix (ι × Fin w) κ ℤ :=
  fun p k => gadgetDecomp w (fun i => U i k) p

theorem gadgetDecomp_eq_scalarDecomp (w : ℕ) (u : ι → ZMod (2 ^ w)) (p : ι × Fin w) :
    gadgetDecomp w u p = scalarDecomp w (u p.1) p.2 := rfl

theorem scalarDecomp_nonneg (w : ℕ) (u : ZMod (2 ^ w)) (j : Fin w) :
    0 ≤ scalarDecomp w u j :=
  Int.natCast_nonneg _

theorem scalarDecomp_le_one (w : ℕ) (u : ZMod (2 ^ w)) (j : Fin w) :
    scalarDecomp w u j ≤ 1 :=
  Int.ofNat_le.mpr (Bool.toNat_le _)

theorem natAbs_scalarDecomp_le_one (w : ℕ) (u : ZMod (2 ^ w)) (j : Fin w) :
    (scalarDecomp w u j).natAbs ≤ 1 :=
  Bool.toNat_le _

theorem gadgetDecomp_nonneg (w : ℕ) (u : ι → ZMod (2 ^ w)) (p : ι × Fin w) :
    0 ≤ gadgetDecomp w u p :=
  Int.natCast_nonneg _

theorem gadgetDecomp_le_one (w : ℕ) (u : ι → ZMod (2 ^ w)) (p : ι × Fin w) :
    gadgetDecomp w u p ≤ 1 :=
  Int.ofNat_le.mpr (Bool.toNat_le _)

theorem natAbs_gadgetDecomp_le_one (w : ℕ) (u : ι → ZMod (2 ^ w)) (p : ι × Fin w) :
    (gadgetDecomp w u p).natAbs ≤ 1 :=
  Bool.toNat_le _

theorem natAbs_gadgetDecompMatrix_le_one (w : ℕ) (U : Matrix ι κ (ZMod (2 ^ w)))
    (p : ι × Fin w) (k : κ) :
    (gadgetDecompMatrix w U p k).natAbs ≤ 1 :=
  Bool.toNat_le _

/-- `gadgetDecomp w` is a deterministic right inverse of `f_G(x) = G x mod 2 ^ w`:
`G *ᵥ gadgetDecomp w u = u` ([MicciancioPeikert2012], Section 4). -/
@[simp] theorem gadgetMatrix_mulVec_gadgetDecomp [Fintype ι] [DecidableEq ι] (w : ℕ)
    (u : ι → ZMod (2 ^ w)) :
    gadgetMatrix w *ᵥ (Int.cast ∘ gadgetDecomp w u) = u := by
  rw [gadgetMatrix_mulVec]
  simp only [Function.comp_def, gadgetDecomp, Int.cast_natCast]
  exact GSW.bitCompose_bitDecomp w u

/-- `scalarDecomp w` is a deterministic right inverse of `x ↦ ⟨g, x⟩ mod 2 ^ w`. -/
@[simp] theorem gadgetVector_dotProduct_scalarDecomp (w : ℕ) (u : ZMod (2 ^ w)) :
    gadgetVector w ⬝ᵥ (Int.cast ∘ scalarDecomp w u) = u := by
  have h := congrFun (gadgetMatrix_mulVec_gadgetDecomp (ι := Unit) w (fun _ => u)) ()
  simpa only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fintype.sum_unique,
    gadgetMatrix_apply_same, gadgetVector_apply, Function.comp_apply,
    gadgetDecomp_eq_scalarDecomp] using h

/-- Matrix form of gadget right-inversion: `G * gadgetDecompMatrix w U = U` modulo `2 ^ w`. -/
@[simp] theorem gadgetMatrix_mul_gadgetDecompMatrix [Fintype ι] [DecidableEq ι] (w : ℕ)
    (U : Matrix ι κ (ZMod (2 ^ w))) :
    gadgetMatrix w * (gadgetDecompMatrix w U).map Int.cast = U := by
  ext i k
  exact congrFun (gadgetMatrix_mulVec_gadgetDecomp w (fun r => U r k)) i

/-- The gadget matrix `G` is primitive ([MicciancioPeikert2012], Section 4): its integer column
combinations span `(ZMod (2 ^ w)) ^ ι`. -/
theorem gadgetMatrix_surjective [Fintype ι] [DecidableEq ι] (w : ℕ) :
    Function.Surjective (fun x : ι × Fin w → ℤ => gadgetMatrix w *ᵥ (Int.cast ∘ x)) :=
  fun u => ⟨gadgetDecomp w u, gadgetMatrix_mulVec_gadgetDecomp w u⟩

/-! ### Kernel lattice `Λ^⊥(gᵀ)`, `Λ^⊥(G)` and the explicit short basis `S_w` -/

/-- Membership in the scalar gadget kernel lattice
`Λ^⊥(gᵀ) = { z ∈ ℤ ^ w : ⟨g, z⟩ ≡ 0 (mod 2 ^ w) }`
([MicciancioPeikert2012], Section 4). -/
def InScalarKernel (w : ℕ) (z : Fin w → ℤ) : Prop :=
  gadgetVector w ⬝ᵥ (Int.cast ∘ z) = 0

/-- Membership in the `q`-ary kernel lattice `Λ^⊥(A) = { z ∈ ℤ ^ κ : A z ≡ 0 (mod q) }`
([MicciancioPeikert2012], Section 2.2). The last conjunct of `Cslib.Crypto.SIS.IsSolution` is
this condition. -/
def InKernelLattice {q : ℕ} [Fintype κ] (A : Matrix ρ κ (ZMod q)) (z : κ → ℤ) : Prop :=
  A *ᵥ (Int.cast ∘ z) = 0

/-- The matrix `S_w ∈ ℤ ^ {w × w}` that [MicciancioPeikert2012], Section 4.1 and
Proposition 4.2, shows is a short basis of `Λ^⊥(gᵀ)` for `q = 2 ^ w`: `2` on the diagonal, `-1`
on the first subdiagonal, and `0` elsewhere. This module proves kernel membership and the
determinant and norm bounds, not the basis property. -/
def scalarBasis (w : ℕ) : Matrix (Fin w) (Fin w) ℤ :=
  fun i j => if i.val = j.val then 2 else if i.val = j.val + 1 then -1 else 0

@[simp] theorem scalarBasis_self (w : ℕ) (i : Fin w) :
    scalarBasis w i i = 2 := by
  simp [scalarBasis]

theorem scalarBasis_eq_zero_of_lt {w : ℕ} {i j : Fin w} (hij : i < j) :
    scalarBasis w i j = 0 := by
  have hlt : i.val < j.val := hij
  have hne1 : i.val ≠ j.val := by omega
  have hne2 : i.val ≠ j.val + 1 := by omega
  simp [scalarBasis, hne1, hne2]

theorem scalarBasis_isLowerTriangular (w : ℕ) :
    (scalarBasis w).IsLowerTriangular :=
  fun _ _ hij => scalarBasis_eq_zero_of_lt hij

/-- `det(S_w) = 2 ^ w` ([MicciancioPeikert2012], Section 4.1). -/
@[simp] theorem det_scalarBasis (w : ℕ) :
    (scalarBasis w).det = 2 ^ w := by
  rw [Matrix.det_of_isLowerTriangular (scalarBasis w) (scalarBasis_isLowerTriangular w)]
  simp

/-- Every entry of `S_w` has magnitude at most `2`. -/
theorem natAbs_scalarBasis_le_two (w : ℕ) (i j : Fin w) :
    (scalarBasis w i j).natAbs ≤ 2 := by
  simp only [scalarBasis]
  split_ifs <;> decide

private theorem sum_scalarBasis_col {M : Type*} [AddCommMonoid M] (w : ℕ) (j : Fin w)
    (f : Fin w → ℤ → M) (hf0 : ∀ i, f i 0 = 0) :
    (∑ i : Fin w, f i (scalarBasis w i j)) =
      if hj : j.val + 1 < w then f j 2 + f ⟨j.val + 1, hj⟩ (-1) else f j 2 := by
  simp only [scalarBasis]
  have hdiag : ∀ i : Fin w, i.val = j.val ↔ i = j := fun i => Fin.ext_iff.symm
  simp only [hdiag]
  split_ifs with hj
  · let j' : Fin w := ⟨j.val + 1, hj⟩
    have hsub : ∀ i : Fin w, i.val = j.val + 1 ↔ i = j' :=
      fun i => (Fin.ext_iff (a := i) (b := j')).symm
    have hne : j' ≠ j := by
      intro h
      have hval : j.val + 1 = j.val := congrArg Fin.val h
      omega
    simp only [hsub]
    rw [Finset.sum_eq_add j j' hne.symm
      (fun i _ ⟨hij, hij'⟩ => by simp [hij, hij', hf0])
      (fun h => (h (Finset.mem_univ j)).elim)
      (fun h => (h (Finset.mem_univ j')).elim)]
    simp [hne, j']
  · have hno : ∀ i : Fin w, ¬(i.val = j.val + 1) := fun i => by omega
    simp only [hno, ↓reduceIte]
    rw [Finset.sum_eq_single j
      (fun i _ hij => by simp [hij, hf0])
      (fun h => (h (Finset.mem_univ j)).elim)]
    simp

/-- Every column of `S_w` belongs to `Λ^⊥(gᵀ)` ([MicciancioPeikert2012], Section 4.1). -/
theorem scalarBasis_col_inScalarKernel (w : ℕ) (j : Fin w) :
    InScalarKernel w (fun i => scalarBasis w i j) := by
  unfold InScalarKernel
  simp only [dotProduct, Function.comp_apply]
  rw [sum_scalarBasis_col w j (fun i (z : ℤ) => gadgetVector w i * (z : ZMod (2 ^ w)))
    (fun _ => by simp)]
  split_ifs with hj
  · simp only [gadgetVector_apply, Int.cast_ofNat, Int.cast_neg, Int.cast_one, pow_succ]
    ring
  · simp only [gadgetVector_apply, Int.cast_ofNat]
    have hjw : j.val + 1 = w := by omega
    calc
      (2 : ZMod (2 ^ w)) ^ j.val * 2 = 2 ^ (j.val + 1) := (pow_succ 2 j.val).symm
      _ = ((2 ^ w : ℕ) : ZMod (2 ^ w)) := by rw [hjw, Nat.cast_pow, Nat.cast_ofNat]
      _ = 0 := CharP.cast_eq_zero (ZMod (2 ^ w)) (2 ^ w)

/-- Matrix form of `gᵀ S_w ≡ 0 (mod 2 ^ w)` ([MicciancioPeikert2012], Section 4.1). -/
@[simp] theorem gadgetVector_vecMul_scalarBasis (w : ℕ) :
    gadgetVector w ᵥ* (scalarBasis w).map Int.cast = 0 := by
  funext j
  exact scalarBasis_col_inScalarKernel w j

/-- Every column of `S_w` has squared Euclidean length at most `5` (`‖S_w‖ ≤ √5`,
[MicciancioPeikert2012], Proposition 4.2). -/
theorem sum_sq_scalarBasis_col_le_five (w : ℕ) (j : Fin w) :
    (∑ i : Fin w, (scalarBasis w i j) ^ 2) ≤ 5 := by
  rw [sum_scalarBasis_col w j (fun _ z => z ^ 2) (fun _ => by simp)]
  split_ifs <;> decide

/-- The block-diagonal matrix `S = I_ι ⊗ S_w`, the short basis of `Λ^⊥(G)` for `q = 2 ^ w` in
[MicciancioPeikert2012], Section 4 and Theorem 4.1 (only kernel membership and norm bounds are
proved here). -/
def gadgetBasis (w : ℕ) [DecidableEq ι] : Matrix (ι × Fin w) (ι × Fin w) ℤ :=
  fun p q => if p.1 = q.1 then scalarBasis w p.2 q.2 else 0

@[simp] theorem gadgetBasis_apply (w : ℕ) [DecidableEq ι] (p q : ι × Fin w) :
    gadgetBasis w p q = if p.1 = q.1 then scalarBasis w p.2 q.2 else 0 := rfl

/-- Every entry of `S = I_ι ⊗ S_w` has magnitude at most `2`. -/
theorem natAbs_gadgetBasis_le_two [DecidableEq ι] (w : ℕ) (p q : ι × Fin w) :
    (gadgetBasis w p q).natAbs ≤ 2 := by
  simp only [gadgetBasis]
  split_ifs
  · exact natAbs_scalarBasis_le_two w p.2 q.2
  · simp

/-- `G * S ≡ 0 (mod 2 ^ w)` ([MicciancioPeikert2012], Section 4, Theorem 4.1). -/
@[simp] theorem gadgetMatrix_mul_gadgetBasis [Fintype ι] [DecidableEq ι] (w : ℕ) :
    gadgetMatrix (ι := ι) w * (gadgetBasis (ι := ι) w).map (Int.cast : ℤ → ZMod (2 ^ w)) = 0 := by
  ext i ⟨i', j⟩
  simp only [Matrix.mul_apply, gadgetMatrix_apply, Matrix.map_apply, gadgetBasis_apply,
    Fintype.sum_prod_type, Int.cast_ite, Int.cast_zero, Matrix.zero_apply]
  by_cases hii' : i = i'
  · subst hii'
    rw [Finset.sum_eq_single i
      (fun r _ hri => Finset.sum_eq_zero fun _ _ => by simp [hri.symm])
      (fun h => (h (Finset.mem_univ i)).elim)]
    simp only [↓reduceIte]
    exact scalarBasis_col_inScalarKernel w j
  · refine Finset.sum_eq_zero fun r _ => Finset.sum_eq_zero fun k _ => ?_
    by_cases hir : i = r
    · subst hir
      simp [hii']
    · simp [hir]

/-- Every column of `gadgetBasis w` belongs to `Λ^⊥(G)`. -/
theorem gadgetBasis_col_inKernelLattice [Fintype ι] [DecidableEq ι] (w : ℕ) (q : ι × Fin w) :
    InKernelLattice (gadgetMatrix (ι := ι) w) (fun p => gadgetBasis w p q) := by
  funext i
  exact congrFun (congrFun (gadgetMatrix_mul_gadgetBasis (ι := ι) w) i) q

/-- Every column of `S = I_ι ⊗ S_w` has squared Euclidean length at most `5` (`‖S‖ ≤ √5`,
[MicciancioPeikert2012], Theorem 4.1 and Proposition 4.2). -/
theorem sum_sq_gadgetBasis_col_le_five [Fintype ι] [DecidableEq ι] (w : ℕ) (q : ι × Fin w) :
    (∑ p : ι × Fin w, (gadgetBasis w p q) ^ 2) ≤ 5 := by
  rcases q with ⟨i, j⟩
  simp only [Fintype.sum_prod_type, gadgetBasis_apply]
  rw [Finset.sum_eq_single i
    (fun r _ hri => by simp [hri])
    (fun h => (h (Finset.mem_univ i)).elim)]
  simp only [↓reduceIte]
  exact sum_sq_scalarBasis_col_le_five w j

/-! ### Deterministic `g_G`-inversion (`Theorem 4.1`, `Section 4.1`) -/

/-- The gadget LWE evaluation `g_G(s, e) = sᵀ G + eᵀ mod 2 ^ w`
([MicciancioPeikert2012], Theorem 4.1). -/
def gadgetLWE [Fintype ι] [DecidableEq ι] (w : ℕ)
    (s : ι → ZMod (2 ^ w)) (e : ι × Fin w → ℤ) : ι × Fin w → ZMod (2 ^ w) :=
  s ᵥ* gadgetMatrix w + (Int.cast ∘ e)

@[simp] theorem gadgetLWE_apply [Fintype ι] [DecidableEq ι] (w : ℕ)
    (s : ι → ZMod (2 ^ w)) (e : ι × Fin w → ℤ) (p : ι × Fin w) :
    gadgetLWE w s e p = 2 ^ p.2.val * s p.1 + (e p : ZMod (2 ^ w)) := by
  simp [gadgetLWE, vecMul_gadgetMatrix, GSW.powersOfTwo]

/-- Iterative recovery of the low `l` binary digits of `s` from `b = s · gᵀ + eᵀ mod 2 ^ w`
([MicciancioPeikert2012], Section 4.1). At step `l < w`, coordinate `w - 1 - l` determines bit `l`
via `LWE.decode w`. -/
def invertScalarAux (w : ℕ) (b : Fin w → ZMod (2 ^ w)) : ℕ → ℕ
  | 0 => 0
  | l + 1 =>
    let acc := invertScalarAux w b l
    if h : l < w then
      let idx : Fin w := ⟨w - 1 - l, by omega⟩
      let bit := LWE.decode w (b idx - 2 ^ idx.val * (acc : ZMod (2 ^ w)))
      acc + bit.toNat * 2 ^ l
    else acc

/-- Recover `s ∈ ZMod (2 ^ w)` from `b = s · gᵀ + eᵀ mod 2 ^ w`
([MicciancioPeikert2012], Section 4.1). -/
def invertScalar (w : ℕ) (b : Fin w → ZMod (2 ^ w)) : ZMod (2 ^ w) :=
  (invertScalarAux w b w : ZMod (2 ^ w))

/-- Recover the secret vector `s : ι → ZMod (2 ^ w)` from `b = sᵀ G + eᵀ mod 2 ^ w` by applying
`invertScalar w` independently to each `w`-coordinate block
([MicciancioPeikert2012], Section 4). -/
def invertGadget (w : ℕ) (b : ι × Fin w → ZMod (2 ^ w)) : ι → ZMod (2 ^ w) :=
  fun i => invertScalar w (fun j => b (i, j))

private theorem mod_two_pow_succ (n l : ℕ) :
    n % 2 ^ l + (n.testBit l).toNat * 2 ^ l = n % 2 ^ (l + 1) := by
  rw [pow_succ, Nat.mod_mul, ← Nat.toNat_testBit, mul_comm]

private theorem nat_decomp_step (n l : ℕ) :
    n = n % 2 ^ l + (n.testBit l).toNat * 2 ^ l + 2 ^ (l + 1) * (n / 2 ^ (l + 1)) := by
  rw [mod_two_pow_succ]
  exact (Nat.mod_add_div n (2 ^ (l + 1))).symm

private theorem shifted_sub_mod_eq (w l : ℕ) (hl : l < w) (s : ZMod (2 ^ w)) :
    (2 : ZMod (2 ^ w)) ^ (w - 1 - l) * s -
        (2 : ZMod (2 ^ w)) ^ (w - 1 - l) * ((s.val % 2 ^ l : ℕ) : ZMod (2 ^ w)) =
      ((s.val.testBit l).toNat : ZMod (2 ^ w)) * 2 ^ (w - 1) := by
  have hexp1 : 2 ^ (w - 1 - l) * 2 ^ l = 2 ^ (w - 1) := by
    rw [← pow_add, show w - 1 - l + l = w - 1 by omega]
  have hexp2 : 2 ^ (w - 1 - l) * 2 ^ (l + 1) = 2 ^ w := by
    rw [← pow_add, show w - 1 - l + (l + 1) = w by omega]
  have hnat :
      2 ^ (w - 1 - l) * s.val =
        2 ^ (w - 1 - l) * (s.val % 2 ^ l) + (s.val.testBit l).toNat * 2 ^ (w - 1) +
          2 ^ w * (s.val / 2 ^ (l + 1)) := by
    calc
      2 ^ (w - 1 - l) * s.val =
          2 ^ (w - 1 - l) *
            (s.val % 2 ^ l + (s.val.testBit l).toNat * 2 ^ l +
              2 ^ (l + 1) * (s.val / 2 ^ (l + 1))) :=
        congrArg (2 ^ (w - 1 - l) * ·) (nat_decomp_step s.val l)
      _ = 2 ^ (w - 1 - l) * (s.val % 2 ^ l) +
            (s.val.testBit l).toNat * (2 ^ (w - 1 - l) * 2 ^ l) +
            (2 ^ (w - 1 - l) * 2 ^ (l + 1)) * (s.val / 2 ^ (l + 1)) := by ring
      _ = 2 ^ (w - 1 - l) * (s.val % 2 ^ l) + (s.val.testBit l).toNat * 2 ^ (w - 1) +
            2 ^ w * (s.val / 2 ^ (l + 1)) := by rw [hexp1, hexp2]
  have hcast := congrArg (fun k : ℕ => (k : ZMod (2 ^ w))) hnat
  push_cast at hcast
  have hzero : ((2 : ZMod (2 ^ w)) ^ w) = 0 := by
    exact_mod_cast CharP.cast_eq_zero (ZMod (2 ^ w)) (2 ^ w)
  rw [ZMod.natCast_zmod_val, hzero, zero_mul, add_zero] at hcast
  rw [hcast]
  ring

private theorem invertScalarAux_eq_mod (w : ℕ) (s : ZMod (2 ^ w)) (e : Fin w → ℤ)
    (he : ∀ j : Fin w, 4 * (e j).natAbs < 2 ^ w) (l : ℕ) (hl : l ≤ w) :
    invertScalarAux w (fun j => 2 ^ j.val * s + (e j : ZMod (2 ^ w))) l = s.val % 2 ^ l := by
  induction l with
  | zero =>
    simp [invertScalarAux, Nat.mod_one]
  | succ l ih =>
    have hlw : l < w := Nat.lt_of_succ_le hl
    have hw : 0 < w := Nat.zero_lt_of_lt hlw
    simp only [invertScalarAux, hlw, ↓reduceDIte, ih (Nat.le_of_lt hlw)]
    let idx : Fin w := ⟨w - 1 - l, by omega⟩
    have hres :
        (2 : ZMod (2 ^ w)) ^ idx.val * s + (e idx : ZMod (2 ^ w)) -
            2 ^ idx.val * ((s.val % 2 ^ l : ℕ) : ZMod (2 ^ w)) =
          (((s.val.testBit l).toNat : ℤ) * 2 ^ (w - 1) + e idx : ℤ) := by
      have hshift := shifted_sub_mod_eq w l hlw s
      push_cast
      change (2 : ZMod (2 ^ w)) ^ (w - 1 - l) * s + (e idx : ZMod (2 ^ w)) -
          2 ^ (w - 1 - l) * ((s.val % 2 ^ l : ℕ) : ZMod (2 ^ w)) =
        ((s.val.testBit l).toNat : ZMod (2 ^ w)) * 2 ^ (w - 1) + (e idx : ZMod (2 ^ w))
      rw [← hshift]
      ring
    have hdec :
        LWE.decode w
            ((2 : ZMod (2 ^ w)) ^ idx.val * s + (e idx : ZMod (2 ^ w)) -
              2 ^ idx.val * ((s.val % 2 ^ l : ℕ) : ZMod (2 ^ w))) =
          s.val.testBit l := by
      rw [hres]
      exact LWE.decode_eq_of_error hw (s.val.testBit l) (e idx) (he idx)
    change s.val % 2 ^ l +
        (LWE.decode w
          ((2 : ZMod (2 ^ w)) ^ idx.val * s + (e idx : ZMod (2 ^ w)) -
            2 ^ idx.val * ((s.val % 2 ^ l : ℕ) : ZMod (2 ^ w)))).toNat * 2 ^ l =
      s.val % 2 ^ (l + 1)
    rw [hdec, mod_two_pow_succ]

/-- Iterative scalar gadget inversion recovers `s` whenever `4 * (e j).natAbs < 2 ^ w` for every
coordinate `j` ([MicciancioPeikert2012], Section 4.1, "Inversion"; the paper's condition
`e_j ∈ [-q/4, q/4)` also admits `e_j = -q/4`). -/
@[simp] theorem invertScalar_correct (w : ℕ) (s : ZMod (2 ^ w)) (e : Fin w → ℤ)
    (he : ∀ j : Fin w, 4 * (e j).natAbs < 2 ^ w) :
    invertScalar w (fun j => 2 ^ j.val * s + (e j : ZMod (2 ^ w))) = s := by
  rw [invertScalar, invertScalarAux_eq_mod w s e he w le_rfl,
    Nat.mod_eq_of_lt (ZMod.val_lt s), ZMod.natCast_zmod_val]

/-- Blockwise gadget inversion recovers `s` from `g_G(s, e) = sᵀ G + eᵀ mod 2 ^ w` whenever
`4 * (e p).natAbs < 2 ^ w` for every coordinate `p : ι × Fin w`
([MicciancioPeikert2012], Theorem 4.1 and Section 4.1). -/
@[simp] theorem invertGadget_gadgetLWE [Fintype ι] [DecidableEq ι] (w : ℕ)
    (s : ι → ZMod (2 ^ w)) (e : ι × Fin w → ℤ)
    (he : ∀ p : ι × Fin w, 4 * (e p).natAbs < 2 ^ w) :
    invertGadget w (gadgetLWE w s e) = s := by
  funext i
  simp only [invertGadget, gadgetLWE_apply]
  exact invertScalar_correct w (s i) (fun j => e (i, j)) (fun j => he (i, j))

end Cslib.Crypto.LWE.Trapdoor
