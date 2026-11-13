/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.LWE.KeyGen
public import CslibFrontier.Crypto.Computational.LWE.Trapdoor.Gadget
public import CslibFrontier.Crypto.Computational.SIS.Basic
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.Data.ZMod.ValMinAbs
import CslibFrontier.Probability.PMF.Map
import CslibFrontier.Probability.PMF.Uniform

/-!
# Micciancio–Peikert gadget-based lattice trapdoors (`GenTrap`, syndrome lifting, LWE inversion)

This module formalizes the gadget-based trapdoor construction of
[Micciancio and Peikert, Section 5][MicciancioPeikert2012] over `ZMod (2 ^ w)`, building on the
primitive gadget matrix `G = gadgetMatrix w` and short kernel matrix `S = gadgetBasis w` from
`CslibFrontier.Crypto.Computational.LWE.Trapdoor.Gadget`:

1. **Tagged parity-check matrices and `H`-tag trapdoors (Definition 5.2, Algorithm 1):**
   Given `Abar : Matrix ι μ (ZMod (2 ^ w))`, a short integer matrix
   `R : Matrix μ (ι × Fin w) ℤ`, and a tag `H : Matrix ι ι (ZMod (2 ^ w))`,
   `taggedMatrix w Abar R H = [Abar | H * G - Abar * R]` (`Matrix.fromCols`) and
   `trapdoorTransform R = [R; I]` (`Matrix.fromRows`) satisfy the unrestricted tag equation
   `A * [R; I] = H * G` (`taggedMatrix_mul_trapdoorTransform`). When `H` is invertible
   (`IsUnit H`), `R` is an `H`-tag `G`-trapdoor for `A` in the sense of Definition 5.2
   (`IsHTagTrapdoor`, `isHTagTrapdoor_taggedMatrix`, `isHTagTrapdoor_untaggedMatrix`).
2. **Syndrome lifting (`f_A⁻¹`) and lifted kernel vectors in `Λ^⊥(A)` (Section 5.1):**
   Applying `[R; I]` lifts any gadget preimage `z` of `H⁻¹ u` to a short preimage `x = [R z; z]`
   satisfying `A x = u` (`taggedMatrix_mulVec_invertSyndrome`), so any matrix admitting an
   `H`-tag `G`-trapdoor is primitive (`IsHTagTrapdoor.surjective`, `taggedMatrix_surjective`;
   the remark after Definition 5.2). The `w` columns of
   `[R; I] * S = [R S; S]` lie in `Λ^⊥(A)` (`taggedMatrix_mul_extendedGadgetBasis`,
   `extendedGadgetBasis_col_inKernelLattice`), with entrywise bounds
   (`natAbs_extendedGadgetBasis_inl_le`, `natAbs_extendedGadgetBasis_inr_le`). These are the
   right-hand `w` columns of the basis `S_A` of Lemma 5.3; the left-hand block (built from a
   solution `W` of `G W = -H⁻¹ A [I | 0]ᵀ`), the claim that `S_A` generates `Λ^⊥(A)`, and the
   Gram–Schmidt bound of Lemma 5.3 are not formalized.
3. **Deterministic trapdoor LWE inversion (`g_A⁻¹`, Section 5.3, Algorithm 2 / Theorem 5.4):**
   Given `bᵀ = sᵀ A + eᵀ mod 2 ^ w`, right-multiplying by `[R; I]` yields
   `bᵀ [R; I] = (sᵀ H) G + (e_1ᵀ R + e_2ᵀ)` (`trapdoorLWE_vecMul_trapdoorTransform`). Applying
   `invertGadget w` followed by `H⁻¹` recovers `s` whenever every coordinate of the projected
   error `e_1ᵀ R + e_2ᵀ` satisfies `4 * |projectedError R e p| < 2 ^ w`
   (`invertLWESecret_trapdoorLWE`), and centered lifting (`ZMod.valMinAbs`) recovers the full
   pair `(s, e)` when in addition every original error coordinate satisfies
   `2 * |e k| < 2 ^ w` (`invertLWE_trapdoorLWE`), both of which follow from the combined
   entrywise norm bound `4 * (1 + |μ| * B_R) * B_e < 2 ^ w`
   (`invertLWE_trapdoorLWE_of_norm_bound`). This is the deterministic part of Theorem 5.4 with
   the oracle `O` instantiated by `invertGadget` and with coordinatewise (infinity-norm)
   hypotheses in place of the paper's Euclidean bound `‖e‖ < q / (2 ‖B‖ s)`; the second claim of
   Theorem 5.4 (success with overwhelming probability for Gaussian errors) is not formalized.
4. **Probabilistic trapdoor generation `GenTrap` and an idealized hybrid
   (Section 5.2, Algorithm 1):**
   `genTrap` samples `Abar` uniformly via `LWE.sampleMatrix` and `R` with centered-binomial
   entries in `[-η, η]` (`sampleTrapdoorMatrix`; the paper allows any distribution `D`),
   returning `(taggedMatrix w Abar R H, R)` (`mem_support_genTrap`). In the idealized hybrid
   `genTrapIdeal`, where `Abar * R` is replaced by an independent uniform block, the public matrix
   is exactly uniform for every tag `H` (`eval_genTrapIdeal_eq_uniform`,
   `eval_genTrapIdeal_eq_of_tags`).

Not formalized here: the step from `genTrap` to `genTrapIdeal`, that is, the statistical
instantiation (regularity of `[Abar | Abar R]`) and the computational instantiation (decision-LWE)
of Section 5.2, so neither the statistical closeness of `A` to uniform claimed in Theorem 5.1 nor
its pseudorandomness is proved; the trapdoor quality `s_1(R)`; discrete-Gaussian preimage sampling
(`SampleD`, Section 5.4); and trapdoor delegation (Section 5.5).

## Main definitions

* `Cslib.Crypto.LWE.Trapdoor.taggedRightBlock`, `Cslib.Crypto.LWE.Trapdoor.taggedMatrix`,
  `Cslib.Crypto.LWE.Trapdoor.untaggedMatrix`, `Cslib.Crypto.LWE.Trapdoor.trapdoorTransform`,
  `Cslib.Crypto.LWE.Trapdoor.IsHTagTrapdoor`: the tagged matrix `[Abar | H G - Abar R]`,
  transformation `[R; I]`, and `H`-tag trapdoor predicate.
* `Cslib.Crypto.LWE.Trapdoor.liftPreimage`, `Cslib.Crypto.LWE.Trapdoor.invertSyndrome`,
  `Cslib.Crypto.LWE.Trapdoor.extendedGadgetBasis`: preimage lifting, deterministic syndrome
  inversion `f_A⁻¹`, and the lifted kernel vectors `[R; I] * S`.
* `Cslib.Crypto.LWE.Trapdoor.trapdoorLWE`, `Cslib.Crypto.LWE.Trapdoor.projectedError`,
  `Cslib.Crypto.LWE.Trapdoor.invertLWESecret`, `Cslib.Crypto.LWE.Trapdoor.invertLWE`:
  trapdoor LWE evaluation and Algorithm 2 (`Invert`).
* `Cslib.Crypto.LWE.Trapdoor.sampleTrapdoorRow`, `Cslib.Crypto.LWE.Trapdoor.sampleTrapdoorMatrix`,
  `Cslib.Crypto.LWE.Trapdoor.genTrap`, `Cslib.Crypto.LWE.Trapdoor.genTrapIdeal`: probabilistic
  trapdoor generation (`GenTrap`, Algorithm 1) and its idealized uniform hybrid.

## Main results

* `Cslib.Crypto.LWE.Trapdoor.taggedMatrix_mul_trapdoorTransform`,
  `Cslib.Crypto.LWE.Trapdoor.isHTagTrapdoor_taggedMatrix`: the unrestricted tag identity
  `[Abar | H G - Abar R] * [R; I] = H G` and the `H`-tag `G`-trapdoor property for invertible `H`.
* `Cslib.Crypto.LWE.Trapdoor.taggedMatrix_mul_extendedGadgetBasis`,
  `Cslib.Crypto.LWE.Trapdoor.natAbs_extendedGadgetBasis_inl_le`,
  `Cslib.Crypto.LWE.Trapdoor.natAbs_extendedGadgetBasis_inr_le`: kernel membership and entry
  bounds for the lifted vectors `[R; I] * S` (the right-hand block of `S_A` in Lemma 5.3).
* `Cslib.Crypto.LWE.Trapdoor.taggedMatrix_mulVec_invertSyndrome`,
  `Cslib.Crypto.LWE.Trapdoor.IsHTagTrapdoor.surjective`,
  `Cslib.Crypto.LWE.Trapdoor.taggedMatrix_surjective`,
  `Cslib.Crypto.LWE.Trapdoor.natAbs_invertSyndrome_inl_le`: deterministic syndrome inversion
  and primitivity of matrices admitting an `H`-tag `G`-trapdoor.
* `Cslib.Crypto.LWE.Trapdoor.trapdoorLWE_vecMul_trapdoorTransform`,
  `Cslib.Crypto.LWE.Trapdoor.invertLWESecret_trapdoorLWE`,
  `Cslib.Crypto.LWE.Trapdoor.invertLWE_trapdoorLWE`,
  `Cslib.Crypto.LWE.Trapdoor.invertLWE_trapdoorLWE_of_norm_bound`: exact LWE inversion via a
  gadget trapdoor (Algorithm 2, deterministic part of Theorem 5.4).
* `Cslib.Crypto.LWE.Trapdoor.mem_support_genTrap`,
  `Cslib.Crypto.LWE.Trapdoor.eval_genTrapIdeal_eq_uniform`,
  `Cslib.Crypto.LWE.Trapdoor.eval_genTrapIdeal_eq_of_tags`: support guarantees for `genTrap` and
  exact uniformity / tag-independence of the idealized hybrid `genTrapIdeal`.

## References

* [D. Micciancio and C. Peikert, *Trapdoors for Lattices: Simpler, Tighter, Faster, Smaller*,
  Section 5][MicciancioPeikert2012]; numbering follows IACR ePrint 2011/501.
-/

@[expose] public section

namespace Cslib.Crypto.LWE.Trapdoor

open Cslib.ProbComp Cslib.Probability
open scoped BigOperators _root_.Matrix

variable {ι μ κ : Type*} {w : ℕ}

/-! ### Tagged parity-check matrices and `H`-tag trapdoors (Definition 5.2, Algorithm 1) -/

/-- The right block `A_1 = H * G - Abar * R` of a Micciancio–Peikert tagged parity-check matrix
([MicciancioPeikert2012], Section 5.2, Algorithm 1, step 2). -/
def taggedRightBlock (w : ℕ) [Fintype ι] [DecidableEq ι] [Fintype μ]
    (Abar : _root_.Matrix ι μ (ZMod (2 ^ w)))
    (R : _root_.Matrix μ (ι × Fin w) ℤ)
    (H : _root_.Matrix ι ι (ZMod (2 ^ w))) : _root_.Matrix ι (ι × Fin w) (ZMod (2 ^ w)) :=
  H * gadgetMatrix w - Abar * R.map Int.cast

/-- The Micciancio–Peikert tagged parity-check matrix `A = [Abar | H * G - Abar * R]`
([MicciancioPeikert2012], Section 5.2, Algorithm 1, step 2). -/
def taggedMatrix (w : ℕ) [Fintype ι] [DecidableEq ι] [Fintype μ]
    (Abar : _root_.Matrix ι μ (ZMod (2 ^ w)))
    (R : _root_.Matrix μ (ι × Fin w) ℤ)
    (H : _root_.Matrix ι ι (ZMod (2 ^ w))) : _root_.Matrix ι (μ ⊕ (ι × Fin w)) (ZMod (2 ^ w)) :=
  _root_.Matrix.fromCols Abar (taggedRightBlock w Abar R H)

/-- The untagged parity-check matrix `A = [Abar | G - Abar * R]` corresponding to `H = I`, the
default tag of [MicciancioPeikert2012], Algorithm 1. -/
def untaggedMatrix (w : ℕ) [Fintype ι] [DecidableEq ι] [Fintype μ]
    (Abar : _root_.Matrix ι μ (ZMod (2 ^ w)))
    (R : _root_.Matrix μ (ι × Fin w) ℤ) : _root_.Matrix ι (μ ⊕ (ι × Fin w)) (ZMod (2 ^ w)) :=
  taggedMatrix w Abar R 1

/-- The integer trapdoor transformation matrix `[R; I]` mapping gadget coordinates `ι × Fin w`
into full column coordinates `μ ⊕ (ι × Fin w)` ([MicciancioPeikert2012], Definition 5.2). -/
def trapdoorTransform [DecidableEq ι]
    (R : _root_.Matrix μ (ι × Fin w) ℤ) : _root_.Matrix (μ ⊕ (ι × Fin w)) (ι × Fin w) ℤ :=
  _root_.Matrix.fromRows R 1

/-- `R` is a `G`-trapdoor for `A` with tag `H` ([MicciancioPeikert2012], Definition 5.2):
`A * [R; I] = H * G` modulo `2 ^ w` and the tag `H` is invertible (`IsUnit H`). -/
def IsHTagTrapdoor (w : ℕ) [Fintype ι] [DecidableEq ι] [Fintype μ]
    (A : _root_.Matrix ι (μ ⊕ (ι × Fin w)) (ZMod (2 ^ w)))
    (R : _root_.Matrix μ (ι × Fin w) ℤ)
    (H : _root_.Matrix ι ι (ZMod (2 ^ w))) : Prop :=
  A * (trapdoorTransform R).map Int.cast = H * gadgetMatrix w ∧ IsUnit H

theorem trapdoorTransform_map_intCast (w : ℕ) [DecidableEq ι]
    (R : _root_.Matrix μ (ι × Fin w) ℤ) :
    (trapdoorTransform R).map (Int.cast : ℤ → ZMod (2 ^ w)) =
      _root_.Matrix.fromRows (R.map Int.cast) 1 := by
  rw [trapdoorTransform, _root_.Matrix.fromRows_map]
  congr 1
  ext p q
  by_cases hpq : p = q
  · subst hpq; simp
  · simp [_root_.Matrix.one_apply_ne hpq]

/-- Unrestricted tag equation: `[Abar | H * G - Abar * R] * [R; I] = H * G` modulo `2 ^ w` for any
`Abar`, `R`, and `H` ([MicciancioPeikert2012], Section 5.2, Algorithm 1). -/
@[simp] theorem taggedMatrix_mul_trapdoorTransform (w : ℕ)
    [Fintype ι] [DecidableEq ι] [Fintype μ]
    (Abar : _root_.Matrix ι μ (ZMod (2 ^ w)))
    (R : _root_.Matrix μ (ι × Fin w) ℤ)
    (H : _root_.Matrix ι ι (ZMod (2 ^ w))) :
    taggedMatrix w Abar R H * (trapdoorTransform R).map Int.cast = H * gadgetMatrix w := by
  rw [taggedMatrix, trapdoorTransform_map_intCast, _root_.Matrix.fromCols_mul_fromRows,
    _root_.Matrix.mul_one, taggedRightBlock, add_sub_cancel]

/-- When `H` is invertible (`IsUnit H`), `R` is an `H`-tag `G`-trapdoor for
`taggedMatrix w Abar R H` ([MicciancioPeikert2012], Definition 5.2). -/
theorem isHTagTrapdoor_taggedMatrix (w : ℕ) [Fintype ι] [DecidableEq ι] [Fintype μ]
    (Abar : _root_.Matrix ι μ (ZMod (2 ^ w)))
    (R : _root_.Matrix μ (ι × Fin w) ℤ)
    {H : _root_.Matrix ι ι (ZMod (2 ^ w))} (hH : IsUnit H) :
    IsHTagTrapdoor w (taggedMatrix w Abar R H) R H :=
  ⟨taggedMatrix_mul_trapdoorTransform w Abar R H, hH⟩

/-- `R` is an `I`-tag `G`-trapdoor for `untaggedMatrix w Abar R`
([MicciancioPeikert2012], Definition 5.2 and Algorithm 1). -/
theorem isHTagTrapdoor_untaggedMatrix (w : ℕ) [Fintype ι] [DecidableEq ι] [Fintype μ]
    (Abar : _root_.Matrix ι μ (ZMod (2 ^ w)))
    (R : _root_.Matrix μ (ι × Fin w) ℤ) :
    IsHTagTrapdoor w (untaggedMatrix w Abar R) R 1 :=
  isHTagTrapdoor_taggedMatrix w Abar R isUnit_one

/-- Tag-shift identity: subtracting `(H - H') * G` from the right block of an `H`-tagged matrix
yields the `H'`-tagged matrix for the same `(Abar, R)`. -/
theorem taggedRightBlock_sub_tag (w : ℕ) [Fintype ι] [DecidableEq ι] [Fintype μ]
    (Abar : _root_.Matrix ι μ (ZMod (2 ^ w)))
    (R : _root_.Matrix μ (ι × Fin w) ℤ)
    (H H' : _root_.Matrix ι ι (ZMod (2 ^ w))) :
    taggedRightBlock w Abar R H - (H - H') * gadgetMatrix w =
      taggedRightBlock w Abar R H' := by
  simp only [taggedRightBlock, _root_.Matrix.sub_mul]
  abel

/-- When the tag vanishes (`H = 0`, which is not an invertible tag), the trapdoor
transformation maps into the kernel of `A`: `taggedMatrix w Abar R 0 * [R; I] = 0`. -/
theorem taggedMatrix_zero_mul_trapdoorTransform (w : ℕ)
    [Fintype ι] [DecidableEq ι] [Fintype μ]
    (Abar : _root_.Matrix ι μ (ZMod (2 ^ w)))
    (R : _root_.Matrix μ (ι × Fin w) ℤ) :
    taggedMatrix w Abar R 0 * (trapdoorTransform R).map (Int.cast : ℤ → ZMod (2 ^ w)) = 0 := by
  rw [taggedMatrix_mul_trapdoorTransform, _root_.Matrix.zero_mul]

/-! ### Syndrome lifting (`f_A⁻¹`) and lifted kernel vectors in `Λ^⊥(A)` (Section 5.1) -/

/-- Every short integer solution in the sense of `Cslib.Crypto.SIS.IsSolution` lies in the
`q`-ary kernel lattice `Λ^⊥(A)`. -/
theorem inKernelLattice_of_isSolution {q : ℕ} {ρ : Type*} [Fintype κ]
    {A : _root_.Matrix ρ κ (ZMod q)} {β : ℕ} {z : κ → ℤ} (hz : SIS.IsSolution A β z) :
    InKernelLattice A z := by
  obtain ⟨-, -, hker⟩ := hz
  exact hker

/-- Lift an integer vector `z : ι × Fin w → ℤ` in gadget space to `x = [R z; z]` in full column
space `μ ⊕ (ι × Fin w)`. -/
def liftPreimage [Fintype ι] (R : _root_.Matrix μ (ι × Fin w) ℤ) (z : ι × Fin w → ℤ) :
    μ ⊕ (ι × Fin w) → ℤ :=
  Sum.elim (R *ᵥ z) z

@[simp] theorem liftPreimage_inl [Fintype ι] (R : _root_.Matrix μ (ι × Fin w) ℤ)
    (z : ι × Fin w → ℤ) (j : μ) :
    liftPreimage R z (Sum.inl j) = (R *ᵥ z) j := rfl

@[simp] theorem liftPreimage_inr [Fintype ι] (R : _root_.Matrix μ (ι × Fin w) ℤ)
    (z : ι × Fin w → ℤ) (p : ι × Fin w) :
    liftPreimage R z (Sum.inr p) = z p := rfl

theorem liftPreimage_eq_mulVec [Fintype ι] [DecidableEq ι]
    (R : _root_.Matrix μ (ι × Fin w) ℤ) (z : ι × Fin w → ℤ) :
    liftPreimage R z = trapdoorTransform R *ᵥ z := by
  rw [trapdoorTransform, _root_.Matrix.fromRows_mulVec, _root_.Matrix.one_mulVec, liftPreimage]

theorem cast_comp_liftPreimage (w : ℕ) [Fintype ι] [DecidableEq ι]
    (R : _root_.Matrix μ (ι × Fin w) ℤ) (z : ι × Fin w → ℤ) :
    (Int.cast ∘ liftPreimage R z : μ ⊕ (ι × Fin w) → ZMod (2 ^ w)) =
      (trapdoorTransform R).map Int.cast *ᵥ (Int.cast ∘ z) := by
  rw [liftPreimage_eq_mulVec]
  funext k
  exact RingHom.map_mulVec (Int.castRingHom (ZMod (2 ^ w))) (trapdoorTransform R) z k

/-- Action of `taggedMatrix w Abar R H` on a lifted vector `[R z; z]`:
`A *ᵥ [R z; z] = H *ᵥ (G *ᵥ z)` modulo `2 ^ w`. -/
@[simp] theorem taggedMatrix_mulVec_liftPreimage (w : ℕ)
    [Fintype ι] [DecidableEq ι] [Fintype μ]
    (Abar : _root_.Matrix ι μ (ZMod (2 ^ w)))
    (R : _root_.Matrix μ (ι × Fin w) ℤ)
    (H : _root_.Matrix ι ι (ZMod (2 ^ w)))
    (z : ι × Fin w → ℤ) :
    taggedMatrix w Abar R H *ᵥ (Int.cast ∘ liftPreimage R z) =
      H *ᵥ (gadgetMatrix w *ᵥ (Int.cast ∘ z)) := by
  rw [cast_comp_liftPreimage, _root_.Matrix.mulVec_mulVec, taggedMatrix_mul_trapdoorTransform,
    ← _root_.Matrix.mulVec_mulVec]

/-- Lifting any kernel vector `z ∈ Λ^⊥(G)` yields a kernel vector `[R z; z] ∈ Λ^⊥(A)`. -/
theorem liftPreimage_inKernelLattice (w : ℕ)
    [Fintype ι] [DecidableEq ι] [Fintype μ]
    (Abar : _root_.Matrix ι μ (ZMod (2 ^ w)))
    (R : _root_.Matrix μ (ι × Fin w) ℤ)
    (H : _root_.Matrix ι ι (ZMod (2 ^ w)))
    {z : ι × Fin w → ℤ} (hz : InKernelLattice (gadgetMatrix w) z) :
    InKernelLattice (taggedMatrix w Abar R H) (liftPreimage R z) := by
  unfold InKernelLattice at hz ⊢
  rw [taggedMatrix_mulVec_liftPreimage, hz, _root_.Matrix.mulVec_zero]

/-- The `w` lifted kernel vectors `[R; I] * S = [R S; S]` obtained from the gadget basis
`S = gadgetBasis w`. These are the right-hand `w` columns of the basis `S_A` of
[MicciancioPeikert2012], Lemma 5.3; they alone do not span `Λ^⊥(A)`, and the left-hand block of
`S_A` is not formalized. -/
def extendedGadgetBasis (w : ℕ) [Fintype ι] [DecidableEq ι]
    (R : _root_.Matrix μ (ι × Fin w) ℤ) : _root_.Matrix (μ ⊕ (ι × Fin w)) (ι × Fin w) ℤ :=
  trapdoorTransform R * gadgetBasis w

theorem extendedGadgetBasis_eq_fromRows (w : ℕ) [Fintype ι] [DecidableEq ι]
    (R : _root_.Matrix μ (ι × Fin w) ℤ) :
    extendedGadgetBasis w R = _root_.Matrix.fromRows (R * gadgetBasis w) (gadgetBasis w) := by
  rw [extendedGadgetBasis, trapdoorTransform, _root_.Matrix.fromRows_mul, _root_.Matrix.one_mul]

/-- Every column of `extendedGadgetBasis w R` lies in `Λ^⊥(A)`:
`taggedMatrix w Abar R H * ([R; I] * S) ≡ 0 (mod 2 ^ w)`. -/
@[simp] theorem taggedMatrix_mul_extendedGadgetBasis (w : ℕ)
    [Fintype ι] [DecidableEq ι] [Fintype μ]
    (Abar : _root_.Matrix ι μ (ZMod (2 ^ w)))
    (R : _root_.Matrix μ (ι × Fin w) ℤ)
    (H : _root_.Matrix ι ι (ZMod (2 ^ w))) :
    taggedMatrix w Abar R H *
        (extendedGadgetBasis w R).map (Int.cast : ℤ → ZMod (2 ^ w)) = 0 := by
  have hmap :
      (extendedGadgetBasis w R).map (Int.cast : ℤ → ZMod (2 ^ w)) =
        (trapdoorTransform R).map Int.cast * (gadgetBasis w).map Int.cast := by
    ext k q
    exact RingHom.map_matrix_mul (trapdoorTransform R) (gadgetBasis w) k q
      (Int.castRingHom (ZMod (2 ^ w)))
  rw [hmap, ← _root_.Matrix.mul_assoc, taggedMatrix_mul_trapdoorTransform,
    _root_.Matrix.mul_assoc, gadgetMatrix_mul_gadgetBasis, _root_.Matrix.mul_zero]

theorem extendedGadgetBasis_col_inKernelLattice (w : ℕ)
    [Fintype ι] [DecidableEq ι] [Fintype μ]
    (Abar : _root_.Matrix ι μ (ZMod (2 ^ w)))
    (R : _root_.Matrix μ (ι × Fin w) ℤ)
    (H : _root_.Matrix ι ι (ZMod (2 ^ w)))
    (q : ι × Fin w) :
    InKernelLattice (taggedMatrix w Abar R H) (fun k => extendedGadgetBasis w R k q) := by
  funext i
  exact congrFun (congrFun (taggedMatrix_mul_extendedGadgetBasis w Abar R H) i) q

private theorem natAbs_sum_le {α : Type*} [Fintype α] (f : α → ℤ) (B : ℕ)
    (hf : ∀ a : α, (f a).natAbs ≤ B) :
    (∑ a : α, f a).natAbs ≤ Fintype.card α * B := by
  calc
    (∑ a : α, f a).natAbs ≤ ∑ a : α, (f a).natAbs := Int.natAbs_sum_le Finset.univ f
    _ ≤ ∑ _a : α, B := Finset.sum_le_sum fun a _ => hf a
    _ = Fintype.card α * B := by simp

/-- Top-block entry bound for `extendedGadgetBasis w R`: if every entry of row `j` of `R` has
magnitude at most `B`, then `|(R * S) j q| ≤ 2 * (|ι| * w) * B`. -/
theorem natAbs_extendedGadgetBasis_inl_le (w : ℕ) [Fintype ι] [DecidableEq ι]
    (R : _root_.Matrix μ (ι × Fin w) ℤ) (j : μ) (q : ι × Fin w) (B : ℕ)
    (hR : ∀ p : ι × Fin w, (R j p).natAbs ≤ B) :
    (extendedGadgetBasis w R (Sum.inl j) q).natAbs ≤ 2 * Fintype.card (ι × Fin w) * B := by
  rw [extendedGadgetBasis_eq_fromRows, _root_.Matrix.fromRows_apply_inl, _root_.Matrix.mul_apply]
  have hterm : ∀ p : ι × Fin w, (R j p * gadgetBasis w p q).natAbs ≤ 2 * B := fun p => by
    rw [Int.natAbs_mul, mul_comm]
    exact Nat.mul_le_mul (natAbs_gadgetBasis_le_two w p q) (hR p)
  calc
    (∑ p : ι × Fin w, R j p * gadgetBasis w p q).natAbs ≤
        Fintype.card (ι × Fin w) * (2 * B) :=
      natAbs_sum_le (fun p => R j p * gadgetBasis w p q) (2 * B) hterm
    _ = 2 * Fintype.card (ι × Fin w) * B := by ring

/-- Bottom-block entry bound for `extendedGadgetBasis w R`: every entry has magnitude at most `2`.
-/
theorem natAbs_extendedGadgetBasis_inr_le (w : ℕ) [Fintype ι] [DecidableEq ι]
    (R : _root_.Matrix μ (ι × Fin w) ℤ) (p q : ι × Fin w) :
    (extendedGadgetBasis w R (Sum.inr p) q).natAbs ≤ 2 := by
  rw [extendedGadgetBasis_eq_fromRows, _root_.Matrix.fromRows_apply_inr]
  exact natAbs_gadgetBasis_le_two w p q

/-- Deterministic syndrome inversion `f_A⁻¹` using the trapdoor `R` and inverse tag `Hinv`:
given `u : ι → ZMod (2 ^ w)`, decompose `Hinv *ᵥ u` into `{0, 1}` digits via `gadgetDecomp w` and
lift via `[R; I]`. This is a deterministic analogue of the preimage sampler of
[MicciancioPeikert2012], Section 5.4: it returns a short preimage, not a Gaussian sample. -/
def invertSyndrome (w : ℕ) [Fintype ι]
    (Hinv : _root_.Matrix ι ι (ZMod (2 ^ w)))
    (R : _root_.Matrix μ (ι × Fin w) ℤ)
    (u : ι → ZMod (2 ^ w)) : μ ⊕ (ι × Fin w) → ℤ :=
  liftPreimage R (gadgetDecomp w (Hinv *ᵥ u))

/-- Correctness of deterministic syndrome inversion: if `H * Hinv = 1`, then
`A *ᵥ invertSyndrome w Hinv R u = u` modulo `2 ^ w`. -/
@[simp] theorem taggedMatrix_mulVec_invertSyndrome (w : ℕ)
    [Fintype ι] [DecidableEq ι] [Fintype μ]
    (Abar : _root_.Matrix ι μ (ZMod (2 ^ w)))
    (R : _root_.Matrix μ (ι × Fin w) ℤ)
    {H Hinv : _root_.Matrix ι ι (ZMod (2 ^ w))} (hH : H * Hinv = 1)
    (u : ι → ZMod (2 ^ w)) :
    taggedMatrix w Abar R H *ᵥ (Int.cast ∘ invertSyndrome w Hinv R u) = u := by
  rw [invertSyndrome, taggedMatrix_mulVec_liftPreimage, gadgetMatrix_mulVec_gadgetDecomp,
    _root_.Matrix.mulVec_mulVec, hH, _root_.Matrix.one_mulVec]

/-- Any parity-check matrix `A` admitting an `H`-tag `G`-trapdoor `R` is primitive: its integer
column combinations span `(ZMod (2 ^ w)) ^ ι` (the remark after [MicciancioPeikert2012],
Definition 5.2). -/
theorem IsHTagTrapdoor.surjective [Fintype ι] [DecidableEq ι] [Fintype μ]
    {A : _root_.Matrix ι (μ ⊕ (ι × Fin w)) (ZMod (2 ^ w))}
    {R : _root_.Matrix μ (ι × Fin w) ℤ}
    {H : _root_.Matrix ι ι (ZMod (2 ^ w))}
    (htrap : IsHTagTrapdoor w A R H) :
    Function.Surjective (fun x : μ ⊕ (ι × Fin w) → ℤ => A *ᵥ (Int.cast ∘ x)) := by
  rcases htrap with ⟨heq, ⟨u, rfl⟩⟩
  intro v
  refine ⟨invertSyndrome w ↑u⁻¹ R v, ?_⟩
  dsimp only [invertSyndrome]
  rw [cast_comp_liftPreimage, _root_.Matrix.mulVec_mulVec, heq,
    ← _root_.Matrix.mulVec_mulVec, gadgetMatrix_mulVec_gadgetDecomp,
    _root_.Matrix.mulVec_mulVec, Units.mul_inv, _root_.Matrix.one_mulVec]

/-- Any tagged matrix with an invertible tag `H` (`H * Hinv = 1`) is primitive: its integer
column combinations span `(ZMod (2 ^ w)) ^ ι` (the remark after [MicciancioPeikert2012],
Definition 5.2). -/
theorem taggedMatrix_surjective (w : ℕ) [Fintype ι] [DecidableEq ι] [Fintype μ]
    (Abar : _root_.Matrix ι μ (ZMod (2 ^ w)))
    (R : _root_.Matrix μ (ι × Fin w) ℤ)
    {H Hinv : _root_.Matrix ι ι (ZMod (2 ^ w))} (hH : H * Hinv = 1) :
    Function.Surjective
      (fun x : μ ⊕ (ι × Fin w) → ℤ => taggedMatrix w Abar R H *ᵥ (Int.cast ∘ x)) :=
  fun u => ⟨invertSyndrome w Hinv R u, taggedMatrix_mulVec_invertSyndrome w Abar R hH u⟩

/-- Top-block infinity-norm bound for `invertSyndrome`: if every entry in row `j` of `R` has
magnitude at most `B`, then `|invertSyndrome w Hinv R u (Sum.inl j)| ≤ (|ι| * w) * B`. -/
theorem natAbs_invertSyndrome_inl_le (w : ℕ) [Fintype ι]
    (Hinv : _root_.Matrix ι ι (ZMod (2 ^ w)))
    (R : _root_.Matrix μ (ι × Fin w) ℤ)
    (u : ι → ZMod (2 ^ w)) (j : μ) (B : ℕ)
    (hR : ∀ p : ι × Fin w, (R j p).natAbs ≤ B) :
    (invertSyndrome w Hinv R u (Sum.inl j)).natAbs ≤ Fintype.card (ι × Fin w) * B := by
  simp only [invertSyndrome, liftPreimage_inl, _root_.Matrix.mulVec, dotProduct]
  refine natAbs_sum_le (fun p : ι × Fin w => R j p * gadgetDecomp w (Hinv *ᵥ u) p) B fun p => ?_
  calc
    (R j p * gadgetDecomp w (Hinv *ᵥ u) p).natAbs =
        (R j p).natAbs * (gadgetDecomp w (Hinv *ᵥ u) p).natAbs := Int.natAbs_mul _ _
    _ ≤ B * 1 := Nat.mul_le_mul (hR p) (natAbs_gadgetDecomp_le_one w (Hinv *ᵥ u) p)
    _ = B := Nat.mul_one B

/-- Bottom-block infinity-norm bound for `invertSyndrome`: every bottom coordinate lies in
`{0, 1}`, hence has magnitude at most `1`. -/
theorem natAbs_invertSyndrome_inr_le (w : ℕ) [Fintype ι]
    (Hinv : _root_.Matrix ι ι (ZMod (2 ^ w)))
    (R : _root_.Matrix μ (ι × Fin w) ℤ)
    (u : ι → ZMod (2 ^ w)) (p : ι × Fin w) :
    (invertSyndrome w Hinv R u (Sum.inr p)).natAbs ≤ 1 :=
  natAbs_gadgetDecomp_le_one w (Hinv *ᵥ u) p

/-! ### Deterministic trapdoor LWE inversion (Section 5.3, Algorithm 2, Theorem 5.4) -/

/-- The LWE evaluation `g_A(s, e) = sᵀ A + eᵀ mod 2 ^ w` associated with a parity-check matrix `A`
([MicciancioPeikert2012], Section 5.3; LWE itself is recalled in Section 2.2). -/
def trapdoorLWE (w : ℕ) [Fintype ι]
    (A : _root_.Matrix ι κ (ZMod (2 ^ w)))
    (s : ι → ZMod (2 ^ w))
    (e : κ → ℤ) : κ → ZMod (2 ^ w) :=
  s ᵥ* A + (Int.cast ∘ e)

/-- The projected error `eᵀ [R; I] = e_1ᵀ R + e_2ᵀ` in gadget space `ι × Fin w`
([MicciancioPeikert2012], Section 5.3, Algorithm 2 and the proof of Theorem 5.4). -/
def projectedError [Fintype μ]
    (R : _root_.Matrix μ (ι × Fin w) ℤ)
    (e : μ ⊕ (ι × Fin w) → ℤ) : ι × Fin w → ℤ :=
  (e ∘ Sum.inl) ᵥ* R + (e ∘ Sum.inr)

theorem projectedError_eq_vecMul [Fintype ι] [DecidableEq ι] [Fintype μ]
    (R : _root_.Matrix μ (ι × Fin w) ℤ)
    (e : μ ⊕ (ι × Fin w) → ℤ) :
    projectedError R e = e ᵥ* trapdoorTransform R := by
  rw [trapdoorTransform, _root_.Matrix.vecMul_fromRows, _root_.Matrix.vecMul_one, projectedError]

theorem cast_comp_projectedError (w : ℕ) [Fintype ι] [DecidableEq ι] [Fintype μ]
    (R : _root_.Matrix μ (ι × Fin w) ℤ)
    (e : μ ⊕ (ι × Fin w) → ℤ) :
    (Int.cast ∘ projectedError R e : ι × Fin w → ZMod (2 ^ w)) =
      (Int.cast ∘ e) ᵥ* (trapdoorTransform R).map Int.cast := by
  rw [projectedError_eq_vecMul]
  funext p
  exact RingHom.map_vecMul (Int.castRingHom (ZMod (2 ^ w))) (trapdoorTransform R) e p

/-- Fundamental reduction of `g_A` to `g_G` via `[R; I]`: right-multiplying
`bᵀ = sᵀ A + eᵀ mod 2 ^ w` by `[R; I]` produces `g_G(Hᵀ s, eᵀ [R; I])`
([MicciancioPeikert2012], Section 5.3, Algorithm 2, step 1). -/
@[simp] theorem trapdoorLWE_vecMul_trapdoorTransform (w : ℕ)
    [Fintype ι] [DecidableEq ι] [Fintype μ]
    (Abar : _root_.Matrix ι μ (ZMod (2 ^ w)))
    (R : _root_.Matrix μ (ι × Fin w) ℤ)
    (H : _root_.Matrix ι ι (ZMod (2 ^ w)))
    (s : ι → ZMod (2 ^ w))
    (e : μ ⊕ (ι × Fin w) → ℤ) :
    trapdoorLWE w (taggedMatrix w Abar R H) s e ᵥ* (trapdoorTransform R).map Int.cast =
      gadgetLWE w (s ᵥ* H) (projectedError R e) := by
  rw [trapdoorLWE, _root_.Matrix.add_vecMul, _root_.Matrix.vecMul_vecMul,
    taggedMatrix_mul_trapdoorTransform, ← _root_.Matrix.vecMul_vecMul,
    ← cast_comp_projectedError, gadgetLWE]

/-- Infinity-norm bound on the projected error `eᵀ [R; I]`:
if `|R j p| ≤ B_R` for all `j` and `|e k| ≤ B_e` for all `k`, then
`|projectedError R e p| ≤ (1 + |μ| * B_R) * B_e`. This is an infinity-norm substitute for the
Cauchy–Schwarz step in the proof of [MicciancioPeikert2012], Theorem 5.4. -/
theorem natAbs_projectedError_le [Fintype μ]
    (R : _root_.Matrix μ (ι × Fin w) ℤ)
    (e : μ ⊕ (ι × Fin w) → ℤ)
    (p : ι × Fin w) (B_R B_e : ℕ)
    (hR : ∀ j : μ, (R j p).natAbs ≤ B_R)
    (he : ∀ k : μ ⊕ (ι × Fin w), (e k).natAbs ≤ B_e) :
    (projectedError R e p).natAbs ≤ (1 + Fintype.card μ * B_R) * B_e := by
  simp only [projectedError, Pi.add_apply, _root_.Matrix.vecMul, dotProduct, Function.comp_apply]
  have hsum : (∑ j : μ, e (Sum.inl j) * R j p).natAbs ≤ Fintype.card μ * (B_e * B_R) :=
    natAbs_sum_le (fun j => e (Sum.inl j) * R j p) (B_e * B_R) fun j => by
      rw [Int.natAbs_mul]
      exact Nat.mul_le_mul (he (Sum.inl j)) (hR j)
  have hinr : (e (Sum.inr p)).natAbs ≤ B_e := he (Sum.inr p)
  have htri := Int.natAbs_add_le (∑ j : μ, e (Sum.inl j) * R j p) (e (Sum.inr p))
  calc
    (∑ j : μ, e (Sum.inl j) * R j p + e (Sum.inr p)).natAbs ≤
        Fintype.card μ * (B_e * B_R) + B_e := by omega
    _ = (1 + Fintype.card μ * B_R) * B_e := by ring

/-- Recover the LWE secret `s` from `bᵀ = sᵀ A + eᵀ mod 2 ^ w` using the trapdoor `R` and inverse
tag `Hinv` ([MicciancioPeikert2012], Section 5.3, Algorithm 2, steps 1–3, with the oracle `O`
instantiated by `invertGadget w`): compute `bhat = b ᵥ* [R; I]`, invert `g_G`, and multiply by
`Hinv`. -/
def invertLWESecret (w : ℕ) [Fintype ι] [DecidableEq ι] [Fintype μ]
    (Hinv : _root_.Matrix ι ι (ZMod (2 ^ w)))
    (R : _root_.Matrix μ (ι × Fin w) ℤ)
    (b : μ ⊕ (ι × Fin w) → ZMod (2 ^ w)) : ι → ZMod (2 ^ w) :=
  invertGadget w (b ᵥ* (trapdoorTransform R).map Int.cast) ᵥ* Hinv

/-- Full LWE inversion algorithm `Invert(R, A, b)` ([MicciancioPeikert2012], Algorithm 2):
recover `s = invertLWESecret w Hinv R b` and lift `b - s ᵥ* A` to its unique short integer
representative via `ZMod.valMinAbs`. -/
def invertLWE (w : ℕ) [Fintype ι] [DecidableEq ι] [Fintype μ]
    (Abar : _root_.Matrix ι μ (ZMod (2 ^ w)))
    (R : _root_.Matrix μ (ι × Fin w) ℤ)
    (H Hinv : _root_.Matrix ι ι (ZMod (2 ^ w)))
    (b : μ ⊕ (ι × Fin w) → ZMod (2 ^ w)) :
    (ι → ZMod (2 ^ w)) × (μ ⊕ (ι × Fin w) → ℤ) :=
  let s := invertLWESecret w Hinv R b
  let A := taggedMatrix w Abar R H
  (s, fun k => (b k - (s ᵥ* A) k).valMinAbs)

/-- Secret recovery for Algorithm 2 (deterministic part of [MicciancioPeikert2012],
Theorem 5.4): if `H * Hinv = 1` and `4 * |projectedError R e p| < 2 ^ w` for all
`p : ι × Fin w`, then `invertLWESecret` recovers `s` from
`trapdoorLWE w (taggedMatrix w Abar R H) s e`. The hypothesis is the coordinatewise condition
`R̄ e ∈ P_{1/2}(q · B⁻ᵗ)` from the proof of Theorem 5.4 with `B = 2 I` (slightly strict at the
endpoint `-q / 4`), not the paper's Euclidean bound on `e`. -/
@[simp] theorem invertLWESecret_trapdoorLWE (w : ℕ)
    [Fintype ι] [DecidableEq ι] [Fintype μ]
    (Abar : _root_.Matrix ι μ (ZMod (2 ^ w)))
    (R : _root_.Matrix μ (ι × Fin w) ℤ)
    {H Hinv : _root_.Matrix ι ι (ZMod (2 ^ w))} (hH : H * Hinv = 1)
    (s : ι → ZMod (2 ^ w))
    (e : μ ⊕ (ι × Fin w) → ℤ)
    (he : ∀ p : ι × Fin w, 4 * (projectedError R e p).natAbs < 2 ^ w) :
    invertLWESecret w Hinv R (trapdoorLWE w (taggedMatrix w Abar R H) s e) = s := by
  rw [invertLWESecret, trapdoorLWE_vecMul_trapdoorTransform, invertGadget_gadgetLWE w _ _ he,
    _root_.Matrix.vecMul_vecMul, hH, _root_.Matrix.vecMul_one]

/-- Full LWE inversion correctness (`Invert`, [MicciancioPeikert2012], Algorithm 2,
deterministic part of Theorem 5.4): under `H * Hinv = 1`, `4 * |projectedError R e p| < 2 ^ w`,
and `2 * |e k| < 2 ^ w`, `invertLWE` recovers the exact pair `(s, e)`. -/
@[simp] theorem invertLWE_trapdoorLWE (w : ℕ)
    [Fintype ι] [DecidableEq ι] [Fintype μ]
    (Abar : _root_.Matrix ι μ (ZMod (2 ^ w)))
    (R : _root_.Matrix μ (ι × Fin w) ℤ)
    {H Hinv : _root_.Matrix ι ι (ZMod (2 ^ w))} (hH : H * Hinv = 1)
    (s : ι → ZMod (2 ^ w))
    (e : μ ⊕ (ι × Fin w) → ℤ)
    (hproj : ∀ p : ι × Fin w, 4 * (projectedError R e p).natAbs < 2 ^ w)
    (he : ∀ k : μ ⊕ (ι × Fin w), 2 * (e k).natAbs < 2 ^ w) :
    invertLWE w Abar R H Hinv (trapdoorLWE w (taggedMatrix w Abar R H) s e) = (s, e) := by
  dsimp only [invertLWE]
  rw [invertLWESecret_trapdoorLWE w Abar R hH s e hproj]
  congr 1
  funext k
  have hsub : trapdoorLWE w (taggedMatrix w Abar R H) s e k - (s ᵥ* taggedMatrix w Abar R H) k =
      (e k : ZMod (2 ^ w)) := by
    simp [trapdoorLWE]
  rw [hsub]
  have hk := he k
  exact (ZMod.valMinAbs_spec (e k : ZMod (2 ^ w)) (e k)).mpr ⟨rfl, by omega, by omega⟩

/-- Infinity-norm analogue of the first claim of [MicciancioPeikert2012], Theorem 5.4:
if `|R j p| ≤ B_R`, `|e k| ≤ B_e`, and `4 * (1 + |μ| * B_R) * B_e < 2 ^ w`, then `invertLWE`
recovers `(s, e)` from `g_A(s, e)`. The paper's version bounds `‖e‖` in terms of `s_1(R)`; the
probabilistic claim for Gaussian errors is not formalized. -/
theorem invertLWE_trapdoorLWE_of_norm_bound (w : ℕ)
    [Fintype ι] [DecidableEq ι] [Fintype μ]
    (Abar : _root_.Matrix ι μ (ZMod (2 ^ w)))
    (R : _root_.Matrix μ (ι × Fin w) ℤ)
    {H Hinv : _root_.Matrix ι ι (ZMod (2 ^ w))} (hH : H * Hinv = 1)
    (s : ι → ZMod (2 ^ w))
    (e : μ ⊕ (ι × Fin w) → ℤ)
    {B_R B_e : ℕ}
    (hR : ∀ j p, (R j p).natAbs ≤ B_R)
    (he : ∀ k, (e k).natAbs ≤ B_e)
    (hbound : 4 * (1 + Fintype.card μ * B_R) * B_e < 2 ^ w) :
    invertLWE w Abar R H Hinv (trapdoorLWE w (taggedMatrix w Abar R H) s e) = (s, e) := by
  refine invertLWE_trapdoorLWE w Abar R hH s e (fun p => ?_) (fun k => ?_)
  · calc
      4 * (projectedError R e p).natAbs ≤ 4 * ((1 + Fintype.card μ * B_R) * B_e) :=
        Nat.mul_le_mul_left 4 (natAbs_projectedError_le R e p B_R B_e (fun j => hR j p) he)
      _ = 4 * (1 + Fintype.card μ * B_R) * B_e := (Nat.mul_assoc _ _ _).symm
      _ < 2 ^ w := hbound
  · have hle : 2 * (e k).natAbs ≤ 4 * (1 + Fintype.card μ * B_R) * B_e := by
      calc
        2 * (e k).natAbs ≤ 2 * B_e := Nat.mul_le_mul_left 2 (he k)
        _ ≤ 4 * (1 + Fintype.card μ * B_R) * B_e :=
          Nat.mul_le_mul_right B_e (by omega : 2 ≤ 4 * (1 + Fintype.card μ * B_R))
    exact Nat.lt_of_le_of_lt hle hbound

/-! ### Probabilistic `GenTrap` algorithm and idealized hybrid (Section 5.2, Algorithm 1) -/

/-- Sample a row of a short integer trapdoor matrix `R` with independent centered-binomial
entries in `[-η, η]` (one admissible choice of the distribution `D` in
[MicciancioPeikert2012], Algorithm 1; the paper's instantiations use subgaussian or discrete
Gaussian `D`). -/
noncomputable def sampleTrapdoorRow (n w η : ℕ) : ProbComp (Fin n × Fin w → ℤ) :=
  (fun (blocks : Fin n → Fin w → ℤ) p => blocks p.1 p.2) <$>
    OracleComp.replicateFin n (OracleComp.replicateFin w (sampleCenteredBinomial η))

/-- Sample a short integer trapdoor matrix `R : Matrix (Fin mbar) (Fin n × Fin w) ℤ` with
independent centered-binomial entries in `[-η, η]`. -/
noncomputable def sampleTrapdoorMatrix (mbar n w η : ℕ) :
    ProbComp (_root_.Matrix (Fin mbar) (Fin n × Fin w) ℤ) :=
  OracleComp.replicateFin mbar (sampleTrapdoorRow n w η)

theorem mem_support_sampleTrapdoorRow_iff (n w η : ℕ) (row : Fin n × Fin w → ℤ) :
    row ∈ (ProbComp.eval (sampleTrapdoorRow n w η)).support ↔
      ∀ p : Fin n × Fin w, (row p).natAbs ≤ η := by
  simp only [sampleTrapdoorRow, ProbComp.eval_map, PMF.mem_support_map_iff,
    ProbComp.mem_support_replicateFin_iff, mem_support_sampleCenteredBinomial_iff]
  constructor
  · rintro ⟨blocks, hblocks, rfl⟩ ⟨i, j⟩
    exact hblocks i j
  · intro hrow
    refine ⟨fun i j => row (i, j), fun i j => hrow (i, j), ?_⟩
    funext ⟨i, j⟩
    rfl

/-- Support characterization of `sampleTrapdoorMatrix`: a matrix `R` is in the support iff every
entry has magnitude at most `η`. -/
theorem mem_support_sampleTrapdoorMatrix_iff (mbar n w η : ℕ)
    (R : _root_.Matrix (Fin mbar) (Fin n × Fin w) ℤ) :
    R ∈ (ProbComp.eval (sampleTrapdoorMatrix mbar n w η)).support ↔
      ∀ j p, (R j p).natAbs ≤ η :=
  (ProbComp.mem_support_replicateFin_iff mbar (sampleTrapdoorRow n w η) R).trans
    (forall_congr' fun j => mem_support_sampleTrapdoorRow_iff n w η (R j))

/-- Probabilistic trapdoor key generation `GenTrap_D(Abar, H)` with uniform `Abar`
([MicciancioPeikert2012], Section 5.2, Algorithm 1):
sample a uniform matrix `Abar ← sampleMatrix n mbar w` and a short trapdoor matrix
`R ← sampleTrapdoorMatrix mbar n w η`, and output `(taggedMatrix w Abar R H, R)`. -/
noncomputable def genTrap (n mbar w η : ℕ)
    (H : _root_.Matrix (Fin n) (Fin n) (ZMod (2 ^ w))) :
    ProbComp
      (_root_.Matrix (Fin n) (Fin mbar ⊕ (Fin n × Fin w)) (ZMod (2 ^ w)) ×
        _root_.Matrix (Fin mbar) (Fin n × Fin w) ℤ) := do
  let Abar ← sampleMatrix n mbar w
  let R ← sampleTrapdoorMatrix mbar n w η
  return (taggedMatrix w Abar R H, R)

/-- For any invertible tag `H` (`IsUnit H`), every pair `(A, R)` in the support of
`genTrap n mbar w η H` satisfies `IsHTagTrapdoor w A R H`, the entrywise bound `|R j p| ≤ η`, and
`A = taggedMatrix w Abar R H` for some `Abar`
([MicciancioPeikert2012], Algorithm 1, "whose correctness is immediate"). -/
theorem mem_support_genTrap (n mbar w η : ℕ)
    {H : _root_.Matrix (Fin n) (Fin n) (ZMod (2 ^ w))} (hH : IsUnit H)
    {out : _root_.Matrix (Fin n) (Fin mbar ⊕ (Fin n × Fin w)) (ZMod (2 ^ w)) ×
      _root_.Matrix (Fin mbar) (Fin n × Fin w) ℤ}
    (hout : out ∈ (ProbComp.eval (genTrap n mbar w η H)).support) :
    IsHTagTrapdoor w out.1 out.2 H ∧
      (∀ j p, (out.2 j p).natAbs ≤ η) ∧
      ∃ Abar : _root_.Matrix (Fin n) (Fin mbar) (ZMod (2 ^ w)),
        out.1 = taggedMatrix w Abar out.2 H := by
  rcases out with ⟨A, R⟩
  simp only [genTrap, ProbComp.eval_bind, ProbComp.eval_pure, eval_sampleMatrix,
    PMF.mem_support_bind_iff, PMF.mem_support_uniformOfFintype, true_and,
    mem_support_sampleTrapdoorMatrix_iff, PMF.mem_support_pure_iff, Prod.mk.injEq] at hout
  rcases hout with ⟨Abar, R, hR, rfl, rfl⟩
  exact ⟨isHTagTrapdoor_taggedMatrix w Abar R hH, hR, Abar, rfl⟩

/-- Sample a uniform gadget-sized row `Fin n × Fin w → ZMod (2 ^ w)`. -/
noncomputable def sampleGadgetRow (n w : ℕ) : ProbComp (Fin n × Fin w → ZMod (2 ^ w)) :=
  (fun (blocks : Fin n → Fin w → ZMod (2 ^ w)) p => blocks p.1 p.2) <$>
    OracleComp.replicateFin n (sampleVector w w)

@[simp] theorem eval_sampleGadgetRow (n w : ℕ) :
    ProbComp.eval (sampleGadgetRow n w) =
      PMF.uniformOfFintype (Fin n × Fin w → ZMod (2 ^ w)) := by
  simp only [sampleGadgetRow, ProbComp.eval_map, ProbComp.eval_replicateFin,
    eval_sampleVector, PMF.pi_uniformOfFintype]
  exact PMF.uniformOfFintype_map_equiv (Equiv.curry (Fin n) (Fin w) (ZMod (2 ^ w))).symm

/-- Sample a uniform gadget-sized matrix `Matrix (Fin n) (Fin n × Fin w) (ZMod (2 ^ w))`. -/
noncomputable def sampleGadgetBlock (n w : ℕ) :
    ProbComp (_root_.Matrix (Fin n) (Fin n × Fin w) (ZMod (2 ^ w))) :=
  OracleComp.replicateFin n (sampleGadgetRow n w)

@[simp] theorem eval_sampleGadgetBlock (n w : ℕ) :
    ProbComp.eval (sampleGadgetBlock n w) =
      PMF.uniformOfFintype (_root_.Matrix (Fin n) (Fin n × Fin w) (ZMod (2 ^ w))) := by
  unfold _root_.Matrix
  simp only [sampleGadgetBlock, ProbComp.eval_replicateFin, eval_sampleGadgetRow,
    PMF.pi_uniformOfFintype]
  congr 1

/-- Idealized hybrid of `GenTrap`: replacing `Abar * R` by an independent uniform matrix `U`
yields `[Abar | H * G - U]`. [MicciancioPeikert2012], Section 5.2, argues that `A` is close to
uniform "as long as the distribution of `[Abar | -Abar R]` is"; both the statistical and the
computational instantiation justify exactly this replacement. Neither justification is
formalized here, so no statement relates `genTrap` to `genTrapIdeal`. -/
noncomputable def genTrapIdeal (n mbar w : ℕ)
    (H : _root_.Matrix (Fin n) (Fin n) (ZMod (2 ^ w))) :
    ProbComp (_root_.Matrix (Fin n) (Fin mbar ⊕ (Fin n × Fin w)) (ZMod (2 ^ w))) := do
  let Abar ← sampleMatrix n mbar w
  let U ← sampleGadgetBlock n w
  return _root_.Matrix.fromCols Abar (H * gadgetMatrix w - U)

/-- In the ideal LWE hybrid of `GenTrap`, the public matrix `[Abar | H * G - U]` is identically
uniform over `Matrix (Fin n) (Fin mbar ⊕ (Fin n × Fin w)) (ZMod (2 ^ w))` for every tag `H`.
In particular, its distribution is independent of `H`. -/
@[simp] theorem eval_genTrapIdeal_eq_uniform (n mbar w : ℕ)
    (H : _root_.Matrix (Fin n) (Fin n) (ZMod (2 ^ w))) :
    ProbComp.eval (genTrapIdeal n mbar w H) =
      PMF.uniformOfFintype
        (_root_.Matrix (Fin n) (Fin mbar ⊕ (Fin n × Fin w)) (ZMod (2 ^ w))) := by
  simp only [genTrapIdeal, ProbComp.eval_bind, ProbComp.eval_pure,
    eval_sampleMatrix, eval_sampleGadgetBlock]
  change
    ((PMF.uniformOfFintype (_root_.Matrix (Fin n) (Fin mbar) (ZMod (2 ^ w)))).bind fun Abar =>
        (PMF.uniformOfFintype (_root_.Matrix (Fin n) (Fin n × Fin w) (ZMod (2 ^ w)))).map fun U =>
          _root_.Matrix.fromCols Abar (H * gadgetMatrix w - U)) =
      PMF.uniformOfFintype
        (_root_.Matrix (Fin n) (Fin mbar ⊕ (Fin n × Fin w)) (ZMod (2 ^ w)))
  rw [PMF.uniformOfFintype_bind_map]
  let e :
      (_root_.Matrix (Fin n) (Fin mbar) (ZMod (2 ^ w)) ×
          _root_.Matrix (Fin n) (Fin n × Fin w) (ZMod (2 ^ w))) ≃
        _root_.Matrix (Fin n) (Fin mbar ⊕ (Fin n × Fin w)) (ZMod (2 ^ w)) :=
    { toFun := fun pair => _root_.Matrix.fromCols pair.1 (H * gadgetMatrix w - pair.2)
      invFun := fun A => (A.toCols₁, H * gadgetMatrix w - A.toCols₂)
      left_inv := fun ⟨Abar, U⟩ => by
        ext <;> simp
      right_inv := fun A => by
        simp [sub_sub_cancel] }
  exact PMF.uniformOfFintype_map_equiv e

/-- Tag-independence of `genTrapIdeal`: any two tags `H` and `H'` induce the exact same public
matrix distribution. -/
theorem eval_genTrapIdeal_eq_of_tags (n mbar w : ℕ)
    (H H' : _root_.Matrix (Fin n) (Fin n) (ZMod (2 ^ w))) :
    ProbComp.eval (genTrapIdeal n mbar w H) = ProbComp.eval (genTrapIdeal n mbar w H') := by
  rw [eval_genTrapIdeal_eq_uniform, eval_genTrapIdeal_eq_uniform]

end Cslib.Crypto.LWE.Trapdoor
