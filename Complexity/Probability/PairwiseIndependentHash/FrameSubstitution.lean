/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Probability.PairwiseIndependentHash.FrameChannel
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Affine substitution invariance of frame-conditioned channels

A frame-conditioned channel `A = (a₀, F)` (`Cslib.Probability.FrameChannel`) evaluates an
identifier `y` as the polynomial `a₀ + ∑ j, y ^ (j + 1) • F j`. Substituting `α y + β` for `y`, with
`α ≠ 0`, gives another polynomial of the same degree. Its constant column is
`a₀ + ∑ j, β ^ (j + 1) • F j`, and its coefficient columns are `B F`, where `B` is the
upper-triangular matrix of binomial coefficients with diagonal `α, α ^ 2, …, α ^ r`. Since `B` is
invertible, `B F` is again a frame, so the substitution is a map of frame-conditioned channels
(`FrameChannel.affineSubst`) with `(A.affineSubst β hα).eval y = A.eval (α * y + β)`
(`FrameChannel.eval_affineSubst`). The map is injective, hence a permutation of the finite
channel space (`FrameChannel.affineSubstEquiv`). So it preserves the uniform law.

Consequently, replacing every identifier `y` by `α y + β` leaves the joint law of all evaluations
unchanged, for one channel (`dens_eval_comp_affine`) and for any finite family of independent
channels (`dens_pi_eval_comp_affine`). This is item 4 of Lemma 3.1 of the OpenAI preprint
[OpenAI2026LogSpace, Lemma 3.1 and its proof, pp. 9–10]. There it covers, in particular, a common
fixed padding suffix appended to all identifiers.

## Main definitions

* `Cslib.Probability.FrameChannel.affineSubst`: the channel obtained by substituting `α y + β`.
* `Cslib.Probability.FrameChannel.affineSubstEquiv`: the same map, as a permutation.

## Main results

* `Cslib.Probability.FrameChannel.eval_affineSubst`: its value at `y` is the value at `α y + β`.
* `Cslib.Probability.FrameChannel.affineSubst_injective`: substitution is injective.
* `Cslib.Probability.dens_eval_comp_affine`, `Cslib.Probability.dens_pi_eval_comp_affine`: the
  substitution leaves the law of all evaluations unchanged.

## References

* [OpenAI, *Exact Derandomization of Logarithmic Space: L = RL = BPL*][OpenAI2026LogSpace],
  Lemma 3.1 (preprint, not peer reviewed)
-/

public section

namespace Cslib.Probability

open Finset Matrix

variable {P H r : ℕ} [Fact P.Prime]

section SubstMatrix

variable (α β : ZMod P)

/-- The **substitution matrix** of `y ↦ α y + β`: its entry `(k, j)` is the coefficient of
`y ^ (k + 1)` in `(α y + β) ^ (j + 1)`, namely `C(j + 1, k + 1) α ^ (k + 1) β ^ (j - k)`. -/
private def substMatrix : Matrix (Fin r) (Fin r) (ZMod P) :=
  Matrix.of fun k j ↦ ((j.val + 1).choose (k.val + 1) : ZMod P) * α ^ (k.val + 1) *
    β ^ (j.val - k.val)

private theorem substMatrix_apply (k j : Fin r) :
    substMatrix α β k j =
      ((j.val + 1).choose (k.val + 1) : ZMod P) * α ^ (k.val + 1) * β ^ (j.val - k.val) :=
  rfl

private theorem substMatrix_isUpperTriangular : (substMatrix (r := r) α β).IsUpperTriangular := by
  intro k j hjk
  rw [substMatrix_apply, Nat.choose_eq_zero_of_lt (by simp only [id] at hjk; omega),
    Nat.cast_zero, zero_mul, zero_mul]

variable {α} in
/-- The substitution matrix is invertible: it is upper triangular with diagonal `α ^ (k + 1)`. -/
private theorem isUnit_substMatrix (hα : α ≠ 0) : IsUnit (substMatrix (r := r) α β) := by
  rw [isUnit_iff_isUnit_det, isUnit_iff_ne_zero,
    (substMatrix_isUpperTriangular α β).det_ne_zero_iff]
  intro k
  simp [substMatrix_apply, hα]

/-- The binomial expansion of `(α y + β) ^ (j + 1)` through the substitution matrix. -/
private theorem pow_add_sum_substMatrix (j : Fin r) (y : ZMod P) :
    β ^ (j.val + 1) + ∑ k : Fin r, y ^ (k.val + 1) * substMatrix α β k j =
      (α * y + β) ^ (j.val + 1) := by
  rw [add_pow, sum_range_succ', pow_zero, one_mul, Nat.sub_zero, Nat.choose_zero_right,
    Nat.cast_one, mul_one, add_comm (β ^ (j.val + 1))]
  congr 1
  simp only [substMatrix_apply]
  rw [Fin.sum_univ_eq_sum_range (fun k ↦ y ^ (k + 1) * (((j.val + 1).choose (k + 1) : ZMod P) *
    α ^ (k + 1) * β ^ (j.val - k)))]
  refine (sum_subset (range_subset_range.2 (by omega : j.val + 1 ≤ r)) fun k _ hk ↦ ?_).symm.trans
    (sum_congr rfl fun k _ ↦ ?_)
  · rw [Nat.choose_eq_zero_of_lt (by simp only [mem_range] at hk; omega), Nat.cast_zero,
      zero_mul, zero_mul, mul_zero]
  · rw [Nat.add_sub_add_right, mul_pow]
    ring

/-- The coefficient columns after substituting `α y + β`: `F' k = ∑ j, B k j • F j`. -/
private def substColumns (F : Fin r → Fin H → ZMod P) : Fin r → Fin H → ZMod P :=
  fun k ↦ ∑ j, substMatrix α β k j • F j

/-- Substitution maps frames to frames, since the substitution matrix is invertible. -/
private theorem linearIndependent_substColumns {α : ZMod P} (hα : α ≠ 0)
    {F : Fin r → Fin H → ZMod P} (hF : LinearIndependent (ZMod P) F) :
    LinearIndependent (ZMod P) (substColumns α β F) := by
  rw [Fintype.linearIndependent_iff] at hF ⊢
  intro g hg
  have hsum : ∑ j, (g ᵥ* substMatrix α β) j • F j = 0 := by
    rw [← hg]
    simp only [substColumns, smul_sum, smul_smul, vecMul, dotProduct, sum_smul]
    exact sum_comm
  have h0 : g ᵥ* substMatrix α β = 0 ᵥ* substMatrix α β := by
    rw [zero_vecMul]
    exact funext (hF _ hsum)
  intro k
  rw [vecMul_injective_iff_isUnit.2 (isUnit_substMatrix β hα) h0]
  rfl

end SubstMatrix

namespace FrameChannel

variable {α : ZMod P} (β : ZMod P) (hα : α ≠ 0)

/-- The channel obtained by **substituting `α y + β`** into `A`, for `α ≠ 0`: its value at `y` is
the value of `A` at `α y + β` (`eval_affineSubst`). -/
def affineSubst (A : FrameChannel P H r) : FrameChannel P H r :=
  (A.1 + ∑ j, β ^ (j.val + 1) • A.2.1 j,
    ⟨substColumns α β A.2.1, linearIndependent_substColumns β hα A.2.2⟩)

/-- **Substitution**: the substituted channel evaluates `y` as the original channel evaluates
`α y + β`. -/
theorem eval_affineSubst (A : FrameChannel P H r) (y : ZMod P) :
    (A.affineSubst β hα).eval y = A.eval (α * y + β) := by
  simp only [FrameChannel.eval, affineSubst, substColumns]
  simp_rw [← pow_add_sum_substMatrix α β, add_smul, sum_add_distrib, sum_smul, smul_sum,
    smul_smul]
  rw [sum_comm (s := univ) (t := univ)
    (f := fun j k ↦ (y ^ (k.val + 1) * substMatrix α β k j) • A.2.1 j)]
  abel

/-- The substituted channel, as a function of the identifier. -/
theorem eval_comp_affineSubst (A : FrameChannel P H r) :
    (A.affineSubst β hα).eval = fun y ↦ A.eval (α * y + β) :=
  funext (eval_affineSubst β hα A)

/-- Substitution is injective: the substitution matrix is invertible, so it recovers the frame,
and then the constant column. -/
theorem affineSubst_injective :
    Function.Injective (affineSubst (P := P) (H := H) (r := r) β hα) := by
  intro A A' h
  have hF : A.2.1 = A'.2.1 := by
    have h2 := congrArg (fun A ↦ A.2.1) h
    funext j i
    have hi : substMatrix α β *ᵥ (fun j ↦ A.2.1 j i) = substMatrix α β *ᵥ (fun j ↦ A'.2.1 j i) := by
      funext k
      have := congrFun (congrFun h2 k) i
      simpa [affineSubst, substColumns, mulVec, dotProduct, Finset.sum_apply] using this
    exact congrFun (mulVec_injective_iff_isUnit.2 (isUnit_substMatrix β hα) hi) j
  have h1 := congrArg Prod.fst h
  simp only [affineSubst, hF] at h1
  exact Prod.ext (add_right_cancel h1) (Subtype.ext hF)

/-- Substituting `α y + β`, for `α ≠ 0`, permutes the frame-conditioned channels. -/
noncomputable def affineSubstEquiv : FrameChannel P H r ≃ FrameChannel P H r :=
  Equiv.ofBijective _ (Finite.injective_iff_bijective.1 (affineSubst_injective β hα))

theorem affineSubstEquiv_apply (A : FrameChannel P H r) :
    affineSubstEquiv β hα A = A.affineSubst β hα := by
  rw [affineSubstEquiv, Equiv.ofBijective_apply]

end FrameChannel

/-- Precomposing an event with a permutation of a finite uniform space keeps its probability. -/
private theorem dens_filter_comp_equiv {ι : Type*} [Fintype ι] (e : ι ≃ ι) (p : ι → Prop)
    [DecidablePred p] : dens {i | p (e i)} = dens {i | p i} := by
  rw [dens_eq_card_div_card, dens_eq_card_div_card]
  congr 2
  exact card_nbij' e e.symm (fun i hi ↦ by simpa using hi) (fun i hi ↦ by simpa using hi)
    (fun i _ ↦ e.symm_apply_apply i) fun i _ ↦ e.apply_symm_apply i

variable {α : ZMod P} (hα : α ≠ 0) (β : ZMod P)

include hα in
/-- **Affine substitution invariance**: for `α ≠ 0`, the evaluations `y ↦ A.eval (α y + β)` of a
uniformly random frame-conditioned channel have the same law as the evaluations `y ↦ A.eval y`
[OpenAI2026LogSpace, Lemma 3.1, item 4]. -/
theorem dens_eval_comp_affine (E : (ZMod P → Fin H → ZMod P) → Prop) [DecidablePred E] :
    dens {A : FrameChannel P H r | E fun y ↦ A.eval (α * y + β)} =
      dens {A : FrameChannel P H r | E A.eval} := by
  rw [← dens_filter_comp_equiv (FrameChannel.affineSubstEquiv β hα) fun A ↦ E A.eval]
  simp only [FrameChannel.affineSubstEquiv_apply, FrameChannel.eval_comp_affineSubst]

include hα in
/-- **Affine substitution invariance for independent channels**: for `α ≠ 0`, replacing every
identifier `y` by `α y + β` in a finite family of independent uniformly random frame-conditioned
channels leaves the joint law of all their evaluations unchanged
[OpenAI2026LogSpace, Lemma 3.1, item 4]. -/
theorem dens_pi_eval_comp_affine {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : (ι → ZMod P → Fin H → ZMod P) → Prop) [DecidablePred E] :
    dens {As : ι → FrameChannel P H r | E fun c y ↦ (As c).eval (α * y + β)} =
      dens {As : ι → FrameChannel P H r | E fun c ↦ (As c).eval} := by
  rw [← dens_filter_comp_equiv (Equiv.piCongrRight fun _ ↦ FrameChannel.affineSubstEquiv β hα)
    fun As : ι → FrameChannel P H r ↦ E fun c ↦ (As c).eval]
  simp only [Equiv.piCongrRight_apply, Pi.map_apply, FrameChannel.affineSubstEquiv_apply,
    FrameChannel.eval_comp_affineSubst]

end Cslib.Probability
