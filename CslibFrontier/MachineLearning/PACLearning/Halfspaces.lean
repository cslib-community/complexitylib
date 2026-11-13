/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.MachineLearning.PACLearning.VCDimension
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# The VC dimension of halfspaces

For a linear map `Φ : V →ₗ[ℝ] α → ℝ` from a real vector space of parameters to real functions on
`α`, `positivityClass Φ` is the binary class `{x ↦ decide (0 < Φ v x) : v ∈ V}`. If `V` is
finite-dimensional, no set of more than `finrank ℝ V` points is shattered
(`card_le_finrank_of_setShatters_positivityClass`): the evaluation functionals at such points are
linearly dependent in the dual space, and labelling the points with positive coefficients `true`
makes the vanishing combination strictly positive. If the parameters can realize every real
vector of values at `finrank ℝ V` distinct points, those points are shattered, and the VC dimension
equals `finrank ℝ V` (`vcDim_positivityClass_eq`). This is the argument of
[ShalevShwartzBenDavid2014, Theorem 9.2] for an arbitrary finite-dimensional family of linear
functionals.

Instances:
* homogeneous halfspaces `x ↦ decide (0 < w ⬝ᵥ x)` in `Fin d → ℝ` have VC dimension `d`
  [ShalevShwartzBenDavid2014, Theorem 9.2], shattering the standard basis;
* affine halfspaces `x ↦ decide (0 < w ⬝ᵥ x + b)` have VC dimension `d + 1`
  [ShalevShwartzBenDavid2014, Theorem 9.3], shattering `0` and the standard basis.

The source writes halfspaces as `sign (⟪w, x⟫ + b)`; here a point is labelled `true` exactly when
the value is strictly positive, as in the perceptron
(`CslibFrontier.MachineLearning.OnlineLearning.MistakeBound.Perceptron`). The upper bound holds for
this convention without any general-position assumption.

## Main definitions

* `Cslib.MachineLearning.PACLearning.positivityClass`: the positivity sets of a linear family.
* `Cslib.MachineLearning.PACLearning.homogeneousHalfspaces`,
  `Cslib.MachineLearning.PACLearning.affineHalfspaces`: halfspaces in `Fin d → ℝ`.

## Main results

* `Cslib.MachineLearning.PACLearning.card_le_finrank_of_setShatters_positivityClass`,
  `Cslib.MachineLearning.PACLearning.vcDim_positivityClass_le`: at most `finrank ℝ V` points are
  shattered.
* `Cslib.MachineLearning.PACLearning.setShatters_positivityClass_range`: points at which every
  vector of values is realized are shattered.
* `Cslib.MachineLearning.PACLearning.vcDim_positivityClass_eq`: the VC dimension is `finrank ℝ V`
  when `finrank ℝ V` points admit all values.
* `Cslib.MachineLearning.PACLearning.vcDim_homogeneousHalfspaces`,
  `Cslib.MachineLearning.PACLearning.vcDim_affineHalfspaces`: the values `d` and `d + 1`.

## References

* [S. Shalev-Shwartz, S. Ben-David, *Understanding Machine Learning: From Theory to
  Algorithms*][ShalevShwartzBenDavid2014], Section 9.1.3, Theorems 9.2 and 9.3
-/

public section

open Module

namespace Cslib.MachineLearning.PACLearning

variable {α V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The **positivity class** of a linear family `Φ : V →ₗ[ℝ] α → ℝ`: the classifiers
`x ↦ decide (0 < Φ v x)` for `v : V`. -/
noncomputable def positivityClass (Φ : V →ₗ[ℝ] α → ℝ) : ConceptClass α Bool :=
  Set.range fun v x => decide (0 < Φ v x)

theorem mem_positivityClass {Φ : V →ₗ[ℝ] α → ℝ} {c : α → Bool} :
    c ∈ positivityClass Φ ↔ ∃ v, (fun x => decide (0 < Φ v x)) = c := Iff.rfl

/-- **No more than `finrank ℝ V` points are shattered** by the positivity class of a linear family
on a finite-dimensional parameter space. -/
theorem card_le_finrank_of_setShatters_positivityClass [FiniteDimensional ℝ V]
    (Φ : V →ₗ[ℝ] α → ℝ) {W : Finset α} (hW : SetShatters (positivityClass Φ) ↑W) :
    W.card ≤ finrank ℝ V := by
  classical
  by_contra hlt
  push Not at hlt
  let ev : W → Dual ℝ V := fun x => (LinearMap.proj (R := ℝ) (φ := fun _ : α => ℝ) x.1).comp Φ
  have hdep : ¬ LinearIndependent ℝ ev := fun hli => by
    have := hli.fintype_card_le_finrank
    rw [Fintype.card_coe, Subspace.dual_finrank_eq] at this
    omega
  obtain ⟨g, hg, i₀, hi₀⟩ := Fintype.not_linearIndependent_iff.1 hdep
  have hsum (v : V) : ∑ x, g x * Φ v x.1 = 0 := by
    have := congrArg (fun f : Dual ℝ V => f v) hg
    simpa [ev, LinearMap.sum_apply] using this
  -- Replace `g` by `-g` if needed so that some coefficient is positive.
  obtain ⟨g, hsum, i₁, hi₁⟩ : ∃ g : W → ℝ, (∀ v, ∑ x, g x * Φ v x.1 = 0) ∧ ∃ i, 0 < g i := by
    rcases hi₀.lt_or_gt with h | h
    · refine ⟨-g, fun v => ?_, i₀, by simpa using h⟩
      simp only [Pi.neg_apply, neg_mul, Finset.sum_neg_distrib, hsum v, neg_zero]
    · exact ⟨g, hsum, i₀, h⟩
  -- Label `true` exactly the points with a positive coefficient.
  obtain ⟨c, ⟨v, rfl⟩, hc⟩ := hW {x | ∃ h : x ∈ W, 0 < g ⟨x, h⟩} fun x hx => hx.1
  have hmem (x : W) : 0 < Φ v x.1 ↔ 0 < g x := by
    have := congrArg (fun s : Set α => x.1 ∈ s) hc
    simpa [x.2] using this
  have hterm (x : W) : 0 ≤ g x * Φ v x.1 := by
    rcases le_or_gt (g x) 0 with h | h
    · exact mul_nonneg_of_nonpos_of_nonpos h (not_lt.1 fun h' => h.not_gt ((hmem x).1 h'))
    · exact (mul_pos h ((hmem x).2 h)).le
  have hpos : 0 < ∑ x, g x * Φ v x.1 :=
    Finset.sum_pos' (fun x _ => hterm x) ⟨i₁, Finset.mem_univ _, mul_pos hi₁ ((hmem i₁).2 hi₁)⟩
  exact hpos.ne' (hsum v)

/-- Points at which the parameters realize every vector of real values are shattered. -/
theorem setShatters_positivityClass_range {ι : Type*} (Φ : V →ₗ[ℝ] α → ℝ) (x : ι → α)
    (hsurj : ∀ t : ι → ℝ, ∃ v, ∀ i, Φ v (x i) = t i) :
    SetShatters (positivityClass Φ) (Set.range x) := by
  classical
  intro W' hW'
  obtain ⟨v, hv⟩ := hsurj fun i => if x i ∈ W' then 1 else -1
  refine ⟨_, ⟨v, rfl⟩, ?_⟩
  ext y
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, decide_eq_true_eq,
    Set.mem_range]
  constructor
  · rintro ⟨hpos, i, rfl⟩
    by_contra hy
    simp only [hv, hy, ite_false] at hpos
    norm_num at hpos
  · intro hy
    obtain ⟨i, rfl⟩ := hW' hy
    exact ⟨by simp only [hv, hy, ite_true, zero_lt_one], i, rfl⟩

/-- The positivity class of a linear family on a finite-dimensional space has finite VC
dimension. -/
theorem hasFiniteVCDim_positivityClass [FiniteDimensional ℝ V] (Φ : V →ₗ[ℝ] α → ℝ) :
    HasFiniteVCDim (positivityClass Φ) :=
  hasFiniteVCDim_iff.2 ⟨_, fun _ hW => card_le_finrank_of_setShatters_positivityClass Φ hW⟩

/-- The VC dimension of the positivity class is at most `finrank ℝ V`. -/
theorem vcDim_positivityClass_le [FiniteDimensional ℝ V] (Φ : V →ₗ[ℝ] α → ℝ) :
    vcDim (positivityClass Φ) ≤ finrank ℝ V :=
  csSup_le' fun _ ⟨_, hWc, hW⟩ => hWc ▸ card_le_finrank_of_setShatters_positivityClass Φ hW

/-- The VC dimension of the positivity class is `finrank ℝ V` when `finrank ℝ V` distinct points
admit every vector of values. -/
theorem vcDim_positivityClass_eq [FiniteDimensional ℝ V] {ι : Type*} [Fintype ι]
    (Φ : V →ₗ[ℝ] α → ℝ) (x : ι → α) (hx : Function.Injective x)
    (hcard : Fintype.card ι = finrank ℝ V)
    (hsurj : ∀ t : ι → ℝ, ∃ v, ∀ i, Φ v (x i) = t i) :
    vcDim (positivityClass Φ) = finrank ℝ V := by
  classical
  refine le_antisymm (vcDim_positivityClass_le Φ) ?_
  have hsh : SetShatters (positivityClass Φ) ↑(Finset.univ.image x) := by
    rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
    exact setShatters_positivityClass_range Φ x hsurj
  have := hsh.card_le_vcDim (hasFiniteVCDim_positivityClass Φ)
  rwa [Finset.card_image_of_injective _ hx, Finset.card_univ, hcard] at this

/-! ### Halfspaces in `Fin d → ℝ` -/

variable {d : ℕ}

/-- The linear family `w ↦ (x ↦ w ⬝ᵥ x)` of homogeneous linear functionals. -/
noncomputable def homogeneousForm (d : ℕ) : (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ) → ℝ where
  toFun w x := w ⬝ᵥ x
  map_add' _ _ := funext fun _ => add_dotProduct _ _ _
  map_smul' _ _ := funext fun _ => smul_dotProduct _ _ _

/-- The linear family `(w, b) ↦ (x ↦ w ⬝ᵥ x + b)` of affine functionals. -/
noncomputable def affineForm (d : ℕ) : ((Fin d → ℝ) × ℝ) →ₗ[ℝ] (Fin d → ℝ) → ℝ where
  toFun p x := p.1 ⬝ᵥ x + p.2
  map_add' p q := by
    ext x
    simp only [Prod.fst_add, Prod.snd_add, add_dotProduct, Pi.add_apply]
    ring
  map_smul' r p := by
    ext x
    simp only [Prod.smul_fst, Prod.smul_snd, smul_dotProduct, smul_eq_mul, RingHom.id_apply,
      Pi.smul_apply]
    ring

/-- **Homogeneous halfspaces** in `Fin d → ℝ`: the classifiers `x ↦ decide (0 < w ⬝ᵥ x)`. -/
noncomputable def homogeneousHalfspaces (d : ℕ) : ConceptClass (Fin d → ℝ) Bool :=
  positivityClass (homogeneousForm d)

/-- **Affine halfspaces** in `Fin d → ℝ`: the classifiers `x ↦ decide (0 < w ⬝ᵥ x + b)`. -/
noncomputable def affineHalfspaces (d : ℕ) : ConceptClass (Fin d → ℝ) Bool :=
  positivityClass (affineForm d)

@[simp]
theorem homogeneousForm_apply (w x : Fin d → ℝ) : homogeneousForm d w x = w ⬝ᵥ x := by
  simp [homogeneousForm]

@[simp]
theorem affineForm_apply (p : (Fin d → ℝ) × ℝ) (x : Fin d → ℝ) :
    affineForm d p x = p.1 ⬝ᵥ x + p.2 := by
  simp [affineForm]

/-- Homogeneous halfspaces as the positivity class of `homogeneousForm`, for applying the general
`positivityClass` results. -/
theorem homogeneousHalfspaces_eq_positivityClass :
    homogeneousHalfspaces d = positivityClass (homogeneousForm d) := by
  rw [homogeneousHalfspaces]

/-- Affine halfspaces as the positivity class of `affineForm`, for applying the general
`positivityClass` results. -/
theorem affineHalfspaces_eq_positivityClass :
    affineHalfspaces d = positivityClass (affineForm d) := by
  rw [affineHalfspaces]

theorem mem_homogeneousHalfspaces {c : (Fin d → ℝ) → Bool} :
    c ∈ homogeneousHalfspaces d ↔ ∃ w : Fin d → ℝ, (fun x => decide (0 < w ⬝ᵥ x)) = c :=
  Iff.rfl

theorem mem_affineHalfspaces {c : (Fin d → ℝ) → Bool} :
    c ∈ affineHalfspaces d ↔
      ∃ w : Fin d → ℝ, ∃ b : ℝ, (fun x => decide (0 < w ⬝ᵥ x + b)) = c := by
  simp only [affineHalfspaces, mem_positivityClass, Prod.exists]
  rfl

/-- **The VC dimension of homogeneous halfspaces** in `Fin d → ℝ` is `d`
[ShalevShwartzBenDavid2014, Theorem 9.2]. -/
theorem vcDim_homogeneousHalfspaces (d : ℕ) : vcDim (homogeneousHalfspaces d) = d := by
  refine (vcDim_positivityClass_eq (homogeneousForm d) (fun k : Fin d => Pi.single k (1 : ℝ))
    (Pi.single_left_injective one_ne_zero) (by rw [Fintype.card_fin, finrank_fin_fun])
    fun t => ⟨t, fun i => ?_⟩).trans (finrank_fin_fun ℝ)
  simp [dotProduct_single]

/-- **The VC dimension of affine halfspaces** in `Fin d → ℝ` is `d + 1`
[ShalevShwartzBenDavid2014, Theorem 9.3]. -/
theorem vcDim_affineHalfspaces (d : ℕ) : vcDim (affineHalfspaces d) = d + 1 := by
  have hr : finrank ℝ ((Fin d → ℝ) × ℝ) = d + 1 := by
    rw [Module.finrank_prod, finrank_fin_fun, finrank_self]
  let x : Option (Fin d) → Fin d → ℝ := fun o => o.elim 0 fun k => Pi.single k 1
  refine (vcDim_positivityClass_eq (affineForm d) x ?_
    (by rw [Fintype.card_option, Fintype.card_fin, hr])
    fun t => ⟨(fun k => t (some k) - t none, t none), ?_⟩).trans hr
  · rintro (_ | i) (_ | j) hij
    · rfl
    · exact absurd (congrFun hij j).symm (by simp [x])
    · exact absurd (congrFun hij i) (by simp [x])
    · exact congrArg some (Pi.single_left_injective one_ne_zero hij)
  · rintro (_ | i)
    · simp [x]
    · simp [x, dotProduct_single]

end Cslib.MachineLearning.PACLearning
