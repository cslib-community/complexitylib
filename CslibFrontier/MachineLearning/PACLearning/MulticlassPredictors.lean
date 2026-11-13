/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.MachineLearning.PACLearning.NatarajanDimension
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Matrix.DotProduct
import CslibFrontier.MachineLearning.PACLearning.GrowthFunction
import CslibFrontier.MachineLearning.PACLearning.Halfspaces
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Fintype.BigOperators
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# The Natarajan dimension of multiclass predictors

Upper bounds on the Natarajan dimension of the multiclass classes of
[ShalevShwartzBenDavid2014, Section 29.3]:

* **Multiclass-to-binary reductions** (Section 29.3.2). For a binary class `H`, a finite index
  type `κ` with `l` elements and a rule `r : (κ → Bool) → β`, `reductionClass H r` is the class
  of predictors `x ↦ r (fun i => h i x)` for `h : κ → α → Bool` with every `h i ∈ H`. If every
  shattered set of `H` has at most `d` points, every N-shattered set of the reduction has at most
  `3 d l log (3 l)` points (`card_le_of_natarajanShatters_reductionClass`). An N-shattered set of
  `n` points carries at least `2 ^ n` labelings of the reduction, while every labeling comes from
  `l` labelings of `H`, of which there are at most `exp (n / T) T ^ d` by Sauer's lemma
  (`growthFunction_le_exp_mul_pow`); the choice `T = 3 l` and `log 2 > 2 / 3` give the bound.
* **One-versus-all** (Section 29.3.1). `oneVsAllClass H ι` predicts the first label `i : ι`
  whose binary classifier says `true`, or the first label when none does; it is the reduction
  with the rule `argmaxFirst`, so its Natarajan dimension is at most `3 d k log (3 k)` for
  `k = |ι|` (`natarajanDim_oneVsAllClass_le`).
* **Linear multiclass predictors** (Section 29.3.3). For a linear family of scores
  `Φ : V →ₗ[ℝ] α → ι → ℝ` on a finite-dimensional space, `linearArgmaxClass Φ` is the class of
  predictors `x ↦ argmaxFirst (Φ v x)`. Every N-shattered set has at most `finrank ℝ V` points
  (`card_le_finrank_of_natarajanShatters_linearArgmaxClass`); for a class-sensitive feature map
  `Ψ : α → ι → Fin d → ℝ` and scores `⟪w, Ψ x i⟫` this is Theorem 29.7, `Ndim(H_Ψ) ≤ d`
  (`natarajanDim_linearArgmaxClass_featureScores_le`). The multivector construction, with one
  weight vector in `Fin n → ℝ` per label, has Natarajan dimension at most `|ι| n`, the upper bound
  of Corollary 29.8 (`natarajanDim_linearArgmaxClass_multivectorScores_le`).

Ties between labels are broken in favour of the smallest label (`argmaxFirst`), as the source
does for one-versus-all. The proof of Theorem 29.7 maps a point `x` of an N-shattered set to the
difference of the score vectors of the two witness labels; the source uses `f₀ x` minus `f₁ x`
and asserts strict inequalities that fail under ties. Here the difference is taken from the
smaller to the larger of the two labels: the predictor picks the larger label only if its score
is strictly greater, and the smaller label only if its score is at least as large, which is the
positive-versus-nonpositive split of `positivityClass`. The points are then shattered by a
positivity class with parameters in `V`, so `card_le_finrank_of_setShatters_positivityClass`
bounds their number.

Lemmas 29.5 and 29.6 display the bound `3 l d log (l d)`, which vanishes at `l = d = 1` although
the class `{x ↦ r (h x)}` with `r = id` N-shatters a point whenever `H` shatters one; the bound
`3 d l log (3 l)` proved here implies the displayed one when `d ≥ 3`. The source derives its bound
from `2 ^ n ≤ n ^ (d l)` and Lemma A.1; this file uses the exponential form of Sauer's lemma
instead.

## Main definitions

- `argmaxFirst s`: the smallest index at which `s : ι → γ` attains its maximum.
- `reductionClass H r`: the multiclass class obtained from the binary class `H` by the rule `r`.
- `oneVsAllClass H ι`: the one-versus-all class with labels `ι`.
- `linearArgmaxClass Φ`: the argmax predictors of a linear family of scores.
- `featureScores Ψ`, `multivectorScores ι n`: the scores of a class-sensitive feature map and of
  the multivector construction.

## Main results

- `card_le_of_natarajanShatters_reductionClass`, `natarajanDim_reductionClass_le`: Lemma 29.6 with
  the bound `3 d l log (3 l)`.
- `natarajanDim_oneVsAllClass_le`: Lemma 29.5 with the bound `3 d k log (3 k)`.
- `card_le_finrank_of_natarajanShatters_linearArgmaxClass`,
  `natarajanDim_linearArgmaxClass_le`: linear multiclass predictors with parameters in `V`.
- `natarajanDim_linearArgmaxClass_featureScores_le`: Theorem 29.7.
- `natarajanDim_linearArgmaxClass_multivectorScores_le`: the upper bound of Corollary 29.8.

## References

* [S. Shalev-Shwartz, S. Ben-David, *Understanding Machine Learning: From Theory to
  Algorithms*][ShalevShwartzBenDavid2014], Section 29.3
-/

public section

open Module

namespace Cslib.MachineLearning.PACLearning

variable {α β ι κ γ : Type*}

/-! ### The first maximizer -/

section ArgmaxFirst

variable [Fintype ι] [LinearOrder γ]

/-- The indices at which `s : ι → γ` attains its maximum. -/
private def maximizers (s : ι → γ) : Finset ι :=
  Finset.univ.filter fun i => ∀ j, s j ≤ s i

private theorem mem_maximizers {s : ι → γ} {i : ι} : i ∈ maximizers s ↔ ∀ j, s j ≤ s i := by
  simp only [maximizers, Finset.mem_filter, Finset.mem_univ, true_and]

private theorem maximizers_nonempty [Nonempty ι] (s : ι → γ) : (maximizers s).Nonempty := by
  obtain ⟨i, -, hi⟩ := Finset.univ.exists_max_image s Finset.univ_nonempty
  exact ⟨i, mem_maximizers.2 fun j => hi j (Finset.mem_univ j)⟩

variable [LinearOrder ι] [Nonempty ι]

/-- The smallest index at which `s : ι → γ` attains its maximum over the finite, nonempty,
linearly ordered index type `ι`. -/
def argmaxFirst (s : ι → γ) : ι :=
  (maximizers s).min' (maximizers_nonempty s)

/-- `argmaxFirst s` attains the maximum of `s`. -/
theorem apply_le_apply_argmaxFirst (s : ι → γ) (j : ι) : s j ≤ s (argmaxFirst s) :=
  mem_maximizers.1 (Finset.min'_mem _ _) j

/-- Every index before `argmaxFirst s` has a strictly smaller value. -/
theorem apply_lt_apply_argmaxFirst {s : ι → γ} {j : ι} (hj : j < argmaxFirst s) :
    s j < s (argmaxFirst s) := by
  refine lt_of_le_of_ne (apply_le_apply_argmaxFirst s j) fun h => hj.not_ge ?_
  refine Finset.min'_le _ _ (mem_maximizers.2 fun j' => ?_)
  rw [h]
  exact apply_le_apply_argmaxFirst s j'

/-- `argmaxFirst s = i` iff `s` attains its maximum at `i` and at no earlier index. -/
theorem argmaxFirst_eq_iff {s : ι → γ} {i : ι} :
    argmaxFirst s = i ↔ (∀ j, s j ≤ s i) ∧ ∀ j < i, s j < s i := by
  constructor
  · rintro rfl
    exact ⟨apply_le_apply_argmaxFirst s, fun _ => apply_lt_apply_argmaxFirst⟩
  · rintro ⟨hle, hlt⟩
    rcases lt_trichotomy (argmaxFirst s) i with h | h | h
    · exact absurd (apply_le_apply_argmaxFirst s i) (hlt _ h).not_ge
    · exact h
    · exact absurd (hle _) (apply_lt_apply_argmaxFirst h).not_ge

end ArgmaxFirst

/-! ### Multiclass-to-binary reductions -/

/-- The multiclass class obtained from the binary class `H` by the rule `r : (κ → Bool) → β`:
the predictors `x ↦ r (fun i => h i x)` for `h : κ → α → Bool` with every `h i ∈ H`
[ShalevShwartzBenDavid2014, Section 29.3.2]. -/
def reductionClass (H : ConceptClass α Bool) (r : (κ → Bool) → β) : ConceptClass α β :=
  {c | ∃ h : κ → α → Bool, (∀ i, h i ∈ H) ∧ c = fun x => r fun i => h i x}

theorem mem_reductionClass {H : ConceptClass α Bool} {r : (κ → Bool) → β} {c : α → β} :
    c ∈ reductionClass H r ↔ ∃ h : κ → α → Bool, (∀ i, h i ∈ H) ∧ c = fun x => r fun i => h i x :=
  Iff.rfl

private theorem natarajanBound_nonneg (d l : ℕ) :
    (0 : ℝ) ≤ 3 * d * l * Real.log (3 * l) := by
  rcases Nat.eq_zero_or_pos l with hl | hl
  · simp [hl]
  · have : (1 : ℝ) ≤ 3 * l := by
      have : (1 : ℝ) ≤ l := by exact_mod_cast hl
      linarith
    exact mul_nonneg (by positivity) (Real.log_nonneg this)

/-- **The Natarajan dimension of a multiclass-to-binary reduction**
[ShalevShwartzBenDavid2014, Lemma 29.6]: if every shattered set of `H` has at most `d` points,
then every set N-shattered by the reduction of `H` with `l = |κ|` binary classifiers has at most
`3 d l log (3 l)` points. The source displays `3 l d log (l d)`, which fails at `l = d = 1`. -/
theorem card_le_of_natarajanShatters_reductionClass [Fintype κ] {H : ConceptClass α Bool}
    {d : ℕ} (hH : ∀ W : Finset α, SetShatters H ↑W → W.card ≤ d) (r : (κ → Bool) → β)
    {W : Finset α} (hW : NatarajanShatters (reductionClass H r) ↑W) :
    (W.card : ℝ) ≤ 3 * d * Fintype.card κ * Real.log (3 * Fintype.card κ) := by
  classical
  obtain ⟨f₀, f₁, hne, hsh⟩ := hW
  set n := W.card
  let x : Fin n → α := fun j => (W.equivFin.symm j : α)
  have hxW (j : Fin n) : x j ∈ W := (W.equivFin.symm j).2
  -- The labelings of the points `x` realized by `H`, and the labelings of the reduction they
  -- generate.
  let F : Finset (Fin n → Bool) := Finset.univ.filter fun v => v ∈ restriction H x
  let P : Finset (Fin n → β) :=
    (Fintype.piFinset fun _ : κ => F).image fun u j => r fun i => u i j
  -- The `2 ^ n` labelings that choose `f₀` or `f₁` at each point all lie in `P`.
  let g : (Fin n → Bool) → Fin n → β := fun v j => cond (v j) (f₀ (x j)) (f₁ (x j))
  have hg : Function.Injective g := by
    intro v w hvw
    funext j
    have hj := congrFun hvw j
    have hne' := hne (x j) (hxW j)
    cases hv : v j <;> cases hw : w j <;>
      simp only [g, hv, hw, Bool.cond_true, Bool.cond_false] at hj
    · rfl
    · exact absurd hj.symm hne'
    · exact absurd hj hne'
    · rfl
  have hgP (v : Fin n → Bool) : g v ∈ P := by
    obtain ⟨c, hc, h₀, h₁⟩ := hsh {y | ∃ j, y = x j ∧ v j = true}
      (by rintro _ ⟨j, rfl, -⟩; exact hxW j)
    obtain ⟨h, hH', rfl⟩ := hc
    refine Finset.mem_image.2 ⟨fun i j => h i (x j), Fintype.mem_piFinset.2 fun i =>
      Finset.mem_filter.2 ⟨Finset.mem_univ _, mem_restriction.2 ⟨h i, hH' i, fun _ => rfl⟩⟩, ?_⟩
    funext j
    cases hv : v j
    · simp only [g, hv, Bool.cond_false]
      refine h₁ (x j) ⟨hxW j, ?_⟩
      rintro ⟨j', hj', hv'⟩
      rw [W.equivFin.symm.injective (Subtype.ext hj')] at hv
      rw [hv] at hv'
      exact Bool.false_ne_true hv'
    · simp only [g, hv, Bool.cond_true]
      exact h₀ (x j) ⟨j, rfl, hv⟩
  have hlow : 2 ^ n ≤ P.card := by
    calc 2 ^ n = (Finset.univ.image g).card := by
          rw [Finset.card_image_of_injective _ hg, Finset.card_univ, Fintype.card_fun,
            Fintype.card_bool, Fintype.card_fin]
      _ ≤ P.card := Finset.card_le_card fun _ hv => by
          obtain ⟨v, -, rfl⟩ := Finset.mem_image.1 hv
          exact hgP v
  have hF : F.card ≤ growthFunction H n := by
    have : F = (restriction H x).toFinset := by
      ext v
      simp only [F, Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_toFinset]
    rw [this, ← Set.ncard_eq_toFinset_card']
    exact ncard_restriction_le_growthFunction H x
  have hup : P.card ≤ growthFunction H n ^ Fintype.card κ := by
    calc P.card ≤ (Fintype.piFinset fun _ : κ => F).card := Finset.card_image_le
      _ = F.card ^ Fintype.card κ := by
          rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ]
      _ ≤ growthFunction H n ^ Fintype.card κ := Nat.pow_le_pow_left hF _
  set l := Fintype.card κ
  rcases Nat.eq_zero_or_pos l with hl0 | hlpos
  · rw [hl0, pow_zero] at hup
    have hn0 : n = 0 := by
      by_contra hn0
      have := Nat.one_lt_two_pow hn0
      omega
    rw [hn0, Nat.cast_zero]
    exact natarajanBound_nonneg d l
  -- Sauer's lemma with `T = 3 l`.
  have hl1 : (1 : ℝ) ≤ l := by exact_mod_cast hlpos
  have hT : (1 : ℝ) ≤ 3 * l := by linarith
  have hsauer := growthFunction_le_exp_mul_pow hH n hT
  have hpow : (2 : ℝ) ^ n ≤ Real.exp (n / 3) * (3 * l) ^ (d * l) := by
    calc (2 : ℝ) ^ n ≤ (growthFunction H n : ℝ) ^ l := by
          exact_mod_cast hlow.trans hup
      _ ≤ (Real.exp (n / (3 * l)) * (3 * l) ^ d) ^ l :=
          pow_le_pow_left₀ (Nat.cast_nonneg _) hsauer l
      _ = Real.exp (n / 3) * (3 * l) ^ (d * l) := by
          rw [mul_pow, ← Real.exp_nat_mul, ← pow_mul]
          congr 2
          field_simp
  have hlog := Real.log_le_log (by positivity) hpow
  rw [Real.log_mul (Real.exp_pos _).ne' (pow_pos (by linarith) _).ne', Real.log_exp,
    Real.log_pow, Real.log_pow] at hlog
  have hlog2 : (2 : ℝ) / 3 < Real.log 2 := lt_trans (by norm_num) Real.log_two_gt_d9
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  push_cast at hlog
  nlinarith [mul_le_mul_of_nonneg_left hlog2.le hn0]

/-- **The Natarajan dimension of a multiclass-to-binary reduction**
[ShalevShwartzBenDavid2014, Lemma 29.6]: for a binary class of finite VC dimension `d` and
`l = |κ|` binary classifiers, the reduction has finite Natarajan dimension at most
`3 d l log (3 l)`. -/
theorem natarajanDim_reductionClass_le [Fintype κ] {H : ConceptClass α Bool}
    (hH : HasFiniteVCDim H) (r : (κ → Bool) → β) :
    HasFiniteNatarajanDim (reductionClass H r) ∧
      (natarajanDim (reductionClass H r) : ℝ) ≤
        3 * vcDim H * Fintype.card κ * Real.log (3 * Fintype.card κ) := by
  set b := 3 * (vcDim H : ℝ) * Fintype.card κ * Real.log (3 * Fintype.card κ)
  have hcard (W : Finset α) (hW : NatarajanShatters (reductionClass H r) ↑W) : W.card ≤ ⌊b⌋₊ :=
    Nat.le_floor <| card_le_of_natarajanShatters_reductionClass
      (fun _ hW => hW.card_le_vcDim hH) r hW
  exact ⟨hasFiniteNatarajanDim_iff.2 ⟨_, hcard⟩,
    (Nat.cast_le.2 (natarajanDim_le hcard)).trans (Nat.floor_le (natarajanBound_nonneg _ _))⟩

/-- The **one-versus-all** class with labels `ι` built from the binary class `H`: for a
classifier `h i ∈ H` per label, predict the first label whose classifier says `true`, or the
first label when none does [ShalevShwartzBenDavid2014, Section 29.3.1]. -/
def oneVsAllClass (H : ConceptClass α Bool) (ι : Type*) [Fintype ι] [LinearOrder ι]
    [Nonempty ι] : ConceptClass α ι :=
  reductionClass H (argmaxFirst : (ι → Bool) → ι)

/-- **The Natarajan dimension of one-versus-all** [ShalevShwartzBenDavid2014, Lemma 29.5]: for a
binary class of finite VC dimension `d` and `k` labels, the one-versus-all class has finite
Natarajan dimension at most `3 d k log (3 k)`; the source displays `3 k d log (k d)`. -/
theorem natarajanDim_oneVsAllClass_le [Fintype ι] [LinearOrder ι] [Nonempty ι]
    {H : ConceptClass α Bool} (hH : HasFiniteVCDim H) :
    HasFiniteNatarajanDim (oneVsAllClass H ι) ∧
      (natarajanDim (oneVsAllClass H ι) : ℝ) ≤
        3 * vcDim H * Fintype.card ι * Real.log (3 * Fintype.card ι) :=
  natarajanDim_reductionClass_le hH _

/-! ### Linear multiclass predictors -/

section Linear

variable [Fintype ι] [LinearOrder ι] [Nonempty ι] {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The **linear multiclass predictors** of a linear family of scores `Φ : V →ₗ[ℝ] α → ι → ℝ`:
the predictors `x ↦ argmaxFirst (Φ v x)` for `v : V`, breaking ties in favour of the smallest
label [ShalevShwartzBenDavid2014, Equation 29.1]. -/
noncomputable def linearArgmaxClass (Φ : V →ₗ[ℝ] α → ι → ℝ) : ConceptClass α ι :=
  Set.range fun v x => argmaxFirst (Φ v x)

theorem mem_linearArgmaxClass {Φ : V →ₗ[ℝ] α → ι → ℝ} {c : α → ι} :
    c ∈ linearArgmaxClass Φ ↔ ∃ v, (fun x => argmaxFirst (Φ v x)) = c :=
  Iff.rfl

/-- **No more than `finrank ℝ V` points are N-shattered** by the linear multiclass predictors of a
linear family of scores with parameters in a finite-dimensional space
[ShalevShwartzBenDavid2014, Theorem 29.7]. -/
theorem card_le_finrank_of_natarajanShatters_linearArgmaxClass [FiniteDimensional ℝ V]
    (Φ : V →ₗ[ℝ] α → ι → ℝ) {W : Finset α} (hW : NatarajanShatters (linearArgmaxClass Φ) ↑W) :
    W.card ≤ finrank ℝ V := by
  classical
  obtain ⟨f₀, f₁, hne, hsh⟩ := hW
  -- The smaller and the larger witness label at each point.
  let lo : α → ι := fun x => min (f₀ x) (f₁ x)
  let hi : α → ι := fun x => max (f₀ x) (f₁ x)
  have hlohi (x : α) (hx : x ∈ W) : lo x < hi x := min_lt_max.2 (hne x hx)
  -- The score of the larger label minus the score of the smaller one.
  let τ : V →ₗ[ℝ] α → ℝ :=
    { toFun := fun v x => Φ v x (hi x) - Φ v x (lo x)
      map_add' := fun v w => by
        funext x
        simp only [map_add, Pi.add_apply]
        ring
      map_smul' := fun a v => by
        funext x
        simp only [map_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        ring }
  refine card_le_finrank_of_setShatters_positivityClass τ fun W' hW' => ?_
  -- Choose the larger label on `W'` and the smaller one on the rest of `W`.
  obtain ⟨_, ⟨v, rfl⟩, h₀, h₁⟩ := hsh {y | y ∈ W ∧ (if y ∈ W' then hi y else lo y) = f₀ y}
    fun y hy => hy.1
  have hv (y : α) (hy : y ∈ W) : argmaxFirst (Φ v y) = if y ∈ W' then hi y else lo y := by
    by_cases ht : (if y ∈ W' then hi y else lo y) = f₀ y
    · rw [ht]
      exact h₀ y ⟨hy, ht⟩
    · have hmem : (if y ∈ W' then hi y else lo y) = f₀ y ∨
          (if y ∈ W' then hi y else lo y) = f₁ y := by
        split_ifs
        · exact max_choice _ _
        · exact min_choice _ _
      rw [hmem.resolve_left ht]
      exact h₁ y ⟨hy, fun h => ht h.2⟩
  refine ⟨_, mem_positivityClass.2 ⟨v, rfl⟩, ?_⟩
  ext y
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, decide_eq_true_eq,
    Finset.mem_coe]
  have hτ : τ v y = Φ v y (hi y) - Φ v y (lo y) := rfl
  constructor
  · rintro ⟨hpos, hy⟩
    by_contra hy'
    have h := apply_le_apply_argmaxFirst (Φ v y) (hi y)
    rw [hv y hy, ite_eq_right hy'] at h
    rw [hτ] at hpos
    linarith
  · intro hy
    have hyW : y ∈ W := hW' hy
    refine ⟨?_, hyW⟩
    have hlt : lo y < argmaxFirst (Φ v y) := by
      rw [hv y hyW, ite_eq_left hy]
      exact hlohi y hyW
    have h := apply_lt_apply_argmaxFirst hlt
    rw [hv y hyW, ite_eq_left hy] at h
    rw [hτ]
    linarith

/-- The linear multiclass predictors of a linear family of scores with parameters in a
finite-dimensional space have finite Natarajan dimension at most `finrank ℝ V`
[ShalevShwartzBenDavid2014, Theorem 29.7]. -/
theorem natarajanDim_linearArgmaxClass_le [FiniteDimensional ℝ V] (Φ : V →ₗ[ℝ] α → ι → ℝ) :
    HasFiniteNatarajanDim (linearArgmaxClass Φ) ∧
      natarajanDim (linearArgmaxClass Φ) ≤ finrank ℝ V :=
  ⟨hasFiniteNatarajanDim_iff.2
      ⟨_, fun _ hW => card_le_finrank_of_natarajanShatters_linearArgmaxClass Φ hW⟩,
    natarajanDim_le fun _ hW => card_le_finrank_of_natarajanShatters_linearArgmaxClass Φ hW⟩

end Linear

/-! ### Feature maps and the multivector construction -/

/-- The scores `⟪w, Ψ x i⟫` of a class-sensitive feature map `Ψ : α → ι → Fin d → ℝ`
[ShalevShwartzBenDavid2014, Section 17.2]. -/
noncomputable def featureScores {d : ℕ} (Ψ : α → ι → Fin d → ℝ) :
    (Fin d → ℝ) →ₗ[ℝ] α → ι → ℝ where
  toFun w x i := w ⬝ᵥ Ψ x i
  map_add' _ _ := funext fun _ => funext fun _ => add_dotProduct _ _ _
  map_smul' _ _ := funext fun _ => funext fun _ => smul_dotProduct _ _ _

@[simp]
theorem featureScores_apply {d : ℕ} (Ψ : α → ι → Fin d → ℝ) (w : Fin d → ℝ) (x : α) (i : ι) :
    featureScores Ψ w x i = w ⬝ᵥ Ψ x i := by
  simp [featureScores]

/-- The scores of the **multivector construction** with labels `ι` on `Fin n → ℝ`: one weight
vector `w i` per label and the score `⟪w i, x⟫` of label `i` [ShalevShwartzBenDavid2014,
Section 17.2.1]. Up to the identification of `ι → Fin n → ℝ` with `ℝ ^ (|ι| n)`, these are the
scores `⟪w, Ψ (x, i)⟫` of the feature map that places `x` in the block of label `i`. -/
noncomputable def multivectorScores (ι : Type*) (n : ℕ) :
    (ι → Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) → ι → ℝ where
  toFun w x i := w i ⬝ᵥ x
  map_add' _ _ := funext fun _ => funext fun _ => add_dotProduct _ _ _
  map_smul' _ _ := funext fun _ => funext fun _ => by
    simp only [Pi.smul_apply, smul_dotProduct, RingHom.id_apply]

@[simp]
theorem multivectorScores_apply {n : ℕ} (w : ι → Fin n → ℝ) (x : Fin n → ℝ) (i : ι) :
    multivectorScores ι n w x i = w i ⬝ᵥ x := by
  simp [multivectorScores]

section Scores

variable [Fintype ι] [LinearOrder ι] [Nonempty ι]

/-- **The Natarajan dimension of linear multiclass predictors** [ShalevShwartzBenDavid2014,
Theorem 29.7]: for a class-sensitive feature map `Ψ : α → ι → Fin d → ℝ`, the predictors
`x ↦ argmax_i ⟪w, Ψ x i⟫` have finite Natarajan dimension at most `d`. -/
theorem natarajanDim_linearArgmaxClass_featureScores_le {d : ℕ} (Ψ : α → ι → Fin d → ℝ) :
    HasFiniteNatarajanDim (linearArgmaxClass (featureScores Ψ)) ∧
      natarajanDim (linearArgmaxClass (featureScores Ψ)) ≤ d := by
  have h := natarajanDim_linearArgmaxClass_le (featureScores Ψ)
  rwa [finrank_fin_fun] at h

/-- **The multivector construction** with `k` labels on `Fin n → ℝ` has finite Natarajan
dimension at most `k n`, the upper bound of [ShalevShwartzBenDavid2014, Corollary 29.8]. -/
theorem natarajanDim_linearArgmaxClass_multivectorScores_le (n : ℕ) :
    HasFiniteNatarajanDim (linearArgmaxClass (multivectorScores ι n)) ∧
      natarajanDim (linearArgmaxClass (multivectorScores ι n)) ≤ Fintype.card ι * n := by
  have h := natarajanDim_linearArgmaxClass_le (multivectorScores ι n)
  rwa [Module.finrank_pi_fintype, Finset.sum_const, finrank_fin_fun, smul_eq_mul,
    Finset.card_univ] at h

end Scores

end Cslib.MachineLearning.PACLearning
