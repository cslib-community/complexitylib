/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.MachineLearning.Rademacher.Basic
public import Mathlib.Topology.MetricSpace.Lipschitz
import CslibFrontier.Probability.BitString.Massart
import CslibFrontier.Probability.PMF.Expect
import CslibFrontier.Probability.PMF.ToReal
import Mathlib.Algebra.Order.BigOperators.Expect

/-!
# Talagrand's contraction lemma for Rademacher complexity

Composing a bounded family of vectors `a : ι → Fin m → ℝ` coordinatewise with `K`-Lipschitz
functions `φ i : ℝ → ℝ` multiplies its Rademacher average by at most `K`:
`rademacherAverage (fun j i => φ i (a j i)) ≤ K * rademacherAverage a`
[MohriRostamizadehTalwalkar2018, Lemma 5.7]; cf. [LedouxTalagrand1991, Theorem 4.12, pp. 112–114]
and [ShalevShwartzBenDavid2014, Lemma 26.9]. No centering assumption `φ i 0 = 0` is required:
shifting `φ i` by a constant changes every vector by a fixed coordinate offset, which cancels in
expectation against a symmetric sign.

The proof follows [MohriRostamizadehTalwalkar2018, Lemma 5.7], replacing `(K : ℝ) * a j i` by
`φ i (a j i)` one coordinate at a time. At coordinate `i₀`, pairing each sign vector `σ` with its
flip at `i₀` reduces the step to the elementary two-branch inequality
`(⨆ j, (u j + g (x j))) + (⨆ j, (u j - g (x j))) ≤
  (⨆ j, (u j + K * x j)) + ⨆ j, (u j - K * x j)`
for a `K`-Lipschitz map `g`.

Specializing to restrictions of a uniformly bounded hypothesis class `F : Set (X → ℝ)` yields
contraction bounds for empirical and expected Rademacher complexities, both for direct composition
`(φ ∘ ·) '' F` and for sample-dependent per-example losses `(fun f z => φ z (f (g z))) '' F` such
as margin losses on labeled examples.

## Main results

* `Cslib.MachineLearning.rademacherAverage_comp_le`: **Talagrand's contraction lemma** in vector
  form [MohriRostamizadehTalwalkar2018, Lemma 5.7].
* `Cslib.MachineLearning.rademacherAverage_comp_le_empiricalRademacherComplexity`: per-index
  contraction against the empirical Rademacher complexity of a bounded class.
* `Cslib.MachineLearning.empiricalRademacherComplexity_image_comp_le_of_map`,
  `Cslib.MachineLearning.rademacherComplexity_image_comp_le_of_map`: contraction of empirical and
  population Rademacher complexities under example-dependent Lipschitz maps `z ↦ φ z (f (g z))`.
* `Cslib.MachineLearning.empiricalRademacherComplexity_image_comp_le`,
  `Cslib.MachineLearning.rademacherComplexity_image_comp_le`: contraction for `(φ ∘ ·) '' F`.

## References

* [M. Mohri, A. Rostamizadeh, A. Talwalkar, *Foundations of Machine Learning*, 2nd
  ed.][MohriRostamizadehTalwalkar2018], Section 5.4, Lemma 5.7
* [M. Ledoux, M. Talagrand, *Probability in Banach Spaces: Isoperimetry and
  Processes*][LedouxTalagrand1991], Theorem 4.12, pp. 112–114
* [S. Shalev-Shwartz, S. Ben-David, *Understanding Machine Learning: From Theory to
  Algorithms*][ShalevShwartzBenDavid2014], Lemma 26.9
-/

public section

open Finset
open scoped BigOperators NNReal

namespace Cslib.MachineLearning

open Cslib.BitString

/-! ### Single-coordinate contraction helpers -/

private theorem abs_apply_le_of_lipschitzWith {g : ℝ → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g)
    {t B : ℝ} (ht : |t| ≤ B) :
    |g t| ≤ |g 0| + K * max B 0 := by
  have hdist : |g t - g 0| ≤ K * |t| := by
    simpa only [Real.dist_eq, sub_zero] using hg.dist_le_mul t 0
  have hmul : (K : ℝ) * |t| ≤ K * max B 0 :=
    mul_le_mul_of_nonneg_left (ht.trans (le_max_left _ _)) K.coe_nonneg
  have habs : |g t| - |g 0| ≤ |g t - g 0| := abs_sub_abs_le_abs_sub (g t) (g 0)
  linarith

/-- Two-sign contraction step: for any bounded `u, x : ι → ℝ` and `K`-Lipschitz `g : ℝ → ℝ`,
averaging over the two signs `+1` and `-1` replaces `g (x j)` by `K * x j`. -/
private theorem ciSup_add_ciSup_lipschitz_le {ι : Type*} [Nonempty ι] {u x : ι → ℝ} {Bu B : ℝ}
    (hu : ∀ j, |u j| ≤ Bu) (hx : ∀ j, |x j| ≤ B) {g : ℝ → ℝ} {K : ℝ≥0}
    (hg : LipschitzWith K g) :
    (⨆ j, (u j + g (x j))) + (⨆ j, (u j - g (x j))) ≤
      (⨆ j, (u j + K * x j)) + ⨆ j, (u j - K * x j) := by
  have hbdd_lin {v : ι → ℝ} (hv : ∀ j, |v j| ≤ B) :
      BddAbove (Set.range fun j => u j + (K : ℝ) * v j) := by
    refine ⟨max Bu 0 + K * max B 0, ?_⟩
    rintro _ ⟨j, rfl⟩
    have hu_le : u j ≤ max Bu 0 := (le_abs_self _).trans ((hu j).trans (le_max_left _ _))
    have hv_le : (K : ℝ) * v j ≤ K * max B 0 :=
      mul_le_mul_of_nonneg_left ((le_abs_self _).trans ((hv j).trans (le_max_left _ _)))
        K.coe_nonneg
    dsimp only
    linarith
  have hbdd_pos : BddAbove (Set.range fun j => u j + (K : ℝ) * x j) := hbdd_lin hx
  have hbdd_neg : BddAbove (Set.range fun j => u j - (K : ℝ) * x j) := by
    simpa only [mul_neg, ← sub_eq_add_neg] using hbdd_lin (v := fun j => -x j) fun j => by
      rw [abs_neg]
      exact hx j
  set S := (⨆ j, (u j + (K : ℝ) * x j)) + ⨆ j, (u j - (K : ℝ) * x j)
  have hpair : ∀ j₁ j₂ : ι, (u j₁ + g (x j₁)) + (u j₂ - g (x j₂)) ≤ S := by
    intro j₁ j₂
    have hlip : |g (x j₁) - g (x j₂)| ≤ K * |x j₁ - x j₂| := by
      simpa only [Real.dist_eq] using hg.dist_le_mul (x j₁) (x j₂)
    have hdiff : g (x j₁) - g (x j₂) ≤ K * |x j₁ - x j₂| := (le_abs_self _).trans hlip
    rcases le_total (x j₂) (x j₁) with hle | hle
    · rw [abs_of_nonneg (sub_nonneg.2 hle)] at hdiff
      have h1 := le_ciSup hbdd_pos j₁
      have h2 := le_ciSup hbdd_neg j₂
      linarith
    · rw [abs_of_nonpos (sub_nonpos.2 hle)] at hdiff
      have h1 := le_ciSup hbdd_pos j₂
      have h2 := le_ciSup hbdd_neg j₁
      linarith
  have hstep : ∀ j₁ : ι, u j₁ + g (x j₁) ≤ S - ⨆ j₂, (u j₂ - g (x j₂)) := by
    intro j₁
    have h2 : (⨆ j₂, (u j₂ - g (x j₂))) ≤ S - (u j₁ + g (x j₁)) :=
      ciSup_le fun j₂ => by linarith [hpair j₁ j₂]
    linarith
  linarith [ciSup_le hstep]

private def flipSignAt {m : ℕ} (i₀ : Fin m) (σ : Fin m → Bool) : Fin m → Bool :=
  Function.update σ i₀ (!σ i₀)

private theorem flipSignAt_involutive {m : ℕ} (i₀ : Fin m) :
    Function.Involutive (flipSignAt i₀) := by
  intro σ
  funext i
  by_cases hi : i = i₀
  · subst hi
    simp only [flipSignAt, Function.update_self, Bool.not_not]
  · simp only [flipSignAt, Function.update_of_ne hi]

private theorem two_mul_expect_eq_expect_add_flipSignAt {m : ℕ} (i₀ : Fin m)
    (F : (Fin m → Bool) → ℝ) :
    2 * 𝔼 σ : Fin m → Bool, F σ = 𝔼 σ : Fin m → Bool, (F σ + F (flipSignAt i₀ σ)) := by
  have heq : 𝔼 σ : Fin m → Bool, F (flipSignAt i₀ σ) = 𝔼 σ : Fin m → Bool, F σ :=
    Fintype.expect_equiv (Function.Involutive.toPerm _ (flipSignAt_involutive i₀)) _ _ fun _ => rfl
  rw [Finset.expect_add_distrib, heq, two_mul]

private theorem ciSup_sum_update_add_flipSignAt {ι : Type*} {m : ℕ} (i₀ : Fin m)
    (b : ι → Fin m → ℝ) (c : ι → ℝ) (σ : Fin m → Bool) :
    let u := fun j => ∑ i ∈ Finset.univ.erase i₀, b j i * signVal (σ i)
    (⨆ j, ∑ i, (if i = i₀ then c j else b j i) * signVal (σ i)) +
        (⨆ j, ∑ i, (if i = i₀ then c j else b j i) * signVal (flipSignAt i₀ σ i)) =
      (⨆ j, (u j + c j)) + ⨆ j, (u j - c j) := by
  intro u
  have hsplit (τ : Fin m → Bool) (hτ : ∀ i ∈ Finset.univ.erase i₀, τ i = σ i) :
      (⨆ j, ∑ i, (if i = i₀ then c j else b j i) * signVal (τ i)) =
        ⨆ j, (u j + c j * signVal (τ i₀)) := by
    refine iSup_congr fun j => ?_
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i₀)]
    simp only [ite_true]
    have herase : ∑ i ∈ Finset.univ.erase i₀, (if i = i₀ then c j else b j i) * signVal (τ i) =
        u j := by
      refine Finset.sum_congr rfl fun i hi => ?_
      simp only [Finset.ne_of_mem_erase hi, ↓reduceIte, hτ i hi]
    rw [herase, add_comm]
  have hσ := hsplit σ fun _ _ => rfl
  have hflip := hsplit (flipSignAt i₀ σ) fun i hi => by
    simp only [flipSignAt, Function.update_of_ne (Finset.ne_of_mem_erase hi)]
  rw [hσ, hflip]
  simp only [flipSignAt, Function.update_self]
  cases σ i₀
  · simp only [signVal_false, Bool.not_false, signVal_true, mul_one, mul_neg, ← sub_eq_add_neg]
  · simp only [signVal_true, Bool.not_true, signVal_false, mul_neg, mul_one, ← sub_eq_add_neg]
    exact add_comm _ _

private theorem expect_ciSup_sum_update_lipschitz_le {ι : Type*} [Nonempty ι] {m : ℕ}
    (i₀ : Fin m) {b : ι → Fin m → ℝ} {Bb : ℝ} (hb : ∀ j i, |b j i| ≤ Bb)
    {x : ι → ℝ} {B : ℝ} (hx : ∀ j, |x j| ≤ B) {g : ℝ → ℝ} {K : ℝ≥0}
    (hg : LipschitzWith K g) :
    𝔼 σ : Fin m → Bool, (⨆ j, ∑ i, (if i = i₀ then g (x j) else b j i) * signVal (σ i)) ≤
      𝔼 σ : Fin m → Bool,
        (⨆ j, ∑ i, (if i = i₀ then (K : ℝ) * x j else b j i) * signVal (σ i)) := by
  set F₁ : (Fin m → Bool) → ℝ := fun σ =>
    ⨆ j, ∑ i, (if i = i₀ then g (x j) else b j i) * signVal (σ i)
  set F₂ : (Fin m → Bool) → ℝ := fun σ =>
    ⨆ j, ∑ i, (if i = i₀ then (K : ℝ) * x j else b j i) * signVal (σ i)
  have hle : ∀ σ : Fin m → Bool, F₁ σ + F₁ (flipSignAt i₀ σ) ≤ F₂ σ + F₂ (flipSignAt i₀ σ) := by
    intro σ
    dsimp only [F₁, F₂]
    rw [ciSup_sum_update_add_flipSignAt i₀ b (fun j => g (x j)) σ,
      ciSup_sum_update_add_flipSignAt i₀ b (fun j => (K : ℝ) * x j) σ]
    refine ciSup_add_ciSup_lipschitz_le (Bu := m * max Bb 0) (fun j => ?_) hx hg
    calc |∑ i ∈ Finset.univ.erase i₀, b j i * signVal (σ i)|
        ≤ ∑ i ∈ Finset.univ.erase i₀, |b j i * signVal (σ i)| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i ∈ Finset.univ.erase i₀, max Bb 0 :=
          Finset.sum_le_sum fun i _ => by
            rw [abs_mul, abs_signVal, mul_one]
            exact (hb j i).trans (le_max_left _ _)
      _ = ((Finset.univ.erase i₀).card : ℝ) * max Bb 0 := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ m * max Bb 0 := by
          gcongr
          exact_mod_cast (Finset.card_le_univ _).trans_eq (Fintype.card_fin m)
  have h2 := Finset.expect_le_expect (s := Finset.univ) fun σ _ => hle σ
  rw [← two_mul_expect_eq_expect_add_flipSignAt i₀ F₁,
    ← two_mul_expect_eq_expect_add_flipSignAt i₀ F₂] at h2
  linarith

/-! ### Vector contraction -/

/-- **Talagrand's contraction lemma** [MohriRostamizadehTalwalkar2018, Lemma 5.7]
(cf. [LedouxTalagrand1991, Theorem 4.12, pp. 112–114]): for a bounded family of vectors
`a : ι → Fin m → ℝ` and `K`-Lipschitz functions `φ i : ℝ → ℝ` (`i : Fin m`),
`rademacherAverage (fun j i => φ i (a j i)) ≤ K * rademacherAverage a`. No centering condition
`φ i 0 = 0` is needed. -/
theorem rademacherAverage_comp_le {ι : Type*} {m : ℕ} {a : ι → Fin m → ℝ} {B : ℝ}
    (ha : ∀ j i, |a j i| ≤ B) {φ : Fin m → ℝ → ℝ} {K : ℝ≥0}
    (hφ : ∀ i, LipschitzWith K (φ i)) :
    rademacherAverage (fun j i => φ i (a j i)) ≤ K * rademacherAverage a := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp only [rademacherAverage_of_isEmpty, mul_zero, le_rfl]
  let interp (k : ℕ) (j : ι) (i : Fin m) : ℝ :=
    if i.val < k then φ i (a j i) else (K : ℝ) * a j i
  let M0 : ℝ := (∑ i : Fin m, |φ i 0|) + K * max B 0
  have hinterp_bdd (k : ℕ) (j : ι) (i : Fin m) : |interp k j i| ≤ M0 := by
    dsimp only [interp, M0]
    split_ifs with hik
    · have h0 : |φ i 0| ≤ ∑ i' : Fin m, |φ i' 0| :=
        Finset.single_le_sum (f := fun i' : Fin m => |φ i' 0|) (fun _ _ => abs_nonneg _)
          (Finset.mem_univ i)
      linarith [abs_apply_le_of_lipschitzWith (hφ i) (ha j i)]
    · have hsum_nn : 0 ≤ ∑ i' : Fin m, |φ i' 0| := Finset.sum_nonneg fun _ _ => abs_nonneg _
      have hmul : |(K : ℝ) * a j i| ≤ K * max B 0 := by
        rw [abs_mul, abs_of_nonneg K.coe_nonneg]
        exact mul_le_mul_of_nonneg_left ((ha j i).trans (le_max_left _ _)) K.coe_nonneg
      linarith
  have hind : ∀ k ≤ m,
      (𝔼 σ : Fin m → Bool, ⨆ j, ∑ i, interp k j i * signVal (σ i)) ≤
        𝔼 σ : Fin m → Bool, ⨆ j, ∑ i, interp 0 j i * signVal (σ i) := by
    intro k hk
    induction k with
    | zero => exact le_rfl
    | succ k ih =>
      have hk_lt : k < m := Nat.lt_of_succ_le hk
      let i₀ : Fin m := ⟨k, hk_lt⟩
      have hstep := expect_ciSup_sum_update_lipschitz_le i₀ (hinterp_bdd k) (fun j => ha j i₀)
        (hφ i₀)
      have hlhs (j : ι) (i : Fin m) :
          interp (k + 1) j i = if i = i₀ then φ i₀ (a j i₀) else interp k j i := by
        dsimp only [interp, i₀]
        by_cases hi : i = ⟨k, hk_lt⟩
        · subst hi
          simp only [Nat.lt_succ_self, ite_true]
        · have hne : i.val ≠ k := fun hval => hi (Fin.ext hval)
          simp only [hi, ↓reduceIte]
          split_ifs <;> first | rfl | omega
      have hrhs (j : ι) (i : Fin m) :
          (if i = i₀ then (K : ℝ) * a j i₀ else interp k j i) = interp k j i := by
        by_cases hi : i = i₀
        · subst hi
          simp only [ite_true, interp, i₀, lt_self_iff_false, ite_false]
        · simp only [hi, ite_false]
      simp only [hlhs]
      exact (hstep.trans_eq (by simp only [hrhs])).trans (ih hk_lt.le)
  have hscale : rademacherAverage (interp 0) = K * rademacherAverage a := by
    have h := rademacherAverage_add_mul_signVal_mul ha (fun _ => 0) (fun _ => false) K.coe_nonneg
    simpa only [zero_add, signVal_false, one_mul, interp, Nat.not_lt_zero, ite_false] using h
  have hfull : (fun j i => φ i (a j i)) = interp m := by
    funext j i
    simp only [interp, i.isLt, ite_true]
  rw [hfull, ← hscale, rademacherAverage_eq_expect_ciSup_sum_div,
    rademacherAverage_eq_expect_ciSup_sum_div]
  exact div_le_div_of_nonneg_right (hind m le_rfl) (Nat.cast_nonneg m)

/-! ### Function-class contraction -/

/-- **Talagrand's contraction lemma for a function class**
[MohriRostamizadehTalwalkar2018, Lemma 5.7]: for a uniformly bounded class `F : Set (Z → ℝ)`, a
sample `S : Fin m → Z`, and `K`-Lipschitz maps `φ i : ℝ → ℝ`,
`rademacherAverage (fun (f : F) i => φ i (f (S i))) ≤ K * empiricalRademacherComplexity F S`. -/
theorem rademacherAverage_comp_le_empiricalRademacherComplexity {Z : Type*} {F : Set (Z → ℝ)}
    {B : ℝ} (hF : ∀ f ∈ F, ∀ z, |f z| ≤ B) {m : ℕ} (S : Fin m → Z) {φ : Fin m → ℝ → ℝ}
    {K : ℝ≥0} (hφ : ∀ i, LipschitzWith K (φ i)) :
    rademacherAverage (fun (f : F) i => φ i ((f : Z → ℝ) (S i))) ≤
      K * empiricalRademacherComplexity F S := by
  rw [empiricalRademacherComplexity_def]
  exact rademacherAverage_comp_le (fun (f : F) i => hF f.1 f.2 (S i)) hφ

/-- **Empirical Rademacher contraction under example-dependent Lipschitz maps**: if `F` is a
uniformly bounded set of functions `X → ℝ`, `g : Z → X` extracts features from examples, and
`φ z : ℝ → ℝ` is `K`-Lipschitz for every `z : Z`, then on any sample `S : Fin m → Z` the induced
class `{(z ↦ φ z (f (g z))) | f ∈ F}` has empirical Rademacher complexity at most `K` times that of
`F` on `g ∘ S`. -/
theorem empiricalRademacherComplexity_image_comp_le_of_map {Z X : Type*} {F : Set (X → ℝ)}
    {B : ℝ} (hF : ∀ f ∈ F, ∀ x, |f x| ≤ B) (g : Z → X) {φ : Z → ℝ → ℝ} {K : ℝ≥0}
    (hφ : ∀ z, LipschitzWith K (φ z)) {m : ℕ} (S : Fin m → Z) :
    empiricalRademacherComplexity ((fun (f : X → ℝ) z => φ z (f (g z))) '' F) S ≤
      K * empiricalRademacherComplexity F (fun i => g (S i)) := by
  rw [empiricalRademacherComplexity_def]
  have hcomp_bdd : ∀ (f : F) (i : Fin m),
      |φ (S i) ((f : X → ℝ) (g (S i)))| ≤ (∑ i' : Fin m, |φ (S i') 0|) + K * max B 0 := by
    intro f i
    have h0 : |φ (S i) 0| ≤ ∑ i' : Fin m, |φ (S i') 0| :=
      Finset.single_le_sum (f := fun i' : Fin m => |φ (S i') 0|) (fun _ _ => abs_nonneg _)
        (Finset.mem_univ i)
    linarith [abs_apply_le_of_lipschitzWith (hφ (S i)) (hF f.1 f.2 (g (S i)))]
  refine (rademacherAverage_le_of_forall_exists hcomp_bdd ?_).trans
    (rademacherAverage_comp_le_empiricalRademacherComplexity hF (fun i => g (S i))
      fun i => hφ (S i))
  rintro ⟨_, f, hf, rfl⟩
  exact ⟨⟨f, hf⟩, rfl⟩

/-- **Empirical Rademacher contraction for `(φ ∘ ·) '' F`**
[MohriRostamizadehTalwalkar2018, Lemma 5.7]: composing a uniformly bounded class `F : Set (Z → ℝ)`
with a `K`-Lipschitz function `φ : ℝ → ℝ` multiplies its empirical Rademacher complexity by at most
`K`. -/
theorem empiricalRademacherComplexity_image_comp_le {Z : Type*} {F : Set (Z → ℝ)} {B : ℝ}
    (hF : ∀ f ∈ F, ∀ z, |f z| ≤ B) {φ : ℝ → ℝ} {K : ℝ≥0} (hφ : LipschitzWith K φ) {m : ℕ}
    (S : Fin m → Z) :
    empiricalRademacherComplexity ((φ ∘ ·) '' F) S ≤ K * empiricalRademacherComplexity F S :=
  empiricalRademacherComplexity_image_comp_le_of_map hF id (fun _ => hφ) S

/-- **Population Rademacher contraction under example-dependent Lipschitz maps**: under a
distribution `D : PMF Z` on a finite domain, the class `{(z ↦ φ z (f (g z))) | f ∈ F}` has
Rademacher complexity at most `K` times that of `F` under `D.map g`. -/
theorem rademacherComplexity_image_comp_le_of_map {Z X : Type*} [Fintype Z] [Fintype X]
    (D : PMF Z) {F : Set (X → ℝ)} {B : ℝ} (hF : ∀ f ∈ F, ∀ x, |f x| ≤ B) (g : Z → X)
    {φ : Z → ℝ → ℝ} {K : ℝ≥0} (hφ : ∀ z, LipschitzWith K (φ z)) (m : ℕ) :
    rademacherComplexity D ((fun (f : X → ℝ) z => φ z (f (g z))) '' F) m ≤
      K * rademacherComplexity (D.map g) F m := by
  rw [rademacherComplexity_def, rademacherComplexity_def, Probability.PMF.pi_map,
    Probability.PMF.sum_map_mul, Finset.mul_sum]
  refine Finset.sum_le_sum fun S _ => ?_
  rw [← mul_assoc, mul_comm (K : ℝ), mul_assoc]
  exact mul_le_mul_of_nonneg_left
    (empiricalRademacherComplexity_image_comp_le_of_map hF g hφ S) ENNReal.toReal_nonneg

/-- **Population Rademacher contraction for `(φ ∘ ·) '' F`**
[MohriRostamizadehTalwalkar2018, Lemma 5.7]: composing a uniformly bounded class `F : Set (Z → ℝ)`
with a `K`-Lipschitz function `φ : ℝ → ℝ` multiplies its Rademacher complexity under `D` by at most
`K`. -/
theorem rademacherComplexity_image_comp_le {Z : Type*} [Fintype Z] (D : PMF Z)
    {F : Set (Z → ℝ)} {B : ℝ} (hF : ∀ f ∈ F, ∀ z, |f z| ≤ B) {φ : ℝ → ℝ} {K : ℝ≥0}
    (hφ : LipschitzWith K φ) (m : ℕ) :
    rademacherComplexity D ((φ ∘ ·) '' F) m ≤ K * rademacherComplexity D F m := by
  have h := rademacherComplexity_image_comp_le_of_map D hF id (fun _ => hφ) m
  rw [PMF.map_id] at h
  exact h

end Cslib.MachineLearning
