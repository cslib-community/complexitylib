/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Cslib.MachineLearning.PACLearning.VCDimension
public import Mathlib.Analysis.SpecialFunctions.Exp
import CslibFrontier.Foundations.Combinatorics.SmallSubsets
import CslibFrontier.Foundations.Data.Nat.Choose.Sum
import CslibFrontier.Foundations.Data.Nat.Choose.Real
import CslibFrontier.MachineLearning.PACLearning.VCDimension

/-! # The growth function and Sauer's lemma

For a binary concept class `C` and points `x₀, …, x_{m-1}` of the domain, the *restriction* of `C`
to `x` is the set of labelings `(c x₀, …, c x_{m-1})` realized by concepts `c ∈ C`
[ShalevShwartzBenDavid2014, Definition 6.2]. The *growth function* `growthFunction C m` is the
largest number of such labelings over all choices of `m` points
[ShalevShwartzBenDavid2014, Definition 6.9]. Points are given as a sequence `Fin m → α`, so
repetitions are allowed; repeated points never add labelings, so for a domain with at least `m`
points this is the maximum over `m`-element subsets used by Shalev-Shwartz and Ben-David.

*Sauer's lemma* bounds the growth function of a class all of whose shattered sets have at most
`d` points by `∑_{i ≤ d} (m choose i)`, hence by `(e m / d) ^ d` for `d ≤ m` and by `(m + 1) ^ d`
[ShalevShwartzBenDavid2014, Lemma 6.10]. The combinatorial core is the Sauer–Shelah lemma for
finite set families in Mathlib (`Finset.card_le_card_shatterer`), applied to the supports of the
realized labelings.

The main bounds take the hypothesis "every shattered finite set has at most `d` points" rather
than a bound on `vcDim`, since `vcDim` is only meaningful under `HasFiniteVCDim`; the `vcDim` forms
follow (`growthFunction_le_sum_choose_vcDim`).

## Main definitions

- `restriction C x`: the labelings of the points `x : Fin m → α` realized by concepts of `C`.
- `growthFunction C m`: the maximum number of labelings of `m` points realized by `C`.

## Main results

- `growthFunction_le_two_pow`, `growthFunction_le_card`, `growthFunction_mono`: elementary bounds.
- `growthFunction_eq_two_pow_of_setShatters`: the growth function is maximal at the size of a
  shattered set.
- `growthFunction_le_sum_choose`: **Sauer's lemma**.
- `growthFunction_le_add_one_pow`, `growthFunction_le_exp_one_mul_div_pow`: polynomial forms.
- `growthFunction_le_exp_mul_pow`: the form `exp (m / T) * T ^ d`, used for sample sizes.
- `growthFunction_le_sum_choose_vcDim`: Sauer's lemma in terms of `vcDim`.

## References

* [S. Shalev-Shwartz, S. Ben-David, *Understanding Machine Learning: From Theory to
  Algorithms*][ShalevShwartzBenDavid2014]
-/

public section

open Set
open scoped Finset

namespace Cslib.MachineLearning.PACLearning

variable {α : Type*}

/-- The *restriction* of a binary concept class `C` to the points `x : Fin m → α`: the set of
labelings `i ↦ c (x i)` realized by concepts `c ∈ C` [ShalevShwartzBenDavid2014, Definition 6.2].
-/
def restriction (C : ConceptClass α Bool) {m : ℕ} (x : Fin m → α) : Set (Fin m → Bool) :=
  (fun c i => c (x i)) '' C

/-- The *growth function* of a binary concept class `C`: the largest number of labelings of `m`
points realized by concepts of `C` [ShalevShwartzBenDavid2014, Definition 6.9]. -/
noncomputable def growthFunction (C : ConceptClass α Bool) (m : ℕ) : ℕ :=
  ⨆ x : Fin m → α, (restriction C x).ncard

theorem mem_restriction {C : ConceptClass α Bool} {m : ℕ} {x : Fin m → α} {v : Fin m → Bool} :
    v ∈ restriction C x ↔ ∃ c ∈ C, ∀ i, c (x i) = v i := by
  simp only [restriction, Set.mem_image, funext_iff]

theorem restriction_mono {C C' : ConceptClass α Bool} (h : C ⊆ C') {m : ℕ} (x : Fin m → α) :
    restriction C x ⊆ restriction C' x :=
  Set.image_mono h

theorem ncard_restriction_le_two_pow (C : ConceptClass α Bool) {m : ℕ} (x : Fin m → α) :
    (restriction C x).ncard ≤ 2 ^ m := by
  calc (restriction C x).ncard ≤ (Set.univ : Set (Fin m → Bool)).ncard :=
        Set.ncard_le_ncard (Set.subset_univ _)
    _ = 2 ^ m := by simp [Set.ncard_univ]

theorem bddAbove_range_ncard_restriction (C : ConceptClass α Bool) (m : ℕ) :
    BddAbove (Set.range fun x : Fin m → α => (restriction C x).ncard) :=
  ⟨2 ^ m, by rintro _ ⟨x, rfl⟩; exact ncard_restriction_le_two_pow C x⟩

theorem ncard_restriction_le_growthFunction (C : ConceptClass α Bool) {m : ℕ}
    (x : Fin m → α) : (restriction C x).ncard ≤ growthFunction C m :=
  le_ciSup (bddAbove_range_ncard_restriction C m) x

theorem growthFunction_le {C : ConceptClass α Bool} {m n : ℕ}
    (h : ∀ x : Fin m → α, (restriction C x).ncard ≤ n) : growthFunction C m ≤ n := by
  rcases isEmpty_or_nonempty (Fin m → α) with hx | hx
  · simp [growthFunction]
  · exact ciSup_le h

theorem growthFunction_le_two_pow (C : ConceptClass α Bool) (m : ℕ) :
    growthFunction C m ≤ 2 ^ m :=
  growthFunction_le (ncard_restriction_le_two_pow C)

theorem growthFunction_mono {C C' : ConceptClass α Bool} (h : C ⊆ C') (m : ℕ) :
    growthFunction C m ≤ growthFunction C' m :=
  growthFunction_le fun x => (Set.ncard_le_ncard (restriction_mono h x) (Set.toFinite _)).trans
    (ncard_restriction_le_growthFunction C' x)

/-- A finite class realizes at most `|H|` labelings of any points. -/
theorem growthFunction_le_card (H : Finset (α → Bool)) (m : ℕ) :
    growthFunction (H : Set (α → Bool)) m ≤ H.card :=
  growthFunction_le fun _ =>
    (Set.ncard_image_le H.finite_toSet).trans (Set.ncard_coe_finset H).le

/-- If `C` shatters a finite set `W`, then the growth function attains its maximum `2 ^ |W|` at
`|W|`. -/
theorem growthFunction_eq_two_pow_of_setShatters {C : ConceptClass α Bool} {W : Finset α}
    (hW : SetShatters C ↑W) : growthFunction C W.card = 2 ^ W.card := by
  classical
  refine le_antisymm (growthFunction_le_two_pow C _) ?_
  set x : Fin W.card → α := fun i => (W.equivFin.symm i : α)
  have hx : Function.Injective x := fun i j h => W.equivFin.symm.injective (Subtype.ext h)
  have hxW : ∀ i, x i ∈ (W : Set α) := fun i => Finset.mem_coe.2 (W.equivFin.symm i).2
  have huniv : restriction C x = Set.univ := by
    refine Set.eq_univ_of_forall fun v => ?_
    obtain ⟨c, hc, hcW⟩ := hW ((Finset.univ.filter fun i => v i = true).image x : Set α)
      (by
        intro y hy
        obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hy)
        exact hxW i)
    refine mem_restriction.2 ⟨c, hc, fun i => ?_⟩
    have hmem : x i ∈ c ⁻¹' {true} ∩ ↑W ↔
        x i ∈ ((Finset.univ.filter fun i => v i = true).image x : Set α) := by
      rw [hcW]
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, Finset.coe_image,
      Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_image, Set.mem_ofPred_eq,
      hx.eq_iff, exists_eq_right] at hmem
    have := hxW i
    cases hv : v i <;> cases hci : c (x i) <;> simp_all
  calc 2 ^ W.card = (Set.univ : Set (Fin W.card → Bool)).ncard := by simp [Set.ncard_univ]
    _ = (restriction C x).ncard := by rw [huniv]
    _ ≤ growthFunction C W.card := ncard_restriction_le_growthFunction C x

/-- **Sauer's lemma** for one choice of points: if every finite set shattered by `C` has at most
`d` points, then `C` realizes at most `∑_{i ≤ d} (m choose i)` labelings of any `m` points
[ShalevShwartzBenDavid2014, Lemma 6.10]. -/
theorem ncard_restriction_le_sum_choose {C : ConceptClass α Bool} {d : ℕ}
    (hC : ∀ W : Finset α, SetShatters C ↑W → W.card ≤ d) {m : ℕ} (x : Fin m → α) :
    (restriction C x).ncard ≤ ∑ i ∈ Finset.range (d + 1), m.choose i := by
  classical
  -- Encode each realized labeling by its support, a subset of `Fin m`.
  set P : Finset (Fin m → Bool) := (restriction C x).toFinite.toFinset with hP
  set supp : (Fin m → Bool) → Finset (Fin m) := fun v => Finset.univ.filter fun i => v i = true
  have hsupp : Function.Injective supp := by
    intro v w hvw
    funext i
    have := congrArg (i ∈ ·) hvw
    simp only [supp, Finset.mem_filter, Finset.mem_univ, true_and, eq_iff_iff] at this
    cases hv : v i <;> cases hw : w i <;> simp_all
  set 𝒜 : Finset (Finset (Fin m)) := P.image supp
  have hcard : (restriction C x).ncard = #𝒜 := by
    rw [Finset.card_image_of_injective _ hsupp, hP, Set.ncard_eq_toFinset_card _ (Set.toFinite _)]
  -- A set of indices shattered by `𝒜` is mapped injectively by `x` to a set shattered by `C`.
  have hsh : ∀ s ∈ 𝒜.shatterer, #s ≤ d := by
    intro s hs
    rw [Finset.mem_shatterer] at hs
    have h𝒜 : ∀ u ∈ 𝒜, ∃ c ∈ C, ∀ i, i ∈ u ↔ c (x i) = true := by
      intro u hu
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hu
      rw [hP, Set.Finite.mem_toFinset, mem_restriction] at hv
      obtain ⟨c, hc, hcv⟩ := hv
      exact ⟨c, hc, fun i => by simp [supp, hcv]⟩
    have hinj : Set.InjOn x s := by
      intro i hi j hj hij
      obtain ⟨u, hu, hsu⟩ := hs (Finset.singleton_subset_iff.2 hi)
      obtain ⟨c, hc, hcu⟩ := h𝒜 u hu
      have hiu : i ∈ u := (Finset.mem_inter.1 (hsu.symm ▸ Finset.mem_singleton_self i)).2
      have hju : j ∈ u := (hcu j).2 (hij ▸ (hcu i).1 hiu)
      have : j ∈ s ∩ u := Finset.mem_inter.2 ⟨hj, hju⟩
      rw [hsu] at this
      exact (Finset.mem_singleton.1 this).symm
    have hW : SetShatters C ↑(s.image x) := by
      intro W' hW'
      obtain ⟨u, hu, hsu⟩ := hs (Finset.filter_subset (fun i => x i ∈ W') s)
      obtain ⟨c, hc, hcu⟩ := h𝒜 u hu
      refine ⟨c, hc, ?_⟩
      ext y
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, Finset.coe_image,
        Set.mem_image, Finset.mem_coe]
      constructor
      · rintro ⟨hcy, i, hi, rfl⟩
        have : i ∈ s ∩ u := Finset.mem_inter.2 ⟨hi, (hcu i).2 hcy⟩
        rw [hsu] at this
        exact (Finset.mem_filter.1 this).2
      · intro hy
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 (hW' hy))
        have hit : i ∈ s.filter (fun i => x i ∈ W') := Finset.mem_filter.2 ⟨hi, hy⟩
        rw [← hsu] at hit
        exact ⟨(hcu i).1 (Finset.mem_inter.1 hit).2, i, hi, rfl⟩
    calc #s = #(s.image x) := (Finset.card_image_of_injOn hinj).symm
      _ ≤ d := hC _ hW
  have hsub : 𝒜.shatterer ⊆ (Finset.univ : Finset (Finset (Fin m))).filter fun s => #s ≤ d :=
    fun s hs => Finset.mem_filter.2 ⟨Finset.mem_univ _, hsh s hs⟩
  -- Mathlib's Sauer–Shelah lemma: a family has at most as many members as shattered sets.
  calc (restriction C x).ncard = #𝒜 := hcard
    _ ≤ #𝒜.shatterer := Finset.card_le_card_shatterer 𝒜
    _ ≤ #((Finset.univ : Finset (Finset (Fin m))).filter fun s => #s ≤ d) :=
        Finset.card_le_card hsub
    _ = ∑ i ∈ Finset.range (d + 1), m.choose i := by
        rw [Finset.card_filter_card_le_eq_sum_choose, Fintype.card_fin]

/-- **Sauer's lemma** [ShalevShwartzBenDavid2014, Lemma 6.10]: if every finite set shattered by
`C` has at most `d` points, then `growthFunction C m ≤ ∑_{i ≤ d} (m choose i)`. -/
theorem growthFunction_le_sum_choose {C : ConceptClass α Bool} {d : ℕ}
    (hC : ∀ W : Finset α, SetShatters C ↑W → W.card ≤ d) (m : ℕ) :
    growthFunction C m ≤ ∑ i ∈ Finset.range (d + 1), m.choose i :=
  growthFunction_le (ncard_restriction_le_sum_choose hC)

/-- Polynomial form of Sauer's lemma: `growthFunction C m ≤ (m + 1) ^ d`. -/
theorem growthFunction_le_add_one_pow {C : ConceptClass α Bool} {d : ℕ}
    (hC : ∀ W : Finset α, SetShatters C ↑W → W.card ≤ d) (m : ℕ) :
    growthFunction C m ≤ (m + 1) ^ d :=
  (growthFunction_le_sum_choose hC m).trans (Cslib.sum_range_choose_le_add_one_pow m d)

/-- Sauer's lemma in the form `growthFunction C m ≤ (e m / d) ^ d` for `d ≤ m`
[ShalevShwartzBenDavid2014, Lemma 6.10, which states it for `m > d + 1`]. At `d = 0` both sides
are at most one. -/
theorem growthFunction_le_exp_one_mul_div_pow {C : ConceptClass α Bool} {d m : ℕ}
    (hC : ∀ W : Finset α, SetShatters C ↑W → W.card ≤ d) (hdm : d ≤ m) :
    (growthFunction C m : ℝ) ≤ (Real.exp 1 * m / d) ^ d := by
  calc (growthFunction C m : ℝ) ≤ ∑ i ∈ Finset.range (d + 1), (m.choose i : ℝ) := by
        exact_mod_cast growthFunction_le_sum_choose hC m
    _ ≤ (Real.exp 1 * m / d) ^ d := Cslib.sum_choose_le_exp_one_mul_div_pow hdm

/-- Sauer's lemma in the form `growthFunction C m ≤ exp (m / T) * T ^ d` for every real `T ≥ 1`.
Unlike `growthFunction_le_exp_one_mul_div_pow`, it needs no relation between `d` and `m`; sample
size bounds choose `T` to trade the exponential factor against the polynomial one. -/
theorem growthFunction_le_exp_mul_pow {C : ConceptClass α Bool} {d : ℕ}
    (hC : ∀ W : Finset α, SetShatters C ↑W → W.card ≤ d) (m : ℕ) {T : ℝ} (hT : 1 ≤ T) :
    (growthFunction C m : ℝ) ≤ Real.exp (m / T) * T ^ d := by
  calc (growthFunction C m : ℝ) ≤ ∑ i ∈ Finset.range (d + 1), (m.choose i : ℝ) := by
        exact_mod_cast growthFunction_le_sum_choose hC m
    _ ≤ Real.exp (m / T) * T ^ d := Cslib.sum_choose_le_exp_mul_pow m d T hT

/-- Sauer's lemma in terms of the VC dimension, for a class of finite VC dimension. -/
theorem growthFunction_le_sum_choose_vcDim {C : ConceptClass α Bool} (hC : HasFiniteVCDim C)
    (m : ℕ) : growthFunction C m ≤ ∑ i ∈ Finset.range (vcDim C + 1), m.choose i :=
  growthFunction_le_sum_choose (fun _ hW => hW.card_le_vcDim hC) m

end Cslib.MachineLearning.PACLearning
