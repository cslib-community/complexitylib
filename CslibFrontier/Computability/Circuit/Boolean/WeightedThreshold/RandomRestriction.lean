/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.WeightedThreshold.LTF
public import CslibFrontier.Foundations.Combinatorics.LittlewoodOfford

/-!
# Random restriction lemmas for linear threshold functions

This module formalizes the repaired Kane–Williams gate and wire random restriction lemmas for
linear threshold functions ([KaneWilliams2016], `arXiv:1511.07860v1`, Lemma 1.1 and Lemma 3.1;
Milestone 3 of [#2347](https://github.com/cslib-community/cslib-frontier/issues/2347)).

Given a linear threshold function `ltfEval a θ w = decide (θ ≤ ∑ i, a i * (w i).toNat)` on
`ι → Bool` with nonzero weight support `S = ltfSupport a` and a live set `B : Finset ι`:

* `ForcedToConst f B w` holds when fixing all coordinates outside `B` to `w` makes `f` constant on
  completions `u` on `B`.
* `ForcedToAtMostOne f B w` holds when fixing all coordinates outside `B` to `w` makes `f` depend
  on at most one live coordinate `i₀ ∈ B` (equivalently, constant or a literal `u i₀` / `!(u i₀)`).
* `card_not_forcedToConst_ltfEval_le`: for any fixed `B`, the fraction of `w : ι → Bool` not
  forcing `ltfEval a θ` to a constant outside `B` is at most
  `2 * ∑ i ∈ B ∩ S, 1 / √(ltfWeightRank a i)`.
* `sum_card_not_forcedToConst_ltfEval_le` (**Gate Random Restriction Lemma**, Lemma 1.1): averaging
  over `B : Ω → Finset ι` with singleton survival probability `≤ p` on `S` gives non-forcing
  probability at most `4 * p * √(#S)`.
* `sum_card_not_forcedToAtMostOne_ltfEval_le` (**Wire Random Restriction Lemma**, Lemma 3.1):
  averaging over `B : Ω → Finset ι` with singleton survival `≤ p` and distinct-pair survival
  `≤ p ^ 2` on `S` gives probability at most `4 * #S * p * √p` of not being forced to a function
  of at most one input.
* `sum_card_not_forcedToConst_blockLiveSet_le`, `sum_card_not_forcedToAtMostOne_blockLiveSet_le`:
  specializations to `blockLiveSet blockVar σ` for jointly injective `blockVar : κ → τ → ι`.

## References

* [D. M. Kane and R. Williams, *Super-Linear Gate and Super-Quadratic Wire Lower Bounds for
  Depth-Two and Depth-Three Threshold Circuits*][KaneWilliams2016]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.WeightedThreshold

open Finset Real Cslib.Combinatorics.LittlewoodOfford

/-! ### Partial-assignment completions and forcing predicates -/

/-- Replace the coordinates of `w` inside the live set `B` with `u`, keeping `w` outside `B`. -/
def restrictUpdate {ι : Type*} [DecidableEq ι] (B : Finset ι) (w u : ι → Bool) : ι → Bool :=
  fun i => if i ∈ B then u i else w i

@[simp] theorem restrictUpdate_of_mem {ι : Type*} [DecidableEq ι] {B : Finset ι} (w u : ι → Bool)
    {i : ι} (hi : i ∈ B) : restrictUpdate B w u i = u i := by simp [restrictUpdate, hi]

@[simp] theorem restrictUpdate_of_notMem {ι : Type*} [DecidableEq ι] {B : Finset ι}
    (w u : ι → Bool) {i : ι} (hi : i ∉ B) : restrictUpdate B w u i = w i := by
  simp [restrictUpdate, hi]

@[simp] theorem restrictUpdate_self {ι : Type*} [DecidableEq ι] (B : Finset ι) (w : ι → Bool) :
    restrictUpdate B w w = w := by funext i; by_cases hi : i ∈ B <;> simp [restrictUpdate, hi]

@[simp] theorem restrictUpdate_restrictUpdate_right {ι : Type*} [DecidableEq ι] (B : Finset ι)
    (w v u : ι → Bool) : restrictUpdate B w (restrictUpdate B v u) = restrictUpdate B w u := by
  funext i; by_cases hi : i ∈ B <;> simp [restrictUpdate, hi]

/-- A Boolean function `f : (ι → Bool) → Bool` is **forced to a constant** outside `B` by `w` if
all completions `restrictUpdate B w u` take the same Boolean value `c`. -/
def ForcedToConst {ι : Type*} [DecidableEq ι] (f : (ι → Bool) → Bool)
    (B : Finset ι) (w : ι → Bool) : Prop :=
  ∃ c : Bool, ∀ u : ι → Bool, f (restrictUpdate B w u) = c

/-- A Boolean function `f : (ι → Bool) → Bool` is **forced to a function of at most one input**
outside `B` by `w` if it is forced to a constant or depends on at most one coordinate `i₀ ∈ B`. -/
def ForcedToAtMostOne {ι : Type*} [DecidableEq ι] (f : (ι → Bool) → Bool)
    (B : Finset ι) (w : ι → Bool) : Prop :=
  ForcedToConst f B w ∨ ∃ i₀ ∈ B, ∀ u₁ u₂ : ι → Bool,
    u₁ i₀ = u₂ i₀ → f (restrictUpdate B w u₁) = f (restrictUpdate B w u₂)

noncomputable instance {ι : Type*} [DecidableEq ι] (f : (ι → Bool) → Bool) (B : Finset ι)
    (w : ι → Bool) : Decidable (ForcedToConst f B w) := Classical.propDecidable _

noncomputable instance {ι : Type*} [DecidableEq ι] (f : (ι → Bool) → Bool) (B : Finset ι)
    (w : ι → Bool) : Decidable (ForcedToAtMostOne f B w) := Classical.propDecidable _

/-- Being forced to a constant implies being forced to a function of at most one input. -/
theorem ForcedToConst.forcedToAtMostOne {ι : Type*} [DecidableEq ι] {f : (ι → Bool) → Bool}
    {B : Finset ι} {w : ι → Bool} (h : ForcedToConst f B w) : ForcedToAtMostOne f B w :=
  Or.inl h

/-- A restricted Boolean function depends on at most one coordinate in `B` if and only if it is
constant or equals a literal `u i₀` or `!(u i₀)` for some `i₀ ∈ B`. -/
theorem forcedToAtMostOne_iff_const_or_literal {ι : Type*} [DecidableEq ι]
    (f : (ι → Bool) → Bool) (B : Finset ι) (w : ι → Bool) :
    ForcedToAtMostOne f B w ↔
      ForcedToConst f B w ∨
        ∃ i₀ ∈ B,
          (∀ u : ι → Bool, f (restrictUpdate B w u) = u i₀) ∨
            (∀ u : ι → Bool, f (restrictUpdate B w u) = !(u i₀)) := by
  constructor
  · rintro (hconst | ⟨i₀, hi₀, hdep⟩)
    · exact Or.inl hconst
    · have h0 (u : ι → Bool) (hu : u i₀ = false) := hdep u (fun _ => false) hu
      have h1 (u : ι → Bool) (hu : u i₀ = true) := hdep u (fun _ => true) hu
      cases hb₀ : f (restrictUpdate B w (fun _ => false)) <;>
        cases hb₁ : f (restrictUpdate B w (fun _ => true))
      · exact Or.inl ⟨false, fun u => by
          cases hu : u i₀ <;> [exact (h0 u hu).trans hb₀; exact (h1 u hu).trans hb₁]⟩
      · exact Or.inr ⟨i₀, hi₀, Or.inl fun u => by
          cases hu : u i₀ <;> [exact (h0 u hu).trans hb₀; exact (h1 u hu).trans hb₁]⟩
      · exact Or.inr ⟨i₀, hi₀, Or.inr fun u => by
          cases hu : u i₀ <;> [exact (h0 u hu).trans hb₀; exact (h1 u hu).trans hb₁]⟩
      · exact Or.inl ⟨true, fun u => by
          cases hu : u i₀ <;> [exact (h0 u hu).trans hb₀; exact (h1 u hu).trans hb₁]⟩
  · rintro (hconst | ⟨i₀, hi₀, hlit | hneg⟩)
    · exact Or.inl hconst
    · exact Or.inr ⟨i₀, hi₀, fun u₁ u₂ hu => by rw [hlit u₁, hlit u₂, hu]⟩
    · exact Or.inr ⟨i₀, hi₀, fun u₁ u₂ hu => by rw [hneg u₁, hneg u₂, hu]⟩

/-! ### Extremal completions and forcing characterizations for linear threshold functions -/

/-- Completion on `B` minimizing `∑ i, a i * (u i).toNat` by setting `u i = decide (a i < 0)`. -/
noncomputable def ltfMinAssign {ι : Type*} [DecidableEq ι] (a : ι → ℝ) (B : Finset ι)
    (w : ι → Bool) : ι → Bool :=
  restrictUpdate B w (fun i => decide (a i < 0))

/-- Completion on `B` maximizing `∑ i, a i * (u i).toNat` by setting `u i = decide (0 ≤ a i)`. -/
noncomputable def ltfMaxAssign {ι : Type*} [DecidableEq ι] (a : ι → ℝ) (B : Finset ι)
    (w : ι → Bool) : ι → Bool :=
  restrictUpdate B w (fun i => decide (0 ≤ a i))

/-- On any completion `restrictUpdate B w u`, the linear form is bounded below by `ltfMinAssign`
and above by `ltfMaxAssign`. -/
theorem sum_ltfMinAssign_le_and_le_sum_ltfMaxAssign {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℝ) (B : Finset ι) (w u : ι → Bool) :
    (∑ i : ι, a i * (ltfMinAssign a B w i).toNat) ≤
      (∑ i : ι, a i * (restrictUpdate B w u i).toNat) ∧
    (∑ i : ι, a i * (restrictUpdate B w u i).toNat) ≤
      (∑ i : ι, a i * (ltfMaxAssign a B w i).toNat) := by
  refine ⟨sum_le_sum fun i _ => ?_, sum_le_sum fun i _ => ?_⟩
  · by_cases hi : i ∈ B
    · simp only [ltfMinAssign, restrictUpdate, hi, ↓reduceIte]
      by_cases ha : a i < 0 <;> cases u i <;> (simp [ha, not_lt.mp]; try linarith)
    · simp [ltfMinAssign, restrictUpdate, hi]
  · by_cases hi : i ∈ B
    · simp only [ltfMaxAssign, restrictUpdate, hi, ↓reduceIte]
      by_cases ha : 0 ≤ a i <;> cases u i <;> (simp [ha]; try linarith [not_le.mp ha])
    · simp [ltfMaxAssign, restrictUpdate, hi]

/-- The maximum completion sum minus the minimum completion sum on `B` equals
`∑ i ∈ B ∩ ltfSupport a, |a i|`. -/
theorem sum_ltfMaxAssign_eq_sum_ltfMinAssign_add {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℝ) (B : Finset ι) (w : ι → Bool) :
    (∑ i : ι, a i * (ltfMaxAssign a B w i).toNat) =
      (∑ i : ι, a i * (ltfMinAssign a B w i).toNat) + ∑ i ∈ B ∩ ltfSupport a, |a i| := by
  have hsupp : (∑ i ∈ B ∩ ltfSupport a, |a i|) = ∑ i : ι, if i ∈ B then |a i| else 0 := by
    rw [← sum_filter, filter_mem_eq_inter, univ_inter]
    refine sum_subset inter_subset_left fun i hiB hi => ?_
    simp only [mem_inter, mem_ltfSupport, not_and, not_ne_iff] at hi; simp [hi hiB]
  rw [hsupp, ← sum_add_distrib]
  refine sum_congr rfl fun i _ => ?_
  by_cases hi : i ∈ B
  · by_cases ha : 0 ≤ a i
    · simp [ltfMaxAssign, ltfMinAssign, restrictUpdate, hi, ha, not_lt.mpr ha, abs_of_nonneg ha]
    · simp [ltfMaxAssign, ltfMinAssign, restrictUpdate, hi, ha, not_le.mp ha,
        abs_of_neg (not_le.mp ha)]
  · simp [ltfMaxAssign, ltfMinAssign, restrictUpdate, hi]

/-- `ltfEval a θ` is not forced to a constant outside `B` at `w` if and only if its minimum
completion sum on `B` lies in the half-open interval `[θ - ∑ i ∈ B ∩ ltfSupport a, |a i|, θ)`. -/
theorem not_forcedToConst_ltfEval_iff {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℝ) (θ : ℝ) (B : Finset ι) (w : ι → Bool) :
    ¬ ForcedToConst (ltfEval a θ) B w ↔
      θ - (∑ i ∈ B ∩ ltfSupport a, |a i|) ≤ ∑ i : ι, a i * (ltfMinAssign a B w i).toNat ∧
        (∑ i : ι, a i * (ltfMinAssign a B w i).toNat) < θ := by
  have hmax_eq := sum_ltfMaxAssign_eq_sum_ltfMinAssign_add a B w
  constructor
  · intro hnot
    have hlt : (∑ i : ι, a i * (ltfMinAssign a B w i).toNat) < θ := by
      by_contra hge
      refine hnot ⟨true, fun u => ?_⟩
      simp only [ltfEval, decide_eq_true_eq]
      exact (not_lt.mp hge).trans (sum_ltfMinAssign_le_and_le_sum_ltfMaxAssign a B w u).1
    have hge : θ ≤ ∑ i : ι, a i * (ltfMaxAssign a B w i).toNat := by
      by_contra hlt'
      refine hnot ⟨false, fun u => ?_⟩
      simp only [ltfEval, decide_eq_false_iff_not, not_le]
      exact (sum_ltfMinAssign_le_and_le_sum_ltfMaxAssign a B w u).2.trans_lt (not_le.mp hlt')
    exact ⟨by linarith, hlt⟩
  · rintro ⟨hlow, hhigh⟩ ⟨c, hc⟩
    have hmin : ltfEval a θ (ltfMinAssign a B w) = false := by
      simp only [ltfEval, decide_eq_false_iff_not, not_le]; exact hhigh
    have hmax : ltfEval a θ (ltfMaxAssign a B w) = true := by
      simp only [ltfEval, decide_eq_true_eq]; linarith
    have hc_min : ltfEval a θ (ltfMinAssign a B w) = c := hc (fun i => decide (a i < 0))
    have hc_max : ltfEval a θ (ltfMaxAssign a B w) = c := hc (fun i => decide (0 ≤ a i))
    rw [hmin] at hc_min; rw [hmax, ← hc_min] at hc_max
    exact Bool.false_ne_true hc_max.symm

/-- If `B` contains at most one coordinate of `ltfSupport a`, then `ltfEval a θ` is forced to a
function of at most one input outside `B` at every `w`. -/
theorem forcedToAtMostOne_ltfEval_of_card_inter_le_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℝ) (θ : ℝ) (B : Finset ι) (hcard : #(B ∩ ltfSupport a) ≤ 1) (w : ι → Bool) :
    ForcedToAtMostOne (ltfEval a θ) B w := by
  rcases (B ∩ ltfSupport a).eq_empty_or_nonempty with hempty | ⟨i₀, hi₀⟩
  · refine Or.inl ⟨ltfEval a θ w, fun u => ?_⟩
    simp only [ltfEval]; congr 2; refine sum_congr rfl fun i _ => ?_
    by_cases hiB : i ∈ B
    · have hi0 : a i = 0 := by
        by_contra hne
        have : i ∈ B ∩ ltfSupport a := mem_inter.mpr ⟨hiB, (mem_ltfSupport a i).mpr hne⟩
        rw [hempty] at this; exact notMem_empty i this
      simp [hi0]
    · simp [restrictUpdate, hiB]
  · refine Or.inr ⟨i₀, (mem_inter.mp hi₀).1, fun u₁ u₂ hu => ?_⟩
    simp only [ltfEval]; congr 2; refine sum_congr rfl fun i _ => ?_
    by_cases hiB : i ∈ B
    · by_cases hii₀ : i = i₀
      · subst hii₀; simp [restrictUpdate, hiB, hu]
      · have hi0 : a i = 0 := by
          by_contra hne
          have hi_mem : i ∈ B ∩ ltfSupport a := mem_inter.mpr ⟨hiB, (mem_ltfSupport a i).mpr hne⟩
          have := one_lt_card.mpr ⟨i, hi_mem, i₀, hi₀, hii₀⟩; omega
        simp [hi0]
    · simp [restrictUpdate, hiB]

/-- If `ltfEval a θ` is not forced to a function of at most one input outside `B` at `w`, then
`2 ≤ #(B ∩ ltfSupport a)` and `ltfEval a θ` is not forced to a constant outside `B` at `w`. -/
theorem not_forcedToAtMostOne_ltfEval_imp {ι : Type*} [Fintype ι] [DecidableEq ι]
    {a : ι → ℝ} {θ : ℝ} {B : Finset ι} {w : ι → Bool}
    (h : ¬ ForcedToAtMostOne (ltfEval a θ) B w) :
    2 ≤ #(B ∩ ltfSupport a) ∧ ¬ ForcedToConst (ltfEval a θ) B w := by
  refine ⟨?_, fun hconst => h (Or.inl hconst)⟩
  by_contra hlt
  exact h (forcedToAtMostOne_ltfEval_of_card_inter_le_one a θ B (by omega) w)

/-! ### Fixed-`B` LTF restriction bound (repaired Kane–Williams Equation `RestrictToBEqn`) -/

/-- **Fixed-`B` LTF non-forcing bound** (repaired Equation `(RestrictToBEqn)` of Kane–Williams,
`arXiv:1511.07860v1`): for any linear threshold function `ltfEval a θ` and any live set
`B : Finset ι`,
`(#{w : ι → Bool | ¬ ForcedToConst (ltfEval a θ) B w} : ℝ) ≤
  (2 : ℝ) ^ Fintype.card ι * (2 * ∑ i ∈ B ∩ ltfSupport a, 1 / Real.sqrt (ltfWeightRank a i))`. -/
theorem card_not_forcedToConst_ltfEval_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℝ) (θ : ℝ) (B : Finset ι) :
    (#{w : ι → Bool | ¬ ForcedToConst (ltfEval a θ) B w} : ℝ) ≤
      (2 : ℝ) ^ Fintype.card ι *
        (2 * ∑ i ∈ B ∩ ltfSupport a, (1 : ℝ) / Real.sqrt (ltfWeightRank a i)) := by
  classical
  let S := ltfSupport a
  let k' (i : ι) : ℕ := #{j ∈ S \ B | |a i| ≤ |a j|}
  let kB (i : ι) : ℕ := #{j ∈ B ∩ S | |a i| ≤ |a j|}
  let minSum (w : ι → Bool) : ℝ := ∑ j : ι, a j * (ltfMinAssign a B w j).toNat
  have hk_split (i : ι) : ltfWeightRank a i = kB i + k' i := by
    have h1 : {j ∈ B ∩ S | |a i| ≤ |a j|} = ({j ∈ S | |a i| ≤ |a j|}).filter (· ∈ B) := by
      ext j; simp [and_left_comm, and_comm]
    have h2 : {j ∈ S \ B | |a i| ≤ |a j|} = ({j ∈ S | |a i| ≤ |a j|}).filter (· ∉ B) := by
      ext j; simp [and_left_comm, and_comm]
    dsimp only [ltfWeightRank, S, kB, k']; rw [h1, h2, card_filter_add_card_filter_not]
  by_cases hcase : ∀ i ∈ B ∩ S, ltfWeightRank a i ≤ 2 * (k' i + 1)
  · let aOut : ι → ℝ := fun j => if j ∈ B then 0 else a j
    let cB : ℝ := ∑ j : ι, if j ∈ B then a j * (decide (a j < 0)).toNat else 0
    have hmin_decomp (w : ι → Bool) : minSum w = cB + ∑ j : ι, aOut j * (w j).toNat := by
      dsimp only [minSum, cB, aOut, ltfMinAssign, restrictUpdate]
      rw [← sum_add_distrib]; refine sum_congr rfl fun j _ => ?_
      by_cases hj : j ∈ B <;> simp [hj]
    have hLO (i : ι) (_hi : i ∈ B ∩ S) (c : ℝ) :
        (#{w : ι → Bool | c ≤ minSum w ∧ minSum w < c + |a i|} : ℝ) ≤
          (2 : ℝ) ^ Fintype.card ι / Real.sqrt (k' i + 1) := by
      have hrewrite :
          (univ.filter fun w : ι → Bool => c ≤ minSum w ∧ minSum w < c + |a i|) =
          (univ.filter fun w : ι → Bool =>
            c - cB ≤ ∑ j : ι, aOut j * (w j).toNat ∧
              (∑ j : ι, aOut j * (w j).toNat) < (c - cB) + |a i|) := by
        ext w; simp only [mem_filter, mem_univ, true_and, hmin_decomp]
        constructor <;> intro h <;> constructor <;> linarith
      rw [hrewrite]
      refine card_filter_sum_bool_Ico_le_two_pow_div_sqrt aOut
        ({j ∈ S \ B | |a i| ≤ |a j|}) (c - cB) fun j hj => ?_
      simp only [mem_filter, mem_sdiff] at hj; dsimp only [aOut]; simpa [hj.1.2] using hj.2
    have hunion :
        (#{w : ι → Bool | ¬ ForcedToConst (ltfEval a θ) B w} : ℝ) ≤
          ∑ i ∈ B ∩ S, (2 : ℝ) ^ Fintype.card ι / Real.sqrt (k' i + 1) := by
      have hfilter :
          (univ.filter fun w : ι → Bool => ¬ ForcedToConst (ltfEval a θ) B w) =
            (univ.filter fun w : ι → Bool =>
              θ - (∑ i ∈ B ∩ S, |a i|) ≤ minSum w ∧ minSum w < θ) := by
        ext w; simp [S, minSum, not_forcedToConst_ltfEval_iff]
      rw [hfilter]
      exact card_filter_Ico_sum_le minSum (B ∩ S) (fun i => |a i|)
        (fun i => (2 : ℝ) ^ Fintype.card ι / Real.sqrt (k' i + 1)) hLO θ
    refine hunion.trans ?_
    rw [mul_sum, mul_sum]; refine sum_le_sum fun i hi => ?_
    have hki_pos : (0 : ℝ) < (ltfWeightRank a i : ℝ) :=
      Nat.cast_pos.mpr (one_le_ltfWeightRank (mem_inter.mp hi).2)
    have hsqrt_le : Real.sqrt (ltfWeightRank a i) ≤ 2 * Real.sqrt (k' i + 1) := by
      have hnat : (ltfWeightRank a i : ℝ) ≤ 2 * ((k' i : ℝ) + 1) := by exact_mod_cast hcase i hi
      have hsq := Real.sqrt_le_sqrt (show (ltfWeightRank a i : ℝ) ≤ (2 : ℝ) ^ 2 * ((k' i : ℝ) + 1)
        by linarith)
      rwa [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)] at hsq
    rw [div_eq_mul_one_div]; refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [div_le_iff₀ (by positivity), mul_assoc, one_div_mul_eq_div, ← mul_div_assoc,
      le_div_iff₀ (Real.sqrt_pos.mpr hki_pos), one_mul]
    exact hsqrt_le
  · push Not at hcase
    rcases hcase with ⟨i₀, hi₀, hgt⟩
    have hki₀_pos : 1 ≤ ltfWeightRank a i₀ := one_le_ltfWeightRank (mem_inter.mp hi₀).2
    have hkB_ge : ltfWeightRank a i₀ ≤ 2 * kB i₀ := by have := hk_split i₀; omega
    have hsum_ge : 1 ≤ 2 * ∑ j ∈ B ∩ S, (1 : ℝ) / Real.sqrt (ltfWeightRank a j) := by
      let T₀ := (B ∩ S).filter fun j => |a i₀| ≤ |a j|
      have hsum_sub :
          (∑ j ∈ T₀, (1 : ℝ) / Real.sqrt (ltfWeightRank a j)) ≤
            ∑ j ∈ B ∩ S, (1 : ℝ) / Real.sqrt (ltfWeightRank a j) :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ => by positivity
      have hterm_ge :
          (∑ _j ∈ T₀, (1 : ℝ) / Real.sqrt (ltfWeightRank a i₀)) ≤
            ∑ j ∈ T₀, (1 : ℝ) / Real.sqrt (ltfWeightRank a j) := by
        refine sum_le_sum fun j hj => ?_
        have hj_pos : (0 : ℝ) < (ltfWeightRank a j : ℝ) :=
          Nat.cast_pos.mpr (one_le_ltfWeightRank (mem_inter.mp (mem_filter.mp hj).1).2)
        exact one_div_le_one_div_of_le (Real.sqrt_pos.mpr hj_pos)
          (Real.sqrt_le_sqrt (Nat.cast_le.mpr (ltfWeightRank_le_of_abs_le a (mem_filter.mp hj).2)))
      have hconst_sum :
          (∑ _j ∈ T₀, (1 : ℝ) / Real.sqrt (ltfWeightRank a i₀)) =
            (kB i₀ : ℝ) / Real.sqrt (ltfWeightRank a i₀) := by
        rw [sum_const, nsmul_eq_mul, div_eq_mul_one_div]; ring
      have h1 : (1 : ℝ) ≤ Real.sqrt (ltfWeightRank a i₀) := by
        rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt (by exact_mod_cast hki₀_pos)
      have h2 : Real.sqrt (ltfWeightRank a i₀) ≤
          2 * ((kB i₀ : ℝ) / Real.sqrt (ltfWeightRank a i₀)) := by
        rw [← mul_div_assoc, le_div_iff₀ (by positivity), Real.mul_self_sqrt (by positivity)]
        exact_mod_cast hkB_ge
      linarith
    have htriv :
        (#{w : ι → Bool | ¬ ForcedToConst (ltfEval a θ) B w} : ℝ) ≤
          (2 : ℝ) ^ Fintype.card ι * 1 := by
      rw [mul_one]
      simpa [Fintype.card_fun, Fintype.card_bool] using
        (Nat.cast_le (α := ℝ).mpr (card_filter_le univ fun w : ι → Bool =>
          ¬ ForcedToConst (ltfEval a θ) B w))
    exact htriv.trans (mul_le_mul_of_nonneg_left hsum_ge (by positivity))

/-- **Fixed-`B` LTF single-input non-forcing bound**: if `#(B ∩ ltfSupport a) < 2`, no input fails
`ForcedToAtMostOne (ltfEval a θ) B`; otherwise the non-forcing count satisfies the same bound as
`ForcedToConst`. -/
theorem card_not_forcedToAtMostOne_ltfEval_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℝ) (θ : ℝ) (B : Finset ι) :
    (#{w : ι → Bool | ¬ ForcedToAtMostOne (ltfEval a θ) B w} : ℝ) ≤
      if 2 ≤ #(B ∩ ltfSupport a) then
        (2 : ℝ) ^ Fintype.card ι *
          (2 * ∑ i ∈ B ∩ ltfSupport a, (1 : ℝ) / Real.sqrt (ltfWeightRank a i))
      else 0 := by
  classical
  split_ifs with h2
  · have hsub :
        (univ.filter fun w : ι → Bool => ¬ ForcedToAtMostOne (ltfEval a θ) B w) ⊆
          (univ.filter fun w : ι → Bool => ¬ ForcedToConst (ltfEval a θ) B w) :=
      fun _ hw => mem_filter.mpr
        ⟨mem_univ _, (not_forcedToAtMostOne_ltfEval_imp (mem_filter.mp hw).2).2⟩
    exact (Nat.cast_le.mpr (card_le_card hsub)).trans (card_not_forcedToConst_ltfEval_le a θ B)
  · rw [filter_false_of_mem (fun w _ =>
      not_not.mpr (forcedToAtMostOne_ltfEval_of_card_inter_le_one a θ B (by omega) w)),
      card_empty, Nat.cast_zero]

/-! ### Kane–Williams Gate and Wire Random Restriction Lemmas (Lemma 1.1 and Lemma 3.1) -/

/-- Shared averaging step of the gate and wire restriction lemmas. If each `ω` contributes at most
`2 ^ |ι| * 2 * ∑ i ∈ ltfSupport a, if P ω i then 1 / √(ltfWeightRank a i) else 0` and every
`i ∈ ltfSupport a` satisfies `P ω i` for at most `F` choices of `ω`, then exchanging the sums and
`sum_one_div_sqrt_card_ge_le` bound the total by `2 ^ |ι| * 2 * (F * (2 * √#(ltfSupport a)))`. -/
private theorem sum_le_of_card_filter_le {Ω ι : Type*} [Fintype Ω] [Fintype ι]
    (a : ι → ℝ) (N : Ω → ℝ) (P : Ω → ι → Prop) [∀ ω i, Decidable (P ω i)] {F : ℝ}
    (hN : ∀ ω, N ω ≤ (2 : ℝ) ^ Fintype.card ι * 2 *
      ∑ i ∈ ltfSupport a, if P ω i then (1 : ℝ) / Real.sqrt (ltfWeightRank a i) else 0)
    (hF : ∀ i ∈ ltfSupport a, (#{ω : Ω | P ω i} : ℝ) ≤ F) :
    ∑ ω, N ω ≤ (2 : ℝ) ^ Fintype.card ι * 2 * (F * (2 * Real.sqrt #(ltfSupport a))) := by
  have hfreq : (∑ i ∈ ltfSupport a, (#{ω : Ω | P ω i} : ℝ) *
      ((1 : ℝ) / Real.sqrt (ltfWeightRank a i))) ≤ F * (2 * Real.sqrt #(ltfSupport a)) := by
    rcases (ltfSupport a).eq_empty_or_nonempty with hempty | ⟨i₀, hi₀⟩
    · simp [hempty]
    refine (sum_le_sum fun i hi => mul_le_mul_of_nonneg_right (hF i hi) (by positivity)).trans ?_
    rw [← mul_sum]
    exact mul_le_mul_of_nonneg_left (sum_one_div_sqrt_card_ge_le _ a)
      ((Nat.cast_nonneg _).trans (hF i₀ hi₀))
  calc ∑ ω, N ω
      ≤ (2 : ℝ) ^ Fintype.card ι * 2 * ∑ ω : Ω, ∑ i ∈ ltfSupport a,
          if P ω i then (1 : ℝ) / Real.sqrt (ltfWeightRank a i) else 0 := by
        rw [mul_sum]; exact sum_le_sum fun ω _ => hN ω
    _ = (2 : ℝ) ^ Fintype.card ι * 2 * ∑ i ∈ ltfSupport a,
          (#{ω : Ω | P ω i} : ℝ) * ((1 : ℝ) / Real.sqrt (ltfWeightRank a i)) := by
        rw [sum_comm]; congr 1
        refine sum_congr rfl fun i _ => ?_
        rw [← sum_filter, sum_const, nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left hfreq (by positivity)

/-- **Gate Random Restriction Lemma** (Kane–Williams `arXiv:1511.07860v1`, Lemma 1.1):
for any family of live sets `B : Ω → Finset ι` such that every active coordinate
`i ∈ ltfSupport a` belongs to `B ω` for at most `p * |Ω|` choices of `ω : Ω`,
the total number of pairs `(ω, w)` where `ltfEval a θ` is not forced to a constant outside `B ω`
at `w` is at most `|Ω| * 2 ^ |ι| * (4 * p * √(#(ltfSupport a)))`. -/
theorem sum_card_not_forcedToConst_ltfEval_le {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
    (a : ι → ℝ) (θ : ℝ) (B : Ω → Finset ι) {p : ℝ}
    (hp : ∀ i ∈ ltfSupport a, (#{ω : Ω | i ∈ B ω} : ℝ) ≤ p * (Fintype.card Ω : ℝ)) :
    (∑ ω : Ω, (#{w : ι → Bool | ¬ ForcedToConst (ltfEval a θ) (B ω) w} : ℝ)) ≤
      (Fintype.card Ω : ℝ) * (2 : ℝ) ^ Fintype.card ι *
        (4 * p * Real.sqrt #(ltfSupport a)) := by
  classical
  refine (sum_le_of_card_filter_le a _ (fun ω i => i ∈ B ω) (fun ω => ?_) hp).trans_eq (by ring)
  refine (card_not_forcedToConst_ltfEval_le a θ (B ω)).trans_eq ?_
  rw [mul_assoc, ← sum_filter, filter_mem_eq_inter, inter_comm]

/-- **Wire Random Restriction Lemma** (Kane–Williams `arXiv:1511.07860v1`, Lemma 3.1):
for any family of live sets `B : Ω → Finset ι` with `0 ≤ p` such that every active coordinate
`i ∈ ltfSupport a` is live for at most `p * |Ω|` choices of `ω : Ω` and every distinct pair
`i, j ∈ ltfSupport a` (`j ≠ i`) is jointly live for at most `p ^ 2 * |Ω|` choices of `ω : Ω`,
the total number of pairs `(ω, w)` where `ltfEval a θ` is not forced to a function of at most one
input outside `B ω` at `w` is at most `|Ω| * 2 ^ |ι| * (4 * #(ltfSupport a) * p * √p)`. -/
theorem sum_card_not_forcedToAtMostOne_ltfEval_le {Ω ι : Type*} [Fintype Ω] [Fintype ι]
    [DecidableEq ι] (a : ι → ℝ) (θ : ℝ) (B : Ω → Finset ι) {p : ℝ} (hp0 : 0 ≤ p)
    (hp1 : ∀ i ∈ ltfSupport a, (#{ω : Ω | i ∈ B ω} : ℝ) ≤ p * (Fintype.card Ω : ℝ))
    (hp2 : ∀ i ∈ ltfSupport a, ∀ j ∈ (ltfSupport a).erase i,
      (#{ω : Ω | i ∈ B ω ∧ j ∈ B ω} : ℝ) ≤ p ^ 2 * (Fintype.card Ω : ℝ)) :
    (∑ ω : Ω, (#{w : ι → Bool | ¬ ForcedToAtMostOne (ltfEval a θ) (B ω) w} : ℝ)) ≤
      (Fintype.card Ω : ℝ) * (2 : ℝ) ^ Fintype.card ι *
        (4 * (#(ltfSupport a) : ℝ) * p * Real.sqrt p) := by
  classical
  have hpair_bound (i : ι) (hi : i ∈ ltfSupport a) :
      (#{ω : Ω | i ∈ B ω ∧ 2 ≤ #(B ω ∩ ltfSupport a)} : ℝ) ≤
        Real.sqrt #(ltfSupport a) * p * Real.sqrt p * (Fintype.card Ω : ℝ) := by
    set S := ltfSupport a
    have hb1 : (#{ω : Ω | i ∈ B ω ∧ 2 ≤ #(B ω ∩ S)} : ℝ) ≤ p * (Fintype.card Ω : ℝ) := by
      have hsub :
          (univ.filter fun ω : Ω => i ∈ B ω ∧ 2 ≤ #(B ω ∩ S)) ⊆
            (univ.filter fun ω : Ω => i ∈ B ω) :=
        fun _ h => mem_filter.mpr ⟨mem_univ _, (mem_filter.mp h).2.1⟩
      exact (Nat.cast_le.mpr (card_le_card hsub)).trans (hp1 i hi)
    have hb2 :
        (#{ω : Ω | i ∈ B ω ∧ 2 ≤ #(B ω ∩ S)} : ℝ) ≤
          (#S : ℝ) * p ^ 2 * (Fintype.card Ω : ℝ) := by
      have hsub :
          (univ.filter fun ω : Ω => i ∈ B ω ∧ 2 ≤ #(B ω ∩ S)) ⊆
            (S.erase i).biUnion fun j => univ.filter fun ω : Ω => i ∈ B ω ∧ j ∈ B ω := by
        intro ω hω
        simp only [mem_filter, mem_univ, true_and, mem_biUnion] at hω ⊢
        have hiBS : i ∈ B ω ∩ S := mem_inter.mpr ⟨hω.1, hi⟩
        have hpos : 0 < #((B ω ∩ S).erase i) := by rw [card_erase_of_mem hiBS]; omega
        obtain ⟨j, hj⟩ := card_pos.mp hpos
        rw [mem_erase, mem_inter] at hj
        exact ⟨j, mem_erase.mpr ⟨hj.1, hj.2.2⟩, hω.1, hj.2.1⟩
      have hreal :
          (#{ω : Ω | i ∈ B ω ∧ 2 ≤ #(B ω ∩ S)} : ℝ) ≤
            ∑ j ∈ S.erase i, (#{ω : Ω | i ∈ B ω ∧ j ∈ B ω} : ℝ) := by
        exact_mod_cast (card_le_card hsub).trans card_biUnion_le
      refine hreal.trans ((sum_le_sum fun j hj => hp2 i hi j hj).trans ?_)
      rw [sum_const, nsmul_eq_mul, mul_assoc]
      exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr card_erase_le) (by positivity)
    have hsq :
        (#{ω : Ω | i ∈ B ω ∧ 2 ≤ #(B ω ∩ S)} : ℝ) ^ 2 ≤
          (Real.sqrt #S * p * Real.sqrt p * (Fintype.card Ω : ℝ)) ^ 2 := by
      calc (#{ω : Ω | i ∈ B ω ∧ 2 ≤ #(B ω ∩ S)} : ℝ) ^ 2
          = (#{ω : Ω | i ∈ B ω ∧ 2 ≤ #(B ω ∩ S)} : ℝ) *
              (#{ω : Ω | i ∈ B ω ∧ 2 ≤ #(B ω ∩ S)} : ℝ) := sq _
        _ ≤ (p * (Fintype.card Ω : ℝ)) * ((#S : ℝ) * p ^ 2 * (Fintype.card Ω : ℝ)) := by gcongr
        _ = (Real.sqrt #S) ^ 2 * p ^ 2 * (Real.sqrt p) ^ 2 * (Fintype.card Ω : ℝ) ^ 2 := by
            rw [Real.sq_sqrt (by positivity), Real.sq_sqrt hp0]; ring
        _ = (Real.sqrt #S * p * Real.sqrt p * (Fintype.card Ω : ℝ)) ^ 2 := by ring
    have hsqrt := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq (by positivity), Real.sqrt_sq (by positivity)] at hsqrt
  refine (sum_le_of_card_filter_le a _ (fun ω i => i ∈ B ω ∧ 2 ≤ #(B ω ∩ ltfSupport a))
    (fun ω => ?_) hpair_bound).trans_eq ?_
  · refine (card_not_forcedToAtMostOne_ltfEval_le a θ (B ω)).trans_eq ?_
    by_cases h2 : 2 ≤ #(B ω ∩ ltfSupport a)
    · simp only [h2, and_true, ↓reduceIte]
      rw [mul_assoc, ← sum_filter, filter_mem_eq_inter, inter_comm]
    · simp [h2]
  · have hS := Real.mul_self_sqrt (Nat.cast_nonneg (α := ℝ) #(ltfSupport a))
    linear_combination (4 * (2 : ℝ) ^ Fintype.card ι * p * Real.sqrt p * (Fintype.card Ω : ℝ)) * hS

/-! ### Block-partition random restriction corollaries -/

/-- **Block-partition Gate Random Restriction Lemma**: when `blockVar : κ → τ → ι` is jointly
injective across blocks and slots, averaging
`¬ ForcedToConst (ltfEval a θ) (blockLiveSet blockVar σ) w` over all choices of one live variable
per block `σ : κ → τ` and `w : ι → Bool` gives at most
`|κ → τ| * 2 ^ |ι| * (4 * (1 / |τ|) * √(#(ltfSupport a)))`. -/
theorem sum_card_not_forcedToConst_blockLiveSet_le {κ τ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype τ] [Fintype ι] [DecidableEq ι] (blockVar : κ → τ → ι)
    (hinj : ∀ j₁ t₁ j₂ t₂, blockVar j₁ t₁ = blockVar j₂ t₂ → j₁ = j₂ ∧ t₁ = t₂)
    (a : ι → ℝ) (θ : ℝ) :
    (∑ σ : κ → τ,
      (#{w : ι → Bool | ¬ ForcedToConst (ltfEval a θ) (blockLiveSet blockVar σ) w} : ℝ)) ≤
      (Fintype.card (κ → τ) : ℝ) * (2 : ℝ) ^ Fintype.card ι *
        (4 * (1 / (Fintype.card τ : ℝ)) * Real.sqrt #(ltfSupport a)) :=
  sum_card_not_forcedToConst_ltfEval_le a θ (blockLiveSet blockVar) fun i _ =>
    card_mem_blockLiveSet_le blockVar hinj i

/-- **Block-partition Wire Random Restriction Lemma**: when `blockVar : κ → τ → ι` is jointly
injective across blocks and slots, averaging
`¬ ForcedToAtMostOne (ltfEval a θ) (blockLiveSet blockVar σ) w` over all `σ : κ → τ` and
`w : ι → Bool` gives at most
`|κ → τ| * 2 ^ |ι| * (4 * #(ltfSupport a) * (1 / |τ|) * √(1 / |τ|))`. -/
theorem sum_card_not_forcedToAtMostOne_blockLiveSet_le {κ τ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype τ] [Fintype ι] [DecidableEq ι] (blockVar : κ → τ → ι)
    (hinj : ∀ j₁ t₁ j₂ t₂, blockVar j₁ t₁ = blockVar j₂ t₂ → j₁ = j₂ ∧ t₁ = t₂)
    (a : ι → ℝ) (θ : ℝ) :
    (∑ σ : κ → τ,
      (#{w : ι → Bool | ¬ ForcedToAtMostOne (ltfEval a θ) (blockLiveSet blockVar σ) w} : ℝ)) ≤
      (Fintype.card (κ → τ) : ℝ) * (2 : ℝ) ^ Fintype.card ι *
        (4 * (#(ltfSupport a) : ℝ) * (1 / (Fintype.card τ : ℝ)) *
          Real.sqrt (1 / (Fintype.card τ : ℝ))) :=
  sum_card_not_forcedToAtMostOne_ltfEval_le a θ (blockLiveSet blockVar) (by positivity)
    (fun i _ => card_mem_blockLiveSet_le blockVar hinj i)
    (fun i _ j hj => card_mem_and_mem_blockLiveSet_le blockVar hinj (ne_of_mem_erase hj).symm)

end Cslib.Circuits.Boolean.WeightedThreshold
