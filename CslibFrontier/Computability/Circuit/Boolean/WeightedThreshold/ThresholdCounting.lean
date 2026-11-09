/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.WeightedThreshold.DepthTwo
public import CslibFrontier.Computability.Circuit.Boolean.WeightedThreshold.RandomRestriction

/-!
# Counting depth-two threshold functions and restricting depth-two threshold circuits

This module formalizes the threshold-function counting bound and the depth-two circuit
random-restriction collapse used in the Kane–Williams gate and wire lower bounds for depth-two
weighted threshold circuits ([KaneWilliams2016], `arXiv:1511.07860v1`, Theorem 2.3 and Section 4):

1. **Chow moment injectivity and threshold counting (`IsThresholdOver`, `featureMoment`,
   `eq_of_isThresholdOver_of_featureMoment_eq`, `card_isThresholdOver_le`):**
   Every threshold function `f : X → Bool` over `g : ι → X → Bool` is uniquely determined among
   all Boolean functions on `X` by `#{x | f x}` and `fun j => #{x | f x ∧ g j x}`, giving at most
   `(|X| + 1) ^ (|ι| + 1)` threshold functions over `g`.
2. **Counting LTFs and depth-two threshold functions (`IsLTF`, `card_isLTF_le`,
   `IsDepthTwoWithGates`, `card_isDepthTwoWithGates_le`):**
   On `κ → Bool`, there are at most `(2 ^ |κ| + 1) ^ (|κ| + 1)` LTFs and at most
   `(2 ^ |κ| + 1) ^ ((|κ| + 2) * q + |κ| + 1)` functions in `IsDepthTwoWithGates q`.
   The original fixed-weight refinement `IsDepthTwoOverWeights` counts threshold shifts from a
   fixed finite family `W`: `card_isThresholdShift_le`, `card_isWeightShift_le`, and
   `card_isDepthTwoOverWeights_le`; it is monotone in `q` and `W`
   (`IsDepthTwoOverWeights.mono`, `IsDepthTwoOverWeights.mono_weights`) and contains the
   constants (`isDepthTwoOverWeights_const`). Its per-survivor
   description costs `O(|κ| + log (#W + 1))` bits. This refinement is not attributed to
   Kane–Williams.
3. **Depth-two circuit collapse under subcube restrictions (`embedUpdate`,
   `sum_card_filter_embedUpdate`, `isDepthTwoWithGates_eval_embedUpdate`,
   `isDepthTwoWithGates_eval_embedUpdate_const`,
   `sum_circuitUnforcedConstCount_blockLiveSet_le`,
   `sum_circuitUnforcedAtMostOneCount_blockLiveSet_le`):**
   Under any restriction fixing all inputs outside `univ.image emb` (`emb : κ → Fin n` injective),
   every depth-1 gate satisfying `ForcedToAtMostOne` collapses to an affine-linear form on `κ` and
   is absorbed into the top threshold gate.
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.WeightedThreshold

open Finset Real Cslib.Combinatorics.LittlewoodOfford

/-! ### Chow moment injectivity and threshold counting over finite feature maps -/

/-- A Boolean function `f : X → Bool` is a **threshold function over a feature family**
`g : ι → X → Bool` if `f x = ltfEval a θ (fun j => g j x)` for some `a : ι → ℝ` and `θ : ℝ`. -/
def IsThresholdOver {X ι : Type*} [Fintype ι] (g : ι → X → Bool) (f : X → Bool) : Prop :=
  ∃ (a : ι → ℝ) (θ : ℝ), ∀ x : X, f x = ltfEval a θ (fun j => g j x)

noncomputable instance {X ι : Type*} [Fintype ι] (g : ι → X → Bool) (f : X → Bool) :
    Decidable (IsThresholdOver g f) := Classical.propDecidable _

/-- The **feature moment vector** (generalized Chow parameters) of `f : X → Bool` with respect to
`g : ι → X → Bool`, recording `#{x : X | f x = true}` and
`fun j => #{x : X | f x = true ∧ g j x = true}`. -/
def featureMoment {X ι : Type*} [Fintype X] (g : ι → X → Bool) (f : X → Bool) :
    Fin (Fintype.card X + 1) × (ι → Fin (Fintype.card X + 1)) :=
  (⟨#{x : X | f x = true}, Nat.lt_succ_of_le (card_filter_le _ _)⟩,
   fun j => ⟨#{x : X | f x = true ∧ g j x = true}, Nat.lt_succ_of_le (card_filter_le _ _)⟩)

/-- **Chow moment injectivity**: if `f₁ : X → Bool` is a threshold function over `g : ι → X → Bool`
and `featureMoment g f₁ = featureMoment g f₂`, then `f₁ = f₂`. -/
theorem eq_of_isThresholdOver_of_featureMoment_eq {X ι : Type*} [Fintype X] [Fintype ι]
    (g : ι → X → Bool) {f₁ f₂ : X → Bool} (hf₁ : IsThresholdOver g f₁)
    (hm : featureMoment g f₁ = featureMoment g f₂) : f₁ = f₂ := by
  classical
  rcases hf₁ with ⟨a, θ, h₁⟩
  have hcard : #{x : X | f₁ x = true} = #{x : X | f₂ x = true} := congrArg (fun p => p.1.val) hm
  have hfeat (j : ι) :
      #{x : X | f₁ x = true ∧ g j x = true} = #{x : X | f₂ x = true ∧ g j x = true} :=
    congrArg (fun p => (p.2 j).val) hm
  let S : X → ℝ := fun x => (∑ j : ι, a j * (g j x).toNat) - θ
  have hsum_S (f : X → Bool) : (∑ x : X, ((f x).toNat : ℝ) * S x) =
      (∑ j : ι, a j * (#{x : X | f x = true ∧ g j x = true} : ℝ)) -
        θ * (#{x : X | f x = true} : ℝ) := by
    have hcount : (#{x : X | f x = true} : ℝ) = ∑ x : X, ((f x).toNat : ℝ) := by
      rw [card_filter, Nat.cast_sum]; exact sum_congr rfl fun x _ => by cases f x <;> simp
    have hcount_j (j : ι) : (#{x : X | f x = true ∧ g j x = true} : ℝ) =
        ∑ x : X, ((f x).toNat : ℝ) * ((g j x).toNat : ℝ) := by
      rw [card_filter, Nat.cast_sum]
      exact sum_congr rfl fun x _ => by cases f x <;> cases g j x <;> simp
    simp_rw [S, mul_sub, sum_sub_distrib, hcount, hcount_j, mul_sum]; rw [sum_comm]; congr 1
    · exact sum_congr rfl fun x _ => sum_congr rfl fun j _ => by ring
    · exact sum_congr rfl fun x _ => mul_comm _ _
  have hdiff_zero : (∑ x : X, (((f₁ x).toNat : ℝ) - ((f₂ x).toNat : ℝ)) * S x) = 0 := by
    simp_rw [sub_mul, sum_sub_distrib, hsum_S, hcard, hfeat, sub_self]
  have hS_nonneg {x : X} (hx : f₁ x = true) : 0 ≤ S x := by
    linarith [of_decide_eq_true ((h₁ x).symm.trans hx)]
  have hS_neg {x : X} (hx : f₁ x = false) : S x < 0 := by
    linarith [of_decide_eq_false ((h₁ x).symm.trans hx)]
  have hterm_nonneg (x : X) : 0 ≤ (((f₁ x).toNat : ℝ) - ((f₂ x).toNat : ℝ)) * S x := by
    cases hx₁ : f₁ x <;> cases hx₂ : f₂ x <;>
      [simp; exact mul_nonneg_of_nonpos_of_nonpos (by norm_num) (hS_neg hx₁).le;
       exact mul_nonneg (by norm_num) (hS_nonneg hx₁); simp]
  have hterm_zero (x : X) : (((f₁ x).toNat : ℝ) - ((f₂ x).toNat : ℝ)) * S x = 0 :=
    (sum_eq_zero_iff_of_nonneg fun y _ => hterm_nonneg y).mp hdiff_zero x (mem_univ x)
  have hsub : (univ.filter fun x : X => f₂ x = true) ⊆ univ.filter fun x : X => f₁ x = true := by
    intro x hx; rw [mem_filter] at hx ⊢; refine ⟨mem_univ x, ?_⟩
    by_contra hx₁; have hx₁' : f₁ x = false := Bool.eq_false_iff.mpr hx₁
    have htz := hterm_zero x; rw [hx₁', hx.2] at htz
    simp only [Bool.toNat_false, Bool.toNat_true, Nat.cast_zero, Nat.cast_one] at htz
    linarith [hS_neg hx₁']
  have heq_set := eq_of_subset_of_card_le hsub (by omega)
  funext x
  have hiff : f₂ x = true ↔ f₁ x = true := by simpa [mem_filter] using congrArg (x ∈ ·) heq_set
  cases hf₁x : f₁ x <;> cases hf₂x : f₂ x <;> simp_all

/-- At most `(|X| + 1) ^ (|ι| + 1)` Boolean functions `f : X → Bool` are threshold functions over
`g : ι → X → Bool`. -/
theorem card_isThresholdOver_le {X ι : Type*} [Fintype X] [DecidableEq X] [Fintype ι]
    (g : ι → X → Bool) :
    #{f : X → Bool | IsThresholdOver g f} ≤ (Fintype.card X + 1) ^ (Fintype.card ι + 1) := by
  classical
  have hinj : Set.InjOn (featureMoment g) ↑(univ.filter (IsThresholdOver g)) := fun _ hf₁ _ _ hm =>
    eq_of_isThresholdOver_of_featureMoment_eq g (mem_filter.mp (mem_coe.mp hf₁)).2 hm
  calc #{f : X → Bool | IsThresholdOver g f}
      ≤ #(univ : Finset (Fin (Fintype.card X + 1) × (ι → Fin (Fintype.card X + 1)))) :=
        card_le_card_of_injOn (featureMoment g) (fun _ _ => mem_univ _) hinj
    _ = (Fintype.card X + 1) ^ (Fintype.card ι + 1) := by
        rw [card_univ, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, pow_succ']

/-! ### Counting linear threshold functions and depth-two threshold functions -/

/-- A Boolean function `f : (κ → Bool) → Bool` is a **linear threshold function (LTF)** if
`f u = ltfEval a θ u` for some `a : κ → ℝ` and `θ : ℝ`. -/
def IsLTF {κ : Type*} [Fintype κ] (f : (κ → Bool) → Bool) : Prop :=
  ∃ (a : κ → ℝ) (θ : ℝ), ∀ u : κ → Bool, f u = ltfEval a θ u

noncomputable instance {κ : Type*} [Fintype κ] (f : (κ → Bool) → Bool) :
    Decidable (IsLTF f) := Classical.propDecidable _

/-- `IsLTF` is `IsThresholdOver` for the coordinate projections `fun j u => u j`. -/
theorem isLTF_iff_isThresholdOver {κ : Type*} [Fintype κ] (f : (κ → Bool) → Bool) :
    IsLTF f ↔ IsThresholdOver (fun (j : κ) (u : κ → Bool) => u j) f := Iff.rfl

/-- Every constant Boolean function is a linear threshold function. -/
theorem isLTF_const {κ : Type*} [Fintype κ] (c : Bool) : IsLTF (fun _ : κ → Bool => c) := by
  cases c <;> [exact ⟨0, 1, fun _ => by simp [ltfEval]⟩; exact ⟨0, 0, fun _ => by simp [ltfEval]⟩]

/-- There are at most `(2 ^ |κ| + 1) ^ (|κ| + 1)` linear threshold functions on `κ → Bool`. -/
theorem card_isLTF_le {κ : Type*} [Fintype κ] [DecidableEq κ] :
    #{f : (κ → Bool) → Bool | IsLTF f} ≤ (2 ^ Fintype.card κ + 1) ^ (Fintype.card κ + 1) := by
  have hfilter : (univ.filter IsLTF) =
      univ.filter (IsThresholdOver (fun (j : κ) (u : κ → Bool) => u j)) := by
    ext f; simp [isLTF_iff_isThresholdOver]
  rw [hfilter]; simpa only [Fintype.card_fun, Fintype.card_bool] using
    card_isThresholdOver_le (fun (j : κ) (u : κ → Bool) => u j)

/-- Combined feature map `Fin q ⊕ κ → (κ → Bool) → Bool` consisting of `q` bottom functions
`g : Fin q → (κ → Bool) → Bool` together with the `|κ|` direct coordinate projections. -/
def depthTwoFeatures {κ : Type*} (q : ℕ) (g : Fin q → (κ → Bool) → Bool) :
    Fin q ⊕ κ → (κ → Bool) → Bool := Sum.elim g (fun j u => u j)

/-- A Boolean function `f : (κ → Bool) → Bool` belongs to `IsDepthTwoWithGates q` if it is a
threshold function over `q` bottom LTFs `g : Fin q → (κ → Bool) → Bool` and the `|κ|` direct input
coordinates. -/
def IsDepthTwoWithGates {κ : Type*} [Fintype κ] (q : ℕ) (f : (κ → Bool) → Bool) : Prop :=
  ∃ g : Fin q → (κ → Bool) → Bool,
    (∀ r : Fin q, IsLTF (g r)) ∧ IsThresholdOver (depthTwoFeatures q g) f

noncomputable instance {κ : Type*} [Fintype κ] (q : ℕ) (f : (κ → Bool) → Bool) :
    Decidable (IsDepthTwoWithGates q f) := Classical.propDecidable _

/-- Pad `q₁` bottom features to `q₂` features with constant-`false` features. -/
def padFeatures {κ : Type*} {q₁ q₂ : ℕ} (g : Fin q₁ → (κ → Bool) → Bool) :
    Fin q₂ → (κ → Bool) → Bool :=
  fun r => if h : r.val < q₁ then g ⟨r.val, h⟩ else fun _ => false

/-- Every padded feature is an original feature or the constant `false` feature. -/
theorem padFeatures_eq {κ : Type*} {q₁ q₂ : ℕ} (g : Fin q₁ → (κ → Bool) → Bool) (r : Fin q₂) :
    (∃ r' : Fin q₁, padFeatures g r = g r') ∨ padFeatures g r = fun _ => false := by
  unfold padFeatures; split_ifs with h <;> [exact Or.inl ⟨_, rfl⟩; exact Or.inr rfl]

/-- Padding the bottom features with constant-`false` features preserves threshold functions. -/
theorem IsThresholdOver.padFeatures {κ : Type*} [Fintype κ] {q₁ q₂ : ℕ} (hq : q₁ ≤ q₂)
    {g : Fin q₁ → (κ → Bool) → Bool} {f : (κ → Bool) → Bool}
    (hf : IsThresholdOver (depthTwoFeatures q₁ g) f) :
    IsThresholdOver (depthTwoFeatures q₂ (WeightedThreshold.padFeatures g)) f := by
  rcases hf with ⟨a, θ, ha⟩
  let a' : Fin q₂ ⊕ κ → ℝ := Sum.elim
    (fun r => if h : r.val < q₁ then a (Sum.inl ⟨r.val, h⟩) else 0) (fun j => a (Sum.inr j))
  refine ⟨a', θ, fun u => ?_⟩
  rw [ha u]; unfold ltfEval; congr 2; rw [Fintype.sum_sum_type, Fintype.sum_sum_type]; congr 1
  let emb : Fin q₁ ↪ Fin q₂ := ⟨fun r => ⟨r.val, r.isLt.trans_le hq⟩, fun r₁ r₂ h => by
    ext; exact Fin.mk.inj h⟩
  have hzero : ∀ r ∈ (univ : Finset (Fin q₂)), r ∉ map emb univ →
      a' (Sum.inl r) * (((fun j => depthTwoFeatures q₂ (WeightedThreshold.padFeatures g) j u)
        (Sum.inl r)).toNat : ℝ) = 0 := by
    intro r _ hr
    have : ¬ r.val < q₁ := fun hlt => hr (mem_map.mpr ⟨⟨r.val, hlt⟩, mem_univ _, rfl⟩)
    simp [a', this]
  rw [← sum_subset (subset_univ _) hzero, sum_map]; refine sum_congr rfl fun r _ => ?_
  have hemb : (emb r).val = r.val := rfl
  simp [a', WeightedThreshold.padFeatures, depthTwoFeatures, hemb, r.isLt]

/-- `IsDepthTwoWithGates` is monotone in the bottom gate budget `q`. -/
theorem IsDepthTwoWithGates.mono {κ : Type*} [Fintype κ] {q₁ q₂ : ℕ} (hq : q₁ ≤ q₂)
    {f : (κ → Bool) → Bool} (hf : IsDepthTwoWithGates q₁ f) : IsDepthTwoWithGates q₂ f := by
  rcases hf with ⟨g, hg, hthr⟩
  refine ⟨padFeatures g, fun r => ?_, hthr.padFeatures hq⟩
  rcases padFeatures_eq g r with ⟨r', hr'⟩ | hr' <;> rw [hr']
  exacts [hg r', isLTF_const false]

/-- **Counting depth-two threshold functions with `q` bottom LTF gates**: there are at most
`(2 ^ |κ| + 1) ^ ((|κ| + 2) * q + |κ| + 1)` functions in `IsDepthTwoWithGates q`. -/
theorem card_isDepthTwoWithGates_le {κ : Type*} [Fintype κ] [DecidableEq κ] (q : ℕ) :
    #{f : (κ → Bool) → Bool | IsDepthTwoWithGates q f} ≤
      (2 ^ Fintype.card κ + 1) ^ ((Fintype.card κ + 2) * q + Fintype.card κ + 1) := by
  let G : Finset (Fin q → (κ → Bool) → Bool) := Fintype.piFinset fun _ : Fin q => univ.filter IsLTF
  have hsub : (univ.filter fun f : (κ → Bool) → Bool => IsDepthTwoWithGates q f) ⊆
      G.biUnion fun g => univ.filter (IsThresholdOver (depthTwoFeatures q g)) := by
    intro f hf; rw [mem_filter] at hf; rcases hf.2 with ⟨g, hg, hthr⟩
    exact mem_biUnion.mpr ⟨g, Fintype.mem_piFinset.mpr fun r => mem_filter.mpr ⟨mem_univ _, hg r⟩,
      mem_filter.mpr ⟨mem_univ _, hthr⟩⟩
  have htop (g : Fin q → (κ → Bool) → Bool) :
      #{f : (κ → Bool) → Bool | IsThresholdOver (depthTwoFeatures q g) f} ≤
        (2 ^ Fintype.card κ + 1) ^ (q + Fintype.card κ + 1) := by
    simpa [Fintype.card_fun, Fintype.card_bool, Fintype.card_sum, Fintype.card_fin] using
      card_isThresholdOver_le (depthTwoFeatures q g)
  have hG : #G ≤ ((2 ^ Fintype.card κ + 1) ^ (Fintype.card κ + 1)) ^ q := by
    rw [Fintype.card_piFinset, prod_const, card_univ, Fintype.card_fin]
    exact Nat.pow_le_pow_left card_isLTF_le q
  calc #{f : (κ → Bool) → Bool | IsDepthTwoWithGates q f}
      ≤ ∑ g ∈ G, #{f : (κ → Bool) → Bool | IsThresholdOver (depthTwoFeatures q g) f} :=
        (card_le_card hsub).trans card_biUnion_le
    _ ≤ ∑ _g ∈ G, (2 ^ Fintype.card κ + 1) ^ (q + Fintype.card κ + 1) :=
        sum_le_sum fun g _ => htop g
    _ ≤ ((2 ^ Fintype.card κ + 1) ^ (Fintype.card κ + 1)) ^ q *
          (2 ^ Fintype.card κ + 1) ^ (q + Fintype.card κ + 1) := by
        rw [sum_const, smul_eq_mul]; exact Nat.mul_le_mul_right _ hG
    _ = (2 ^ Fintype.card κ + 1) ^ ((Fintype.card κ + 2) * q + Fintype.card κ + 1) := by
        rw [← pow_mul, ← pow_add]; congr 1; ring

/-! ### Threshold shifts of fixed weight vectors -/

/-- `g : (κ → Bool) → Bool` is a **threshold shift** of the weight vector `β : κ → ℝ` if
`g = ltfEval β τ` for some threshold `τ : ℝ`. -/
def IsThresholdShift {κ : Type*} [Fintype κ] (β : κ → ℝ) (g : (κ → Bool) → Bool) : Prop :=
  ∃ τ : ℝ, ∀ u : κ → Bool, g u = ltfEval β τ u

noncomputable instance {κ : Type*} [Fintype κ] (β : κ → ℝ) (g : (κ → Bool) → Bool) :
    Decidable (IsThresholdShift β g) := Classical.propDecidable _

/-- Threshold shifts of a fixed weight vector are nested, so a threshold shift is determined by the
number of its satisfying assignments. -/
theorem eq_of_isThresholdShift_of_card_eq {κ : Type*} [Fintype κ] [DecidableEq κ] {β : κ → ℝ}
    {g₁ g₂ : (κ → Bool) → Bool} (h₁ : IsThresholdShift β g₁) (h₂ : IsThresholdShift β g₂)
    (hcard : #{u : κ → Bool | g₁ u = true} = #{u : κ → Bool | g₂ u = true}) : g₁ = g₂ := by
  classical
  have key : ∀ {g g' : (κ → Bool) → Bool} {τ τ' : ℝ}, (∀ u, g u = ltfEval β τ u) →
      (∀ u, g' u = ltfEval β τ' u) → τ ≤ τ' →
      #{u : κ → Bool | g u = true} = #{u : κ → Bool | g' u = true} → g = g' := by
    intro g g' τ τ' h h' hle hc
    have hsub : (univ.filter fun u => g' u = true) ⊆ univ.filter fun u => g u = true := by
      intro u hu
      simp only [mem_filter, mem_univ, true_and, h' u, h u, ltfEval, decide_eq_true_eq] at hu ⊢
      linarith
    have heq := eq_of_subset_of_card_le hsub hc.le
    funext u
    have hu := congrArg (u ∈ ·) heq
    simp only [mem_filter, mem_univ, true_and, eq_iff_iff] at hu
    cases hgu : g u <;> cases hg'u : g' u <;> simp_all
  obtain ⟨τ₁, h₁⟩ := h₁
  obtain ⟨τ₂, h₂⟩ := h₂
  rcases le_total τ₁ τ₂ with hle | hle
  · exact key h₁ h₂ hle hcard
  · exact (key h₂ h₁ hle hcard.symm).symm

/-- A fixed weight vector `β : κ → ℝ` has at most `2 ^ |κ| + 1` threshold shifts. -/
theorem card_isThresholdShift_le {κ : Type*} [Fintype κ] [DecidableEq κ] (β : κ → ℝ) :
    #{g : (κ → Bool) → Bool | IsThresholdShift β g} ≤ 2 ^ Fintype.card κ + 1 := by
  classical
  let F : ((κ → Bool) → Bool) → Fin (2 ^ Fintype.card κ + 1) := fun g =>
    ⟨#{u : κ → Bool | g u = true}, Nat.lt_succ_of_le ((card_filter_le _ _).trans_eq (by simp))⟩
  have hinj : Set.InjOn F ↑(univ.filter (IsThresholdShift β)) := fun _ hg₁ _ hg₂ hF =>
    eq_of_isThresholdShift_of_card_eq (mem_filter.mp (mem_coe.mp hg₁)).2
      (mem_filter.mp (mem_coe.mp hg₂)).2 (congrArg Fin.val hF)
  exact (card_le_card_of_injOn F (fun _ _ => mem_univ _) hinj).trans_eq (by simp)

/-- `g : (κ → Bool) → Bool` is a **weight shift** over a finite set `W : Finset (κ → ℝ)` of weight
vectors if it is the constant `false` function or a threshold shift of some `β ∈ W`. -/
def IsWeightShift {κ : Type*} [Fintype κ] (W : Finset (κ → ℝ)) (g : (κ → Bool) → Bool) : Prop :=
  g = (fun _ => false) ∨ ∃ β ∈ W, IsThresholdShift β g

noncomputable instance {κ : Type*} [Fintype κ] (W : Finset (κ → ℝ)) (g : (κ → Bool) → Bool) :
    Decidable (IsWeightShift W g) := Classical.propDecidable _

/-- Every weight shift is a linear threshold function. -/
theorem IsWeightShift.isLTF {κ : Type*} [Fintype κ] {W : Finset (κ → ℝ)}
    {g : (κ → Bool) → Bool} (h : IsWeightShift W g) : IsLTF g := by
  rcases h with rfl | ⟨β, -, τ, hτ⟩
  exacts [isLTF_const false, ⟨β, τ, hτ⟩]

/-- There are at most `(2 ^ |κ| + 1) * min (#W + 1) ((2 ^ |κ| + 1) ^ |κ|)` weight shifts over
`W : Finset (κ → ℝ)`. -/
theorem card_isWeightShift_le {κ : Type*} [Fintype κ] [DecidableEq κ] (W : Finset (κ → ℝ)) :
    #{g : (κ → Bool) → Bool | IsWeightShift W g} ≤
      (2 ^ Fintype.card κ + 1) * min (#W + 1) ((2 ^ Fintype.card κ + 1) ^ Fintype.card κ) := by
  classical
  have hW : #{g : (κ → Bool) → Bool | IsWeightShift W g} ≤
      (2 ^ Fintype.card κ + 1) * (#W + 1) := by
    have hsub : (univ.filter fun g : (κ → Bool) → Bool => IsWeightShift W g) ⊆
        insert (fun _ => false) (W.biUnion fun β => univ.filter (IsThresholdShift β)) := by
      intro g hg
      rcases (mem_filter.mp hg).2 with rfl | ⟨β, hβ, hshift⟩
      · exact mem_insert_self _ _
      · exact mem_insert_of_mem (mem_biUnion.mpr ⟨β, hβ, mem_filter.mpr ⟨mem_univ _, hshift⟩⟩)
    refine (card_le_card hsub).trans ((card_insert_le _ _).trans ?_)
    have hbi := (card_biUnion_le (s := W) (t := fun β => univ.filter (IsThresholdShift β))).trans
      (sum_le_sum fun β _ => card_isThresholdShift_le (κ := κ) β)
    rw [sum_const, smul_eq_mul] at hbi
    have hexp : (2 ^ Fintype.card κ + 1) * (#W + 1) =
        #W * (2 ^ Fintype.card κ + 1) + (2 ^ Fintype.card κ + 1) := by ring
    have hpos : 1 ≤ 2 ^ Fintype.card κ + 1 := Nat.le_add_left _ _
    rw [hexp]; linarith
  have hLTF : #{g : (κ → Bool) → Bool | IsWeightShift W g} ≤
      (2 ^ Fintype.card κ + 1) * (2 ^ Fintype.card κ + 1) ^ Fintype.card κ := by
    rw [← pow_succ']
    exact (card_le_card fun g hg => mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hg).2.isLTF⟩).trans
      card_isLTF_le
  rcases min_choice (#W + 1) ((2 ^ Fintype.card κ + 1) ^ Fintype.card κ) with h | h <;> rw [h]
  exacts [hW, hLTF]

/-- A Boolean function `f : (κ → Bool) → Bool` belongs to `IsDepthTwoOverWeights W q` if it is a
threshold function over `q` weight shifts over `W` and the `|κ|` direct input coordinates. Unlike
`IsDepthTwoWithGates q`, the bottom weight vectors are drawn from the fixed finite set `W`; only
their thresholds are free. -/
def IsDepthTwoOverWeights {κ : Type*} [Fintype κ] (W : Finset (κ → ℝ)) (q : ℕ)
    (f : (κ → Bool) → Bool) : Prop :=
  ∃ g : Fin q → (κ → Bool) → Bool,
    (∀ r : Fin q, IsWeightShift W (g r)) ∧ IsThresholdOver (depthTwoFeatures q g) f

noncomputable instance {κ : Type*} [Fintype κ] (W : Finset (κ → ℝ)) (q : ℕ)
    (f : (κ → Bool) → Bool) : Decidable (IsDepthTwoOverWeights W q f) := Classical.propDecidable _

/-- Every function in `IsDepthTwoOverWeights W q` belongs to `IsDepthTwoWithGates q`. -/
theorem IsDepthTwoOverWeights.isDepthTwoWithGates {κ : Type*} [Fintype κ]
    {W : Finset (κ → ℝ)} {q : ℕ} {f : (κ → Bool) → Bool} (hf : IsDepthTwoOverWeights W q f) :
    IsDepthTwoWithGates q f :=
  let ⟨g, hg, hthr⟩ := hf; ⟨g, fun r => (hg r).isLTF, hthr⟩

/-- `IsDepthTwoOverWeights W` is monotone in the bottom gate budget `q`. -/
theorem IsDepthTwoOverWeights.mono {κ : Type*} [Fintype κ] {W : Finset (κ → ℝ)} {q₁ q₂ : ℕ}
    (hq : q₁ ≤ q₂) {f : (κ → Bool) → Bool} (hf : IsDepthTwoOverWeights W q₁ f) :
    IsDepthTwoOverWeights W q₂ f := by
  rcases hf with ⟨g, hg, hthr⟩
  refine ⟨padFeatures g, fun r => ?_, hthr.padFeatures hq⟩
  rcases padFeatures_eq g r with ⟨r', hr'⟩ | hr' <;> rw [hr']
  exacts [hg r', Or.inl rfl]

/-- `IsDepthTwoOverWeights W q` is monotone in the set `W` of bottom weight vectors. -/
theorem IsDepthTwoOverWeights.mono_weights {κ : Type*} [Fintype κ] {W₁ W₂ : Finset (κ → ℝ)}
    (hW : W₁ ⊆ W₂) {q : ℕ} {f : (κ → Bool) → Bool} (hf : IsDepthTwoOverWeights W₁ q f) :
    IsDepthTwoOverWeights W₂ q f := by
  rcases hf with ⟨g, hg, hthr⟩
  exact ⟨g, fun r => (hg r).imp_right fun ⟨β, hβ, hshift⟩ => ⟨β, hW hβ, hshift⟩, hthr⟩

/-- Every constant Boolean function belongs to `IsDepthTwoOverWeights W q`. -/
theorem isDepthTwoOverWeights_const {κ : Type*} [Fintype κ] (W : Finset (κ → ℝ)) (q : ℕ)
    (b : Bool) : IsDepthTwoOverWeights W q fun _ => b := by
  refine ⟨fun _ _ => false, fun _ => Or.inl rfl, 0, if b then 0 else 1, fun u => ?_⟩
  cases b <;> simp [ltfEval]

/-- **Counting depth-two threshold functions over fixed bottom weight vectors**: there are at most
`((2 ^ |κ| + 1) * min (#W + 1) ((2 ^ |κ| + 1) ^ |κ|)) ^ q * (2 ^ |κ| + 1) ^ (q + |κ| + 1)`
functions in `IsDepthTwoOverWeights W q`. Each bottom gate costs `O(|κ| + log #W)` bits, compared
with the `O(|κ| ^ 2)` bits of an arbitrary LTF in `card_isDepthTwoWithGates_le`. -/
theorem card_isDepthTwoOverWeights_le {κ : Type*} [Fintype κ] [DecidableEq κ]
    (W : Finset (κ → ℝ)) (q : ℕ) :
    #{f : (κ → Bool) → Bool | IsDepthTwoOverWeights W q f} ≤
      ((2 ^ Fintype.card κ + 1) * min (#W + 1) ((2 ^ Fintype.card κ + 1) ^ Fintype.card κ)) ^ q *
        (2 ^ Fintype.card κ + 1) ^ (q + Fintype.card κ + 1) := by
  let G : Finset (Fin q → (κ → Bool) → Bool) :=
    Fintype.piFinset fun _ : Fin q => univ.filter (IsWeightShift W)
  have hsub : (univ.filter fun f : (κ → Bool) → Bool => IsDepthTwoOverWeights W q f) ⊆
      G.biUnion fun g => univ.filter (IsThresholdOver (depthTwoFeatures q g)) := by
    intro f hf; rw [mem_filter] at hf; rcases hf.2 with ⟨g, hg, hthr⟩
    exact mem_biUnion.mpr ⟨g, Fintype.mem_piFinset.mpr fun r => mem_filter.mpr ⟨mem_univ _, hg r⟩,
      mem_filter.mpr ⟨mem_univ _, hthr⟩⟩
  have htop (g : Fin q → (κ → Bool) → Bool) :
      #{f : (κ → Bool) → Bool | IsThresholdOver (depthTwoFeatures q g) f} ≤
        (2 ^ Fintype.card κ + 1) ^ (q + Fintype.card κ + 1) := by
    simpa [Fintype.card_fun, Fintype.card_bool, Fintype.card_sum, Fintype.card_fin] using
      card_isThresholdOver_le (depthTwoFeatures q g)
  have hG : #G ≤ ((2 ^ Fintype.card κ + 1) *
      min (#W + 1) ((2 ^ Fintype.card κ + 1) ^ Fintype.card κ)) ^ q := by
    rw [Fintype.card_piFinset, prod_const, card_univ, Fintype.card_fin]
    exact Nat.pow_le_pow_left (card_isWeightShift_le W) q
  calc #{f : (κ → Bool) → Bool | IsDepthTwoOverWeights W q f}
      ≤ ∑ g ∈ G, #{f : (κ → Bool) → Bool | IsThresholdOver (depthTwoFeatures q g) f} :=
        (card_le_card hsub).trans card_biUnion_le
    _ ≤ ∑ _g ∈ G, (2 ^ Fintype.card κ + 1) ^ (q + Fintype.card κ + 1) :=
        sum_le_sum fun g _ => htop g
    _ ≤ _ := by rw [sum_const, smul_eq_mul]; exact Nat.mul_le_mul_right _ hG

/-! ### Embedded subcube completions and collapse of depth-two threshold circuits -/

/-- Lift an assignment `u : κ → Bool` along `emb : κ → ι` (`false` outside `univ.image emb`). -/
noncomputable def liftAssign {κ ι : Type*} [Fintype κ] [DecidableEq ι]
    (emb : κ → ι) (u : κ → Bool) (i : ι) : Bool :=
  if h : ∃ j : κ, emb j = i then u h.choose else false

/-- Replace the coordinates of `w : ι → Bool` inside `univ.image emb` by `u : κ → Bool`. -/
noncomputable def embedUpdate {κ ι : Type*} [Fintype κ] [DecidableEq ι]
    (emb : κ → ι) (w : ι → Bool) (u : κ → Bool) : ι → Bool :=
  restrictUpdate (univ.image emb) w (liftAssign emb u)

@[simp] theorem liftAssign_emb {κ ι : Type*} [Fintype κ] [DecidableEq ι]
    {emb : κ → ι} (hinj : Function.Injective emb) (u : κ → Bool) (j : κ) :
    liftAssign emb u (emb j) = u j := by
  have hex : ∃ j' : κ, emb j' = emb j := ⟨j, rfl⟩
  simp only [liftAssign, hex, ↓reduceDIte]; rw [hinj hex.choose_spec]

@[simp] theorem embedUpdate_emb {κ ι : Type*} [Fintype κ] [DecidableEq ι]
    {emb : κ → ι} (hinj : Function.Injective emb) (w : ι → Bool) (u : κ → Bool) (j : κ) :
    embedUpdate emb w u (emb j) = u j := by
  rw [embedUpdate, restrictUpdate_of_mem _ _ (mem_image_of_mem emb (mem_univ j)),
    liftAssign_emb hinj]

@[simp] theorem embedUpdate_of_notMem {κ ι : Type*} [Fintype κ] [DecidableEq ι]
    {emb : κ → ι} (w : ι → Bool) (u : κ → Bool) {i : ι} (hi : i ∉ univ.image emb) :
    embedUpdate emb w u i = w i := restrictUpdate_of_notMem w (liftAssign emb u) hi

/-- Involution on `(ι → Bool) × (κ → Bool)` swapping `w` on `univ.image emb` with `u`. -/
noncomputable def embedUpdateSwap {κ ι : Type*} [Fintype κ] [DecidableEq ι]
    (emb : κ → ι) (p : (ι → Bool) × (κ → Bool)) : (ι → Bool) × (κ → Bool) :=
  (embedUpdate emb p.1 p.2, fun j => p.1 (emb j))

theorem embedUpdateSwap_involutive {κ ι : Type*} [Fintype κ] [DecidableEq ι]
    {emb : κ → ι} (hinj : Function.Injective emb) :
    Function.Involutive (embedUpdateSwap emb) := fun ⟨w, u⟩ => by
  refine Prod.ext (funext fun i => ?_) (funext fun j => ?_)
  · by_cases hi : i ∈ univ.image emb
    · rcases mem_image.mp hi with ⟨j, -, rfl⟩; simp [embedUpdateSwap, embedUpdate_emb hinj]
    · simp [embedUpdateSwap, embedUpdate_of_notMem _ _ hi]
  · simp [embedUpdateSwap, embedUpdate_emb hinj]

/-- Summing `#{u : κ → Bool | P (embedUpdate emb w u)}` over all `w : ι → Bool` equals
`2 ^ |κ| * #{w : ι → Bool | P w}`. -/
theorem sum_card_filter_embedUpdate {κ ι : Type*} [Fintype κ] [DecidableEq κ] [Fintype ι]
    [DecidableEq ι] {emb : κ → ι} (hinj : Function.Injective emb) (P : (ι → Bool) → Prop)
    [DecidablePred P] : (∑ w : ι → Bool, #{u : κ → Bool | P (embedUpdate emb w u)}) =
      2 ^ Fintype.card κ * #{w : ι → Bool | P w} := by
  let e : Equiv.Perm ((ι → Bool) × (κ → Bool)) := (embedUpdateSwap_involutive hinj).toPerm
  have he (p : (ι → Bool) × (κ → Bool)) : (e p).1 = embedUpdate emb p.1 p.2 := rfl
  have hsum := Equiv.sum_comp e (fun p : (ι → Bool) × (κ → Bool) => if P p.1 then (1 : ℕ) else 0)
  have hrhs (w : ι → Bool) : (∑ _u : κ → Bool, if P w then (1 : ℕ) else 0) =
      2 ^ Fintype.card κ * (if P w then 1 else 0) := by
    rw [sum_const, card_univ, Fintype.card_fun, Fintype.card_bool, smul_eq_mul]
  simp only [he, Fintype.sum_prod_type, hrhs, ← mul_sum] at hsum
  simpa only [← card_filter] using hsum

/-- Splitting `∑ i : ι, a i * (embedUpdate emb w u i).toNat` into outside and live parts. -/
theorem sum_mul_embedUpdate {κ ι : Type*} [Fintype κ] [Fintype ι] [DecidableEq ι]
    {emb : κ → ι} (hinj : Function.Injective emb) (a : ι → ℝ) (w : ι → Bool) (u : κ → Bool) :
    (∑ i : ι, a i * (embedUpdate emb w u i).toNat) =
      (∑ i ∈ (univ.image emb)ᶜ, a i * (w i).toNat) + ∑ j : κ, a (emb j) * (u j).toNat := by
  rw [← sum_compl_add_sum (univ.image emb) fun i => a i * ((embedUpdate emb w u i).toNat : ℝ)]
  congr 1
  · refine sum_congr rfl fun i hi => ?_; rw [mem_compl] at hi; rw [embedUpdate_of_notMem w u hi]
  · rw [sum_image fun j₁ _ j₂ _ h => hinj h]
    exact sum_congr rfl fun j _ => by rw [embedUpdate_emb hinj]

/-- Any LTF `ltfEval a θ` restricted via `embedUpdate emb w` is an LTF on `κ → Bool`. -/
theorem ltfEval_embedUpdate {κ ι : Type*} [Fintype κ] [Fintype ι] [DecidableEq ι]
    {emb : κ → ι} (hinj : Function.Injective emb) (a : ι → ℝ) (θ : ℝ)
    (w : ι → Bool) (u : κ → Bool) : ltfEval a θ (embedUpdate emb w u) =
      ltfEval (fun j => a (emb j)) (θ - ∑ i ∈ (univ.image emb)ᶜ, a i * (w i).toNat) u := by
  simp only [ltfEval, sum_mul_embedUpdate hinj, sub_le_iff_le_add', add_comm]

theorem isLTF_ltfEval_embedUpdate {κ ι : Type*} [Fintype κ] [Fintype ι] [DecidableEq ι]
    {emb : κ → ι} (hinj : Function.Injective emb) (a : ι → ℝ) (θ : ℝ) (w : ι → Bool) :
    IsLTF (fun u : κ → Bool => ltfEval a θ (embedUpdate emb w u)) :=
  ⟨fun j => a (emb j), θ - ∑ i ∈ (univ.image emb)ᶜ, a i * (w i).toNat,
    ltfEval_embedUpdate hinj a θ w⟩

/-- Any Boolean function `f : (ι → Bool) → Bool` satisfying `ForcedToAtMostOne f (univ.image emb) w`
has `((f (embedUpdate emb w u)).toNat : ℝ) = c₀ + ∑ j : κ, d j * (u j).toNat`. -/
theorem exists_linear_of_forcedToAtMostOne {κ ι : Type*} [Fintype κ] [DecidableEq ι]
    {emb : κ → ι} (hinj : Function.Injective emb) {f : (ι → Bool) → Bool} {w : ι → Bool}
    (hf : ForcedToAtMostOne f (univ.image emb) w) : ∃ (c₀ : ℝ) (d : κ → ℝ), ∀ u : κ → Bool,
      ((f (embedUpdate emb w u)).toNat : ℝ) = c₀ + ∑ j : κ, d j * (u j).toNat := by
  classical
  rw [forcedToAtMostOne_iff_const_or_literal] at hf
  rcases hf with ⟨c, hc⟩ | ⟨i₀, hi₀, hlit | hneg⟩
  · refine ⟨c.toNat, 0, fun u => ?_⟩; rw [embedUpdate, hc (liftAssign emb u)]; simp
  · rcases mem_image.mp hi₀ with ⟨j₀, -, rfl⟩
    refine ⟨0, fun j => if j = j₀ then 1 else 0, fun u => ?_⟩
    rw [embedUpdate, hlit (liftAssign emb u), liftAssign_emb hinj]; simp
  · rcases mem_image.mp hi₀ with ⟨j₀, -, rfl⟩
    refine ⟨1, fun j => if j = j₀ then -1 else 0, fun u => ?_⟩
    rw [embedUpdate, hneg (liftAssign emb u), liftAssign_emb hinj]
    simp only [ite_mul, neg_one_mul, zero_mul, sum_ite_eq', mem_univ, ↓reduceIte]
    cases u j₀ <;> norm_num

/-- Predecessor gates of `top` whose depth-1 LTF is not `ForcedToConst` outside `B` by `w`. -/
noncomputable def unforcedConstGates {n g : ℕ} (p : Program signature n g) (top : Fin g)
    (B : Finset (Fin n)) (w : Fin n → Bool) : Finset (Fin g) :=
  (gateSupport p top).filter fun k =>
    ¬ ForcedToConst (ltfEval (inputWeight p k) (p.lines k).op.threshold) B w

/-- Predecessor gates of `top` whose depth-1 LTF is not `ForcedToAtMostOne` outside `B` by `w`. -/
noncomputable def unforcedAtMostOneGates {n g : ℕ} (p : Program signature n g) (top : Fin g)
    (B : Finset (Fin n)) (w : Fin n → Bool) : Finset (Fin g) :=
  (gateSupport p top).filter fun k =>
    ¬ ForcedToAtMostOne (ltfEval (inputWeight p k) (p.lines k).op.threshold) B w

/-- Number of bottom gates of a circuit output `o` not forced to a constant outside `B` by `w`. -/
noncomputable def circuitUnforcedConstCount {n : ℕ} (c : Circuit signature n 1) (o : Fin 1)
    (B : Finset (Fin n)) (w : Fin n → Bool) : ℕ :=
  match c.outputs o with | .input _ => 0 | .gate top => #(unforcedConstGates c.program top B w)

/-- Number of bottom gates of `o` not forced to a function of at most one input outside `B`. -/
noncomputable def circuitUnforcedAtMostOneCount {n : ℕ} (c : Circuit signature n 1) (o : Fin 1)
    (B : Finset (Fin n)) (w : Fin n → Bool) : ℕ :=
  match c.outputs o with | .input _ => 0 | .gate top => #(unforcedAtMostOneGates c.program top B w)

/-- `circuitUnforcedAtMostOneCount c o B w ≤ circuitUnforcedConstCount c o B w`. -/
theorem circuitUnforcedAtMostOneCount_le_circuitUnforcedConstCount {n : ℕ}
    (c : Circuit signature n 1) (o : Fin 1) (B : Finset (Fin n)) (w : Fin n → Bool) :
    circuitUnforcedAtMostOneCount c o B w ≤ circuitUnforcedConstCount c o B w := by
  unfold circuitUnforcedAtMostOneCount circuitUnforcedConstCount
  cases c.outputs o <;> [exact le_rfl; exact card_le_card fun k hk => mem_filter.mpr
    ⟨(mem_filter.mp hk).1, fun h => (mem_filter.mp hk).2 h.forcedToAtMostOne⟩]

/-- Every gate `k ∈ gateSupport p top` has depth strictly less than `p.depths top`. -/
theorem depths_lt_of_mem_gateSupport {n g : ℕ} (p : Program signature n g) {top k : Fin g}
    (hk : k ∈ gateSupport p top) : p.depths k < p.depths top := by
  rw [mem_gateSupport] at hk; unfold gateWeight lineWeight at hk
  obtain ⟨a, ha, _⟩ := exists_ne_zero_of_sum_ne_zero hk
  have hlt := p.wireDepths_lines_lt top a; rwa [(mem_filter.mp ha).2] at hlt

/-- The **live weight vectors** of a circuit output `o` along `emb : κ → Fin n`: the restrictions
`fun j => inputWeight c.program k (emb j)` of the input weight vectors of the bottom gates
`k ∈ gateSupport c.program top` read by the output gate `top` (empty if `o` is an input wire).
They depend on `emb` but not on the values of the fixed inputs. -/
noncomputable def circuitLiveWeights {κ : Type*} [Fintype κ] {n : ℕ}
    (c : Circuit signature n 1) (o : Fin 1) (emb : κ → Fin n) : Finset (κ → ℝ) :=
  match c.outputs o with
  | .input _ => ∅
  | .gate top => (gateSupport c.program top).image fun k j => inputWeight c.program k (emb j)

/-- A circuit output has at most `c.size` live weight vectors. -/
theorem card_circuitLiveWeights_le_size {κ : Type*} [Fintype κ] {n : ℕ}
    (c : Circuit signature n 1) (o : Fin 1) (emb : κ → Fin n) :
    #(circuitLiveWeights c o emb) ≤ c.size := by
  classical
  unfold circuitLiveWeights
  cases c.outputs o with
  | input _ => exact Nat.zero_le _
  | gate top => exact card_image_le.trans ((card_le_univ _).trans_eq (Fintype.card_fin _))

/-- A circuit output has at most `c.wireCount` live weight vectors: every bottom gate read by the
output gate contributes an active gate-to-gate wire. -/
theorem card_circuitLiveWeights_le_wireCount {κ : Type*} [Fintype κ] {n : ℕ}
    (c : Circuit signature n 1) (o : Fin 1) (emb : κ → Fin n) :
    #(circuitLiveWeights c o emb) ≤ c.wireCount := by
  classical
  unfold circuitLiveWeights
  cases c.outputs o with
  | input _ => exact Nat.zero_le _
  | gate top =>
    calc #((gateSupport c.program top).image fun k j => inputWeight c.program k (emb j))
        ≤ #(gateSupport c.program top) := card_image_le
      _ ≤ #(inputSupport c.program top) + #(gateSupport c.program top) := Nat.le_add_left _ _
      _ = #(lineSupport (c.program.lines top)) := (card_lineSupport_eq _ _).symm
      _ ≤ c.wireCount := single_le_sum (f := fun gate => #(lineSupport (c.program.lines gate)))
          (fun _ _ => Nat.zero_le _) (mem_univ top)

/-- **Depth-Two Circuit Restriction Collapse over Fixed Weights**: for any weighted threshold
circuit `c : Circuit signature n 1` of depth at most `2` and any injective live-variable embedding
`emb : κ → Fin n`, restricting `c` outside `univ.image emb` to `w` produces a function in
`IsDepthTwoOverWeights (circuitLiveWeights c o emb) (circuitUnforcedAtMostOneCount c o
(univ.image emb) w)`. The surviving bottom gates keep their weights on the live coordinates; only
their thresholds depend on `w`. -/
theorem isDepthTwoOverWeights_eval_embedUpdate {κ : Type*} [Fintype κ]
    {n : ℕ} (c : Circuit signature n 1) (hd : c.depth ≤ 2) (o : Fin 1)
    {emb : κ → Fin n} (hinj : Function.Injective emb) (w : Fin n → Bool) :
    IsDepthTwoOverWeights (circuitLiveWeights c o emb)
      (circuitUnforcedAtMostOneCount c o (univ.image emb) w)
      (fun u : κ → Bool => c.eval interpretation (embedUpdate emb w u) o) := by
  classical
  have hout_le : c.outputDepths o ≤ 2 := (c.outputDepths_le_depth o).trans hd
  unfold circuitUnforcedAtMostOneCount circuitLiveWeights
  cases hout : c.outputs o with
  | input i₀ =>
    dsimp only
    have hval (x : Fin n → Bool) :
        c.eval interpretation x o = ltfEval (fun i : Fin n => if i = i₀ then 1 else 0) 1 x := by
      simp only [Circuit.eval, Function.comp_apply, hout, Program.trace, Wire.elim_input, ltfEval,
        ite_mul, one_mul, zero_mul, sum_ite_eq', mem_univ, ↓reduceIte]
      cases x i₀ <;> simp
    refine ⟨Fin.elim0, fun r => r.elim0, Sum.elim Fin.elim0 (fun j => if emb j = i₀ then 1 else 0),
      1 - ∑ i ∈ (univ.image emb)ᶜ, (if i = i₀ then (1 : ℝ) else 0) * (w i).toNat, fun u => ?_⟩
    dsimp only; rw [hval, ltfEval_embedUpdate hinj]
    unfold ltfEval depthTwoFeatures; congr 2; simp [Fintype.sum_sum_type]
  | gate top =>
    dsimp only
    have htop_depth : c.program.depths top ≤ 2 := by
      simpa [Circuit.outputDepths, hout] using hout_le
    set U := unforcedAtMostOneGates c.program top (univ.image emb) w
    set F := (gateSupport c.program top).filter fun k =>
      ForcedToAtMostOne (ltfEval (inputWeight c.program k) (c.program.lines k).op.threshold)
        (univ.image emb) w
    let ev (k : Fin c.size) (u : κ → Bool) : ℝ :=
      ((c.program.eval interpretation (embedUpdate emb w u) k).toNat : ℝ)
    have hk_ltf (k : Fin c.size) (hk : k ∈ gateSupport c.program top) (x : Fin n → Bool) :
        c.program.eval interpretation x k =
          ltfEval (inputWeight c.program k) (c.program.lines k).op.threshold x := by
      have hlt := depths_lt_of_mem_gateSupport c.program hk
      exact eval_eq_ltfEval_inputWeight_of_depths_le_one c.program x (by omega)
    have hlin (k : Fin c.size) : ∃ (c₀ : ℝ) (d : κ → ℝ), k ∈ F → ∀ u : κ → Bool,
        ev k u = c₀ + ∑ j : κ, d j * (u j).toNat := by
      by_cases hkF : k ∈ F
      · obtain ⟨c₀, d, hcd⟩ := exists_linear_of_forcedToAtMostOne hinj (mem_filter.mp hkF).2
        exact ⟨c₀, d, fun _ u => by dsimp only [ev]; rw [hk_ltf k (mem_filter.mp hkF).1, hcd u]⟩
      · exact ⟨0, 0, fun h => (hkF h).elim⟩
    choose c₀ d hcd using hlin
    let eU : Fin #U ≃ U := Fintype.equivOfCardEq (by simp)
    let g : Fin #U → (κ → Bool) → Bool := fun r u =>
      ltfEval (inputWeight c.program (eU r).1) (c.program.lines (eU r).1).op.threshold
        (embedUpdate emb w u)
    let a : Fin #U ⊕ κ → ℝ := Sum.elim (fun r => gateWeight c.program top (eU r).1)
      (fun j => inputWeight c.program top (emb j) + ∑ k ∈ F, gateWeight c.program top k * d k j)
    let θ : ℝ := (c.program.lines top).op.threshold -
      ((∑ i ∈ (univ.image emb)ᶜ, inputWeight c.program top i * (w i).toNat) +
        ∑ k ∈ F, gateWeight c.program top k * c₀ k)
    refine ⟨g, fun r => Or.inr ⟨fun j => inputWeight c.program (eU r).1 (emb j),
      mem_image_of_mem _ (mem_filter.mp (eU r).2).1, _, ltfEval_embedUpdate hinj _ _ w⟩,
      a, θ, fun u => ?_⟩
    dsimp only; rw [Circuit.eval_of_output_eq_gate hout, eval_gate_eq, sum_mul_embedUpdate hinj]
    have hgate_split : (∑ k : Fin c.size, gateWeight c.program top k * ev k u) =
        (∑ k ∈ U, gateWeight c.program top k * ev k u) +
        ∑ k ∈ F, gateWeight c.program top k * ev k u := by
      have hsupp : (∑ k : Fin c.size, gateWeight c.program top k * ev k u) =
          ∑ k ∈ gateSupport c.program top, gateWeight c.program top k * ev k u := by
        refine (sum_subset (subset_univ _) fun k _ hk => ?_).symm
        rw [mem_gateSupport, not_not] at hk; simp [hk]
      rw [hsupp, ← sum_filter_not_add_sum_filter (gateSupport c.program top)
        (fun k => ForcedToAtMostOne
          (ltfEval (inputWeight c.program k) (c.program.lines k).op.threshold)
          (univ.image emb) w)]
      rfl
    have hU_sum : (∑ k ∈ U, gateWeight c.program top k * ev k u) =
        ∑ r : Fin #U, a (Sum.inl r) * ((depthTwoFeatures #U g (Sum.inl r) u).toNat : ℝ) := by
      rw [← sum_coe_sort U, ← eU.sum_comp]; refine sum_congr rfl fun r _ => ?_
      simp only [a, g, ev, depthTwoFeatures, Sum.elim_inl,
        hk_ltf (eU r).1 (mem_filter.mp (eU r).2).1]
    have hF_sum : (∑ k ∈ F, gateWeight c.program top k * ev k u) =
        (∑ k ∈ F, gateWeight c.program top k * c₀ k) +
          ∑ j : κ, (∑ k ∈ F, gateWeight c.program top k * d k j) * (u j).toNat := by
      calc (∑ k ∈ F, gateWeight c.program top k * ev k u)
          = ∑ k ∈ F, gateWeight c.program top k * (c₀ k + ∑ j : κ, d k j * (u j).toNat) :=
            sum_congr rfl fun k hk => by rw [hcd k hk u]
        _ = (∑ k ∈ F, gateWeight c.program top k * c₀ k) +
              ∑ k ∈ F, ∑ j : κ, gateWeight c.program top k * d k j * (u j).toNat := by
            simp_rw [mul_add, sum_add_distrib, mul_sum, mul_assoc]
        _ = (∑ k ∈ F, gateWeight c.program top k * c₀ k) +
              ∑ j : κ, (∑ k ∈ F, gateWeight c.program top k * d k j) * (u j).toNat := by
            rw [sum_comm]; congr 1; exact sum_congr rfl fun j _ => by rw [sum_mul]
    change decide ((c.program.lines top).op.threshold ≤
      ((∑ i ∈ (univ.image emb)ᶜ, inputWeight c.program top i * (w i).toNat) +
        ∑ j : κ, inputWeight c.program top (emb j) * (u j).toNat) +
        ∑ k : Fin c.size, gateWeight c.program top k * ev k u) = _
    rw [hgate_split, hU_sum, hF_sum]; unfold ltfEval; rw [Fintype.sum_sum_type]
    simp only [a, θ, depthTwoFeatures, Sum.elim_inr, add_mul, sum_add_distrib, sub_le_iff_le_add']
    exact decide_eq_decide.mpr ⟨fun h => by linarith, fun h => by linarith⟩

/-- Monotonicity corollary of `isDepthTwoOverWeights_eval_embedUpdate` using
`circuitUnforcedConstCount`. -/
theorem isDepthTwoOverWeights_eval_embedUpdate_const {κ : Type*} [Fintype κ]
    {n : ℕ} (c : Circuit signature n 1) (hd : c.depth ≤ 2) (o : Fin 1)
    {emb : κ → Fin n} (hinj : Function.Injective emb) (w : Fin n → Bool) :
    IsDepthTwoOverWeights (circuitLiveWeights c o emb)
      (circuitUnforcedConstCount c o (univ.image emb) w)
      (fun u : κ → Bool => c.eval interpretation (embedUpdate emb w u) o) := by
  classical
  exact (isDepthTwoOverWeights_eval_embedUpdate c hd o hinj w).mono
    (circuitUnforcedAtMostOneCount_le_circuitUnforcedConstCount c o (univ.image emb) w)

/-- **Depth-Two Circuit Restriction Collapse**: for any weighted threshold circuit
`c : Circuit signature n 1` of depth at most `2` and any injective live-variable embedding
`emb : κ → Fin n`, restricting `c` outside `univ.image emb` to `w` produces a function in
`IsDepthTwoWithGates (circuitUnforcedAtMostOneCount c o (univ.image emb) w)`. -/
theorem isDepthTwoWithGates_eval_embedUpdate {κ : Type*} [Fintype κ]
    {n : ℕ} (c : Circuit signature n 1) (hd : c.depth ≤ 2) (o : Fin 1)
    {emb : κ → Fin n} (hinj : Function.Injective emb) (w : Fin n → Bool) :
    IsDepthTwoWithGates (circuitUnforcedAtMostOneCount c o (univ.image emb) w)
      (fun u : κ → Bool => c.eval interpretation (embedUpdate emb w u) o) := by
  classical exact (isDepthTwoOverWeights_eval_embedUpdate c hd o hinj w).isDepthTwoWithGates

/-- Monotonicity corollary of `isDepthTwoWithGates_eval_embedUpdate` using
`circuitUnforcedConstCount`. -/
theorem isDepthTwoWithGates_eval_embedUpdate_const {κ : Type*} [Fintype κ]
    {n : ℕ} (c : Circuit signature n 1) (hd : c.depth ≤ 2) (o : Fin 1)
    {emb : κ → Fin n} (hinj : Function.Injective emb) (w : Fin n → Bool) :
    IsDepthTwoWithGates (circuitUnforcedConstCount c o (univ.image emb) w)
      (fun u : κ → Bool => c.eval interpretation (embedUpdate emb w u) o) := by
  classical exact (isDepthTwoOverWeights_eval_embedUpdate_const c hd o hinj w).isDepthTwoWithGates

/-! ### Expected unforced gate counts under block-partition random restrictions -/

/-- Averaging `circuitUnforcedConstCount c o (blockLiveSet blockVar σ) w` over all block selections
`σ : κ → τ` and assignments `w : Fin n → Bool` gives at most
`|κ → τ| * 2 ^ n * (4 * (1 / |τ|) * c.size * √n)`. -/
theorem sum_circuitUnforcedConstCount_blockLiveSet_le {κ τ : Type*}
    [Fintype κ] [DecidableEq κ] [Fintype τ] {n : ℕ}
    (c : Circuit signature n 1) (o : Fin 1) (blockVar : κ → τ → Fin n)
    (hinj : ∀ j₁ t₁ j₂ t₂, blockVar j₁ t₁ = blockVar j₂ t₂ → j₁ = j₂ ∧ t₁ = t₂) :
    (∑ σ : κ → τ, ∑ w : Fin n → Bool,
      (circuitUnforcedConstCount c o (blockLiveSet blockVar σ) w : ℝ)) ≤
      (Fintype.card (κ → τ) : ℝ) * (2 : ℝ) ^ n *
        (4 * (1 / (Fintype.card τ : ℝ)) * (c.size : ℝ) * Real.sqrt (n : ℝ)) := by
  classical
  unfold circuitUnforcedConstCount
  cases hout : c.outputs o with
  | input _ => simp only [CharP.cast_eq_zero, sum_const_zero]; positivity
  | gate top =>
    dsimp only
    have hswap : (∑ σ : κ → τ, ∑ w : Fin n → Bool,
        (#(unforcedConstGates c.program top (blockLiveSet blockVar σ) w) : ℝ)) =
        ∑ k ∈ gateSupport c.program top, ∑ σ : κ → τ, (#{w : Fin n → Bool | ¬ ForcedToConst
          (ltfEval (inputWeight c.program k) (c.program.lines k).op.threshold)
          (blockLiveSet blockVar σ) w} : ℝ) := by
      simp_rw [unforcedConstGates, ← sum_boole]
      exact (sum_congr rfl fun _ _ => sum_comm).trans sum_comm
    rw [hswap]
    have hgate (k : Fin c.size) : (∑ σ : κ → τ, (#{w : Fin n → Bool | ¬ ForcedToConst
        (ltfEval (inputWeight c.program k) (c.program.lines k).op.threshold)
        (blockLiveSet blockVar σ) w} : ℝ)) ≤ (Fintype.card (κ → τ) : ℝ) * (2 : ℝ) ^ n *
          (4 * (1 / (Fintype.card τ : ℝ)) * Real.sqrt (n : ℝ)) := by
      refine (sum_card_not_forcedToConst_blockLiveSet_le blockVar hinj _ _).trans ?_
      rw [Fintype.card_fin]
      refine mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) (by positivity)) (by positivity)
      exact_mod_cast (card_le_univ _).trans_eq (by simp)
    refine (sum_le_sum fun k _ => hgate k).trans ?_; rw [sum_const, nsmul_eq_mul]
    have hcard : (#(gateSupport c.program top) : ℝ) ≤ (c.size : ℝ) := by
      exact_mod_cast (card_le_univ _).trans_eq (by simp)
    nlinarith [(by positivity : (0 : ℝ) ≤ (Fintype.card (κ → τ) : ℝ) * (2 : ℝ) ^ n *
      (4 * (1 / (Fintype.card τ : ℝ)) * Real.sqrt (n : ℝ)))]

/-- Averaging `circuitUnforcedAtMostOneCount c o (blockLiveSet blockVar σ) w` over all block
selections `σ : κ → τ` and assignments `w : Fin n → Bool` gives at most
`|κ → τ| * 2 ^ n * (4 * c.wireCount * (1 / |τ|) * √(1 / |τ|))`. -/
theorem sum_circuitUnforcedAtMostOneCount_blockLiveSet_le {κ τ : Type*}
    [Fintype κ] [DecidableEq κ] [Fintype τ] {n : ℕ}
    (c : Circuit signature n 1) (o : Fin 1) (blockVar : κ → τ → Fin n)
    (hinj : ∀ j₁ t₁ j₂ t₂, blockVar j₁ t₁ = blockVar j₂ t₂ → j₁ = j₂ ∧ t₁ = t₂) :
    (∑ σ : κ → τ, ∑ w : Fin n → Bool,
      (circuitUnforcedAtMostOneCount c o (blockLiveSet blockVar σ) w : ℝ)) ≤
      (Fintype.card (κ → τ) : ℝ) * (2 : ℝ) ^ n * (4 * (c.wireCount : ℝ) *
        (1 / (Fintype.card τ : ℝ)) * Real.sqrt (1 / (Fintype.card τ : ℝ))) := by
  classical
  unfold circuitUnforcedAtMostOneCount
  cases hout : c.outputs o with
  | input _ => simp only [CharP.cast_eq_zero, sum_const_zero]; positivity
  | gate top =>
    dsimp only
    have hswap : (∑ σ : κ → τ, ∑ w : Fin n → Bool,
        (#(unforcedAtMostOneGates c.program top (blockLiveSet blockVar σ) w) : ℝ)) =
        ∑ k ∈ gateSupport c.program top, ∑ σ : κ → τ, (#{w : Fin n → Bool | ¬ ForcedToAtMostOne
          (ltfEval (inputWeight c.program k) (c.program.lines k).op.threshold)
          (blockLiveSet blockVar σ) w} : ℝ) := by
      simp_rw [unforcedAtMostOneGates, ← sum_boole]
      exact (sum_congr rfl fun _ _ => sum_comm).trans sum_comm
    rw [hswap]
    refine (sum_le_sum fun k _ =>
      sum_card_not_forcedToAtMostOne_blockLiveSet_le blockVar hinj _ _).trans ?_
    rw [Fintype.card_fin]
    have hwire : (∑ k ∈ gateSupport c.program top,
        (#(ltfSupport (inputWeight c.program k)) : ℝ)) ≤ (c.wireCount : ℝ) := by
      simp_rw [ltfSupport_inputWeight_eq_inputSupport]
      exact_mod_cast (sum_le_univ_sum_of_nonneg fun _ => Nat.zero_le _).trans
        c.inputWireCount_le_wireCount
    have hfactor : (∑ k ∈ gateSupport c.program top, (Fintype.card (κ → τ) : ℝ) * (2 : ℝ) ^ n *
        (4 * (#(ltfSupport (inputWeight c.program k)) : ℝ) *
          (1 / (Fintype.card τ : ℝ)) * Real.sqrt (1 / (Fintype.card τ : ℝ)))) =
        (Fintype.card (κ → τ) : ℝ) * (2 : ℝ) ^ n *
          (4 * (1 / (Fintype.card τ : ℝ)) * Real.sqrt (1 / (Fintype.card τ : ℝ))) *
          ∑ k ∈ gateSupport c.program top, (#(ltfSupport (inputWeight c.program k)) : ℝ) := by
      rw [mul_sum]; exact sum_congr rfl fun k _ => by ring
    rw [hfactor]
    nlinarith [(by positivity : (0 : ℝ) ≤ (Fintype.card (κ → τ) : ℝ) * (2 : ℝ) ^ n *
      (4 * (1 / (Fintype.card τ : ℝ)) * Real.sqrt (1 / (Fintype.card τ : ℝ))))]

end Cslib.Circuits.Boolean.WeightedThreshold
