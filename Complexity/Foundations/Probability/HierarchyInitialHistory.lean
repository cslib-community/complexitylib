/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Foundations.Probability.HierarchyCompressedBin
public import Complexity.Foundations.Probability.RootMetric.WeightedError

/-!
# Payments for literal initial evaluator histories

Every completed group has its own walk length. Their conditional means add, and their
centered errors are summed on the original environment. The estimates below pay correlated
noise without a group-count factor or a heavy-event rarity assumption. Canonical mean bias,
preparation transport and the simultaneous lower-budget accuracy invariant remain separate.

## Main results

* `initialPrefixes_grid`: actual groups with distinct scheduled walk lengths.
* `initialPrefix_mean` and `initialGroupInput_sum`: literal means and budget boundaries.
* `initialPrefix_relative_noise`: denominator-retaining conditional group payment.
* `initialGroupInput_relative_fourth_le`: finite actual input/target moment relation.
* `initial_actualNoiseEntry`: full-rank noise payment in the shared predecoder API.
* `initialFirstSignal_preloss`: weighted stationary noise, with inverse-floor cancellation.
* `initialFirstSignal_overflowNoise`: unconditional correlated-noise tail payment.
* `initialFirstSignal_falseNoise`: first-noise payment at the raw prefix j+1.
-/

public section
noncomputable section
namespace Matrix.HierarchyParams.H4RankEnvironment.BudgetData
open Finset Cslib Cslib.RowCompression Cslib.Probability
open NormalizedMoments
open scoped BigOperators
attribute [local instance] Classical.propDecidable
attribute [local implicit_reducible] Matrix
variable {P : ℕ} [Fact P.Prime] {HP : FourthRootHierarchyParams 16 1 16 32 8}

/-- The actual successful initial prefixes are sums of distinct scheduled walks. This does
not identify their sum with one walk or change any group's allocation. -/
theorem initialPrefixes_grid (B : BudgetData HP P) (M : ℕ) (hM : 0 < M)
    (hbins : B.bins.Nonempty) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (s t : Fin 3) (hst : s ≠ t) (ks ka : ℕ) (ss st : List (ZMod P))
    (hs : r.source = gridChannel s ks ss) (ht : r.terminal = gridChannel t ka st) :
    let m := Nat.log2 M + 1
    let q := { r with usage := r.terminal }
    let Xs := X s (side P ks) (CopyPadding.identifier B.padding ss)
    let Ya := Y t (side P ka) (CopyPadding.identifier B.padding st)
    let A := fun i => B.initialGroupInput M (dyadicSlack m i) q
    let W := fun i => conditionalWalk Xs Ya
      (graph s t hst (side P ks) (side P ka) (side_le P ks) (side_le P ka)
        (CopyPadding.identifier B.padding ss) (CopyPadding.identifier B.padding st))
      (fun _ _ => B.steps M q (dyadicSlack m i)) (A i)
    B.initialPrefixes M r = some (fun j σ x y => ∑ i ∈ range (min j m), W i σ x y) ∧
    ∀ i < m, rowNormPow 4 P r.source.rate Xs Ya
      (fun σ x y => W i σ x y - rowSliceMean Xs Ya (A i) x y) ≤
      ((2 : ℝ) ^ (-B.requestPrecision M q) * (1 / 64 : ℝ) ^ dyadicSlack m i) ^ 4 := by
  dsimp only
  let q := { r with usage := r.terminal }
  have hg (i : ℕ) := B.completedGroup_initial_grid M
    (dyadicSlack (Nat.log2 M + 1) i) hM hbins q s t hst ks ka ss st hs ht
  constructor
  · unfold initialPrefixes
    dsimp only [q] at hg
    simp_rw [(hg _).1]
    have hm (l : List ℕ) (f : ℕ → Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ) :
        l.mapM (fun i => some (f i)) = some (l.map f) := List.mapM_pure
    rw [hm]
    simp only [bind, Option.bind_some, pure]
    congr 1
    funext j σ x y
    rw [← List.map_take, List.take_range, List.map_map]
    rw [← List.sum_toFinset _ List.nodup_range, List.toFinset_range]
    rfl
  · intro i _
    simpa only [q, one_div] using (hg i).2

/-- Exact centered input/target payment for correlated initial groups. Literal paired
amplitudes and bin importance remain inside `initialGroupInput`; no heavy rarity factor
or uniform absolute input envelope is substituted. The prefix cube pays correlation. -/
@[expose] def initialRelativeNoiseBudget (B : BudgetData HP P) (M : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (s t : Fin 3) (hst : s ≠ t) (ks ka : ℕ) (ss st : List (ZMod P))
    (G : Matrix (ZMod P) (ZMod P) ℝ) (j : ℕ) : ℝ :=
  let Xs := retainedMask s (side P ks) B.padding ss
  let Ya := retainedMask t (side P ka) B.padding st
  let graphV := graph s t hst (side P ks) (side P ka) (side_le P ks) (side_le P ka)
    (CopyPadding.identifier B.padding ss) (CopyPadding.identifier B.padding st)
  let q := { r with usage := r.terminal }
  let m := Nat.log2 M + 1
  (min j m : ℕ) ^ (3 : ℕ) *
    ∑ i ∈ range (min j m), ((P : ℝ) * r.source.rate)⁻¹ * ∑ x, ∑ y,
      (({σ | Xs σ x ∧ Ya σ y} : Finset (Environment P 3)).dens : ℝ) *
        (2 * (graphV x y).spectralExpansion ^ (2 * B.steps M q (dyadicSlack m i)) *
          𝔼 σ ∈ ({σ | Xs σ x ∧ Ya σ y} : Finset (Environment P 3)),
            |(B.initialGroupInput M (dyadicSlack m i) q σ x y -
              rowSliceMean Xs Ya (B.initialGroupInput M (dyadicSlack m i) q) x y) /
                (rate ka + G x y)| ^ 4)

/-- A derived finite input/target relation for each literal paired group. The genuine
amplitude (including importance weights) is divided by the same fixed-pair denominator.
This supplies no uniform rate or width absorption when the target is small. -/
theorem initialGroupInput_relative_fourth_le (B : BudgetData HP P) (M d : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (s t : Fin 3) (ks ka : ℕ) (ss st : List (ZMod P))
    (G : Matrix (ZMod P) (ZMod P) ℝ) (hG : ∀ x y, 0 ≤ G x y) (x y : ZMod P) :
    let Xs := retainedMask s (side P ks) B.padding ss
    let Ya := retainedMask t (side P ka) B.padding st
    (𝔼 σ ∈ ({σ | Xs σ x ∧ Ya σ y} : Finset (Environment P 3)),
      |(B.initialGroupInput M d r σ x y -
        rowSliceMean Xs Ya (B.initialGroupInput M d r) x y) / (rate ka + G x y)| ^ 4) ≤
        (2 * B.magnitude r / (rate ka + G x y)) ^ 4 := by
  dsimp only
  let S := ({σ | retainedMask s (side P ks) B.padding ss σ x ∧
    retainedMask t (side P ka) B.padding st σ y} : Finset (Environment P 3))
  have hd := add_pos_of_pos_of_nonneg (rate_pos ka) (hG x y)
  rcases S.eq_empty_or_nonempty with he | he
  · change (𝔼 σ ∈ S, _) ≤ _
    rw [he, expect_empty]
    positivity
  have hmean : |rowSliceMean (retainedMask s (side P ks) B.padding ss)
      (retainedMask t (side P ka) B.padding st) (B.initialGroupInput M d r) x y| ≤
      B.magnitude r :=
    (abs_expect_le S _).trans (expect_le he (fun σ _ => B.initialGroupInput_bound M d r σ x y))
  apply expect_le he
  intro σ _
  apply pow_le_pow_left₀ (by positivity) _ 4
  rw [abs_div, abs_of_pos hd]
  apply div_le_div_of_nonneg_right _ hd.le
  calc
    _ ≤ |B.initialGroupInput M d r σ x y| + |rowSliceMean _ _ _ x y| := abs_sub _ _
    _ ≤ B.magnitude r + B.magnitude r := add_le_add (B.initialGroupInput_bound M d r σ x y) hmean
    _ = _ := by ring

/-- Nonnegativity needs only the source normalization, not a positive target. -/
lemma initialRelativeNoiseBudget_nonneg (B : BudgetData HP P) (M : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (hr : 0 ≤ r.source.rate)
    (s t : Fin 3) (hst : s ≠ t) (ks ka : ℕ) (ss st : List (ZMod P))
    (G : Matrix (ZMod P) (ZMod P) ℝ) (j : ℕ) :
    0 ≤ B.initialRelativeNoiseBudget M r s t hst ks ka ss st G j := by
  unfold initialRelativeNoiseBudget
  apply mul_nonneg (by positivity)
  apply sum_nonneg
  intro i _
  apply mul_nonneg (inv_nonneg.mpr (mul_nonneg (Nat.cast_nonneg _) hr))
  apply sum_nonneg
  intro x _
  apply sum_nonneg
  intro y _
  exact mul_nonneg (by positivity) (mul_nonneg
    (mul_nonneg (by norm_num) (pow_nonneg (RotationMap.spectralExpansion_nonneg _) _))
    (expect_nonneg fun _ _ => by positivity))

/-- The literal paired inputs telescope bin by bin. Both remaining budget cutoffs are
shown: inactive fine samples and the initial coarse sample are not silently discarded. -/
theorem initialGroupInput_sum (B : BudgetData HP P) (M m j : ℕ) (hj : j < m)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (σ : Environment P 3)
    (x y : ZMod P) :
    ∑ i ∈ range (j + 1), B.initialGroupInput M (dyadicSlack m i) r σ x y =
      ∑ bin ∈ B.bins,
        ((if LogSpaceEstimation.lastBudget M (dyadicSlack m j) B.slack
          (B.sampleScale r (some bin)) = 0 then 0 else B.initialSample r bin σ x y) -
        (if LogSpaceEstimation.lastBudget M (2 * dyadicSlack m 0) B.slack
          (B.sampleScale r (some bin)) = 0 then 0 else B.initialSample r bin σ x y)) := by
  induction j with
  | zero => simp only [Nat.zero_add, sum_range_one, initialGroupInput]
  | succ j ih =>
    rw [sum_range_succ, ih (by omega), initialGroupInput, ← sum_add_distrib]
    apply sum_congr rfl
    intro bin _
    rw [dyadicSlack_succ (by omega : j + 1 < m)]
    ring

/-- Each group's stationarity identifies the literal prefix mean with the sum of its
input means, even though the scheduled walk lengths differ. Empty slices are included. -/
theorem initialPrefix_mean (B : BudgetData HP P) (M : ℕ) (hM : 0 < M)
    (hbins : B.bins.Nonempty) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (s t : Fin 3) (hst : s ≠ t) (ks ka : ℕ) (ss st : List (ZMod P))
    (hs : r.source = gridChannel s ks ss) (ht : r.terminal = gridChannel t ka st)
    (F : ℕ → Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
    (hF : B.initialPrefixes M r = some F) (j : ℕ) (x y : ZMod P) :
    let m := Nat.log2 M + 1
    let Xs := X s (side P ks) (CopyPadding.identifier B.padding ss)
    let Ya := Y t (side P ka) (CopyPadding.identifier B.padding st)
    rowSliceMean Xs Ya (F j) x y = ∑ i ∈ range (min j m),
      rowSliceMean Xs Ya
        (B.initialGroupInput M (dyadicSlack m i) {r with usage := r.terminal}) x y := by
  obtain ⟨hgrid, _⟩ := B.initialPrefixes_grid M hM hbins r s t hst ks ka ss st hs ht
  rw [hF] at hgrid
  have he := Option.some.inj hgrid
  subst F
  dsimp only
  unfold rowSliceMean
  rw [expect_sum_comm]
  apply sum_congr rfl
  intro i _
  exact rowSliceMean_conditionalWalk _ _ _ _ _ x y

/-- Literal semantic prefixes retain their fixed-pair denominator through each scheduled
contraction. This bounds actual relative centered noise and does not assume independence. -/
theorem initialPrefix_relative_noise (B : BudgetData HP P) (M : ℕ) (hM : 0 < M)
    (hbins : B.bins.Nonempty) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (s t : Fin 3) (hst : s ≠ t) (ks ka : ℕ) (ss st : List (ZMod P))
    (hs : r.source = gridChannel s ks ss) (ht : r.terminal = gridChannel t ka st)
    (F : ℕ → Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
    (hF : B.initialPrefixes M r = some F)
    (G : Matrix (ZMod P) (ZMod P) ℝ) (j : ℕ) :
    let Xs := retainedMask s (side P ks) B.padding ss
    let Ya := retainedMask t (side P ka) B.padding st
    rowNormPow 4 P r.source.rate Xs Ya (fun σ x y =>
      (F j σ x y - rowSliceMean Xs Ya (F j) x y) / (rate ka + G x y)) ≤
        B.initialRelativeNoiseBudget M r s t hst ks ka ss st G j := by
  obtain ⟨hgrid, _⟩ := B.initialPrefixes_grid M hM hbins r s t hst ks ka ss st hs ht
  have hmean := B.initialPrefix_mean M hM hbins r s t hst ks ka ss st hs ht F hF j
  rw [hF] at hgrid
  have he := Option.some.inj hgrid
  dsimp only at he hmean ⊢
  change rowNormPow 4 P r.source.rate
    (X s (side P ks) (CopyPadding.identifier B.padding ss))
    (Y t (side P ka) (CopyPadding.identifier B.padding st))
    (fun σ x y => (F j σ x y - rowSliceMean
      (X s (side P ks) (CopyPadding.identifier B.padding ss))
      (Y t (side P ka) (CopyPadding.identifier B.padding st)) (F j) x y) /
        (rate ka + G x y)) ≤ _
  simp_rw [hmean]
  rw [he]
  simp_rw [← sum_sub_distrib, sum_div]
  have hNu : 0 ≤ (P : ℝ) * r.source.rate := by
    rw [hs]; exact mul_nonneg (Nat.cast_nonneg _) (rate_pos ks).le
  apply (rowNormPow_sum_fourth_le _ hNu _ _ _).trans
  simp only [card_range, initialRelativeNoiseBudget]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply sum_le_sum
  intro i _
  exact rowNormPow_conditionalWalk_div_le_sum _ _ hNu _ _ _ _

/-- Literal full-rank first-prefix noise is the sum of correlated group noises. Individual
scheduled payments give a finite Minkowski payment, with the actual scheduled amplitudes.
No conditional independence of completed groups is required. -/
theorem initialPrefix_noise (B : BudgetData HP P) (M : ℕ) (hM : 0 < M)
    (hbins : B.bins.Nonempty) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (s t : Fin 3) (hst : s ≠ t) (ks ka : ℕ) (ss st : List (ZMod P))
    (hs : r.source = gridChannel s ks ss) (ht : r.terminal = gridChannel t ka st)
    (F : ℕ → Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
    (hF : B.initialPrefixes M r = some F) (j : ℕ) :
    let m := Nat.log2 M + 1
    let q := { r with usage := r.terminal }
    let Xs := X s (side P ks) (CopyPadding.identifier B.padding ss)
    let Ya := Y t (side P ka) (CopyPadding.identifier B.padding st)
    let μ := fun i => rowSliceMean Xs Ya (B.initialGroupInput M (dyadicSlack m i) q)
    rowNormPow 4 P r.source.rate Xs Ya
      (fun σ x y => F j σ x y - ∑ i ∈ range (min j m), μ i x y) ≤
      ((2 : ℝ) ^ (-B.requestPrecision M q) *
        ∑ i ∈ range (min j m), (1 / 64 : ℝ) ^ dyadicSlack m i) ^ 4 := by
  obtain ⟨hgrid, hnoise⟩ := B.initialPrefixes_grid M hM hbins r s t hst ks ka ss st hs ht
  rw [hF] at hgrid
  have he := Option.some.inj hgrid
  subst F
  dsimp only
  simp_rw [← sum_sub_distrib]
  rw [row_as_vertex]
  have hNu : 0 ≤ (P : ℝ) * r.source.rate := by
    rw [hs]; exact mul_nonneg (Nat.cast_nonneg _) (rate_pos ks).le
  let Xs := X s (side P ks) (CopyPadding.identifier B.padding ss)
  let Ya := Y t (side P ka) (CopyPadding.identifier B.padding st)
  let graphs := graph s t hst (side P ks) (side P ka) (side_le P ks) (side_le P ka)
    (CopyPadding.identifier B.padding ss) (CopyPadding.identifier B.padding st)
  have h := vertexNormPow_sum_le_pow_sum (X := fun σ (z : ZMod P × ZMod P) =>
      Xs σ z.1 ∧ Ya σ z.2) (by decide : 4 ≠ 0) hNu
    (range (min j (Nat.log2 M + 1)))
    (fun i σ (z : ZMod P × ZMod P) =>
      conditionalWalk Xs Ya graphs (fun _ _ => B.steps M {r with usage := r.terminal}
        (dyadicSlack (Nat.log2 M + 1) i))
        (B.initialGroupInput M (dyadicSlack (Nat.log2 M + 1) i) {r with usage := r.terminal})
        σ z.1 z.2 - rowSliceMean Xs Ya
        (B.initialGroupInput M (dyadicSlack (Nat.log2 M + 1) i)
          {r with usage := r.terminal}) z.1 z.2)
    (fun _ => 1) (fun i => (2 : ℝ) ^ (-B.requestPrecision M {r with usage := r.terminal}) *
      (1 / 64 : ℝ) ^ dyadicSlack (Nat.log2 M + 1) i)
    (fun _ _ => zero_le_one) (fun _ _ => by positivity) ?_
  · simpa only [one_mul, ← mul_sum] using h
  · intro i hi
    have hi' := hnoise i ((mem_range.mp hi).trans_le (min_le_right _ _))
    rw [row_as_vertex] at hi'
    exact hi'

/-- The actual first-prefix noise retains geometric decay at the last included group.
This is an unconditional payment: a heavy event cannot discount this correlated noise. -/
theorem initialPrefix_noise_dyadic (B : BudgetData HP P) (M : ℕ) (hM : 0 < M)
    (hbins : B.bins.Nonempty) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (s t : Fin 3) (hst : s ≠ t) (ks ka : ℕ) (ss st : List (ZMod P))
    (hs : r.source = gridChannel s ks ss) (ht : r.terminal = gridChannel t ka st)
    (F : ℕ → Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
    (hF : B.initialPrefixes M r = some F) (j : ℕ) (hj : j ≤ Nat.log2 M + 1) :
    let Xs := X s (side P ks) (CopyPadding.identifier B.padding ss)
    let Ya := Y t (side P ka) (CopyPadding.identifier B.padding st)
    rowNormPow 4 P r.source.rate Xs Ya
      (fun σ x y => F j σ x y - rowSliceMean Xs Ya (F j) x y) ≤
      (((2 : ℝ) ^ (-B.requestPrecision M {r with usage := r.terminal}) * (64 / 63)) *
        (1 / 64 : ℝ) ^ dyadicSlack (Nat.log2 M + 1) (j - 1)) ^ 4 := by
  have h := B.initialPrefix_noise M hM hbins r s t hst ks ka ss st hs ht F hF j
  dsimp only at h ⊢
  simp_rw [B.initialPrefix_mean M hM hbins r s t hst ks ka ss st hs ht F hF j]
  have hd := sum_prefix_dyadic_decay_le (by norm_num : (0 : ℝ) ≤ 1 / 64)
    (by norm_num : (1 / 64 : ℝ) < 1) hj
  rw [min_eq_left hj] at h
  rw [min_eq_left hj]
  refine h.trans (pow_le_pow_left₀ (by positivity) ?_ 4)
  have hm := mul_le_mul_of_nonneg_left hd
    (show 0 ≤ (2 : ℝ) ^ (-B.requestPrecision M {r with usage := r.terminal}) by positivity)
  convert hm using 1; ring

/-- The full-rank first signal has a derived unconditional row-maximum noise budget.
The explicit inverse rank rate converts matrix units to decoder units. -/
theorem initialFirstSignal_noise (B : BudgetData HP P) (M : ℕ) (hM : 0 < M)
    (hbins : B.bins.Nonempty) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (s t : Fin 3) (hst : s ≠ t) (ks ka : ℕ) (ss st : List (ZMod P))
    (hs : r.source = gridChannel s ks ss) (ht : r.terminal = gridChannel t ka st)
    (F : ℕ → Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
    (hF : B.initialPrefixes M r = some F) (i : ℕ) (hi : i < Nat.log2 M + 1) :
    let Xs := X s (side P ks) (CopyPadding.identifier B.padding ss)
    let Ya := Y t (side P ka) (CopyPadding.identifier B.padding st)
    let e := (2 : ℝ) ^ (-B.requestPrecision M {r with usage := r.terminal}) *
      (64 / 63) / rate ka
    vertexNormPow 4 P r.source.rate Xs (fun σ x => kthLargest 1 {y | Ya σ y}
      (fun y => |(F (i + 1) σ x y - rowSliceMean Xs Ya (F (i + 1)) x y) / rate ka|)) ≤
      (e * (1 / 64 : ℝ) ^ dyadicSlack (Nat.log2 M + 1) i) ^ 4 := by
  dsimp only
  have hNu : 0 ≤ (P : ℝ) * r.source.rate := by
    rw [hs]; exact mul_nonneg (Nat.cast_nonneg _) (rate_pos ks).le
  refine (vertex_row_max _ _ hNu _).trans ?_
  simp_rw [div_eq_mul_inv, mul_comm _ (rate ka)⁻¹]
  rw [row_const_mul, abs_of_pos (inv_pos.mpr (rate_pos ka))]
  have hnoise := B.initialPrefix_noise_dyadic M hM hbins r s t hst ks ka ss st hs ht F hF
    (i + 1) (by omega)
  dsimp only at hnoise
  simp only [Nat.add_sub_cancel] at hnoise
  apply (mul_le_mul_of_nonneg_left hnoise (by positivity)).trans_eq
  simp only [mul_pow, div_eq_mul_inv]
  ring

/-- The derived scheduled-history payment in the existing predecoder statistics API.
It can be used by `ActualMoment` without assuming that the whole prefix is one walk.
The preparation signal is arbitrary here and has no bearing on first-channel noise. -/
theorem initial_actualNoiseEntry (B : BudgetData HP P) (M : ℕ) (hM : 0 < M)
    (hbins : B.bins.Nonempty) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (s t : Fin 3) (hst : s ≠ t) (ks ka : ℕ) (ss st : List (ZMod P))
    (hs : r.source = gridChannel s ks ss) (ht : r.terminal = gridChannel t ka st)
    (F : ℕ → Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
    (hF : B.initialPrefixes M r = some F)
    (G : Matrix (ZMod P) (ZMod P) ℝ) (hG : ∀ x y, 0 ≤ G x y)
    (Lt : ℕ) (second : Environment P 3 → ZMod P → ℕ → ZMod P → ℝ)
    (i : ℕ) (hi : i < Nat.log2 M + 1) :
    rowNormPow 4 P r.source.rate (retainedMask s (side P ks) B.padding ss)
      (retainedMask t (side P ka) B.padding st)
      (actualNoiseEntry s t (side P ks) (side P ka) Lt B.padding ss st ka G
        (firstSignalIncrement F ka second) 0 0 i) ≤
      (((2 : ℝ) ^ (-B.requestPrecision M {r with usage := r.terminal}) * (64 / 63) / rate ka) *
        (1 / 64 : ℝ) ^ dyadicSlack (Nat.log2 M + 1) i) ^ 4 := by
  have hNu : 0 ≤ (P : ℝ) * r.source.rate := by
    rw [hs]; exact mul_nonneg (Nat.cast_nonneg _) (rate_pos ks).le
  have hn := actualNoiseEntry_first_prefix_row_le s t (side P ks) (side P ka) Lt
    B.padding ss st F ka G hG second 0 (by intros; rfl) i hNu
  have hp := B.initialPrefix_noise_dyadic M hM hbins r s t hst ks ka ss st hs ht F hF
    (i + 1) (by omega)
  dsimp only at hp
  simp only [Nat.add_sub_cancel] at hp
  refine hn.trans ((mul_le_mul_of_nonneg_left hp (by positivity)).trans_eq ?_)
  simp only [mul_pow, div_eq_mul_inv]
  ring

/-- The scheduled first-signal noise pays its weighted stationary preloss, including the
inverse-floor coefficient. The surviving `72 L` term is explicit; shrinking the floor
alone does not make this payment vanish. No mean error is included in this theorem. -/
theorem initialFirstSignal_preloss (B : BudgetData HP P) (M : ℕ) (hM : 0 < M)
    (hbins : B.bins.Nonempty) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (s t : Fin 3) (hst : s ≠ t) (ks ka : ℕ) (ss st : List (ZMod P))
    (hs : r.source = gridChannel s ks ss) (ht : r.terminal = gridChannel t ka st)
    (F : ℕ → Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
    (hF : B.initialPrefixes M r = some F) {floor L : ℝ} (hf : 0 < floor) :
    let m := Nat.log2 M + 1
    let Xs := X s (side P ks) (CopyPadding.identifier B.padding ss)
    let Ya := Y t (side P ka) (CopyPadding.identifier B.padding st)
    let e := (2 : ℝ) ^ (-B.requestPrecision M {r with usage := r.terminal}) *
      (64 / 63) / rate ka
    let γ := fun i σ x => kthLargest 1 {y | Ya σ y}
      (fun y => |(F (i + 1) σ x y - rowSliceMean Xs Ya (F (i + 1)) x y) / rate ka|)
    (36 * L + 72 * L / floor) ^ 4 * vertexNormPow 4 P r.source.rate Xs
      (fun σ x => ∑ i ∈ range m, dyadicFloor floor m i * γ i σ x) ≤
      ((36 * L * floor + 72 * L) * e / 511) ^ 4 := by
  extract_lets m Xs Ya e γ
  have hra := rate_pos ka
  have he : 0 ≤ e := by dsimp only [e]; positivity
  have hNu : 0 ≤ (P : ℝ) * r.source.rate := by
    rw [hs]; exact mul_nonneg (Nat.cast_nonneg _) (rate_pos ks).le
  have hbudget (i : ℕ) (hi : i ∈ range m) :
      vertexNormPow 4 P r.source.rate Xs (γ i) ≤ (e * 2 ^ dyadicSlack m i) ^ 4 := by
    have hn := B.initialFirstSignal_noise M hM hbins r s t hst ks ka ss st hs ht F hF
      i (mem_range.mp hi)
    refine hn.trans (pow_le_pow_left₀ (by positivity) ?_ 4)
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by norm_num) (by norm_num : (1 / 64 : ℝ) ≤ 2) _) he
  have hp := vertexNormPow_sum_le_pow_sum (X := Xs) (by decide : 4 ≠ 0) hNu
    (range m) γ (dyadicFloor floor m) (fun i => e * 2 ^ dyadicSlack m i)
    (fun i _ => dyadicFloor_nonneg hf.le m i) (fun _ _ => by positivity) hbudget
  have hsched := pre_schedule_sum hf.le he m
  have hsum : 0 ≤ ∑ i ∈ range m, dyadicFloor floor m i * (e * 2 ^ dyadicSlack m i) :=
    sum_nonneg fun i _ => mul_nonneg (dyadicFloor_nonneg hf.le m i) (by positivity)
  have hp' := hp.trans (pow_le_pow_left₀ hsum hsched 4)
  refine (mul_le_mul_of_nonneg_left hp' (by positivity)).trans_eq ?_
  rw [← mul_pow]
  congr 1
  field_simp

/-- All actual first-signal noise in a selected overflow tail is paid unconditionally.
In particular this bound can be restricted to heavy first overflows without invoking rarity
for noise. The other signal's noise and both deterministic mean tails remain separate. -/
theorem initialFirstSignal_overflowNoise (B : BudgetData HP P) (M : ℕ) (hM : 0 < M)
    (hbins : B.bins.Nonempty) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (s t : Fin 3) (hst : s ≠ t) (ks ka : ℕ) (ss st : List (ZMod P))
    (hs : r.source = gridChannel s ks ss) (ht : r.terminal = gridChannel t ka st)
    (F : ℕ → Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
    (hF : B.initialPrefixes M r = some F)
    (S : Environment P 3 → ZMod P → Finset (ZMod P)) (n K : ℕ → ℕ) (floor : ℕ → ℝ)
    (Δ : Environment P 3 → ZMod P → ℕ → ZMod P → Fin 2 → ℝ)
    (a : Environment P 3 → ZMod P → State (ZMod P)) :
    let m := Nat.log2 M + 1
    let Xs := X s (side P ks) (CopyPadding.identifier B.padding ss)
    let Ya := Y t (side P ka) (CopyPadding.identifier B.padding st)
    let e := (2 : ℝ) ^ (-B.requestPrecision M {r with usage := r.terminal}) *
      (64 / 63) / rate ka
    let γ := fun i σ x => kthLargest 1 {y | Ya σ y}
      (fun y => |(F (i + 1) σ x y - rowSliceMean Xs Ya (F (i + 1)) x y) / rate ka|)
    vertexNormPow 4 P r.source.rate Xs (fun σ x => firstOverflowNoiseTail
      (S σ x) n K floor (Δ σ x) (a σ x) m (fun i => 28 ^ (m - i)) (fun i => γ i σ x)) ≤
      (e * (7 / 9)) ^ 4 := by
  extract_lets m Xs Ya e γ
  have hra := rate_pos ka
  have he : 0 ≤ e := by dsimp only [e]; positivity
  have hNu : 0 ≤ (P : ℝ) * r.source.rate := by
    rw [hs]; exact mul_nonneg (Nat.cast_nonneg _) (rate_pos ks).le
  have h := vertexNormPow_firstOverflowNoiseTail_le_dyadic_budget S n K floor Δ a m
    (by decide : 4 ≠ 0) hNu Xs (C := 28) (q := 1 / 64) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) he γ (fun _ _ _ _ _ => kthLargest_nonneg)
    (fun i hi => B.initialFirstSignal_noise M hM hbins r s t hst ks ka ss st hs ht F hF i hi)
  norm_num only [show (28 : ℝ) * (1 / 64) / (1 - 28 * (1 / 64)) = 7 / 9 by norm_num] at h
  exact h

/-- The first-noise component of the integrated false-overflow raw-prefix charge is paid
at the already-added prefix j+1. This is not a bound for the combined clipped error: both
mean discrepancies and second noise must still be included before applying the decoder. -/
theorem initialFirstSignal_falseNoise (B : BudgetData HP P) (M : ℕ) (hM : 0 < M)
    (hbins : B.bins.Nonempty) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (s t : Fin 3) (hst : s ≠ t) (ks ka : ℕ) (ss st : List (ZMod P))
    (hs : r.source = gridChannel s ks ss) (ht : r.terminal = gridChannel t ka st)
    (F : ℕ → Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
    (hF : B.initialPrefixes M r = some F)
    (G : Matrix (ZMod P) (ZMod P) ℝ) (hG : ∀ x y, 0 ≤ G x y)
    (Lt : ℕ) (second : Environment P 3 → ZMod P → ℕ → ZMod P → ℝ)
    {floor : ℝ} (hf : 0 < floor) (R : ℝ) :
    let m := Nat.log2 M + 1
    let n := compatibleCapacity HP.K m
    let e := (2 : ℝ) ^ (-B.requestPrecision M {r with usage := r.terminal}) *
      (64 / 63) / rate ka
    ∑ j ∈ range m, (64 * (HP.K : ℝ) * R ^ 4 /
        ((n j : ℝ) * dyadicFloor floor m j ^ 4)) *
      rowNormPow 4 P r.source.rate (retainedMask s (side P ks) B.padding ss)
        (retainedMask t (side P ka) B.padding st)
        (actualNoiseEntry s t (side P ks) (side P ka) Lt B.padding ss st ka G
          (firstSignalIncrement F ka second) 0 0 j) ≤
      64 * (HP.K : ℝ) * R ^ 4 / floor ^ 4 * e ^ 4 / 63 := by
  extract_lets m n e
  have hra := rate_pos ka
  have he : 0 ≤ e := by dsimp only [e]; positivity
  refine (sum_le_sum fun j hj => ?_).trans
    (false_schedule_sum_capacity hf (Nat.cast_nonneg HP.K) m n
      (fun j _ => (compatibleCapacity_bounds HP.K m j).2))
  have hn := B.initial_actualNoiseEntry M hM hbins r s t hst ks ka ss st hs ht F hF
    G hG Lt second j (mem_range.mp hj)
  have hbudget := hn.trans (pow_le_pow_left₀ (by positivity)
    (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by norm_num) (by norm_num : (1 / 64 : ℝ) ≤ 2) _) he) 4)
  exact mul_le_mul_of_nonneg_left hbudget (by positivity)

end Matrix.HierarchyParams.H4RankEnvironment.BudgetData
