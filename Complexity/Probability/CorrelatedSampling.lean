/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Cslib.Probability.StatisticalDistance
public import Complexity.Probability.PMF
import Complexity.Probability.PMF.Bind
import Complexity.Probability.PMF.Event
import Mathlib.Data.Finset.Max

/-!
# Correlated sampling

Two parties hold distributions `P` and `Q` on a finite set and share randomness, but do not
communicate. Correlated sampling lets each party output a sample with exactly its own distribution
so that the two samples agree with probability at least `(1 - δ) / (1 + δ) ≥ 1 - 2δ`, where `δ` is
the statistical distance between `P` and `Q`. This is the sampling step of Holenstein's proof of
the parallel repetition theorem [Holenstein, Lemma 8][Holenstein2009].

Holenstein's parties scan a shared infinite sequence of uniform points of `S × [0, 1]` and output
the first point under the graph of their own distribution. We use a finite version of the same
idea. For a finite family `P : I → PMF S`, the region under the graph of each `P i` is a union of
finitely many *cells* (`Cslib.Probability.CorrelatedSampling.Cell`): above each `s`, the intervals
between consecutive values `P i s`. The shared randomness orders the cells by drawing them without
replacement, each draw proportional to the length of the cell (`weightedOrder`). In such an order
the first cell inside any region is distributed as a single draw from that region
(`map_firstIn_weightedOrder`). Party `i` outputs the point `s` of the first cell under the graph of
`P i` (`sample`), so its output has distribution `P i` (`map_sample`). If the first cell under the
graph of `P i ⊔ P j` lies under the graph of `P i ⊓ P j`, both parties output it, which gives the
agreement bound (`agree_ge`, `disagree_le`).

The finite construction of the shared randomness is an adaptation of Holenstein's argument; it
proves the same bound.

## Main definitions

* `Cslib.Probability.CorrelatedSampling.weightedOrder`: drawing all elements of a finite type
  without replacement, each draw proportional to a weight.
* `Cslib.Probability.CorrelatedSampling.shared`: the shared randomness of correlated sampling.
* `Cslib.Probability.CorrelatedSampling.sample`: the output of party `i`.

## Main results

* `Cslib.Probability.CorrelatedSampling.map_firstIn_weightedOrder`: the first element of a set in a
  weighted order is a weighted draw from that set.
* `Cslib.Probability.CorrelatedSampling.map_sample`: party `i` outputs a sample of `P i`.
* `Cslib.Probability.CorrelatedSampling.agree_ge`: the two outputs agree with probability at least
  `(1 - δ) / (1 + δ)`.
* `Cslib.Probability.CorrelatedSampling.disagree_le`: they disagree with probability at most `2δ`.

## References

* [T. Holenstein, *Parallel repetition: simplifications and the no-signaling case*][Holenstein2009]
-/

@[expose] public section

namespace Cslib.Probability.CorrelatedSampling

open Finset
open scoped ENNReal NNReal

/-! ### Weighted orders -/

section WeightedOrder

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- One element of `U`, drawn with probability proportional to the weight `w`. -/
noncomputable def weightedDraw (w : Ω → ℝ≥0) (U : Finset Ω) (hU : ∑ a ∈ U, (w a : ℝ≥0∞) ≠ 0) :
    PMF Ω :=
  PMF.normalize (fun a => if a ∈ U then (w a : ℝ≥0∞) else 0)
    (by rwa [tsum_fintype, sum_ite_mem, univ_inter])
    (by
      rw [tsum_fintype, sum_ite_mem, univ_inter]
      exact ENNReal.sum_ne_top.mpr fun _ _ => ENNReal.coe_ne_top)

theorem weightedDraw_apply (w : Ω → ℝ≥0) (U : Finset Ω) (hU : ∑ a ∈ U, (w a : ℝ≥0∞) ≠ 0)
    (a : Ω) :
    weightedDraw w U hU a = if a ∈ U then (w a : ℝ≥0∞) * (∑ b ∈ U, (w b : ℝ≥0∞))⁻¹ else 0 := by
  rw [weightedDraw, PMF.normalize_apply, tsum_fintype, sum_ite_mem, univ_inter]
  split_ifs <;> simp

/-- The first `m` draws without replacement from `U`, each proportional to `w`, stopping early
when the remaining elements have weight zero. -/
noncomputable def weightedOrderAux (w : Ω → ℝ≥0) : ℕ → Finset Ω → PMF (List Ω)
  | 0, _ => PMF.pure []
  | m + 1, U =>
    if hU : ∑ a ∈ U, (w a : ℝ≥0∞) = 0 then PMF.pure [] else
      (weightedDraw w U hU).bind fun a => (weightedOrderAux w m (U.erase a)).map (a :: ·)

/-- All elements of positive weight, drawn without replacement, each draw with probability
proportional to the weight `w`. -/
noncomputable def weightedOrder (w : Ω → ℝ≥0) : PMF (List Ω) :=
  weightedOrderAux w (Fintype.card Ω) univ

/-- The first element of the list `l` that lies in `R`. -/
def firstIn (R : Finset Ω) (l : List Ω) : Option Ω := l.find? (· ∈ R)

omit [Fintype Ω] in
theorem firstIn_cons (R : Finset Ω) (a : Ω) (l : List Ω) :
    firstIn R (a :: l) = if a ∈ R then some a else firstIn R l := by
  by_cases ha : a ∈ R <;> simp [firstIn, ha]

omit [Fintype Ω] in
/-- If the first element of `l` in `A ∪ B` lies in `A`, it is also the first element in `A`. -/
theorem firstIn_of_firstIn_union {A B : Finset Ω} {l : List Ω} {c : Ω}
    (h : firstIn (A ∪ B) l = some c) (hc : c ∈ A) : firstIn A l = some c := by
  induction l with
  | nil => simp [firstIn] at h
  | cons a l ih =>
    rw [firstIn_cons] at h ⊢
    by_cases ha : a ∈ A ∪ B
    · rw [ite_eq_left ha] at h
      cases h
      rw [ite_eq_left hc]
    · rw [ite_eq_right ha] at h
      rw [ite_eq_right fun haA => ha (mem_union_left _ haA)]
      exact ih h

/-- **Luce's choice axiom for weighted orders.** In the draws without replacement from `U`, the
first element of `R` is distributed as a single weighted draw from `R ∩ U`. -/
theorem map_firstIn_weightedOrderAux (w : Ω → ℝ≥0) :
    ∀ (m : ℕ) (U R : Finset Ω), U.card ≤ m → (hR : ∑ a ∈ R ∩ U, (w a : ℝ≥0∞) ≠ 0) →
      (weightedOrderAux w m U).map (firstIn R) = (weightedDraw w (R ∩ U) hR).map some
  | 0, U, R, hU, hR => by
    rw [card_eq_zero.mp (Nat.le_zero.mp hU), inter_empty, sum_empty] at hR
    exact absurd rfl hR
  | m + 1, U, R, hU, hR => by
    have hU0 : ∑ a ∈ U, (w a : ℝ≥0∞) ≠ 0 := fun h =>
      hR (le_antisymm (h ▸ sum_le_sum_of_subset (inter_subset_right)) zero_le)
    rw [weightedOrderAux, dite_eq_right hU0, PMF.map_bind]
    -- Each continuation either stops at an element of `R` or recurses with `R ∩ U` unchanged.
    have hcont : ∀ a ∈ (weightedDraw w U hU0).support,
        ((weightedOrderAux w m (U.erase a)).map (a :: ·)).map (firstIn R) =
          if a ∈ R then PMF.pure (some a) else (weightedDraw w (R ∩ U) hR).map some := by
      intro a ha
      have haU : a ∈ U := by
        by_contra haU
        exact (PMF.mem_support_iff _ _).mp ha (by rw [weightedDraw_apply, ite_eq_right haU])
      rw [PMF.map_comp]
      by_cases haR : a ∈ R
      · rw [ite_eq_left haR]
        have : firstIn R ∘ (a :: ·) = Function.const _ (some a) := by
          funext l
          simp [firstIn_cons, haR]
        rw [this, PMF.map_const]
      · rw [ite_eq_right haR]
        have : firstIn R ∘ (a :: ·) = firstIn R := by
          funext l
          simp [firstIn_cons, haR]
        have hRU : R ∩ U.erase a = R ∩ U := by
          ext x
          simp only [mem_inter, mem_erase]
          exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, fun hx => haR (hx ▸ h.1), h.2⟩⟩
        rw [this, map_firstIn_weightedOrderAux w m (U.erase a) R
          (by rw [card_erase_of_mem haU]; omega) (hRU ▸ hR)]
        simp only [hRU]
    rw [Cslib.Probability.PMF.bind_congr_on_support _ _ _ hcont]
    have hrhs : ∀ c, (PMF.map some (weightedDraw w (R ∩ U) hR)) (some c) =
        weightedDraw w (R ∩ U) hR c := by
      intro c
      rw [PMF.map_apply, tsum_fintype]
      simp
    ext o
    rcases o with _ | c
    · rw [PMF.bind_apply, PMF.map_apply]
      simp only [reduceCtorEq, ite_false, tsum_zero]
      refine tsum_eq_zero_iff.mpr fun a => ?_
      split_ifs <;> simp [PMF.map_apply]
    rw [PMF.bind_apply, tsum_fintype, hrhs]
    set du := weightedDraw w U hU0
    set D := weightedDraw w (R ∩ U) hR
    by_cases hc : c ∈ R ∩ U
    · set WU := ∑ b ∈ U, (w b : ℝ≥0∞)
      set WRU := ∑ b ∈ R ∩ U, (w b : ℝ≥0∞)
      have hterm : ∀ a, du a *
          (if a ∈ R then PMF.pure (some a) else PMF.map some D) (some c) =
          (if a = c then (w c : ℝ≥0∞) * WU⁻¹ else 0) +
            (if a ∈ U.filter (· ∉ R) then (w a : ℝ≥0∞) * WU⁻¹ * ((w c : ℝ≥0∞) * WRU⁻¹)
              else 0) := by
        intro a
        by_cases haR : a ∈ R
        · rw [ite_eq_left haR, PMF.pure_apply]
          by_cases hac : a = c
          · subst hac
            simp only [weightedDraw_apply, (mem_inter.mp hc).2, ↓reduceIte, mul_one, mem_filter,
              haR, not_true_eq_false, and_false, add_zero, du]
            rfl
          · simp [hac, Ne.symm hac, haR]
        · rw [ite_eq_right haR, hrhs]
          have hac : a ≠ c := fun h => haR (h ▸ (mem_inter.mp hc).1)
          by_cases haU : a ∈ U
          · simp [du, D, weightedDraw_apply, hac, haR, haU, hc, WU, WRU]
          · simp [du, weightedDraw_apply, hac, haU]
      rw [sum_congr rfl fun a _ => hterm a, sum_add_distrib, sum_ite_eq', ite_eq_left (mem_univ _),
        sum_ite_mem, univ_inter, ← sum_mul, ← sum_mul]
      have hsplit : WU = WRU + ∑ b ∈ U.filter (· ∉ R), (w b : ℝ≥0∞) := by
        simp only [WU, WRU]
        rw [← sum_filter_add_sum_filter_not U (· ∈ R), filter_mem_eq_inter, inter_comm]
      have hWU : WU ≠ ⊤ := ENNReal.sum_ne_top.mpr fun _ _ => ENNReal.coe_ne_top
      have hWRU : WRU ≠ ⊤ := ENNReal.sum_ne_top.mpr fun _ _ => ENNReal.coe_ne_top
      have h1 : WRU * WRU⁻¹ = 1 := ENNReal.mul_inv_cancel hR hWRU
      have h2 : WU⁻¹ * WU = 1 := ENNReal.inv_mul_cancel hU0 hWU
      rw [show D c = (w c : ℝ≥0∞) * WRU⁻¹ by simp [D, weightedDraw_apply, hc, WRU]]
      calc (w c : ℝ≥0∞) * WU⁻¹ + (∑ b ∈ U.filter (· ∉ R), (w b : ℝ≥0∞)) * WU⁻¹ *
            ((w c : ℝ≥0∞) * WRU⁻¹)
          = (w c : ℝ≥0∞) * WRU⁻¹ * (WU⁻¹ * (WRU + ∑ b ∈ U.filter (· ∉ R), (w b : ℝ≥0∞))) := by
            rw [← mul_one ((w c : ℝ≥0∞) * WU⁻¹), ← h1]
            ring
        _ = (w c : ℝ≥0∞) * WRU⁻¹ := by rw [← hsplit, h2, mul_one]
    · have hDc : D c = 0 := by simp [D, weightedDraw_apply, hc]
      rw [hDc]
      refine sum_eq_zero fun a _ => ?_
      by_cases haR : a ∈ R
      · rw [ite_eq_left haR, PMF.pure_apply]
        by_cases hac : c = a
        · subst hac
          have hcU : c ∉ U := fun hcU => hc (mem_inter.mpr ⟨haR, hcU⟩)
          simp [du, weightedDraw_apply, hcU]
        · simp [hac]
      · rw [ite_eq_right haR, hrhs, hDc, mul_zero]

/-- In a weighted order of all elements, the first element of `R` is distributed as a single
weighted draw from `R`. -/
theorem map_firstIn_weightedOrder (w : Ω → ℝ≥0) (R : Finset Ω)
    (hR : ∑ a ∈ R, (w a : ℝ≥0∞) ≠ 0) :
    (weightedOrder w).map (firstIn R) = (weightedDraw w R hR).map some := by
  rw [weightedOrder, map_firstIn_weightedOrderAux w _ univ R card_univ.le (by rwa [inter_univ])]
  congr 2
  exact inter_univ R

end WeightedOrder

/-! ### Cells -/

section Telescoping

/-- The largest element of `T` below `v`, or `0` if there is none. -/
noncomputable def predIn (T : Finset ℝ≥0) (v : ℝ≥0) : ℝ≥0 := (T.filter (· < v)).sup id

/-- The gaps between consecutive elements of `T` add up to its maximum. -/
theorem sum_sub_predIn (T : Finset ℝ≥0) : ∑ v ∈ T, (v - predIn T v) = T.sup id := by
  induction T using Finset.induction_on_max with
  | empty => simp
  | insert a T hlt ih =>
    have haT : a ∉ T := fun ha => lt_irrefl a (hlt a ha)
    have hpa : predIn (insert a T) a = T.sup id := by
      rw [predIn, filter_insert, ite_eq_right (lt_irrefl a), filter_true_of_mem hlt]
    have hpv : ∀ v ∈ T, predIn (insert a T) v = predIn T v := by
      intro v hv
      rw [predIn, predIn, filter_insert, ite_eq_right (lt_asymm (hlt v hv))]
    have hsup : T.sup id ≤ a := Finset.sup_le fun v hv => (hlt v hv).le
    rw [sum_insert haT, hpa, sum_congr rfl fun v hv => by rw [hpv v hv], ih, sup_insert,
      tsub_add_cancel_of_le hsup, id, sup_of_le_left hsup]

/-- The gaps between consecutive elements of `T` up to `p ∈ T` add up to `p`. -/
theorem sum_filter_le_sub_predIn {T : Finset ℝ≥0} {p : ℝ≥0} (hp : p ∈ T) :
    ∑ v ∈ T.filter (· ≤ p), (v - predIn T v) = p := by
  have hpred : ∀ v ∈ T.filter (· ≤ p), predIn T v = predIn (T.filter (· ≤ p)) v := by
    intro v hv
    rw [predIn, predIn, filter_filter]
    congr 1
    refine filter_congr fun u _ => ⟨fun h => ⟨h.le.trans (mem_filter.mp hv).2, h⟩, And.right⟩
  rw [sum_congr rfl fun v hv => by rw [hpred v hv], sum_sub_predIn]
  exact le_antisymm (Finset.sup_le fun v hv => (mem_filter.mp hv).2)
    (le_sup (f := id) (mem_filter.mpr ⟨hp, le_rfl⟩))

end Telescoping

section Cells

variable {S I : Type*} [Fintype S] [Fintype I] (P : I → PMF S)

/-- The values `P i s` of the family at `s`. -/
noncomputable def values (s : S) : Finset ℝ≥0 :=
  open Classical in univ.image fun i => (P i s).toNNReal

/-- The cells of the family: a cell `⟨s, v⟩` stands for the interval from the next smaller value
at `s` up to the value `v`. -/
abbrev Cell := Σ s : S, {v // v ∈ values P s}

noncomputable instance : DecidableEq (Cell P) := Classical.decEq _

/-- The length of the interval of a cell. -/
noncomputable def weight (c : Cell P) : ℝ≥0 := c.2.1 - predIn (values P c.1) c.2.1

/-- The cells under the graph of `t`. -/
noncomputable def under (t : S → ℝ≥0) : Finset (Cell P) := univ.filter fun c => c.2.1 ≤ t c.1

/-- The cells under the graph of `P i`. -/
noncomputable def region (i : I) : Finset (Cell P) := under P fun s => (P i s).toNNReal

/-- The shared randomness of correlated sampling: a weighted order of the cells. -/
noncomputable def shared : PMF (List (Cell P)) := weightedOrder (weight P)

/-- The output of party `i`: the point of the first cell under the graph of `P i`. -/
noncomputable def sample (i : I) (l : List (Cell P)) : S :=
  ((firstIn (region P i) l).map Sigma.fst).getD (P i).support_nonempty.some

variable {P}

omit [Fintype S] in
theorem mem_values (i : I) (s : S) : (P i s).toNNReal ∈ values P s := by
  classical
  exact mem_image_of_mem _ (mem_univ i)

/-- Above each point, the cells under the graph of `t` have total length `t s`. -/
theorem sum_weight_fiber [DecidableEq S] {t : S → ℝ≥0} (s : S) (hts : t s ∈ values P s) :
    ∑ c ∈ (under P t).filter (·.1 = s), weight P c = t s := by
  rw [← sum_filter_le_sub_predIn hts, under, filter_filter, sum_filter, Fintype.sum_sigma,
    sum_filter, ← sum_coe_sort (values P s)]
  rw [sum_eq_single s]
  · refine sum_congr rfl fun v _ => ?_
    simp [weight]
  · intro s' _ hs'
    exact sum_eq_zero fun v _ => by simp [hs']
  · simp

/-- The cells under the graph of `t` have total length `∑ s, t s`. -/
theorem sum_weight_under {t : S → ℝ≥0} (ht : ∀ s, t s ∈ values P s) :
    ∑ c ∈ under P t, weight P c = ∑ s, t s := by
  classical
  rw [← sum_fiberwise (under P t) (·.1) (weight P)]
  exact sum_congr rfl fun s _ => sum_weight_fiber s (ht s)

theorem under_inter_under (t t' : S → ℝ≥0) : under P t ∩ under P t' = under P (t ⊓ t') := by
  ext c
  simp [under]

theorem under_union_under (t t' : S → ℝ≥0) : under P t ∪ under P t' = under P (t ⊔ t') := by
  ext c
  simp [under, le_max_iff]

omit [Fintype S] [Fintype I] in
theorem coe_toNNReal_apply (i : I) (s : S) : ((P i s).toNNReal : ℝ≥0∞) = P i s :=
  ENNReal.coe_toNNReal (PMF.apply_ne_top _ _)

/-- The region of each party has total length one. -/
theorem sum_weight_region (i : I) : ∑ c ∈ region P i, (weight P c : ℝ≥0∞) = 1 := by
  rw [← ENNReal.ofNNReal_finsetSum, region, sum_weight_under fun s => mem_values i s,
    ENNReal.ofNNReal_finsetSum]
  simp_rw [coe_toNNReal_apply]
  simpa [tsum_fintype] using (P i).tsum_coe

theorem sum_weight_region_ne_zero (i : I) : ∑ c ∈ region P i, (weight P c : ℝ≥0∞) ≠ 0 := by
  rw [sum_weight_region]
  exact one_ne_zero

/-- **Correlated sampling, marginals.** Party `i` outputs a sample of `P i`. -/
theorem map_sample (i : I) : (shared P).map (sample P i) = P i := by
  classical
  have hs : sample P i = (fun o => (o.map Sigma.fst).getD (P i).support_nonempty.some) ∘
      firstIn (region P i) := rfl
  rw [hs, ← PMF.map_comp, shared, map_firstIn_weightedOrder _ _ (sum_weight_region_ne_zero i),
    PMF.map_comp]
  ext s
  rw [PMF.map_apply, tsum_fintype, ← coe_toNNReal_apply i s,
    ← sum_weight_fiber (t := fun s => (P i s).toNNReal) s (mem_values i s),
    ENNReal.ofNNReal_finsetSum, sum_filter, under, sum_filter]
  refine sum_congr rfl fun c _ => ?_
  simp only [Function.comp_apply, Option.map_some, Option.getD_some, weightedDraw_apply,
    sum_weight_region, inv_one, mul_one]
  by_cases hcs : c.1 = s
  · subst hcs
    simp [region, under]
  · simp [hcs, Ne.symm hcs]

/-- The probability that the first cell under the graph of `P i ⊔ P j` lies under the graph of
`P i ⊓ P j`: the ratio of the lengths of the two regions. -/
theorem toOuterMeasure_firstIn_union (i j : I) :
    (shared P).toOuterMeasure (firstIn (region P i ∪ region P j) ⁻¹'
        (some '' ((region P i ∩ region P j : Finset (Cell P)) : Set (Cell P)))) =
      (∑ c ∈ region P i ∩ region P j, (weight P c : ℝ≥0∞)) *
        (∑ c ∈ region P i ∪ region P j, (weight P c : ℝ≥0∞))⁻¹ := by
  have hU : ∑ c ∈ region P i ∪ region P j, (weight P c : ℝ≥0∞) ≠ 0 := fun h =>
    sum_weight_region_ne_zero (P := P) i
      (le_antisymm (h ▸ sum_le_sum_of_subset subset_union_left) zero_le)
  rw [← PMF.toOuterMeasure_map_apply, shared, map_firstIn_weightedOrder _ _ hU,
    PMF.toOuterMeasure_map_apply, Set.preimage_image_eq _ (Option.some_injective _),
    PMF.toOuterMeasure_apply_finset, sum_mul]
  refine sum_congr rfl fun c hc => ?_
  rw [weightedDraw_apply, ite_eq_left (inter_subset_union hc)]

/-- The regions of two parties meet in length `∑ s, min (P i s) (P j s)` and together have length
`∑ s, max (P i s) (P j s)`. -/
theorem sum_weight_region_inter (i j : I) :
    ∑ c ∈ region P i ∩ region P j, weight P c = ∑ s, min (P i s).toNNReal (P j s).toNNReal := by
  rw [region, region, under_inter_under, sum_weight_under fun s => ?_]
  · rfl
  · rcases min_choice (P i s).toNNReal (P j s).toNNReal with h | h
    · exact (congrArg (· ∈ values P s) h).mpr (mem_values i s)
    · exact (congrArg (· ∈ values P s) h).mpr (mem_values j s)

theorem sum_weight_region_union (i j : I) :
    ∑ c ∈ region P i ∪ region P j, weight P c = ∑ s, max (P i s).toNNReal (P j s).toNNReal := by
  rw [region, region, under_union_under, sum_weight_under fun s => ?_]
  · rfl
  · rcases max_choice (P i s).toNNReal (P j s).toNNReal with h | h
    · exact (congrArg (· ∈ values P s) h).mpr (mem_values i s)
    · exact (congrArg (· ∈ values P s) h).mpr (mem_values j s)

open scoped Cslib.Probability.PMF in
/-- **Correlated sampling** [Holenstein, proof of Lemma 8][Holenstein2009]. The outputs of
parties `i` and `j` agree with probability at least `(1 - δ) / (1 + δ)`, where `δ` is the
statistical distance between `P i` and `P j`. -/
theorem agree_ge (i j : I) :
    (1 - dist (P i) (P j)) / (1 + dist (P i) (P j)) ≤
      ((shared P).toOuterMeasure {l | sample P i l = sample P j l}).toReal := by
  -- If the first cell of the union lies in the intersection, both parties output it.
  have hsub : firstIn (region P i ∪ region P j) ⁻¹'
      (some '' ((region P i ∩ region P j : Finset (Cell P)) : Set (Cell P))) ⊆
        {l | sample P i l = sample P j l} := by
    rintro l ⟨c, hc, hl⟩
    rw [coe_inter, Set.mem_inter_iff, mem_coe, mem_coe] at hc
    have hi := firstIn_of_firstIn_union hl.symm hc.1
    have hj := firstIn_of_firstIn_union (union_comm (region P i) _ ▸ hl.symm) hc.2
    simp [sample, hi, hj]
  refine le_trans ?_ (ENNReal.toReal_mono (PMF.toOuterMeasure_ne_top _ _)
    (MeasureTheory.measure_mono (μ := (shared P).toOuterMeasure) hsub))
  rw [toOuterMeasure_firstIn_union, ← ENNReal.ofNNReal_finsetSum, ← ENNReal.ofNNReal_finsetSum,
    sum_weight_region_inter, sum_weight_region_union, ENNReal.toReal_mul, ENNReal.toReal_inv,
    ENNReal.coe_toReal, ENNReal.coe_toReal, NNReal.coe_sum, NNReal.coe_sum, ← div_eq_mul_inv]
  simp only [NNReal.coe_min, NNReal.coe_max, ENNReal.coe_toNNReal_eq_toReal]
  -- `∑ min + ∑ max = 2` and `∑ max - ∑ min = 2δ`.
  have hsum := Cslib.Probability.PMF.sum_toReal (P i)
  have hsum' := Cslib.Probability.PMF.sum_toReal (P j)
  have hadd : ∑ s, min (P i s).toReal (P j s).toReal + ∑ s, max (P i s).toReal (P j s).toReal =
      2 := by
    rw [← sum_add_distrib]
    simp only [min_add_max, sum_add_distrib, hsum, hsum']
    norm_num
  have hsub' : ∑ s, max (P i s).toReal (P j s).toReal - ∑ s, min (P i s).toReal (P j s).toReal =
      2 * dist (P i) (P j) := by
    rw [← sum_sub_distrib, Cslib.Probability.PMF.dist_eq]
    simp only [max_sub_min_eq_abs']
    ring
  have hmin : ∑ s, min (P i s).toReal (P j s).toReal = 1 - dist (P i) (P j) := by linarith
  have hmax : ∑ s, max (P i s).toReal (P j s).toReal = 1 + dist (P i) (P j) := by linarith
  rw [hmin, hmax]

open scoped Cslib.Probability.PMF in
/-- **Correlated sampling, disagreement.** The outputs of parties `i` and `j` differ with
probability at most `2δ / (1 + δ) ≤ 2δ`, where `δ` is the statistical distance between `P i` and
`P j`. -/
theorem disagree_le (i j : I) :
    ((shared P).toOuterMeasure {l | sample P i l ≠ sample P j l}).toReal ≤
      2 * dist (P i) (P j) := by
  have h := agree_ge (P := P) i j
  have hcompl := Cslib.Probability.PMF.toOuterMeasure_toReal_add_compl (shared P)
    {l | sample P i l = sample P j l}
  have hδ : 0 ≤ dist (P i) (P j) := dist_nonneg
  have hfrac : 1 - 2 * dist (P i) (P j) ≤ (1 - dist (P i) (P j)) / (1 + dist (P i) (P j)) := by
    rw [le_div_iff₀ (by linarith)]
    nlinarith
  have : {l | sample P i l = sample P j l}ᶜ = {l | sample P i l ≠ sample P j l} := rfl
  rw [this] at hcompl
  linarith

end Cells

end Cslib.Probability.CorrelatedSampling
