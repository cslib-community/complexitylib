/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Statistics.LeastSquares.FixedEffects.FixedColumns
public import Complexity.Statistics.LeastSquares.FixedEffects.MatrixBridge
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Tactic

/-!
# Original row indices for the executable fixed-effects audit

Multiplicity-preserving refinement of [XuGaoHu2027], equation (2) and
Theorem 4.1 (PDF p. 9). Both directions connect actual retained sublists to
subsets of the original row positions. Empty groups are permitted. The scalar
refitted stability is identified with the indexed subset problem, without
assuming that the original dummy columns survive.

## Main definitions

* `Corresponds`: retained sublists identified with original row positions.

## Main results

* `feasible_cost_iff`: feasibility and cost refinement in both directions.
* `refittedIntegralStability_eq_subsetStability`: equality of refitted infima.
* `integralStability_eq_refittedIntegralStability`: equality of optimum values for
  nonempty input groups when a feasible plan exists.
* `run_indexed_optimal`: returned-subset semantics and the executed resource bound.
-/

public section

namespace Cslib.LeastSquares.FixedEffects

open FiniteMinPlus
open scoped List

namespace Indexed

/-- Original groups, including empty ones. -/
abbrev Groups (gs : List (List Point)) := Fin gs.length
/-- Original row positions, so equal-valued observations remain distinct. -/
abbrev Rows (gs : List (List Point)) (g : Groups gs) := Fin (gs.get g).length
/-- The real regressor at an original row position. -/
@[expose] def x (gs : List (List Point)) (g : Groups gs) (i : Rows gs g) : ℝ :=
  ((gs.get g).get i).1
/-- The real response at an original row position. -/
@[expose] def y (gs : List (List Point)) (g : Groups gs) (i : Rows gs g) : ℝ :=
  ((gs.get g).get i).2

/-- Row positions selected in a particular original group. -/
@[expose] def fiber (gs : List (List Point)) (s : Finset (Sigma (Rows gs)))
    (g : Groups gs) : Finset (Rows gs g) :=
  Finset.univ.filter fun i => Sigma.mk g i ∈ s

/-- A sublist is represented by distinct original positions. The witness identifies
each retained occurrence with an input position; no values are deduplicated. -/
@[expose] def Represents (g kept : List Point) (t : Finset (Fin g.length)) : Prop :=
  kept <+ g ∧ ∃ is : List (Fin g.length),
    is.Nodup ∧ is.toFinset = t ∧ is.map g.get = kept

/-- Every actual sublist has a positional representation, including repetitions. -/
theorem represents_of_sublist (g kept : List Point) (h : kept <+ g) :
    ∃ t, Represents g kept t := by
  obtain ⟨e, he⟩ := List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp h
  refine ⟨(List.ofFn e).toFinset, h, List.ofFn e,
    List.nodup_ofFn.mpr e.injective, rfl, ?_⟩
  rw [List.map_ofFn]
  convert List.ofFn_get kept using 1
  congr 1
  funext i
  exact (he i).symm

/-- Every subset of original positions yields an actual sublist. -/
theorem exists_represents (g : List Point) (t : Finset (Fin g.length)) :
    ∃ kept, Represents g kept t := by
  let is := (List.finRange g.length).filter fun i => i ∈ t
  refine ⟨is.map g.get, ?_, is, (List.nodup_finRange _).filter _, ?_, rfl⟩
  · have h := (List.filter_sublist (p := fun i => decide (i ∈ t))
      (l := List.finRange g.length)).map g.get
    simpa only [List.map_get_finRange] using h
  · ext i
    simp [is]

/-- Positional representation preserves all additive statistics. -/
theorem sum_represents {g kept : List Point} {t : Finset (Fin g.length)}
    (h : Represents g kept t) {A : Type*} [AddCommMonoid A] (f : Point → A) :
    ∑ i ∈ t, f (g.get i) = (kept.map f).sum := by
  obtain ⟨_, is, hn, rfl, rfl⟩ := h
  rw [List.sum_toFinset _ hn, List.map_map]
  rfl

/-- Positional representation preserves cardinality. -/
theorem card_represents {g kept : List Point} {t : Finset (Fin g.length)}
    (h : Represents g kept t) : t.card = kept.length := by
  obtain ⟨_, is, hn, rfl, rfl⟩ := h
  rw [List.toFinset_card_of_nodup hn, List.length_map]

/-- A recovered plan corresponds to a subset of the original indexed input. -/
@[expose] def Corresponds (gs : List (List Point)) (p : List Choice)
    (s : Finset (Sigma (Rows gs))) : Prop :=
  ∃ c : Groups gs → Choice, p = List.ofFn c ∧
    ∀ g, Represents (gs.get g) (c g).kept (fiber gs s g) ∧
      (c g).deleted = (gs.get g).length - (c g).kept.length

private theorem valid_ofFn (gs : List (List Point)) (c : Groups gs → Choice) :
    Valid gs (List.ofFn c) ↔ ∀ g, c g ∈ choices (gs.get g) := by
  rw [Valid, Admissible, List.forall₂_iff_get]
  simp only [List.length_map, List.length_ofFn, true_and, List.get_eq_getElem,
    List.getElem_map, List.getElem_ofFn]
  constructor
  · intro h g
    exact h g.val g.isLt g.isLt
  · intro h i hi _
    exact h ⟨i, hi⟩

/-- Corresponding plans are valid removal plans. -/
theorem Corresponds.valid {gs : List (List Point)} {p : List Choice}
    {s : Finset (Sigma (Rows gs))} (h : Corresponds gs p s) : Valid gs p := by
  obtain ⟨c, rfl, hc⟩ := h
  exact (valid_ofFn gs c).mpr fun g => (mem_choices _ _).mpr ⟨(hc g).1.1, (hc g).2⟩

/-- Every valid executable plan recovers a subset of original row positions. -/
theorem subset_of_valid (gs : List (List Point)) (p : List Choice) (hp : Valid gs p) :
    ∃ s, Corresponds gs p s := by
  have hl : p.length = gs.length := by
    have := hp.length_eq
    simpa only [List.length_map] using this.symm
  let c : Groups gs → Choice := fun g => p.get (Fin.cast hl.symm g)
  have he : p = List.ofFn c := by
    apply List.ext_get
    · simp [hl]
    · intro i hi hj
      simp [c]
  have hc : ∀ g, c g ∈ choices (gs.get g) := (valid_ofFn gs c).mp (he ▸ hp)
  choose t ht using fun g => represents_of_sublist (gs.get g) (c g).kept
    ((mem_choices _ _).mp (hc g)).1
  refine ⟨Finset.univ.sigma t, c, he, fun g => ⟨?_, ((mem_choices _ _).mp (hc g)).2⟩⟩
  have hf : fiber gs (Finset.univ.sigma t) g = t g := by
    ext i
    simp [fiber]
  rw [hf]
  exact ht g

/-- Every indexed subset is representable by a valid executable plan. -/
theorem plan_of_subset (gs : List (List Point)) (s : Finset (Sigma (Rows gs))) :
    ∃ p, Corresponds gs p s := by
  choose kept hk using fun g => exists_represents (gs.get g) (fiber gs s g)
  exact ⟨List.ofFn (fun g => ⟨(gs.get g).length - (kept g).length, kept g⟩),
    _, rfl, fun g => ⟨hk g, rfl⟩⟩

private theorem subset_eq_sigma (gs : List (List Point)) (s : Finset (Sigma (Rows gs))) :
    s = Finset.univ.sigma (fiber gs s) := by
  ext i
  simp [fiber]

/-- Sample size counts original positions, without identifying equal observations. -/
theorem card_rows (gs : List (List Point)) :
    Fintype.card (Sigma (Rows gs)) = sampleSize gs := by
  rw [Fintype.card_sigma]
  simp only [Rows, Fintype.card_fin, sampleSize, total]
  conv_rhs => rw [← List.ofFn_get gs, List.map_ofFn, List.sum_ofFn]
  rfl

/-- The number of deletions is preserved by the positional refinement. -/
theorem Corresponds.deletions {gs : List (List Point)} {p : List Choice}
    {s : Finset (Sigma (Rows gs))} (h : Corresponds gs p s) :
    FixedEffects.deletions p = Fintype.card (Sigma (Rows gs)) - s.card := by
  obtain ⟨c, rfl, hc⟩ := h
  have hcard : s.card = ∑ g, (c g).kept.length := by
    rw [subset_eq_sigma gs s, Finset.card_sigma]
    exact Finset.sum_congr rfl fun g _ => card_represents (hc g).1
  rw [FixedEffects.deletions, total, List.map_ofFn, List.sum_ofFn,
    Fintype.card_sigma, hcard]
  simp only [Rows, Fintype.card_fin]
  change (∑ g, (c g).deleted) =
    (∑ g, (gs.get g).length) - ∑ g, (c g).kept.length
  rw [show (fun g => (c g).deleted) =
    (fun g => (gs.get g).length - (c g).kept.length) from funext fun g => (hc g).2]
  exact Finset.sum_tsub_distrib _ fun g _ => (hc g).1.1.length_le

private theorem group_sum {gs : List (List Point)} {c : Groups gs → Choice}
    {s : Finset (Sigma (Rows gs))}
    (hc : ∀ g, Represents (gs.get g) (c g).kept (fiber gs s g))
    (g : Groups gs) (f : Point → ℚ) :
    (∑ i : MatrixModel.Kept s g, (f ((gs.get g).get i.val) : ℝ)) =
      (((c g).kept.map f).sum : ℝ) := by
  rw [← Finset.sum_subtype (fiber gs s g) (by simp [fiber])
    (fun i => (f ((gs.get g).get i) : ℝ))]
  have hr := congrArg (fun q : ℚ => (q : ℝ)) (sum_represents (hc g) f)
  simpa only [Rat.cast_sum] using hr

private theorem group_card {gs : List (List Point)} {c : Groups gs → Choice}
    {s : Finset (Sigma (Rows gs))}
    (hc : ∀ g, Represents (gs.get g) (c g).kept (fiber gs s g)) (g : Groups gs) :
    Fintype.card (MatrixModel.Kept s g) = (c g).kept.length := by
  rw [Fintype.card_subtype]
  exact card_represents (hc g)

/-- The centered cross-scatter is preserved, even when groups disappear. -/
theorem Corresponds.cross {gs : List (List Point)} {p : List Choice}
    {s : Finset (Sigma (Rows gs))} (h : Corresponds gs p s) :
    MatrixModel.cross (MatrixModel.restrict (x gs) s) (MatrixModel.restrict (y gs) s) =
      (numerator p : ℝ) := by
  obtain ⟨c, rfl, hc⟩ := h
  simp only [MatrixModel.cross, numerator, total, List.map_ofFn, List.sum_ofFn,
    Rat.cast_sum, Function.comp_apply]
  apply Finset.sum_congr rfl
  intro g _
  simp only [MatrixModel.restrict, x, y]
  have hxy := group_sum (fun g => (hc g).1) g (fun p => p.1 * p.2)
  have hx := group_sum (fun g => (hc g).1) g Prod.fst
  have hy := group_sum (fun g => (hc g).1) g Prod.snd
  simp only [Rat.cast_mul] at hxy
  rw [hxy, hx, hy, group_card (fun g => (hc g).1) g, cross_running_sums]
  push_cast
  rfl

/-- The pooled regressor scatter is preserved. -/
theorem Corresponds.scatter {gs : List (List Point)} {p : List Choice}
    {s : Finset (Sigma (Rows gs))} (h : Corresponds gs p s) :
    MatrixModel.scatter (MatrixModel.restrict (x gs) s) = (denominator p : ℝ) := by
  obtain ⟨c, rfl, hc⟩ := h
  simp only [MatrixModel.scatter, MatrixModel.cross, denominator, total,
    List.map_ofFn, List.sum_ofFn, Rat.cast_sum, Function.comp_apply]
  apply Finset.sum_congr rfl
  intro g _
  simp only [MatrixModel.restrict, x]
  have hxx := group_sum (fun g => (hc g).1) g (fun p => p.1 ^ 2)
  have hx := group_sum (fun g => (hc g).1) g Prod.fst
  simp only [pow_two, Rat.cast_mul] at hxx
  rw [hxx, hx, group_card (fun g => (hc g).1) g, variance_running_sums]
  simp only [Rat.cast_sub, Rat.cast_div, Rat.cast_mul, Rat.cast_natCast, pow_two]

/-- Feasibility agrees with the actual original-index refitted subset test. -/
theorem Corresponds.feasible_iff {gs : List (List Point)} {p : List Choice}
    {s : Finset (Sigma (Rows gs))} (h : Corresponds gs p s) :
    Feasible gs p ↔
      0 < MatrixModel.scatter (MatrixModel.restrict (x gs) s) ∧
        MatrixModel.cross (MatrixModel.restrict (x gs) s)
          (MatrixModel.restrict (y gs) s) ≤ 0 := by
  rw [h.scatter, h.cross]
  constructor
  · rintro ⟨_, hv, ht⟩
    exact ⟨by exact_mod_cast hv, by exact_mod_cast (slope_nonpos_iff p hv).mp ht⟩
  · rintro ⟨hv, ht⟩
    have hv' : 0 < denominator p := by exact_mod_cast hv
    exact ⟨h.valid, hv', (slope_nonpos_iff p hv').mpr (by exact_mod_cast ht)⟩

/-- Exact feasible cost correspondence in both directions. No desired optimizer,
group-survival premise, or injectivity of observation values is supplied. -/
theorem feasible_cost_iff (gs : List (List Point)) (k : ℕ) :
    (∃ p, Feasible gs p ∧ k = deletions p) ↔
      ∃ s : Finset (Sigma (Rows gs)),
        (0 < MatrixModel.scatter (MatrixModel.restrict (x gs) s) ∧
          MatrixModel.cross (MatrixModel.restrict (x gs) s)
            (MatrixModel.restrict (y gs) s) ≤ 0) ∧
        k = Fintype.card (Sigma (Rows gs)) - s.card := by
  constructor
  · rintro ⟨p, hp, rfl⟩
    obtain ⟨s, hs⟩ := subset_of_valid gs p hp.1
    exact ⟨s, hs.feasible_iff.mp hp, hs.deletions⟩
  · rintro ⟨s, hs, rfl⟩
    obtain ⟨p, hp⟩ := plan_of_subset gs s
    exact ⟨p, hp.feasible_iff.mpr hs, hp.deletions.symm⟩

/-- An optimal feasible plan cannot erase an originally nonempty group: keeping
one row of such a group preserves both centered scores and saves one deletion.
This derives group survival without any small-deletion hypothesis. -/
theorem Corresponds.preservesGroups_of_optimal {gs : List (List Point)} {p : List Choice}
    {s : Finset (Sigma (Rows gs))} (h : Corresponds gs p s)
    (hne : ∀ g ∈ gs, g ≠ []) (hp : Feasible gs p)
    (hm : ∀ q, Feasible gs q → FixedEffects.deletions p ≤ FixedEffects.deletions q) :
    MatrixModel.PreservesGroups s := by
  obtain ⟨c, rfl, hc⟩ := h
  have hcvalid : ∀ g, c g ∈ choices (gs.get g) :=
    (valid_ofFn gs c).mp hp.1
  intro g
  by_contra hn
  have hz : (c g).kept = [] := by
    have hf : fiber gs s g = ∅ := by
      ext i
      simp only [fiber, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
        iff_false]
      exact fun hi => hn ⟨i, hi⟩
    have hh := card_represents (hc g).1
    rw [hf, Finset.card_empty] at hh
    exact List.length_eq_zero_iff.mp hh.symm
  have hg : gs.get g ≠ [] := hne _ (List.get_mem gs g)
  obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil _ hg
  let d : Groups gs → Choice := fun j =>
    if j = g then ⟨(gs.get g).length - 1, [a]⟩ else c j
  have hd : Valid gs (List.ofFn d) := (valid_ofFn gs d).mpr (by
    intro j
    by_cases hj : j = g
    · subst j
      simp only [d, ite_eq_left rfl]
      exact (mem_choices _ _).mpr ⟨List.singleton_sublist.mpr ha, rfl⟩
    · simpa only [d, ite_eq_right hj] using hcvalid j)
  have hnum : numerator (List.ofFn d) = numerator (List.ofFn c) := by
    simp only [numerator, total, List.map_ofFn, List.sum_ofFn, Function.comp_apply]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : j = g
    · subst j
      simp [d, hz, singleton_scatter, empty_scatter]
    · simp [d, hj]
  have hden : denominator (List.ofFn d) = denominator (List.ofFn c) := by
    simp only [denominator, total, List.map_ofFn, List.sum_ofFn, Function.comp_apply]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : j = g
    · subst j
      simp [d, hz, singleton_scatter, empty_scatter]
    · simp [d, hj]
  have hfeas : Feasible gs (List.ofFn d) := by
    refine ⟨hd, hden.symm ▸ hp.2.1, ?_⟩
    simpa only [slope, hnum, hden] using hp.2.2
  have hcost : FixedEffects.deletions (List.ofFn d) < FixedEffects.deletions (List.ofFn c) := by
    simp only [FixedEffects.deletions, total, List.map_ofFn, List.sum_ofFn, Function.comp_apply]
    have hlen : 0 < (gs.get g).length := List.length_pos_iff_ne_nil.mpr hg
    have hcg : (c g).deleted = (gs.get g).length := by simpa [hz] using (hc g).2
    apply Finset.sum_lt_sum
    · intro j _
      by_cases hj : j = g
      · subst j
        simp only [d, ite_eq_left rfl, hcg]
        omega
      · simp [d, hj]
    · exact ⟨g, Finset.mem_univ _, by simp only [d, ite_eq_left rfl, hcg]; omega⟩
  exact (not_lt_of_ge (hm _ hfeas)) hcost

/-- Executable-plan matrix stability equals original-index refitted stability.
This equality also respects the common zero convention for empty feasible sets. -/
theorem refittedIntegralStability_eq_subsetStability (gs : List (List Point)) :
    refittedIntegralStability gs = MatrixModel.subsetStability (x gs) (y gs) := by
  unfold refittedIntegralStability MatrixModel.subsetStability
  congr 1
  ext k
  simp only [Set.mem_ofPred_eq]
  exact (show (∃ p, MatrixFeasible gs p ∧ k = deletions p) ↔
    ∃ p, Feasible gs p ∧ k = deletions p from
      exists_congr fun p => and_congr_left fun _ => matrix_feasible_iff gs p).trans
        (feasible_cost_iff gs k)

/-- For nonempty original groups, the two optimum values agree. Unlike arbitrary
feasible subsets, an optimum cannot contain a vanished group. Existence is
explicit, avoiding the natural-infimum convention for infeasible problems. -/
theorem integralStability_eq_refittedIntegralStability (gs : List (List Point))
    (hne : ∀ g ∈ gs, g ≠ []) (hex : ∃ p, Feasible gs p) :
    integralStability (MatrixModel.row (x gs))
      (fun p => y gs p.1 p.2) (Pi.single none 1) 0 = refittedIntegralStability gs := by
  classical
  obtain ⟨q, hq⟩ := hex
  have hset : {k : ℕ | ∃ p, MatrixFeasible gs p ∧ k = deletions p}.Nonempty :=
    ⟨_, q, (matrix_feasible_iff gs q).mpr hq, rfl⟩
  obtain ⟨p, hp, he⟩ := Nat.sInf_mem hset
  have hp' : Feasible gs p := (matrix_feasible_iff gs p).mp hp
  have hm : ∀ q, Feasible gs q → deletions p ≤ deletions q := by
    intro q hq
    rw [← he]
    exact Nat.sInf_le ⟨q, (matrix_feasible_iff gs q).mpr hq, rfl⟩
  obtain ⟨s, hs⟩ := subset_of_valid gs p hp'.1
  have hpres := hs.preservesGroups_of_optimal hne hp' hm
  have hf := (MatrixModel.feasible_iff (x gs) (y gs) s hpres).mpr
    (hs.feasible_iff.mp hp')
  have hbound : integralStability (MatrixModel.row (x gs))
      (fun p => y gs p.1 p.2) (Pi.single none 1) 0 ≤ refittedIntegralStability gs := by
    change _ ≤ sInf _
    rw [he, hs.deletions]
    apply Nat.sInf_le
    refine ⟨s, ?_, rfl⟩
    convert hf using 1; (funext p; split_ifs <;> rfl)
  apply le_antisymm hbound
  unfold integralStability
  apply le_csInf
  · refine ⟨_, s, ?_, rfl⟩
    convert hf using 1; (funext p; split_ifs <;> rfl)
  · rintro k ⟨t, ht, rfl⟩
    have hscalar := ((MatrixModel.feasible_iff_preservesGroups (x gs) (y gs) t).mp
      (by convert ht using 1; (funext p; split_ifs <;> rfl))).2
    obtain ⟨r, hr, hc⟩ := (feasible_cost_iff gs _).mpr ⟨t, hscalar, rfl⟩
    change sInf _ ≤ _
    rw [hc]
    exact Nat.sInf_le ⟨r, (matrix_feasible_iff gs r).mpr hr, rfl⟩

/-- Original-input-to-returned-subset interpretation of the actual execution.
The returned optimum preserves every original group, and the established
arithmetic-RAM bound is expressed using the actual indexed optimum. -/
theorem run_indexed_optimal (gs : List (List Point)) (T : ℕ) (r : Resources.Result)
    (hr : (Resources.run gs).ret = some r)
    (hne : ∀ g ∈ gs, g ≠ []) (hT : ∀ g ∈ gs, g.length ≤ T)
    (hfull : 0 < numerator (Resources.fullPlan gs))
    (hnd : ∃ q, Valid gs q ∧ deletions q = r.hit.index ∧
      numerator q = numerator r.hit.entry.plan ∧ 0 < denominator q) :
    ∃ s : Finset (Sigma (Rows gs)),
      Corresponds gs r.hit.entry.plan s ∧ MatrixModel.PreservesGroups s ∧
      Feasible gs r.hit.entry.plan ∧
      Cslib.LeastSquares.Feasible (MatrixModel.row (x gs)) (fun p => y gs p.1 p.2)
        (Pi.single none 1) 0 (fun p => if p ∈ s then 1 else 0) ∧
      Fintype.card (Sigma (Rows gs)) - s.card = r.hit.index ∧
      integralStability (MatrixModel.row (x gs)) (fun p => y gs p.1 p.2)
        (Pi.single none 1) 0 = r.hit.index ∧
      (Resources.run gs).time ≤ 300 *
        (sampleSize gs * 2 ^ T + sampleSize gs * r.hit.index) := by
  obtain ⟨hf, hm, ht⟩ := Resources.run_time_of_nondegenerate gs T r hr hne hT hfull hnd
  have hc := (Resources.run_spec gs r hr).2.1
  obtain ⟨s, hs⟩ := subset_of_valid gs r.hit.entry.plan hf.1
  have hpres := hs.preservesGroups_of_optimal hne hf (by simpa only [hc] using hm)
  have he := refittedIntegralStability_eq gs r.hit.entry.plan hf (by simpa only [hc] using hm)
  rw [hc] at he
  refine ⟨s, hs, hpres, hf,
    (MatrixModel.feasible_iff (x gs) (y gs) s hpres).mpr (hs.feasible_iff.mp hf),
    hs.deletions ▸ hc, ?_, ht⟩
  rw [integralStability_eq_refittedIntegralStability gs hne ⟨_, hf⟩, he]

end Indexed

end Cslib.LeastSquares.FixedEffects
