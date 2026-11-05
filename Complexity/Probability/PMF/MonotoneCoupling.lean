/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Probability.PMF
public import Mathlib.Order.UpperLower.Basic
import Complexity.Probability.PMF.Expect
import Complexity.Probability.PMF.Map
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Tactic.Linarith

/-!
# Monotone couplings on finite preorders

Comparison on all upper sets implies existence of a joint probability mass function whose
marginals are the compared laws and whose support consists of ordered pairs. The proof uses
finite level-set decomposition and separation of a compact convex hull; no transport or
coupling existence theorem is assumed. There is no algorithmic resource bound.

The finite level-set and separation argument is developed here using Mathlib's compact
convex hull and Hahn–Banach separation APIs. In the separating dual potentials `u, v`, the
score `g x = min {v y | x ≤ y}` is monotone, lies below `v`, and satisfies `c ≤ u x + g x`.
Upper-event comparison therefore contradicts strict separation of the two prescribed marginals.

## Main results

* `sum_mul_le_of_upperSet`: upper-event comparison extends to monotone real scores.
* `exists_monotone_coupling`: upper-event comparison produces an ordered joint PMF.
* `upperSet_le_of_monotone_coupling`: the converse upper-event comparison.
-/

public section

namespace Cslib.Probability.PMF

open Finset
open scoped BigOperators

variable {α : Type*} [Fintype α] [DecidableEq α] [Preorder α]

omit [DecidableEq α] in
/-- Upper-event comparison extends to every monotone real score on a finite preorder. -/
theorem sum_mul_le_of_upperSet (μ ν : α → ℝ)
    (hmass : ∑ x, μ x = ∑ x, ν x)
    (hupper : ∀ U : Set α, IsUpperSet U →
      (∑ x, μ x * U.indicator (1 : α → ℝ) x) ≤
        ∑ x, ν x * U.indicator (1 : α → ℝ) x)
    (f : α → ℝ) (hf : Monotone f) :
    (∑ x, μ x * f x) ≤ ∑ x, ν x * f x := by
  classical
  suffices h : ∀ s : Finset ℝ, ∀ g : α → ℝ, (∀ x, g x ∈ s) → Monotone g →
      (∑ x, μ x * g x) ≤ ∑ x, ν x * g x from
    h (univ.image f) f (fun x => mem_image.mpr ⟨x, mem_univ _, rfl⟩) hf
  intro s
  induction s using Finset.induction_on_max with
  | empty =>
    intro g hg _
    have : IsEmpty α := ⟨fun x => notMem_empty (g x) (hg x)⟩
    simp
  | insert b s hb ih =>
    intro g hg hmono
    obtain rfl | hs := s.eq_empty_or_nonempty
    · have he : g = fun _ => b := funext fun x => by simpa using hg x
      simp only [he, ← sum_mul, hmass, le_refl]
    · let a := s.max' hs
      have hab : a < b := hb a (max'_mem s hs)
      let k := fun x => min (g x) a
      have hk : ∀ x, k x ∈ s := by
        intro x
        rcases mem_insert.mp (hg x) with hx | hx
        · simp only [k, hx, min_eq_right hab.le]
          exact max'_mem s hs
        · rw [show k x = g x from min_eq_left (le_max' s _ hx)]
          exact hx
      have hi := ih k hk (hmono.min monotone_const)
      have hu := hupper {x | b ≤ g x} (fun x y hxy hx => hx.trans (hmono hxy))
      have he (x : α) : g x = k x + (b - a) *
          ({x | b ≤ g x} : Set α).indicator (1 : α → ℝ) x := by
        rcases mem_insert.mp (hg x) with hx | hx
        · simp [hx, k, hab.le]
        · have hxa : g x ≤ a := le_max' s _ hx
          have hxb : ¬b ≤ g x := not_le.mpr (hb _ hx)
          simp [k, min_eq_left hxa, hxb]
      have hex (w : α → ℝ) : (∑ x, w x * g x) =
          (∑ x, w x * k x) + (b - a) *
            ∑ x, w x * ({x | b ≤ g x} : Set α).indicator (1 : α → ℝ) x := by
        rw [mul_sum, ← sum_add_distrib]
        apply sum_congr rfl
        intro x _
        conv_lhs => rw [he x]
        ring
      rw [hex μ, hex ν]
      exact add_le_add hi (mul_le_mul_of_nonneg_left hu (sub_nonneg.mpr hab.le))

/-- Finite upper-event comparison places the pair of mass vectors in the convex hull of
ordered point masses. This is the compact separation step of the coupling argument. -/
private theorem mem_convexHull_ordered (μ ν : α → ℝ)
    (hμ : ∀ x, 0 ≤ μ x) (hν : ∀ x, 0 ≤ ν x)
    (hmμ : ∑ x, μ x = 1) (hmν : ∑ x, ν x = 1)
    (hupper : ∀ U : Set α, IsUpperSet U →
      (∑ x, μ x * U.indicator (1 : α → ℝ) x) ≤
        ∑ x, ν x * U.indicator (1 : α → ℝ) x) :
    (μ, ν) ∈ convexHull ℝ (Set.range (fun z : {z : α × α // z.1 ≤ z.2} =>
      ((Pi.single z.val.1 1 : α → ℝ), (Pi.single z.val.2 1 : α → ℝ)))) := by
  classical
  let vertex := fun z : {z : α × α // z.1 ≤ z.2} =>
    ((Pi.single z.val.1 1 : α → ℝ), (Pi.single z.val.2 1 : α → ℝ))
  by_contra hn
  obtain ⟨L, c, hLc, hc⟩ := geometric_hahn_banach_point_closed
    (convex_convexHull ℝ (Set.range vertex))
    ((Set.finite_range vertex).isCompact_convexHull ℝ).isClosed hn
  let u := fun x => L (Pi.single x (1 : ℝ), 0)
  let v := fun x => L (0, Pi.single x (1 : ℝ))
  have huv (x y : α) (hxy : x ≤ y) : c ≤ u x + v y := by
    have hh := hc (vertex ⟨(x, y), hxy⟩) (subset_convexHull ℝ _ (Set.mem_range_self _))
    have he : vertex ⟨(x, y), hxy⟩ =
        (Pi.single x (1 : ℝ), 0) + (0, Pi.single y (1 : ℝ)) := by ext <;> simp [vertex]
    rw [he, map_add] at hh
    exact hh.le
  let upper := fun x : α => univ.filter (fun y => x ≤ y)
  have hne (x : α) : (upper x).Nonempty := ⟨x, mem_filter.mpr ⟨mem_univ _, le_rfl⟩⟩
  let g := fun x => (upper x).inf' (hne x) v
  have hgv (x : α) : g x ≤ v x := inf'_le _ (mem_filter.mpr ⟨mem_univ _, le_rfl⟩)
  have hmono : Monotone g := by
    intro x y hxy
    apply le_inf'
    intro z hz
    exact inf'_le _ (mem_filter.mpr ⟨mem_univ _, hxy.trans (mem_filter.mp hz).2⟩)
  have hug (x : α) : c ≤ u x + g x := by
    have hh : c - u x ≤ g x := by
      apply le_inf'
      intro y hy
      linarith [huv x y (mem_filter.mp hy).2]
    linarith
  have hcompare := sum_mul_le_of_upperSet μ ν (hmμ.trans hmν.symm) hupper g hmono
  have hlow : c ≤ (∑ x, μ x * u x) + ∑ x, ν x * v x := by
    calc
      c = ∑ x, μ x * c := by rw [← sum_mul, hmμ, one_mul]
      _ ≤ ∑ x, μ x * (u x + g x) :=
        sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hug x) (hμ x)
      _ = (∑ x, μ x * u x) + ∑ x, μ x * g x := by simp [mul_add, sum_add_distrib]
      _ ≤ (∑ x, μ x * u x) + ∑ x, ν x * g x := add_le_add le_rfl hcompare
      _ ≤ _ := add_le_add le_rfl
        (sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hgv x) (hν x))
  have hexpand : (μ, ν) =
      (∑ x, μ x • (Pi.single x (1 : ℝ), (0 : α → ℝ))) +
        ∑ x, ν x • ((0 : α → ℝ), Pi.single x (1 : ℝ)) := by
    ext x <;> simp [Prod.fst_sum, Prod.snd_sum, Pi.single_apply]
  rw [hexpand, map_add, map_sum, map_sum] at hLc
  simp only [map_smul, smul_eq_mul] at hLc
  exact (not_lt_of_ge hlow) hLc

omit [DecidableEq α] in
/-- **Finite monotone coupling theorem.** Upper-event comparison produces an actual joint
PMF with the given marginals and almost-sure order. This includes every finite preorder;
no nonemptiness assumption on the ambient type is needed. -/
theorem exists_monotone_coupling (μ ν : PMF α)
    (hupper : ∀ U : Set α, IsUpperSet U →
      (∑ x, (μ x).toReal * U.indicator (1 : α → ℝ) x) ≤
        ∑ x, (ν x).toReal * U.indicator (1 : α → ℝ) x) :
    ∃ γ : PMF (α × α), γ.map Prod.fst = μ ∧ γ.map Prod.snd = ν ∧
      ∀ z ∈ γ.support, z.1 ≤ z.2 := by
  classical
  have hh := mem_convexHull_ordered (fun x => (μ x).toReal) (fun x => (ν x).toReal)
    (fun _ => ENNReal.toReal_nonneg) (fun _ => ENNReal.toReal_nonneg)
    (sum_toReal μ) (sum_toReal ν) hupper
  obtain ⟨κ, _, w, z, hw, hsum, hz, heq⟩ :=
    (mem_convexHull_iff_exists_fintype).mp hh
  choose pair hpair using hz
  let r : PMF κ := PMF.ofFintype (fun i => ENNReal.ofReal (w i)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hw i), hsum, ENNReal.ofReal_one])
  let γ := r.map (fun i => (pair i).val)
  have hr (i : κ) : (r i).toReal = w i := ENNReal.toReal_ofReal (hw i)
  have hmarg (f : α × α → α) (law : PMF α)
      (hcoord : ∀ x, (∑ i, w i * (if x = f (pair i).val then 1 else 0)) = (law x).toReal) :
      γ.map f = law := by
    apply PMF.ext
    intro x
    apply (ENNReal.toReal_eq_toReal_iff' ((γ.map f).apply_ne_top x) (law.apply_ne_top x)).mp
    rw [show γ.map f = r.map (fun i => f (pair i).val) from PMF.map_comp _ _ _]
    rw [map_apply_toReal]
    simp only [hr]
    convert hcoord x using 1
    apply sum_congr rfl
    intro i _
    split_ifs <;> simp
  refine ⟨γ, hmarg Prod.fst μ ?_, hmarg Prod.snd ν ?_, ?_⟩
  · intro x
    have hh := congrArg (fun p : (α → ℝ) × (α → ℝ) => p.1 x) heq
    simp only [← hpair, Prod.fst_sum, Prod.smul_fst] at hh
    simpa only [Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, Pi.single_apply] using hh
  · intro x
    have hh := congrArg (fun p : (α → ℝ) × (α → ℝ) => p.2 x) heq
    simp only [← hpair, Prod.snd_sum, Prod.smul_snd] at hh
    simpa only [Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, Pi.single_apply] using hh
  · intro p hp
    obtain ⟨i, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hp
    exact (pair i).property

omit [DecidableEq α] in
/-- An ordered coupling compares all upper events. Together with
`exists_monotone_coupling`, this gives the finite upper-event characterization. -/
theorem upperSet_le_of_monotone_coupling (μ ν : PMF α) (γ : PMF (α × α))
    (hleft : γ.map Prod.fst = μ) (hright : γ.map Prod.snd = ν)
    (horder : ∀ z ∈ γ.support, z.1 ≤ z.2)
    {U : Set α} (hU : IsUpperSet U) :
    (∑ x, (μ x).toReal * U.indicator (1 : α → ℝ) x) ≤
      ∑ x, (ν x).toReal * U.indicator (1 : α → ℝ) x := by
  classical
  rw [← hleft, ← hright, sum_map_mul, sum_map_mul]
  apply sum_le_sum
  intro z _
  by_cases hz : z ∈ γ.support
  · apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
    by_cases hx : z.1 ∈ U
    · simp [hx, hU (horder z hz) hx]
    · simp only [Set.indicator_of_notMem hx]
      exact Set.indicator_nonneg (fun _ _ => zero_le_one) _
  · have hz' : γ z = 0 := by simpa only [PMF.mem_support_iff, not_not] using hz
    simp [hz']

end Cslib.Probability.PMF
