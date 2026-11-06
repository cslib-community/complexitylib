/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Init
public import Cslib.Algorithms.Lean.TimeM
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Tactic

/-!
# Rational isolation of a polynomial threshold boundary

`bisect` is a finite rational program, using an external threshold decision
procedure. Its returned interval contains the threshold and has an exact dyadic
width. If the threshold is a root of a supplied rational polynomial, a supplied
root-separation bound makes that interval an exact algebraic representation.
`boundary_root` derives the root condition from a quantifier-free polynomial
sign description, rather than assuming an optimization result.

This is an original generic bridge, not an implementation of quantifier
elimination or root separation. Neither such a description nor its complexity
is obtained from a Boolean decision oracle alone. Costs count oracle calls and
three rational arithmetic operations per iteration, with unit-cost arithmetic;
coefficient sizes and rational bit costs are not bounded.
-/

public section

namespace Cslib.Polynomial.ThresholdIsolation

open Algorithms.Lean Set Filter
open scoped Topology

/-- A polynomial together with rational endpoints; soundness is a separate
predicate so that the executable program does not contain real-valued data. -/
structure RootInterval where
  /-- Rational defining polynomial, supplied as input to the isolator. -/
  polynomial : Polynomial ℚ
  /-- Closed rational lower endpoint. -/
  lower : ℚ
  /-- Closed rational upper endpoint. -/
  upper : ℚ
  deriving DecidableEq

/-- Exact interpretation: the closed interval contains exactly one real root.
A nonzero polynomial is required; endpoints may themselves be roots. -/
@[expose] def RootInterval.Represents (a : RootInterval) (s : ℝ) : Prop :=
  a.polynomial ≠ 0 ∧ s ∈ Icc (a.lower : ℝ) a.upper ∧
    (a.polynomial.map (algebraMap ℚ ℝ)).IsRoot s ∧
    ∀ r ∈ Icc (a.lower : ℝ) a.upper,
      (a.polynomial.map (algebraMap ℚ ℝ)).IsRoot r → r = s

/-- Finite bisection with a threshold oracle. True selects the lower half.
The count charges addition, division by two and loop dispatch once per step. -/
@[expose] def bisect (q : ℚ → TimeM ℕ Bool) : ℕ → ℚ → ℚ → TimeM ℕ (ℚ × ℚ)
  | 0, l, u => pure (l, u)
  | t + 1, l, u => do
    let m := (l + u) / 2
    TimeM.tick 3
    let b ← q m
    if b then bisect q t l m else bisect q t m u

/-- Every returned interval contains the actual threshold. -/
theorem bisect_contains (q : ℚ → TimeM ℕ Bool) (s : ℝ) (t : ℕ) (l u : ℚ)
    (hq : ∀ r ∈ Icc l u, (q r).ret = true ↔ s ≤ (r : ℝ))
    (hl : (l : ℝ) ≤ s) (hu : s ≤ (u : ℝ)) :
    s ∈ Icc ((bisect q t l u).ret.1 : ℝ) (bisect q t l u).ret.2 := by
  induction t generalizing l u with
  | zero => exact ⟨hl, hu⟩
  | succ t ih =>
    have hlu : l ≤ u := by exact_mod_cast hl.trans hu
    have hm : (l + u) / 2 ∈ Icc l u := ⟨by linarith, by linarith⟩
    simp only [bisect, TimeM.ret_bind]
    split_ifs with h
    · exact ih l _ (fun r hr => hq r ⟨hr.1, hr.2.trans hm.2⟩) hl ((hq _ hm).mp h)
    · exact ih _ u (fun r hr => hq r ⟨hm.1.trans hr.1, hr.2⟩)
        (le_of_lt (not_le.mp (fun hh => h ((hq _ hm).mpr hh)))) hu

/-- The exact width follows from the program's two branches, regardless of the oracle. -/
theorem bisect_width (q : ℚ → TimeM ℕ Bool) (t : ℕ) (l u : ℚ) :
    (bisect q t l u).ret.2 - (bisect q t l u).ret.1 = (u - l) / 2 ^ t := by
  induction t generalizing l u with
  | zero => simp [bisect]
  | succ t ih =>
    simp only [bisect, TimeM.ret_bind]
    split_ifs <;> rw [ih] <;> field_simp <;> ring

/-- At most one oracle call and three other operations per iteration. -/
theorem bisect_time (q : ℚ → TimeM ℕ Bool) (B : ℕ)
    (hq : ∀ r, (q r).time ≤ B) (t : ℕ) (l u : ℚ) :
    (bisect q t l u).time ≤ t * (B + 3) := by
  induction t generalizing l u with
  | zero => simp [bisect]
  | succ t ih =>
    simp only [bisect, TimeM.time_bind, TimeM.time_tick]
    split <;> have h := hq ((l + u) / 2)
    · have := ih l ((l + u) / 2); nlinarith
    · have := ih ((l + u) / 2) u; nlinarith

/-- Package the actual rational output with its defining polynomial. -/
@[expose] def isolate (p : Polynomial ℚ) (q : ℚ → TimeM ℕ Bool)
    (t : ℕ) (l u : ℚ) : TimeM ℕ RootInterval := do
  let (a, b) ← bisect q t l u
  pure ⟨p, a, b⟩

/-- A root-separation bound and a sufficiently narrow dyadic interval certify
exact output, including uniqueness. Separation is an explicit mathematical
input, not an assertion that a root-isolation backend has been implemented. -/
theorem isolate_represents (p : Polynomial ℚ) (hp : p ≠ 0)
    (q : ℚ → TimeM ℕ Bool) (s δ : ℝ)
    (hs : (p.map (algebraMap ℚ ℝ)).IsRoot s)
    (hsep : ∀ a b : ℝ, (p.map (algebraMap ℚ ℝ)).IsRoot a →
      (p.map (algebraMap ℚ ℝ)).IsRoot b → a ≠ b → δ ≤ |a - b|)
    (t : ℕ) (l u : ℚ)
    (hq : ∀ r ∈ Icc l u, (q r).ret = true ↔ s ≤ (r : ℝ))
    (hl : (l : ℝ) ≤ s) (hu : s ≤ (u : ℝ))
    (hwidth : ((u - l : ℚ) : ℝ) / 2 ^ t < δ) :
    (isolate p q t l u).ret.Represents s := by
  change (⟨p, (bisect q t l u).ret.1, (bisect q t l u).ret.2⟩ : RootInterval).Represents s
  push_cast at hwidth
  have hc := bisect_contains q s t l u hq hl hu
  have hw := congrArg (fun r : ℚ => (r : ℝ)) (bisect_width q t l u)
  push_cast at hw
  refine ⟨hp, hc, hs, ?_⟩
  intro r hr hroot
  by_contra hn
  have hd := hsep r s hroot hs hn
  have habs : |r - s| ≤ ((bisect q t l u).ret.2 : ℝ) - (bisect q t l u).ret.1 := by
    apply abs_le.mpr
    constructor <;> linarith [hc.1, hc.2, hr.1, hr.2]
  rw [hw] at habs
  linarith

/-- A quantifier-free threshold description has a polynomial root at every
interior boundary. The arbitrary Boolean recipe permits all finite Boolean
combinations of nonpositive polynomial tests (use both `p` and `-p` for equality).
No elimination theorem or algorithm is assumed implicitly. -/
theorem boundary_root {m : ℕ} (p : Fin m → Polynomial ℚ)
    (recipe : (Fin m → Bool) → Bool) (s l u : ℝ) (hl : l < s) (hu : s ≤ u)
    (hdesc : ∀ r ∈ Icc l u,
      recipe (fun i => decide (((p i).map (algebraMap ℚ ℝ)).eval r ≤ 0)) = true ↔ s ≤ r) :
    ∃ i, ((p i).map (algebraMap ℚ ℝ)).IsRoot s := by
  classical
  by_contra hn
  have hne (i) : ((p i).map (algebraMap ℚ ℝ)).eval s ≠ 0 := by
    exact fun h => hn ⟨i, h⟩
  have he (i) : ∀ᶠ r in 𝓝 s,
      decide (((p i).map (algebraMap ℚ ℝ)).eval r ≤ 0) =
        decide (((p i).map (algebraMap ℚ ℝ)).eval s ≤ 0) := by
    have hc := (((p i).map (algebraMap ℚ ℝ)).continuous).continuousAt (x := s)
    rcases lt_or_gt_of_ne (hne i) with h | h
    · filter_upwards [hc.eventually (gt_mem_nhds h)] with r hr
      simp only [hr.le, h.le, decide_true]
    · filter_upwards [hc.eventually (lt_mem_nhds h)] with r hr
      simp only [not_le.mpr hr, not_le.mpr h, decide_false]
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp (Filter.eventually_all.mpr he)
  let r := s - min (ε / 2) ((s - l) / 2)
  have hmin : 0 < min (ε / 2) ((s - l) / 2) := lt_min (by positivity) (by linarith)
  have hrs : r < s := by dsimp [r]; linarith
  have hrl : l ≤ r := by have := min_le_right (ε / 2) ((s - l) / 2); dsimp [r]; linarith
  have hd : dist r s < ε := by
    rw [Real.dist_eq, abs_of_neg (sub_neg.mpr hrs)]
    have := min_le_left (ε / 2) ((s - l) / 2)
    dsimp [r]; linarith
  have heq := funext (hball hd)
  have htrue := (hdesc s ⟨hl.le, hu⟩).mpr le_rfl
  rw [← heq] at htrue
  exact (not_le.mpr hrs) ((hdesc r ⟨hrl, hrs.le.trans hu⟩).mp htrue)

/-- A finite threshold transcript cannot identify an arbitrary real boundary
unless it queries that boundary itself. This concerns comparison-only access;
it does not rule out algorithms using additional algebraic input or primitives. -/
theorem exists_same_finite_threshold_answers (queries : Finset ℝ) (s : ℝ)
    (hs : s ∉ queries) :
    ∃ r : ℝ, s < r ∧ ∀ k ∈ queries, (s ≤ k ↔ r ≤ k) := by
  have he : ∀ᶠ r in 𝓝 s, ∀ k ∈ queries, (s ≤ k ↔ r ≤ k) := by
    apply (Filter.eventually_all_finset queries).mpr
    intro k hk
    have hne : s ≠ k := fun h => hs (h ▸ hk)
    rcases lt_or_gt_of_ne hne with h | h
    · filter_upwards [gt_mem_nhds h] with r hr
      exact iff_of_true h.le hr.le
    · filter_upwards [lt_mem_nhds h] with r hr
      exact iff_of_false (not_le.mpr h) (not_le.mpr hr)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp he
  refine ⟨s + ε / 2, by linarith, hball ?_⟩
  rw [Real.dist_eq, abs_of_pos (by linarith : 0 < s + ε / 2 - s)]
  linarith

/-- Taking the product retains every possible boundary root, without making
an uncomputable choice of one of the sign tests. -/
theorem boundary_product_root {m : ℕ} (p : Fin m → Polynomial ℚ)
    (recipe : (Fin m → Bool) → Bool) (s l u : ℝ) (hl : l < s) (hu : s ≤ u)
    (hdesc : ∀ r ∈ Icc l u,
      recipe (fun i => decide (((p i).map (algebraMap ℚ ℝ)).eval r ≤ 0)) = true ↔ s ≤ r) :
    ((∏ i, p i).map (algebraMap ℚ ℝ)).IsRoot s := by
  obtain ⟨i, hi⟩ := boundary_root p recipe s l u hl hu hdesc
  rw [Polynomial.map_prod, Polynomial.isRoot_prod]
  exact ⟨i, Finset.mem_univ i, hi⟩

/-- Packaging the interval adds no arithmetic or oracle operations in this model. -/
theorem isolate_time (p : Polynomial ℚ) (q : ℚ → TimeM ℕ Bool) (B : ℕ)
    (hq : ∀ r, (q r).time ≤ B) (t : ℕ) (l u : ℚ) :
    (isolate p q t l u).time ≤ t * (B + 3) := by
  simpa only [isolate, TimeM.time_bind, TimeM.time_pure, add_zero] using
    bisect_time q B hq t l u

end Cslib.Polynomial.ThresholdIsolation
