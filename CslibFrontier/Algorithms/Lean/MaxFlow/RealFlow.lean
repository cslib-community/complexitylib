/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Combinatorics.WeightedCut.RealCut
import CslibFrontier.Foundations.LinearAlgebra.Matrix.LinearProgramming
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Logic.Relation
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Maximum flows with capacities in a linearly ordered field

Flows on a finite vertex type `V` with capacities `W : V → V → K` in a linearly ordered field `K`
(for example `ℝ` or `ℚ`), and the max-flow min-cut theorem in this setting. The integral theory
over `ℕ`, with algorithms, is in `CslibFrontier.Algorithms.Lean.MaxFlow.Basic`.

**Source mapping.** [Schrijver2003], Section 10.1 (pp. 148–149), defines flows on a digraph with
real capacities `c : A → ℝ₊`, conservation and the value as net outflow at `s`; Theorem 10.3
(Section 10.2, p. 150) is the max-flow min-cut theorem. This module differs in three ways:

* A flow is a function `f : V × V → K` on all ordered pairs, so absent arcs are pairs of capacity
  `0`. Antiparallel arcs, loops, arcs into `s` and arcs out of `t` are allowed; a loop contributes
  to both the outflow and the inflow of its vertex, so it cancels.
* Capacities lie in an arbitrary linearly ordered field `K` rather than in `ℝ`. This is an
  extension of the source statement.
* Since `K` need not be complete, a maximum flow is not obtained by compactness. It comes from
  linear-programming duality over `K` (`Matrix.exists_isGreatest_of_bddAbove`), and augmenting
  paths need not terminate either.

Since capacities need not be integers, augmenting paths need not terminate. Instead, a maximum
flow is obtained from linear-programming duality over `K`
(`Matrix.exists_isGreatest_of_bddAbove`). Its optimality is then certified by the set of vertices
reachable from `s` in the residual graph: if `t` were reachable, an augmentation along the
reachability relation would increase the value.

## Main definitions

* `Cslib.Algorithms.Lean.MaxFlow.IsFeasibleRealFlow`: capacity and conservation constraints.
* `Cslib.Algorithms.Lean.MaxFlow.realNetOut`: net outflow at a vertex; the value at the source.
* `Cslib.Algorithms.Lean.MaxFlow.IsMaxRealFlow`: the greatest value of a feasible flow.

## Main results

* `Cslib.Algorithms.Lean.MaxFlow.IsFeasibleRealFlow.realNetOut_eq_sub`: the value of a feasible
  flow equals its net flow across any `s`–`t` cut.
* `Cslib.Algorithms.Lean.MaxFlow.IsFeasibleRealFlow.realNetOut_le_cutWeight`: weak duality.
* `Cslib.Algorithms.Lean.MaxFlow.exists_isMaxRealFlow`: a maximum flow exists.
* `Cslib.Algorithms.Lean.MaxFlow.isMaxRealFlow_minRealCutBetween`: the **max-flow min-cut
  theorem**, the maximum flow value is `minRealCutBetween W s t`.

## References

* [FordFulkerson1962]
* [Schrijver2003]
-/

public section

namespace Cslib.Algorithms.Lean.MaxFlow

open Cslib.WeightedCut Finset Matrix

variable {V : Type*} [Fintype V] {K : Type*} [Field K]

/-- The net outflow `∑ w, f (v, w) - ∑ u, f (u, v)` of `f` at `v`. At the source `s` this is the
value of the flow. -/
def realNetOut (f : V × V → K) (v : V) : K :=
  ∑ w, f (v, w) - ∑ u, f (u, v)

theorem realNetOut_add (f g : V × V → K) (v : V) :
    realNetOut (f + g) v = realNetOut f v + realNetOut g v := by
  simp only [realNetOut, Pi.add_apply, sum_add_distrib]
  ring

theorem realNetOut_smul (c : K) (f : V × V → K) (v : V) :
    realNetOut (c • f) v = c * realNetOut f v := by
  simp only [realNetOut, Pi.smul_apply, smul_eq_mul, ← mul_sum]
  ring

/-- `c` units on the single arc `(a, b)` leave `a` and enter `b`. -/
theorem realNetOut_single [DecidableEq V] (a b : V) (c : K) (v : V) :
    realNetOut (Pi.single (a, b) c) v = (if v = a then c else 0) - (if v = b then c else 0) := by
  simp only [realNetOut, Pi.single_apply, Prod.mk.injEq]
  congr 1
  · by_cases hv : v = a <;> simp [hv]
  · by_cases hv : v = b <;> simp [hv]

variable [LinearOrder K]

/-- A feasible `s`–`t` flow for the capacities `W`: every arc value `f (u, v)` lies between `0`
and `W u v`, and inflow equals outflow at every vertex other than `s` and `t`. -/
def IsFeasibleRealFlow (W : V → V → K) (s t : V) (f : V × V → K) : Prop :=
  (∀ u v, 0 ≤ f (u, v)) ∧ (∀ u v, f (u, v) ≤ W u v) ∧
    ∀ v, v ≠ s → v ≠ t → ∑ u, f (u, v) = ∑ w, f (v, w)

/-- `val` is the greatest value of a feasible `s`–`t` flow for the capacities `W`. -/
def IsMaxRealFlow (W : V → V → K) (s t : V) (val : K) : Prop :=
  IsGreatest ((realNetOut · s) '' {f | IsFeasibleRealFlow W s t f}) val

/-! ### Flow across a cut -/

variable {W : V → V → K} {s t : V} {f : V × V → K}

theorem IsFeasibleRealFlow.realNetOut_eq_zero (hf : IsFeasibleRealFlow W s t f) {v : V}
    (hs : v ≠ s) (ht : v ≠ t) : realNetOut f v = 0 := by
  rw [realNetOut, hf.2.2 v hs ht, sub_self]

variable [DecidableEq V]

/-- The value of a feasible flow equals its net flow across any `s`–`t` cut `X`: the flow on
arcs leaving `X` minus the flow on arcs entering `X`. -/
theorem IsFeasibleRealFlow.realNetOut_eq_sub (hf : IsFeasibleRealFlow W s t f) {X : Finset V}
    (hs : s ∈ X) (ht : t ∉ X) :
    realNetOut f s =
      ∑ u ∈ X, ∑ v ∈ univ \ X, f (u, v) - ∑ u ∈ X, ∑ v ∈ univ \ X, f (v, u) := by
  have hsum : realNetOut f s = ∑ x ∈ X, realNetOut f x := by
    rw [sum_eq_single_of_mem s hs]
    exact fun x hx hxs => hf.realNetOut_eq_zero hxs fun h => ht (h ▸ hx)
  have hsplit : ∀ x, realNetOut f x =
      (∑ v ∈ univ \ X, f (x, v) - ∑ v ∈ univ \ X, f (v, x)) +
        (∑ v ∈ X, f (x, v) - ∑ v ∈ X, f (v, x)) := by
    intro x
    rw [realNetOut, ← sum_sdiff (subset_univ X) (f := fun v => f (x, v)),
      ← sum_sdiff (subset_univ X) (f := fun v => f (v, x))]
    ring
  have hcomm : ∑ x ∈ X, ∑ v ∈ X, f (v, x) = ∑ x ∈ X, ∑ v ∈ X, f (x, v) := sum_comm
  rw [hsum, sum_congr rfl fun x _ => hsplit x, sum_add_distrib, sum_sub_distrib, sum_sub_distrib,
    hcomm, sub_self, add_zero]

variable [IsStrictOrderedRing K]

/-- **Weak duality**: the value of a feasible `s`–`t` flow is at most the weight of every `s`–`t`
cut. -/
theorem IsFeasibleRealFlow.realNetOut_le_cutWeight (hf : IsFeasibleRealFlow W s t f)
    {X : Finset V} (hs : s ∈ X) (ht : t ∉ X) : realNetOut f s ≤ cutWeight W X := by
  rw [hf.realNetOut_eq_sub hs ht, cutWeight]
  have hout : ∑ u ∈ X, ∑ v ∈ univ \ X, f (u, v) ≤ ∑ u ∈ X, ∑ v ∈ univ \ X, W u v :=
    sum_le_sum fun u _ => sum_le_sum fun v _ => hf.2.1 u v
  have hin : 0 ≤ ∑ u ∈ X, ∑ v ∈ univ \ X, f (v, u) :=
    sum_nonneg fun u _ => sum_nonneg fun v _ => hf.1 v u
  linarith

/-! ### Existence of a maximum flow -/

/-- Signed incidence of the arc `e` at `v`: `1` if `e` enters `v`, `-1` if it leaves `v`, and `0`
otherwise, including for loops. -/
private def inflow (v : V) (e : V × V) : K :=
  (if e.2 = v then 1 else 0) - (if e.1 = v then 1 else 0)

omit [LinearOrder K] [IsStrictOrderedRing K] in
private theorem inflow_dotProduct (v : V) (f : V × V → K) :
    inflow v ⬝ᵥ f = ∑ u, f (u, v) - ∑ w, f (v, w) := by
  have h₁ : ∑ e : V × V, (if e.2 = v then f e else 0) = ∑ u, f (u, v) := by
    rw [Fintype.sum_prod_type]
    simp
  have h₂ : ∑ e : V × V, (if e.1 = v then f e else 0) = ∑ w, f (v, w) := by
    rw [Fintype.sum_prod_type, sum_eq_single v (fun a _ ha => by simp [ha]) (by simp)]
    simp
  simp only [dotProduct, inflow, sub_mul, ite_mul, one_mul, zero_mul, sum_sub_distrib, h₁, h₂]

/-- Conservation at the vertices other than `s` and `t`, as a matrix. -/
private def conservationMatrix (s t : V) : Matrix V (V × V) K :=
  Matrix.of fun v e => if v = s ∨ v = t then 0 else inflow v e

/-- The constraints of `IsFeasibleRealFlow` as a system `flowMatrix s t *ᵥ f ≤ flowBound W`:
capacities, non-negativity, and conservation as two opposite inequalities. -/
private def flowMatrix (s t : V) : Matrix ((V × V) ⊕ (V × V) ⊕ V ⊕ V) (V × V) K :=
  fromRows 1 (fromRows (-1) (fromRows (conservationMatrix s t) (-conservationMatrix s t)))

private def flowBound (W : V → V → K) : (V × V) ⊕ (V × V) ⊕ V ⊕ V → K :=
  Sum.elim (fun e => W e.1 e.2) (Sum.elim 0 (Sum.elim 0 0))

private theorem flowMatrix_mulVec_le_iff :
    flowMatrix s t *ᵥ f ≤ flowBound W ↔ IsFeasibleRealFlow W s t f := by
  have hC : ∀ v, (conservationMatrix s t *ᵥ f) v =
      if v = s ∨ v = t then 0 else ∑ u, f (u, v) - ∑ w, f (v, w) := by
    intro v
    simp only [conservationMatrix, mulVec, dotProduct, Matrix.of_apply]
    split_ifs with h
    · simp
    · rw [← inflow_dotProduct]
      rfl
  simp only [flowMatrix, flowBound, fromRows_mulVec, one_mulVec, neg_mulVec, Sum.elim_le_elim_iff]
  simp only [Pi.le_def, Pi.neg_apply, Pi.zero_apply, neg_nonpos, Prod.forall, hC]
  constructor
  · rintro ⟨hcap, hnn, hle, hge⟩
    refine ⟨hnn, hcap, fun v hs ht => ?_⟩
    have h := le_antisymm (hle v) (hge v)
    rw [ite_eq_right (not_or.mpr ⟨hs, ht⟩)] at h
    exact sub_eq_zero.mp h
  · rintro ⟨hnn, hcap, hcons⟩
    have h0 : ∀ v, (if v = s ∨ v = t then (0 : K) else ∑ u, f (u, v) - ∑ w, f (v, w)) = 0 := by
      intro v
      split_ifs with h
      · rfl
      · rw [not_or] at h
        rw [hcons v h.1 h.2, sub_self]
    exact ⟨hcap, hnn, fun v => (h0 v).le, fun v => (h0 v).ge⟩

/-- The value `realNetOut f s` as a linear objective. -/
private def valueCoeff (s : V) : V × V → K :=
  -inflow s

omit [LinearOrder K] [IsStrictOrderedRing K] in
private theorem valueCoeff_dotProduct (s : V) (f : V × V → K) :
    valueCoeff s ⬝ᵥ f = realNetOut f s := by
  rw [valueCoeff, neg_dotProduct, inflow_dotProduct, realNetOut]
  ring

omit [DecidableEq V] in
/-- For non-negative capacities a maximum flow exists. Since the capacities need not be integers,
it is obtained from linear-programming duality over `K` rather than from augmenting paths. -/
theorem exists_isMaxRealFlow (hW : ∀ u v, 0 ≤ W u v) (s t : V) :
    ∃ f, IsFeasibleRealFlow W s t f ∧ IsMaxRealFlow W s t (realNetOut f s) := by
  classical
  have himage : (realNetOut · s) '' {f | IsFeasibleRealFlow W s t f} =
      (valueCoeff s ⬝ᵥ ·) '' {x | flowMatrix s t *ᵥ x ≤ flowBound W} := by
    have hset : {f | IsFeasibleRealFlow W s t f} = {x | flowMatrix s t *ᵥ x ≤ flowBound W} :=
      Set.ext fun _ => flowMatrix_mulVec_le_iff.symm
    rw [hset]
    congr 1
    funext x
    exact (valueCoeff_dotProduct s x).symm
  have hzero : IsFeasibleRealFlow W s t 0 :=
    ⟨fun _ _ => le_rfl, fun u v => hW u v, fun _ _ _ => by simp⟩
  have hbdd : BddAbove ((valueCoeff s ⬝ᵥ ·) '' {x | flowMatrix s t *ᵥ x ≤ flowBound W}) := by
    refine ⟨∑ w, W s w, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    have hx' := flowMatrix_mulVec_le_iff.mp hx
    have hout : ∑ w, x (s, w) ≤ ∑ w, W s w := sum_le_sum fun w _ => hx'.2.1 s w
    have hin : 0 ≤ ∑ u, x (u, s) := sum_nonneg fun u _ => hx'.1 u s
    refine (valueCoeff_dotProduct s x).trans_le ?_
    rw [realNetOut]
    linarith
  obtain ⟨f, hf, hmax⟩ := exists_isGreatest_of_bddAbove (flowMatrix s t) (flowBound W)
    (valueCoeff s) ⟨0, flowMatrix_mulVec_le_iff.mpr hzero⟩ hbdd
  refine ⟨f, flowMatrix_mulVec_le_iff.mp hf, ?_⟩
  rw [IsMaxRealFlow, himage, ← valueCoeff_dotProduct]
  exact hmax

/-! ### Max-flow min-cut -/

/-- The arc `(u, v)` has positive residual capacity for `f`: unused capacity on `(u, v)` or
cancellable flow on `(v, u)`. -/
private def Residual (W : V → V → K) (f : V × V → K) (u v : V) : Prop :=
  f (u, v) < W u v ∨ 0 < f (v, u)

/-- A value between `a` and `a + μ * d` stays above a common lower bound. -/
private theorem le_add_mul_of_le {lo a d μ μ' : K} (h₀ : 0 ≤ μ') (h₁ : μ' ≤ μ) (ha : lo ≤ a)
    (had : lo ≤ a + μ * d) : lo ≤ a + μ' * d := by
  rcases le_total 0 d with hd | hd
  · nlinarith [mul_nonneg h₀ hd]
  · nlinarith [mul_le_mul_of_nonpos_right h₁ hd]

/-- A value between `a` and `a + μ * d` stays below a common upper bound. -/
private theorem add_mul_le_of_le {hi a d μ μ' : K} (h₀ : 0 ≤ μ') (h₁ : μ' ≤ μ) (ha : a ≤ hi)
    (had : a + μ * d ≤ hi) : a + μ' * d ≤ hi := by
  rcases le_total 0 d with hd | hd
  · nlinarith [mul_le_mul_of_nonneg_right h₁ hd]
  · nlinarith [mul_nonpos_of_nonneg_of_nonpos h₀ hd]

/-- If `v` is reachable from `s` in the residual graph of `f`, some direction `d` sends one unit
from `s` to `v` (net outflow `1` at `s`, `-1` at `v`, `0` elsewhere when `s ≠ v`), and a positive
multiple `μ • d` can be added to `f` within the capacities. -/
private theorem exists_augmentation (hnn : ∀ e, 0 ≤ f e) (hcap : ∀ e, f e ≤ W e.1 e.2) {v : V}
    (hv : Relation.ReflTransGen (Residual W f) s v) :
    ∃ d : V × V → K, ∃ μ : K, 0 < μ ∧
      (∀ x, realNetOut d x = (if x = s then 1 else 0) - (if x = v then 1 else 0)) ∧
      ∀ e, 0 ≤ f e + μ * d e ∧ f e + μ * d e ≤ W e.1 e.2 := by
  induction hv with
  | refl =>
    refine ⟨0, 1, one_pos, fun x => by simp [realNetOut], fun e => ?_⟩
    simpa using ⟨hnn e, hcap e⟩
  | @tail v w _ hvw ih =>
    obtain ⟨d, μ, hμ, hnet, hb⟩ := ih
    -- One more residual step `(v, w)`: either push along `(v, w)` or cancel along `(w, v)`.
    suffices step : ∀ (e₀ : V × V) (σ r : K), 0 < r →
        (∀ x, realNetOut (Pi.single e₀ σ) x =
          (if x = v then 1 else 0) - (if x = w then 1 else 0)) →
        (∀ μ', 0 ≤ μ' → μ' ≤ μ → μ' * (|d e₀| + 1) ≤ r →
          0 ≤ f e₀ + μ' * (d e₀ + σ) ∧ f e₀ + μ' * (d e₀ + σ) ≤ W e₀.1 e₀.2) →
        ∃ d : V × V → K, ∃ μ : K, 0 < μ ∧
          (∀ x, realNetOut d x = (if x = s then 1 else 0) - (if x = w then 1 else 0)) ∧
          ∀ e, 0 ≤ f e + μ * d e ∧ f e + μ * d e ≤ W e.1 e.2 by
      by_cases hfwd : f (v, w) < W v w
      · refine step (v, w) 1 (W v w - f (v, w)) (by linarith) (realNetOut_single v w 1) ?_
        intro μ' h₀ h₁ hr
        have hle : μ' * (d (v, w) + 1) ≤ μ' * (|d (v, w)| + 1) :=
          mul_le_mul_of_nonneg_left (by linarith [le_abs_self (d (v, w))]) h₀
        have hlo := le_add_mul_of_le h₀ h₁ (hnn (v, w)) (hb (v, w)).1
        constructor <;> nlinarith
      · have hbwd : 0 < f (w, v) := hvw.resolve_left hfwd
        refine step (w, v) (-1) (f (w, v)) hbwd (fun x => ?_) ?_
        · rw [realNetOut_single]
          split_ifs <;> ring
        · intro μ' h₀ h₁ hr
          have hle : μ' * (-(|d (w, v)|) - 1) ≤ μ' * (d (w, v) - 1) :=
            mul_le_mul_of_nonneg_left (by linarith [neg_abs_le (d (w, v))]) h₀
          have hhi := add_mul_le_of_le h₀ h₁ (hcap (w, v)) (hb (w, v)).2
          constructor <;> nlinarith
    intro e₀ σ r hr hsingle hmove
    have hpos : 0 < |d e₀| + 1 := by positivity
    refine ⟨d + Pi.single e₀ σ, min μ (r / (|d e₀| + 1)), lt_min hμ (div_pos hr hpos),
      fun x => ?_, fun e => ?_⟩
    · rw [realNetOut_add, hnet, hsingle]
      ring
    · have h₀ : 0 ≤ min μ (r / (|d e₀| + 1)) := (lt_min hμ (div_pos hr hpos)).le
      have h₁ : min μ (r / (|d e₀| + 1)) ≤ μ := min_le_left _ _
      by_cases he : e = e₀
      · subst he
        simpa using hmove _ h₀ h₁ ((le_div_iff₀ hpos).mp (min_le_right _ _))
      · simp only [Pi.add_apply, Pi.single_eq_of_ne he, add_zero]
        exact ⟨le_add_mul_of_le h₀ h₁ (hnn e) (hb e).1, add_mul_le_of_le h₀ h₁ (hcap e) (hb e).2⟩

/-- **Max-flow min-cut theorem** over a linearly ordered field ([Schrijver2003], Theorem 10.3,
p. 150, extended from `ℝ` to `K`; [FordFulkerson1962], Chapter I, Sections 4–8): for non-negative
capacities `W` and distinct `s` and `t`, the greatest value of a feasible `s`–`t` flow is the
minimum `s`–`t` cut weight. The maximum is attained (`exists_isMaxRealFlow`). -/
theorem isMaxRealFlow_minRealCutBetween (hW : ∀ u v, 0 ≤ W u v) (hst : s ≠ t) :
    IsMaxRealFlow W s t (minRealCutBetween W s t) := by
  classical
  obtain ⟨f, hf, hmax⟩ := exists_isMaxRealFlow hW s t
  suffices h : realNetOut f s = minRealCutBetween W s t from h ▸ hmax
  apply le_antisymm
  · obtain ⟨X, hs, ht, hX⟩ := exists_cutWeight_eq_minRealCutBetween W hst
    exact hX ▸ hf.realNetOut_le_cutWeight hs ht
  -- The vertices reachable from `s` in the residual graph form a cut of weight `realNetOut f s`.
  let X : Finset V := univ.filter (Relation.ReflTransGen (Residual W f) s)
  have hsX : s ∈ X := mem_filter.mpr ⟨mem_univ s, Relation.ReflTransGen.refl⟩
  have htX : t ∉ X := by
    intro htX
    obtain ⟨d, μ, hμ, hnet, hb⟩ := exists_augmentation (fun e => hf.1 e.1 e.2)
      (fun e => hf.2.1 e.1 e.2) (mem_filter.mp htX).2
    have hfeas : IsFeasibleRealFlow W s t (f + μ • d) := by
      refine ⟨fun u v => (hb (u, v)).1, fun u v => (hb (u, v)).2, fun v hvs hvt => ?_⟩
      have h : realNetOut (f + μ • d) v = 0 := by
        rw [realNetOut_add, realNetOut_smul, hnet, hf.realNetOut_eq_zero hvs hvt]
        simp [hvs, hvt]
      rw [realNetOut, sub_eq_zero] at h
      exact h.symm
    have hgt : realNetOut f s < realNetOut (f + μ • d) s := by
      rw [realNetOut_add, realNetOut_smul, hnet]
      rw [ite_eq_left rfl, ite_eq_right hst, sub_zero, mul_one]
      linarith
    exact (hmax.2 ⟨_, hfeas, rfl⟩).not_gt hgt
  have hsat : ∀ u ∈ X, ∀ v ∈ univ \ X, f (u, v) = W u v ∧ f (v, u) = 0 := by
    intro u hu v hv
    have hres : ¬ Residual W f u v := fun h =>
      (mem_sdiff.mp hv).2 (mem_filter.mpr ⟨mem_univ v, (mem_filter.mp hu).2.tail h⟩)
    simp only [Residual, not_or, not_lt] at hres
    exact ⟨le_antisymm (hf.2.1 u v) hres.1, le_antisymm hres.2 (hf.1 v u)⟩
  have hval : realNetOut f s = cutWeight W X := by
    rw [hf.realNetOut_eq_sub hsX htX, cutWeight,
      sum_congr rfl fun u hu => sum_congr rfl fun v hv => (hsat u hu v hv).1,
      sum_eq_zero fun u hu => sum_eq_zero fun v hv => (hsat u hu v hv).2, sub_zero]
  exact hval ▸ minRealCutBetween_le_cutWeight W hsX htX

end Cslib.Algorithms.Lean.MaxFlow
