/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.Simplex.Dictionary
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Module.Defs
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Order.Bounds.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Linarith

/-!
# The simplex method with Bland's rule

This module formalizes Bland's smallest-subscript pivoting rule ([Bland1977]; [Chvatal1983],
Chapter 3) for the simplex method on the dictionaries of
`CslibFrontier.Algorithms.Lean.Simplex.Dictionary`, proves that it never cycles, and derives
termination and correctness of the simplex method started from a feasible dictionary.

## Algorithm

In a dictionary `D` (`blandStep`):

* if no nonbasic variable has a positive reduced cost, `D` is optimal;
* otherwise the entering variable `s` is the smallest nonbasic variable with a positive reduced
  cost (`blandEntering`);
* if no basic variable has `coeff i s < 0`, the objective is unbounded along the edge of `s`;
* otherwise the leaving variable is the smallest basic variable among those with
  `coeff i s < 0` minimizing the ratio `rhs i / -coeff i s` (`blandLeaving`), and the method
  pivots.

`run D fuel` iterates at most `fuel` pivots, and `simplex D` runs with fuel
`(Fintype.card ι).choose #D.basis - 1`.

## Source mapping

The rule is Bland's smallest-subscript rule ([Bland1977]; [Chvatal1983], Chapter 3), with
variables ordered by the linear order on `ι`. `basis_ne_of_blandPivot` is the theorem that the
rule does not cycle: along any sequence of Bland pivots from a feasible dictionary, no basis
repeats. The proof is the standard argument: in a cycle every pivot is degenerate, so all
dictionaries of the cycle share one basic solution and one objective value; let `t` be the
largest variable that is basic in some dictionary of the cycle and nonbasic in another, `E p` a
dictionary where `t` leaves with `s` entering, and `E q` one where `t` enters. Evaluating the
objective rows of `E p` and `E q` along the edge of `s` in `E p`, where they agree because the
two dictionaries are equivalent, produces a variable `v < t` that ties with `t` in the ratio test
of `E p`, contradicting the choice of `t` as the leaving variable. Since pivots preserve the
number of basic variables, at most `N.choose m` bases occur, where `N = Fintype.card ι` and
`m = #D.basis` (`add_one_le_choose_of_blandPivot`).

## Main definitions

* `Cslib.Algorithms.Lean.Simplex.minOpt`: the smallest element of a finite set, as an `Option`.
* `Cslib.Algorithms.Lean.Simplex.Step`, `Cslib.Algorithms.Lean.Simplex.Outcome`: the decision of
  one simplex step and the result of a run.
* `Cslib.Algorithms.Lean.Simplex.Dictionary.blandEntering`,
  `Cslib.Algorithms.Lean.Simplex.Dictionary.blandLeaving`,
  `Cslib.Algorithms.Lean.Simplex.Dictionary.blandStep`: Bland's rule.
* `Cslib.Algorithms.Lean.Simplex.Dictionary.BlandPivot`: one pivot by Bland's rule.
* `Cslib.Algorithms.Lean.Simplex.Dictionary.run`,
  `Cslib.Algorithms.Lean.Simplex.Dictionary.simplex`: the simplex method with Bland's rule.

## Main results

* `Dictionary.basis_ne_of_blandPivot`: **Bland's rule does not cycle.**
* `Dictionary.add_one_le_choose_of_blandPivot`: at most `N.choose m - 1` Bland pivots occur.
* `Dictionary.run_ne_outOfFuel`, `Dictionary.simplex_ne_outOfFuel`: termination.
* `Dictionary.simplex_spec`: started from a feasible dictionary, the simplex method returns an
  equivalent feasible dictionary whose basic solution is optimal, or detects that the objective
  is unbounded on the feasible set.

## Limitations

A feasible starting dictionary is assumed; Phase I (finding one, or detecting infeasibility) is
not formalized. The method is a pure Lean function over an exact field; no machine-level running
time or bit complexity is certified.

## References

* [R. G. Bland, *New finite pivoting rules for the simplex method*][Bland1977]
* [V. Chvátal, *Linear Programming*][Chvatal1983]
-/

public section

namespace Cslib.Algorithms.Lean.Simplex

/-- The smallest element of a finite set, if any. This is Mathlib's `Finset.min` with the result
in `Option ι` rather than `WithTop ι`; the simplex step matches on it directly, and the worked
examples evaluate it with `decide +kernel`. -/
@[expose] def minOpt {ι : Type*} [LinearOrder ι] (s : Finset ι) : Option ι :=
  if h : s.Nonempty then some (s.min' h) else none

theorem minOpt_eq_none_iff {ι : Type*} [LinearOrder ι] {s : Finset ι} :
    minOpt s = none ↔ s = ∅ := by
  unfold minOpt
  split_ifs with h
  · simp only [false_iff]
    exact h.ne_empty
  · simp only [true_iff]
    exact Finset.not_nonempty_iff_eq_empty.1 h

theorem minOpt_eq_some_iff {ι : Type*} [LinearOrder ι] {s : Finset ι} {a : ι} :
    minOpt s = some a ↔ a ∈ s ∧ ∀ b ∈ s, a ≤ b := by
  unfold minOpt
  split_ifs with h
  · rw [Option.some.injEq]
    constructor
    · rintro rfl
      exact ⟨s.min'_mem h, fun b hb => s.min'_le b hb⟩
    · rintro ⟨ha, hle⟩
      exact le_antisymm (s.min'_le a ha) (hle _ (s.min'_mem h))
  · simp only [false_iff, not_and]
    exact fun ha => absurd ⟨a, ha⟩ h

/-- The decision of one simplex step: stop at an optimal dictionary, stop because the entering
variable `s` has no leaving row, or pivot on the leaving `r` and the entering `s`. -/
inductive Step (ι : Type*)
  | optimal
  | unbounded (s : ι)
  | pivot (r s : ι)

/-- The result of a run of the simplex method: an optimal dictionary, a dictionary with an
unbounded entering variable `s`, or the dictionary reached when the fuel ran out. -/
inductive Outcome (ι K : Type*)
  | optimal (D : Dictionary ι K)
  | unbounded (D : Dictionary ι K) (s : ι)
  | outOfFuel (D : Dictionary ι K)

namespace Dictionary

open Finset

variable {ι K : Type*} [Fintype ι] [LinearOrder ι] [Field K] [LinearOrder K]
  [IsStrictOrderedRing K] (D : Dictionary ι K)

/-! ### Bland's rule -/

/-- The nonbasic variables with a positive reduced cost. -/
@[expose] def enteringCandidates : Finset ι := D.basisᶜ.filter (0 < D.objCoeff ·)

/-- The basic variables whose rows decrease along the edge of `s`. -/
@[expose] def leavingCandidates (s : ι) : Finset ι := D.basis.filter (D.coeff · s < 0)

/-- The leaving candidates of minimal ratio. -/
@[expose] def minRatioCandidates (s : ι) : Finset ι :=
  (D.leavingCandidates s).filter fun i => ∀ k ∈ D.leavingCandidates s, D.ratio s i ≤ D.ratio s k

/-- **Bland's entering rule** ([Bland1977]): the smallest nonbasic variable with a positive
reduced cost. -/
@[expose] def blandEntering : Option ι := minOpt D.enteringCandidates

/-- **Bland's leaving rule** ([Bland1977]): among the rows passing the ratio test for the
entering variable `s`, the smallest basic variable. -/
@[expose] def blandLeaving (s : ι) : Option ι := minOpt (D.minRatioCandidates s)

/-- One step of the simplex method with Bland's rule. -/
@[expose] def blandStep : Step ι :=
  match D.blandEntering with
  | none => .optimal
  | some s =>
    match D.blandLeaving s with
    | none => .unbounded s
    | some r => .pivot r s

omit [IsStrictOrderedRing K] in
theorem blandEntering_eq_none_iff :
    D.blandEntering = none ↔ ∀ j ∉ D.basis, D.objCoeff j ≤ 0 := by
  rw [blandEntering, minOpt_eq_none_iff, Finset.eq_empty_iff_forall_notMem]
  simp only [enteringCandidates, Finset.mem_filter, Finset.mem_compl, not_and, not_lt]

omit [IsStrictOrderedRing K] in
theorem blandEntering_eq_some_iff {s : ι} : D.blandEntering = some s ↔
    s ∉ D.basis ∧ 0 < D.objCoeff s ∧ ∀ j ∉ D.basis, 0 < D.objCoeff j → s ≤ j := by
  rw [blandEntering, minOpt_eq_some_iff]
  simp only [enteringCandidates, Finset.mem_filter, Finset.mem_compl, and_imp, and_assoc]

omit [IsStrictOrderedRing K] in
theorem blandLeaving_eq_none_iff {s : ι} :
    D.blandLeaving s = none ↔ ∀ i ∈ D.basis, 0 ≤ D.coeff i s := by
  rw [blandLeaving, minOpt_eq_none_iff]
  constructor
  · intro h i hi
    by_contra hneg
    push Not at hneg
    have hne : (D.leavingCandidates s).Nonempty := ⟨i, Finset.mem_filter.2 ⟨hi, hneg⟩⟩
    obtain ⟨k, hk, hmin⟩ := (D.leavingCandidates s).exists_min_image (D.ratio s) hne
    have : k ∈ D.minRatioCandidates s := Finset.mem_filter.2 ⟨hk, hmin⟩
    rw [h] at this
    exact Finset.notMem_empty k this
  · intro h
    refine Finset.eq_empty_of_forall_notMem fun i hi => ?_
    obtain ⟨hi, hneg⟩ := Finset.mem_filter.1 (Finset.mem_filter.1 hi).1
    exact (h i hi).not_gt hneg

omit [IsStrictOrderedRing K] in
theorem blandLeaving_eq_some_iff {s r : ι} : D.blandLeaving s = some r ↔
    r ∈ D.basis ∧ D.coeff r s < 0 ∧
      (∀ i ∈ D.basis, D.coeff i s < 0 → D.ratio s r ≤ D.ratio s i) ∧
      ∀ i ∈ D.basis, D.coeff i s < 0 → D.ratio s i = D.ratio s r → r ≤ i := by
  rw [blandLeaving, minOpt_eq_some_iff]
  simp only [minRatioCandidates, leavingCandidates, Finset.mem_filter, and_imp, and_assoc]
  constructor
  · rintro ⟨hr, har, hmin, hle⟩
    exact ⟨hr, har, hmin, fun i hi hai heq => hle i hi hai fun k hk hak => heq ▸ hmin k hk hak⟩
  · rintro ⟨hr, har, hmin, hle⟩
    exact ⟨hr, har, hmin, fun i hi hai himin =>
      hle i hi hai (le_antisymm (himin r hr har) (hmin i hi hai))⟩

omit [IsStrictOrderedRing K] in
theorem blandStep_eq_optimal_iff : D.blandStep = .optimal ↔ D.blandEntering = none := by
  rcases h1 : D.blandEntering with _ | s'
  · simp only [blandStep, h1]
  · rcases h2 : D.blandLeaving s' with _ | r' <;> simp only [blandStep, h1, h2, reduceCtorEq]

omit [IsStrictOrderedRing K] in
theorem blandStep_eq_unbounded_iff {s : ι} :
    D.blandStep = .unbounded s ↔ D.blandEntering = some s ∧ D.blandLeaving s = none := by
  unfold blandStep
  rcases D.blandEntering with _ | s'
  · simp
  · rcases h2 : D.blandLeaving s' with _ | r' <;> grind

omit [IsStrictOrderedRing K] in
theorem blandStep_eq_pivot_iff {r s : ι} :
    D.blandStep = .pivot r s ↔ D.blandEntering = some s ∧ D.blandLeaving s = some r := by
  unfold blandStep
  rcases D.blandEntering with _ | s'
  · simp
  · rcases h2 : D.blandLeaving s' with _ | r' <;> grind

/-- `D'` arises from `D` by one pivot of Bland's rule. -/
def BlandPivot (D D' : Dictionary ι K) : Prop :=
  ∃ r s, D.blandStep = .pivot r s ∧ D' = D.pivot r s

variable {D}

theorem BlandPivot.feasible {D' : Dictionary ι K} (h : D.BlandPivot D') (hD : D.Feasible) :
    D'.Feasible := by
  obtain ⟨r, s, hstep, rfl⟩ := h
  obtain ⟨hs, hr⟩ := D.blandStep_eq_pivot_iff.1 hstep
  obtain ⟨hs, -, -⟩ := D.blandEntering_eq_some_iff.1 hs
  obtain ⟨hr, har, hmin, -⟩ := D.blandLeaving_eq_some_iff.1 hr
  exact D.feasible_pivot hD hr hs har hmin

omit [IsStrictOrderedRing K] in
theorem BlandPivot.equivalent {D' : Dictionary ι K} (h : D.BlandPivot D') :
    D.Equivalent D' := by
  obtain ⟨r, s, hstep, rfl⟩ := h
  obtain ⟨hs, hr⟩ := D.blandStep_eq_pivot_iff.1 hstep
  obtain ⟨hs, -, -⟩ := D.blandEntering_eq_some_iff.1 hs
  obtain ⟨hr, har, -, -⟩ := D.blandLeaving_eq_some_iff.1 hr
  exact D.equivalent_pivot hr hs har.ne

theorem BlandPivot.objConst_le {D' : Dictionary ι K} (h : D.BlandPivot D')
    (hD : D.Feasible) : D.objConst ≤ D'.objConst := by
  obtain ⟨r, s, hstep, rfl⟩ := h
  obtain ⟨hs, hr⟩ := D.blandStep_eq_pivot_iff.1 hstep
  obtain ⟨-, hc, -⟩ := D.blandEntering_eq_some_iff.1 hs
  obtain ⟨hr, har, -, -⟩ := D.blandLeaving_eq_some_iff.1 hr
  exact D.objConst_le_pivot hD hr har hc.le

omit [IsStrictOrderedRing K] in
theorem BlandPivot.card_basis {D' : Dictionary ι K} (h : D.BlandPivot D') :
    #D'.basis = #D.basis := by
  obtain ⟨r, s, hstep, rfl⟩ := h
  obtain ⟨hs, hr⟩ := D.blandStep_eq_pivot_iff.1 hstep
  obtain ⟨hs, -, -⟩ := D.blandEntering_eq_some_iff.1 hs
  obtain ⟨hr, -, -, -⟩ := D.blandLeaving_eq_some_iff.1 hr
  exact D.card_pivot_basis hr hs

/-- A discrete intermediate value property. -/
private theorem exists_flip {P : ℕ → Prop} {a b : ℕ} (hab : a ≤ b) (ha : P a) (hb : ¬P b) :
    ∃ k, a ≤ k ∧ k < b ∧ P k ∧ ¬P (k + 1) := by
  induction b, hab using Nat.le_induction with
  | base => exact absurd ha hb
  | succ b hab ih =>
    by_cases hPb : P b
    · exact ⟨b, hab, Nat.lt_succ_self b, hPb, hb⟩
    · obtain ⟨k, hak, hkb, hk, hk'⟩ := ih hPb
      exact ⟨k, hak, hkb.trans (Nat.lt_succ_self b), hk, hk'⟩

/-- **Bland's rule does not cycle** ([Bland1977]; [Chvatal1983], Chapter 3): along any sequence
of Bland pivots from a feasible dictionary, no basis repeats. -/
theorem basis_ne_of_blandPivot {E : ℕ → Dictionary ι K} {n : ℕ} (hE0 : (E 0).Feasible)
    (hE : ∀ k < n, (E k).BlandPivot (E (k + 1))) {i j : ℕ} (hij : i < j) (hjn : j ≤ n) :
    (E i).basis ≠ (E j).basis := by
  classical
  intro hB
  -- invariants
  have hfeas : ∀ k ≤ n, (E k).Feasible := by
    intro k hk
    induction k with
    | zero => exact hE0
    | succ k ih => exact (hE k (by omega)).feasible (ih (by omega))
  have hequiv : ∀ k, i ≤ k → k ≤ n → (E i).Equivalent (E k) := by
    intro k hik hkn
    induction k, hik using Nat.le_induction with
    | base => exact .refl _
    | succ k hik ih => exact (ih (by omega)).trans (hE k (by omega)).equivalent
  have hmono : ∀ k l, k ≤ l → l ≤ n → (E k).objConst ≤ (E l).objConst := by
    intro k l hkl hln
    induction l, hkl using Nat.le_induction with
    | base => exact le_rfl
    | succ l hkl ih => exact (ih (by omega)).trans ((hE l (by omega)).objConst_le
        (hfeas l (by omega)))
  -- the basic solutions of `E i` and `E j` agree, hence so do the objective values
  have hsolj : (E j).basicSolution = (E i).basicSolution :=
    (E i).eq_basicSolution_of_isSolution
      (((hequiv j hij.le hjn).isSolution_iff _).2 (E j).isSolution_basicSolution)
      fun k hk => (E j).basicSolution_of_notMem (hB ▸ hk)
  have hval : (E j).objConst = (E i).objConst := by
    rw [← (E j).value_basicSolution, ← ((hequiv j hij.le hjn).value_eq _
      (((hequiv j hij.le hjn).isSolution_iff _).2 (E j).isSolution_basicSolution)), hsolj,
      value_basicSolution]
  have hconst : ∀ k, i ≤ k → k ≤ j → (E k).objConst = (E i).objConst := fun k hik hkj =>
    le_antisymm (hval ▸ hmono k j hkj hjn) (hmono i k hik (hkj.trans hjn))
  -- every pivot in the cycle is degenerate
  have hsol : ∀ k, i ≤ k → k ≤ j → (E k).basicSolution = (E i).basicSolution := by
    intro k hik hkj
    induction k, hik using Nat.le_induction with
    | base => rfl
    | succ k hik ih =>
      obtain ⟨r, s, hstep, hEk⟩ := hE k (by omega)
      obtain ⟨hs, hr⟩ := (E k).blandStep_eq_pivot_iff.1 hstep
      obtain ⟨hs, hc, -⟩ := (E k).blandEntering_eq_some_iff.1 hs
      obtain ⟨hr, har, -, -⟩ := (E k).blandLeaving_eq_some_iff.1 hr
      have h0 : (E k).ratio s r = 0 := by
        have h1 := hconst k hik (by omega)
        have h2 := hconst (k + 1) (by omega) hkj
        rw [hEk, objConst_pivot, h1] at h2
        rcases mul_eq_zero.1 (by linarith : (E k).objCoeff s * (E k).ratio s r = 0) with h | h
        · exact absurd h hc.ne'
        · exact h
      rw [hEk, (E k).basicSolution_pivot hr hs har.ne, h0, zero_smul, add_zero, ih (by omega)]
  -- the fickle variables: basic somewhere in the cycle and nonbasic somewhere else
  set F : Finset ι := Finset.univ.filter fun v =>
    ∃ k ∈ Finset.Icc i j, ∃ l ∈ Finset.Icc i j, v ∈ (E k).basis ∧ v ∉ (E l).basis with hF
  have hFmem : ∀ v, v ∈ F ↔ ∃ k, i ≤ k ∧ k ≤ j ∧ ∃ l, i ≤ l ∧ l ≤ j ∧
      v ∈ (E k).basis ∧ v ∉ (E l).basis := by
    intro v
    simp only [hF, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Icc, and_assoc]
  have hFne : F.Nonempty := by
    obtain ⟨r, s, hstep, hEk⟩ := hE i (by omega)
    obtain ⟨hs, -⟩ := (E i).blandStep_eq_pivot_iff.1 hstep
    obtain ⟨hs, -, -⟩ := (E i).blandEntering_eq_some_iff.1 hs
    refine ⟨s, (hFmem s).2 ⟨i + 1, by omega, by omega, i, le_rfl, hij.le, ?_, hs⟩⟩
    rw [hEk, mem_pivot_basis]
    exact .inl rfl
  obtain ⟨t, htF, hleT⟩ : ∃ t ∈ F, ∀ v ∈ F, v ≤ t :=
    ⟨F.max' hFne, F.max'_mem hFne, fun v hv => F.le_max' v hv⟩
  -- find a step `p` where `t` leaves and a step `q` where `t` enters
  obtain ⟨p, q, hip, hpj, hiq, hqj, htp, htp', htq, htq'⟩ : ∃ p q, i ≤ p ∧ p < j ∧ i ≤ q ∧
      q < j ∧ t ∈ (E p).basis ∧ t ∉ (E (p + 1)).basis ∧ t ∉ (E q).basis ∧
      t ∈ (E (q + 1)).basis := by
    obtain ⟨k₀, hik₀, hk₀j, l₀, hil₀, hl₀j, hk₀, hl₀⟩ := (hFmem t).1 htF
    by_cases hti : t ∈ (E i).basis
    · obtain ⟨p, hip, hpl, hp, hp'⟩ :=
        exists_flip (P := fun k => t ∈ (E k).basis) hil₀ hti hl₀
      obtain ⟨q, hlq, hqj, hq, hq'⟩ :=
        exists_flip (P := fun k => t ∉ (E k).basis) hl₀j hl₀
          (by rw [not_not, ← hB]; exact hti)
      exact ⟨p, q, hip, by omega, by omega, hqj, hp, hp', hq, not_not.1 hq'⟩
    · obtain ⟨q, hiq, hqk, hq, hq'⟩ :=
        exists_flip (P := fun k => t ∉ (E k).basis) hik₀ hti (not_not.2 hk₀)
      obtain ⟨p, hkp, hpj, hp, hp'⟩ :=
        exists_flip (P := fun k => t ∈ (E k).basis) hk₀j hk₀ (by rw [← hB]; exact hti)
      exact ⟨p, q, by omega, hpj, hiq, by omega, hp, hp', hq, not_not.1 hq'⟩
  -- at step `p`, `s` enters and `t` leaves
  obtain ⟨r, s, hstepp, hEp⟩ := hE p (by omega)
  obtain ⟨hsp, hrp⟩ := (E p).blandStep_eq_pivot_iff.1 hstepp
  obtain ⟨hs, hcs, -⟩ := (E p).blandEntering_eq_some_iff.1 hsp
  have hrt : t = r := by
    by_contra hrt
    rw [hEp, mem_pivot_basis] at htp'
    exact htp' (.inr ⟨htp, hrt⟩)
  subst r
  obtain ⟨hr, har, hmin, htie⟩ := (E p).blandLeaving_eq_some_iff.1 hrp
  have hsF : s ∈ F :=
    (hFmem s).2 ⟨p + 1, by omega, by omega, p, hip, hpj.le,
      by rw [hEp, mem_pivot_basis]; exact .inl rfl, hs⟩
  have hsr : s < t := lt_of_le_of_ne (hleT s hsF) fun h => hs (h ▸ hr)
  -- at step `q`, `t` enters
  obtain ⟨r', s', hstepq, hEq⟩ := hE q (by omega)
  obtain ⟨hsq, -⟩ := (E q).blandStep_eq_pivot_iff.1 hstepq
  have hs't : s' = t := by
    by_contra hs't
    rw [hEq, mem_pivot_basis] at htq'
    rcases htq' with h | ⟨h, -⟩
    · exact hs't h.symm
    · exact htq h
  subst s'
  obtain ⟨-, hcq, hminq⟩ := (E q).blandEntering_eq_some_iff.1 hsq
  -- compare the objective rows of `E p` and `E q` along the edge of `s`
  set x := (E p).basicSolution + (1 : K) • (E p).ray s with hx
  have hxp : (E p).IsSolution x :=
    (E p).isSolution_add_smul_ray hs (E p).isSolution_basicSolution 1
  have hpq : (E p).Equivalent (E q) :=
    (hequiv p hip (by omega)).symm.trans (hequiv q hiq (by omega))
  have hvalpq := hpq.value_eq x hxp
  rw [hx, (E p).value_add_smul_ray hs, (E p).value_basicSolution, one_mul] at hvalpq
  have hbs : (E p).basicSolution = (E q).basicSolution := by
    rw [hsol p hip hpj.le, hsol q hiq hqj.le]
  have hvalq : (E q).value ((E p).basicSolution + (1 : K) • (E p).ray s) =
      (E q).objConst + ∑ v ∈ (E q).basisᶜ, (E q).objCoeff v * (E p).ray s v := by
    simp only [value, Pi.add_apply, Pi.smul_apply, smul_eq_mul, one_mul, mul_add,
      Finset.sum_add_distrib, hbs]
    rw [Finset.sum_eq_zero fun v hv => by
      rw [(E q).basicSolution_of_notMem (Finset.mem_compl.1 hv), mul_zero], zero_add]
  rw [hvalq, hconst p hip hpj.le, hconst q hiq hqj.le] at hvalpq
  have hsum : ∑ v ∈ (E q).basisᶜ, (0 : K) <
      ∑ v ∈ (E q).basisᶜ, (E q).objCoeff v * (E p).ray s v := by
    rw [Finset.sum_const_zero]
    linarith
  obtain ⟨v, hv, hpos⟩ := Finset.exists_lt_of_sum_lt hsum
  have hvq : v ∉ (E q).basis := Finset.mem_compl.1 hv
  by_cases hvs : v = s
  · rw [hvs, (E p).ray_self, mul_one] at hpos
    exact absurd (hminq s (hvs ▸ hvq) hpos) (not_le.2 hsr)
  by_cases hvp : v ∈ (E p).basis
  swap
  · rw [(E p).ray_of_notMem hvp hvs, mul_zero] at hpos
    exact lt_irrefl _ hpos
  rw [(E p).ray_of_mem hvp hs] at hpos
  have hvF : v ∈ F := (hFmem v).2 ⟨p, hip, hpj.le, q, hiq, hqj.le, hvp, hvq⟩
  have hvr : v ≠ t := by
    rintro rfl
    exact absurd hpos (not_lt.2 (mul_nonpos_of_nonneg_of_nonpos hcq.le har.le))
  have hvlt : v < t := lt_of_le_of_ne (hleT v hvF) hvr
  have hcv : (E q).objCoeff v ≤ 0 := by
    by_contra h
    exact absurd (hminq v hvq (not_le.1 h)) (not_le.2 hvlt)
  have hav : (E p).coeff v s < 0 := by
    rcases mul_pos_iff.1 hpos with ⟨h, -⟩ | ⟨-, h⟩
    · exact absurd h (not_lt.2 hcv)
    · exact h
  -- `v` is basic at value `0` in `E p`, so it ties with `t` in the ratio test
  have hv0 : (E p).ratio s v = 0 := by
    have : (E p).rhs v = 0 := by
      rw [← (E p).basicSolution_of_mem hvp, hbs, (E q).basicSolution_of_notMem hvq]
    rw [ratio, this, zero_div]
  have hr0 : (E p).ratio s t = 0 :=
    le_antisymm (hv0 ▸ hmin v hvp hav) ((E p).ratio_nonneg (hfeas p (by omega)) hr har)
  exact absurd (htie v hvp hav (hv0.trans hr0.symm)) (not_le.2 hvlt)

/-- **At most `N.choose m - 1` Bland pivots**: along a sequence of `n` Bland pivots from a
feasible dictionary with `m` basic variables among `N` variables, `n + 1 ≤ N.choose m`. -/
theorem add_one_le_choose_of_blandPivot {E : ℕ → Dictionary ι K} {n : ℕ}
    (hE0 : (E 0).Feasible) (hE : ∀ k < n, (E k).BlandPivot (E (k + 1))) :
    n + 1 ≤ (Fintype.card ι).choose #(E 0).basis := by
  have hcard : ∀ k ≤ n, #(E k).basis = #(E 0).basis := by
    intro k hk
    induction k with
    | zero => rfl
    | succ k ih => rw [(hE k (by omega)).card_basis, ih (by omega)]
  have h := Finset.card_le_card_of_injOn (s := Finset.range (n + 1))
    (t := Finset.powersetCard #(E 0).basis Finset.univ) (fun k => (E k).basis)
    (fun k hk => Finset.mem_powersetCard.2 ⟨Finset.subset_univ _,
      hcard k (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk))⟩)
    (fun k hk l hl hkl => by
      have hk := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
      have hl := Nat.lt_succ_iff.1 (Finset.mem_range.1 hl)
      by_contra hne
      rcases lt_or_gt_of_ne hne with h | h
      · exact basis_ne_of_blandPivot hE0 hE h hl hkl
      · exact basis_ne_of_blandPivot hE0 hE h hk hkl.symm)
  rwa [Finset.card_range, Finset.card_powersetCard, Finset.card_univ] at h

/-! ### The simplex method with Bland's rule -/

variable (D)

/-- The simplex method with Bland's rule and at most `fuel` pivots. -/
@[expose] def run : Dictionary ι K → ℕ → Outcome ι K
  | D, 0 =>
    match D.blandStep with
    | .optimal => .optimal D
    | .unbounded s => .unbounded D s
    | .pivot _ _ => .outOfFuel D
  | D, fuel + 1 =>
    match D.blandStep with
    | .optimal => .optimal D
    | .unbounded s => .unbounded D s
    | .pivot r s => run (D.pivot r s) fuel

/-- **The simplex method with Bland's rule** ([Bland1977]; [Chvatal1983], Chapter 3), with the
fuel `N.choose m - 1` that suffices from a feasible dictionary (`simplex_ne_outOfFuel`). -/
@[expose] def simplex : Outcome ι K := run D ((Fintype.card ι).choose #D.basis - 1)

omit [IsStrictOrderedRing K] in
theorem exists_blandPivot_of_run_eq_outOfFuel {fuel : ℕ} {D' : Dictionary ι K}
    (h : run D fuel = .outOfFuel D') :
    ∃ E : ℕ → Dictionary ι K, E 0 = D ∧ ∀ k < fuel + 1, (E k).BlandPivot (E (k + 1)) := by
  induction fuel generalizing D with
  | zero =>
    rcases hstep : D.blandStep with _ | s | ⟨r, s⟩ <;>
      simp only [run, hstep, reduceCtorEq] at h
    exact ⟨fun k => if k = 0 then D else D.pivot r s, rfl, fun k hk => by
      obtain rfl : k = 0 := by omega
      exact ⟨r, s, hstep, rfl⟩⟩
  | succ fuel ih =>
    rcases hstep : D.blandStep with _ | s | ⟨r, s⟩ <;>
      simp only [run, hstep, reduceCtorEq] at h
    obtain ⟨E, hE0, hE⟩ := ih _ h
    refine ⟨fun k => if k = 0 then D else E (k - 1), rfl, fun k hk => ?_⟩
    rcases k with _ | k
    · simp only [↓reduceIte, Nat.zero_add, one_ne_zero]
      rw [Nat.sub_self, hE0]
      exact ⟨r, s, hstep, rfl⟩
    · simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, Nat.add_sub_cancel]
      exact hE k (by omega)

/-- **Termination of Bland's rule**: from a feasible dictionary, `N.choose m - 1` pivots of fuel
suffice. -/
theorem run_ne_outOfFuel (hD : D.Feasible) {fuel : ℕ}
    (hfuel : (Fintype.card ι).choose #D.basis ≤ fuel + 1) (D' : Dictionary ι K) :
    run D fuel ≠ .outOfFuel D' := by
  intro h
  obtain ⟨E, hE0, hE⟩ := exists_blandPivot_of_run_eq_outOfFuel D h
  subst hE0
  have := add_one_le_choose_of_blandPivot hD hE
  omega

theorem simplex_ne_outOfFuel (hD : D.Feasible) (D' : Dictionary ι K) :
    D.simplex ≠ .outOfFuel D' :=
  D.run_ne_outOfFuel hD (by omega) D'

/-- A run that stops at an optimal dictionary `D'` returns an equivalent feasible dictionary
with no positive reduced cost and an objective value at least that of `D`. -/
theorem run_eq_optimal {fuel : ℕ} {D' : Dictionary ι K} (hD : D.Feasible)
    (h : run D fuel = .optimal D') :
    D.Equivalent D' ∧ D'.Feasible ∧ D.objConst ≤ D'.objConst ∧
      ∀ j ∉ D'.basis, D'.objCoeff j ≤ 0 := by
  induction fuel generalizing D with
  | zero =>
    rcases hstep : D.blandStep with _ | s | ⟨r, s⟩ <;>
      simp only [run, hstep, reduceCtorEq, Outcome.optimal.injEq] at h
    rw [← h]
    exact ⟨.refl _, hD, le_rfl,
      D.blandEntering_eq_none_iff.1 (D.blandStep_eq_optimal_iff.1 hstep)⟩
  | succ fuel ih =>
    rcases hstep : D.blandStep with _ | s | ⟨r, s⟩ <;>
      simp only [run, hstep, reduceCtorEq, Outcome.optimal.injEq] at h
    · rw [← h]
      exact ⟨.refl _, hD, le_rfl,
        D.blandEntering_eq_none_iff.1 (D.blandStep_eq_optimal_iff.1 hstep)⟩
    · have hp : D.BlandPivot (D.pivot r s) := ⟨r, s, hstep, rfl⟩
      obtain ⟨h1, h2, h3, h4⟩ := ih _ (hp.feasible hD) h
      exact ⟨hp.equivalent.trans h1, h2, (hp.objConst_le hD).trans h3, h4⟩

/-- A run that stops with an unbounded entering variable `s` returns an equivalent feasible
dictionary in which `s` is nonbasic with a positive reduced cost and no row bounds its
increase. -/
theorem run_eq_unbounded {fuel : ℕ} {D' : Dictionary ι K} {s : ι} (hD : D.Feasible)
    (h : run D fuel = .unbounded D' s) :
    D.Equivalent D' ∧ D'.Feasible ∧ s ∉ D'.basis ∧ 0 < D'.objCoeff s ∧
      ∀ i ∈ D'.basis, 0 ≤ D'.coeff i s := by
  induction fuel generalizing D with
  | zero =>
    rcases hstep : D.blandStep with _ | s' | ⟨r, s'⟩ <;>
      simp only [run, hstep, reduceCtorEq, Outcome.unbounded.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨h1, h2⟩ := D.blandStep_eq_unbounded_iff.1 hstep
    obtain ⟨hs, hc, -⟩ := D.blandEntering_eq_some_iff.1 h1
    exact ⟨.refl _, hD, hs, hc, D.blandLeaving_eq_none_iff.1 h2⟩
  | succ fuel ih =>
    rcases hstep : D.blandStep with _ | s' | ⟨r, s'⟩ <;>
      simp only [run, hstep, reduceCtorEq, Outcome.unbounded.injEq] at h
    · obtain ⟨rfl, rfl⟩ := h
      obtain ⟨h1, h2⟩ := D.blandStep_eq_unbounded_iff.1 hstep
      obtain ⟨hs, hc, -⟩ := D.blandEntering_eq_some_iff.1 h1
      exact ⟨.refl _, hD, hs, hc, D.blandLeaving_eq_none_iff.1 h2⟩
    · have hp : D.BlandPivot (D.pivot r s') := ⟨r, s', hstep, rfl⟩
      obtain ⟨h1, h2⟩ := ih _ (hp.feasible hD) h
      exact ⟨hp.equivalent.trans h1, h2⟩

/-- **Correctness of the simplex method with Bland's rule** ([Chvatal1983], Chapter 3): from a
feasible dictionary `D` it either stops at an equivalent feasible dictionary whose basic solution
attains the maximum `D'.objConst` of the objective over the feasible set, or detects that the
objective is unbounded above on the feasible set. -/
theorem simplex_spec (hD : D.Feasible) :
    (∃ D', D.simplex = .optimal D' ∧ D.Equivalent D' ∧ D'.Feasible ∧
      IsGreatest (D.value '' D.feasibleSet) D'.objConst) ∨
    ((∃ D' s, D.simplex = .unbounded D' s) ∧ ¬BddAbove (D.value '' D.feasibleSet)) := by
  rcases h : D.simplex with D' | ⟨D', s⟩ | D'
  · obtain ⟨h1, h2, -, h4⟩ := D.run_eq_optimal hD h
    refine .inl ⟨D', rfl, h1, h2, ?_⟩
    rw [D.image_value_feasibleSet_eq h1]
    exact D'.isGreatest_value h2 h4
  · obtain ⟨h1, h2, h3, h4, h5⟩ := D.run_eq_unbounded hD h
    refine .inr ⟨⟨D', s, rfl⟩, ?_⟩
    rw [D.image_value_feasibleSet_eq h1]
    exact D'.not_bddAbove_value h2 h3 h4 h5
  · exact absurd h (D.simplex_ne_outOfFuel hD D')

end Dictionary

end Cslib.Algorithms.Lean.Simplex
