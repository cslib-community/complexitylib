/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Cslib.Algorithms.Lean.TimeM
public import CslibFrontier.Foundations.Algebra.Polynomial.RealRoot.RatPoly
public import Mathlib.FieldTheory.Perfect

/-!
# Certified Real-Root Isolation via Sturm Bisection

This module implements executable Sturm-count bisection over `ℚ[X]` using `TimeM ℕ`-instrumented
list operations (`isolateRootsM` and its pure return value `isolateRoots`), returning sorted
rational isolating intervals `RootInterval`. It proves soundness, completeness, strict root
ordering, exact bijection with the real roots of any squarefree rational polynomial, and an
explicit `TimeM ℕ` count bound from Mignotte's separation theorem.

**Cost model convention.** `isolateRootsM` runs preprocessing (`trim cs`, `sturmSeqList cs`
polynomial divisions, `cauchyBoundNat cs`, and `mignotteBisectionDepth cs` including `lcmDens`,
`clearDenomsList`, `sqNormList`, and `Nat.clog`) outside `TimeM` (`0` ticks), and inside bisection
and left-root refinement charges only `sturmVariationsM` (`sturmSeqOpCost`) and `evalListM`
(`t.length`); rational arithmetic (`(u + v) / 2`), subtraction (`vu - vv`), and list
concatenation (`left ++ right`) are uncharged (`0` ticks).

## Main definitions

* `Cslib.RealRoot.RootInterval`: rational interval `[lower, upper]` together with
  `RootInterval.IsIsolatingFor` and `RootInterval.IsHalfOpenIsolatingFor`.
* `Cslib.RealRoot.sturmSeqOpCost`, `Cslib.RealRoot.evalListM`,
  `Cslib.RealRoot.sturmVariationsM`, `Cslib.RealRoot.refineLeftRootM`,
  `Cslib.RealRoot.isolateIocM`, `Cslib.RealRoot.isolateRootsM`,
  `Cslib.RealRoot.isolateRoots`: computable Sturm-bisection real-root isolator.
* `Cslib.RealRoot.isolatedRoot`: subtype map sending each interval index to the unique real root
  inside that interval.
* `Cslib.RealRoot.isolatePolyRoots`, `Cslib.RealRoot.isolatePolyRootsM`,
  `Cslib.RealRoot.polyIsolatedRoot`: `Polynomial ℚ` wrappers via `Polynomial.coeffsBelow`.

## Main results

* `Cslib.RealRoot.isolateRoots_isIsolatingFor`, `Cslib.RealRoot.isolateRoots_pairwise`,
  `Cslib.RealRoot.isolateRoots_complete`, `Cslib.RealRoot.isolateRoots_length_eq_card_roots`,
  `Cslib.RealRoot.isolatedRoot_strictMono`, `Cslib.RealRoot.isolateRoots_bijective`:
  correctness, ordering, completeness, and strictly monotone bijection onto real roots of any
  separable (squarefree) polynomial.
* `Cslib.RealRoot.isolateRootsM_time_le`: upper bound on the `TimeM ℕ` bisection/evaluation ticks
  in terms of `natDegree` and `mignotteBisectionDepth`.
* `Cslib.RealRoot.polyIsolatedRoot_mem`, `Cslib.RealRoot.polyIsolatedRoot_strictMono`,
  `Cslib.RealRoot.isolatePolyRoots_bijective`, and `Cslib.RealRoot.isolatePolyRootsM_time_le`:
  squarefree `Polynomial ℚ` versions.

## References

* [BasuPollackRoy2006] (locator unverified)
* [Mahler1964] (originator of the Mahler-measure root-separation inequality; locator unverified)
* [Mignotte1982] (locator unverified; `isolateRootsM_time_le` and left-root refinement packaging
  are specific to this module)
-/

public section

namespace Cslib.RealRoot

open Polynomial Cslib.Algorithms.Lean

/-- Closed rational interval `[lower, upper]` representing an isolated real root. -/
structure RootInterval where
  /-- Left rational endpoint of the isolating interval. -/
  lower : ℚ
  /-- Right rational endpoint of the isolating interval. -/
  upper : ℚ
  deriving DecidableEq, Repr

/-- Closed-interval root isolation predicate: `I.lower ≤ I.upper` and `[I.lower, I.upper]`
contains a unique real root of `p`. -/
def RootInterval.IsIsolatingFor (I : RootInterval) (p : ℝ[X]) : Prop :=
  I.lower ≤ I.upper ∧
    ∃! r : ℝ, (I.lower : ℝ) ≤ r ∧ r ≤ (I.upper : ℝ) ∧ p.IsRoot r

/-- Half-open-interval root isolation predicate: `I.lower < I.upper` and `(I.lower, I.upper]`
contains a unique real root of `p`. -/
def RootInterval.IsHalfOpenIsolatingFor (I : RootInterval) (p : ℝ[X]) : Prop :=
  I.lower < I.upper ∧
    ∃! r : ℝ, (I.lower : ℝ) < r ∧ r ≤ (I.upper : ℝ) ∧ p.IsRoot r

/-- Operation weight charged for one Sturm sign-variation evaluation over `seq`: Horner
coefficient evaluations across all Sturm polynomials plus scanning the resulting signs. -/
@[expose] def sturmSeqOpCost (seq : List (List ℚ)) : ℕ :=
  (seq.map List.length).sum + seq.length

/-- Cost-instrumented Horner evaluation of `t : List ℚ` at `x : ℚ`. -/
@[expose] def evalListM (t : List ℚ) (x : ℚ) : TimeM ℕ ℚ := do
  TimeM.tick t.length
  pure (evalCoeffList x t)

/-- Cost-instrumented Sturm sign-variation count of `seq` at `x : ℚ`. -/
@[expose] def sturmVariationsM (seq : List (List ℚ)) (x : ℚ) : TimeM ℕ ℕ := do
  TimeM.tick (sturmSeqOpCost seq)
  pure (sturmVariationsList seq x)

/-- Pure value returned by `evalListM t x`. -/
@[simp]
theorem evalListM_ret (t : List ℚ) (x : ℚ) : (evalListM t x).ret = evalCoeffList x t := by
  simp only [evalListM, TimeM.ret_bind, TimeM.ret_pure]

/-- Time cost charged by `evalListM t x`: `t.length`. -/
@[simp]
theorem evalListM_time (t : List ℚ) (x : ℚ) : (evalListM t x).time = t.length := by
  simp only [evalListM, TimeM.time_bind, TimeM.time_tick, TimeM.time_pure, add_zero]

/-- Pure value returned by `sturmVariationsM seq x`. -/
@[simp]
theorem sturmVariationsM_ret (seq : List (List ℚ)) (x : ℚ) :
    (sturmVariationsM seq x).ret = sturmVariationsList seq x := by
  simp only [sturmVariationsM, TimeM.ret_bind, TimeM.ret_pure]

/-- Time cost charged by `sturmVariationsM seq x`: `sturmSeqOpCost seq`. -/
@[simp]
theorem sturmVariationsM_time (seq : List (List ℚ)) (x : ℚ) :
    (sturmVariationsM seq x).time = sturmSeqOpCost seq := by
  simp only [sturmVariationsM, TimeM.time_bind, TimeM.time_tick, TimeM.time_pure, add_zero]

/-- Upper bound on `sturmSeqOpCost (sturmSeqList cs)` in terms of `natDegree (ofCoeffList cs)`. -/
theorem sturmSeqOpCost_le (cs : List ℚ) :
    sturmSeqOpCost (sturmSeqList cs) ≤
      ((ofCoeffList cs).natDegree + 1) ^ 2 + ((ofCoeffList cs).natDegree + 1) := by
  let d := (ofCoeffList cs).natDegree
  have hlen : (sturmSeqList cs).length ≤ d + 1 := sturmSeqList_length_le cs
  have hentry : ∀ f ∈ sturmSeqList cs, f.length ≤ d + 1 := by
    intro f hf
    have h1 := sturmSeqList_entry_length_le cs hf
    by_cases h0 : trim cs = []
    · simp only [h0, List.length_nil] at h1
      omega
    · have hdeg : (ofCoeffList cs).natDegree + 1 = (trim cs).length := by
        rw [← ofCoeffList_trim cs]
        exact (isTrimmed_trim cs).natDegree_add_one h0
      omega
  have hsum : ((sturmSeqList cs).map List.length).sum ≤ (d + 1) ^ 2 := by
    have hmap : ∀ n ∈ (sturmSeqList cs).map List.length, n ≤ d + 1 := by
      intro n hn
      rw [List.mem_map] at hn
      obtain ⟨f, hf, rfl⟩ := hn
      exact hentry f hf
    have hle := List.sum_le_length_nsmul ((sturmSeqList cs).map List.length) (d + 1) hmap
    rw [List.length_map, smul_eq_mul] at hle
    calc ((sturmSeqList cs).map List.length).sum
        ≤ (sturmSeqList cs).length * (d + 1) := hle
      _ ≤ (d + 1) * (d + 1) := Nat.mul_le_mul_right _ hlen
      _ = (d + 1) ^ 2 := (sq (d + 1)).symm
  rw [sturmSeqOpCost]
  exact Nat.add_le_add hsum hlen

/-- Inner loop shrinking `(u, v]` away from a root at `u` when `(u, v]` contains a unique root
of `t`. -/
@[expose] def refineLeftLoopM (t : List ℚ) (seq : List (List ℚ)) :
    ℕ → ℚ → ℚ → ℕ → TimeM ℕ RootInterval
  | 0, u, v, _ => pure { lower := u, upper := v }
  | fuel + 1, u, v, vu => do
    let m := (u + v) / 2
    let vm ← sturmVariationsM seq m
    if vm = vu then
      pure { lower := m, upper := v }
    else
      let em ← evalListM t m
      if em = 0 then
        pure { lower := m, upper := m }
      else
        refineLeftLoopM t seq fuel u m vu

/-- Convert a half-open isolating interval `(u, v]` (`u < v`, `V(u) - V(v) = 1`) into a closed
isolating interval `[a, b] ⊆ [u, v]`, strictly separating `u` when `t` vanishes at `u`. -/
@[expose] def refineLeftRootM (t : List ℚ) (seq : List (List ℚ)) (fuel : ℕ)
    (u v : ℚ) (vu : ℕ) : TimeM ℕ RootInterval := do
  let ev ← evalListM t v
  if ev = 0 then
    pure { lower := v, upper := v }
  else
    let eu ← evalListM t u
    if eu ≠ 0 then
      pure { lower := u, upper := v }
    else
      refineLeftLoopM t seq fuel u v vu

/-- Recursive Sturm-count bisection on `(u, v]` with cached endpoint variation counts `vu` and
`vv`. -/
@[expose] def isolateIocM (t : List ℚ) (seq : List (List ℚ)) (depthBound : ℕ) :
    ℕ → ℚ → ℚ → ℕ → ℕ → TimeM ℕ (List RootInterval)
  | fuel, u, v, vu, vv =>
    let count := vu - vv
    if count = 0 then
      pure []
    else if count = 1 then do
      let rint ← refineLeftRootM t seq depthBound u v vu
      pure [rint]
    else
      match fuel with
      | 0 => pure []
      | fuel' + 1 => do
        let m := (u + v) / 2
        let vm ← sturmVariationsM seq m
        let left ← isolateIocM t seq depthBound fuel' u m vu vm
        let right ← isolateIocM t seq depthBound fuel' m v vm vv
        pure (left ++ right)

/-- Execute Sturm-count real-root isolation on `ofCoeffList cs`. Preprocessing (`trim`,
`sturmSeqList`, `cauchyBoundNat`, `mignotteBisectionDepth`) and scalar/list control work run outside
`TimeM` (`0` ticks); bisection and left-root refinement charge `sturmVariationsM` and `evalListM`
in `TimeM ℕ`. -/
@[expose] def isolateRootsM (cs : List ℚ) : TimeM ℕ (List RootInterval) :=
  let t := trim cs
  if t.isEmpty then
    pure []
  else
    let seq := sturmSeqList cs
    let b : ℚ := (cauchyBoundNat cs : ℚ)
    let depth := mignotteBisectionDepth cs
    do
      let vLeft ← sturmVariationsM seq (-b)
      let vRight ← sturmVariationsM seq b
      isolateIocM t seq depth depth (-b) b vLeft vRight

/-- Executable Sturm-count real-root isolator returning sorted isolating rational intervals for
`ofCoeffList cs`. -/
@[expose] def isolateRoots (cs : List ℚ) : List RootInterval :=
  (isolateRootsM cs).ret

/-- Pure value returned by `isolateRootsM cs` equals `isolateRoots cs`. -/
@[simp]
theorem isolateRootsM_ret (cs : List ℚ) : (isolateRootsM cs).ret = isolateRoots cs := rfl

private theorem refineLeftLoopM_time_le (t : List ℚ) (seq : List (List ℚ)) (fuel : ℕ)
    (u v : ℚ) (vu : ℕ) :
    (refineLeftLoopM t seq fuel u v vu).time ≤ fuel * (sturmSeqOpCost seq + t.length) := by
  induction fuel generalizing u v vu with
  | zero => simp only [refineLeftLoopM, TimeM.time_pure, zero_mul, le_refl]
  | succ fuel ih =>
    simp only [refineLeftLoopM, TimeM.time_bind, sturmVariationsM_time, sturmVariationsM_ret]
    by_cases hvm : sturmVariationsList seq ((u + v) / 2) = vu
    · simp only [hvm, ↓reduceIte, TimeM.time_pure, add_zero]
      rw [Nat.succ_mul]
      omega
    · simp only [hvm, ↓reduceIte, TimeM.time_bind, evalListM_time, evalListM_ret]
      by_cases hem : evalCoeffList ((u + v) / 2) t = 0
      · simp only [hem, ↓reduceIte, TimeM.time_pure, add_zero]
        rw [Nat.succ_mul]
        omega
      · simp only [hem, ↓reduceIte]
        have hrec := ih u ((u + v) / 2) vu
        rw [Nat.succ_mul]
        omega

private theorem refineLeftRootM_time_le (t : List ℚ) (seq : List (List ℚ)) (fuel : ℕ)
    (u v : ℚ) (vu : ℕ) :
    (refineLeftRootM t seq fuel u v vu).time ≤
      2 * t.length + fuel * (sturmSeqOpCost seq + t.length) := by
  simp only [refineLeftRootM, TimeM.time_bind, evalListM_time, evalListM_ret]
  by_cases hev : evalCoeffList v t = 0
  · simp only [eq_true hev, ↓reduceIte, TimeM.time_pure, add_zero]
    omega
  · simp only [eq_false hev, ↓reduceIte, TimeM.time_bind, evalListM_time, evalListM_ret]
    by_cases heu : evalCoeffList u t ≠ 0
    · simp only [eq_true heu, ↓reduceIte, TimeM.time_pure, add_zero]
      omega
    · simp only [eq_false heu, ↓reduceIte]
      have hloop := refineLeftLoopM_time_le t seq fuel u v vu
      omega

private theorem sturmVariationsList_antitone {cs : List ℚ} (hsep : (ofCoeffList cs).Separable)
    {u v : ℚ} (huv : u ≤ v) :
    sturmVariationsList (sturmSeqList cs) v ≤ sturmVariationsList (sturmSeqList cs) u := by
  let pR := (ofCoeffList cs).map (algebraMap ℚ ℝ)
  have hsepR : pR.Separable := hsep.map
  rw [sturmVariationsList_eq_sturmVariations, sturmVariationsList_eq_sturmVariations]
  exact Polynomial.sturmVariations_antitone hsepR (Rat.cast_le.mpr huv)

private theorem isolateIocM_time_le {cs : List ℚ} (hsep : (ofCoeffList cs).Separable)
    (t : List ℚ) (depthBound : ℕ) :
    ∀ (fuel : ℕ) (u v : ℚ) (vu vv : ℕ),
      u ≤ v →
      vu = sturmVariationsList (sturmSeqList cs) u →
      vv = sturmVariationsList (sturmSeqList cs) v →
      let seq := sturmSeqList cs
      let c := vu - vv
      let sCost := sturmSeqOpCost seq
      let lCost := 2 * t.length + depthBound * (sCost + t.length)
      (isolateIocM t seq depthBound fuel u v vu vv).time ≤
        (if c ≤ 1 then 0 else fuel * (c / 2)) * sCost + c * lCost
  | fuel, u, v, vu, vv, huv, hvu, hvv => by
    dsimp only
    let seq := sturmSeqList cs
    let c := vu - vv
    let sCost := sturmSeqOpCost seq
    let lCost := 2 * t.length + depthBound * (sCost + t.length)
    change (isolateIocM t seq depthBound fuel u v vu vv).time ≤
      (if c ≤ 1 then 0 else fuel * (c / 2)) * sCost + c * lCost
    unfold isolateIocM
    dsimp only
    by_cases hc0 : vu - vv = 0
    · simp only [eq_true hc0, ↓reduceIte, TimeM.time_pure]
      exact Nat.zero_le _
    · by_cases hc1 : vu - vv = 1
      · have hc1' : c = 1 := hc1
        simp only [eq_false hc0, eq_true hc1, hc1', eq_true (le_refl (1 : ℕ)), ↓reduceIte,
          TimeM.time_bind, TimeM.time_pure, add_zero, zero_mul, zero_add, one_mul]
        exact refineLeftRootM_time_le t seq depthBound u v vu
      · have hc2 : 2 ≤ c := by omega
        have hif : ¬c ≤ 1 := by omega
        simp only [eq_false hc0, eq_false hc1, eq_false hif, ↓reduceIte]
        cases fuel with
        | zero =>
          simp only [TimeM.time_pure]
          exact Nat.zero_le _
        | succ fuel' =>
          simp only [TimeM.time_bind, sturmVariationsM_time, sturmVariationsM_ret,
            TimeM.time_pure, add_zero]
          let m := (u + v) / 2
          let vm := sturmVariationsList seq m
          have hum : u ≤ m := by dsimp only [m]; linarith
          have hmv : m ≤ v := by dsimp only [m]; linarith
          have hle_left : vm ≤ vu := hvu ▸ sturmVariationsList_antitone hsep hum
          have hle_right : vv ≤ vm := hvv ▸ sturmVariationsList_antitone hsep hmv
          have ihL := isolateIocM_time_le hsep t depthBound fuel' u m vu vm hum hvu rfl
          have ihR := isolateIocM_time_le hsep t depthBound fuel' m v vm vv hmv rfl hvv
          let c₁ := vu - vm
          let c₂ := vm - vv
          have hsum_c : c₁ + c₂ = c := by omega
          have hdiv : (if c₁ ≤ 1 then 0 else fuel' * (c₁ / 2)) +
              (if c₂ ≤ 1 then 0 else fuel' * (c₂ / 2)) + 1 ≤
              (fuel' + 1) * (c / 2) := by
            have hd1 : (if c₁ ≤ 1 then 0 else fuel' * (c₁ / 2)) ≤ fuel' * (c₁ / 2) := by
              split_ifs <;> omega
            have hd2 : (if c₂ ≤ 1 then 0 else fuel' * (c₂ / 2)) ≤ fuel' * (c₂ / 2) := by
              split_ifs <;> omega
            have hhalf : c₁ / 2 + c₂ / 2 ≤ c / 2 := by omega
            have hhalf1 : 1 ≤ c / 2 := by omega
            calc (if c₁ ≤ 1 then 0 else fuel' * (c₁ / 2)) +
                  (if c₂ ≤ 1 then 0 else fuel' * (c₂ / 2)) + 1
                ≤ fuel' * (c₁ / 2) + fuel' * (c₂ / 2) + 1 := by omega
              _ = fuel' * (c₁ / 2 + c₂ / 2) + 1 := by ring
              _ ≤ fuel' * (c / 2) + c / 2 := by gcongr
              _ = (fuel' + 1) * (c / 2) := by ring
          calc sCost +
                ((isolateIocM t seq depthBound fuel' u m vu vm).time +
                  (isolateIocM t seq depthBound fuel' m v vm vv).time)
              ≤ sCost +
                  (((if c₁ ≤ 1 then 0 else fuel' * (c₁ / 2)) * sCost + c₁ * lCost) +
                    ((if c₂ ≤ 1 then 0 else fuel' * (c₂ / 2)) * sCost + c₂ * lCost)) := by
                  gcongr
            _ = ((if c₁ ≤ 1 then 0 else fuel' * (c₁ / 2)) +
                    (if c₂ ≤ 1 then 0 else fuel' * (c₂ / 2)) + 1) * sCost +
                  (c₁ + c₂) * lCost := by ring
            _ ≤ (fuel' + 1) * (c / 2) * sCost + c * lCost := by rw [hsum_c]; gcongr

private theorem eval_rat_eq_zero_iff (cs : List ℚ) (x : ℚ) :
    evalCoeffList x (trim cs) = 0 ↔
      ((ofCoeffList cs).map (algebraMap ℚ ℝ)).eval (x : ℝ) = 0 := by
  have heval : ((ofCoeffList cs).map (algebraMap ℚ ℝ)).eval (x : ℝ) =
      ((evalCoeffList x (trim cs) : ℚ) : ℝ) := by
    rw [← ofCoeffList_trim cs]
    have hmap : (algebraMap ℚ ℝ) (eval x (ofCoeffList (trim cs))) =
        ((ofCoeffList (trim cs)).map (algebraMap ℚ ℝ)).eval ((algebraMap ℚ ℝ) x) := by
      rw [Polynomial.eval_map, Polynomial.eval₂_hom]
    change ((ofCoeffList (trim cs)).map (algebraMap ℚ ℝ)).eval ((algebraMap ℚ ℝ) x) = _
    rw [← hmap, eval_ofCoeffList]
    rfl
  rw [heval]
  exact Rat.cast_eq_zero.symm

private theorem card_roots_Ioc_eq {cs : List ℚ} (hsep : (ofCoeffList cs).Separable)
    {u v : ℚ} (huv : u ≤ v) :
    sturmVariationsList (sturmSeqList cs) u - sturmVariationsList (sturmSeqList cs) v =
      (((ofCoeffList cs).map (algebraMap ℚ ℝ)).roots.toFinset.filter
        (fun r : ℝ => (u : ℝ) < r ∧ r ≤ (v : ℝ))).card := by
  let pR := (ofCoeffList cs).map (algebraMap ℚ ℝ)
  have hsepR : pR.Separable := hsep.map
  rw [sturmVariationsList_eq_sturmVariations, sturmVariationsList_eq_sturmVariations]
  exact sturmVariations_sub_eq_card_roots_Ioc hsepR (Rat.cast_le.mpr huv)

private theorem exists_two_roots_Ioc_of_two_le {pR : ℝ[X]} (hpR : pR ≠ 0) {u v : ℝ}
    (hcard : 2 ≤ (pR.roots.toFinset.filter (fun r => u < r ∧ r ≤ v)).card) :
    ∃ α β : ℝ, pR.IsRoot α ∧ pR.IsRoot β ∧ u < α ∧ α < β ∧ β ≤ v := by
  let S := pR.roots.toFinset.filter (fun r => u < r ∧ r ≤ v)
  have h1 : 1 < S.card := by simpa only [S] using Nat.lt_of_lt_of_le one_lt_two hcard
  obtain ⟨α, hα, β, hβ, hne⟩ := Finset.one_lt_card.mp h1
  simp only [S, Finset.mem_filter, Multiset.mem_toFinset, mem_roots hpR] at hα hβ
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact ⟨α, β, hα.1, hβ.1, hα.2.1, hlt, hβ.2.2⟩
  · exact ⟨β, α, hβ.1, hα.1, hβ.2.1, hgt, hα.2.2⟩

private theorem natDegree_ge_two_of_two_roots {cs : List ℚ} (hsep : (ofCoeffList cs).Separable)
    {α β : ℝ} (hα : ((ofCoeffList cs).map (algebraMap ℚ ℝ)).IsRoot α)
    (hβ : ((ofCoeffList cs).map (algebraMap ℚ ℝ)).IsRoot β) (hne : α ≠ β) :
    2 ≤ (ofCoeffList cs).natDegree := by
  let pR := (ofCoeffList cs).map (algebraMap ℚ ℝ)
  have hp0 : ofCoeffList cs ≠ 0 := hsep.ne_zero
  have hpR0 : pR ≠ 0 := (Polynomial.map_ne_zero_iff (algebraMap ℚ ℝ).injective).mpr hp0
  have hα_mem : α ∈ pR.roots.toFinset :=
    Multiset.mem_toFinset.mpr ((mem_roots hpR0).mpr hα.eq_zero)
  have hβ_mem : β ∈ pR.roots.toFinset :=
    Multiset.mem_toFinset.mpr ((mem_roots hpR0).mpr hβ.eq_zero)
  have hpair : ({α, β} : Finset ℝ) ⊆ pR.roots.toFinset := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  have hcard2 : 2 ≤ pR.roots.toFinset.card := by
    simpa only [Finset.card_pair hne] using Finset.card_le_card hpair
  have hcard_le : pR.roots.toFinset.card ≤ pR.natDegree :=
    (Multiset.toFinset_card_le _).trans (Polynomial.card_roots' pR)
  have hdeg : pR.natDegree = (ofCoeffList cs).natDegree :=
    Polynomial.natDegree_map_eq_of_injective (algebraMap ℚ ℝ).injective _
  omega

private theorem unique_root_Ioc_of_card_eq_one {cs : List ℚ} (hsep : (ofCoeffList cs).Separable)
    {u v : ℚ} (huv : u ≤ v)
    (hcnt : sturmVariationsList (sturmSeqList cs) u -
      sturmVariationsList (sturmSeqList cs) v = 1) :
    ∃! r : ℝ, (u : ℝ) < r ∧ r ≤ (v : ℝ) ∧
      ((ofCoeffList cs).map (algebraMap ℚ ℝ)).IsRoot r := by
  let pR := (ofCoeffList cs).map (algebraMap ℚ ℝ)
  have hpR0 : pR ≠ 0 :=
    (Polynomial.map_ne_zero_iff (algebraMap ℚ ℝ).injective).mpr hsep.ne_zero
  rw [card_roots_Ioc_eq hsep huv] at hcnt
  obtain ⟨r₀, hr₀⟩ := Finset.card_eq_one.mp hcnt
  refine ⟨r₀, ?_, ?_⟩
  · have hmem : r₀ ∈ pR.roots.toFinset.filter (fun r : ℝ => (u : ℝ) < r ∧ r ≤ (v : ℝ)) := by
      rw [hr₀]
      exact Finset.mem_singleton_self r₀
    simp only [Finset.mem_filter, Multiset.mem_toFinset, mem_roots hpR0] at hmem
    exact ⟨hmem.2.1, hmem.2.2, hmem.1⟩
  · intro r ⟨hur, hrv, hroot⟩
    have hmem : r ∈ pR.roots.toFinset.filter (fun r : ℝ => (u : ℝ) < r ∧ r ≤ (v : ℝ)) := by
      simp only [Finset.mem_filter, Multiset.mem_toFinset, mem_roots hpR0]
      exact ⟨hroot, hur, hrv⟩
    rw [hr₀, Finset.mem_singleton] at hmem
    exact hmem

private theorem no_root_Ioc_of_card_eq_zero {cs : List ℚ} (hsep : (ofCoeffList cs).Separable)
    {u v : ℚ} (huv : u ≤ v)
    (hcnt : sturmVariationsList (sturmSeqList cs) u -
      sturmVariationsList (sturmSeqList cs) v = 0)
    {r : ℝ} (hur : (u : ℝ) < r) (hrv : r ≤ (v : ℝ)) :
    ¬((ofCoeffList cs).map (algebraMap ℚ ℝ)).IsRoot r := by
  let pR := (ofCoeffList cs).map (algebraMap ℚ ℝ)
  have hpR0 : pR ≠ 0 :=
    (Polynomial.map_ne_zero_iff (algebraMap ℚ ℝ).injective).mpr hsep.ne_zero
  rw [card_roots_Ioc_eq hsep huv, Finset.card_eq_zero] at hcnt
  intro hroot
  have hmem : r ∈ pR.roots.toFinset.filter (fun x : ℝ => (u : ℝ) < x ∧ x ≤ (v : ℝ)) := by
    simp only [Finset.mem_filter, Multiset.mem_toFinset, mem_roots hpR0]
    exact ⟨hroot, hur, hrv⟩
  rw [hcnt] at hmem
  exact Finset.notMem_empty r hmem

private theorem dyadic_half_width_le {cs : List ℚ} {u v : ℚ} {depth : ℕ}
    (hw : (v - u : ℝ) ≤ 2 * (cauchyBoundNat cs : ℝ) / (2 : ℝ) ^ depth) :
    (((u + v) / 2 : ℚ) - u : ℝ) ≤ 2 * (cauchyBoundNat cs : ℝ) / (2 : ℝ) ^ (depth + 1) ∧
      ((v : ℝ) - ((u + v) / 2 : ℚ) : ℝ) ≤
        2 * (cauchyBoundNat cs : ℝ) / (2 : ℝ) ^ (depth + 1) := by
  have hbound : ((v - u : ℝ) / 2) ≤ 2 * (cauchyBoundNat cs : ℝ) / (2 : ℝ) ^ (depth + 1) := by
    rw [pow_succ]
    calc (v - u : ℝ) / 2
        ≤ (2 * (cauchyBoundNat cs : ℝ) / (2 : ℝ) ^ depth) / 2 := by linarith
      _ = 2 * (cauchyBoundNat cs : ℝ) / ((2 : ℝ) ^ depth * 2) := by ring
  have h1 : (((u + v) / 2 : ℚ) - u : ℝ) = (v - u : ℝ) / 2 := by push_cast; ring
  have h2 : ((v : ℝ) - ((u + v) / 2 : ℚ) : ℝ) = (v - u : ℝ) / 2 := by push_cast; ring
  exact ⟨h1 ▸ hbound, h2 ▸ hbound⟩

private theorem singleton_isolating_of_Ioc {pR : ℝ[X]} {u v m : ℚ} (hum : u < m) (hmv : m ≤ v)
    (hm_root : pR.IsRoot (m : ℝ))
    (huniq : ∀ r : ℝ, (u : ℝ) < r → r ≤ (v : ℝ) → pR.IsRoot r → r = (m : ℝ)) :
    ({ lower := m, upper := m } : RootInterval).IsIsolatingFor pR ∧
      ∀ r : ℝ, ((m : ℝ) ≤ r ∧ r ≤ (m : ℝ) ∧ pR.IsRoot r) ↔
        ((u : ℝ) < r ∧ r ≤ (v : ℝ) ∧ pR.IsRoot r) := by
  refine ⟨⟨le_rfl, (m : ℝ), ⟨le_rfl, le_rfl, hm_root⟩, fun r ⟨hmr, hrm, _⟩ =>
    le_antisymm hrm hmr⟩, fun r => ?_⟩
  constructor
  · rintro ⟨hmr, hrm, _⟩
    have heq : r = (m : ℝ) := le_antisymm hrm hmr
    subst heq
    exact ⟨Rat.cast_lt.mpr hum, Rat.cast_le.mpr hmv, hm_root⟩
  · rintro ⟨hur, hrv, hrr⟩
    rw [huniq r hur hrv hrr]
    exact ⟨le_rfl, le_rfl, hm_root⟩

private theorem refineLeftLoopM_spec {cs : List ℚ} (hsep : (ofCoeffList cs).Separable) :
    ∀ (fuel depth : ℕ) (u v : ℚ) (vu vv : ℕ),
      depth + fuel = mignotteBisectionDepth cs →
      u < v →
      vu = sturmVariationsList (sturmSeqList cs) u →
      vv = sturmVariationsList (sturmSeqList cs) v →
      vu - vv = 1 →
      evalCoeffList u (trim cs) = 0 →
      (v - u : ℝ) ≤ 2 * (cauchyBoundNat cs : ℝ) / (2 : ℝ) ^ depth →
      let I := (refineLeftLoopM (trim cs) (sturmSeqList cs) fuel u v vu).ret
      let pR := (ofCoeffList cs).map (algebraMap ℚ ℝ)
      I.IsIsolatingFor pR ∧ u < I.lower ∧ I.upper ≤ v ∧
        ∀ r : ℝ, ((I.lower : ℝ) ≤ r ∧ r ≤ (I.upper : ℝ) ∧ pR.IsRoot r) ↔
          ((u : ℝ) < r ∧ r ≤ (v : ℝ) ∧ pR.IsRoot r)
  | 0, depth, u, v, vu, vv, hsum, huv, hvu, hvv, hcnt, hu_root, hwidth => by
    exfalso
    have hdepth : depth = mignotteBisectionDepth cs := by omega
    rw [hvu, hvv] at hcnt
    obtain ⟨r, ⟨hur, hrv, hr_root⟩, _⟩ := unique_root_Ioc_of_card_eq_one hsep huv.le hcnt
    have huR_root : ((ofCoeffList cs).map (algebraMap ℚ ℝ)).IsRoot (u : ℝ) := by
      rw [IsRoot.def, ← eval_rat_eq_zero_iff]
      exact hu_root
    have hne : (u : ℝ) ≠ r := hur.ne
    have hd2 : 2 ≤ (ofCoeffList cs).natDegree :=
      natDegree_ge_two_of_two_roots hsep huR_root hr_root hne
    have hsep_width := dyadic_width_lt_root_sep hsep hd2 huR_root hr_root hne
    rw [← hdepth, abs_of_neg (sub_neg.mpr hur), neg_sub] at hsep_width
    have hr_sub : r - (u : ℝ) ≤ (v : ℝ) - (u : ℝ) := by linarith
    have hw' : (v : ℝ) - (u : ℝ) ≤ 2 * (cauchyBoundNat cs : ℝ) / (2 : ℝ) ^ depth := by
      simpa only [Rat.cast_sub] using hwidth
    linarith
  | fuel + 1, depth, u, v, vu, vv, hsum, huv, hvu, hvv, hcnt, hu_root, hwidth => by
    let pR := (ofCoeffList cs).map (algebraMap ℚ ℝ)
    let m := (u + v) / 2
    let vm := sturmVariationsList (sturmSeqList cs) m
    have hum : u < m := by dsimp only [m]; linarith
    have hmv : m < v := by dsimp only [m]; linarith
    have hle_left : vm ≤ vu := hvu ▸ sturmVariationsList_antitone hsep hum.le
    have hle_right : vv ≤ vm := hvv ▸ sturmVariationsList_antitone hsep hmv.le
    dsimp only [refineLeftLoopM]
    rw [TimeM.ret_bind, sturmVariationsM_ret]
    split_ifs with hvm_eq
    · rw [TimeM.ret_pure]
      have hvm_eq' : vm = vu := hvm_eq
      have hcnt_right : sturmVariationsList (sturmSeqList cs) m -
          sturmVariationsList (sturmSeqList cs) v = 1 := by
        rw [← hvv]
        change vm - vv = 1
        omega
      have hcnt_left : sturmVariationsList (sturmSeqList cs) u -
          sturmVariationsList (sturmSeqList cs) m = 0 := by
        rw [← hvu]
        change vu - vm = 0
        omega
      have hm_not_root : ¬pR.IsRoot (m : ℝ) :=
        no_root_Ioc_of_card_eq_zero hsep hum.le hcnt_left (Rat.cast_lt.mpr hum) le_rfl
      obtain ⟨r₀, ⟨hmr₀, hr₀v, hr₀_root⟩, hr₀_uniq⟩ :=
        unique_root_Ioc_of_card_eq_one hsep hmv.le hcnt_right
      have hequiv : ∀ r : ℝ, ((m : ℝ) ≤ r ∧ r ≤ (v : ℝ) ∧ pR.IsRoot r) ↔
          ((u : ℝ) < r ∧ r ≤ (v : ℝ) ∧ pR.IsRoot r) := by
        intro r
        constructor
        · rintro ⟨hmr, hrv, hrr⟩
          exact ⟨lt_of_lt_of_le (Rat.cast_lt.mpr hum) hmr, hrv, hrr⟩
        · rintro ⟨hur, hrv, hrr⟩
          refine ⟨?_, hrv, hrr⟩
          by_contra hlt
          have hrm : r ≤ (m : ℝ) := le_of_not_ge hlt
          exact no_root_Ioc_of_card_eq_zero hsep hum.le hcnt_left hur hrm hrr
      refine ⟨⟨hmv.le, r₀, ⟨hmr₀.le, hr₀v, hr₀_root⟩, fun r ⟨hmr, hrv, hrr⟩ => ?_⟩, hum,
        le_rfl, hequiv⟩
      refine hr₀_uniq r ⟨?_, hrv, hrr⟩
      refine lt_of_le_of_ne hmr ?_
      intro heq
      apply hm_not_root
      simpa only [heq] using hrr
    · have hvm_ne : vm ≠ vu := hvm_eq
      have hvm_eq_vv : vm = vv := by omega
      have hcnt_left : sturmVariationsList (sturmSeqList cs) u -
          sturmVariationsList (sturmSeqList cs) m = 1 := by
        rw [← hvu]
        change vu - vm = 1
        omega
      have hcnt_right : sturmVariationsList (sturmSeqList cs) m -
          sturmVariationsList (sturmSeqList cs) v = 0 := by
        rw [← hvv]
        change vm - vv = 0
        omega
      rw [TimeM.ret_bind, evalListM_ret]
      split_ifs with hem
      · rw [TimeM.ret_pure]
        have hm_root : pR.IsRoot (m : ℝ) := by
          rw [IsRoot.def, ← eval_rat_eq_zero_iff]
          exact hem
        obtain ⟨hiso, hequiv⟩ := singleton_isolating_of_Ioc hum hmv.le hm_root
          fun r hur hrv hrr => by
          have hle_m : r ≤ (m : ℝ) := by
            by_contra hgt
            exact no_root_Ioc_of_card_eq_zero hsep hmv.le hcnt_right (lt_of_not_ge hgt) hrv hrr
          obtain ⟨r₀, _, hr₀_uniq⟩ := unique_root_Ioc_of_card_eq_one hsep hum.le hcnt_left
          exact (hr₀_uniq r ⟨hur, hle_m, hrr⟩).trans
            (hr₀_uniq (m : ℝ) ⟨Rat.cast_lt.mpr hum, le_rfl, hm_root⟩).symm
        exact ⟨hiso, hum, hmv.le, hequiv⟩
      · have hwidth' : (m - u : ℝ) ≤ 2 * (cauchyBoundNat cs : ℝ) / (2 : ℝ) ^ (depth + 1) :=
          (dyadic_half_width_le hwidth).1
        have ih := refineLeftLoopM_spec hsep fuel (depth + 1) u m vu vm (by omega) hum hvu rfl
          (by omega) hu_root hwidth'
        rcases ih with ⟨ih_iso, ih_low, ih_up, ih_equiv⟩
        refine ⟨ih_iso, ih_low, ih_up.trans hmv.le, fun r => ?_⟩
        rw [ih_equiv r]
        constructor
        · rintro ⟨hur, hrm, hrr⟩
          exact ⟨hur, hrm.trans (Rat.cast_lt.mpr hmv).le, hrr⟩
        · rintro ⟨hur, hrv, hrr⟩
          refine ⟨hur, ?_, hrr⟩
          by_contra hgt
          exact no_root_Ioc_of_card_eq_zero hsep hmv.le hcnt_right (lt_of_not_ge hgt) hrv hrr

private theorem refineLeftRootM_spec {cs : List ℚ} (hsep : (ofCoeffList cs).Separable)
    {u v : ℚ} (huv : u < v) {vu vv : ℕ}
    (hvu : vu = sturmVariationsList (sturmSeqList cs) u)
    (hvv : vv = sturmVariationsList (sturmSeqList cs) v)
    (hcnt : vu - vv = 1)
    (hwidth : (v - u : ℝ) ≤ 2 * (cauchyBoundNat cs : ℝ)) :
    let I := (refineLeftRootM (trim cs) (sturmSeqList cs) (mignotteBisectionDepth cs) u v vu).ret
    let pR := (ofCoeffList cs).map (algebraMap ℚ ℝ)
    I.IsIsolatingFor pR ∧ u ≤ I.lower ∧ I.upper ≤ v ∧
      (evalCoeffList u (trim cs) = 0 → u < I.lower) ∧
      ∀ r : ℝ, ((I.lower : ℝ) ≤ r ∧ r ≤ (I.upper : ℝ) ∧ pR.IsRoot r) ↔
        ((u : ℝ) < r ∧ r ≤ (v : ℝ) ∧ pR.IsRoot r) := by
  let pR := (ofCoeffList cs).map (algebraMap ℚ ℝ)
  have hcnt' : sturmVariationsList (sturmSeqList cs) u -
      sturmVariationsList (sturmSeqList cs) v = 1 := by
    rw [← hvu, ← hvv]
    exact hcnt
  obtain ⟨r₀, ⟨hur₀, hr₀v, hr₀_root⟩, hr₀_uniq⟩ :=
    unique_root_Ioc_of_card_eq_one hsep huv.le hcnt'
  dsimp only [refineLeftRootM]
  rw [TimeM.ret_bind, evalListM_ret]
  split_ifs with hev
  · rw [TimeM.ret_pure]
    have hv_root : pR.IsRoot (v : ℝ) := by
      rw [IsRoot.def, ← eval_rat_eq_zero_iff]
      exact hev
    obtain ⟨hiso, hequiv⟩ := singleton_isolating_of_Ioc huv le_rfl hv_root fun r hur hrv hrr =>
      (hr₀_uniq r ⟨hur, hrv, hrr⟩).trans
        (hr₀_uniq (v : ℝ) ⟨Rat.cast_lt.mpr huv, le_rfl, hv_root⟩).symm
    exact ⟨hiso, huv.le, le_rfl, fun _ => huv, hequiv⟩
  · rw [TimeM.ret_bind, evalListM_ret]
    split_ifs with heu
    · rw [TimeM.ret_pure]
      have hu_not : ¬pR.IsRoot (u : ℝ) := by
        rw [IsRoot.def, ← eval_rat_eq_zero_iff]
        exact heu
      have hequiv : ∀ r : ℝ, ((u : ℝ) ≤ r ∧ r ≤ (v : ℝ) ∧ pR.IsRoot r) ↔
          ((u : ℝ) < r ∧ r ≤ (v : ℝ) ∧ pR.IsRoot r) := by
        intro r
        constructor
        · rintro ⟨hur, hrv, hrr⟩
          refine ⟨lt_of_le_of_ne hur ?_, hrv, hrr⟩
          intro heq
          apply hu_not
          simpa only [← heq] using hrr
        · rintro ⟨hur, hrv, hrr⟩
          exact ⟨hur.le, hrv, hrr⟩
      exact ⟨⟨huv.le, r₀, ⟨hur₀.le, hr₀v, hr₀_root⟩, fun r h => hr₀_uniq r ((hequiv r).mp h)⟩,
        le_rfl, le_rfl, fun h0 => absurd h0 heu, hequiv⟩
    · have hu0 : evalCoeffList u (trim cs) = 0 := not_not.mp heu
      have hw0 : (v - u : ℝ) ≤ 2 * (cauchyBoundNat cs : ℝ) / (2 : ℝ) ^ 0 := by
        simpa only [pow_zero, div_one] using hwidth
      have hloop := refineLeftLoopM_spec hsep (mignotteBisectionDepth cs) 0 u v vu vv
        (Nat.zero_add _) huv hvu hvv hcnt hu0 hw0
      rcases hloop with ⟨hiso, hlow, hup, hequiv⟩
      exact ⟨hiso, hlow.le, hup, fun _ => hlow, hequiv⟩

private def IntervalGapOk (p : ℝ[X]) (I₁ I₂ : RootInterval) : Prop :=
  I₁.upper < I₂.lower ∨ (I₁.upper = I₂.lower ∧ p.eval (I₁.upper : ℝ) ≠ 0)

private theorem intervalGapOk_of_mid {p : ℝ[X]} {m : ℚ} {I₁ I₂ : RootInterval}
    (h1 : I₁.upper ≤ m) (h2 : m ≤ I₂.lower) (hstrict : p.eval (m : ℝ) = 0 → m < I₂.lower) :
    IntervalGapOk p I₁ I₂ := by
  rcases lt_or_eq_of_le h1 with h1lt | rfl
  · exact Or.inl (lt_of_lt_of_le h1lt h2)
  · rcases lt_or_eq_of_le h2 with h2lt | h2eq
    · exact Or.inl h2lt
    · refine Or.inr ⟨h2eq, fun hm0 => ?_⟩
      exact (hstrict hm0).ne h2eq

private theorem pairwise_append_of_intervalGapOk {p : ℝ[X]} {L₁ L₂ : List RootInterval}
    (h1 : L₁.Pairwise (IntervalGapOk p)) (h2 : L₂.Pairwise (IntervalGapOk p))
    (hcross : ∀ I₁ ∈ L₁, ∀ I₂ ∈ L₂, IntervalGapOk p I₁ I₂) :
    (L₁ ++ L₂).Pairwise (IntervalGapOk p) := by
  rw [List.pairwise_append]
  exact ⟨h1, h2, hcross⟩

private theorem isolateIocM_spec {cs : List ℚ} (hsep : (ofCoeffList cs).Separable) :
    ∀ (fuel depth : ℕ) (u v : ℚ) (vu vv : ℕ),
      depth + fuel = mignotteBisectionDepth cs →
      u ≤ v →
      vu = sturmVariationsList (sturmSeqList cs) u →
      vv = sturmVariationsList (sturmSeqList cs) v →
      (v - u : ℝ) ≤ 2 * (cauchyBoundNat cs : ℝ) / (2 : ℝ) ^ depth →
      let L := (isolateIocM (trim cs) (sturmSeqList cs) (mignotteBisectionDepth cs)
        fuel u v vu vv).ret
      let pR := (ofCoeffList cs).map (algebraMap ℚ ℝ)
      (∀ I ∈ L, I.IsIsolatingFor pR ∧ u ≤ I.lower ∧ I.upper ≤ v ∧
        (evalCoeffList u (trim cs) = 0 → u < I.lower)) ∧
      L.Pairwise (IntervalGapOk pR) ∧
      L.length = vu - vv ∧
      (∀ I ∈ L, ∀ r : ℝ, ((I.lower : ℝ) ≤ r ∧ r ≤ (I.upper : ℝ) ∧ pR.IsRoot r) →
        (u : ℝ) < r ∧ r ≤ (v : ℝ)) ∧
      (∀ r : ℝ, ((u : ℝ) < r ∧ r ≤ (v : ℝ) ∧ pR.IsRoot r) →
        ∃ I ∈ L, (I.lower : ℝ) ≤ r ∧ r ≤ (I.upper : ℝ))
  | fuel, depth, u, v, vu, vv, hsum, huv, hvu, hvv, hwidth => by
    let pR := (ofCoeffList cs).map (algebraMap ℚ ℝ)
    have hvu_ge : vv ≤ vu := by
      rw [hvu, hvv]
      exact sturmVariationsList_antitone hsep huv
    unfold isolateIocM
    dsimp only
    split_ifs with hc0 hc1
    · rw [TimeM.ret_pure]
      refine ⟨fun _ h => absurd h (List.not_mem_nil), List.Pairwise.nil,
        by simp only [List.length_nil, hc0], fun _ h => absurd h (List.not_mem_nil),
        fun r ⟨hur, hrv, hrr⟩ => ?_⟩
      rw [hvu, hvv] at hc0
      exact False.elim (no_root_Ioc_of_card_eq_zero hsep huv hc0 hur hrv hrr)
    · have huv_lt : u < v := by
        refine lt_of_le_of_ne huv ?_
        rintro rfl
        omega
      have hwidth0 : (v - u : ℝ) ≤ 2 * (cauchyBoundNat cs : ℝ) := by
        have hpow1 : (1 : ℝ) ≤ (2 : ℝ) ^ depth := by
          exact_mod_cast Nat.one_le_pow depth 2 (by omega)
        have hnonneg : 0 ≤ 2 * (cauchyBoundNat cs : ℝ) := by positivity
        exact hwidth.trans (div_le_self hnonneg hpow1)
      have href := refineLeftRootM_spec hsep huv_lt hvu hvv hc1 hwidth0
      rcases href with ⟨hiso, hlow, hup, hstrict, hequiv⟩
      rw [TimeM.ret_bind, TimeM.ret_pure]
      refine ⟨fun I hI => ?_, List.pairwise_singleton _ _,
        by simp only [List.length_singleton, hc1],
        fun I hI r hr => ?_, fun r hr => ?_⟩
      · rw [List.mem_singleton] at hI
        subst hI
        exact ⟨hiso, hlow, hup, hstrict⟩
      · rw [List.mem_singleton] at hI
        subst hI
        let h := (hequiv r).mp hr
        exact ⟨h.1, h.2.1⟩
      · let h := (hequiv r).mpr hr
        exact ⟨_, List.mem_singleton_self _, h.1, h.2.1⟩
    · have hc2 : 2 ≤ vu - vv := by omega
      cases fuel with
        | zero =>
          exfalso
          have hdepth : depth = mignotteBisectionDepth cs := by omega
          have hpR0 : pR ≠ 0 :=
            (Polynomial.map_ne_zero_iff (algebraMap ℚ ℝ).injective).mpr hsep.ne_zero
          have hcard :
              2 ≤ (pR.roots.toFinset.filter (fun r => (u : ℝ) < r ∧ r ≤ (v : ℝ))).card := by
            rw [← card_roots_Ioc_eq hsep huv, ← hvu, ← hvv]
            exact hc2
          obtain ⟨α, β, hα, hβ, _, hαβ, hβv⟩ := exists_two_roots_Ioc_of_two_le hpR0 hcard
          have hd2 : 2 ≤ (ofCoeffList cs).natDegree :=
            natDegree_ge_two_of_two_roots hsep hα hβ hαβ.ne
          have hsep_w := dyadic_width_lt_root_sep hsep hd2 hα hβ hαβ.ne
          rw [← hdepth, abs_of_neg (sub_neg.mpr hαβ), neg_sub] at hsep_w
          have hw' : (v : ℝ) - (u : ℝ) ≤ 2 * (cauchyBoundNat cs : ℝ) / (2 : ℝ) ^ depth := by
            simpa only [Rat.cast_sub] using hwidth
          linarith
        | succ fuel' =>
          simp only [TimeM.ret_bind, sturmVariationsM_ret, TimeM.ret_pure]
          let m := (u + v) / 2
          let vm := sturmVariationsList (sturmSeqList cs) m
          have hum : u ≤ m := by dsimp only [m]; linarith
          have hmv : m ≤ v := by dsimp only [m]; linarith
          have hvm_le : vm ≤ vu := hvu ▸ sturmVariationsList_antitone hsep hum
          have hvv_le : vv ≤ vm := hvv ▸ sturmVariationsList_antitone hsep hmv
          have ⟨hwidth', hwidth''⟩ := dyadic_half_width_le hwidth
          have ihL := isolateIocM_spec hsep fuel' (depth + 1) u m vu vm (by omega) hum hvu rfl
            hwidth'
          have ihR := isolateIocM_spec hsep fuel' (depth + 1) m v vm vv (by omega) hmv rfl hvv
            hwidth''
          rcases ihL with ⟨ihL_iso, ihL_pw, ihL_len, ihL_sub, ihL_comp⟩
          rcases ihR with ⟨ihR_iso, ihR_pw, ihR_len, ihR_sub, ihR_comp⟩
          refine ⟨?_, ?_, ?_, ?_, ?_⟩
          · intro I hI
            rw [List.mem_append] at hI
            rcases hI with hIL | hIR
            · obtain ⟨hi, hl, hu, hs⟩ := ihL_iso I hIL
              exact ⟨hi, hl, hu.trans hmv, hs⟩
            · obtain ⟨hi, hl, hu, hs⟩ := ihR_iso I hIR
              refine ⟨hi, hum.trans hl, hu, fun _ => ?_⟩
              by_cases heqm : u = m
              · have huv_eq : u = v := by
                  dsimp only [m] at heqm
                  linarith
                subst huv_eq
                omega
              · exact lt_of_lt_of_le (lt_of_le_of_ne hum heqm) hl
          · refine pairwise_append_of_intervalGapOk ihL_pw ihR_pw ?_
            intro I₁ hI₁ I₂ hI₂
            obtain ⟨_, _, h1up, _⟩ := ihL_iso I₁ hI₁
            obtain ⟨_, h2low, _, h2strict⟩ := ihR_iso I₂ hI₂
            refine intervalGapOk_of_mid h1up h2low fun hm0 => h2strict ?_
            rw [eval_rat_eq_zero_iff]
            exact hm0
          · rw [List.length_append, ihL_len, ihR_len]
            omega
          · intro I hI r hr
            rw [List.mem_append] at hI
            rcases hI with hIL | hIR
            · obtain ⟨hur, hrm⟩ := ihL_sub I hIL r hr
              exact ⟨hur, hrm.trans (Rat.cast_le.mpr hmv)⟩
            · obtain ⟨hmr, hrv⟩ := ihR_sub I hIR r hr
              exact ⟨lt_of_le_of_lt (Rat.cast_le.mpr hum) hmr, hrv⟩
          · intro r ⟨hur, hrv, hrr⟩
            rcases le_or_gt r (m : ℝ) with hrm | hmr
            · obtain ⟨I, hIL, hl, hu⟩ := ihL_comp r ⟨hur, hrm, hrr⟩
              exact ⟨I, List.mem_append_left _ hIL, hl, hu⟩
            · obtain ⟨I, hIR, hl, hu⟩ := ihR_comp r ⟨hmr, hrv, hrr⟩
              exact ⟨I, List.mem_append_right _ hIR, hl, hu⟩

private theorem isolateRoots_spec_aux {cs : List ℚ} (hsep : (ofCoeffList cs).Separable) :
    let b : ℚ := (cauchyBoundNat cs : ℚ)
    let seq := sturmSeqList cs
    let pR := (ofCoeffList cs).map (algebraMap ℚ ℝ)
    (∀ I ∈ isolateRoots cs, I.IsIsolatingFor pR) ∧
      (isolateRoots cs).Pairwise (IntervalGapOk pR) ∧
      (isolateRoots cs).length =
        sturmVariationsList seq (-b) - sturmVariationsList seq b ∧
      ∀ r : ℝ, (( (-b : ℚ) : ℝ) < r ∧ r ≤ (b : ℝ) ∧ pR.IsRoot r) →
        ∃ I ∈ isolateRoots cs, (I.lower : ℝ) ≤ r ∧ r ≤ (I.upper : ℝ) := by
  have hp0 : ofCoeffList cs ≠ 0 := hsep.ne_zero
  have htnil : trim cs ≠ [] := fun hnil =>
    hp0 (by rw [← ofCoeffList_trim cs, hnil, ofCoeffList_nil])
  have hte : (trim cs).isEmpty = false := List.isEmpty_eq_false_iff.mpr htnil
  let b : ℚ := (cauchyBoundNat cs : ℚ)
  let seq := sturmSeqList cs
  have hb_nonneg : (0 : ℚ) ≤ b := Nat.cast_nonneg _
  have hwidth0 : ((b : ℝ) - ((-b : ℚ) : ℝ)) ≤ 2 * (cauchyBoundNat cs : ℝ) / (2 : ℝ) ^ 0 := by
    simp only [Rat.cast_neg, sub_neg_eq_add, pow_zero, div_one, Rat.cast_natCast, two_mul, b]
    rfl
  have hspec := isolateIocM_spec hsep (mignotteBisectionDepth cs) 0 (-b) b
    (sturmVariationsList seq (-b)) (sturmVariationsList seq b) (Nat.zero_add _)
    (by linarith) rfl rfl hwidth0
  have heq : isolateRoots cs = (isolateIocM (trim cs) seq (mignotteBisectionDepth cs)
      (mignotteBisectionDepth cs) (-b) b
      (sturmVariationsList seq (-b)) (sturmVariationsList seq b)).ret := by
    simp only [isolateRoots, isolateRootsM, hte, Bool.false_eq_true, ↓reduceIte,
      TimeM.ret_bind, sturmVariationsM_ret]
    rfl
  rw [heq]
  exact ⟨fun I hI => (hspec.1 I hI).1, hspec.2.1, hspec.2.2.1, hspec.2.2.2.2⟩

/-- Soundness: every rational interval returned by `isolateRoots cs` isolates a unique real root
of `(ofCoeffList cs).map (algebraMap ℚ ℝ)`. -/
theorem isolateRoots_isIsolatingFor {cs : List ℚ} (hsep : (ofCoeffList cs).Separable) :
    ∀ I ∈ isolateRoots cs, I.IsIsolatingFor ((ofCoeffList cs).map (algebraMap ℚ ℝ)) :=
  (isolateRoots_spec_aux hsep).1

/-- Ordering: consecutive intervals returned by `isolateRoots cs` satisfy `I₁.upper ≤ I₂.lower`. -/
theorem isolateRoots_pairwise {cs : List ℚ} (hsep : (ofCoeffList cs).Separable) :
    (isolateRoots cs).Pairwise (fun I₁ I₂ => I₁.upper ≤ I₂.lower) := by
  refine (isolateRoots_spec_aux hsep).2.1.imp fun {I₁ I₂} hgap => ?_
  rcases hgap with hlt | ⟨heq_lu, _⟩
  · exact hlt.le
  · exact heq_lu.le

private theorem isolateRoots_intervalGapOk {cs : List ℚ} (hsep : (ofCoeffList cs).Separable) :
    (isolateRoots cs).Pairwise (IntervalGapOk ((ofCoeffList cs).map (algebraMap ℚ ℝ))) :=
  (isolateRoots_spec_aux hsep).2.1

/-- Completeness: every real root of `(ofCoeffList cs).map (algebraMap ℚ ℝ)` belongs to at least
one isolating interval in `isolateRoots cs`, and that interval is unique in the list. -/
theorem isolateRoots_complete {cs : List ℚ} (hsep : (ofCoeffList cs).Separable) {r : ℝ}
    (hr : ((ofCoeffList cs).map (algebraMap ℚ ℝ)).IsRoot r) :
    ∃! i : Fin (isolateRoots cs).length,
      let I := (isolateRoots cs)[i]
      (I.lower : ℝ) ≤ r ∧ r ≤ (I.upper : ℝ) := by
  have hp0 : ofCoeffList cs ≠ 0 := hsep.ne_zero
  let b : ℚ := (cauchyBoundNat cs : ℚ)
  have hcb := abs_lt_cauchyBoundNat_of_isRoot hp0 hr
  have hr_mem : ((-b : ℚ) : ℝ) < r ∧ r ≤ ((b : ℚ) : ℝ) := by
    rw [abs_lt] at hcb
    simp only [Rat.cast_neg, Rat.cast_natCast, b]
    exact ⟨hcb.1, hcb.2.le⟩
  obtain ⟨I, hI_mem, hlow, hup⟩ :=
    (isolateRoots_spec_aux hsep).2.2.2 r ⟨hr_mem.1, hr_mem.2, hr⟩
  obtain ⟨k, hk_lt, hk_eq⟩ := List.mem_iff_getElem.mp hI_mem
  refine ⟨⟨k, hk_lt⟩, ?_, ?_⟩
  · dsimp only
    rw [Fin.getElem_fin, hk_eq]
    exact ⟨hlow, hup⟩
  · intro j ⟨hj_low, hj_up⟩
    rw [Fin.getElem_fin] at hj_low hj_up
    by_contra hne
    have hgap_pw := isolateRoots_intervalGapOk hsep
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hlt
    · have hlt' : j.1 < k := hlt
      have hgap := (List.pairwise_iff_getElem.mp hgap_pw) j.1 k j.2 hk_lt hlt'
      rcases hgap with hupper_lt | ⟨hupper_eq, hnot0⟩
      · have h1 : (r : ℝ) < ((isolateRoots cs)[k].lower : ℝ) :=
          lt_of_le_of_lt hj_up (Rat.cast_lt.mpr hupper_lt)
        rw [hk_eq] at h1
        linarith
      · have heq_r : r = ((isolateRoots cs)[j.1].upper : ℝ) := by
          have hlo : ((isolateRoots cs)[k].lower : ℝ) ≤ r := by
            rw [hk_eq]
            exact hlow
          have heqR : ((isolateRoots cs)[j.1].upper : ℝ) = ((isolateRoots cs)[k].lower : ℝ) :=
            congrArg Rat.cast hupper_eq
          linarith
        apply hnot0
        rw [← heq_r]
        exact hr.eq_zero
    · have hlt' : k < j.1 := hlt
      have hgap := (List.pairwise_iff_getElem.mp hgap_pw) k j.1 hk_lt j.2 hlt'
      rcases hgap with hupper_lt | ⟨hupper_eq, hnot0⟩
      · have h1 : (r : ℝ) < ((isolateRoots cs)[j.1].lower : ℝ) := by
          have hup' : r ≤ ((isolateRoots cs)[k].upper : ℝ) := by
            rw [hk_eq]
            exact hup
          exact lt_of_le_of_lt hup' (Rat.cast_lt.mpr hupper_lt)
        linarith
      · have heq_r : r = ((isolateRoots cs)[k].upper : ℝ) := by
          have hup' : r ≤ ((isolateRoots cs)[k].upper : ℝ) := by
            rw [hk_eq]
            exact hup
          have heqR : ((isolateRoots cs)[k].upper : ℝ) = ((isolateRoots cs)[j.1].lower : ℝ) :=
            congrArg Rat.cast hupper_eq
          linarith
        apply hnot0
        rw [← heq_r]
        exact hr.eq_zero

/-- The number of isolating intervals returned by `isolateRoots cs` equals the number of real
roots of `(ofCoeffList cs).map (algebraMap ℚ ℝ)`. -/
theorem isolateRoots_length_eq_card_roots {cs : List ℚ} (hsep : (ofCoeffList cs).Separable) :
    (isolateRoots cs).length =
      ((ofCoeffList cs).map (algebraMap ℚ ℝ)).roots.toFinset.card := by
  have hp0 : ofCoeffList cs ≠ 0 := hsep.ne_zero
  let b : ℚ := (cauchyBoundNat cs : ℚ)
  have hb0 : (0 : ℚ) ≤ b := Nat.cast_nonneg _
  rw [(isolateRoots_spec_aux hsep).2.2.1, card_roots_Ioc_eq hsep (by linarith : -b ≤ b)]
  let pR := (ofCoeffList cs).map (algebraMap ℚ ℝ)
  have hpR0 : pR ≠ 0 := (Polynomial.map_ne_zero_iff (algebraMap ℚ ℝ).injective).mpr hp0
  congr 1
  ext r
  simp only [Finset.mem_filter, Multiset.mem_toFinset, and_iff_left_iff_imp]
  intro hr
  have hcb := abs_lt_cauchyBoundNat_of_isRoot hp0 ((mem_roots hpR0).mp hr)
  rw [abs_lt] at hcb
  simp only [Rat.cast_neg, Rat.cast_natCast, b]
  exact ⟨hcb.1, hcb.2.le⟩

/-- The unique real root inside the `i`-th isolating interval of `isolateRoots cs`. -/
noncomputable def isolatedRoot {cs : List ℚ} (hsep : (ofCoeffList cs).Separable)
    (i : Fin (isolateRoots cs).length) :
    {r : ℝ // ((ofCoeffList cs).map (algebraMap ℚ ℝ)).IsRoot r} :=
  let I := (isolateRoots cs)[i]
  let hex := (isolateRoots_isIsolatingFor hsep I (List.getElem_mem i.2)).2.exists
  ⟨Classical.choose hex, let ⟨_, _, hroot⟩ := Classical.choose_spec hex; hroot⟩

/-- Membership of `isolatedRoot hsep i` in the `i`-th isolating interval of `isolateRoots cs`. -/
theorem isolatedRoot_mem {cs : List ℚ} (hsep : (ofCoeffList cs).Separable)
    (i : Fin (isolateRoots cs).length) :
    let I := (isolateRoots cs)[i]
    let r := (isolatedRoot hsep i).1
    (I.lower : ℝ) ≤ r ∧ r ≤ (I.upper : ℝ) := by
  let I := (isolateRoots cs)[i]
  let hex := (isolateRoots_isIsolatingFor hsep I (List.getElem_mem i.2)).2.exists
  have hspec := Classical.choose_spec hex
  exact ⟨hspec.1, hspec.2.1⟩

/-- The isolated real roots are strictly increasing across `Fin (isolateRoots cs).length`. -/
theorem isolatedRoot_strictMono {cs : List ℚ} (hsep : (ofCoeffList cs).Separable) :
    StrictMono (fun i : Fin (isolateRoots cs).length => (isolatedRoot hsep i).1) := by
  intro i j hij
  have hmem_i := isolatedRoot_mem hsep i
  have hmem_j := isolatedRoot_mem hsep j
  dsimp only at hmem_i hmem_j
  rw [Fin.getElem_fin] at hmem_i hmem_j
  have hgap := (List.pairwise_iff_getElem.mp (isolateRoots_intervalGapOk hsep))
    i.1 j.1 i.2 j.2 hij
  rcases hgap with hlt | ⟨heq, hnot0⟩
  · have hltR : ((isolateRoots cs)[i.1].upper : ℝ) < ((isolateRoots cs)[j.1].lower : ℝ) :=
      Rat.cast_lt.mpr hlt
    exact lt_of_le_of_lt hmem_i.2 (lt_of_lt_of_le hltR hmem_j.1)
  · have heqR : ((isolateRoots cs)[i.1].upper : ℝ) = ((isolateRoots cs)[j.1].lower : ℝ) :=
      congrArg Rat.cast heq
    have hle : (isolatedRoot hsep i).1 ≤ (isolatedRoot hsep j).1 := by
      calc (isolatedRoot hsep i).1
          ≤ ((isolateRoots cs)[i.1].upper : ℝ) := hmem_i.2
        _ = ((isolateRoots cs)[j.1].lower : ℝ) := heqR
        _ ≤ (isolatedRoot hsep j).1 := hmem_j.1
    refine lt_of_le_of_ne hle ?_
    intro hreq
    apply hnot0
    have hri_val : (isolatedRoot hsep i).1 = ((isolateRoots cs)[i.1].upper : ℝ) :=
      le_antisymm hmem_i.2 (by
        change (isolatedRoot hsep i).1 = (isolatedRoot hsep j).1 at hreq
        linarith [hmem_j.1])
    rw [← hri_val]
    exact (isolatedRoot hsep i).2.eq_zero

/-- Exact bijection between isolating interval indices `Fin (isolateRoots cs).length` and the set
of real roots `{r : ℝ // ((ofCoeffList cs).map (algebraMap ℚ ℝ)).IsRoot r}`. -/
theorem isolateRoots_bijective {cs : List ℚ} (hsep : (ofCoeffList cs).Separable) :
    Function.Bijective (isolatedRoot hsep) := by
  refine ⟨?_, ?_⟩
  · intro i j hij
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact (isolatedRoot_strictMono hsep hlt).ne (congrArg Subtype.val hij)
    · exact (isolatedRoot_strictMono hsep hgt).ne (congrArg Subtype.val hij).symm
  · rintro ⟨r, hr⟩
    obtain ⟨i, hi_mem, _⟩ := isolateRoots_complete hsep hr
    refine ⟨i, Subtype.ext ?_⟩
    have huniq := (isolateRoots_isIsolatingFor hsep (isolateRoots cs)[i]
      (List.getElem_mem i.2)).2
    have hri := isolatedRoot_mem hsep i
    exact huniq.unique ⟨hri.1, hri.2, (isolatedRoot hsep i).2⟩ ⟨hi_mem.1, hi_mem.2, hr⟩

/-- `TimeM ℕ` bisection/evaluation tick upper bound for `isolateRootsM cs` in terms of `natDegree`
and `mignotteBisectionDepth cs` (preprocessing and scalar/list control steps cost `0` ticks). -/
theorem isolateRootsM_time_le {cs : List ℚ} (hsep : (ofCoeffList cs).Separable) :
    let d := (ofCoeffList cs).natDegree
    let k := mignotteBisectionDepth cs
    let cOp := (d + 1) ^ 2 + (d + 1)
    let cEv := d + 1
    (isolateRootsM cs).time ≤ 2 * cOp + k * (d / 2) * cOp + d * (2 * cEv + k * (cOp + cEv)) := by
  dsimp only
  let d := (ofCoeffList cs).natDegree
  let k := mignotteBisectionDepth cs
  let cOp := (d + 1) ^ 2 + (d + 1)
  let cEv := d + 1
  have hp0 : ofCoeffList cs ≠ 0 := hsep.ne_zero
  have htnil : trim cs ≠ [] := fun hnil =>
    hp0 (by rw [← ofCoeffList_trim cs, hnil, ofCoeffList_nil])
  have hte : (trim cs).isEmpty = false := List.isEmpty_eq_false_iff.mpr htnil
  have ht_len : (trim cs).length ≤ cEv := by
    have hdeg : (ofCoeffList cs).natDegree + 1 = (trim cs).length := by
      rw [← ofCoeffList_trim cs]
      exact (isTrimmed_trim cs).natDegree_add_one htnil
    omega
  have hs_le : sturmSeqOpCost (sturmSeqList cs) ≤ cOp := sturmSeqOpCost_le cs
  let b : ℚ := (cauchyBoundNat cs : ℚ)
  let seq := sturmSeqList cs
  let vL := sturmVariationsList seq (-b)
  let vR := sturmVariationsList seq b
  have hc_le : vL - vR ≤ d := by
    have hb0 : (0 : ℚ) ≤ b := Nat.cast_nonneg _
    have heq := card_roots_Ioc_eq hsep (by linarith : -b ≤ b)
    have hpR_deg : ((ofCoeffList cs).map (algebraMap ℚ ℝ)).natDegree = d :=
      Polynomial.natDegree_map_eq_of_injective (algebraMap ℚ ℝ).injective _
    have hcard_le : (((ofCoeffList cs).map (algebraMap ℚ ℝ)).roots.toFinset.filter
        (fun r : ℝ => ((-b : ℚ) : ℝ) < r ∧ r ≤ (b : ℝ))).card ≤ d := by
      calc _ ≤ ((ofCoeffList cs).map (algebraMap ℚ ℝ)).roots.toFinset.card :=
            Finset.card_filter_le _ _
        _ ≤ ((ofCoeffList cs).map (algebraMap ℚ ℝ)).roots.card := Multiset.toFinset_card_le _
        _ ≤ ((ofCoeffList cs).map (algebraMap ℚ ℝ)).natDegree := Polynomial.card_roots' _
        _ = d := hpR_deg
    change sturmVariationsList seq (-b) - sturmVariationsList seq b ≤ d
    rw [heq]
    exact hcard_le
  simp only [isolateRootsM, hte, Bool.false_eq_true, ↓reduceIte, TimeM.time_bind,
    sturmVariationsM_time, sturmVariationsM_ret]
  have hb0 : (0 : ℚ) ≤ b := Nat.cast_nonneg _
  have hrec := isolateIocM_time_le hsep (trim cs) k k (-b) b vL vR (by linarith) rfl rfl
  let sCost := sturmSeqOpCost seq
  let lCost := 2 * (trim cs).length + k * (sCost + (trim cs).length)
  have hl_le : lCost ≤ 2 * cEv + k * (cOp + cEv) := by
    dsimp only [lCost, sCost]
    gcongr
  have hsplit_le : (if vL - vR ≤ 1 then 0 else k * ((vL - vR) / 2)) ≤ k * (d / 2) := by
    split_ifs
    · exact Nat.zero_le _
    · have hhalf : (vL - vR) / 2 ≤ d / 2 := by omega
      exact Nat.mul_le_mul_left k hhalf
  calc sCost + (sCost + (isolateIocM (trim cs) seq k k (-b) b vL vR).time)
      ≤ sCost + (sCost + ((if vL - vR ≤ 1 then 0 else k * ((vL - vR) / 2)) * sCost +
          (vL - vR) * lCost)) := by gcongr
    _ ≤ cOp + (cOp + (k * (d / 2) * cOp + d * (2 * cEv + k * (cOp + cEv)))) := by gcongr
    _ = 2 * cOp + k * (d / 2) * cOp + d * (2 * cEv + k * (cOp + cEv)) := by ring

/-- Soundness for squarefree `ofCoeffList cs`: every interval in `isolateRoots cs` isolates a
unique real root. -/
theorem isolateRoots_isIsolatingFor_of_squarefree {cs : List ℚ}
    (hsq : Squarefree (ofCoeffList cs)) :
    ∀ I ∈ isolateRoots cs, I.IsIsolatingFor ((ofCoeffList cs).map (algebraMap ℚ ℝ)) :=
  isolateRoots_isIsolatingFor (PerfectField.separable_iff_squarefree.mpr hsq)

/-- Bijection onto real roots for squarefree `ofCoeffList cs`. -/
theorem isolateRoots_bijective_of_squarefree {cs : List ℚ}
    (hsq : Squarefree (ofCoeffList cs)) :
    Function.Bijective (isolatedRoot (PerfectField.separable_iff_squarefree.mpr hsq)) :=
  isolateRoots_bijective (PerfectField.separable_iff_squarefree.mpr hsq)

/-- Bisection/evaluation time bound for `isolateRootsM cs` when `ofCoeffList cs` is squarefree. -/
theorem isolateRootsM_time_le_of_squarefree {cs : List ℚ}
    (hsq : Squarefree (ofCoeffList cs)) :
    let d := (ofCoeffList cs).natDegree
    let k := mignotteBisectionDepth cs
    let cOp := (d + 1) ^ 2 + (d + 1)
    let cEv := d + 1
    (isolateRootsM cs).time ≤ 2 * cOp + k * (d / 2) * cOp + d * (2 * cEv + k * (cOp + cEv)) :=
  isolateRootsM_time_le (PerfectField.separable_iff_squarefree.mpr hsq)

/-- Real-root isolation for an arbitrary polynomial `p : ℚ[X]` via `Polynomial.coeffsBelow`. -/
noncomputable def isolatePolyRoots (p : ℚ[X]) : List RootInterval :=
  isolateRoots (p.coeffsBelow (p.natDegree + 1))

/-- Cost-tracked real-root isolation for an arbitrary polynomial `p : ℚ[X]`. -/
noncomputable def isolatePolyRootsM (p : ℚ[X]) : TimeM ℕ (List RootInterval) :=
  isolateRootsM (p.coeffsBelow (p.natDegree + 1))

/-- Soundness for `isolatePolyRoots p` on squarefree `p : ℚ[X]`. -/
theorem isolatePolyRoots_isIsolatingFor {p : ℚ[X]} (hsq : Squarefree p) :
    ∀ I ∈ isolatePolyRoots p, I.IsIsolatingFor (p.map (algebraMap ℚ ℝ)) := by
  have heq : ofCoeffList (p.coeffsBelow (p.natDegree + 1)) = p :=
    Polynomial.ofCoeffList_coeffsBelow (Nat.lt_succ_self p.natDegree)
  have hmap_eq : p.map (algebraMap ℚ ℝ) =
      (ofCoeffList (p.coeffsBelow (p.natDegree + 1))).map (algebraMap ℚ ℝ) := by
    rw [heq]
  rw [isolatePolyRoots, hmap_eq]
  exact isolateRoots_isIsolatingFor_of_squarefree (heq.symm ▸ hsq)

/-- Ordering: consecutive intervals in `isolatePolyRoots p` satisfy `I₁.upper ≤ I₂.lower`. -/
theorem isolatePolyRoots_pairwise {p : ℚ[X]} (hsq : Squarefree p) :
    (isolatePolyRoots p).Pairwise (fun I₁ I₂ => I₁.upper ≤ I₂.lower) := by
  have heq : ofCoeffList (p.coeffsBelow (p.natDegree + 1)) = p :=
    Polynomial.ofCoeffList_coeffsBelow (Nat.lt_succ_self p.natDegree)
  exact isolateRoots_pairwise (PerfectField.separable_iff_squarefree.mpr (heq.symm ▸ hsq))

private theorem polySeparable {p : ℚ[X]} (hsq : Squarefree p) :
    (ofCoeffList (p.coeffsBelow (p.natDegree + 1))).Separable :=
  PerfectField.separable_iff_squarefree.mpr
    ((Polynomial.ofCoeffList_coeffsBelow (Nat.lt_succ_self p.natDegree)).symm ▸ hsq)

/-- The unique real root of `p.map (algebraMap ℚ ℝ)` inside the `i`-th isolating interval of
`isolatePolyRoots p`. -/
noncomputable def polyIsolatedRoot {p : ℚ[X]} (hsq : Squarefree p)
    (i : Fin (isolatePolyRoots p).length) :
    {r : ℝ // (p.map (algebraMap ℚ ℝ)).IsRoot r} :=
  let r := (isolatedRoot (polySeparable hsq) i).1
  ⟨r, (congrArg (fun q : ℚ[X] => (q.map (algebraMap ℚ ℝ)).IsRoot r)
      (Polynomial.ofCoeffList_coeffsBelow (Nat.lt_succ_self p.natDegree))).mp
      (isolatedRoot (polySeparable hsq) i).2⟩

/-- Membership of `polyIsolatedRoot hsq i` in the `i`-th isolating interval of
`isolatePolyRoots p`. -/
theorem polyIsolatedRoot_mem {p : ℚ[X]} (hsq : Squarefree p)
    (i : Fin (isolatePolyRoots p).length) :
    let I := (isolatePolyRoots p)[i]
    let r := (polyIsolatedRoot hsq i).1
    (I.lower : ℝ) ≤ r ∧ r ≤ (I.upper : ℝ) :=
  isolatedRoot_mem (polySeparable hsq) i

/-- The isolated real roots of `p.map (algebraMap ℚ ℝ)` are strictly increasing across
`Fin (isolatePolyRoots p).length`. -/
theorem polyIsolatedRoot_strictMono {p : ℚ[X]} (hsq : Squarefree p) :
    StrictMono (fun i : Fin (isolatePolyRoots p).length => (polyIsolatedRoot hsq i).1) :=
  isolatedRoot_strictMono (polySeparable hsq)

/-- For any squarefree `p : ℚ[X]`, `polyIsolatedRoot hsq` is a bijection from
`Fin (isolatePolyRoots p).length` onto the real roots of `p.map (algebraMap ℚ ℝ)`. -/
theorem isolatePolyRoots_bijective {p : ℚ[X]} (hsq : Squarefree p) :
    Function.Bijective (polyIsolatedRoot hsq) := by
  have heq : ofCoeffList (p.coeffsBelow (p.natDegree + 1)) = p :=
    Polynomial.ofCoeffList_coeffsBelow (Nat.lt_succ_self p.natDegree)
  have hbij := isolateRoots_bijective (polySeparable hsq)
  refine ⟨fun i j hij => ?_, fun ⟨r, hr⟩ => ?_⟩
  · have hij' : (polyIsolatedRoot hsq i).1 = (polyIsolatedRoot hsq j).1 :=
      congrArg Subtype.val hij
    exact hbij.1 (Subtype.ext hij')
  · have hr' : ((ofCoeffList (p.coeffsBelow (p.natDegree + 1))).map (algebraMap ℚ ℝ)).IsRoot r :=
      heq.symm ▸ hr
    obtain ⟨i, hi⟩ := hbij.2 ⟨r, hr'⟩
    have hi' : (polyIsolatedRoot hsq i).1 = r := congrArg Subtype.val hi
    exact ⟨i, Subtype.ext hi'⟩

/-- Bisection/evaluation time bound for `isolatePolyRootsM p` on squarefree `p : ℚ[X]`. -/
theorem isolatePolyRootsM_time_le {p : ℚ[X]} (hsq : Squarefree p) :
    let cs := p.coeffsBelow (p.natDegree + 1)
    let d := p.natDegree
    let k := mignotteBisectionDepth cs
    let cOp := (d + 1) ^ 2 + (d + 1)
    let cEv := d + 1
    (isolatePolyRootsM p).time ≤
      2 * cOp + k * (d / 2) * cOp + d * (2 * cEv + k * (cOp + cEv)) := by
  dsimp only [isolatePolyRootsM]
  have heq : ofCoeffList (p.coeffsBelow (p.natDegree + 1)) = p :=
    Polynomial.ofCoeffList_coeffsBelow (Nat.lt_succ_self p.natDegree)
  have hle := isolateRootsM_time_le_of_squarefree (cs := p.coeffsBelow (p.natDegree + 1))
    (heq.symm ▸ hsq)
  simpa only [heq] using hle

end Cslib.RealRoot
