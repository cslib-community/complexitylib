/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Algebra.Polynomial.RealRoot.TotalRatPoly

/-!
# End-to-End `TimeM`-Charged Real-Root Isolation with Disjoint Isolating Intervals

This module completes the end-to-end `TimeM ℕ`-charged computable Sturm-bisection real-root
isolator `isolateRootsTotalM` (and its pure projection `isolateRootsTotal`, together with
`Polynomial ℚ` wrappers `isolatePolyRootsTotalM` and `isolatePolyRootsTotal`).

Unlike the bisection-only `isolateRootsM` in `Isolation.lean`:
1. **All preprocessing and control operations are charged in `TimeM ℕ`:** `trimM`,
   `sturmSeqListM` (including `derivListM` and Euclidean polynomial divisions), `cauchyBoundNatM`,
   `mignotteBisectionDepthM` (including `lcmDensM`, `clearDenomsListM`, `sqNormListM`, `powNatM`,
   and `clog4M`), midpoint arithmetic, comparisons, variation subtractions, list appends
   (`appendM`), and boundary-disjointness refinement (`separateTouchingM`).
2. **Strictly disjoint closed rational intervals:** adjacent intervals touching at a non-root
   midpoint are separated via `separateTouchingM`, guaranteeing `I₁.upper < I₂.lower` and pairwise
   disjoint closed real intervals `Set.Icc (I.lower : ℝ) (I.upper : ℝ)`.
3. **Complete `aeval` bijection and polynomial bit-parameterized cost bounds:** for every
   squarefree `p : ℚ[X]` (represented computably by any `cs : List ℚ` with `ofCoeffList cs = p`, or
   via `isolatePolyRootsTotal p`), the returned intervals are in strictly monotone bijection with
   `{x : ℝ // Polynomial.aeval x p = 0}`, with proved `TimeM ℕ` operation-count bounds and dyadic
   endpoint numerator/denominator bounds in `(cs.length, B)` under `HasCoeffBitBound B cs`.

**Model boundary note.** `TimeM ℕ` counts algebraic/RAM operations where primitive `ℚ`, `ℤ`, and
`ℕ` scalar operations cost `O(1)` ticks; compiling Euclidean Sturm remainders to a multi-tape
bit-level Turing machine would additionally track intermediate rational remainder bit-lengths (or
use subresultant pseudo-remainders), whereas all bisection query points and returned interval
endpoints here are dyadic rationals whose bit-lengths are bounded polynomially by
`isolateRootsTotal_endpoint_bounds` and `mignotteBisectionDepth_le_of_bitBound`.

## Main definitions

* `Cslib.RealRoot.refineLeftLoopTotalM`, `Cslib.RealRoot.refineLeftRootTotalM`,
  `Cslib.RealRoot.isolateIocTotalM`: fully step-charged bisection and left-root refinement.
* `Cslib.RealRoot.separateMidLoopM`, `Cslib.RealRoot.separatePairM`,
  `Cslib.RealRoot.separateTouchingM`: `TimeM ℕ`-charged boundary separation producing strictly
  disjoint closed intervals (`I₁.upper < I₂.lower`).
* `Cslib.RealRoot.isolateRootsTotalM`, `Cslib.RealRoot.isolateRootsTotal`,
  `Cslib.RealRoot.totalIsolatedRoot`: computable end-to-end isolator and root bijection on
  `List ℚ`.
* `Cslib.RealRoot.isolatePolyRootsTotalM`, `Cslib.RealRoot.isolatePolyRootsTotal`,
  `Cslib.RealRoot.polyTotalIsolatedRoot`: `Polynomial ℚ` wrappers.

## Main results

* `Cslib.RealRoot.isolateRootsTotal_isIsolatingFor`,
  `Cslib.RealRoot.isolateRootsTotal_pairwise_lt`,
  `Cslib.RealRoot.isolateRootsTotal_pairwise_disjoint`,
  `Cslib.RealRoot.isolateRootsTotal_bijective`: soundness, strict separation, closed-interval
  disjointness, and strictly monotone bijection onto `{x : ℝ // Polynomial.aeval x p = 0}`.
* `Cslib.RealRoot.isolateRootsTotal_endpoint_bounds`: unconditional dyadic numerator/denominator
  bounds on all returned endpoints.
* `Cslib.RealRoot.isolateRootsTotalM_time_le` and
  `Cslib.RealRoot.isolateRootsTotalM_time_le_of_bitBound`: explicit end-to-end `TimeM ℕ` cost
  bounds in `(cs.length, natDegree, mignotteBisectionDepth)` and in `(cs.length, B)`.
* `Cslib.RealRoot.isolatePolyRootsTotal_bijective`,
  `Cslib.RealRoot.isolatePolyRootsTotal_pairwise_disjoint`,
  `Cslib.RealRoot.isolatePolyRootsTotalM_time_le`,
  `Cslib.RealRoot.isolatePolyRootsTotalM_time_le_of_bitBound`: `Polynomial ℚ` theorems.
-/

public section

namespace Cslib.RealRoot

open Polynomial Cslib.Algorithms.Lean

/-! ### Step-charged bisection and left-endpoint refinement -/

/-- Step-charged inner loop shrinking `(u, v]` away from a root at `u`. -/
@[expose] def refineLeftLoopTotalM (t : List ℚ) (seq : List (List ℚ)) :
    ℕ → ℚ → ℚ → ℕ → TimeM ℕ RootInterval
  | 0, u, v, _ => do
    TimeM.tick 1
    pure { lower := u, upper := v }
  | fuel + 1, u, v, vu => do
    TimeM.tick 2
    let m := (u + v) / 2
    let vm ← sturmVariationsListM seq m
    TimeM.tick 1
    if vm = vu then
      pure { lower := m, upper := v }
    else do
      let em ← evalCoeffListM m t
      TimeM.tick 1
      if em = 0 then
        pure { lower := m, upper := m }
      else
        refineLeftLoopTotalM t seq fuel u m vu

@[simp]
theorem refineLeftLoopTotalM_ret (t : List ℚ) (seq : List (List ℚ)) :
    ∀ (fuel : ℕ) (u v : ℚ) (vu : ℕ),
      (refineLeftLoopTotalM t seq fuel u v vu).ret = (refineLeftLoopM t seq fuel u v vu).ret
  | 0, u, v, _ => by
    simp only [refineLeftLoopTotalM, refineLeftLoopM, TimeM.ret_bind, TimeM.ret_pure]
  | fuel + 1, u, v, vu => by
    simp only [refineLeftLoopTotalM, refineLeftLoopM, TimeM.ret_bind, sturmVariationsListM_ret,
      sturmVariationsM_ret]
    split_ifs with hvm
    · simp only [TimeM.ret_pure]
    · simp only [TimeM.ret_bind, evalCoeffListM_ret, evalListM_ret]
      split_ifs with hem
      · simp only [TimeM.ret_pure]
      · exact refineLeftLoopTotalM_ret t seq fuel u ((u + v) / 2) vu

theorem refineLeftLoopTotalM_time_le (t : List ℚ) (seq : List (List ℚ)) :
    ∀ (fuel : ℕ) (u v : ℚ) (vu : ℕ),
      let vCost := 2 * (seq.map List.length).sum + 6 * seq.length + 7
      let eCost := 2 * t.length + 1
      (refineLeftLoopTotalM t seq fuel u v vu).time ≤ fuel * (vCost + eCost + 4) + 1
  | 0, u, v, _ => by
    dsimp only
    simp only [refineLeftLoopTotalM, TimeM.time_bind, TimeM.time_tick, TimeM.time_pure, zero_mul]
  | fuel + 1, u, v, vu => by
    dsimp only
    let m := (u + v) / 2
    have hsv := sturmVariationsListM_time_le seq m
    simp only [refineLeftLoopTotalM, TimeM.time_bind, TimeM.time_tick, sturmVariationsListM_ret]
    have hsplit : (fuel + 1) * ((2 * (seq.map List.length).sum + 6 * seq.length + 7) +
        (2 * t.length + 1) + 4) =
        fuel * ((2 * (seq.map List.length).sum + 6 * seq.length + 7) +
          (2 * t.length + 1) + 4) +
        ((2 * (seq.map List.length).sum + 6 * seq.length + 7) + (2 * t.length + 1) + 4) :=
      Nat.succ_mul fuel _
    split_ifs with hvm
    · simp only [TimeM.time_pure]
      rw [hsplit]
      omega
    · simp only [TimeM.time_bind, evalCoeffListM_time, evalCoeffListM_ret, TimeM.time_tick]
      split_ifs with hem
      · simp only [TimeM.time_pure]
        rw [hsplit]
        omega
      · have ih := refineLeftLoopTotalM_time_le t seq fuel u m vu
        dsimp only [m] at hsv ih
        rw [hsplit]
        omega

/-- Step-charged conversion of a half-open isolating interval `(u, v]` into a closed isolating
interval `[a, b] ⊆ [u, v]`. -/
@[expose] def refineLeftRootTotalM (t : List ℚ) (seq : List (List ℚ)) (fuel : ℕ)
    (u v : ℚ) (vu : ℕ) : TimeM ℕ RootInterval := do
  let ev ← evalCoeffListM v t
  TimeM.tick 1
  if ev = 0 then
    pure { lower := v, upper := v }
  else do
    let eu ← evalCoeffListM u t
    TimeM.tick 1
    if eu ≠ 0 then
      pure { lower := u, upper := v }
    else
      refineLeftLoopTotalM t seq fuel u v vu

@[simp]
theorem refineLeftRootTotalM_ret (t : List ℚ) (seq : List (List ℚ)) (fuel : ℕ)
    (u v : ℚ) (vu : ℕ) :
    (refineLeftRootTotalM t seq fuel u v vu).ret = (refineLeftRootM t seq fuel u v vu).ret := by
  simp only [refineLeftRootTotalM, refineLeftRootM, TimeM.ret_bind, evalCoeffListM_ret,
    evalListM_ret]
  split_ifs with hev
  · simp only [TimeM.ret_pure]
  · simp only [TimeM.ret_bind, evalCoeffListM_ret, evalListM_ret]
    split_ifs with heu
    · simp only [TimeM.ret_pure]
    · exact refineLeftLoopTotalM_ret t seq fuel u v vu

theorem refineLeftRootTotalM_time_le (t : List ℚ) (seq : List (List ℚ)) (fuel : ℕ)
    (u v : ℚ) (vu : ℕ) :
    let vCost := 2 * (seq.map List.length).sum + 6 * seq.length + 7
    let eCost := 2 * t.length + 1
    (refineLeftRootTotalM t seq fuel u v vu).time ≤
      2 * eCost + 3 + fuel * (vCost + eCost + 4) := by
  dsimp only
  simp only [refineLeftRootTotalM, TimeM.time_bind, evalCoeffListM_time, evalCoeffListM_ret,
    TimeM.time_tick]
  split_ifs with hev
  · simp only [TimeM.time_pure]
    omega
  · simp only [TimeM.time_bind, evalCoeffListM_time, evalCoeffListM_ret, TimeM.time_tick]
    split_ifs with heu
    · simp only [TimeM.time_pure]
      omega
    · have hloop := refineLeftLoopTotalM_time_le t seq fuel u v vu
      dsimp only at hloop
      omega

/-- Step-charged recursive Sturm-count bisection on `(u, v]`, charging arithmetic, comparisons,
and list appends (`appendM`). -/
@[expose] def isolateIocTotalM (t : List ℚ) (seq : List (List ℚ)) (depthBound : ℕ) :
    ℕ → ℚ → ℚ → ℕ → ℕ → TimeM ℕ (List RootInterval)
  | fuel, u, v, vu, vv => do
    TimeM.tick 2
    let count := vu - vv
    if count = 0 then
      pure []
    else do
      TimeM.tick 1
      if count = 1 then do
        let rint ← refineLeftRootTotalM t seq depthBound u v vu
        TimeM.tick 1
        pure [rint]
      else
        match fuel with
        | 0 => do
          TimeM.tick 1
          pure []
        | fuel' + 1 => do
          TimeM.tick 2
          let m := (u + v) / 2
          let vm ← sturmVariationsListM seq m
          let left ← isolateIocTotalM t seq depthBound fuel' u m vu vm
          let right ← isolateIocTotalM t seq depthBound fuel' m v vm vv
          appendM left right

@[simp]
theorem isolateIocTotalM_ret (t : List ℚ) (seq : List (List ℚ)) (depthBound : ℕ) :
    ∀ (fuel : ℕ) (u v : ℚ) (vu vv : ℕ),
      (isolateIocTotalM t seq depthBound fuel u v vu vv).ret =
        (isolateIocM t seq depthBound fuel u v vu vv).ret
  | fuel, u, v, vu, vv => by
    unfold isolateIocTotalM isolateIocM
    dsimp only
    simp only [TimeM.ret_bind]
    split_ifs with hc0 hc1
    · simp only [TimeM.ret_pure]
    · simp only [TimeM.ret_bind, refineLeftRootTotalM_ret, TimeM.ret_pure]
    · cases fuel with
      | zero => simp only [TimeM.ret_bind, TimeM.ret_pure]
      | succ fuel' =>
        simp only [TimeM.ret_bind, sturmVariationsListM_ret, sturmVariationsM_ret,
          isolateIocTotalM_ret t seq depthBound fuel', appendM_ret, TimeM.ret_pure]

private theorem isolateIocM_length_le {cs : List ℚ} (hsep : (ofCoeffList cs).Separable)
    (t : List ℚ) (depthBound : ℕ) :
    ∀ (fuel : ℕ) (u v : ℚ) (vu vv : ℕ),
      u ≤ v →
      vu = sturmVariationsList (sturmSeqList cs) u →
      vv = sturmVariationsList (sturmSeqList cs) v →
      ((isolateIocM t (sturmSeqList cs) depthBound fuel u v vu vv).ret).length ≤ vu - vv
  | fuel, u, v, vu, vv, huv, hvu, hvv => by
    unfold isolateIocM
    dsimp only
    split_ifs with hc0 hc1
    · simp only [TimeM.ret_pure, List.length_nil, Nat.zero_le]
    · simp only [TimeM.ret_bind, TimeM.ret_pure, List.length_singleton, hc1, le_refl]
    · cases fuel with
      | zero => simp only [TimeM.ret_pure, List.length_nil, Nat.zero_le]
      | succ fuel' =>
        simp only [TimeM.ret_bind, sturmVariationsM_ret, TimeM.ret_pure, List.length_append]
        let m := (u + v) / 2
        let vm := sturmVariationsList (sturmSeqList cs) m
        have hum : u ≤ m := by dsimp only [m]; linarith
        have hmv : m ≤ v := by dsimp only [m]; linarith
        have h1 : vm ≤ vu := by
          rw [hvu]
          have hsepR : ((ofCoeffList cs).map (algebraMap ℚ ℝ)).Separable := hsep.map
          rw [sturmVariationsList_eq_sturmVariations, sturmVariationsList_eq_sturmVariations]
          exact Polynomial.sturmVariations_antitone hsepR (Rat.cast_le.mpr hum)
        have h2 : vv ≤ vm := by
          rw [hvv]
          have hsepR : ((ofCoeffList cs).map (algebraMap ℚ ℝ)).Separable := hsep.map
          rw [sturmVariationsList_eq_sturmVariations, sturmVariationsList_eq_sturmVariations]
          exact Polynomial.sturmVariations_antitone hsepR (Rat.cast_le.mpr hmv)
        have ihL := isolateIocM_length_le hsep t depthBound fuel' u m vu vm hum hvu rfl
        have ihR := isolateIocM_length_le hsep t depthBound fuel' m v vm vv hmv rfl hvv
        dsimp only [m, vm] at ihL ihR h1 h2
        omega

private theorem sturmVariationsList_le_length (seq : List (List ℚ)) (x : ℚ) :
    sturmVariationsList seq x ≤ seq.length := by
  simp only [sturmVariationsList, List.signVariations]
  let fs := ((seq.map (evalCoeffList x)).map SignType.sign).filter (fun s => decide (s ≠ 0))
  have hsub : (List.destutter (· ≠ ·) fs).length ≤ fs.length :=
    (List.destutter_sublist (· ≠ ·) fs).length_le
  have hfl : fs.length ≤ seq.length := by
    calc fs.length ≤ ((seq.map (evalCoeffList x)).map SignType.sign).length :=
          List.length_filter_le _ _
      _ = seq.length := by simp only [List.length_map]
  omega

private theorem isolateIocTotalM_time_le {cs : List ℚ} (hsep : (ofCoeffList cs).Separable)
    (t : List ℚ) (depthBound : ℕ) :
    ∀ (fuel : ℕ) (u v : ℚ) (vu vv : ℕ),
      u ≤ v →
      vu = sturmVariationsList (sturmSeqList cs) u →
      vv = sturmVariationsList (sturmSeqList cs) v →
      let seq := sturmSeqList cs
      let c := vu - vv
      let vCost := 2 * (seq.map List.length).sum + 6 * seq.length + 7
      let eCost := 2 * t.length + 1
      let sTotal := vCost + seq.length + 10
      let rTotal := 2 * eCost + 6 + depthBound * (vCost + eCost + 4)
      (isolateIocTotalM t seq depthBound fuel u v vu vv).time ≤
        2 + (if c ≤ 1 then 0 else fuel * (c / 2)) * sTotal + c * rTotal
  | fuel, u, v, vu, vv, huv, hvu, hvv => by
    dsimp only
    let seq := sturmSeqList cs
    let c := vu - vv
    let vCost := 2 * (seq.map List.length).sum + 6 * seq.length + 7
    let eCost := 2 * t.length + 1
    let sTotal := vCost + seq.length + 10
    let rTotal := 2 * eCost + 6 + depthBound * (vCost + eCost + 4)
    unfold isolateIocTotalM
    dsimp only
    simp only [TimeM.time_bind, TimeM.time_tick]
    by_cases hc0 : vu - vv = 0
    · simp only [eq_true hc0, ↓reduceIte, TimeM.time_pure]
      omega
    · by_cases hc1 : vu - vv = 1
      · have hc1' : c = 1 := hc1
        simp only [eq_false hc0, eq_true hc1, hc1', eq_true (le_refl (1 : ℕ)), ↓reduceIte,
          TimeM.time_bind, TimeM.time_tick, TimeM.time_pure, zero_mul, one_mul]
        have href := refineLeftRootTotalM_time_le t seq depthBound u v vu
        dsimp only at href
        dsimp only [rTotal, vCost, eCost, seq] at *
        omega
      · have hc2 : 2 ≤ c := by omega
        have hif : ¬c ≤ 1 := by omega
        simp only [eq_false hc0, eq_false hc1, eq_false hif, ↓reduceIte]
        cases fuel with
        | zero =>
          simp only [TimeM.time_bind, TimeM.time_tick, TimeM.time_pure, zero_mul]
          have hr_pos : 1 ≤ rTotal := by dsimp only [rTotal]; omega
          have hc_r : 2 ≤ c * rTotal := by
            calc 2 = 2 * 1 := rfl
              _ ≤ c * rTotal := Nat.mul_le_mul hc2 hr_pos
          omega
        | succ fuel' =>
          simp only [TimeM.time_bind, TimeM.time_tick, sturmVariationsListM_ret,
            isolateIocTotalM_ret, appendM_time]
          let m := (u + v) / 2
          let vm := sturmVariationsList seq m
          have hum : u ≤ m := by dsimp only [m]; linarith
          have hmv : m ≤ v := by dsimp only [m]; linarith
          have hsepR : ((ofCoeffList cs).map (algebraMap ℚ ℝ)).Separable := hsep.map
          have hle_left : vm ≤ vu := by
            rw [hvu]
            dsimp only [vm, seq]
            rw [sturmVariationsList_eq_sturmVariations, sturmVariationsList_eq_sturmVariations]
            exact Polynomial.sturmVariations_antitone hsepR (Rat.cast_le.mpr hum)
          have hle_right : vv ≤ vm := by
            rw [hvv]
            dsimp only [vm, seq]
            rw [sturmVariationsList_eq_sturmVariations, sturmVariationsList_eq_sturmVariations]
            exact Polynomial.sturmVariations_antitone hsepR (Rat.cast_le.mpr hmv)
          have hsv := sturmVariationsListM_time_le seq m
          have hlenL :
              ((isolateIocM t seq depthBound fuel' u m vu vm).ret).length ≤ seq.length := by
            have hl1 := isolateIocM_length_le hsep t depthBound fuel' u m vu vm hum hvu rfl
            have hl2 : vu ≤ seq.length := hvu ▸ sturmVariationsList_le_length seq u
            omega
          have ihL := isolateIocTotalM_time_le hsep t depthBound fuel' u m vu vm hum hvu rfl
          have ihR := isolateIocTotalM_time_le hsep t depthBound fuel' m v vm vv hmv rfl hvv
          let c₁ := vu - vm
          let c₂ := vm - vv
          have hsum_c : c₁ + c₂ = c := by omega
          have hdiv : (if c₁ ≤ 1 then 0 else fuel' * (c₁ / 2)) +
              (if c₂ ≤ 1 then 0 else fuel' * (c₂ / 2)) + 1 ≤ (fuel' + 1) * (c / 2) := by
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
          have hmul_div : ((if c₁ ≤ 1 then 0 else fuel' * (c₁ / 2)) +
              (if c₂ ≤ 1 then 0 else fuel' * (c₂ / 2)) + 1) * sTotal ≤
              (fuel' + 1) * (c / 2) * sTotal := Nat.mul_le_mul_right sTotal hdiv
          have hlin : 2 + (1 + (2 + ((sturmVariationsListM seq m).time +
              ((isolateIocTotalM t seq depthBound fuel' u m vu vm).time +
                ((isolateIocTotalM t seq depthBound fuel' m v vm vv).time +
                  (((isolateIocM t seq depthBound fuel' u m vu vm).ret).length + 1)))))) ≤
              2 + ((if c₁ ≤ 1 then 0 else fuel' * (c₁ / 2)) * sTotal +
                (if c₂ ≤ 1 then 0 else fuel' * (c₂ / 2)) * sTotal + sTotal) +
                (c₁ * rTotal + c₂ * rTotal) := by
            dsimp only [sTotal, vCost, m, vm, seq, c₁, c₂] at *
            omega
          have hring : 2 + ((if c₁ ≤ 1 then 0 else fuel' * (c₁ / 2)) * sTotal +
                (if c₂ ≤ 1 then 0 else fuel' * (c₂ / 2)) * sTotal + sTotal) +
                (c₁ * rTotal + c₂ * rTotal) =
              2 + ((if c₁ ≤ 1 then 0 else fuel' * (c₁ / 2)) +
                (if c₂ ≤ 1 then 0 else fuel' * (c₂ / 2)) + 1) * sTotal +
                (c₁ + c₂) * rTotal := by ring
          dsimp only [m, vm, seq] at hlin
          rw [hring, hsum_c] at hlin
          exact hlin.trans (by omega)

/-! ### Step-charged boundary separation into strictly disjoint closed intervals -/

/-- Bisect `(a, m]` and `(m, b]` around a non-root midpoint `m` until finding `(u₁', l₂')` with
`u₁' < l₂'`, no roots in `(u₁', m]`, and no roots in `(m, l₂']`. -/
@[expose] def separateMidLoopM (seq : List (List ℚ)) :
    ℕ → ℚ → ℚ → ℚ → ℕ → TimeM ℕ (ℚ × ℚ)
  | 0, a, _, b, _ => do
    TimeM.tick 1
    pure (a, b)
  | fuel + 1, a, m, b, vm => do
    TimeM.tick 2
    let m₁ := (a + m) / 2
    let vm₁ ← sturmVariationsListM seq m₁
    TimeM.tick 1
    if vm₁ = vm then
      pure (m₁, m)
    else do
      TimeM.tick 2
      let m₂ := (m + b) / 2
      let vm₂ ← sturmVariationsListM seq m₂
      TimeM.tick 1
      if vm₂ = vm then
        pure (m, m₂)
      else
        separateMidLoopM seq fuel m₁ m m₂ vm

theorem separateMidLoopM_time_le (seq : List (List ℚ)) :
    ∀ (fuel : ℕ) (a m b : ℚ) (vm : ℕ),
      let vCost := 2 * (seq.map List.length).sum + 6 * seq.length + 7
      (separateMidLoopM seq fuel a m b vm).time ≤ fuel * (2 * vCost + 6) + 1
  | 0, _, _, _, _ => by
    dsimp only
    simp only [separateMidLoopM, TimeM.time_bind, TimeM.time_tick, TimeM.time_pure, zero_mul]
  | fuel + 1, a, m, b, vm => by
    dsimp only
    let m₁ := (a + m) / 2
    let m₂ := (m + b) / 2
    have hsv1 := sturmVariationsListM_time_le seq m₁
    have hsv2 := sturmVariationsListM_time_le seq m₂
    have hsplit : (fuel + 1) * (2 * (2 * (seq.map List.length).sum + 6 * seq.length + 7) + 6) =
        fuel * (2 * (2 * (seq.map List.length).sum + 6 * seq.length + 7) + 6) +
          (2 * (2 * (seq.map List.length).sum + 6 * seq.length + 7) + 6) :=
      Nat.succ_mul fuel _
    simp only [separateMidLoopM, TimeM.time_bind, TimeM.time_tick, sturmVariationsListM_ret]
    split_ifs with h1
    · simp only [TimeM.time_pure]
      dsimp only [m₁] at hsv1
      rw [hsplit]
      omega
    · simp only [TimeM.time_bind, TimeM.time_tick, sturmVariationsListM_ret]
      split_ifs with h2
      · simp only [TimeM.time_pure]
        dsimp only [m₁, m₂] at hsv1 hsv2
        rw [hsplit]
        omega
      · have ih := separateMidLoopM_time_le seq fuel m₁ m m₂ vm
        dsimp only [m₁, m₂] at hsv1 hsv2 ih
        rw [hsplit]
        omega

private theorem separateMidLoopM_dyadicBounded (seq : List (List ℚ)) :
    ∀ (fuel B e : ℕ) (a m b : ℚ) (vm : ℕ),
      DyadicBounded B e a → DyadicBounded B e m → DyadicBounded B e b →
      let p := (separateMidLoopM seq fuel a m b vm).ret
      DyadicBounded B (e + fuel) p.1 ∧ DyadicBounded B (e + fuel) p.2
  | 0, B, e, a, _, b, _, ha, _, hb => by
    simp only [separateMidLoopM, TimeM.ret_bind, TimeM.ret_pure, Nat.add_zero]
    exact ⟨ha, hb⟩
  | fuel + 1, B, e, a, m, b, vm, ha, hm, hb => by
    dsimp only [separateMidLoopM]
    simp only [TimeM.ret_bind, sturmVariationsListM_ret]
    have hm1 : DyadicBounded B (e + 1) ((a + m) / 2) := ha.mid hm
    have hm2 : DyadicBounded B (e + 1) ((m + b) / 2) := hm.mid hb
    split_ifs with h1
    · simp only [TimeM.ret_pure]
      exact ⟨hm1.mono (by omega), hm.mono (by omega)⟩
    · simp only [TimeM.ret_bind, sturmVariationsListM_ret]
      split_ifs with h2
      · simp only [TimeM.ret_pure]
        exact ⟨hm.mono (by omega), hm2.mono (by omega)⟩
      · have ih := separateMidLoopM_dyadicBounded seq fuel B (e + 1)
          ((a + m) / 2) m ((m + b) / 2) vm hm1 (hm.mono (by omega)) hm2
        have heq : e + 1 + fuel = e + (fuel + 1) := by omega
        simpa only [heq] using ih

private theorem card_roots_Ioc_eq_sep {cs : List ℚ} (hsep : (ofCoeffList cs).Separable)
    {u v : ℚ} (huv : u ≤ v) :
    sturmVariationsList (sturmSeqList cs) u - sturmVariationsList (sturmSeqList cs) v =
      (((ofCoeffList cs).map (algebraMap ℚ ℝ)).roots.toFinset.filter
        (fun r : ℝ => (u : ℝ) < r ∧ r ≤ (v : ℝ))).card := by
  rw [sturmVariationsList_eq_sturmVariations, sturmVariationsList_eq_sturmVariations]
  exact sturmVariations_sub_eq_card_roots_Ioc hsep.map (Rat.cast_le.mpr huv)

private theorem no_root_Ioc_of_var_eq {cs : List ℚ} (hsep : (ofCoeffList cs).Separable)
    {u v : ℚ} (huv : u ≤ v)
    (h0 : sturmVariationsList (sturmSeqList cs) u - sturmVariationsList (sturmSeqList cs) v = 0)
    {r : ℝ} (hur : (u : ℝ) < r) (hrv : r ≤ (v : ℝ)) :
    ¬((ofCoeffList cs).map (algebraMap ℚ ℝ)).IsRoot r := by
  let pR := (ofCoeffList cs).map (algebraMap ℚ ℝ)
  have hpR0 : pR ≠ 0 := (Polynomial.map_ne_zero_iff (algebraMap ℚ ℝ).injective).mpr hsep.ne_zero
  rw [card_roots_Ioc_eq_sep hsep huv, Finset.card_eq_zero] at h0
  intro hrr
  have hmem : r ∈ pR.roots.toFinset.filter (fun x : ℝ => (u : ℝ) < x ∧ x ≤ (v : ℝ)) := by
    simp only [Finset.mem_filter, Multiset.mem_toFinset, mem_roots hpR0]
    exact ⟨hrr, hur, hrv⟩
  rw [h0] at hmem
  exact Finset.notMem_empty r hmem

private theorem exists_root_Ioc_of_var_pos {cs : List ℚ} (hsep : (ofCoeffList cs).Separable)
    {u v : ℚ} (huv : u ≤ v)
    (hpos : 1 ≤ sturmVariationsList (sturmSeqList cs) u -
      sturmVariationsList (sturmSeqList cs) v) :
    ∃ r : ℝ, (u : ℝ) < r ∧ r ≤ (v : ℝ) ∧ ((ofCoeffList cs).map (algebraMap ℚ ℝ)).IsRoot r := by
  let pR := (ofCoeffList cs).map (algebraMap ℚ ℝ)
  have hpR0 : pR ≠ 0 := (Polynomial.map_ne_zero_iff (algebraMap ℚ ℝ).injective).mpr hsep.ne_zero
  rw [card_roots_Ioc_eq_sep hsep huv] at hpos
  obtain ⟨r, hr⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero (by omega))
  simp only [Finset.mem_filter, Multiset.mem_toFinset, mem_roots hpR0] at hr
  exact ⟨r, hr.2.1, hr.2.2, hr.1⟩

private theorem separateMidLoopM_spec {cs : List ℚ} (hsep : (ofCoeffList cs).Separable) :
    ∀ (fuel depth : ℕ) (a m b : ℚ) (vm : ℕ),
      depth + fuel = mignotteBisectionDepth cs →
      a < m →
      m < b →
      vm = sturmVariationsList (sturmSeqList cs) m →
      sturmVariationsList (sturmSeqList cs) a - vm = 1 →
      vm - sturmVariationsList (sturmSeqList cs) b = 1 →
      ¬((ofCoeffList cs).map (algebraMap ℚ ℝ)).IsRoot (m : ℝ) →
      (b - a : ℝ) ≤ 2 * (cauchyBoundNat cs : ℝ) / (2 : ℝ) ^ depth →
      let res := (separateMidLoopM (sturmSeqList cs) fuel a m b vm).ret
      let pR := (ofCoeffList cs).map (algebraMap ℚ ℝ)
      a ≤ res.1 ∧ res.1 ≤ m ∧ m ≤ res.2 ∧ res.2 ≤ b ∧ res.1 < res.2 ∧
        (∀ r : ℝ, (res.1 : ℝ) < r → r ≤ (m : ℝ) → ¬pR.IsRoot r) ∧
        (∀ r : ℝ, (m : ℝ) < r → r ≤ (res.2 : ℝ) → ¬pR.IsRoot r)
  | 0, depth, a, m, b, vm, hsum, ham, hmb, hvm, hca, hcb, hnotm, hwidth => by
    exfalso
    have hdepth : depth = mignotteBisectionDepth cs := by omega
    rw [hvm] at hca hcb
    obtain ⟨r₁, har₁, hr₁m, hr₁⟩ := exists_root_Ioc_of_var_pos hsep ham.le (by omega)
    obtain ⟨r₂, hmr₂, hr₂b, hr₂⟩ := exists_root_Ioc_of_var_pos hsep hmb.le (by omega)
    have hr₁_lt_m : r₁ < (m : ℝ) := lt_of_le_of_ne hr₁m fun heq => hnotm (heq ▸ hr₁)
    have hr₁₂ : r₁ < r₂ := lt_trans hr₁_lt_m hmr₂
    have p0 : ofCoeffList cs ≠ 0 := hsep.ne_zero
    let pR := (ofCoeffList cs).map (algebraMap ℚ ℝ)
    have hpR0 : pR ≠ 0 := (Polynomial.map_ne_zero_iff (algebraMap ℚ ℝ).injective).mpr p0
    have hmem₁ : r₁ ∈ pR.roots.toFinset := Multiset.mem_toFinset.mpr ((mem_roots hpR0).mpr hr₁)
    have hmem₂ : r₂ ∈ pR.roots.toFinset := Multiset.mem_toFinset.mpr ((mem_roots hpR0).mpr hr₂)
    have hpair : ({r₁, r₂} : Finset ℝ) ⊆ pR.roots.toFinset := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> assumption
    have hcard2 : 2 ≤ pR.roots.toFinset.card := by
      simpa only [Finset.card_pair hr₁₂.ne] using Finset.card_le_card hpair
    have hd2 : 2 ≤ (ofCoeffList cs).natDegree := by
      have hc := (Multiset.toFinset_card_le _).trans (Polynomial.card_roots' pR)
      have hd_eq := Polynomial.natDegree_map_eq_of_injective (algebraMap ℚ ℝ).injective
        (ofCoeffList cs)
      omega
    have hsep_w := dyadic_width_lt_root_sep hsep hd2 hr₁ hr₂ hr₁₂.ne
    rw [← hdepth, abs_of_neg (sub_neg.mpr hr₁₂), neg_sub] at hsep_w
    have hw' : (b : ℝ) - (a : ℝ) ≤ 2 * (cauchyBoundNat cs : ℝ) / (2 : ℝ) ^ depth := by
      simpa only [Rat.cast_sub] using hwidth
    have hba : r₂ - r₁ < (b : ℝ) - (a : ℝ) := by linarith
    linarith
  | fuel + 1, depth, a, m, b, vm, hsum, ham, hmb, hvm, hca, hcb, hnotm, hwidth => by
    let seq := sturmSeqList cs
    let m₁ := (a + m) / 2
    let m₂ := (m + b) / 2
    have ham1 : a < m₁ := by dsimp only [m₁]; linarith
    have hm1m : m₁ < m := by dsimp only [m₁]; linarith
    have hmm2 : m < m₂ := by dsimp only [m₂]; linarith
    have hm2b : m₂ < b := by dsimp only [m₂]; linarith
    have hsepR : ((ofCoeffList cs).map (algebraMap ℚ ℝ)).Separable := hsep.map
    have hanti : ∀ {x y : ℚ}, x ≤ y → sturmVariationsList seq y ≤ sturmVariationsList seq x := by
      intro x y hxy
      dsimp only [seq]
      rw [sturmVariationsList_eq_sturmVariations, sturmVariationsList_eq_sturmVariations]
      exact Polynomial.sturmVariations_antitone hsepR (Rat.cast_le.mpr hxy)
    have hva_m1 : sturmVariationsList seq m₁ ≤ sturmVariationsList seq a := hanti ham1.le
    have hvm1_m : vm ≤ sturmVariationsList seq m₁ := hvm ▸ hanti hm1m.le
    have hvm_m2 : sturmVariationsList seq m₂ ≤ vm := hvm ▸ hanti hmm2.le
    have hvm2_b : sturmVariationsList seq b ≤ sturmVariationsList seq m₂ := hanti hm2b.le
    dsimp only [separateMidLoopM]
    simp only [TimeM.ret_bind, sturmVariationsListM_ret]
    split_ifs with h1
    · simp only [TimeM.ret_pure]
      have h0 : sturmVariationsList seq m₁ - sturmVariationsList seq m = 0 := by
        rw [← hvm]
        change sturmVariationsList seq m₁ - vm = 0
        omega
      refine ⟨ham1.le, hm1m.le, le_rfl, hmb.le, hm1m, fun r h1r hrm =>
        no_root_Ioc_of_var_eq hsep hm1m.le h0 h1r hrm, fun r hmr hrm => ?_⟩
      linarith
    · simp only [TimeM.ret_bind, sturmVariationsListM_ret]
      split_ifs with h2
      · simp only [TimeM.ret_pure]
        have h0 : sturmVariationsList seq m - sturmVariationsList seq m₂ = 0 := by
          rw [← hvm]
          change vm - sturmVariationsList seq m₂ = 0
          omega
        refine ⟨ham.le, le_rfl, hmm2.le, hm2b.le, hmm2, fun r hmr hrm => by linarith,
          fun r hmr hrm2 => no_root_Ioc_of_var_eq hsep hmm2.le h0 hmr hrm2⟩
      · have hca' : sturmVariationsList seq m₁ - vm = 1 := by omega
        have hcb' : vm - sturmVariationsList seq m₂ = 1 := by omega
        have hw_next : (m₂ - m₁ : ℝ) ≤ 2 * (cauchyBoundNat cs : ℝ) / (2 : ℝ) ^ (depth + 1) := by
          have hhalf : (m₂ - m₁ : ℝ) = (b - a : ℝ) / 2 := by
            dsimp only [m₁, m₂]
            push_cast
            ring
          rw [hhalf, pow_succ]
          calc (b - a : ℝ) / 2
              ≤ (2 * (cauchyBoundNat cs : ℝ) / (2 : ℝ) ^ depth) / 2 := by linarith
            _ = 2 * (cauchyBoundNat cs : ℝ) / ((2 : ℝ) ^ depth * 2) := by ring
        have ih := separateMidLoopM_spec hsep fuel (depth + 1) m₁ m m₂ vm (by omega)
          hm1m hmm2 hvm hca' hcb' hnotm hw_next
        rcases ih with ⟨ih1, ih2, ih3, ih4, ihlt, ihn1, ihn2⟩
        exact ⟨ham1.le.trans ih1, ih2, ih3, ih4.trans hm2b.le, ihlt, ihn1, ihn2⟩

/-- Separate the boundary between two consecutive isolating intervals `I₁` and `I₂` in `TimeM ℕ`,
returning `(u₁', l₂')` with `I₁.lower ≤ u₁' ≤ I₁.upper`, `I₂.lower ≤ l₂' ≤ I₂.upper`, and
`u₁' < l₂'`. -/
@[expose] def separatePairM (t : List ℚ) (seq : List (List ℚ)) (depth : ℕ)
    (I₁ I₂ : RootInterval) : TimeM ℕ (ℚ × ℚ) := do
  TimeM.tick 1
  if I₁.upper < I₂.lower then
    pure (I₁.upper, I₂.lower)
  else do
    let el ← evalCoeffListM I₁.lower t
    TimeM.tick 1
    if el = 0 then
      pure (I₁.lower, I₂.lower)
    else do
      let vm ← sturmVariationsListM seq I₁.upper
      separateMidLoopM seq depth I₁.lower I₁.upper I₂.upper vm

theorem separatePairM_time_le (t : List ℚ) (seq : List (List ℚ)) (depth : ℕ)
    (I₁ I₂ : RootInterval) :
    let vCost := 2 * (seq.map List.length).sum + 6 * seq.length + 7
    let eCost := 2 * t.length + 1
    (separatePairM t seq depth I₁ I₂).time ≤
      eCost + vCost + depth * (2 * vCost + 6) + 3 := by
  dsimp only
  simp only [separatePairM, TimeM.time_bind, TimeM.time_tick]
  split_ifs with hlt
  · simp only [TimeM.time_pure]
    omega
  · simp only [TimeM.time_bind, evalCoeffListM_time, evalCoeffListM_ret, TimeM.time_tick]
    split_ifs with hel
    · simp only [TimeM.time_pure]
      omega
    · simp only [TimeM.time_bind, sturmVariationsListM_ret]
      have hsv := sturmVariationsListM_time_le seq I₁.upper
      have hmid := separateMidLoopM_time_le seq depth I₁.lower I₁.upper I₂.upper
        (sturmVariationsList seq I₁.upper)
      dsimp only at hmid
      omega

private theorem separatePairM_dyadicBounded (t : List ℚ) (seq : List (List ℚ))
    (depth B e : ℕ) (I₁ I₂ : RootInterval)
    (h1l : DyadicBounded B e I₁.lower) (h1u : DyadicBounded B e I₁.upper)
    (h2l : DyadicBounded B e I₂.lower) (h2u : DyadicBounded B e I₂.upper) :
    let p := (separatePairM t seq depth I₁ I₂).ret
    DyadicBounded B (e + depth) p.1 ∧ DyadicBounded B (e + depth) p.2 := by
  dsimp only [separatePairM]
  simp only [TimeM.ret_bind]
  split_ifs with hlt
  · simp only [TimeM.ret_pure]
    exact ⟨h1u.mono (by omega), h2l.mono (by omega)⟩
  · simp only [TimeM.ret_bind, evalCoeffListM_ret]
    split_ifs with hel
    · simp only [TimeM.ret_pure]
      exact ⟨h1l.mono (by omega), h2l.mono (by omega)⟩
    · simp only [TimeM.ret_bind, sturmVariationsListM_ret]
      exact separateMidLoopM_dyadicBounded seq depth B e I₁.lower I₁.upper I₂.upper _
        h1l h1u h2u

private theorem eval_trim_eq_zero_iff (cs : List ℚ) (x : ℚ) :
    evalCoeffList x (trim cs) = 0 ↔
      ((ofCoeffList cs).map (algebraMap ℚ ℝ)).IsRoot (x : ℝ) := by
  rw [IsRoot.def, ← ofCoeffList_trim cs]
  have hmap : (algebraMap ℚ ℝ) (eval x (ofCoeffList (trim cs))) =
      ((ofCoeffList (trim cs)).map (algebraMap ℚ ℝ)).eval ((algebraMap ℚ ℝ) x) := by
    rw [Polynomial.eval_map, Polynomial.eval₂_hom]
  have hcast : ((ofCoeffList (trim cs)).map (algebraMap ℚ ℝ)).eval (x : ℝ) =
      ((evalCoeffList x (trim cs) : ℚ) : ℝ) := by
    change ((ofCoeffList (trim cs)).map (algebraMap ℚ ℝ)).eval ((algebraMap ℚ ℝ) x) = _
    rw [← hmap, eval_ofCoeffList]
    rfl
  rw [hcast]
  exact Rat.cast_eq_zero.symm

private theorem separatePairM_spec {cs : List ℚ} (hsep : (ofCoeffList cs).Separable)
    {I₁ I₂ : RootInterval}
    (hiso₁ : I₁.IsIsolatingFor ((ofCoeffList cs).map (algebraMap ℚ ℝ)))
    (hiso₂ : I₂.IsIsolatingFor ((ofCoeffList cs).map (algebraMap ℚ ℝ)))
    (hb₁ : -(cauchyBoundNat cs : ℚ) ≤ I₁.lower)
    (hb₂ : I₂.upper ≤ (cauchyBoundNat cs : ℚ))
    (hgap : IntervalGapOk ((ofCoeffList cs).map (algebraMap ℚ ℝ)) I₁ I₂) :
    let res := (separatePairM (trim cs) (sturmSeqList cs) (mignotteBisectionDepth cs) I₁ I₂).ret
    let pR := (ofCoeffList cs).map (algebraMap ℚ ℝ)
    I₁.lower ≤ res.1 ∧ res.1 ≤ I₁.upper ∧ I₂.lower ≤ res.2 ∧ res.2 ≤ I₂.upper ∧
      res.1 < res.2 ∧
      (∀ r : ℝ, (I₁.lower : ℝ) ≤ r ∧ r ≤ (I₁.upper : ℝ) ∧ pR.IsRoot r → r ≤ (res.1 : ℝ)) ∧
      (∀ r : ℝ, (I₂.lower : ℝ) ≤ r ∧ r ≤ (I₂.upper : ℝ) ∧ pR.IsRoot r → (res.2 : ℝ) ≤ r) := by
  let pR := (ofCoeffList cs).map (algebraMap ℚ ℝ)
  have hpR0 : pR ≠ 0 := (Polynomial.map_ne_zero_iff (algebraMap ℚ ℝ).injective).mpr hsep.ne_zero
  dsimp only [separatePairM]
  simp only [TimeM.ret_bind]
  split_ifs with hlt
  · simp only [TimeM.ret_pure]
    exact ⟨hiso₁.1, le_rfl, le_rfl, hiso₂.1, hlt, fun _ h => h.2.1, fun _ h => h.1⟩
  · rcases hgap with hlt' | ⟨heq_m, hnot0⟩
    · exact absurd hlt' hlt
    · have hnotm : ¬pR.IsRoot (I₁.upper : ℝ) := hnot0
      simp only [TimeM.ret_bind, evalCoeffListM_ret]
      split_ifs with hel
      · simp only [TimeM.ret_pure]
        have hl_root : pR.IsRoot (I₁.lower : ℝ) := (eval_trim_eq_zero_iff cs I₁.lower).mp hel
        have hl_lt : I₁.lower < I₁.upper := by
          refine lt_of_le_of_ne hiso₁.1 fun heq => hnotm ?_
          simpa only [heq] using hl_root
        refine ⟨le_rfl, hiso₁.1, le_rfl, hiso₂.1, heq_m ▸ hl_lt, fun r hr => ?_, fun _ h => h.1⟩
        obtain ⟨r₀, hr₀, huniq⟩ := hiso₁.2
        have h1 := huniq r hr
        have h2 := huniq (I₁.lower : ℝ) ⟨le_rfl, Rat.cast_le.mpr hiso₁.1, hl_root⟩
        rw [h1, ← h2]
      · simp only [TimeM.ret_bind, sturmVariationsListM_ret]
        have hnotl : ¬pR.IsRoot (I₁.lower : ℝ) := fun h =>
          hel ((eval_trim_eq_zero_iff cs I₁.lower).mpr h)
        obtain ⟨r₁, ⟨hr₁l, hr₁u, hr₁_root⟩, hr₁_uniq⟩ := hiso₁.2
        obtain ⟨r₂, ⟨hr₂l, hr₂u, hr₂_root⟩, hr₂_uniq⟩ := hiso₂.2
        have hr₁_gt : (I₁.lower : ℝ) < r₁ := lt_of_le_of_ne hr₁l fun h => hnotl (h ▸ hr₁_root)
        have hr₁_lt : r₁ < (I₁.upper : ℝ) := lt_of_le_of_ne hr₁u fun h => hnotm (h.symm ▸ hr₁_root)
        have hr₂_gt : (I₁.upper : ℝ) < r₂ := by
          have heqR : (I₁.upper : ℝ) = (I₂.lower : ℝ) := congrArg Rat.cast heq_m
          rw [heqR]
          exact lt_of_le_of_ne hr₂l fun h => hnotm (heqR.symm ▸ (h ▸ hr₂_root))
        have ham : I₁.lower < I₁.upper := Rat.cast_lt.mp (lt_trans hr₁_gt hr₁_lt)
        have hmb : I₁.upper < I₂.upper := Rat.cast_lt.mp (lt_of_lt_of_le hr₂_gt hr₂u)
        have hca : sturmVariationsList (sturmSeqList cs) I₁.lower -
            sturmVariationsList (sturmSeqList cs) I₁.upper = 1 := by
          rw [card_roots_Ioc_eq_sep hsep ham.le]
          have hset : pR.roots.toFinset.filter
              (fun r : ℝ => (I₁.lower : ℝ) < r ∧ r ≤ (I₁.upper : ℝ)) = {r₁} := by
            ext x
            simp only [Finset.mem_filter, Multiset.mem_toFinset, mem_roots hpR0,
              Finset.mem_singleton]
            exact ⟨fun ⟨hx, hxl, hxu⟩ => hr₁_uniq x ⟨hxl.le, hxu, hx⟩,
              fun h => h ▸ ⟨hr₁_root, hr₁_gt, hr₁u⟩⟩
          rw [hset, Finset.card_singleton]
        have hcb : sturmVariationsList (sturmSeqList cs) I₁.upper -
            sturmVariationsList (sturmSeqList cs) I₂.upper = 1 := by
          rw [card_roots_Ioc_eq_sep hsep hmb.le]
          have hset : pR.roots.toFinset.filter
              (fun r : ℝ => (I₁.upper : ℝ) < r ∧ r ≤ (I₂.upper : ℝ)) = {r₂} := by
            ext x
            simp only [Finset.mem_filter, Multiset.mem_toFinset, mem_roots hpR0,
              Finset.mem_singleton]
            constructor
            · rintro ⟨hx, hxl, hxu⟩
              have heqR : (I₁.upper : ℝ) = (I₂.lower : ℝ) := congrArg Rat.cast heq_m
              exact hr₂_uniq x ⟨(heqR ▸ hxl).le, hxu, hx⟩
            · rintro rfl
              exact ⟨hr₂_root, hr₂_gt, hr₂u⟩
          rw [hset, Finset.card_singleton]
        have hw0 : (I₂.upper - I₁.lower : ℝ) ≤ 2 * (cauchyBoundNat cs : ℝ) / (2 : ℝ) ^ 0 := by
          have h1 : (-(cauchyBoundNat cs : ℚ) : ℝ) ≤ (I₁.lower : ℝ) := Rat.cast_le.mpr hb₁
          have h2 : (I₂.upper : ℝ) ≤ ((cauchyBoundNat cs : ℚ) : ℝ) := Rat.cast_le.mpr hb₂
          simp only [Rat.cast_neg, Rat.cast_natCast, pow_zero, div_one] at h1 h2 ⊢
          linarith
        have hmid := separateMidLoopM_spec hsep (mignotteBisectionDepth cs) 0
          I₁.lower I₁.upper I₂.upper _ (Nat.zero_add _) ham hmb rfl hca hcb hnotm hw0
        rcases hmid with ⟨hm1, hm2, hm3, hm4, hmlt, hno1, hno2⟩
        refine ⟨hm1, hm2, heq_m ▸ hm3, hm4, hmlt, fun r ⟨hrl, hru, hrr⟩ => ?_,
          fun r ⟨hrl, hru, hrr⟩ => ?_⟩
        · by_contra hgt
          exact hno1 r (lt_of_not_ge hgt) hru hrr
        · by_contra hgt
          have hlt_r : r < _ := lt_of_not_ge hgt
          have heqR : (I₁.upper : ℝ) = (I₂.lower : ℝ) := congrArg Rat.cast heq_m
          have hm_lt_r : (I₁.upper : ℝ) < r :=
            lt_of_le_of_ne (heqR.symm ▸ hrl) fun h => hnotm (h ▸ hrr)
          exact hno2 r hm_lt_r hlt_r.le hrr

/-- Walk a chain of isolating intervals carrying an updated `curLower` endpoint and separating
every adjacent pair in `TimeM ℕ`. -/
@[expose] def separateChainM (t : List ℚ) (seq : List (List ℚ)) (depth : ℕ)
    (curLower : ℚ) : List RootInterval → TimeM ℕ (List RootInterval)
  | [] => do
    TimeM.tick 1
    pure []
  | [I] => do
    TimeM.tick 1
    pure [{ lower := curLower, upper := I.upper }]
  | I₁ :: I₂ :: rest => do
    let p ← separatePairM t seq depth I₁ I₂
    let tail ← separateChainM t seq depth p.2 (I₂ :: rest)
    TimeM.tick 1
    pure ({ lower := curLower, upper := p.1 } :: tail)

/-- Separate all touching adjacent boundaries in a list of isolating intervals in `TimeM ℕ`. -/
@[expose] def separateTouchingM (t : List ℚ) (seq : List (List ℚ)) (depth : ℕ) :
    List RootInterval → TimeM ℕ (List RootInterval)
  | [] => do
    TimeM.tick 1
    pure []
  | I₀ :: rest => do
    TimeM.tick 1
    separateChainM t seq depth I₀.lower (I₀ :: rest)

private theorem separateChainM_length (t : List ℚ) (seq : List (List ℚ)) (depth : ℕ) :
    ∀ (L : List RootInterval) (curLower : ℚ),
      ((separateChainM t seq depth curLower L).ret).length = L.length
  | [], _ => by simp only [separateChainM, TimeM.ret_bind, TimeM.ret_pure, List.length_nil]
  | [_], _ => by simp only [separateChainM, TimeM.ret_bind, TimeM.ret_pure, List.length_singleton]
  | I₁ :: I₂ :: rest, curLower => by
    simp only [separateChainM, TimeM.ret_bind, TimeM.ret_pure, List.length_cons]
    rw [separateChainM_length t seq depth (I₂ :: rest)]
    simp only [List.length_cons]

theorem separateTouchingM_length (t : List ℚ) (seq : List (List ℚ)) (depth : ℕ)
    (L : List RootInterval) :
    ((separateTouchingM t seq depth L).ret).length = L.length := by
  cases L with
  | nil => simp only [separateTouchingM, TimeM.ret_bind, TimeM.ret_pure, List.length_nil]
  | cons I₀ rest =>
    simp only [separateTouchingM, TimeM.ret_bind, separateChainM_length]

private theorem separateChainM_time_le (t : List ℚ) (seq : List (List ℚ)) (depth : ℕ) :
    ∀ (L : List RootInterval) (curLower : ℚ),
      let vCost := 2 * (seq.map List.length).sum + 6 * seq.length + 7
      let eCost := 2 * t.length + 1
      let pCost := eCost + vCost + depth * (2 * vCost + 6) + 4
      (separateChainM t seq depth curLower L).time ≤ L.length * pCost + 1
  | [], _ => by
    dsimp only
    simp only [separateChainM, TimeM.time_bind, TimeM.time_tick, TimeM.time_pure, List.length_nil,
      zero_mul]
  | [_], _ => by
    dsimp only
    simp only [separateChainM, TimeM.time_bind, TimeM.time_tick, TimeM.time_pure,
      List.length_singleton, one_mul]
    omega
  | I₁ :: I₂ :: rest, curLower => by
    dsimp only
    simp only [separateChainM, TimeM.time_bind, TimeM.time_tick, TimeM.time_pure, List.length_cons]
    have hp := separatePairM_time_le t seq depth I₁ I₂
    have ih := separateChainM_time_le t seq depth (I₂ :: rest)
      (separatePairM t seq depth I₁ I₂).ret.2
    dsimp only at hp ih
    simp only [List.length_cons] at ih
    have hsplit : (rest.length + 1 + 1) *
        ((2 * t.length + 1) + (2 * (seq.map List.length).sum + 6 * seq.length + 7) +
          depth * (2 * (2 * (seq.map List.length).sum + 6 * seq.length + 7) + 6) + 4) =
        (rest.length + 1) *
          ((2 * t.length + 1) + (2 * (seq.map List.length).sum + 6 * seq.length + 7) +
            depth * (2 * (2 * (seq.map List.length).sum + 6 * seq.length + 7) + 6) + 4) +
          ((2 * t.length + 1) + (2 * (seq.map List.length).sum + 6 * seq.length + 7) +
            depth * (2 * (2 * (seq.map List.length).sum + 6 * seq.length + 7) + 6) + 4) :=
      Nat.succ_mul (rest.length + 1) _
    rw [hsplit]
    omega

theorem separateTouchingM_time_le (t : List ℚ) (seq : List (List ℚ)) (depth : ℕ)
    (L : List RootInterval) :
    let vCost := 2 * (seq.map List.length).sum + 6 * seq.length + 7
    let eCost := 2 * t.length + 1
    let pCost := eCost + vCost + depth * (2 * vCost + 6) + 4
    (separateTouchingM t seq depth L).time ≤ L.length * pCost + 2 := by
  dsimp only
  cases L with
  | nil =>
    simp only [separateTouchingM, TimeM.time_bind, TimeM.time_tick, TimeM.time_pure,
      List.length_nil, zero_mul]
    omega
  | cons I₀ rest =>
    simp only [separateTouchingM, TimeM.time_bind, TimeM.time_tick]
    have h := separateChainM_time_le t seq depth (I₀ :: rest) I₀.lower
    dsimp only at h
    omega

private theorem separateChainM_dyadicBounded (t : List ℚ) (seq : List (List ℚ))
    (depth B e : ℕ) :
    ∀ (L : List RootInterval) (curLower : ℚ),
      DyadicBounded B (e + depth) curLower →
      (∀ I ∈ L, DyadicBounded B e I.lower ∧ DyadicBounded B e I.upper) →
      ∀ J ∈ (separateChainM t seq depth curLower L).ret,
        DyadicBounded B (e + depth) J.lower ∧ DyadicBounded B (e + depth) J.upper
  | [], _, _, _ => by
    simp only [separateChainM, TimeM.ret_bind, TimeM.ret_pure]
    intro _ h; cases h
  | [I], curLower, hcur, hL => by
    simp only [separateChainM, TimeM.ret_bind, TimeM.ret_pure, List.mem_singleton]
    rintro J rfl
    exact ⟨hcur, (hL I List.mem_cons_self).2.mono (by omega)⟩
  | I₁ :: I₂ :: rest, curLower, hcur, hL => by
    simp only [separateChainM, TimeM.ret_bind, TimeM.ret_pure, List.mem_cons]
    have h1 := hL I₁ List.mem_cons_self
    have h2 := hL I₂ (List.mem_cons_of_mem I₁ List.mem_cons_self)
    have hp := separatePairM_dyadicBounded t seq depth B e I₁ I₂ h1.1 h1.2 h2.1 h2.2
    rintro J (rfl | hmem)
    · exact ⟨hcur, hp.1⟩
    · exact separateChainM_dyadicBounded t seq depth B e (I₂ :: rest) _ hp.2
        (fun I hI => hL I (List.mem_cons_of_mem I₁ hI)) J hmem

private theorem separateChainM_spec {cs : List ℚ} (hsep : (ofCoeffList cs).Separable) :
    ∀ (rest : List RootInterval) (I₀ : RootInterval) (curLower : ℚ),
      let pR := (ofCoeffList cs).map (algebraMap ℚ ℝ)
      let b : ℚ := (cauchyBoundNat cs : ℚ)
      (∀ I ∈ I₀ :: rest, I.IsIsolatingFor pR ∧ -b ≤ I.lower ∧ I.upper ≤ b) →
      (I₀ :: rest).Pairwise (IntervalGapOk pR) →
      I₀.lower ≤ curLower →
      (∀ r : ℝ, (I₀.lower : ℝ) ≤ r ∧ r ≤ (I₀.upper : ℝ) ∧ pR.IsRoot r → (curLower : ℝ) ≤ r) →
      let out := (separateChainM (trim cs) (sturmSeqList cs) (mignotteBisectionDepth cs)
        curLower (I₀ :: rest)).ret
      (∃ J₀ Js, out = J₀ :: Js ∧ J₀.lower = curLower) ∧
      out.Pairwise (fun A B => A.upper < B.lower) ∧
      ∀ (k : ℕ) (hk : k < (I₀ :: rest).length),
        let I := (I₀ :: rest)[k]
        let J := out[k]'(by
          rw [separateChainM_length]
          exact hk)
        J.IsIsolatingFor pR ∧ I.lower ≤ J.lower ∧ J.upper ≤ I.upper ∧
          ∀ r : ℝ, ((J.lower : ℝ) ≤ r ∧ r ≤ (J.upper : ℝ) ∧ pR.IsRoot r) ↔
            ((I.lower : ℝ) ≤ r ∧ r ≤ (I.upper : ℝ) ∧ pR.IsRoot r)
  | [], I₀, curLower, hiso_all, _, hcur_le, hcur_root => by
    let pR := (ofCoeffList cs).map (algebraMap ℚ ℝ)
    have h0 := (hiso_all I₀ List.mem_cons_self).1
    obtain ⟨r₀, ⟨hr₀l, hr₀u, hr₀r⟩, hr₀_uniq⟩ := h0.2
    have hcur_r₀ : (curLower : ℝ) ≤ r₀ := hcur_root r₀ ⟨hr₀l, hr₀u, hr₀r⟩
    have hcur_up : curLower ≤ I₀.upper := Rat.cast_le.mp (hcur_r₀.trans hr₀u)
    have hequiv : ∀ r : ℝ, ((curLower : ℝ) ≤ r ∧ r ≤ (I₀.upper : ℝ) ∧ pR.IsRoot r) ↔
        ((I₀.lower : ℝ) ≤ r ∧ r ≤ (I₀.upper : ℝ) ∧ pR.IsRoot r) := by
      intro r
      exact ⟨fun ⟨hcl, hru, hrr⟩ => ⟨(Rat.cast_le.mpr hcur_le).trans hcl, hru, hrr⟩,
        fun h => ⟨hcur_root r h, h.2.1, h.2.2⟩⟩
    have hisoJ : ({ lower := curLower, upper := I₀.upper } : RootInterval).IsIsolatingFor pR :=
      ⟨hcur_up, r₀, ⟨hcur_r₀, hr₀u, hr₀r⟩, fun r hr => hr₀_uniq r ((hequiv r).mp hr)⟩
    simp only [separateChainM, TimeM.ret_bind, TimeM.ret_pure]
    refine ⟨⟨_, [], rfl, rfl⟩, List.pairwise_singleton _ _, fun k hk => ?_⟩
    simp only [List.length_singleton] at hk
    have hk0 : k = 0 := by omega
    subst hk0
    simp only [List.getElem_cons_zero]
    exact ⟨hisoJ, hcur_le, le_rfl, hequiv⟩
  | I₁ :: rest', I₀, curLower, hiso_all, hpw, hcur_le, hcur_root => by
    let pR := (ofCoeffList cs).map (algebraMap ℚ ℝ)
    have hI₀ := hiso_all I₀ List.mem_cons_self
    have hI₁ := hiso_all I₁ (List.mem_cons_of_mem I₀ List.mem_cons_self)
    have hpw_cons := List.pairwise_cons.mp hpw
    have hgap01 : IntervalGapOk pR I₀ I₁ := hpw_cons.1 I₁ List.mem_cons_self
    have hp := separatePairM_spec hsep hI₀.1 hI₁.1 hI₀.2.1 hI₁.2.2 hgap01
    rcases hp with ⟨hp1, hp2, hp3, hp4, hplt, hproot1, hproot2⟩
    have ih := separateChainM_spec hsep rest' I₁
      (separatePairM (trim cs) (sturmSeqList cs) (mignotteBisectionDepth cs) I₀ I₁).ret.2
      (fun I hI => hiso_all I (List.mem_cons_of_mem I₀ hI))
      hpw_cons.2 hp3 hproot2
    rcases ih with ⟨⟨J₁, Js, htail_eq, hJ₁_low⟩, htail_pw, htail_idx⟩
    obtain ⟨r₀, ⟨hr₀l, hr₀u, hr₀r⟩, hr₀_uniq⟩ := hI₀.1.2
    have hcur_r₀ : (curLower : ℝ) ≤ r₀ := hcur_root r₀ ⟨hr₀l, hr₀u, hr₀r⟩
    have hr₀_u' : r₀ ≤ ((separatePairM (trim cs) (sturmSeqList cs)
        (mignotteBisectionDepth cs) I₀ I₁).ret.1 : ℝ) := hproot1 r₀ ⟨hr₀l, hr₀u, hr₀r⟩
    have hJ₀_le : curLower ≤ (separatePairM (trim cs) (sturmSeqList cs)
        (mignotteBisectionDepth cs) I₀ I₁).ret.1 := Rat.cast_le.mp (hcur_r₀.trans hr₀_u')
    have hequiv₀ : ∀ r : ℝ,
        ((curLower : ℝ) ≤ r ∧
          r ≤ ((separatePairM (trim cs) (sturmSeqList cs)
            (mignotteBisectionDepth cs) I₀ I₁).ret.1 : ℝ) ∧ pR.IsRoot r) ↔
        ((I₀.lower : ℝ) ≤ r ∧ r ≤ (I₀.upper : ℝ) ∧ pR.IsRoot r) := by
      intro r
      exact ⟨fun ⟨hcl, hru, hrr⟩ =>
          ⟨(Rat.cast_le.mpr hcur_le).trans hcl, hru.trans (Rat.cast_le.mpr hp2), hrr⟩,
        fun h => ⟨hcur_root r h, hproot1 r h, h.2.2⟩⟩
    have hisoJ₀ : ({ lower := curLower,
        upper := (separatePairM (trim cs) (sturmSeqList cs)
          (mignotteBisectionDepth cs) I₀ I₁).ret.1 } : RootInterval).IsIsolatingFor pR :=
      ⟨hJ₀_le, r₀, ⟨hcur_r₀, hr₀_u', hr₀r⟩, fun r hr => hr₀_uniq r ((hequiv₀ r).mp hr)⟩
    have hJ₁_iso : J₁.lower ≤ J₁.upper := by
      have h0 := (htail_idx 0 (by simp only [List.length_cons]; omega)).1.1
      simpa only [htail_eq, List.getElem_cons_zero] using h0
    simp only [separateChainM, TimeM.ret_bind, TimeM.ret_pure]
    refine ⟨⟨_, _, rfl, rfl⟩, ?_, fun k hk => ?_⟩
    · rw [List.pairwise_cons]
      refine ⟨fun B hB => ?_, htail_pw⟩
      rw [htail_eq] at hB htail_pw
      rcases List.mem_cons.mp hB with rfl | hBs
      · dsimp only
        rwa [hJ₁_low]
      · have h1B : J₁.upper < B.lower := (List.pairwise_cons.mp htail_pw).1 B hBs
        dsimp only
        have hlt1 : (separatePairM (trim cs) (sturmSeqList cs)
            (mignotteBisectionDepth cs) I₀ I₁).ret.1 < J₁.lower := by rwa [hJ₁_low]
        exact lt_trans (lt_of_lt_of_le hlt1 hJ₁_iso) h1B
    · cases k with
      | zero =>
        simp only [List.getElem_cons_zero]
        exact ⟨hisoJ₀, hcur_le, hp2, hequiv₀⟩
      | succ k' =>
        simp only [List.length_cons] at hk
        have hk' : k' < (I₁ :: rest').length := by omega
        simpa only [List.getElem_cons_succ] using htail_idx k' hk'

/-! ### End-to-end `TimeM ℕ`-charged computable isolator -/

/-- End-to-end `TimeM ℕ`-charged computable Sturm-bisection real-root isolator on `List ℚ`,
charging all preprocessing, bisection, left-root refinement, and boundary-disjointness steps. -/
@[expose] def isolateRootsTotalM (cs : List ℚ) : TimeM ℕ (List RootInterval) := do
  let t ← trimM cs
  let emp ← isEmptyM t
  if emp then
    pure []
  else do
    let seq ← sturmSeqListM cs
    let bNat ← cauchyBoundNatM cs
    TimeM.tick 2
    let b : ℚ := (bNat : ℚ)
    let depth ← mignotteBisectionDepthM cs
    let vLeft ← sturmVariationsListM seq (-b)
    let vRight ← sturmVariationsListM seq b
    let raw ← isolateIocTotalM t seq depth depth (-b) b vLeft vRight
    separateTouchingM t seq depth raw

/-- Pure list of strictly disjoint isolating rational intervals returned by `isolateRootsTotalM`. -/
@[expose] def isolateRootsTotal (cs : List ℚ) : List RootInterval :=
  (isolateRootsTotalM cs).ret

@[simp]
theorem isolateRootsTotalM_ret (cs : List ℚ) :
    (isolateRootsTotalM cs).ret = isolateRootsTotal cs := rfl

private theorem isolateRootsTotal_eq_separateTouching (cs : List ℚ) :
    isolateRootsTotal cs =
      (separateTouchingM (trim cs) (sturmSeqList cs) (mignotteBisectionDepth cs)
        (isolateRoots cs)).ret := by
  simp only [isolateRootsTotal, isolateRootsTotalM, isolateRoots, isolateRootsM,
    TimeM.ret_bind, trimM_ret, isEmptyM_ret]
  by_cases he : (trim cs).isEmpty = true
  · simp only [he, ↓reduceIte, TimeM.ret_pure, separateTouchingM, TimeM.ret_bind]
  · simp only [he, Bool.false_eq_true, ↓reduceIte, TimeM.ret_bind, sturmSeqListM_ret,
      cauchyBoundNatM_ret, mignotteBisectionDepthM_ret, sturmVariationsListM_ret,
      sturmVariationsM_ret, isolateIocTotalM_ret]

/-- `isolateRootsTotal cs` has the exact same length as `isolateRoots cs`. -/
theorem isolateRootsTotal_length_eq (cs : List ℚ) :
    (isolateRootsTotal cs).length = (isolateRoots cs).length := by
  rw [isolateRootsTotal_eq_separateTouching, separateTouchingM_length]

/-- Unconditional dyadic numerator and denominator bounds on every endpoint in
`isolateRootsTotal cs`. -/
theorem isolateRootsTotal_endpoint_bounds (cs : List ℚ) :
    ∀ J ∈ isolateRootsTotal cs,
      let b := cauchyBoundNat cs
      let e := 3 * mignotteBisectionDepth cs
      DyadicBounded b e J.lower ∧ DyadicBounded b e J.upper ∧
        J.lower.den ≤ 2 ^ e ∧ J.upper.den ≤ 2 ^ e ∧
        Int.natAbs J.lower.num ≤ b * 2 ^ e ∧ Int.natAbs J.upper.num ≤ b * 2 ^ e := by
  rw [isolateRootsTotal_eq_separateTouching]
  have hraw := isolateRoots_dyadicBounded cs
  let b := cauchyBoundNat cs
  let k := mignotteBisectionDepth cs
  cases hL : isolateRoots cs with
  | nil =>
    simp only [separateTouchingM, TimeM.ret_bind, TimeM.ret_pure]
    intro _ h; cases h
  | cons I₀ rest =>
    simp only [separateTouchingM, TimeM.ret_bind]
    intro J hJ
    have hI₀ := hraw I₀ (hL ▸ List.mem_cons_self)
    have hd := separateChainM_dyadicBounded (trim cs) (sturmSeqList cs) k b (2 * k)
      (I₀ :: rest) I₀.lower (hI₀.1.mono (by omega))
      (fun I hI => hraw I (hL ▸ hI)) J hJ
    have heq : 2 * k + k = 3 * k := by omega
    have hlow : DyadicBounded b (3 * k) J.lower := by simpa only [heq] using hd.1
    have hup : DyadicBounded b (3 * k) J.upper := by simpa only [heq] using hd.2
    exact ⟨hlow, hup, hlow.den_le, hup.den_le, hlow.natAbs_num_le, hup.natAbs_num_le⟩

private theorem isolateRootsTotal_index_spec {cs : List ℚ} (hsep : (ofCoeffList cs).Separable)
    (idx : ℕ) (hidx : idx < (isolateRoots cs).length) :
    let pR := (ofCoeffList cs).map (algebraMap ℚ ℝ)
    let I := (isolateRoots cs)[idx]
    let J := (isolateRootsTotal cs)[idx]'(by rw [isolateRootsTotal_length_eq]; exact hidx)
    J.IsIsolatingFor pR ∧ I.lower ≤ J.lower ∧ J.upper ≤ I.upper ∧
      ∀ r : ℝ, ((J.lower : ℝ) ≤ r ∧ r ≤ (J.upper : ℝ) ∧ pR.IsRoot r) ↔
        ((I.lower : ℝ) ≤ r ∧ r ≤ (I.upper : ℝ) ∧ pR.IsRoot r) := by
  have hiso := isolateRoots_isIsolatingFor hsep
  have hcau := isolateRoots_mem_cauchy hsep
  have hpw := isolateRoots_intervalGapOk hsep
  cases hL : isolateRoots cs with
  | nil =>
    simp only [hL, List.length_nil] at hidx
    omega
  | cons I₀ rest =>
    have hchain := separateChainM_spec hsep rest I₀ I₀.lower
      (fun I hI => ⟨hiso I (hL ▸ hI), hcau I (hL ▸ hI)⟩)
      (hL ▸ hpw) le_rfl (fun _ h => h.1)
    have hidx' : idx < (I₀ :: rest).length := hL ▸ hidx
    have h := hchain.2.2 idx hidx'
    have hget : (isolateRootsTotal cs)[idx]'(by rw [isolateRootsTotal_length_eq]; exact hidx) =
        ((separateChainM (trim cs) (sturmSeqList cs) (mignotteBisectionDepth cs)
          I₀.lower (I₀ :: rest)).ret)[idx]'(by rw [separateChainM_length]; exact hidx') := by
      simp only [isolateRootsTotal_eq_separateTouching, hL, separateTouchingM, TimeM.ret_bind]
    have hgetI : (isolateRoots cs)[idx] = (I₀ :: rest)[idx] := by simp only [hL]
    simpa only [hget, hgetI] using h

/-- Soundness: every interval in `isolateRootsTotal cs` isolates a unique real root of
`(ofCoeffList cs).map (algebraMap ℚ ℝ)`. -/
theorem isolateRootsTotal_isIsolatingFor {cs : List ℚ} (hsep : (ofCoeffList cs).Separable) :
    ∀ J ∈ isolateRootsTotal cs, J.IsIsolatingFor ((ofCoeffList cs).map (algebraMap ℚ ℝ)) := by
  intro J hJ
  obtain ⟨idx, hidx, rfl⟩ := List.mem_iff_getElem.mp hJ
  have hidx' : idx < (isolateRoots cs).length := by rwa [← isolateRootsTotal_length_eq]
  exact (isolateRootsTotal_index_spec hsep idx hidx').1

/-- Soundness in `Polynomial.aeval` form: every interval `J ∈ isolateRootsTotal cs` satisfies
`J.lower ≤ J.upper` and contains a unique `x : ℝ` with `Polynomial.aeval x (ofCoeffList cs) = 0`. -/
theorem isolateRootsTotal_aeval_unique {cs : List ℚ} (hsep : (ofCoeffList cs).Separable) :
    ∀ J ∈ isolateRootsTotal cs, J.lower ≤ J.upper ∧
      ∃! x : ℝ, x ∈ Set.Icc (J.lower : ℝ) (J.upper : ℝ) ∧
        Polynomial.aeval x (ofCoeffList cs) = 0 := by
  intro J hJ
  obtain ⟨hle, r₀, ⟨hl, hu, hr₀⟩, huniq⟩ := isolateRootsTotal_isIsolatingFor hsep J hJ
  have haeval : ∀ x : ℝ, ((ofCoeffList cs).map (algebraMap ℚ ℝ)).IsRoot x ↔
      Polynomial.aeval x (ofCoeffList cs) = 0 := by
    intro x
    rw [IsRoot.def, Polynomial.eval_map_algebraMap]
  refine ⟨hle, r₀, ⟨⟨hl, hu⟩, (haeval r₀).mp hr₀⟩, fun x ⟨⟨hxl, hxu⟩, hx0⟩ => ?_⟩
  exact huniq x ⟨hxl, hxu, (haeval x).mpr hx0⟩

/-- Strict separation: every pair of intervals in `isolateRootsTotal cs` satisfies
`J₁.upper < J₂.lower`. -/
theorem isolateRootsTotal_pairwise_lt {cs : List ℚ} (hsep : (ofCoeffList cs).Separable) :
    (isolateRootsTotal cs).Pairwise (fun J₁ J₂ => J₁.upper < J₂.lower) := by
  rw [isolateRootsTotal_eq_separateTouching]
  have hiso := isolateRoots_isIsolatingFor hsep
  have hcau := isolateRoots_mem_cauchy hsep
  have hpw := isolateRoots_intervalGapOk hsep
  cases hL : isolateRoots cs with
  | nil =>
    simp only [separateTouchingM, TimeM.ret_bind, TimeM.ret_pure]
    exact List.Pairwise.nil
  | cons I₀ rest =>
    simp only [separateTouchingM, TimeM.ret_bind]
    exact (separateChainM_spec hsep rest I₀ I₀.lower
      (fun I hI => ⟨hiso I (hL ▸ hI), hcau I (hL ▸ hI)⟩)
      (hL ▸ hpw) le_rfl (fun _ h => h.1)).2.1

/-- Closed-interval disjointness: the closed intervals `Set.Icc (J.lower : ℝ) (J.upper : ℝ)` of
`isolateRootsTotal cs` are pairwise disjoint. -/
theorem isolateRootsTotal_pairwise_disjoint {cs : List ℚ} (hsep : (ofCoeffList cs).Separable) :
    (isolateRootsTotal cs).Pairwise
      (Function.onFun Disjoint fun J => Set.Icc (J.lower : ℝ) (J.upper : ℝ)) := by
  refine (isolateRootsTotal_pairwise_lt hsep).imp fun {J₁ J₂} hlt => ?_
  rw [Function.onFun, Set.disjoint_left]
  intro x hx₁ hx₂
  have hltR : (J₁.upper : ℝ) < (J₂.lower : ℝ) := Rat.cast_lt.mpr hlt
  linarith [hx₁.2, hx₂.1]

/-- The unique real root `x : ℝ` with `Polynomial.aeval x (ofCoeffList cs) = 0` inside the `i`-th
interval of `isolateRootsTotal cs`. -/
noncomputable def totalIsolatedRoot {cs : List ℚ} (hsep : (ofCoeffList cs).Separable)
    (i : Fin (isolateRootsTotal cs).length) :
    {x : ℝ // Polynomial.aeval x (ofCoeffList cs) = 0} :=
  let i₀ : Fin (isolateRoots cs).length := ⟨i.1, (isolateRootsTotal_length_eq cs) ▸ i.2⟩
  let r := isolatedRoot hsep i₀
  ⟨r.1, by
    have h := r.2
    rwa [IsRoot.def, Polynomial.eval_map_algebraMap] at h⟩

/-- `totalIsolatedRoot hsep i` lies in the `i`-th closed interval of `isolateRootsTotal cs`. -/
theorem totalIsolatedRoot_mem {cs : List ℚ} (hsep : (ofCoeffList cs).Separable)
    (i : Fin (isolateRootsTotal cs).length) :
    let J := (isolateRootsTotal cs)[i]
    (totalIsolatedRoot hsep i).1 ∈ Set.Icc (J.lower : ℝ) (J.upper : ℝ) := by
  have hi₀ : i.1 < (isolateRoots cs).length := (isolateRootsTotal_length_eq cs) ▸ i.2
  have hmem₀ := isolatedRoot_mem hsep ⟨i.1, hi₀⟩
  have hspec := isolateRootsTotal_index_spec hsep i.1 hi₀
  have hr₀ := (isolatedRoot hsep ⟨i.1, hi₀⟩).2
  have hJ := (hspec.2.2.2 (isolatedRoot hsep ⟨i.1, hi₀⟩).1).mpr ⟨hmem₀.1, hmem₀.2, hr₀⟩
  exact ⟨hJ.1, hJ.2.1⟩

/-- The real roots indexed by `totalIsolatedRoot hsep` are strictly increasing. -/
theorem totalIsolatedRoot_strictMono {cs : List ℚ} (hsep : (ofCoeffList cs).Separable) :
    StrictMono (fun i : Fin (isolateRootsTotal cs).length => (totalIsolatedRoot hsep i).1) := by
  intro i j hij
  exact isolatedRoot_strictMono hsep hij

/-- Bijection between `Fin (isolateRootsTotal cs).length` and
`{x : ℝ // Polynomial.aeval x (ofCoeffList cs) = 0}` for separable `ofCoeffList cs`. -/
theorem isolateRootsTotal_bijective {cs : List ℚ} (hsep : (ofCoeffList cs).Separable) :
    Function.Bijective (totalIsolatedRoot hsep) := by
  have hbij := isolateRoots_bijective hsep
  refine ⟨fun i j hij => ?_, fun ⟨x, hx⟩ => ?_⟩
  · have hval : (isolatedRoot hsep ⟨i.1, (isolateRootsTotal_length_eq cs) ▸ i.2⟩).1 =
        (isolatedRoot hsep ⟨j.1, (isolateRootsTotal_length_eq cs) ▸ j.2⟩).1 :=
      congrArg Subtype.val hij
    have heq := hbij.1 (Subtype.ext hval)
    exact Fin.ext (congrArg Fin.val heq)
  · have hx' : ((ofCoeffList cs).map (algebraMap ℚ ℝ)).IsRoot x := by
      rwa [IsRoot.def, Polynomial.eval_map_algebraMap]
    obtain ⟨i₀, hi₀⟩ := hbij.2 ⟨x, hx'⟩
    refine ⟨⟨i₀.1, (isolateRootsTotal_length_eq cs).symm ▸ i₀.2⟩, Subtype.ext ?_⟩
    exact congrArg Subtype.val hi₀

/-- Squarefree bijection form for `isolateRootsTotal cs`. -/
theorem isolateRootsTotal_bijective_of_squarefree {cs : List ℚ}
    (hsq : Squarefree (ofCoeffList cs)) :
    Function.Bijective (totalIsolatedRoot (PerfectField.separable_iff_squarefree.mpr hsq)) :=
  isolateRootsTotal_bijective (PerfectField.separable_iff_squarefree.mpr hsq)

/-- Explicit end-to-end `TimeM ℕ` operation-count bound on `isolateRootsTotalM cs` in terms of
`cs.length`, `natDegree`, and `mignotteBisectionDepth cs`. -/
theorem isolateRootsTotalM_time_le {cs : List ℚ} (hsep : (ofCoeffList cs).Separable) :
    let n := cs.length
    let d := (ofCoeffList cs).natDegree
    let k := mignotteBisectionDepth cs
    let vCost := 2 * (d + 1) ^ 2 + 6 * (d + 1) + 7
    let eCost := 2 * (d + 1) + 1
    let prepCost := (n + 2) ^ 2 * (20 * n + 35) + 35 * n + k + 52
    let bisectCost := 2 * vCost + 2 + k * (d / 2) * (vCost + (d + 1) + 10) +
      d * (2 * eCost + 6 + k * (vCost + eCost + 4))
    let sepCost := d * (eCost + vCost + k * (2 * vCost + 6) + 4) + 2
    (isolateRootsTotalM cs).time ≤ prepCost + bisectCost + sepCost := by
  dsimp only
  let n := cs.length
  let d := (ofCoeffList cs).natDegree
  let k := mignotteBisectionDepth cs
  let seq := sturmSeqList cs
  have hp0 : ofCoeffList cs ≠ 0 := hsep.ne_zero
  have htnil : trim cs ≠ [] := fun hnil =>
    hp0 (by rw [← ofCoeffList_trim cs, hnil, ofCoeffList_nil])
  have hte : (trim cs).isEmpty = false := List.isEmpty_eq_false_iff.mpr htnil
  have ht_deg : (trim cs).length = d + 1 := by
    have h := (isTrimmed_trim cs).natDegree_add_one htnil
    rw [ofCoeffList_trim] at h
    exact h.symm
  have hseq_len : seq.length ≤ d + 1 := sturmSeqList_length_le cs
  have hseq_sum : (seq.map List.length).sum ≤ (d + 1) ^ 2 := by
    have hop := sturmSeqOpCost_le cs
    rw [sturmSeqOpCost] at hop
    omega
  let vC_actual := 2 * (seq.map List.length).sum + 6 * seq.length + 7
  let vC := 2 * (d + 1) ^ 2 + 6 * (d + 1) + 7
  let eC_actual := 2 * (trim cs).length + 1
  let eC := 2 * (d + 1) + 1
  have hvC_le : vC_actual ≤ vC := by dsimp only [vC_actual, vC]; omega
  have heC_eq : eC_actual = eC := by dsimp only [eC_actual, eC]; rw [ht_deg]
  let b : ℚ := (cauchyBoundNat cs : ℚ)
  have hb0 : (0 : ℚ) ≤ b := Nat.cast_nonneg _
  let vL := sturmVariationsList seq (-b)
  let vR := sturmVariationsList seq b
  have hc_le : vL - vR ≤ d := by
    have heq := card_roots_Ioc_eq_sep hsep (by linarith : -b ≤ b)
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
  have hraw_len : ((isolateIocM (trim cs) seq k k (-b) b vL vR).ret).length ≤ d :=
    (isolateIocM_length_le hsep (trim cs) k k (-b) b vL vR (by linarith) rfl rfl).trans hc_le
  have htr_t := trimM_time_le cs
  have hseq_t := sturmSeqListM_time_le cs
  have hcb_t := cauchyBoundNatM_time_le cs
  have hmb_t := mignotteBisectionDepthM_time_le cs
  have hvL_t := (sturmVariationsListM_time_le seq (-b)).trans hvC_le
  have hvR_t := (sturmVariationsListM_time_le seq b).trans hvC_le
  have hbis_raw := isolateIocTotalM_time_le hsep (trim cs) k k (-b) b vL vR (by linarith) rfl rfl
  dsimp only at hbis_raw
  have hsplit_le : (if vL - vR ≤ 1 then 0 else k * ((vL - vR) / 2)) ≤ k * (d / 2) := by
    split_ifs
    · exact Nat.zero_le _
    · exact Nat.mul_le_mul_left k (by omega)
  have hbis_le : (isolateIocTotalM (trim cs) seq k k (-b) b vL vR).time ≤
      2 + k * (d / 2) * (vC + (d + 1) + 10) + d * (2 * eC + 6 + k * (vC + eC + 4)) := by
    have h1 : (if vL - vR ≤ 1 then 0 else k * ((vL - vR) / 2)) * (vC_actual + seq.length + 10) ≤
        k * (d / 2) * (vC + (d + 1) + 10) :=
      Nat.mul_le_mul hsplit_le (by omega)
    have h2 : (vL - vR) * (2 * eC_actual + 6 + k * (vC_actual + eC_actual + 4)) ≤
        d * (2 * eC + 6 + k * (vC + eC + 4)) :=
      Nat.mul_le_mul hc_le (Nat.add_le_add (by omega) (Nat.mul_le_mul_left k (by omega)))
    dsimp only [vC_actual, eC_actual, seq, vL, vR, k, b] at h1 h2 hbis_raw
    omega
  have hsep_raw := separateTouchingM_time_le (trim cs) seq k
    ((isolateIocM (trim cs) seq k k (-b) b vL vR).ret)
  dsimp only at hsep_raw
  have hsep_le : (separateTouchingM (trim cs) seq k
      ((isolateIocM (trim cs) seq k k (-b) b vL vR).ret)).time ≤
      d * (eC + vC + k * (2 * vC + 6) + 4) + 2 := by
    have hp_le : eC_actual + vC_actual + k * (2 * vC_actual + 6) + 4 ≤
        eC + vC + k * (2 * vC + 6) + 4 :=
      Nat.add_le_add_right (Nat.add_le_add (by omega) (Nat.mul_le_mul_left k (by omega))) 4
    have hm := Nat.mul_le_mul hraw_len hp_le
    dsimp only [vC_actual, eC_actual] at hm hsep_raw
    omega
  simp only [isolateRootsTotalM, TimeM.time_bind, trimM_ret, isEmptyM_time, isEmptyM_ret,
    hte, Bool.false_eq_true, ↓reduceIte, sturmSeqListM_ret, cauchyBoundNatM_ret,
    TimeM.time_tick, mignotteBisectionDepthM_ret, sturmVariationsListM_ret, isolateIocTotalM_ret]
  dsimp only [seq, b, k, vL, vR, vC, eC, n, d] at *
  omega

/-- Squarefree form of `isolateRootsTotalM_time_le`. -/
theorem isolateRootsTotalM_time_le_of_squarefree {cs : List ℚ}
    (hsq : Squarefree (ofCoeffList cs)) :
    let n := cs.length
    let d := (ofCoeffList cs).natDegree
    let k := mignotteBisectionDepth cs
    let vCost := 2 * (d + 1) ^ 2 + 6 * (d + 1) + 7
    let eCost := 2 * (d + 1) + 1
    let prepCost := (n + 2) ^ 2 * (20 * n + 35) + 35 * n + k + 52
    let bisectCost := 2 * vCost + 2 + k * (d / 2) * (vCost + (d + 1) + 10) +
      d * (2 * eCost + 6 + k * (vCost + eCost + 4))
    let sepCost := d * (eCost + vCost + k * (2 * vCost + 6) + 4) + 2
    (isolateRootsTotalM cs).time ≤ prepCost + bisectCost + sepCost :=
  isolateRootsTotalM_time_le (PerfectField.separable_iff_squarefree.mpr hsq)

/-- Closed-form polynomial operation-count bound on `isolateRootsTotalM cs` purely in terms of
input list length `cs.length` and coefficient bit-length bound `B` (`O(n ^ 5 * (B + 2))`). -/
theorem isolateRootsTotalM_time_le_of_bitBound {B : ℕ} {cs : List ℚ}
    (hsq : Squarefree (ofCoeffList cs)) (hB : HasCoeffBitBound B cs) :
    (isolateRootsTotalM cs).time ≤ 64 * (cs.length + 2) ^ 5 * (B + 2) := by
  have hbase := isolateRootsTotalM_time_le_of_squarefree hsq
  dsimp only at hbase
  let n := cs.length
  let d := (ofCoeffList cs).natDegree
  let k := mignotteBisectionDepth cs
  have hd_le : d ≤ n := (natDegree_ofCoeffList_le cs).trans (Nat.sub_le _ _)
  have hk_le : k ≤ (n + 2) ^ 2 * (B + 2) := mignotteBisectionDepth_le_of_bitBound hB
  let N := n + 2
  have hd1 : d + 1 ≤ N := by dsimp only [N]; omega
  have hd_N : d ≤ N := by dsimp only [N]; omega
  have hd2_N : d / 2 ≤ N := by dsimp only [N]; omega
  have hN_ge2 : 2 ≤ N := by dsimp only [N]; omega
  have hB_ge2 : 2 ≤ B + 2 := by omega
  let vCost := 2 * (d + 1) ^ 2 + 6 * (d + 1) + 7
  let eCost := 2 * (d + 1) + 1
  have hv_le : vCost ≤ 7 * N ^ 2 := by
    have hsq1 : (d + 1) ^ 2 ≤ N ^ 2 := Nat.pow_le_pow_left hd1 2
    dsimp only [vCost]
    nlinarith
  have he_le : eCost ≤ 3 * N := by
    dsimp only [eCost]
    omega
  have hprep : (n + 2) ^ 2 * (20 * n + 35) + 35 * n + k + 52 ≤ 15 * N ^ 5 * (B + 2) := by
    have hn_N : n ≤ N := by dsimp only [N]; omega
    have hN2 : 4 ≤ N ^ 2 := by nlinarith
    have hN3 : N ^ 3 = N ^ 2 * N := by ring
    have hN5 : N ^ 5 = N ^ 2 * N ^ 2 * N := by ring
    change N ^ 2 * (20 * n + 35) + 35 * n + k + 52 ≤ 15 * N ^ 5 * (B + 2)
    have hk_N : k ≤ N ^ 2 * (B + 2) := hk_le
    nlinarith
  have hbis1 : 2 * vCost + 2 ≤ 5 * N ^ 5 * (B + 2) := by
    have hN3 : 8 ≤ N ^ 3 := by nlinarith
    have hN5 : N ^ 5 = N ^ 2 * N ^ 3 := by ring
    nlinarith
  have hbis2 : k * (d / 2) * (vCost + (d + 1) + 10) ≤ 12 * N ^ 5 * (B + 2) := by
    have hv' : vCost + (d + 1) + 10 ≤ 11 * N ^ 2 := by nlinarith
    have hkd : k * (d / 2) ≤ N ^ 2 * (B + 2) * N :=
      Nat.mul_le_mul hk_le hd2_N
    calc k * (d / 2) * (vCost + (d + 1) + 10)
        ≤ (N ^ 2 * (B + 2) * N) * (11 * N ^ 2) := Nat.mul_le_mul hkd hv'
      _ = 11 * N ^ 5 * (B + 2) := by ring
      _ ≤ 12 * N ^ 5 * (B + 2) := by nlinarith
  have hbis3 : d * (2 * eCost + 6 + k * (vCost + eCost + 4)) ≤ 12 * N ^ 5 * (B + 2) := by
    have hve : vCost + eCost + 4 ≤ 10 * N ^ 2 := by nlinarith
    have hkv : k * (vCost + eCost + 4) ≤ N ^ 2 * (B + 2) * (10 * N ^ 2) :=
      Nat.mul_le_mul hk_le hve
    have h2e : 2 * eCost + 6 ≤ 2 * N ^ 4 * (B + 2) := by
      have hN3 : 8 ≤ N ^ 3 := by nlinarith
      have hN4 : N ^ 4 = N * N ^ 3 := by ring
      nlinarith
    calc d * (2 * eCost + 6 + k * (vCost + eCost + 4))
        ≤ N * (2 * N ^ 4 * (B + 2) + N ^ 2 * (B + 2) * (10 * N ^ 2)) :=
            Nat.mul_le_mul hd_N (Nat.add_le_add h2e hkv)
      _ = 12 * N ^ 5 * (B + 2) := by ring
  have hsep_t : d * (eCost + vCost + k * (2 * vCost + 6) + 4) + 2 ≤ 20 * N ^ 5 * (B + 2) := by
    have h2v : 2 * vCost + 6 ≤ 16 * N ^ 2 := by nlinarith
    have hkv : k * (2 * vCost + 6) ≤ N ^ 2 * (B + 2) * (16 * N ^ 2) :=
      Nat.mul_le_mul hk_le h2v
    have h8 : 8 ≤ N ^ 2 * (B + 2) := by nlinarith
    have hev : eCost + vCost + 4 ≤ 2 * N ^ 4 * (B + 2) := by
      have h10 : eCost + vCost + 4 ≤ 10 * N ^ 2 := by nlinarith
      calc eCost + vCost + 4
          ≤ 10 * N ^ 2 := h10
        _ ≤ 2 * N ^ 2 * 8 := by omega
        _ ≤ 2 * N ^ 2 * (N ^ 2 * (B + 2)) := Nat.mul_le_mul_left _ h8
        _ = 2 * N ^ 4 * (B + 2) := by ring
    have hinner : eCost + vCost + k * (2 * vCost + 6) + 4 ≤ 18 * N ^ 4 * (B + 2) := by
      calc eCost + vCost + k * (2 * vCost + 6) + 4
          = (eCost + vCost + 4) + k * (2 * vCost + 6) := by ring
        _ ≤ 2 * N ^ 4 * (B + 2) + N ^ 2 * (B + 2) * (16 * N ^ 2) := Nat.add_le_add hev hkv
        _ = 18 * N ^ 4 * (B + 2) := by ring
    have hd_mul : d * (eCost + vCost + k * (2 * vCost + 6) + 4) ≤ 18 * N ^ 5 * (B + 2) := by
      calc d * (eCost + vCost + k * (2 * vCost + 6) + 4)
          ≤ N * (18 * N ^ 4 * (B + 2)) := Nat.mul_le_mul hd_N hinner
        _ = 18 * N ^ 5 * (B + 2) := by ring
    have h2_le : 2 ≤ 2 * N ^ 5 * (B + 2) := by
      have hN5_pos : 1 ≤ N ^ 5 := Nat.one_le_pow 5 N (by omega)
      nlinarith
    omega
  have htotal_sum :
      15 * N ^ 5 * (B + 2) + (5 * N ^ 5 * (B + 2) + 12 * N ^ 5 * (B + 2) + 12 * N ^ 5 * (B + 2)) +
        20 * N ^ 5 * (B + 2) = 64 * (cs.length + 2) ^ 5 * (B + 2) := by
    dsimp only [N, n]
    ring
  dsimp only [n, d, k, vCost, eCost] at hbase hprep hbis1 hbis2 hbis3 hsep_t
  omega

/-- Specialization of `isolateRootsTotalM_time_le_of_bitBound` to the computable bound
`coeffBitBound cs`. -/
theorem isolateRootsTotalM_time_le_coeffBitBound {cs : List ℚ}
    (hsq : Squarefree (ofCoeffList cs)) :
    (isolateRootsTotalM cs).time ≤ 64 * (cs.length + 2) ^ 5 * (coeffBitBound cs + 2) :=
  isolateRootsTotalM_time_le_of_bitBound hsq (hasCoeffBitBound_coeffBitBound cs)

/-- Explicit polynomial endpoint numerator and denominator bounds in `(cs.length, B)` under
`HasCoeffBitBound B cs`: every returned endpoint has denominator `≤ 2 ^ E` and numerator
`natAbs ≤ (cs.length + 1) * 2 ^ (2 * B + E)`, where `E = 3 * (cs.length + 2) ^ 2 * (B + 2)`. -/
theorem isolateRootsTotal_endpoint_bounds_of_bitBound {B : ℕ} {cs : List ℚ}
    (hB : HasCoeffBitBound B cs) :
    ∀ J ∈ isolateRootsTotal cs,
      let E := 3 * (cs.length + 2) ^ 2 * (B + 2)
      J.lower.den ≤ 2 ^ E ∧ J.upper.den ≤ 2 ^ E ∧
        Int.natAbs J.lower.num ≤ (cs.length + 1) * 2 ^ (2 * B + E) ∧
        Int.natAbs J.upper.num ≤ (cs.length + 1) * 2 ^ (2 * B + E) := by
  intro J hJ
  dsimp only
  let E := 3 * (cs.length + 2) ^ 2 * (B + 2)
  have hraw := isolateRootsTotal_endpoint_bounds cs J hJ
  dsimp only at hraw
  rcases hraw with ⟨_, _, hlden, huden, hlnum, hunum⟩
  have he_le : 3 * mignotteBisectionDepth cs ≤ E := by
    have hk := mignotteBisectionDepth_le_of_bitBound hB
    dsimp only [E]
    nlinarith
  have hpow_e : 2 ^ (3 * mignotteBisectionDepth cs) ≤ 2 ^ E :=
    Nat.pow_le_pow_right (by omega) he_le
  have hb_le : cauchyBoundNat cs ≤ (cs.length + 1) * 2 ^ (2 * B) :=
    cauchyBoundNat_le_of_bitBound hB
  have hmul_le : cauchyBoundNat cs * 2 ^ (3 * mignotteBisectionDepth cs) ≤
      (cs.length + 1) * 2 ^ (2 * B + E) := by
    calc cauchyBoundNat cs * 2 ^ (3 * mignotteBisectionDepth cs)
        ≤ ((cs.length + 1) * 2 ^ (2 * B)) * 2 ^ E := Nat.mul_le_mul hb_le hpow_e
      _ = (cs.length + 1) * (2 ^ (2 * B) * 2 ^ E) := by ring
      _ = (cs.length + 1) * 2 ^ (2 * B + E) := by rw [← Nat.pow_add]
  exact ⟨hlden.trans hpow_e, huden.trans hpow_e, hlnum.trans hmul_le, hunum.trans hmul_le⟩

/-- Combined specification of the computable `TimeM ℕ`-charged isolator `isolateRootsTotalM cs` for
any squarefree `p : ℚ[X]` represented by `cs : List ℚ` (`ofCoeffList cs = p`) with coefficient bit
bound `B`: isolating `aeval` soundness, strict separation `J₁.upper < J₂.lower`, pairwise disjoint
closed real intervals `Set.Icc`, strictly monotone bijection onto `{x : ℝ // Polynomial.aeval x p = 0}`,
polynomial dyadic endpoint numerator/denominator bounds, and `O(n ^ 5 * (B + 2))` total `TimeM ℕ`
operation count. -/
theorem isolateRootsTotal_spec_of_eq {B : ℕ} {cs : List ℚ} {p : ℚ[X]}
    (hp : ofCoeffList cs = p) (hsq : Squarefree p) (hB : HasCoeffBitBound B cs) :
    (∀ J ∈ isolateRootsTotal cs, J.lower ≤ J.upper ∧
      ∃! x : ℝ, x ∈ Set.Icc (J.lower : ℝ) (J.upper : ℝ) ∧ Polynomial.aeval x p = 0) ∧
    (isolateRootsTotal cs).Pairwise (fun J₁ J₂ => J₁.upper < J₂.lower) ∧
    (isolateRootsTotal cs).Pairwise
      (Function.onFun Disjoint fun J => Set.Icc (J.lower : ℝ) (J.upper : ℝ)) ∧
    (∃ f : Fin (isolateRootsTotal cs).length → {x : ℝ // Polynomial.aeval x p = 0},
      Function.Bijective f ∧
      StrictMono (fun i => (f i).1) ∧
      ∀ i,
        let J := (isolateRootsTotal cs)[i]
        (f i).1 ∈ Set.Icc (J.lower : ℝ) (J.upper : ℝ)) ∧
    (∀ J ∈ isolateRootsTotal cs,
      let E := 3 * (cs.length + 2) ^ 2 * (B + 2)
      J.lower.den ≤ 2 ^ E ∧ J.upper.den ≤ 2 ^ E ∧
        Int.natAbs J.lower.num ≤ (cs.length + 1) * 2 ^ (2 * B + E) ∧
        Int.natAbs J.upper.num ≤ (cs.length + 1) * 2 ^ (2 * B + E)) ∧
    (isolateRootsTotalM cs).time ≤ 64 * (cs.length + 2) ^ 5 * (B + 2) := by
  subst hp
  have hsep : (ofCoeffList cs).Separable := PerfectField.separable_iff_squarefree.mpr hsq
  exact ⟨isolateRootsTotal_aeval_unique hsep,
    isolateRootsTotal_pairwise_lt hsep,
    isolateRootsTotal_pairwise_disjoint hsep,
    ⟨totalIsolatedRoot hsep, isolateRootsTotal_bijective hsep,
      totalIsolatedRoot_strictMono hsep, totalIsolatedRoot_mem hsep⟩,
    isolateRootsTotal_endpoint_bounds_of_bitBound hB,
    isolateRootsTotalM_time_le_of_bitBound hsq hB⟩

/-! ### `Polynomial ℚ` wrappers -/

/-- End-to-end `TimeM ℕ`-charged real-root isolation for `p : ℚ[X]` via `Polynomial.coeffsBelow`. -/
noncomputable def isolatePolyRootsTotalM (p : ℚ[X]) : TimeM ℕ (List RootInterval) :=
  isolateRootsTotalM (p.coeffsBelow (p.natDegree + 1))

/-- Pure list of strictly disjoint isolating rational intervals for `p : ℚ[X]`. -/
noncomputable def isolatePolyRootsTotal (p : ℚ[X]) : List RootInterval :=
  (isolatePolyRootsTotalM p).ret

@[simp]
theorem isolatePolyRootsTotalM_ret (p : ℚ[X]) :
    (isolatePolyRootsTotalM p).ret = isolatePolyRootsTotal p := rfl

private theorem polyTotalSeparable {p : ℚ[X]} (hsq : Squarefree p) :
    (ofCoeffList (p.coeffsBelow (p.natDegree + 1))).Separable :=
  PerfectField.separable_iff_squarefree.mpr
    ((Polynomial.ofCoeffList_coeffsBelow (Nat.lt_succ_self p.natDegree)).symm ▸ hsq)

/-- Soundness for `isolatePolyRootsTotal p` on squarefree `p : ℚ[X]`. -/
theorem isolatePolyRootsTotal_isIsolatingFor {p : ℚ[X]} (hsq : Squarefree p) :
    ∀ J ∈ isolatePolyRootsTotal p, J.IsIsolatingFor (p.map (algebraMap ℚ ℝ)) := by
  have heq : ofCoeffList (p.coeffsBelow (p.natDegree + 1)) = p :=
    Polynomial.ofCoeffList_coeffsBelow (Nat.lt_succ_self p.natDegree)
  have hmap : p.map (algebraMap ℚ ℝ) =
      (ofCoeffList (p.coeffsBelow (p.natDegree + 1))).map (algebraMap ℚ ℝ) := by rw [heq]
  rw [isolatePolyRootsTotal, isolatePolyRootsTotalM, isolateRootsTotalM_ret, hmap]
  exact isolateRootsTotal_isIsolatingFor (polyTotalSeparable hsq)

/-- `Polynomial.aeval` soundness for `isolatePolyRootsTotal p` on squarefree `p : ℚ[X]`. -/
theorem isolatePolyRootsTotal_aeval_unique {p : ℚ[X]} (hsq : Squarefree p) :
    ∀ J ∈ isolatePolyRootsTotal p, J.lower ≤ J.upper ∧
      ∃! x : ℝ, x ∈ Set.Icc (J.lower : ℝ) (J.upper : ℝ) ∧ Polynomial.aeval x p = 0 := by
  have heq : ofCoeffList (p.coeffsBelow (p.natDegree + 1)) = p :=
    Polynomial.ofCoeffList_coeffsBelow (Nat.lt_succ_self p.natDegree)
  intro J hJ
  have h := isolateRootsTotal_aeval_unique (polyTotalSeparable hsq) J hJ
  simpa only [heq] using h

/-- Strict separation `J₁.upper < J₂.lower` for `isolatePolyRootsTotal p`. -/
theorem isolatePolyRootsTotal_pairwise_lt {p : ℚ[X]} (hsq : Squarefree p) :
    (isolatePolyRootsTotal p).Pairwise (fun J₁ J₂ => J₁.upper < J₂.lower) :=
  isolateRootsTotal_pairwise_lt (polyTotalSeparable hsq)

/-- Pairwise disjointness of closed intervals `Set.Icc (J.lower : ℝ) (J.upper : ℝ)` for
`isolatePolyRootsTotal p`. -/
theorem isolatePolyRootsTotal_pairwise_disjoint {p : ℚ[X]} (hsq : Squarefree p) :
    (isolatePolyRootsTotal p).Pairwise
      (Function.onFun Disjoint fun J => Set.Icc (J.lower : ℝ) (J.upper : ℝ)) :=
  isolateRootsTotal_pairwise_disjoint (polyTotalSeparable hsq)

/-- The unique real root `x : ℝ` with `Polynomial.aeval x p = 0` inside the `i`-th interval of
`isolatePolyRootsTotal p`. -/
noncomputable def polyTotalIsolatedRoot {p : ℚ[X]} (hsq : Squarefree p)
    (i : Fin (isolatePolyRootsTotal p).length) :
    {x : ℝ // Polynomial.aeval x p = 0} :=
  let r := totalIsolatedRoot (polyTotalSeparable hsq) i
  ⟨r.1, by
    have heq : ofCoeffList (p.coeffsBelow (p.natDegree + 1)) = p :=
      Polynomial.ofCoeffList_coeffsBelow (Nat.lt_succ_self p.natDegree)
    simpa only [heq] using r.2⟩

/-- Membership of `polyTotalIsolatedRoot hsq i` in the `i`-th closed interval of
`isolatePolyRootsTotal p`. -/
theorem polyTotalIsolatedRoot_mem {p : ℚ[X]} (hsq : Squarefree p)
    (i : Fin (isolatePolyRootsTotal p).length) :
    let J := (isolatePolyRootsTotal p)[i]
    (polyTotalIsolatedRoot hsq i).1 ∈ Set.Icc (J.lower : ℝ) (J.upper : ℝ) :=
  totalIsolatedRoot_mem (polyTotalSeparable hsq) i

/-- `polyTotalIsolatedRoot hsq` is strictly increasing across `Fin (isolatePolyRootsTotal p).length`. -/
theorem polyTotalIsolatedRoot_strictMono {p : ℚ[X]} (hsq : Squarefree p) :
    StrictMono (fun i : Fin (isolatePolyRootsTotal p).length => (polyTotalIsolatedRoot hsq i).1) :=
  totalIsolatedRoot_strictMono (polyTotalSeparable hsq)

/-- For every squarefree `p : ℚ[X]`, `polyTotalIsolatedRoot hsq` is a bijection onto
`{x : ℝ // Polynomial.aeval x p = 0}`. -/
theorem isolatePolyRootsTotal_bijective {p : ℚ[X]} (hsq : Squarefree p) :
    Function.Bijective (polyTotalIsolatedRoot hsq) := by
  have heq : ofCoeffList (p.coeffsBelow (p.natDegree + 1)) = p :=
    Polynomial.ofCoeffList_coeffsBelow (Nat.lt_succ_self p.natDegree)
  have hbij := isolateRootsTotal_bijective (polyTotalSeparable hsq)
  refine ⟨fun i j hij => ?_, fun ⟨x, hx⟩ => ?_⟩
  · have hval : (polyTotalIsolatedRoot hsq i).1 = (polyTotalIsolatedRoot hsq j).1 :=
      congrArg Subtype.val hij
    exact hbij.1 (Subtype.ext hval)
  · have hx' : Polynomial.aeval x (ofCoeffList (p.coeffsBelow (p.natDegree + 1))) = 0 := by
      simpa only [heq] using hx
    obtain ⟨i, hi⟩ := hbij.2 ⟨x, hx'⟩
    exact ⟨i, Subtype.ext (congrArg Subtype.val hi)⟩

/-- End-to-end `TimeM ℕ` operation-count bound for `isolatePolyRootsTotalM p` on squarefree
`p : ℚ[X]`. -/
theorem isolatePolyRootsTotalM_time_le {p : ℚ[X]} (hsq : Squarefree p) :
    let cs := p.coeffsBelow (p.natDegree + 1)
    let d := p.natDegree
    let k := mignotteBisectionDepth cs
    let vCost := 2 * (d + 1) ^ 2 + 6 * (d + 1) + 7
    let eCost := 2 * (d + 1) + 1
    let prepCost := (d + 3) ^ 2 * (20 * (d + 1) + 35) + 35 * (d + 1) + k + 52
    let bisectCost := 2 * vCost + 2 + k * (d / 2) * (vCost + (d + 1) + 10) +
      d * (2 * eCost + 6 + k * (vCost + eCost + 4))
    let sepCost := d * (eCost + vCost + k * (2 * vCost + 6) + 4) + 2
    (isolatePolyRootsTotalM p).time ≤ prepCost + bisectCost + sepCost := by
  dsimp only [isolatePolyRootsTotalM]
  have heq : ofCoeffList (p.coeffsBelow (p.natDegree + 1)) = p :=
    Polynomial.ofCoeffList_coeffsBelow (Nat.lt_succ_self p.natDegree)
  have hlen : (p.coeffsBelow (p.natDegree + 1)).length = p.natDegree + 1 :=
    Polynomial.length_coeffsBelow p (p.natDegree + 1)
  have hle := isolateRootsTotalM_time_le_of_squarefree
    (cs := p.coeffsBelow (p.natDegree + 1)) (heq.symm ▸ hsq)
  dsimp only at hle
  rw [heq, hlen] at hle
  have hd3 : p.natDegree + 1 + 2 = p.natDegree + 3 := by omega
  simpa only [hd3] using hle

/-- Closed-form polynomial `TimeM ℕ` cost bound on `isolatePolyRootsTotalM p` in terms of
`p.natDegree` and a bound `B` on the numerator/denominator bit-lengths of `p`'s coefficients. -/
theorem isolatePolyRootsTotalM_time_le_of_bitBound {B : ℕ} {p : ℚ[X]}
    (hsq : Squarefree p)
    (hB : ∀ i ≤ p.natDegree, Int.natAbs (p.coeff i).num ≤ 2 ^ B ∧ (p.coeff i).den ≤ 2 ^ B) :
    (isolatePolyRootsTotalM p).time ≤ 64 * (p.natDegree + 3) ^ 5 * (B + 2) := by
  dsimp only [isolatePolyRootsTotalM]
  have heq : ofCoeffList (p.coeffsBelow (p.natDegree + 1)) = p :=
    Polynomial.ofCoeffList_coeffsBelow (Nat.lt_succ_self p.natDegree)
  have hcsB : HasCoeffBitBound B (p.coeffsBelow (p.natDegree + 1)) := by
    intro c hc
    simp only [Polynomial.coeffsBelow, List.mem_map, List.mem_range] at hc
    obtain ⟨i, hi, rfl⟩ := hc
    exact hB i (by omega)
  have hle := isolateRootsTotalM_time_le_of_bitBound (heq.symm ▸ hsq) hcsB
  rw [Polynomial.length_coeffsBelow] at hle
  have hd3 : p.natDegree + 1 + 2 = p.natDegree + 3 := by omega
  simpa only [hd3] using hle

/-- Polynomial dyadic numerator/denominator bounds on all endpoints of `isolatePolyRootsTotal p`
given a bit-length bound `B` on `p`'s coefficients. -/
theorem isolatePolyRootsTotal_endpoint_bounds_of_bitBound {B : ℕ} {p : ℚ[X]}
    (hB : ∀ i ≤ p.natDegree, Int.natAbs (p.coeff i).num ≤ 2 ^ B ∧ (p.coeff i).den ≤ 2 ^ B) :
    ∀ J ∈ isolatePolyRootsTotal p,
      let E := 3 * (p.natDegree + 3) ^ 2 * (B + 2)
      J.lower.den ≤ 2 ^ E ∧ J.upper.den ≤ 2 ^ E ∧
        Int.natAbs J.lower.num ≤ (p.natDegree + 2) * 2 ^ (2 * B + E) ∧
        Int.natAbs J.upper.num ≤ (p.natDegree + 2) * 2 ^ (2 * B + E) := by
  have hcsB : HasCoeffBitBound B (p.coeffsBelow (p.natDegree + 1)) := by
    intro c hc
    simp only [Polynomial.coeffsBelow, List.mem_map, List.mem_range] at hc
    obtain ⟨i, hi, rfl⟩ := hc
    exact hB i (by omega)
  intro J hJ
  have h := isolateRootsTotal_endpoint_bounds_of_bitBound hcsB J hJ
  dsimp only at h ⊢
  rw [Polynomial.length_coeffsBelow] at h
  have hd3 : p.natDegree + 1 + 2 = p.natDegree + 3 := by omega
  have hd2 : p.natDegree + 1 + 1 = p.natDegree + 2 := by omega
  simpa only [hd3, hd2] using h

end Cslib.RealRoot
