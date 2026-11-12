/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Algebra.Polynomial.RealRoot.BitBounds

/-!
# End-to-End `TimeM`-Charged Rational Polynomial Preprocessing and Sturm Evaluation

This module instruments every list, polynomial-division, Sturm-sequence, sign-variation, Cauchy
bound, denominator-clearing, and Mignotte bisection-depth helper from `RatPoly.lean` in `TimeM ℕ`,
charging every recursive list traversal, scalar arithmetic step, comparison, Euclidean remainder
step, and base-4 ceiling-logarithm step (`clog4M`). Each instrumented operation returns the exact
same pure value as its `RatPoly.lean` counterpart and carries an explicit polynomial `TimeM ℕ`
operation-count upper bound.

**Cost model convention.** Primitive `ℚ` field operations (`+`, `-`, `*`, `/`, `abs`, comparisons,
`SignType.sign`) and primitive `ℤ`/`ℕ` operations (`+`, `-`, `*`, `/`, `Nat.lcm`) count as `O(1)`
arithmetic steps in `TimeM ℕ`; list traversals, polynomial divisions, power loops (`powNatM`), and
logarithm loops (`clog4M`) charge ticks proportional to their actual recursion length.

## Main definitions

* `Cslib.RealRoot.trimM`, `Cslib.RealRoot.derivListM`, `Cslib.RealRoot.divModListM`,
  `Cslib.RealRoot.negModListM`, `Cslib.RealRoot.sturmSeqListM`: `TimeM ℕ`-charged polynomial
  preprocessing and Sturm sequence generation.
* `Cslib.RealRoot.evalCoeffListM`, `Cslib.RealRoot.signVariationsM`,
  `Cslib.RealRoot.sturmVariationsListM`: `TimeM ℕ`-charged Horner evaluation and sign-variation
  counting.
* `Cslib.RealRoot.cauchyBoundNatM`, `Cslib.RealRoot.clearDenomsListM`,
  `Cslib.RealRoot.sqNormListM`, `Cslib.RealRoot.powNatM`, `Cslib.RealRoot.clog4M`,
  `Cslib.RealRoot.mignotteBisectionDepthM`: `TimeM ℕ`-charged root-bound and bisection-depth
  computation.

## Main results

* `*_ret` (`@[simp]`): every `TimeM ℕ` helper computes the identical pure value as its uncharged
  counterpart in `RatPoly.lean`.
* `sturmSeqListM_time_le`, `sturmVariationsListM_time_le`, `cauchyBoundNatM_time_le`,
  `mignotteBisectionDepthM_time_le`: explicit `TimeM ℕ` operation-count upper bounds.

## References

* [BasuPollackRoy2006] (locator unverified)
* [Mignotte1982], pp. 259–263 (locator unverified; `TimeM ℕ`-charged `List ℚ` preprocessing and
  operation-count bounds are specific to this module)
-/

public section

namespace Cslib.RealRoot

open Polynomial Cslib.Algorithms.Lean

/-! ### Basic `TimeM ℕ` list primitives -/

/-- `TimeM ℕ`-charged list length (`xs.length + 1` ticks). -/
@[expose] def lengthM {α : Type*} : List α → TimeM ℕ ℕ
  | [] => do
    TimeM.tick 1
    pure 0
  | _ :: xs => do
    TimeM.tick 1
    let n ← lengthM xs
    pure (n + 1)

@[simp]
theorem lengthM_ret {α : Type*} (xs : List α) : (lengthM xs).ret = xs.length := by
  induction xs with
  | nil => simp only [lengthM, TimeM.ret_bind, TimeM.ret_pure, List.length_nil]
  | cons _ xs ih => simp only [lengthM, TimeM.ret_bind, TimeM.ret_pure, ih, List.length_cons]

theorem lengthM_time {α : Type*} (xs : List α) : (lengthM xs).time = xs.length + 1 := by
  induction xs with
  | nil =>
    simp only [lengthM, TimeM.time_bind, TimeM.time_tick, TimeM.time_pure, List.length_nil]
    omega
  | cons _ xs ih =>
    simp only [lengthM, TimeM.time_bind, TimeM.time_tick, TimeM.time_pure, ih, List.length_cons]
    omega

/-- `TimeM ℕ`-charged emptiness test (`1` tick). -/
@[expose] def isEmptyM {α : Type*} (xs : List α) : TimeM ℕ Bool := do
  TimeM.tick 1
  pure xs.isEmpty

@[simp]
theorem isEmptyM_ret {α : Type*} (xs : List α) : (isEmptyM xs).ret = xs.isEmpty := by
  simp only [isEmptyM, TimeM.ret_bind, TimeM.ret_pure]

@[simp]
theorem isEmptyM_time {α : Type*} (xs : List α) : (isEmptyM xs).time = 1 := by
  simp only [isEmptyM, TimeM.time_bind, TimeM.time_tick, TimeM.time_pure, add_zero]

/-- `TimeM ℕ`-charged list append (`xs.length + 1` ticks). -/
@[expose] def appendM {α : Type*} : List α → List α → TimeM ℕ (List α)
  | [], ys => do
    TimeM.tick 1
    pure ys
  | x :: xs, ys => do
    TimeM.tick 1
    let zs ← appendM xs ys
    pure (x :: zs)

@[simp]
theorem appendM_ret {α : Type*} (xs ys : List α) : (appendM xs ys).ret = xs ++ ys := by
  induction xs with
  | nil => simp only [appendM, TimeM.ret_bind, TimeM.ret_pure, List.nil_append]
  | cons x xs ih => simp only [appendM, TimeM.ret_bind, TimeM.ret_pure, ih, List.cons_append]

theorem appendM_time {α : Type*} (xs ys : List α) : (appendM xs ys).time = xs.length + 1 := by
  induction xs with
  | nil =>
    simp only [appendM, TimeM.time_bind, TimeM.time_tick, TimeM.time_pure, List.length_nil]
    omega
  | cons _ xs ih =>
    simp only [appendM, TimeM.time_bind, TimeM.time_tick, TimeM.time_pure, ih, List.length_cons]
    omega

/-- `TimeM ℕ`-charged zero-padding list `List.replicate k 0` (`k + 1` ticks). -/
@[expose] def replicateZeroM : ℕ → TimeM ℕ (List ℚ)
  | 0 => do
    TimeM.tick 1
    pure []
  | k + 1 => do
    TimeM.tick 1
    let zs ← replicateZeroM k
    pure (0 :: zs)

@[simp]
theorem replicateZeroM_ret (k : ℕ) : (replicateZeroM k).ret = List.replicate k 0 := by
  induction k with
  | zero => simp only [replicateZeroM, TimeM.ret_bind, TimeM.ret_pure, List.replicate_zero]
  | succ k ih =>
    simp only [replicateZeroM, TimeM.ret_bind, TimeM.ret_pure, ih, List.replicate_succ]

theorem replicateZeroM_time (k : ℕ) : (replicateZeroM k).time = k + 1 := by
  induction k with
  | zero =>
    simp only [replicateZeroM, TimeM.time_bind, TimeM.time_tick, TimeM.time_pure]
    omega
  | succ k ih =>
    simp only [replicateZeroM, TimeM.time_bind, TimeM.time_tick, TimeM.time_pure, ih]
    omega

/-- `TimeM ℕ`-charged `List.getLast?` (`≤ xs.length + 1` ticks). -/
@[expose] def getLast?M {α : Type*} : List α → TimeM ℕ (Option α)
  | [] => do
    TimeM.tick 1
    pure none
  | [x] => do
    TimeM.tick 1
    pure (some x)
  | _ :: y :: ys => do
    TimeM.tick 1
    getLast?M (y :: ys)

@[simp]
theorem getLast?M_ret {α : Type*} : ∀ (xs : List α), (getLast?M xs).ret = xs.getLast?
  | [] => by simp only [getLast?M, TimeM.ret_bind, TimeM.ret_pure, List.getLast?_nil]
  | [x] => by simp only [getLast?M, TimeM.ret_bind, TimeM.ret_pure, List.getLast?_singleton]
  | _ :: y :: ys => by
    simp only [getLast?M, TimeM.ret_bind, List.getLast?_cons_cons]
    exact getLast?M_ret (y :: ys)

theorem getLast?M_time_le {α : Type*} : ∀ (xs : List α), (getLast?M xs).time ≤ xs.length + 1
  | [] => by
    simp only [getLast?M, TimeM.time_bind, TimeM.time_tick, TimeM.time_pure, List.length_nil]
    omega
  | [_] => by simp only [getLast?M, TimeM.time_bind, TimeM.time_tick, TimeM.time_pure,
    List.length_singleton]; omega
  | _ :: y :: ys => by
    simp only [getLast?M, TimeM.time_bind, TimeM.time_tick, List.length_cons]
    have ih := getLast?M_time_le (y :: ys)
    simp only [List.length_cons] at ih
    omega

/-- `TimeM ℕ`-charged `List.dropLast` (`≤ xs.length + 1` ticks). -/
@[expose] def dropLastM {α : Type*} : List α → TimeM ℕ (List α)
  | [] => do
    TimeM.tick 1
    pure []
  | [_] => do
    TimeM.tick 1
    pure []
  | x :: y :: ys => do
    TimeM.tick 1
    let zs ← dropLastM (y :: ys)
    pure (x :: zs)

@[simp]
theorem dropLastM_ret {α : Type*} : ∀ (xs : List α), (dropLastM xs).ret = xs.dropLast
  | [] => by simp only [dropLastM, TimeM.ret_bind, TimeM.ret_pure, List.dropLast_nil]
  | [_] => rfl
  | x :: y :: ys => by
    simp only [dropLastM, TimeM.ret_bind, TimeM.ret_pure, List.dropLast_cons_of_ne_nil
      (List.cons_ne_nil y ys)]
    rw [dropLastM_ret (y :: ys)]

theorem dropLastM_time_le {α : Type*} : ∀ (xs : List α), (dropLastM xs).time ≤ xs.length + 1
  | [] => by
    simp only [dropLastM, TimeM.time_bind, TimeM.time_tick, TimeM.time_pure, List.length_nil]
    omega
  | [_] => by simp only [dropLastM, TimeM.time_bind, TimeM.time_tick, TimeM.time_pure,
    List.length_singleton]; omega
  | _ :: y :: ys => by
    simp only [dropLastM, TimeM.time_bind, TimeM.time_tick, TimeM.time_pure, List.length_cons]
    have ih := dropLastM_time_le (y :: ys)
    simp only [List.length_cons] at ih
    omega

/-! ### `TimeM ℕ`-charged polynomial arithmetic and Sturm sequence -/

/-- `TimeM ℕ`-charged `trim`. -/
@[expose] def trimM : List ℚ → TimeM ℕ (List ℚ)
  | [] => do
    TimeM.tick 1
    pure []
  | a :: as => do
    TimeM.tick 1
    let t ← trimM as
    let emp ← isEmptyM t
    if emp then do
      TimeM.tick 1
      pure (if a = 0 then [] else [a])
    else
      pure (a :: t)

@[simp]
theorem trimM_ret (cs : List ℚ) : (trimM cs).ret = trim cs := by
  induction cs with
  | nil => simp only [trimM, trim, TimeM.ret_bind, TimeM.ret_pure]
  | cons a as ih =>
    simp only [trimM, trim, TimeM.ret_bind, isEmptyM_ret, ih]
    split_ifs <;> simp only [TimeM.ret_bind, TimeM.ret_pure]

theorem trimM_time_le (cs : List ℚ) : (trimM cs).time ≤ 3 * cs.length + 1 := by
  induction cs with
  | nil =>
    simp only [trimM, TimeM.time_bind, TimeM.time_tick, TimeM.time_pure, List.length_nil]
    omega
  | cons a as ih =>
    simp only [trimM, TimeM.time_bind, TimeM.time_tick, isEmptyM_time, isEmptyM_ret,
      List.length_cons]
    split_ifs <;> simp only [TimeM.time_bind, TimeM.time_tick, TimeM.time_pure] <;> omega

/-- `TimeM ℕ`-charged pointwise coefficient-list addition. -/
@[expose] def addListM : List ℚ → List ℚ → TimeM ℕ (List ℚ)
  | [], bs => do
    TimeM.tick 1
    pure bs
  | a :: as, [] => do
    TimeM.tick 1
    pure (a :: as)
  | a :: as, b :: bs => do
    TimeM.tick 1
    let cs ← addListM as bs
    pure ((a + b) :: cs)

@[simp]
theorem addListM_ret (as bs : List ℚ) : (addListM as bs).ret = addList as bs := by
  induction as generalizing bs with
  | nil => simp only [addListM, addList, TimeM.ret_bind, TimeM.ret_pure]
  | cons a as ih =>
    cases bs with
    | nil => simp only [addListM, addList, TimeM.ret_bind, TimeM.ret_pure]
    | cons b bs => simp only [addListM, addList, TimeM.ret_bind, TimeM.ret_pure, ih]

theorem addListM_time_le_right (as bs : List ℚ) : (addListM as bs).time ≤ bs.length + 1 := by
  induction as generalizing bs with
  | nil => simp only [addListM, TimeM.time_bind, TimeM.time_tick, TimeM.time_pure]; omega
  | cons a as ih =>
    cases bs with
    | nil =>
      simp only [addListM, TimeM.time_bind, TimeM.time_tick, TimeM.time_pure, List.length_nil]
      omega
    | cons b bs =>
      simp only [addListM, TimeM.time_bind, TimeM.time_tick, TimeM.time_pure, List.length_cons]
      have h := ih bs
      omega

private theorem addList_length (as bs : List ℚ) :
    (addList as bs).length = max as.length bs.length := by
  induction as generalizing bs with
  | nil => simp only [addList, List.length_nil, Nat.zero_max]
  | cons a as ih =>
    cases bs with
    | nil => simp only [addList, List.length_nil, Nat.max_zero]
    | cons b bs => simp only [addList, List.length_cons, ih, Nat.succ_max_succ]

/-- `TimeM ℕ`-charged coefficient-list negation. -/
@[expose] def negListM : List ℚ → TimeM ℕ (List ℚ)
  | [] => do
    TimeM.tick 1
    pure []
  | a :: as => do
    TimeM.tick 1
    let bs ← negListM as
    pure ((-a) :: bs)

@[simp]
theorem negListM_ret (as : List ℚ) : (negListM as).ret = negList as := by
  induction as with
  | nil => simp only [negListM, negList, List.map_nil, TimeM.ret_bind, TimeM.ret_pure]
  | cons a as ih =>
    simp only [negListM, negList, List.map_cons, TimeM.ret_bind, TimeM.ret_pure, ih]

theorem negListM_time (as : List ℚ) : (negListM as).time = as.length + 1 := by
  induction as with
  | nil =>
    simp only [negListM, TimeM.time_bind, TimeM.time_tick, TimeM.time_pure, List.length_nil]
    omega
  | cons _ as ih =>
    simp only [negListM, TimeM.time_bind, TimeM.time_tick, TimeM.time_pure, ih, List.length_cons]
    omega

/-- `TimeM ℕ`-charged coefficient-list subtraction. -/
@[expose] def subListM (as bs : List ℚ) : TimeM ℕ (List ℚ) := do
  let nb ← negListM bs
  addListM as nb

@[simp]
theorem subListM_ret (as bs : List ℚ) : (subListM as bs).ret = subList as bs := by
  simp only [subListM, subList, TimeM.ret_bind, negListM_ret, addListM_ret]

theorem subListM_time_le (as bs : List ℚ) : (subListM as bs).time ≤ 2 * bs.length + 2 := by
  simp only [subListM, TimeM.time_bind, negListM_time, negListM_ret]
  have h := addListM_time_le_right as (negList bs)
  have hlen : (negList bs).length = bs.length := List.length_map _
  omega

/-- `TimeM ℕ`-charged scalar multiplication of a coefficient list. -/
@[expose] def scaleListM (c : ℚ) : List ℚ → TimeM ℕ (List ℚ)
  | [] => do
    TimeM.tick 1
    pure []
  | b :: bs => do
    TimeM.tick 1
    let cs ← scaleListM c bs
    pure ((c * b) :: cs)

@[simp]
theorem scaleListM_ret (c : ℚ) (bs : List ℚ) : (scaleListM c bs).ret = scaleList c bs := by
  induction bs with
  | nil => simp only [scaleListM, scaleList, List.map_nil, TimeM.ret_bind, TimeM.ret_pure]
  | cons b bs ih =>
    simp only [scaleListM, scaleList, List.map_cons, TimeM.ret_bind, TimeM.ret_pure, ih]

theorem scaleListM_time (c : ℚ) (bs : List ℚ) : (scaleListM c bs).time = bs.length + 1 := by
  induction bs with
  | nil =>
    simp only [scaleListM, TimeM.time_bind, TimeM.time_tick, TimeM.time_pure, List.length_nil]
    omega
  | cons _ bs ih =>
    simp only [scaleListM, TimeM.time_bind, TimeM.time_tick, TimeM.time_pure, ih, List.length_cons]
    omega

/-- `TimeM ℕ`-charged `shiftZero`. -/
@[expose] def shiftZeroM (k : ℕ) (bs : List ℚ) : TimeM ℕ (List ℚ) := do
  let zs ← replicateZeroM k
  appendM zs bs

@[simp]
theorem shiftZeroM_ret (k : ℕ) (bs : List ℚ) : (shiftZeroM k bs).ret = shiftZero k bs := by
  simp only [shiftZeroM, shiftZero, TimeM.ret_bind, replicateZeroM_ret, appendM_ret]

theorem shiftZeroM_time (k : ℕ) (bs : List ℚ) : (shiftZeroM k bs).time = 2 * k + 2 := by
  simp only [shiftZeroM, TimeM.time_bind, replicateZeroM_time, replicateZeroM_ret, appendM_time,
    List.length_replicate]
  omega

/-- `TimeM ℕ`-charged `derivAux`. -/
@[expose] def derivAuxM (k : ℕ) : List ℚ → TimeM ℕ (List ℚ)
  | [] => do
    TimeM.tick 1
    pure []
  | a :: as => do
    TimeM.tick 2
    let ds ← derivAuxM (k + 1) as
    pure (((k : ℚ) * a) :: ds)

@[simp]
theorem derivAuxM_ret (k : ℕ) (as : List ℚ) : (derivAuxM k as).ret = derivAux k as := by
  induction as generalizing k with
  | nil => simp only [derivAuxM, derivAux, TimeM.ret_bind, TimeM.ret_pure]
  | cons a as ih => simp only [derivAuxM, derivAux, TimeM.ret_bind, TimeM.ret_pure, ih]

theorem derivAuxM_time (k : ℕ) (as : List ℚ) : (derivAuxM k as).time = 2 * as.length + 1 := by
  induction as generalizing k with
  | nil =>
    simp only [derivAuxM, TimeM.time_bind, TimeM.time_tick, TimeM.time_pure, List.length_nil]
    omega
  | cons _ as ih =>
    simp only [derivAuxM, TimeM.time_bind, TimeM.time_tick, TimeM.time_pure, ih (k + 1),
      List.length_cons]
    omega

/-- `TimeM ℕ`-charged formal derivative `derivList`. -/
@[expose] def derivListM : List ℚ → TimeM ℕ (List ℚ)
  | [] => do
    TimeM.tick 1
    pure []
  | _ :: as => do
    TimeM.tick 1
    let ds ← derivAuxM 1 as
    trimM ds

@[simp]
theorem derivListM_ret (cs : List ℚ) : (derivListM cs).ret = derivList cs := by
  cases cs with
  | nil => simp only [derivListM, derivList, TimeM.ret_bind, TimeM.ret_pure]
  | cons _ as => simp only [derivListM, derivList, TimeM.ret_bind, derivAuxM_ret, trimM_ret]

theorem derivListM_time_le (cs : List ℚ) : (derivListM cs).time ≤ 5 * cs.length + 3 := by
  cases cs with
  | nil => simp only [derivListM, TimeM.time_bind, TimeM.time_tick, TimeM.time_pure,
    List.length_nil]; omega
  | cons _ as =>
    simp only [derivListM, TimeM.time_bind, TimeM.time_tick, derivAuxM_time, derivAuxM_ret,
      List.length_cons]
    have htr := trimM_time_le (derivAux 1 as)
    rw [derivAux_length 1 as] at htr
    omega

/-- `TimeM ℕ`-charged fuel-bounded polynomial Euclidean division `divModAux`. -/
@[expose] def divModAuxM : ℕ → List ℚ → List ℚ → TimeM ℕ (List ℚ × List ℚ)
  | 0, u, _ => do
    let u' ← trimM u
    pure ([], u')
  | n + 1, u, v => do
    let u' ← trimM u
    let luLen ← lengthM u'
    let lvLen ← lengthM v
    TimeM.tick 1
    if luLen < lvLen then
      pure ([], u')
    else
      let vLast ← getLast?M v
      let uLast ← getLast?M u'
      match vLast, uLast with
      | some lc, some lu => do
        TimeM.tick 2
        let shift := luLen - lvLen
        let factor := lu / lc
        let shifted ← shiftZeroM shift v
        let subtrahend ← scaleListM factor shifted
        let diff ← subListM u' subtrahend
        let uNext ← trimM diff
        let res ← divModAuxM n uNext v
        let qTerm ← shiftZeroM shift [factor]
        let qNext ← addListM res.1 qTerm
        pure (qNext, res.2)
      | _, _ => do
        TimeM.tick 1
        pure ([], u')

@[simp]
theorem divModAuxM_ret : ∀ (n : ℕ) (u v : List ℚ), (divModAuxM n u v).ret = divModAux n u v
  | 0, u, v => by simp only [divModAuxM, divModAux, TimeM.ret_bind, trimM_ret, TimeM.ret_pure]
  | n + 1, u, v => by
    simp only [divModAuxM, divModAux, TimeM.ret_bind, trimM_ret, lengthM_ret]
    split_ifs with hlt
    · simp only [TimeM.ret_pure]
    · simp only [TimeM.ret_bind, getLast?M_ret]
      cases v.getLast? with
      | none => simp only [TimeM.ret_bind, TimeM.ret_pure]
      | some lc =>
        cases (trim u).getLast? with
        | none => simp only [TimeM.ret_bind, TimeM.ret_pure]
        | some lu =>
          simp only [TimeM.ret_bind, shiftZeroM_ret, scaleListM_ret, subListM_ret, trimM_ret,
            divModAuxM_ret n, addListM_ret, TimeM.ret_pure]

private theorem divModAux_snd_length_le :
    ∀ (n : ℕ) (u v : List ℚ), (divModAux n u v).2.length ≤ u.length
  | 0, u, _ => trim_length_le u
  | n + 1, u, v => by
    simp only [divModAux]
    split_ifs with hlt
    · exact trim_length_le u
    · cases v.getLast? with
      | none => exact trim_length_le u
      | some lc =>
        cases (trim u).getLast? with
        | none => exact trim_length_le u
        | some lu =>
          dsimp only
          have huv : v.length ≤ (trim u).length := Nat.le_of_not_lt hlt
          let sub := scaleList (lu / lc) (shiftZero ((trim u).length - v.length) v)
          have hsub_len : sub.length = (trim u).length := by
            simp only [sub, scaleList, List.length_map, shiftZero, List.length_append,
              List.length_replicate]
            omega
          have hdiff_len : (subList (trim u) sub).length = (trim u).length := by
            simp only [subList, addList_length, negList, List.length_map, hsub_len, max_self]
          exact (divModAux_snd_length_le n _ v).trans
            ((trim_length_le _).trans (hdiff_len.le.trans (trim_length_le u)))

theorem divModAuxM_time_le :
    ∀ (n : ℕ) (u v : List ℚ),
      (divModAuxM n u v).time ≤ (n + 1) * (20 * max u.length v.length + 20)
  | 0, u, v => by
    simp only [divModAuxM, TimeM.time_bind, TimeM.time_pure, zero_add, one_mul]
    have htr := trimM_time_le u
    have hle : u.length ≤ max u.length v.length := le_max_left _ _
    omega
  | n + 1, u, v => by
    let M := max u.length v.length
    have hu_le : u.length ≤ M := le_max_left _ _
    have hv_le : v.length ≤ M := le_max_right _ _
    have hu'_le : (trim u).length ≤ u.length := trim_length_le u
    have htr_u := trimM_time_le u
    simp only [divModAuxM, TimeM.time_bind, trimM_ret, lengthM_time, lengthM_ret, TimeM.time_tick]
    split_ifs with hlt
    · simp only [TimeM.time_pure]
      have hpos : 0 ≤ (n + 1) * (20 * M + 20) := Nat.zero_le _
      rw [Nat.add_right_comm n 1 1, Nat.succ_mul]
      omega
    · have huv : v.length ≤ (trim u).length := Nat.le_of_not_lt hlt
      simp only [TimeM.time_bind, getLast?M_ret]
      have hgl_v := getLast?M_time_le v
      have hgl_u := getLast?M_time_le (trim u)
      cases v.getLast? with
      | none =>
        simp only [TimeM.time_bind, TimeM.time_tick, TimeM.time_pure]
        rw [Nat.add_right_comm n 1 1, Nat.succ_mul]
        omega
      | some lc =>
        cases (trim u).getLast? with
        | none =>
          simp only [TimeM.time_bind, TimeM.time_tick, TimeM.time_pure]
          rw [Nat.add_right_comm n 1 1, Nat.succ_mul]
          omega
        | some lu =>
          simp only [TimeM.time_bind, TimeM.time_tick, shiftZeroM_time, shiftZeroM_ret,
            scaleListM_time, scaleListM_ret, subListM_ret, trimM_ret, divModAuxM_ret,
            TimeM.time_pure]
          let shift := (trim u).length - v.length
          let factor := lu / lc
          let shifted := shiftZero shift v
          let subtrahend := scaleList factor shifted
          let diff := subList (trim u) subtrahend
          let uNext := trim diff
          have hsh_len : shifted.length = (trim u).length := by
            simp only [shifted, shiftZero, List.length_append, List.length_replicate, shift]
            omega
          have hsub_len : subtrahend.length = (trim u).length := by
            simp only [subtrahend, scaleList, List.length_map, hsh_len]
          have hdiff_len : diff.length = (trim u).length := by
            simp only [diff, subList, addList_length, negList, List.length_map, hsub_len, max_self]
          have huNext_len : uNext.length ≤ u.length :=
            (trim_length_le diff).trans (hdiff_len.le.trans hu'_le)
          have hsub_t := subListM_time_le (trim u) subtrahend
          rw [hsub_len] at hsub_t
          have htr_next := trimM_time_le diff
          rw [hdiff_len] at htr_next
          have hmax_next : max uNext.length v.length ≤ M :=
            max_le (huNext_len.trans hu_le) hv_le
          have ih := (divModAuxM_time_le n uNext v).trans
            (Nat.mul_le_mul_left (n + 1) (by omega : 20 * max uNext.length v.length + 20 ≤
              20 * M + 20))
          have hqTerm_len : (shiftZero shift [factor]).length = shift + 1 := by
            simp only [shiftZero, List.length_append, List.length_replicate, List.length_singleton]
          have hadd_t := addListM_time_le_right (divModAux n uNext v).1 (shiftZero shift [factor])
          rw [hqTerm_len] at hadd_t
          have hshift_le : shift ≤ (trim u).length := Nat.sub_le _ _
          dsimp only [M] at ih
          rw [hsh_len]
          have hsplit : (n + 1 + 1) * (20 * max u.length v.length + 20) =
              (n + 1) * (20 * max u.length v.length + 20) +
                (20 * max u.length v.length + 20) := Nat.succ_mul (n + 1) _
          rw [hsplit]
          dsimp only [uNext, diff, subtrahend, shifted, shift, factor] at hsub_t htr_next ih hadd_t
          omega

/-- `TimeM ℕ`-charged Euclidean quotient and remainder `divModList`. -/
@[expose] def divModListM (u v : List ℚ) : TimeM ℕ (List ℚ × List ℚ) := do
  let u' ← trimM u
  let v' ← trimM v
  let lu ← lengthM u'
  divModAuxM lu u' v'

@[simp]
theorem divModListM_ret (u v : List ℚ) : (divModListM u v).ret = divModList u v := by
  simp only [divModListM, divModList, TimeM.ret_bind, trimM_ret, lengthM_ret, divModAuxM_ret]

theorem divModListM_time_le (u v : List ℚ) :
    (divModListM u v).time ≤ (u.length + 2) * (20 * max u.length v.length + 26) := by
  let M := max u.length v.length
  have hu_le : u.length ≤ M := le_max_left _ _
  have hv_le : v.length ≤ M := le_max_right _ _
  have hu'_le : (trim u).length ≤ u.length := trim_length_le u
  have hv'_le : (trim v).length ≤ v.length := trim_length_le v
  have hmax' : max (trim u).length (trim v).length ≤ M :=
    max_le (hu'_le.trans hu_le) (hv'_le.trans hv_le)
  simp only [divModListM, TimeM.time_bind, trimM_ret, lengthM_time, lengthM_ret]
  have htu := trimM_time_le u
  have htv := trimM_time_le v
  have haux := (divModAuxM_time_le (trim u).length (trim u) (trim v)).trans
    (Nat.mul_le_mul (Nat.add_le_add_right hu'_le 1)
      (by omega : 20 * max (trim u).length (trim v).length + 20 ≤ 20 * M + 20))
  calc (trimM u).time + ((trimM v).time + (((trim u).length + 1) +
        (divModAuxM (trim u).length (trim u) (trim v)).time))
      ≤ (3 * M + 1) + ((3 * M + 1) + ((M + 1) + (u.length + 1) * (20 * M + 20))) := by omega
    _ ≤ (20 * M + 26) + (u.length + 1) * (20 * M + 26) := by nlinarith
    _ = (u.length + 2) * (20 * M + 26) := by ring

/-- `TimeM ℕ`-charged negated Euclidean remainder `negModList`. -/
@[expose] def negModListM (u v : List ℚ) : TimeM ℕ (List ℚ) := do
  let nu ← negListM u
  let qr ← divModListM nu v
  TimeM.tick 1
  pure qr.2

@[simp]
theorem negModListM_ret (u v : List ℚ) : (negModListM u v).ret = negModList u v := by
  simp only [negModListM, negModList, TimeM.ret_bind, negListM_ret, divModListM_ret,
    TimeM.ret_pure]

theorem negModListM_time_le (u v : List ℚ) :
    (negModListM u v).time ≤ (u.length + 2) * (20 * max u.length v.length + 28) := by
  simp only [negModListM, TimeM.time_bind, negListM_time, negListM_ret, TimeM.time_tick,
    TimeM.time_pure]
  have hdiv := divModListM_time_le (negList u) v
  have hnl : (negList u).length = u.length := List.length_map _
  rw [hnl] at hdiv
  have hadd : (u.length + 2) * (20 * max u.length v.length + 28) =
      (u.length + 2) * (20 * max u.length v.length + 26) + 2 * (u.length + 2) := by ring
  omega

private theorem negModList_length_le (u v : List ℚ) : (negModList u v).length ≤ u.length := by
  simp only [negModList, divModList]
  have h := divModAux_snd_length_le (trim (negList u)).length (trim (negList u)) (trim v)
  refine h.trans ((trim_length_le _).trans ?_)
  simp only [negList, List.length_map, le_refl]

/-- `TimeM ℕ`-charged fuel-bounded Sturm sequence `sturmSeqAux`. -/
@[expose] def sturmSeqAuxM : ℕ → List ℚ → List ℚ → TimeM ℕ (List (List ℚ))
  | 0, p, _ => do
    TimeM.tick 1
    pure [p]
  | n + 1, p, q => do
    let emp ← isEmptyM q
    if emp then do
      TimeM.tick 1
      pure [p]
    else do
      let r ← negModListM p q
      let rest ← sturmSeqAuxM n q r
      TimeM.tick 1
      pure (p :: rest)

@[simp]
theorem sturmSeqAuxM_ret :
    ∀ (n : ℕ) (p q : List ℚ), (sturmSeqAuxM n p q).ret = sturmSeqAux n p q
  | 0, p, q => by simp only [sturmSeqAuxM, sturmSeqAux, TimeM.ret_bind, TimeM.ret_pure]
  | n + 1, p, q => by
    simp only [sturmSeqAuxM, sturmSeqAux, TimeM.ret_bind, isEmptyM_ret]
    split_ifs <;> simp only [TimeM.ret_bind, negModListM_ret, sturmSeqAuxM_ret n, TimeM.ret_pure]

theorem sturmSeqAuxM_time_le :
    ∀ (n : ℕ) (p q : List ℚ),
      (sturmSeqAuxM n p q).time ≤
        (n + 1) * ((max p.length q.length + 2) * (20 * max p.length q.length + 30))
  | 0, p, q => by
    simp only [sturmSeqAuxM, TimeM.time_bind, TimeM.time_tick, TimeM.time_pure, zero_add, one_mul]
    calc 1 + 0 ≤ 2 * 30 := by decide
      _ ≤ (max p.length q.length + 2) * (20 * max p.length q.length + 30) :=
            Nat.mul_le_mul (Nat.le_add_left 2 _) (Nat.le_add_left 30 _)
  | n + 1, p, q => by
    let M := max p.length q.length
    have hp_le : p.length ≤ M := le_max_left _ _
    have hq_le : q.length ≤ M := le_max_right _ _
    simp only [sturmSeqAuxM, TimeM.time_bind, isEmptyM_time, isEmptyM_ret]
    split_ifs with hemp
    · simp only [TimeM.time_bind, TimeM.time_tick, TimeM.time_pure]
      have hpos : 0 ≤ (n + 1) * ((max p.length q.length + 2) *
        (20 * max p.length q.length + 30)) := Nat.zero_le _
      have h2 : 2 ≤ (max p.length q.length + 2) * (20 * max p.length q.length + 30) :=
        (by decide : 2 ≤ 2 * 30).trans
          (Nat.mul_le_mul (Nat.le_add_left 2 _) (Nat.le_add_left 30 _))
      have hsplit : (n + 1 + 1) * ((max p.length q.length + 2) *
          (20 * max p.length q.length + 30)) =
          (n + 1) * ((max p.length q.length + 2) * (20 * max p.length q.length + 30)) +
            (max p.length q.length + 2) * (20 * max p.length q.length + 30) :=
        Nat.succ_mul (n + 1) _
      rw [hsplit]
      omega
    · simp only [TimeM.time_bind, negModListM_ret, TimeM.time_tick, TimeM.time_pure]
      have hneg := negModListM_time_le p q
      have hr_le : (negModList p q).length ≤ M := (negModList_length_le p q).trans hp_le
      have hmax_qr : max q.length (negModList p q).length ≤ M := max_le hq_le hr_le
      have hm1 : max q.length (negModList p q).length + 2 ≤ M + 2 := by omega
      have hm2 : 20 * max q.length (negModList p q).length + 30 ≤ 20 * M + 30 := by omega
      have ih := (sturmSeqAuxM_time_le n q (negModList p q)).trans
        (Nat.mul_le_mul_left (n + 1) (Nat.mul_le_mul hm1 hm2))
      have hstep : 1 + ((p.length + 2) * (20 * M + 28) + 1) ≤ (M + 2) * (20 * M + 30) := by
        have hmul : (p.length + 2) * (20 * M + 28) ≤ (M + 2) * (20 * M + 28) :=
          Nat.mul_le_mul_right _ (Nat.add_le_add_right hp_le 2)
        have hexp : (M + 2) * (20 * M + 30) = (M + 2) * (20 * M + 28) + 2 * (M + 2) := by ring
        omega
      dsimp only [M] at ih hstep
      have hsplit : (n + 1 + 1) * ((max p.length q.length + 2) *
          (20 * max p.length q.length + 30)) =
          (n + 1) * ((max p.length q.length + 2) * (20 * max p.length q.length + 30)) +
            (max p.length q.length + 2) * (20 * max p.length q.length + 30) :=
        Nat.succ_mul (n + 1) _
      rw [hsplit]
      omega

/-- `TimeM ℕ`-charged Sturm sequence `sturmSeqList`. -/
@[expose] def sturmSeqListM (cs : List ℚ) : TimeM ℕ (List (List ℚ)) := do
  let p ← trimM cs
  let emp ← isEmptyM p
  if emp then
    pure []
  else do
    let dp ← derivListM p
    let dpLen ← lengthM dp
    sturmSeqAuxM dpLen p dp

@[simp]
theorem sturmSeqListM_ret (cs : List ℚ) : (sturmSeqListM cs).ret = sturmSeqList cs := by
  simp only [sturmSeqListM, sturmSeqList, TimeM.ret_bind, trimM_ret, isEmptyM_ret]
  split_ifs <;> simp only [TimeM.ret_bind, TimeM.ret_pure, derivListM_ret, lengthM_ret,
    sturmSeqAuxM_ret]

/-- Cubic operation-count bound on `sturmSeqListM cs` in terms of `cs.length`. -/
theorem sturmSeqListM_time_le (cs : List ℚ) :
    (sturmSeqListM cs).time ≤ (cs.length + 2) ^ 2 * (20 * cs.length + 35) := by
  let n := cs.length
  have hp_le : (trim cs).length ≤ n := trim_length_le cs
  have htr := trimM_time_le cs
  simp only [sturmSeqListM, TimeM.time_bind, trimM_ret, isEmptyM_time, isEmptyM_ret]
  split_ifs with hemp
  · simp only [TimeM.time_pure]
    nlinarith
  · simp only [TimeM.time_bind, derivListM_ret, lengthM_time, lengthM_ret]
    have hdp_t := derivListM_time_le (trim cs)
    have hdp_len : (derivList (trim cs)).length ≤ n :=
      (derivList_length_le (trim cs)).trans ((Nat.sub_le _ _).trans hp_le)
    have hmax : max (trim cs).length (derivList (trim cs)).length ≤ n := max_le hp_le hdp_len
    have hm1 : max (trim cs).length (derivList (trim cs)).length + 2 ≤ n + 2 := by omega
    have hm2 : 20 * max (trim cs).length (derivList (trim cs)).length + 30 ≤ 20 * n + 30 := by omega
    have haux := (sturmSeqAuxM_time_le (derivList (trim cs)).length (trim cs)
      (derivList (trim cs))).trans
      (Nat.mul_le_mul (Nat.add_le_add_right hdp_len 1) (Nat.mul_le_mul hm1 hm2))
    nlinarith

/-! ### `TimeM ℕ`-charged Horner evaluation and sign variations -/

/-- `TimeM ℕ`-charged Horner evaluation `evalCoeffList z l` (`2 * l.length + 1` ticks). -/
@[expose] def evalCoeffListM (z : ℚ) : List ℚ → TimeM ℕ ℚ
  | [] => do
    TimeM.tick 1
    pure 0
  | a :: l => do
    let acc ← evalCoeffListM z l
    TimeM.tick 2
    pure (a + z * acc)

@[simp]
theorem evalCoeffListM_ret (z : ℚ) (l : List ℚ) :
    (evalCoeffListM z l).ret = evalCoeffList z l := by
  induction l with
  | nil => simp only [evalCoeffListM, evalCoeffList_nil, TimeM.ret_bind, TimeM.ret_pure]
  | cons a l ih =>
    simp only [evalCoeffListM, evalCoeffList_cons, TimeM.ret_bind, TimeM.ret_pure, ih]

theorem evalCoeffListM_time (z : ℚ) (l : List ℚ) :
    (evalCoeffListM z l).time = 2 * l.length + 1 := by
  induction l with
  | nil =>
    simp only [evalCoeffListM, TimeM.time_bind, TimeM.time_tick, TimeM.time_pure, List.length_nil]
    omega
  | cons _ l ih =>
    simp only [evalCoeffListM, TimeM.time_bind, TimeM.time_tick, TimeM.time_pure, ih,
      List.length_cons]
    omega

/-- `TimeM ℕ`-charged `List.map SignType.sign`. -/
@[expose] def mapSignM : List ℚ → TimeM ℕ (List SignType)
  | [] => do
    TimeM.tick 1
    pure []
  | q :: qs => do
    TimeM.tick 1
    let ss ← mapSignM qs
    pure (SignType.sign q :: ss)

private theorem mapSignM_ret (qs : List ℚ) : (mapSignM qs).ret = qs.map SignType.sign := by
  induction qs with
  | nil => simp only [mapSignM, List.map_nil, TimeM.ret_bind, TimeM.ret_pure]
  | cons q qs ih => simp only [mapSignM, List.map_cons, TimeM.ret_bind, TimeM.ret_pure, ih]

private theorem mapSignM_time (qs : List ℚ) : (mapSignM qs).time = qs.length + 1 := by
  induction qs with
  | nil =>
    simp only [mapSignM, TimeM.time_bind, TimeM.time_tick, TimeM.time_pure, List.length_nil]
    omega
  | cons _ qs ih =>
    simp only [mapSignM, TimeM.time_bind, TimeM.time_tick, TimeM.time_pure, ih, List.length_cons]
    omega

/-- `TimeM ℕ`-charged nonzero-sign filter. -/
@[expose] def filterNonzeroSignM : List SignType → TimeM ℕ (List SignType)
  | [] => do
    TimeM.tick 1
    pure []
  | s :: ss => do
    TimeM.tick 1
    let fs ← filterNonzeroSignM ss
    if decide (s ≠ 0) then pure (s :: fs) else pure fs

private theorem filterNonzeroSignM_ret (ss : List SignType) :
    (filterNonzeroSignM ss).ret = ss.filter (fun x => decide (x ≠ 0)) := by
  induction ss with
  | nil => simp only [filterNonzeroSignM, List.filter_nil, TimeM.ret_bind, TimeM.ret_pure]
  | cons s ss ih =>
    simp only [filterNonzeroSignM, List.filter_cons, TimeM.ret_bind, ih]
    split_ifs <;> simp only [TimeM.ret_pure]

private theorem filterNonzeroSignM_time (ss : List SignType) :
    (filterNonzeroSignM ss).time = ss.length + 1 := by
  induction ss with
  | nil =>
    simp only [filterNonzeroSignM, TimeM.time_bind, TimeM.time_tick, TimeM.time_pure,
      List.length_nil]
    omega
  | cons _ ss ih =>
    simp only [filterNonzeroSignM, TimeM.time_bind, TimeM.time_tick, ih, List.length_cons]
    split_ifs <;> simp only [TimeM.time_pure] <;> omega

/-- `TimeM ℕ`-charged `List.destutter' (· ≠ ·)`. -/
@[expose] def destutterNeAuxM (b : SignType) : List SignType → TimeM ℕ (List SignType)
  | [] => do
    TimeM.tick 1
    pure [b]
  | a :: l => do
    TimeM.tick 1
    if b ≠ a then do
      let ds ← destutterNeAuxM a l
      pure (b :: ds)
    else
      destutterNeAuxM b l

private theorem destutterNeAuxM_ret (b : SignType) (l : List SignType) :
    (destutterNeAuxM b l).ret = List.destutter' (· ≠ ·) b l := by
  induction l generalizing b with
  | nil => simp only [destutterNeAuxM, List.destutter'_nil, TimeM.ret_bind, TimeM.ret_pure]
  | cons a l ih =>
    simp only [destutterNeAuxM, TimeM.ret_bind]
    by_cases hne : b ≠ a
    · simp only [eq_true hne, ↓reduceIte, TimeM.ret_bind, TimeM.ret_pure, ih a,
        List.destutter'_cons_pos l hne]
    · simp only [eq_false hne, ↓reduceIte, ih b, List.destutter'_cons_neg l hne]

private theorem destutterNeAuxM_time (b : SignType) (l : List SignType) :
    (destutterNeAuxM b l).time = l.length + 1 := by
  induction l generalizing b with
  | nil =>
    simp only [destutterNeAuxM, TimeM.time_bind, TimeM.time_tick, TimeM.time_pure, List.length_nil]
    omega
  | cons a l ih =>
    simp only [destutterNeAuxM, TimeM.time_bind, TimeM.time_tick, List.length_cons]
    split_ifs <;> simp only [TimeM.time_bind, TimeM.time_pure, ih] <;> omega

/-- `TimeM ℕ`-charged `List.destutter (· ≠ ·)`. -/
@[expose] def destutterNeM : List SignType → TimeM ℕ (List SignType)
  | [] => do
    TimeM.tick 1
    pure []
  | a :: l => do
    TimeM.tick 1
    destutterNeAuxM a l

private theorem destutterNeM_ret (l : List SignType) :
    (destutterNeM l).ret = List.destutter (· ≠ ·) l := by
  cases l with
  | nil => simp only [destutterNeM, List.destutter_nil, TimeM.ret_bind, TimeM.ret_pure]
  | cons a l =>
    simp only [destutterNeM, List.destutter_cons', TimeM.ret_bind, destutterNeAuxM_ret]

private theorem destutterNeM_time_le (l : List SignType) :
    (destutterNeM l).time ≤ l.length + 2 := by
  cases l with
  | nil => simp only [destutterNeM, TimeM.time_bind, TimeM.time_tick, TimeM.time_pure,
    List.length_nil]; omega
  | cons a l =>
    simp only [destutterNeM, TimeM.time_bind, TimeM.time_tick, destutterNeAuxM_time,
      List.length_cons]
    omega

/-- `TimeM ℕ`-charged `List.signVariations` (`≤ 4 * xs.length + 6` ticks). -/
@[expose] def signVariationsM (xs : List ℚ) : TimeM ℕ ℕ := do
  let ss ← mapSignM xs
  let fs ← filterNonzeroSignM ss
  let ds ← destutterNeM fs
  let len ← lengthM ds
  TimeM.tick 1
  pure (len - 1)

@[simp]
theorem signVariationsM_ret (xs : List ℚ) : (signVariationsM xs).ret = xs.signVariations := by
  simp only [signVariationsM, List.signVariations, TimeM.ret_bind, mapSignM_ret,
    filterNonzeroSignM_ret, destutterNeM_ret, lengthM_ret, TimeM.ret_pure]

theorem signVariationsM_time_le (xs : List ℚ) :
    (signVariationsM xs).time ≤ 4 * xs.length + 6 := by
  simp only [signVariationsM, TimeM.time_bind, mapSignM_time, mapSignM_ret,
    filterNonzeroSignM_time, filterNonzeroSignM_ret, destutterNeM_ret, lengthM_time,
    TimeM.time_tick, TimeM.time_pure, List.length_map]
  let fs := (xs.map SignType.sign).filter (fun x => decide (x ≠ 0))
  have hfs_len : fs.length ≤ xs.length := by
    calc fs.length ≤ (xs.map SignType.sign).length := List.length_filter_le _ _
      _ = xs.length := List.length_map _
  have hds_t := destutterNeM_time_le fs
  have hds_len : (List.destutter (· ≠ ·) fs).length ≤ fs.length :=
    (List.destutter_sublist _ _).length_le
  dsimp only [fs] at hfs_len hds_t hds_len
  omega

/-- `TimeM ℕ`-charged map of `evalCoeffListM x` over a polynomial sequence. -/
@[expose] def mapEvalCoeffListM (x : ℚ) : List (List ℚ) → TimeM ℕ (List ℚ)
  | [] => do
    TimeM.tick 1
    pure []
  | f :: fs => do
    TimeM.tick 1
    let v ← evalCoeffListM x f
    let vs ← mapEvalCoeffListM x fs
    pure (v :: vs)

private theorem mapEvalCoeffListM_ret (x : ℚ) (seq : List (List ℚ)) :
    (mapEvalCoeffListM x seq).ret = seq.map (evalCoeffList x) := by
  induction seq with
  | nil => simp only [mapEvalCoeffListM, List.map_nil, TimeM.ret_bind, TimeM.ret_pure]
  | cons f fs ih =>
    simp only [mapEvalCoeffListM, List.map_cons, TimeM.ret_bind, TimeM.ret_pure,
      evalCoeffListM_ret, ih]

private theorem mapEvalCoeffListM_time (x : ℚ) (seq : List (List ℚ)) :
    (mapEvalCoeffListM x seq).time = 2 * (seq.map List.length).sum + 2 * seq.length + 1 := by
  induction seq with
  | nil =>
    simp only [mapEvalCoeffListM, TimeM.time_bind, TimeM.time_tick, TimeM.time_pure,
      List.map_nil, List.sum_nil, List.length_nil]
    omega
  | cons f fs ih =>
    simp only [mapEvalCoeffListM, TimeM.time_bind, TimeM.time_tick, evalCoeffListM_time,
      TimeM.time_pure, ih, List.map_cons, List.sum_cons, List.length_cons]
    omega

/-- Fully step-charged Sturm sign-variation count `sturmVariationsList seq x`. -/
@[expose] def sturmVariationsListM (seq : List (List ℚ)) (x : ℚ) : TimeM ℕ ℕ := do
  let vs ← mapEvalCoeffListM x seq
  signVariationsM vs

@[simp]
theorem sturmVariationsListM_ret (seq : List (List ℚ)) (x : ℚ) :
    (sturmVariationsListM seq x).ret = sturmVariationsList seq x := by
  simp only [sturmVariationsListM, sturmVariationsList, TimeM.ret_bind, mapEvalCoeffListM_ret,
    signVariationsM_ret]

theorem sturmVariationsListM_time_le (seq : List (List ℚ)) (x : ℚ) :
    (sturmVariationsListM seq x).time ≤ 2 * (seq.map List.length).sum + 6 * seq.length + 7 := by
  simp only [sturmVariationsListM, TimeM.time_bind, mapEvalCoeffListM_time, mapEvalCoeffListM_ret]
  have hsv := signVariationsM_time_le (seq.map (evalCoeffList x))
  simp only [List.length_map] at hsv
  omega

/-- Degree-bounded time cost of `sturmVariationsListM (sturmSeqList cs) x`. -/
theorem sturmVariationsListM_sturmSeq_time_le (cs : List ℚ) (x : ℚ) :
    let d := (ofCoeffList cs).natDegree
    (sturmVariationsListM (sturmSeqList cs) x).time ≤ 2 * (d + 1) ^ 2 + 6 * (d + 1) + 7 := by
  dsimp only
  let d := (ofCoeffList cs).natDegree
  have h1 := sturmVariationsListM_time_le (sturmSeqList cs) x
  have hop := sturmSeqOpCost_le cs
  rw [sturmSeqOpCost] at hop
  have hlen := sturmSeqList_length_le cs
  omega

/-! ### `TimeM ℕ`-charged Cauchy bound and Mignotte bisection depth -/

/-- `TimeM ℕ`-charged `maxAbsList`. -/
@[expose] def maxAbsListM : List ℚ → TimeM ℕ ℚ
  | [] => do
    TimeM.tick 1
    pure 0
  | a :: as => do
    TimeM.tick 2
    let m ← maxAbsListM as
    pure (max |a| m)

@[simp]
theorem maxAbsListM_ret (cs : List ℚ) : (maxAbsListM cs).ret = maxAbsList cs := by
  induction cs with
  | nil => simp only [maxAbsListM, maxAbsList, TimeM.ret_bind, TimeM.ret_pure]
  | cons a as ih => simp only [maxAbsListM, maxAbsList, TimeM.ret_bind, TimeM.ret_pure, ih]

theorem maxAbsListM_time (cs : List ℚ) : (maxAbsListM cs).time = 2 * cs.length + 1 := by
  induction cs with
  | nil =>
    simp only [maxAbsListM, TimeM.time_bind, TimeM.time_tick, TimeM.time_pure, List.length_nil]
    omega
  | cons _ as ih =>
    simp only [maxAbsListM, TimeM.time_bind, TimeM.time_tick, TimeM.time_pure, ih, List.length_cons]
    omega

/-- `TimeM ℕ`-charged `cauchyBoundNat`. -/
@[expose] def cauchyBoundNatM (cs : List ℚ) : TimeM ℕ ℕ := do
  let t ← trimM cs
  let tLen ← lengthM t
  TimeM.tick 1
  if tLen ≤ 1 then
    pure 1
  else do
    let lastOpt ← getLast?M t
    let dl ← dropLastM t
    let m ← maxAbsListM dl
    TimeM.tick 5
    let lc := Option.getD lastOpt 1
    let b := m / |lc| + 1
    pure (Int.natAbs b.num / b.den + 1)

@[simp]
theorem cauchyBoundNatM_ret (cs : List ℚ) : (cauchyBoundNatM cs).ret = cauchyBoundNat cs := by
  simp only [cauchyBoundNatM, cauchyBoundNat, TimeM.ret_bind, trimM_ret, lengthM_ret]
  split_ifs <;> simp only [TimeM.ret_bind, getLast?M_ret, dropLastM_ret, maxAbsListM_ret,
    TimeM.ret_pure]

theorem cauchyBoundNatM_time_le (cs : List ℚ) :
    (cauchyBoundNatM cs).time ≤ 8 * cs.length + 12 := by
  have ht_le : (trim cs).length ≤ cs.length := trim_length_le cs
  have htr := trimM_time_le cs
  simp only [cauchyBoundNatM, TimeM.time_bind, trimM_ret, lengthM_time, lengthM_ret,
    TimeM.time_tick]
  split_ifs with hlen
  · simp only [TimeM.time_pure]
    omega
  · simp only [TimeM.time_bind, dropLastM_ret, maxAbsListM_time, TimeM.time_tick, TimeM.time_pure,
      List.length_dropLast]
    have hgl := getLast?M_time_le (trim cs)
    have hdl := dropLastM_time_le (trim cs)
    omega

/-- `TimeM ℕ`-charged `lcmDens`. -/
@[expose] def lcmDensM : List ℚ → TimeM ℕ ℕ
  | [] => do
    TimeM.tick 1
    pure 1
  | q :: qs => do
    let d ← lcmDensM qs
    TimeM.tick 2
    pure (Nat.lcm q.den d)

@[simp]
theorem lcmDensM_ret (cs : List ℚ) : (lcmDensM cs).ret = lcmDens cs := by
  induction cs with
  | nil => simp only [lcmDensM, lcmDens, TimeM.ret_bind, TimeM.ret_pure]
  | cons q qs ih => simp only [lcmDensM, lcmDens, TimeM.ret_bind, TimeM.ret_pure, ih]

theorem lcmDensM_time (cs : List ℚ) : (lcmDensM cs).time = 2 * cs.length + 1 := by
  induction cs with
  | nil =>
    simp only [lcmDensM, TimeM.time_bind, TimeM.time_tick, TimeM.time_pure, List.length_nil]
    omega
  | cons _ qs ih =>
    simp only [lcmDensM, TimeM.time_bind, TimeM.time_tick, TimeM.time_pure, ih, List.length_cons]
    omega

/-- `TimeM ℕ`-charged denominator-clearing pass with multiplier `D`. -/
@[expose] def mapClearEntryM (D : ℕ) : List ℚ → TimeM ℕ (List ℤ)
  | [] => do
    TimeM.tick 1
    pure []
  | q :: qs => do
    TimeM.tick 2
    let ns ← mapClearEntryM D qs
    pure ((q.num * ((D / q.den : ℕ) : ℤ)) :: ns)

private theorem mapClearEntryM_ret (D : ℕ) (cs : List ℚ) :
    (mapClearEntryM D cs).ret = cs.map (fun q => q.num * ((D / q.den : ℕ) : ℤ)) := by
  induction cs with
  | nil => simp only [mapClearEntryM, List.map_nil, TimeM.ret_bind, TimeM.ret_pure]
  | cons q qs ih => simp only [mapClearEntryM, List.map_cons, TimeM.ret_bind, TimeM.ret_pure, ih]

private theorem mapClearEntryM_time (D : ℕ) (cs : List ℚ) :
    (mapClearEntryM D cs).time = 2 * cs.length + 1 := by
  induction cs with
  | nil =>
    simp only [mapClearEntryM, TimeM.time_bind, TimeM.time_tick, TimeM.time_pure, List.length_nil]
    omega
  | cons _ qs ih =>
    simp only [mapClearEntryM, TimeM.time_bind, TimeM.time_tick, TimeM.time_pure, ih,
      List.length_cons]
    omega

/-- `TimeM ℕ`-charged `clearDenomsList`. -/
@[expose] def clearDenomsListM (cs : List ℚ) : TimeM ℕ (ℕ × List ℤ) := do
  let D ← lcmDensM cs
  let ns ← mapClearEntryM D cs
  pure (D, ns)

@[simp]
theorem clearDenomsListM_ret (cs : List ℚ) :
    (clearDenomsListM cs).ret = clearDenomsList cs := by
  simp only [clearDenomsListM, clearDenomsList, TimeM.ret_bind, lcmDensM_ret, mapClearEntryM_ret,
    TimeM.ret_pure]

theorem clearDenomsListM_time (cs : List ℚ) :
    (clearDenomsListM cs).time = 4 * cs.length + 2 := by
  simp only [clearDenomsListM, TimeM.time_bind, lcmDensM_time, lcmDensM_ret, mapClearEntryM_time,
    TimeM.time_pure]
  omega

/-- `TimeM ℕ`-charged accumulator fold for `sqNormList`. -/
@[expose] def sqNormFoldM (acc : ℕ) : List ℤ → TimeM ℕ ℕ
  | [] => do
    TimeM.tick 1
    pure acc
  | a :: ns => do
    TimeM.tick 2
    sqNormFoldM (acc + Int.natAbs a ^ 2) ns

private theorem sqNormFoldM_ret (acc : ℕ) (ns : List ℤ) :
    (sqNormFoldM acc ns).ret = ns.foldl (fun s a => s + Int.natAbs a ^ 2) acc := by
  induction ns generalizing acc with
  | nil => simp only [sqNormFoldM, List.foldl_nil, TimeM.ret_bind, TimeM.ret_pure]
  | cons a ns ih => simp only [sqNormFoldM, List.foldl_cons, TimeM.ret_bind, ih]

private theorem sqNormFoldM_time (acc : ℕ) (ns : List ℤ) :
    (sqNormFoldM acc ns).time = 2 * ns.length + 1 := by
  induction ns generalizing acc with
  | nil =>
    simp only [sqNormFoldM, TimeM.time_bind, TimeM.time_tick, TimeM.time_pure, List.length_nil]
    omega
  | cons a ns ih =>
    simp only [sqNormFoldM, TimeM.time_bind, TimeM.time_tick, ih, List.length_cons]
    omega

/-- `TimeM ℕ`-charged `sqNormList`. -/
@[expose] def sqNormListM (ns : List ℤ) : TimeM ℕ ℕ :=
  sqNormFoldM 0 ns

@[simp]
theorem sqNormListM_ret (ns : List ℤ) : (sqNormListM ns).ret = sqNormList ns :=
  sqNormFoldM_ret 0 ns

theorem sqNormListM_time (ns : List ℤ) : (sqNormListM ns).time = 2 * ns.length + 1 :=
  sqNormFoldM_time 0 ns

/-- `TimeM ℕ`-charged natural-number power `base ^ exp` (`exp + 1` ticks). -/
@[expose] def powNatM (base : ℕ) : ℕ → TimeM ℕ ℕ
  | 0 => do
    TimeM.tick 1
    pure 1
  | exp + 1 => do
    let p ← powNatM base exp
    TimeM.tick 1
    pure (p * base)

@[simp]
theorem powNatM_ret (base exp : ℕ) : (powNatM base exp).ret = base ^ exp := by
  induction exp with
  | zero => simp only [powNatM, pow_zero, TimeM.ret_bind, TimeM.ret_pure]
  | succ exp ih => simp only [powNatM, pow_succ, TimeM.ret_bind, TimeM.ret_pure, ih]

theorem powNatM_time (base exp : ℕ) : (powNatM base exp).time = exp + 1 := by
  induction exp with
  | zero =>
    simp only [powNatM, TimeM.time_bind, TimeM.time_tick, TimeM.time_pure]
    omega
  | succ exp ih =>
    simp only [powNatM, TimeM.time_bind, TimeM.time_tick, TimeM.time_pure, ih]
    omega

/-- `TimeM ℕ`-charged base-4 ceiling logarithm `Nat.clog 4 n` (`Nat.clog 4 n + 1` ticks). -/
@[expose] def clog4M (n : ℕ) : TimeM ℕ ℕ :=
  if _h : n ≤ 1 then do
    TimeM.tick 1
    pure 0
  else do
    TimeM.tick 1
    let r ← clog4M ((n + 3) / 4)
    pure (r + 1)
termination_by n
decreasing_by omega

@[simp]
theorem clog4M_ret (n : ℕ) : (clog4M n).ret = Nat.clog 4 n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    unfold clog4M
    split_ifs with hle
    · simp only [TimeM.ret_bind, TimeM.ret_pure]
      have h0 : Nat.clog 4 n ≤ 0 := Nat.clog_le_of_le_pow (by simpa only [pow_zero] using hle)
      omega
    · simp only [TimeM.ret_bind, TimeM.ret_pure]
      have hlt : (n + 3) / 4 < n := by omega
      rw [ih _ hlt]
      have : (n + 3) / 4 = (n + 4 - 1) / 4 := by omega
      rw [this, ← Nat.clog_of_two_le (by decide : 2 ≤ 4) (by omega)]

theorem clog4M_time (n : ℕ) : (clog4M n).time = Nat.clog 4 n + 1 := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases hle : n ≤ 1
    · have h0 : Nat.clog 4 n = 0 := by
        rw [← clog4M_ret n]
        unfold clog4M
        simp only [eq_true hle, ↓reduceDIte, TimeM.ret_bind, TimeM.ret_pure]
      unfold clog4M
      simp only [eq_true hle, ↓reduceDIte, TimeM.time_bind, TimeM.time_tick, TimeM.time_pure, h0]
      omega
    · have hlt : (n + 3) / 4 < n := by omega
      have hrec : Nat.clog 4 n = Nat.clog 4 ((n + 3) / 4) + 1 := by
        rw [← clog4M_ret n]
        unfold clog4M
        simp only [eq_false hle, ↓reduceDIte, TimeM.ret_bind, TimeM.ret_pure, clog4M_ret]
      unfold clog4M
      simp only [eq_false hle, ↓reduceDIte, TimeM.time_bind, TimeM.time_tick, TimeM.time_pure,
        ih _ hlt, hrec]
      omega

/-- `TimeM ℕ`-charged `mignotteSepSqInv`. -/
@[expose] def mignotteSepSqInvM (cs : List ℚ) : TimeM ℕ ℕ := do
  let t ← trimM cs
  let tLen ← lengthM t
  let cd ← clearDenomsListM t
  let sn ← sqNormListM cd.2
  TimeM.tick 2
  let d := tLen - 1
  let p1 ← powNatM d (d + 2)
  let p2 ← powNatM sn (d - 1)
  TimeM.tick 1
  pure (p1 * p2)

@[simp]
theorem mignotteSepSqInvM_ret (cs : List ℚ) :
    (mignotteSepSqInvM cs).ret = mignotteSepSqInv cs := by
  simp only [mignotteSepSqInvM, mignotteSepSqInv, TimeM.ret_bind, trimM_ret, lengthM_ret,
    clearDenomsListM_ret, sqNormListM_ret, powNatM_ret, TimeM.ret_pure]

theorem mignotteSepSqInvM_time_le (cs : List ℚ) :
    (mignotteSepSqInvM cs).time ≤ 12 * cs.length + 14 := by
  have ht_le : (trim cs).length ≤ cs.length := trim_length_le cs
  have htr := trimM_time_le cs
  simp only [mignotteSepSqInvM, TimeM.time_bind, trimM_ret, lengthM_time, lengthM_ret,
    clearDenomsListM_time, clearDenomsListM_ret, sqNormListM_time, sqNormListM_ret,
    TimeM.time_tick, powNatM_time, TimeM.time_pure]
  have hns_len : (clearDenomsList (trim cs)).2.length = (trim cs).length := by
    simp only [clearDenomsList, List.length_map]
  rw [hns_len]
  omega

/-- `TimeM ℕ`-charged `mignotteBisectionDepth`. -/
@[expose] def mignotteBisectionDepthM (cs : List ℚ) : TimeM ℕ ℕ := do
  let t ← trimM cs
  let tLen ← lengthM t
  TimeM.tick 1
  if tLen ≤ 2 then
    pure 0
  else do
    let b ← cauchyBoundNatM cs
    let s ← mignotteSepSqInvM cs
    TimeM.tick 4
    clog4M (4 * b ^ 2 * s / 3 + 1)

@[simp]
theorem mignotteBisectionDepthM_ret (cs : List ℚ) :
    (mignotteBisectionDepthM cs).ret = mignotteBisectionDepth cs := by
  simp only [mignotteBisectionDepthM, mignotteBisectionDepth, TimeM.ret_bind, trimM_ret,
    lengthM_ret]
  split_ifs <;> simp only [TimeM.ret_bind, TimeM.ret_pure, cauchyBoundNatM_ret,
    mignotteSepSqInvM_ret, clog4M_ret]

theorem mignotteBisectionDepthM_time_le (cs : List ℚ) :
    (mignotteBisectionDepthM cs).time ≤ 24 * cs.length + mignotteBisectionDepth cs + 34 := by
  have ht_le : (trim cs).length ≤ cs.length := trim_length_le cs
  have htr := trimM_time_le cs
  simp only [mignotteBisectionDepthM, TimeM.time_bind, trimM_ret, lengthM_time, lengthM_ret,
    TimeM.time_tick]
  split_ifs with hlen
  · simp only [TimeM.time_pure]
    omega
  · simp only [TimeM.time_bind, cauchyBoundNatM_ret, mignotteSepSqInvM_ret, TimeM.time_tick,
      clog4M_time]
    have hcb := cauchyBoundNatM_time_le cs
    have hms := mignotteSepSqInvM_time_le cs
    have hdepth : mignotteBisectionDepth cs =
        Nat.clog 4 (4 * cauchyBoundNat cs ^ 2 * mignotteSepSqInv cs / 3 + 1) := by
      simp only [mignotteBisectionDepth, hlen, ↓reduceIte]
    omega

end Cslib.RealRoot
