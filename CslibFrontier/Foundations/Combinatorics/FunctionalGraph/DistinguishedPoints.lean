/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Combinatorics.FunctionalGraph

/-!
# Semantic correctness of the distinguished-point algorithm

This module proves the semantic correctness of the six-step distinguished-point procedure for
evaluating a fixed iterate `f^[T] x` using walk length `K`:

1. **Scan (`scan`, `scan_spec`)**: walk `K` steps from `x`, recording the first distinguished
   point `c = f^[d] x` with `d ≤ K` if one occurs, and ending at `u = f^[K] x`.
2. **Lookup**: read the pre-shifted payload `z c = f^[T - K] c`.
3. **Correction (`correctionStep`, `correction_run`)**: apply `f` for `K - d` steps from `z c` to
   obtain `f^[K - d] (f^[T - K] (f^[d] x)) = f^[T] x` (`shifted_payload`).
4. **Period walk (`periodWalk`, `periodWalk_spec`)**: in a separate register, walk up to `K` steps
   from `u = f^[K] x` to find its minimal return period `1 ≤ λ ≤ K` when the prefix repeats.
5. **Residue and cycle walk (`walkStep`, `walk_run`)**: walk `R λ = (T - K) % λ` steps from `u`.
6. **Output (`distinguishedPower`, `distinguishedPower_correct`)**: return the corrected checkpoint
   value when the scan hit `H`, and the cycle-walk value otherwise.

The set `H` of distinguished points is abstract: the proof assumes only that every trajectory
prefix `x, f x, …, f^[K] x` of `K + 1` pairwise distinct states meets `H`.

## Main definitions

* `Cslib.FunctionalGraph.runStages`: sequential execution of `k` indexed stages.
* `Cslib.FunctionalGraph.ScanState`, `Cslib.FunctionalGraph.scanStep`,
  `Cslib.FunctionalGraph.scan`: the `K`-step distinguished-point prefix scan.
* `Cslib.FunctionalGraph.correctionStep`: the forward-correction stage.
* `Cslib.FunctionalGraph.PeriodState`, `Cslib.FunctionalGraph.periodStep`,
  `Cslib.FunctionalGraph.periodWalk`: the short-cycle period walk in a separate register.
* `Cslib.FunctionalGraph.walkStep`: the bounded cycle-walk stage.
* `Cslib.FunctionalGraph.distinguishedPower`: the six-step distinguished-point procedure.

## Main results

* `Cslib.FunctionalGraph.shifted_payload`: forward correction of a backward-shifted checkpoint
  payload recovers `f^[T] x`.
* `Cslib.FunctionalGraph.scan_spec`: invariant and specification of the prefix scan.
* `Cslib.FunctionalGraph.correction_run`: exact step count of the forward correction.
* `Cslib.FunctionalGraph.periodWalk_spec`: exact first return time of the period walk.
* `Cslib.FunctionalGraph.walk_run`: exact step count of the cycle walk.
* `Cslib.FunctionalGraph.distinguishedPower_correct`: semantic correctness of the
  distinguished-point procedure.

## References

* Adapted from lean/Proofs/{Reconstruction,DistinguishedPoints}.lean at revision `c4cfa198` of
  [S. Schlesinger, *Square-root circuit bounds for iterated functions*]
  [Schlesinger2026IteratedFunctions].
-/

@[expose] public section

namespace Cslib.FunctionalGraph

open Function

universe u v
variable {α : Type u} (f : α → α)

variable {f} in
/-- A checkpoint at time `d ≤ K` permits forward-only correction of the backward-shifted payload
`f^[T - K] (f^[d] x)` when `K ≤ T`. -/
theorem shifted_payload {x : α} {d K T : ℕ} (hd : d ≤ K) (hT : K ≤ T) :
    f^[K - d] (f^[T - K] (f^[d] x)) = f^[T] x := by
  rw [← iterate_add_apply, ← iterate_add_apply]
  congr 1
  omega

/-- Apply indexed stages `0, …, k - 1` in order. -/
def runStages {β : Type v} (step : ℕ → β → β) : ℕ → β → β
  | 0, b => b
  | k + 1, b => step k (runStages step k b)

/-- Running no stages leaves the state unchanged. -/
@[simp]
theorem runStages_zero {β : Type v} (step : ℕ → β → β) (b : β) :
    runStages step 0 b = b := rfl

/-- Running `k + 1` stages runs the first `k` and then stage `k`. -/
@[simp]
theorem runStages_succ {β : Type v} (step : ℕ → β → β) (k : ℕ) (b : β) :
    runStages step (k + 1) b = step k (runStages step k b) := rfl

/-! ### Step 1: Prefix scan -/

/-- The state `(u, found, d, c)` maintained during the distinguished-point prefix scan. -/
structure ScanState (α : Type u) where
  /-- Current trajectory state. -/
  u : α
  /-- Whether a distinguished point has been encountered so far. -/
  found : Bool
  /-- Index of the first distinguished point encountered. -/
  d : ℕ
  /-- The first distinguished point encountered. -/
  c : α

section Scan

variable (H : α → Prop) [DecidablePred H]

/-- Scan stage `i`: record the first distinguished point, then advance `u` unless `i = K`. -/
def scanStep (K i : ℕ) (σ : ScanState α) : ScanState α where
  u := if i < K then f σ.u else σ.u
  found := σ.found || decide (H σ.u)
  d := if σ.found = false ∧ H σ.u then i else σ.d
  c := if σ.found = false ∧ H σ.u then σ.u else σ.c

/-- Run stages `i = 0, 1, …, K` of the scan starting from `(x, false, 0, x)`. -/
def scan (K : ℕ) (x : α) : ScanState α :=
  runStages (scanStep f H K) (K + 1) ⟨x, false, 0, x⟩

private theorem scan_invariant (K : ℕ) (x : α) :
    ∀ k ≤ K + 1,
      (runStages (scanStep f H K) k ⟨x, false, 0, x⟩).u = f^[min k K] x ∧
      ((runStages (scanStep f H K) k ⟨x, false, 0, x⟩).found = true ↔
        ∃ i < k, H (f^[i] x)) ∧
      ((runStages (scanStep f H K) k ⟨x, false, 0, x⟩).found = true →
        (runStages (scanStep f H K) k ⟨x, false, 0, x⟩).d < k ∧
        H (f^[(runStages (scanStep f H K) k ⟨x, false, 0, x⟩).d] x) ∧
        (∀ i < (runStages (scanStep f H K) k ⟨x, false, 0, x⟩).d, ¬ H (f^[i] x)) ∧
        (runStages (scanStep f H K) k ⟨x, false, 0, x⟩).c =
          f^[(runStages (scanStep f H K) k ⟨x, false, 0, x⟩).d] x) := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hk
    obtain ⟨hu, hiff, hfd⟩ := ih (by omega)
    rw [runStages_succ]
    generalize hσ : runStages (scanStep f H K) k ⟨x, false, 0, x⟩ = σ at hu hiff hfd
    have hmin : min k K = k := by omega
    rw [hmin] at hu
    refine ⟨?_, ?_, ?_⟩
    · simp only [scanStep]
      by_cases hkK : k < K
      · rw [ite_eq_left hkK, hu, ← iterate_succ_apply' f k x]
        congr 1
        omega
      · rw [ite_eq_right hkK, hu]
        congr 1
        omega
    · simp only [scanStep, Bool.or_eq_true, decide_eq_true_eq, hiff, hu]
      constructor
      · rintro (⟨i, hi, hHi⟩ | hHk)
        · exact ⟨i, by omega, hHi⟩
        · exact ⟨k, by omega, hHk⟩
      · rintro ⟨i, hi, hHi⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
        · exact Or.inl ⟨i, hi, hHi⟩
        · exact Or.inr hHi
    · intro hfound
      simp only [scanStep]
      by_cases hσt : σ.found = true
      · obtain ⟨hd, hHd, hfirst, hc⟩ := hfd hσt
        have hnot : ¬ (σ.found = false ∧ H σ.u) := by simp [hσt]
        rw [ite_eq_right hnot, ite_eq_right hnot]
        exact ⟨by omega, hHd, hfirst, hc⟩
      · have hσf : σ.found = false := by simpa using hσt
        have hHu : H σ.u := by
          simpa [scanStep, hσf] using hfound
        have hyes : σ.found = false ∧ H σ.u := ⟨hσf, hHu⟩
        rw [ite_eq_left hyes, ite_eq_left hyes]
        have hnone : ¬ ∃ i < k, H (f^[i] x) := by
          rw [← hiff, hσf]
          simp
        refine ⟨by omega, hu ▸ hHu, ?_, hu⟩
        intro i hi hHi
        exact hnone ⟨i, hi, hHi⟩

/-- The scan ends at `f^[K] x` and records the first distinguished point among
`x, f x, …, f^[K] x` whenever one exists. -/
theorem scan_spec (K : ℕ) (x : α) :
    (scan f H K x).u = f^[K] x ∧
    ((scan f H K x).found = true ↔ ∃ i ≤ K, H (f^[i] x)) ∧
    ((scan f H K x).found = true →
      (scan f H K x).d ≤ K ∧ H (f^[(scan f H K x).d] x) ∧
      (∀ i < (scan f H K x).d, ¬ H (f^[i] x)) ∧
      (scan f H K x).c = f^[(scan f H K x).d] x) := by
  unfold scan
  obtain ⟨hu, hiff, hfd⟩ := scan_invariant f H K x (K + 1) le_rfl
  rw [show min (K + 1) K = K by omega] at hu
  refine ⟨hu, ?_, ?_⟩
  · rw [hiff]
    exact ⟨fun ⟨i, hi, h⟩ => ⟨i, by omega, h⟩, fun ⟨i, hi, h⟩ => ⟨i, by omega, h⟩⟩
  · intro hfound
    obtain ⟨hd, hHd, hfirst, hc⟩ := hfd hfound
    exact ⟨by omega, hHd, hfirst, hc⟩

end Scan

/-! ### Step 3: Forward correction -/

/-- Correction stage `i`: apply `f` exactly when `d ≤ i`. -/
def correctionStep (d i : ℕ) (v : α) : α :=
  if d ≤ i then f v else v

/-- Running `k` correction stages applies `f` exactly `k - d` times. -/
theorem correction_run (d k : ℕ) (v : α) :
    runStages (correctionStep f d) k v = f^[k - d] v := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [runStages_succ, ih, correctionStep]
    by_cases hd : d ≤ k
    · rw [ite_eq_left hd, ← iterate_succ_apply' f (k - d) v]
      congr 1
      omega
    · rw [ite_eq_right hd]
      congr 1
      omega

/-! ### Step 4: Period walk in a separate register -/

/-- The configuration `(w, found, period)` of the short-cycle period walk. -/
structure PeriodState (α : Type u) where
  /-- Current walking state. -/
  w : α
  /-- Whether a return to the starting state `y` has been observed. -/
  found : Bool
  /-- Recorded return period (initialized to dummy value `1`). -/
  period : ℕ

section Period

variable [DecidableEq α]

/-- Period stage `i` (step `j = i + 1`): advance `w` and record `i + 1` on the first return to
`y`. -/
def periodStep (y : α) (i : ℕ) (σ : PeriodState α) : PeriodState α where
  w := f σ.w
  found := σ.found || decide (f σ.w = y)
  period := if σ.found = false ∧ f σ.w = y then i + 1 else σ.period

/-- Run `K` stages of the period walk from `y`. -/
def periodWalk (K : ℕ) (y : α) : PeriodState α :=
  runStages (periodStep f y) K ⟨y, false, 1⟩

private theorem periodWalk_invariant (y : α) (k : ℕ) :
    (runStages (periodStep f y) k ⟨y, false, 1⟩).w = f^[k] y ∧
    ((runStages (periodStep f y) k ⟨y, false, 1⟩).found = true ↔
      ∃ j, 1 ≤ j ∧ j ≤ k ∧ f^[j] y = y) ∧
    ((runStages (periodStep f y) k ⟨y, false, 1⟩).found = true →
      1 ≤ (runStages (periodStep f y) k ⟨y, false, 1⟩).period ∧
      (runStages (periodStep f y) k ⟨y, false, 1⟩).period ≤ k ∧
      f^[(runStages (periodStep f y) k ⟨y, false, 1⟩).period] y = y ∧
      ∀ j, 1 ≤ j → j < (runStages (periodStep f y) k ⟨y, false, 1⟩).period →
        f^[j] y ≠ y) := by
  induction k with
  | zero =>
    refine ⟨rfl, ?_, ?_⟩
    · simp only [runStages_zero, Bool.false_eq_true, false_iff, not_exists, not_and]
      intro j h1 h0
      omega
    · simp
  | succ k ih =>
    obtain ⟨hw, hiff, hfd⟩ := ih
    rw [runStages_succ]
    generalize hσ : runStages (periodStep f y) k ⟨y, false, 1⟩ = σ at hw hiff hfd
    have hstep : f σ.w = f^[k + 1] y := by
      rw [hw, iterate_succ_apply']
    refine ⟨hstep, ?_, ?_⟩
    · simp only [periodStep, Bool.or_eq_true, decide_eq_true_eq, hiff, hstep]
      constructor
      · rintro (⟨j, h1, hj, he⟩ | he)
        · exact ⟨j, h1, by omega, he⟩
        · exact ⟨k + 1, by omega, le_rfl, he⟩
      · rintro ⟨j, h1, hj, he⟩
        rcases Nat.lt_or_ge j (k + 1) with hj' | hj'
        · exact Or.inl ⟨j, h1, by omega, he⟩
        · have : j = k + 1 := by omega
          subst this
          exact Or.inr he
    · intro hfound
      simp only [periodStep]
      by_cases hσt : σ.found = true
      · obtain ⟨h1, hle, he, hmin⟩ := hfd hσt
        have hnot : ¬ (σ.found = false ∧ f σ.w = y) := by simp [hσt]
        rw [ite_eq_right hnot]
        exact ⟨h1, by omega, he, hmin⟩
      · have hσf : σ.found = false := by simpa using hσt
        have hret : f σ.w = y := by
          simpa [periodStep, hσf] using hfound
        have hyes : σ.found = false ∧ f σ.w = y := ⟨hσf, hret⟩
        rw [ite_eq_left hyes]
        have hnone : ¬ ∃ j, 1 ≤ j ∧ j ≤ k ∧ f^[j] y = y := by
          rw [← hiff, hσf]
          simp
        refine ⟨by omega, le_rfl, hstep ▸ hret, ?_⟩
        intro j h1 hj he
        exact hnone ⟨j, h1, by omega, he⟩

/-- If `y` returns to itself within `K` positive steps, `periodWalk f K y` records the least
positive return time `1 ≤ λ ≤ K`. -/
theorem periodWalk_spec (K : ℕ) (y : α) (h : ∃ p, 1 ≤ p ∧ p ≤ K ∧ f^[p] y = y) :
    1 ≤ (periodWalk f K y).period ∧ (periodWalk f K y).period ≤ K ∧
    IsPeriodicPt f (periodWalk f K y).period y ∧
    ∀ j, 1 ≤ j → j < (periodWalk f K y).period → f^[j] y ≠ y := by
  obtain ⟨_, hiff, hfd⟩ := periodWalk_invariant f y K
  exact hfd (hiff.mpr h)

end Period

/-! ### Step 5: Cycle walk -/

/-- Cycle-walk stage `i`: apply `f` exactly when `i < r`. -/
def walkStep (r i : ℕ) (v : α) : α :=
  if i < r then f v else v

/-- Running `k` cycle-walk stages applies `f` exactly `min r k` times. -/
theorem walk_run (r k : ℕ) (v : α) :
    runStages (walkStep f r) k v = f^[min r k] v := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [runStages_succ, ih, walkStep]
    by_cases hk : k < r
    · rw [ite_eq_left hk, ← iterate_succ_apply' f (min r k) v]
      congr 1
      omega
    · rw [ite_eq_right hk]
      congr 1
      omega

/-! ### The complete distinguished-point procedure -/

section Algorithm

variable (H : α → Prop) [DecidablePred H] [DecidableEq α]

/-- The six-step distinguished-point procedure for `f^[T]` with walk length `K`, payload table `z`,
and residue table `R`. For `T < K` it unrolls `T` steps; otherwise it scans `K` steps, corrects the
payload `z σ.c` forward, walks the period of `σ.u = f^[K] x` in a separate register, advances `σ.u`
by `R w.period` steps, and selects the checkpoint branch iff the scan hit `H`. -/
def distinguishedPower (K T : ℕ) (z : α → α) (R : ℕ → ℕ) (x : α) : α :=
  if T < K then f^[T] x
  else
    let σ := scan f H K x
    let v := runStages (correctionStep f σ.d) K (z σ.c)
    let w := periodWalk f K σ.u
    let v' := runStages (walkStep f (R w.period)) K σ.u
    if σ.found then v else v'

/-- **Semantic correctness of the distinguished-point algorithm.** If every prefix of `K + 1`
pairwise distinct states meets `H`, the payloads satisfy `z h = f^[T - K] h` on `H`, and the
residues satisfy `R l = (T - K) % l` for `1 ≤ l ≤ K`, then `distinguishedPower f H K T z R x =
f^[T] x` for every input `x`. -/
theorem distinguishedPower_correct (K T : ℕ) (z : α → α) (R : ℕ → ℕ)
    (hhit : ∀ y : α, (∀ i ≤ K, ∀ j ≤ K, f^[i] y = f^[j] y → i = j) →
      ∃ i ≤ K, H (f^[i] y))
    (hz : ∀ h, H h → z h = f^[T - K] h)
    (hR : ∀ l, 1 ≤ l → l ≤ K → R l = (T - K) % l)
    (x : α) :
    distinguishedPower f H K T z R x = f^[T] x := by
  unfold distinguishedPower
  split_ifs with hTK
  · rfl
  push Not at hTK
  obtain ⟨hu, hiff, hfd⟩ := scan_spec f H K x
  simp only
  cases hfound : (scan f H K x).found with
  | true =>
    obtain ⟨hd, hHd, -, hc⟩ := hfd hfound
    simp only [ite_true]
    rw [correction_run, hc, hz _ (hc ▸ hHd)]
    exact shifted_payload hd hTK
  | false =>
    simp only [Bool.false_eq_true, ite_false]
    have hnohit : ¬ ∃ i ≤ K, H (f^[i] x) := by
      rw [← hiff, hfound]
      simp
    have hrep : ∃ i j, i < j ∧ j ≤ K ∧ f^[i] x = f^[j] x := by
      by_contra hno
      apply hnohit
      apply hhit x
      intro i hi j hj he
      by_contra hne
      rcases Nat.lt_or_gt_of_ne hne with hij | hji
      · exact hno ⟨i, j, hij, hj, he⟩
      · exact hno ⟨j, i, hji, hi, he.symm⟩
    obtain ⟨i, j, hij, hjK, he⟩ := hrep
    have hperK : IsPeriodicPt f (j - i) (f^[K] x) := by
      have hp := (isPeriodicPt_of_iterate_eq hij.le he).apply_iterate (K - i)
      rwa [← iterate_add_apply, Nat.sub_add_cancel (by omega : i ≤ K)] at hp
    obtain ⟨hl1, hlK, hlper, -⟩ :=
      periodWalk_spec f K (scan f H K x).u ⟨j - i, by omega, by omega, hu ▸ hperK⟩
    set l := (periodWalk f K (scan f H K x).u).period
    have hr : R l = (T - K) % l := hR l hl1 hlK
    have hrK : min (R l) K = (T - K) % l := by
      have := Nat.mod_lt (T - K) (by omega : 0 < l)
      rw [hr]
      omega
    rw [walk_run, hrK, hlper.iterate_mod_apply, hu, ← iterate_add_apply,
      Nat.sub_add_cancel hTK]

end Algorithm

end Cslib.FunctionalGraph
