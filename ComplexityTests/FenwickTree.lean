/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import Complexity.Init
public import Complexity.Algorithms.Lean.FenwickTree.Stateful
import Mathlib.Algebra.Group.ULift

/-!
# Fenwick Tree Tests and Non-Vacuity Witnesses

Kernel-checked examples and theorems (without `native_decide`) exercising:

1. `lowbit`, `downChain`, `upChain`, and `fenwickChildren` combinatorics.
2. Exact agreement between `ofList` / `ofArray` immediate-parent construction and incremental `add`
   from `zeros` (`ofList_eq_buildByAdds`), across empty (`n = 0`), singleton (`n = 1`), power-of-two
   (`n = 16`), and non-power-of-two (`n = 6, 13`) lengths, plus out-of-bounds totality and exact
   `TimeM` tick counts.
3. `[AddCommGroup ℤ]` operations (`rangeSum`, `get`, `set`) at length `n = 7` with negative updates,
   and universe polymorphism of `FenwickTree` in `Type 1` (`ULift.{1} ℤ`).
4. Adaptive `Cslib.Stateful` clients running on `FenwickTree` with checked answers, node-visit
   traces, and `Nat.clog 2 (s.length + 1)` bounds.
5. Positive and negative `Valid` witnesses showing both conjuncts of `Valid` are non-vacuous and
   independently necessary.
-/

public section

namespace ComplexityTests.FenwickTree

open Cslib.Algorithms.Lean Cslib.Algorithms.Lean.FenwickTree Cslib.Stateful

/-! ## 1. `lowbit`, chain, and child-interval checks -/

example :
    lowbit 0 = 0 ∧
      lowbit 1 = 1 ∧
      lowbit 6 = 2 ∧
      lowbit 12 = 4 ∧
      lowbit 13 = 1 ∧
      lowbit 16 = 16 := by
  simp [lowbit]

example :
    downChain 0 = [] ∧
      downChain 7 = [7, 6, 4] ∧
      downChain 13 = [13, 12, 8] ∧
      downChain 16 = [16] := by
  simp [downChain, lowbit]

example :
    upChain 16 0 = [] ∧
      upChain 16 1 = [1, 2, 4, 8, 16] ∧
      upChain 13 3 = [3, 4, 8] ∧
      upChain 13 14 = [] := by
  simp [upChain, lowbit]

example :
    fenwickChildren 8 = ({4, 6, 7} : Finset ℕ) ∧
      fenwickChildren 6 = ({5} : Finset ℕ) ∧
      fenwickChildren 5 = (∅ : Finset ℕ) :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩

/-! ## 2. `ofList` vs incremental `add`, non-power-of-two sizes, and `TimeM` costs -/

private def addFrom {α : Type*} [AddCommMonoid α] :
    ℕ → List α → FenwickTree α → FenwickTree α
  | _, [], t => t
  | idx, x :: xs, t => addFrom (idx + 1) xs (add t idx x)

/-- Build a Fenwick tree by `n` sequential `add` calls starting from `zeros xs.length`. -/
def buildByAdds {α : Type*} [AddCommMonoid α] (xs : List α) : FenwickTree α :=
  addFrom 0 xs (zeros xs.length)

private theorem addAt_append_zero_cons {α : Type*} [AddZeroClass α]
    (pre : List α) (x : α) (rest : List α) :
    addAt (pre ++ 0 :: rest) pre.length x = (pre ++ [x]) ++ rest := by
  induction pre with
  | nil =>
    simp only [addAt, List.nil_append, List.length_nil, List.getD_cons_zero,
      zero_add, List.set_cons_zero, List.singleton_append]
  | cons a as ih =>
    simpa only [addAt, List.cons_append, List.length_cons, List.getD_cons_succ,
      List.set_cons_succ] using congrArg (a :: ·) ih

private theorem valid_addFrom {α : Type*} [AddCommMonoid α]
    (pre suf : List α) {t : FenwickTree α}
    (hv : Valid t (pre ++ List.replicate suf.length 0)) :
    Valid (addFrom pre.length suf t) (pre ++ suf) := by
  induction suf generalizing pre t with
  | nil =>
    simpa only [addFrom, List.length_nil, List.replicate_zero, List.append_nil] using hv
  | cons x xs ih =>
    simp only [addFrom]
    have hstep := addAt_append_zero_cons pre x (List.replicate xs.length 0)
    have hv' : Valid (add t pre.length x) ((pre ++ [x]) ++ List.replicate xs.length 0) :=
      hstep ▸ valid_add hv pre.length x
    have hlen : (pre ++ [x]).length = pre.length + 1 := by
      simp only [List.length_append, List.length_singleton]
    simpa only [hlen, List.append_assoc, List.singleton_append] using ih (pre ++ [x]) hv'

/-- Canonical uniqueness corollary: linear-time `ofList xs` produces the exact same `FenwickTree α`
as `xs.length` incremental `add` updates on `zeros xs.length`. -/
theorem ofList_eq_buildByAdds {α : Type*} [AddCommMonoid α] (xs : List α) :
    ofList xs = buildByAdds xs := by
  apply (valid_ofList xs).unique
  simpa only [buildByAdds, List.nil_append, List.length_nil] using
    valid_addFrom ([] : List α) xs (valid_zeros _)

def sample6 : List ℕ := [3, 1, 4, 1, 5, 9]
def sample13 : List ℕ := [1, 3, 2, 5, 4, 6, 1, 2, 7, 3, 2, 4, 5]
def sample16 : List ℕ := [1, 0, 2, 1, 1, 3, 0, 4, 2, 5, 2, 2, 3, 1, 0, 2]

-- Empty (`n = 0`), singleton (`n = 1`), non-power-of-two (`n = 6, 13`), and `n = 16` checks
example :
    ofList ([] : List ℕ) = zeros 0 ∧
      ofList [42] = buildByAdds [42] ∧
      prefixSum (ofList [42]) 1 = 42 ∧
      (ofListM [42]).time = 1 ∧
      prefixSum (ofList ([] : List ℕ)) 5 = 0 ∧
      (ofListM ([] : List ℕ)).time = 0 ∧
      (prefixSumM (zeros (α := ℕ) 0) 3).time = 0 ∧
      (addM (zeros (α := ℕ) 0) 0 9).time = 0 := by
  refine ⟨ofList_nil, ofList_eq_buildByAdds _, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [prefixSum_eq (valid_ofList [42]) 1]; rfl
  · rw [ofListM_time_eq]; rfl
  · rw [prefixSum_eq (valid_ofList []) 5]; rfl
  · rw [ofListM_time_eq]; rfl
  · rw [prefixSumM_time_eq_downChain, size_zeros]; simp
  · rw [addM_time_eq_upChain, size_zeros]; simp

example :
    ofList sample6 = buildByAdds sample6 ∧
      ofList sample13 = buildByAdds sample13 ∧
      ofList sample16 = buildByAdds sample16 ∧
      (ofList sample13).size = 13 ∧
      (ofListM sample13).time = 13 ∧
      prefixSum (ofList sample13) 0 = 0 ∧
      prefixSum (ofList sample13) 7 = 22 ∧
      prefixSum (ofList sample13) 13 = 45 ∧
      prefixSum (ofList sample13) 20 = 45 ∧
      (prefixSumM (ofList sample13) 13).time = 3 ∧
      (addM (ofList sample13) 2 10).time = 3 ∧
      add (ofList sample6) 6 99 = ofList sample6 ∧
      (addM (ofList sample6) 6 99).time = 0 := by
  refine ⟨ofList_eq_buildByAdds _, ofList_eq_buildByAdds _, ofList_eq_buildByAdds _,
    size_ofList _, ofListM_time_eq _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [prefixSum_eq (valid_ofList sample13) 0]; decide
  · rw [prefixSum_eq (valid_ofList sample13) 7]; decide
  · rw [prefixSum_eq (valid_ofList sample13) 13]; decide
  · rw [prefixSum_eq (valid_ofList sample13) 20]; decide
  · rw [prefixSumM_time_eq_downChain, size_ofList]; simp [sample13, downChain, lowbit]
  · rw [addM_time_eq_upChain, size_ofList]; simp [sample13, upChain, lowbit]
  · exact add_of_size_le _ 99 (by rw [size_ofList]; decide)
  · rw [addM_time_eq_upChain, size_ofList]; simp [sample6]

/-! ## 3. Signed `[AddCommGroup ℤ]` operations and universe polymorphism -/

def signedSample : List ℤ := [4, -2, 7, -5, 3, 1, -6]

example :
    let t0 := ofList signedSample
    let t1 := set (add t0 1 (-10)) 4 20
    rangeSum t0 1 5 = 3 ∧
      rangeSum t0 5 2 = 0 ∧
      get t0 2 = 7 ∧
      get t0 9 = 0 ∧
      get t1 1 = -12 ∧
      get t1 4 = 20 ∧
      rangeSum t1 1 6 = 11 ∧
      set t1 20 99 = t1 := by
  dsimp only
  have hv0 := valid_ofList signedSample
  have hv1 := valid_set (valid_add hv0 1 (-10)) 4 20
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [rangeSum_eq hv0]; decide
  · rw [rangeSum_eq hv0]; decide
  · rw [get_eq hv0]; decide
  · rw [get_eq hv0]; decide
  · rw [get_eq hv1]; decide
  · rw [get_eq hv1]; decide
  · rw [rangeSum_eq hv1]; decide
  · exact set_of_size_le _ 99 (by simp [signedSample])

-- Universe polymorphism check: `FenwickTree` at `Type 1` (`ULift.{1} ℤ`)
example :
    let s : List (ULift.{1} ℤ) := [⟨3⟩, ⟨-1⟩, ⟨5⟩]
    Valid (ofList s) s ∧
      prefixSum (ofList s) 2 = ⟨2⟩ ∧
      rangeSum (ofList s) 1 3 = ⟨4⟩ := by
  intro s
  have hv := valid_ofList s
  refine ⟨hv, ?_, ?_⟩
  · rw [prefixSum_eq hv]; rfl
  · rw [rangeSum_eq hv]; rfl

/-! ## 4. Adaptive `Cslib.Stateful` client execution and non-vacuity -/

/-- Adaptive client: query `prefixSum 3`; if at least `8`, add `10` at index `4`, else add `2` at
index `0`; then return `(initialSum, prefixSum 6)`. -/
def adaptiveClient : (spec ℕ).Client (ℕ × ℕ) :=
  .liftBind (.prefixSum 3) fun s3 =>
    .liftBind (if 8 ≤ s3 then .add 4 10 else .add 0 2) fun _ =>
      .liftBind (.prefixSum 6) fun s6 =>
        .pure (s3, s6)

-- On `[3, 1, 4, 1, 5, 9]`, `s3 = 8 ≥ 8`, so branch 1 adds `10` at index `4` (`s6 = 33`);
-- on `[1, 1, 1, 1, 1, 1]`, `s3 = 3 < 8`, so branch 2 adds `2` at index `0` (`s6 = 8`).
example :
    (run (ofList sample6) adaptiveClient).1 = (8, 33) ∧
      (run (ofList sample6) adaptiveClient).2.2 = [2, 2, 2] ∧
      (run (ofList [1, 1, 1, 1, 1, 1]) adaptiveClient).1 = (3, 8) ∧
      (run (ofList [1, 1, 1, 1, 1, 1]) adaptiveClient).2.2 = [2, 3, 2] := by
  have hc1 := run_correct adaptiveClient (valid_ofList sample6)
  have hc2 := run_correct adaptiveClient (valid_ofList [1, 1, 1, 1, 1, 1])
  refine ⟨hc1.1.trans (by decide), ?_, hc2.1.trans (by decide), ?_⟩
  · dsimp only [adaptiveClient, run, step]
    rw [ret_prefixSumM_eq (valid_ofList sample6) 3]
    simp [sample6, ret_addM, prefixSumM_time_eq_downChain, addM_time_eq_upChain,
      downChain, upChain, lowbit]
  · set ones : List ℕ := [1, 1, 1, 1, 1, 1]
    dsimp only [adaptiveClient, run, step]
    rw [ret_prefixSumM_eq (valid_ofList ones) 3]
    simp [ones, ret_addM, prefixSumM_time_eq_downChain, addM_time_eq_upChain,
      downChain, upChain, lowbit]

-- Non-vacuity witness for `Valid`, `stepBound`, and `run_correct`
example :
    let s := sample6
    let t := ofList s
    Valid t s ∧
      (run t adaptiveClient).1 = ((spec ℕ).runClient s adaptiveClient).1 ∧
      Valid (run t adaptiveClient).2.1 ((spec ℕ).runClient s adaptiveClient).2.1 ∧
      total id (run t adaptiveClient).2.2 ≤
        ((spec ℕ).runClient s adaptiveClient).2.2.length * Nat.clog 2 (s.length + 1) :=
  ⟨valid_ofList sample6, run_correct adaptiveClient (valid_ofList sample6)⟩

/-! ## 5. Positive and negative `Valid` witnesses -/

-- Positive witness: `⟨#[3, 4, 4, 9]⟩` satisfies `Valid` for `[3, 1, 4, 1]`, hence equals `ofList`
theorem valid_manual4 : Valid (⟨#[3, 4, 4, 9]⟩ : FenwickTree ℕ) [3, 1, 4, 1] := by
  refine ⟨rfl, fun m hm1 hm4 => ?_⟩
  have hm_cases : m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 := by
    change m ≤ 4 at hm4
    omega
  rcases hm_cases with rfl | rfl | rfl | rfl <;>
    simp [lowbit]

example : ofList [3, 1, 4, 1] = ⟨#[3, 4, 4, 9]⟩ :=
  (valid_ofList [3, 1, 4, 1]).unique valid_manual4

-- Negative witness 1 (size mismatch): right prefix entries on `[1..3]` but wrong array size
example : ¬ Valid (⟨#[3, 4, 4]⟩ : FenwickTree ℕ) [3, 1, 4, 1] := by
  intro hv
  have h : (3 : ℕ) = 4 := hv.1
  omega

-- Negative witness 2 (corrupted parent slot): right size `4`, leaves OK, node `4` wrong (`8 ≠ 9`)
example : ¬ Valid (⟨#[3, 4, 4, 8]⟩ : FenwickTree ℕ) [3, 1, 4, 1] := by
  intro hv
  have h4 := hv.2 4 (by omega) (by decide)
  have hlhs : (⟨#[3, 4, 4, 8]⟩ : FenwickTree ℕ).tree[4 - 1] = 8 := rfl
  have hrhs : (([3, 1, 4, 1].take 4).drop (4 - lowbit 4)).sum = 9 := by simp [lowbit]
  rw [hlhs, hrhs] at h4
  omega

end ComplexityTests.FenwickTree
