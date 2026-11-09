/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Algorithms.Lean.BurrowsWheeler.Basic
public import Cslib.Algorithms.Lean.TimeM

/-!
# Table-driven inversion of the Burrows–Wheeler transform

[BurrowsWheeler1994], Section 4.2, inverts the transform with two tables computed from the last
column `L`: `C[c]`, the number of symbols of `L` smaller than `c`, and the rank array `P`, where
`P[i]` counts the occurrences of `L[i]` in `L[0..i-1]`. The LF-mapping is then the lookup
`T i = P[i] + C[L[i]]`, and the word is decoded by `|L|` such lookups.

## Cost model

`lfDecodeM` charges one `TimeM` tick per LF step, and nothing else. The tables are given to it
as a function `C : α → ℕ` and a list `P : List ℕ`, so lookups `C c`, `P[r]` and `L[r]` are
idealized as unit-cost random access, and building the tables is not charged. The report builds
them with two passes over the data and one over the alphabet; that construction, and the sort of
the forward transform, are not costed here.

## Main definitions

* `rankTable L`: the rank array `P` of [BurrowsWheeler1994], Section 4.2.
* `lfDecodeM L C P k r acc`: `k` charged LF steps `r ↦ P[r] + C[L[r]]` from row `r`.
* `inverseBwtM (L, I)`: the charged decoder, with `C c = L.countP (· < c)` and `P = rankTable L`.

## Main results

* `getElem?_rankTable`: `P[i] = (L.take i).count L[i]`.
* `lfDecodeM_ret`: with correct tables, the charged decoder returns `lfDecode`.
* `inverseBwtM_bwt`: decoding `bwt w` returns `w` after exactly `|w|` LF steps.
* `inverseBwtM_time_le`: at most `|L|` LF steps on every input.

## References

* [BurrowsWheeler1994]
-/

public section

namespace Cslib.Algorithms.Lean.BurrowsWheeler

open Cslib.Algorithms.Lean

variable {α : Type*}

/-! ## The rank table -/

section RankTable

variable [DecidableEq α]

/-- `rankTableFrom cnt L` lists, for each position `i`, `cnt L[i]` plus the number of earlier
occurrences of `L[i]`. It is one left-to-right pass with a running count per symbol. -/
def rankTableFrom (cnt : α → ℕ) : List α → List ℕ
  | [] => []
  | a :: L => cnt a :: rankTableFrom (Function.update cnt a (cnt a + 1)) L

/-- The rank array `P` of [BurrowsWheeler1994], Section 4.2: `P[i]` is the number of occurrences
of `L[i]` before position `i` (Batteries' `L.countBefore L[i] i`). -/
def rankTable (L : List α) : List ℕ := rankTableFrom (fun _ => 0) L

theorem getElem?_rankTableFrom :
    ∀ (cnt : α → ℕ) (L : List α) (i : ℕ),
      (rankTableFrom cnt L)[i]? = L[i]?.map fun a => cnt a + (L.take i).count a
  | _, [], _ => by simp [rankTableFrom]
  | cnt, a :: L, 0 => by simp [rankTableFrom]
  | cnt, a :: L, i + 1 => by
    rw [rankTableFrom, List.getElem?_cons_succ, getElem?_rankTableFrom, List.getElem?_cons_succ,
      List.take_succ_cons]
    cases L[i]? with
    | none => rfl
    | some b =>
      simp only [Option.map_some, List.count_cons]
      by_cases hab : b = a
      · subst hab
        simp only [Function.update_self, beq_self_eq_true, ite_true]
        rw [Nat.add_right_comm, Nat.add_assoc]
      · simp [hab, Ne.symm hab]

theorem getElem?_rankTable (L : List α) (i : ℕ) :
    (rankTable L)[i]? = L[i]?.map fun a => (L.take i).count a := by
  simp [rankTable, getElem?_rankTableFrom]

end RankTable

/-! ## The charged decoder -/

/-- `k` LF steps from row `r` with the tables `C` and `P`, prepending the symbols read to `acc`.
Each step costs one tick: it reads `L[r]` and `P[r]` and moves to `P[r] + C[L[r]]`
([BurrowsWheeler1994], Section 4.2). It stops early out of range. -/
def lfDecodeM (L : List α) (C : α → ℕ) (P : List ℕ) :
    ℕ → ℕ → List α → TimeM ℕ (List α)
  | 0, _, acc => pure acc
  | k + 1, r, acc =>
    match L[r]?, P[r]? with
    | some c, some p => do
      TimeM.tick 1
      lfDecodeM L C P k (p + C c) (c :: acc)
    | _, _ => pure acc

/-- `k` charged LF steps cost at most `k`, whatever the tables. -/
theorem lfDecodeM_time_le (L : List α) (C : α → ℕ) (P : List ℕ) :
    ∀ (k r : ℕ) (acc : List α), (lfDecodeM L C P k r acc).time ≤ k
  | 0, _, _ => by simp [lfDecodeM]
  | k + 1, r, acc => by
    rw [lfDecodeM]
    split
    · simp only [TimeM.time_bind, TimeM.time_tick]
      have := lfDecodeM_time_le L C P k
      grind
    · simp

variable [LinearOrder α]

/-- With the tables of Section 4.2, the charged decoder computes `lfDecode`. -/
theorem lfDecodeM_ret (L : List α) {C : α → ℕ} (hC : ∀ c, C c = L.countP (· < c)) :
    ∀ (k r : ℕ) (acc : List α),
      (lfDecodeM L C (rankTable L) k r acc).ret = lfDecode L k r acc
  | 0, _, _ => rfl
  | k + 1, r, acc => by
    rw [lfDecodeM, lfDecode, getElem?_rankTable]
    cases h : L[r]? with
    | none => rfl
    | some c =>
      simp only [Option.map_some, TimeM.ret_bind]
      rw [lfDecodeM_ret L hC k, lfMap, h, hC, Nat.add_comm]

/-- From a row holding `w.rotate k`, the charged decoder takes exactly `k` LF steps. -/
theorem lfDecodeM_bwtLast_time (w : List α) {C : α → ℕ}
    (hC : ∀ c, C c = (bwtLast w).countP (· < c)) :
    ∀ (k : ℕ), k ≤ w.length → ∀ (r : ℕ) (hr : r < (bwtMatrix w).length) (acc : List α),
      (bwtMatrix w)[r] = w.rotate k →
        (lfDecodeM (bwtLast w) C (rankTable (bwtLast w)) k r acc).time = k
  | 0, _, _, _, _, _ => rfl
  | k + 1, hk, r, hr, acc, hrow => by
    obtain ⟨hL, hrow'⟩ := bwtLast_lfMap_step w (by omega) hr hrow
    have hP := getElem?_rankTable (bwtLast w) r
    rw [hL, Option.map_some] at hP
    have hlf : ((bwtLast w).take r).count w[k] + C w[k] = lfMap (bwtLast w) r := by
      rw [lfMap, hL, hC, Nat.add_comm]
    rw [lfDecodeM, hL, hP]
    simp only [TimeM.time_bind, TimeM.time_tick]
    rw [hlf, lfDecodeM_bwtLast_time w hC k (by omega) _ (lfMap_bwtLast_lt w hr) _ hrow',
      Nat.add_comm]

/-- The charged inverse transform: `|L|` table-driven LF steps from row `I`. -/
def inverseBwtM (p : List α × ℕ) : TimeM ℕ (List α) :=
  lfDecodeM p.1 (fun c => p.1.countP (· < c)) (rankTable p.1) p.1.length p.2 []

theorem inverseBwtM_ret (p : List α × ℕ) : (inverseBwtM p).ret = inverseBwt p :=
  lfDecodeM_ret p.1 (fun _ => rfl) _ _ _

/-- The charged inverse takes at most `|L|` LF steps on every input. -/
theorem inverseBwtM_time_le (p : List α × ℕ) : (inverseBwtM p).time ≤ p.1.length :=
  lfDecodeM_time_le _ _ _ _ _ _

/-- Decoding `bwt w` returns `w` after exactly `|w|` LF steps. -/
theorem inverseBwtM_bwt (w : List α) :
    (inverseBwtM (bwt w)).ret = w ∧ (inverseBwtM (bwt w)).time = w.length := by
  refine ⟨by rw [inverseBwtM_ret, inverseBwt_bwt], ?_⟩
  rw [inverseBwtM, fst_bwt, snd_bwt, length_bwtLast]
  exact lfDecodeM_bwtLast_time w (fun _ => rfl) _ le_rfl _ (bwtIndex_lt_length w) _
    (by rw [List.rotate_length]; exact getElem_bwtMatrix_bwtIndex w)

end Cslib.Algorithms.Lean.BurrowsWheeler
