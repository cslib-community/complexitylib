/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Universe sizes and a contiguous van Emde Boas layout

At depth `d` the universe has size `2 ^ (2 ^ d)`. A node has a five-word header, with
presence, minimum, maximum, split size and child span at offsets `0` through `4`. At positive
depth, the header is followed by one recursive summary and then one recursive cluster for
each element of the smaller universe. All recursive records are allocated, including empty ones.

This is address arithmetic for the modern minimum-excluded variant described in
[Demaine2015VanEmdeBoas], pp. 4–5. The five-word header and contiguous allocation are choices
of this formalization. The original priority-queue construction is due to van Emde Boas, Kaas
and Zijlstra [VanEmdeBoasKaasZijlstra1977]; we do not identify these layout choices with that
paper's construction. No memory representation or RAM running-time theorem is established here.

## Main definitions

* `universeSize`: the recursively squared universe size.
* `span`: the number of words in the fully allocated recursive record.
* `summaryOffset`, `clusterOffset`: the starts of the recursive records relative to their parent.

## Main results

* `universeSize_eq_two_pow`: the closed form `2 ^ (2 ^ d)`.
* `universeSize_mono`, `span_mono`: monotonicity of `universeSize` and `span` in the depth.
* `span_le`: the explicit linear bound `span d ≤ 10 * universeSize d`.
* `summary_word_lt_span`, `cluster_word_lt_span`: all recursive words lie within their parent.
* `summary_end_le_clusterOffset`, `cluster_end_le_clusterOffset`: recursive records do not overlap.

## References

* [Erik Demaine, *Lecture 4: Divide and Conquer: van Emde Boas Trees*, MIT 6.046J,
  Spring 2015][Demaine2015VanEmdeBoas]
* [Peter van Emde Boas, R. Kaas and E. Zijlstra, *Design and implementation of an efficient
  priority queue*][VanEmdeBoasKaasZijlstra1977]
-/

@[expose] public section

namespace Cslib.Algorithms.Lean.VanEmdeBoas

/-- Size of the depth-`d` universe; each step squares the previous size. -/
def universeSize : ℕ → ℕ
  | 0 => 2
  | d + 1 => universeSize d * universeSize d

/-- The base universe at depth zero has two elements. -/
@[simp] theorem universeSize_zero : universeSize 0 = 2 := rfl

/-- Each additional level of depth squares the universe size. -/
@[simp] theorem universeSize_succ (d : ℕ) :
    universeSize (d + 1) = universeSize d * universeSize d := rfl

/-- Every depth has universe size at least two. -/
theorem two_le_universeSize (d : ℕ) : 2 ≤ universeSize d := by
  induction d with
  | zero => decide
  | succ d ih =>
    rw [universeSize_succ]
    nlinarith

/-- Every depth has positive universe size. -/
theorem universeSize_pos (d : ℕ) : 0 < universeSize d := by
  have := two_le_universeSize d
  omega

/-- Depth counts repeated square roots of the universe size, down to the two-element base. -/
theorem universeSize_eq_two_pow (d : ℕ) : universeSize d = 2 ^ (2 ^ d) := by
  induction d with
  | zero => rfl
  | succ d ih =>
    simp only [universeSize_succ, ih, Nat.pow_succ]
    ring

/-- Number of words in a fully allocated record, including the five-word header. -/
def span : ℕ → ℕ
  | 0 => 5
  | d + 1 => 5 + (universeSize d + 1) * span d

/-- A depth-zero leaf record occupies five header words. -/
@[simp] theorem span_zero : span 0 = 5 := rfl

/-- A depth-`d + 1` record consists of five header words, one summary, and `universeSize d`
clusters of size `span d`. -/
@[simp] theorem span_succ (d : ℕ) :
    span (d + 1) = 5 + (universeSize d + 1) * span d := rfl

/-- Every record occupies at least the five header words. -/
theorem five_le_span (d : ℕ) : 5 ≤ span d := by
  cases d <;> simp [span_succ]

/-- Every record occupies a positive number of words. -/
theorem span_pos (d : ℕ) : 0 < span d := by
  have := five_le_span d
  omega

/-- A strengthened linear bound that leaves enough slack for the recursive header. -/
theorem span_add_fifteen_le (d : ℕ) : span d + 15 ≤ 10 * universeSize d := by
  induction d with
  | zero => decide
  | succ d ih =>
    have hu := two_le_universeSize d
    have h := Nat.mul_le_mul_left (universeSize d + 1) ih
    rw [span_succ, universeSize_succ]
    nlinarith

/-- The fully allocated record occupies at most ten words per universe element. -/
theorem span_le (d : ℕ) : span d ≤ 10 * universeSize d := by
  have := span_add_fifteen_le d
  omega

/-- Relative start of the summary, immediately after the five-word header. -/
def summaryOffset : ℕ := 5

/-- Relative start of cluster `i` in a depth-`d + 1` record. The summary occupies slot zero. -/
def clusterOffset (d i : ℕ) : ℕ := 5 + (i + 1) * span d

/-- Every header word offset lies strictly within the record span. -/
theorem header_word_lt_span (d : ℕ) {h : ℕ} (hh : h < 5) : h < span d :=
  hh.trans_le (five_le_span d)

/-- The entire header precedes every summary word. -/
theorem header_word_lt_summary_word {h : ℕ} (hh : h < 5) (a : ℕ) :
    h < summaryOffset + a := by
  dsimp only [summaryOffset]
  omega

/-- The summary block fits within the parent record's span. -/
theorem summary_end_le_span (d : ℕ) : summaryOffset + span d ≤ span (d + 1) := by
  rw [span_succ]
  dsimp only [summaryOffset]
  nlinarith

/-- Every word of the summary is inside the parent record. -/
theorem summary_word_lt_span (d : ℕ) {a : ℕ} (ha : a < span d) :
    summaryOffset + a < span (d + 1) := by
  have := summary_end_le_span d
  omega

/-- Each valid cluster block fits within the parent record's span. -/
theorem cluster_end_le_span (d : ℕ) {i : ℕ} (hi : i < universeSize d) :
    clusterOffset d i + span d ≤ span (d + 1) := by
  have h := Nat.mul_le_mul_right (span d) (show i + 2 ≤ universeSize d + 1 by omega)
  rw [span_succ]
  dsimp only [clusterOffset]
  nlinarith

/-- Every word of each valid cluster is inside the parent record. -/
theorem cluster_word_lt_span (d : ℕ) {i a : ℕ} (hi : i < universeSize d)
    (ha : a < span d) : clusterOffset d i + a < span (d + 1) := by
  have := cluster_end_le_span d hi
  omega

/-- The summary ends before every cluster starts. -/
theorem summary_end_le_clusterOffset (d i : ℕ) :
    summaryOffset + span d ≤ clusterOffset d i := by
  dsimp only [summaryOffset, clusterOffset]
  nlinarith

/-- Every summary word precedes every cluster word. -/
theorem summary_word_lt_cluster_word (d i b : ℕ) {a : ℕ} (ha : a < span d) :
    summaryOffset + a < clusterOffset d i + b := by
  have := summary_end_le_clusterOffset d i
  omega

/-- Ordered clusters occupy nonoverlapping half-open intervals. -/
theorem cluster_end_le_clusterOffset (d : ℕ) {i j : ℕ} (hij : i < j) :
    clusterOffset d i + span d ≤ clusterOffset d j := by
  have h := Nat.mul_le_mul_right (span d) (show i + 2 ≤ j + 1 by omega)
  dsimp only [clusterOffset]
  nlinarith

/-- Every word of an earlier cluster precedes every word of a later cluster. -/
theorem cluster_word_lt_cluster_word (d : ℕ) {i j a : ℕ} (hij : i < j)
    (ha : a < span d) (b : ℕ) : clusterOffset d i + a < clusterOffset d j + b := by
  have := cluster_end_le_clusterOffset d hij
  omega

/-- Monotonicity of `universeSize` in the recursion depth. -/
theorem universeSize_mono {a b : ℕ} (hab : a ≤ b) : universeSize a ≤ universeSize b := by
  induction hab with
  | refl => exact le_rfl
  | @step m _ ih =>
    rw [universeSize_succ]
    have hpos := two_le_universeSize m
    nlinarith

/-- Monotonicity of `span` in the recursion depth. -/
theorem span_mono {a b : ℕ} (hab : a ≤ b) : span a ≤ span b := by
  induction hab with
  | refl => exact le_rfl
  | @step m _ ih =>
    refine ih.trans (show span m ≤ span (m + 1) by
      have h := summary_end_le_span m
      dsimp only [summaryOffset] at h
      omega)

end Cslib.Algorithms.Lean.VanEmdeBoas
