/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import CslibFrontier.Cryptanalysis.AddXNORWidth

/-!
# Actual Add/XNOR reduction clients

The concrete output checks include both gadget choices, a mixed-pattern guard
failure, zero source numbers, repeated numbers, empty input, out-of-range
rejection, large variable labels, and the rational-width padding construction.
-/

open Cslib.Cryptanalysis.AddXNOR Cslib.Complexity

example : toAddXNOR ([1], 1) = (8, [5, 12, 52, 12, 52, 0, 0, 123]) := by decide

example : toAddXNOR ([0, 1, 0], 1) = toAddXNOR ([1], 1) := by decide

example : toAddXNOR ([1], 2) = (2, [1, 0]) := by decide

example : eval (List.replicate 7 (false, (0 : BitVec 8))) 1#8 = 1#8 := by decide

/-- Select the item by four additions, then add zeros and the correction. -/
example : eval
    [(false, 12#8), (false, 52#8), (false, 12#8), (false, 52#8),
      (false, 0#8), (false, 0#8), (false, 123#8)] 5#8 = 0#8 := by decide

/-- Omit the item by four XNORs and use the target-zero correction. -/
example : eval
    [(true, 12#8), (true, 52#8), (true, 12#8), (true, 52#8),
      (false, 0#8), (false, 0#8), (false, 251#8)] 5#8 = 0#8 := by decide

/-- A mixed block fails on actual full-width operands, not just a supplied guard table. -/
example : (normalize (xnorParity (fourSteps true false true false 12#8 52#8))
    (eval (fourSteps true false true false 12#8 52#8) 5#8)).extractLsb' 2 4 ≠ 1#4 := by
  decide

example : toAddXNOR ([1], 1) ∈ Decision :=
  (toAddXNOR_mem_iff _).2 ⟨([1] : Multiset ℕ), le_rfl, rfl⟩

/-- Repeated values still represent distinct selectable source positions. -/
example : toAddXNOR ([1, 1], 1) ∈ Decision :=
  (toAddXNOR_mem_iff _).2 ⟨([1] : Multiset ℕ), by decide, rfl⟩

example : toAddXNOR ([], 0) ∈ Decision :=
  (toAddXNOR_mem_iff _).2 ⟨0, le_rfl, rfl⟩

example : toAddXNOR ([1], 2) ∉ Decision := by
  intro h
  obtain ⟨chosen, hc, hs⟩ := mem_SubsetSum_iff_sublist.1 ((toAddXNOR_mem_iff _).1 h)
  have hsum := hc.sum_le_sum (fun _ _ => Nat.zero_le _)
  simp only [List.sum_cons, List.sum_nil] at hsum
  omega

example : (threeSATToAddXNOR [[(17, true)]]).1 = 24 := by decide

example : (toPowerAddXNOR 1 2 ([1], 1)).1 = 8 ∧
    (toPowerAddXNOR 1 2 ([1], 1)).2.length = 64 := by decide

example : toPowerAddXNOR 1 2 ([1], 1) ∈ PowerDecision 1 2 :=
  (toPowerAddXNOR_mem_iff 1 2 (by decide) (by decide) _).2
    ⟨([1] : Multiset ℕ), le_rfl, rfl⟩

/-- The two-parameter verifier includes the source's width-one edge case. -/
example : (1, [0, 0]) ∈ WordDecision := by
  refine ⟨by decide, by decide, ?_, [false], rfl, ?_⟩
  · intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl <;> decide
  · decide

example : powerShape 1 2 (1, [0, 0]) = false := by decide

/-- Every positive rational is quantified, with the literal real-power ceiling. -/
example (δ : ℚ) (hδ : 0 < δ) :
    NPComplete encInstance {p : ℕ × List ℕ |
      p.1 = ⌈(p.2.length : ℝ) ^ (δ : ℝ)⌉₊ ∧ p ∈ WordDecision} :=
  rational_width_npComplete δ hδ

example (φ : Cslib.Logic.PL.CNF ℕ) :
    (threeSATToAddXNOR φ).1 ≤ 13 * (φ.distinctVars.length + φ.length) + 3 :=
  threeSATToAddXNOR_width_le φ

/-- A genuine 3-SAT instance, with a non-dense variable label, maps to yes. -/
example : threeSATToAddXNOR [[(17, true)]] ∈ Decision := by
  apply (threeSATToAddXNOR_mem_iff _).2
  refine ⟨?_, fun _ => true, ?_⟩
  · intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    subst c
    decide
  · decide
