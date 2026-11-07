/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.PCP.Approximation.ParitySearch

/-! # Searching a three-wise independent sample space for MAX-SAT: checked examples

For three variables the sample space is the whole cube, so the search is exact; on the eight
clauses with all sign patterns on three variables every assignment falsifies one clause and the
`7 / 8` guarantee is tight. For four variables the eight points of the sample space are the
assignments with an even number of `true` values: the bits are not four-wise independent, and on
the eight four-literal clauses falsified by exactly these assignments every point falsifies one
clause, so the `1 - 2 ^ -4` bound fails although an odd assignment satisfies every clause. The
hypothesis `k ≤ 3` cannot be dropped. An empty clause defeats the `1 / 2` bound without its
hypothesis. The polynomial-time theorems are instantiated at these formulas.
-/

namespace ComplexityTests.ParitySearchMaxSAT

open Cslib Cslib.Logic.PL Cslib.Complexity Cslib.Probability Turing.MultiTapeTM

/-! ### The sample space -/

-- Three variables: `2 ^ (⌈log₂ 3⌉ + 1) = 8` points, all of the cube.
example : parityCandidates [0, 1, 2] =
    [[], [0, 1, 2], [1], [0, 2], [2], [0, 1], [1, 2], [0]] := by decide

-- Four variables: still `8 < 16` points, the assignments with an even number of `true` values.
example : parityCandidates [0, 1, 2, 3] =
    [[], [0, 1, 2, 3], [1, 3], [0, 2], [2, 3], [0, 1], [1, 2], [0, 3]] := by decide
example : (parityCandidates [0, 1, 2, 3]).length < 4 * [0, 1, 2, 3].length := by decide

-- No variables: the two seeds of one bit give the empty assignment.
example : parityCandidates ([] : List ℕ) = [[], []] := by decide

-- The sample bits on two-bit positions are not four-wise independent: the four values always
-- have even parity, so no seed makes exactly one of them `true`.
example : ¬ IsKWiseIndependentHash 4
    (fun (t : BitString 3) (x : BitString 2) => t ⬝ᵥ Fin.cons true x) := by
  intro hh
  have key : ∀ t : BitString 3, ∃ x : BitString 2, t ⬝ᵥ Fin.cons true x ≠ decide (x = 0) := by
    decide
  have hempty : ({t | Finset.univ.restrict (fun x : BitString 2 => t ⬝ᵥ Fin.cons true x) =
      fun x => decide (x.1 = 0)} : Finset (BitString 3)) = ∅ := by
    refine Finset.filter_eq_empty_iff.2 fun t _ ht => ?_
    obtain ⟨x, hx⟩ := key t
    exact hx (congrFun ht ⟨x, Finset.mem_univ x⟩)
  have h := hh.dens_filter_restrict_eq (T := Finset.univ) (by simp) fun x => decide (x.1 = 0)
  rw [hempty, Finset.dens_empty] at h
  norm_num at h

/-! ### The search -/

/-- All eight sign patterns on three variables: every assignment falsifies exactly one clause. -/
def allSigns : CNF ℕ :=
  [[(0, true), (1, true), (2, true)], [(0, true), (1, true), (2, false)],
    [(0, true), (1, false), (2, true)], [(0, true), (1, false), (2, false)],
    [(0, false), (1, true), (2, true)], [(0, false), (1, true), (2, false)],
    [(0, false), (1, false), (2, true)], [(0, false), (1, false), (2, false)]]

example : allSigns.IsExactThreeDistinct := by decide

-- Every candidate ties with the starting all-`false` assignment, and the `7 / 8` bound is tight.
example : paritySearch allSigns = [] := by decide
example : allSigns.countUnsat (paritySearchAssignment allSigns) = 1 := by decide
example : 8 * allSigns.countUnsat (paritySearchAssignment allSigns) ≤ allSigns.length :=
  CNF.IsExactThreeDistinct.eight_mul_countUnsat_paritySearchAssignment_le (by decide)

-- A strict improvement is found: the unit clause `x₁` is falsified by the starting assignment.
example : paritySearch ([[(0, false), (1, true)], [(1, true)]] : CNF ℕ) = [0, 1] := by decide
example : CNF.countUnsat (paritySearchAssignment ([[(0, false), (1, true)], [(1, true)]] : CNF ℕ))
    [[(0, false), (1, true)], [(1, true)]] = 0 := by decide

/-- The eight four-literal clauses falsified by the assignments with an even number of `true`
values. -/
def evenFalse : CNF ℕ :=
  [[(0, true), (1, true), (2, true), (3, true)],
    [(0, false), (1, false), (2, true), (3, true)],
    [(0, false), (1, true), (2, false), (3, true)],
    [(0, false), (1, true), (2, true), (3, false)],
    [(0, true), (1, false), (2, false), (3, true)],
    [(0, true), (1, false), (2, true), (3, false)],
    [(0, true), (1, true), (2, false), (3, false)],
    [(0, false), (1, false), (2, false), (3, false)]]

-- Every clause has four distinct literals, yet every point of the sample space falsifies a
-- clause, so the bound `2 ^ 4 * countUnsat ≤ length` fails; an odd assignment falsifies none.
example : ∀ c ∈ evenFalse, 4 ≤ c.toFinset.card := by decide
example : ∀ T ∈ parityCandidates evenFalse.distinctVars,
    evenFalse.countUnsat (fun v => decide (v ∈ T)) = 1 := by decide
example : ¬ 2 ^ 4 * evenFalse.countUnsat (paritySearchAssignment evenFalse) ≤ evenFalse.length := by
  decide
example : evenFalse.countUnsat (fun v => decide (v ∈ [0])) = 0 := by decide

-- An empty clause is falsified by every assignment: the `1 / 2` bound `2 * 1 ≤ 1` fails, so the
-- hypothesis that no clause is empty cannot be dropped.
example : CNF.countUnsat (paritySearchAssignment ([[]] : CNF ℕ)) [[]] = 1 := by decide
example : ¬ 2 * CNF.countUnsat (paritySearchAssignment ([[]] : CNF ℕ)) [[]] ≤
    ([[]] : CNF ℕ).length := by
  decide

/-! ### Polynomial time -/

-- The oblivious `7 / 8` assignments, applied to `allSigns` on its three variables.
example : ∃ S : List ℕ → List (List ℕ),
    ComputableInPolyTime S (encList encNat) (encList (encList encNat)) ∧
    (S [0, 1, 2]).length < 12 ∧
    ∃ T ∈ S [0, 1, 2], 8 * allSigns.countUnsat (fun v => decide (v ∈ T)) ≤ allSigns.length := by
  obtain ⟨S, hS, hlen, hspec⟩ := exists_polyTime_oblivious_maxExactThreeSAT_assignments
  exact ⟨S, hS, hlen [0, 1, 2] (by decide), hspec [0, 1, 2] allSigns (by decide) (by decide)⟩

-- The search itself, on `encCNF`.
example : ComputableInPolyTime (paritySearch (V := ℕ)) encCNF (encList encNat) :=
  computableInPolyTime_paritySearch_encCNF

end ComplexityTests.ParitySearchMaxSAT
