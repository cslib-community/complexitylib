/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import CslibFrontier.Probability.StochasticOracle.PartialCoverHardness
import Mathlib.Tactic

/-!
# Set Cover hardness of one-turn partial-cover selection: checked clients

A three-element, three-oracle table checks that the actual retention law succeeds
with probability one for a covering batch (also with repeated calls) and zero for a
non-covering batch, that these oracles satisfy Theorem 4's guarantee with `p = 1`,
and that the reduction's readback, token bill and optimum agree with Set Cover.
The final example is the consumer-facing hardness statement.
-/

open Cslib.Complexity Cslib.Probability.StochasticOracle.PartialCover.Hardness
open Turing.MultiTapeTM

private def S : SetSystem := ⟨[1, 2, 3], [[1, 2], [2, 3], [3]]⟩

private def x : Selection := ofSetSystem S

/-- Calling oracles `0` and `1` once each certifies a cover. -/
example : x.success [1, 1, 0] = 1 := by
  suffices h : x.Covers [1, 1, 0] by simp [x.success_eq, h]
  intro e he
  simp only [x, ofSetSystem, S, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl
  · exact ⟨⟨0, by decide⟩, by decide, by decide⟩
  · exact ⟨⟨0, by decide⟩, by decide, by decide⟩
  · exact ⟨⟨1, by decide⟩, by decide, by decide⟩

/-- Repeated calls to a single oracle that misses element `3` never succeed. -/
example : x.success [5, 0, 0] = 0 := by
  suffices h : ¬ x.Covers [5, 0, 0] by simp [x.success_eq, h]
  intro h
  obtain ⟨i, hi, h3⟩ := h 3 (by decide)
  fin_cases i <;> simp_all [x, ofSetSystem, S]

/-- Repeated calls cost every call: five calls to oracle `0` plus two to oracle `2`. -/
example : x.tokens [5, 0, 2] = 7 := by decide

/-- The readback keeps exactly the oracles with positive call counts. -/
example : queried S [5, 0, 2] = [0, 2] := by decide

/-- These deterministic oracles satisfy Theorem 4's conditional guarantee with `p = 1`. -/
example (ζ : List ℕ) : (x.inst).Admissible x.rho 1 (x.kernel ζ) [] ∅ (x.eligible ζ) :=
  x.admissible ζ

/-- The reduction preserves the optimum exactly. -/
example : x.optTokens = S.optCoverSize :=
  optTokens_ofSetSystem S ⟨Finset.univ, by
    intro u hu
    simp only [S, List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl
    · exact ⟨⟨0, by decide⟩, Finset.mem_univ _, by decide⟩
    · exact ⟨⟨0, by decide⟩, Finset.mem_univ _, by decide⟩
    · exact ⟨⟨1, by decide⟩, Finset.mem_univ _, by decide⟩⟩

/-- Consumer form: no polynomial-time `100`-approximation unless `P = NP`. -/
example {A : Selection → List ℕ} (hA : ComputableInPolyTime A encSelection (encList encNat))
    (happrox : minSelection.IsApprox (fun _ => 100) A) : P encNat = NP encNat :=
  P_eq_NP_of_selection_approx_const (by norm_num) hA happrox encNat
