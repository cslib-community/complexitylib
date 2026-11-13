/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Complexity.Problems.ChromaticNumber
import CslibFrontier.Computability.Complexity.Problems.Graph.VertexColors

/-!
# Chromatic number: tests

Colorability of small graphs with the number of colors in the instance, including a number of
colors far beyond the number of vertices and the boundary `k = 0`, reading colors from a list,
the bridge to `SimpleGraph.chromaticNumber`, and the headline results.
-/

namespace CslibFrontierTests.ChromaticNumber

open Cslib.Complexity Turing.MultiTapeTM

private def triangle : Graph := ⟨[0, 1, 2], [(0, 1), (1, 2), (2, 0)]⟩

/-! ### Headline results -/

example : ChromaticNumber ∈ NP encChromaticNumber ∧
    NPHard encChromaticNumber ChromaticNumber ∧
    PolyTimeReducible encGraph encChromaticNumber (KColoring 4) ChromaticNumber :=
  ⟨ChromaticNumber_npComplete.1, ChromaticNumber_npComplete.2,
    polyTimeReducible_KColoring_ChromaticNumber 4⟩

/-! ### Colorability -/

-- The triangle is 3-colorable but not 2-colorable.
example : (⟨triangle, 3⟩ : ChromaticNumberInstance) ∈ ChromaticNumber := by
  rw [mem_ChromaticNumber_iff, mem_KColoring_iff]
  exact ⟨id, by decide, fun u _ v _ huv => huv.ne⟩

example : (⟨triangle, 2⟩ : ChromaticNumberInstance) ∉ ChromaticNumber := by
  rw [mem_ChromaticNumber_iff, mem_KColoring_iff]
  rintro ⟨c, hc, hadj⟩
  have h₀ := hc 0 (by decide)
  have h₁ := hc 1 (by decide)
  have h₂ := hc 2 (by decide)
  have h₀₁ := hadj 0 (by decide) 1 (by decide) ((Graph.adjBool_eq_true_iff _ _ _).1 rfl)
  have h₁₂ := hadj 1 (by decide) 2 (by decide) ((Graph.adjBool_eq_true_iff _ _ _).1 rfl)
  have h₂₀ := hadj 2 (by decide) 0 (by decide) ((Graph.adjBool_eq_true_iff _ _ _).1 rfl)
  omega

-- A number of colors far beyond the number of vertices.
example : (⟨triangle, 2 ^ 64⟩ : ChromaticNumberInstance) ∈ ChromaticNumber := by
  rw [mem_ChromaticNumber_iff, mem_KColoring_iff]
  exact ⟨id, by decide, fun u _ v _ huv => huv.ne⟩

-- Without colors, exactly the graphs without declared vertices are colorable.
example : (⟨⟨([] : List ℕ), [(0, 1)]⟩, 0⟩ : ChromaticNumberInstance) ∈ ChromaticNumber := by
  rw [mem_ChromaticNumber_iff, mem_KColoring_iff]
  exact ⟨id, by simp, by simp⟩

example : (⟨⟨([5] : List ℕ), []⟩, 0⟩ : ChromaticNumberInstance) ∉ ChromaticNumber := by
  rw [mem_ChromaticNumber_iff, mem_KColoring_iff]
  rintro ⟨c, hc, -⟩
  exact Nat.not_lt_zero _ (hc 5 (by simp))

-- The chromatic number of the graph of the declared vertices, in Mathlib's sense.
example : triangle.induced.chromaticNumber ≤ 3 :=
  mem_ChromaticNumber_iff_chromaticNumber_le.1 (by
    rw [mem_ChromaticNumber_iff, mem_KColoring_iff]
    exact ⟨id, by decide, fun u _ v _ huv => huv.ne⟩)

/-! ### Witnesses -/

-- A color is read at the first occurrence of a vertex, with `0` past the end of the list.
example : colorOf ⟨[5, 7, 5], []⟩ [2, 0, 1] 5 = 2 ∧ colorOf ⟨[5, 7, 5], []⟩ [2, 0, 1] 7 = 0 ∧
    colorOf ⟨[5, 7], []⟩ [2] 7 = 0 ∧ colorOf ⟨[5, 7], []⟩ [2, 3] 9 = 0 :=
  ⟨rfl, rfl, rfl, rfl⟩

example : colorOf ⟨[5, 7], []⟩ ([5, 7].map fun v => v + 1) 7 = 8 :=
  colorOf_map (G := ⟨[5, 7], []⟩) (by simp)

-- Compositional `fun_prop` synthesis for colors read from computed lists.
example : ComputableInPolyTime (fun p : (Graph × List ℕ) × ℕ => colorOf p.1.1 p.1.2 0)
    (encPair (encPair encGraph (encList encNat)) encNat) encNat := by
  fun_prop

-- Global `fun_prop` synthesis for `encChromaticNumber` projections and constructor.
example : ComputableInPolyTime (fun x : ChromaticNumberInstance => x.graph)
    encChromaticNumber encGraph := by
  fun_prop

example : ComputableInPolyTime (fun x : ChromaticNumberInstance => x.colors)
    encChromaticNumber encNat := by
  fun_prop

example : ComputableInPolyTime (fun p : Graph × ℕ => (⟨p.1, p.2⟩ : ChromaticNumberInstance))
    (encPair encGraph encNat) encChromaticNumber := by
  fun_prop

end CslibFrontierTests.ChromaticNumber
