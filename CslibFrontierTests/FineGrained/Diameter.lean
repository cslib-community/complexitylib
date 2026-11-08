/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Complexity.FineGrained.Diameter

/-!
# Tests: orthogonal vectors hardness of diameter two versus three

The graph of the reduction on concrete instances: its vertices and edges on one vector per list,
on the instance with no vectors, and on vectors of different lengths; its diameter, three on an
orthogonal pair and two on a non-orthogonal pair and on the empty instance; the parser on an
encoded instance; and the separating set of the corollaries.
-/

namespace ComplexityTests.FineGrained.Diameter

open Cslib.Complexity Cslib.Complexity.OV

/-- One vector per list, `[true, false]` and `[false, true]`, an orthogonal pair. -/
private def p₁ : List (List Bool) × List (List Bool) := ([[true, false]], [[false, true]])

/-- One vector per list, `[true, true]` and `[false, true]`, sharing the coordinate `1`. -/
private def p₂ : List (List Bool) × List (List Bool) := ([[true, true]], [[false, true]])

/-! ### The graph -/

/-- The coordinates `0 ↦ 4` and `1 ↦ 6`, the vectors `0 ↦ 5` and `1 ↦ 7`, and the constants. -/
example : toDiameter p₁ =
    ([4, 6, 5, 4, 6, 7, 0, 1, 2, 3],
      [(0, 4), (1, 4), (4, 5), (0, 6), (1, 6), (0, 5),
        (0, 4), (1, 4), (0, 6), (1, 6), (6, 7), (1, 7),
        (0, 1), (0, 2), (0, 3), (1, 2), (1, 3)]) := rfl

/-- The instance with no vectors: the hubs and the padding vertices. -/
example : toDiameter ([], []) =
    ([0, 1, 2, 3], [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3)]) := rfl

/-- The parser emits the same vertices on the encoded instance. -/
example : parseRun Diameter.bitVertices Diameter.endVertices ((((false, false), false), 0), 0)
    (encOV p₁) ++ Diameter.constVertices = (toDiameter p₁).1 := by decide

/-! ### The diameter -/

/-- An orthogonal pair: diameter three. -/
example : (toDiameter p₁).induced.ediam = 3 := by
  have h : p₁ ∈ OV := ⟨[true, false], List.mem_singleton_self _, [false, true],
    List.mem_singleton_self _, fun i => by
      rcases i with _ | _ | i <;> simp⟩
  simp only [ediam_toDiameter, h, ↓reduceIte]

/-- A non-orthogonal pair: diameter two. -/
example : (toDiameter p₂).induced.ediam = 2 := by
  have h : p₂ ∉ OV := by
    rintro ⟨a, ha, b, hb, h⟩
    simp only [p₂, List.mem_singleton] at ha hb
    subst ha hb
    rcases h 1 with h | h <;> simp at h
  simp only [ediam_toDiameter, h, ↓reduceIte]

/-- The instance with no vectors has diameter two, thanks to the padding vertices. -/
example : (toDiameter ([], [])).induced.ediam = 2 := by
  have h : (([], []) : List (List Bool) × List (List Bool)) ∉ OV := by
    rintro ⟨a, ha, -⟩
    simp at ha
  simp only [ediam_toDiameter, h, ↓reduceIte]

/-- Vectors of different lengths are padded with `false`: `[true]` and `[false, true]` are
orthogonal, so the diameter is three. -/
example : (toDiameter ([[true]], [[false, true]])).induced.ediam = 3 := by
  have h : (([[true]], [[false, true]]) : List (List Bool) × List (List Bool)) ∈ OV :=
    ⟨[true], List.mem_singleton_self _, [false, true], List.mem_singleton_self _, fun i => by
      rcases i with _ | _ | i <;> simp⟩
  simp only [ediam_toDiameter, h, ↓reduceIte]

/-! ### The conditional lower bound -/

/-- The set of graphs of diameter at most two separates diameter two from diameter three. -/
example : (∀ G : Graph, G.induced.ediam ≤ 2 → G ∈ {G : Graph | G.induced.ediam ≤ 2}) ∧
    (∀ G : Graph, G.induced.ediam = 3 → G ∉ {G : Graph | G.induced.ediam ≤ 2}) :=
  ⟨fun _ h => h, fun G h hG => by
    have h₂ : G.induced.ediam ≤ 2 := hG
    rw [h] at h₂
    exact absurd h₂ (by decide)⟩

/-- Under `OVH`, the size form excludes deciders within time `(n + m) ^ 1.5 + L`. -/
example (h : OVH) : ¬DecidableInTimeO {G : Graph | G.induced.ediam ≤ 2} encGraph
    fun G => ((G.1.length + G.2.length : ℕ) : ℝ) ^ (2 - (1 / 2 : ℝ)) + (encGraph G).length :=
  not_decidableInTimeO_diameter_size_of_OVH h (by norm_num) (fun _ h => h) fun G h hG => by
    have h₂ : G.induced.ediam ≤ 2 := hG
    rw [h] at h₂
    exact absurd h₂ (by decide)

end ComplexityTests.FineGrained.Diameter
