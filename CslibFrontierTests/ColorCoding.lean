/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Complexity.Parameterized.Clique
import CslibFrontier.Computability.Complexity.Parameterized.ColorCoding

/-!
# Tests: color coding and k-Path

Concrete instances of `LongPath` and `ColorfulPath` on the path `0 - 1 - 2 - 3`: the color-coding
decider accepts a colorful coloring and rejects a coloring with repeated colors, both evaluated by
`decide`; edge cases `k = 0`, `k` above the number of vertices, and colors at least `k`; and the
resource consequences: an exponent at least `1`, and `FPT` for a larger parameter.
-/

namespace CslibFrontierTests.ColorCoding

open Cslib.Complexity Turing.MultiTapeTM

/-- The path `0 - 1 - 2 - 3`. -/
def P4 : Graph := ⟨[0, 1, 2, 3], [(0, 1), (1, 2), (2, 3)]⟩

/-! ### k-Path -/

example : P4.IsVertexPath [0, 1, 2, 3] :=
  ⟨by decide, by decide, by
    simp only [List.isChain_cons_cons, List.isChain_singleton, and_true,
      ← Graph.adjBool_eq_true_iff]
    decide⟩

example : (⟨P4, 4⟩ : LongPathInstance) ∈ LongPath :=
  ⟨[0, 1, 2, 3], ⟨by decide, by decide, by
    simp only [List.isChain_cons_cons, List.isChain_singleton, and_true,
      ← Graph.adjBool_eq_true_iff]
    decide⟩, rfl⟩

-- `0 - 2` is not an edge.
example : ¬P4.IsVertexPath [0, 2] := fun ⟨_, _, h⟩ => by
  rw [List.isChain_pair, ← Graph.adjBool_eq_true_iff] at h
  exact absurd h (by decide)

example : (⟨P4, 0⟩ : LongPathInstance) ∈ LongPath := mem_LongPath_zero P4

example : (⟨P4, 5⟩ : LongPathInstance) ∉ LongPath := not_mem_LongPath_of_lt (by decide)

/-! ### Colorful paths, decided by the dynamic programming -/

-- A colorful coloring: the whole path is a colorful path on four vertices.
example : colorfulPathBool ⟨P4, [0, 1, 2, 3], 4⟩ = true := by decide

example : (⟨P4, [0, 1, 2, 3], 4⟩ : ColorfulPathInstance) ∈ ColorfulPath :=
  (colorfulPathBool_eq_true_iff _).1 (by decide)

-- Two alternating colors: no colorful path on four vertices, but one on two.
example : (⟨P4, [0, 1, 0, 1], 4⟩ : ColorfulPathInstance) ∉ ColorfulPath := fun h => by
  have := (colorfulPathBool_eq_true_iff _).2 h
  revert this
  decide

example : (⟨P4, [0, 1, 0, 1], 2⟩ : ColorfulPathInstance) ∈ ColorfulPath :=
  (colorfulPathBool_eq_true_iff _).1 (by decide)

-- `1 - 2 - 3` is colorful with colors `{0, 1, 2}`, although `0` and `3` share a color.
example : (⟨P4, [0, 1, 2, 0], 3⟩ : ColorfulPathInstance) ∈ ColorfulPath :=
  (colorfulPathBool_eq_true_iff _).1 (by decide)

-- A vertex off the path may have a color at least `k`: `0 - 1 - 2` is a solution for `k = 3`.
example : (⟨P4, [0, 1, 2, 7], 3⟩ : ColorfulPathInstance) ∈ ColorfulPath :=
  (colorfulPathBool_eq_true_iff _).1 (by decide)

-- Colors must be less than `k`: four distinct colors that are not `{0, 1, 2, 3}` are rejected.
example : (⟨P4, [1, 2, 3, 4], 4⟩ : ColorfulPathInstance) ∉ ColorfulPath := fun h => by
  have := (colorfulPathBool_eq_true_iff _).2 h
  revert this
  decide

-- `k = 0` is accepted by the empty path; `k` above the number of vertices is rejected.
example : (⟨P4, [], 0⟩ : ColorfulPathInstance) ∈ ColorfulPath :=
  (colorfulPathBool_eq_true_iff _).1 (by decide)

example : (⟨P4, [0, 1, 2, 3, 4], 5⟩ : ColorfulPathInstance) ∉ ColorfulPath := fun h => by
  have := (colorfulPathBool_eq_true_iff _).2 h
  revert this
  decide

-- The table entries are the endpoints of colorful paths with the given color set: with colors
-- `[0, 1, 2, 3]`, color set `{0, 1} = 3` is reached at `0` and `1`, and `{0, 2} = 5` nowhere.
example : (ColorCoding.table P4 (colorOf P4 [0, 1, 2, 3]) 16).getD 3 [] = [0, 1] := by decide
example : (ColorCoding.table P4 (colorOf P4 [0, 1, 2, 3]) 16).getD 5 [] = [] := by decide

example : ColorCoding.Reaches P4 (colorOf P4 [0, 1, 2, 3]) 15 3 :=
  (ColorCoding.mem_table_getD (by decide : 15 < 16)).1 (by decide)

/-! ### Resource consequences -/

-- The exponent can be taken at least `1`.
example : ∃ δ : ℝ, 1 ≤ δ ∧ DecidableInExpTime ColorfulPath
    encColorfulPathInstance ColorfulPathInstance.length δ :=
  let ⟨δ, h⟩ := ColorfulPath_decidableInExpTime
  ⟨max δ 1, le_max_right _ _, h.mono (le_max_left _ _)⟩

-- Fixed-parameter tractable also for a larger parameter: `k` plus the number of listed colors.
example : ColorfulPath ∈
    FPT encColorfulPathInstance fun x => x.length + x.colors.length :=
  FPT_subset_FPT_of_le_comp (h := id) (fun _ => Nat.le_add_right _ _) ColorfulPath_mem_FPT

/-! ### Clique and Independent Set -/

example : FPTReducible encCliqueInstance encIndependentSetInstance (·.m) (·.m)
    Clique IndependentSet :=
  fptReducible_Clique_IndependentSet

-- `Clique` and `IndependentSet` stand or fall together in `FPT`.
example (h : IndependentSet ∈ FPT encIndependentSetInstance (·.m)) :
    Clique ∈ FPT encCliqueInstance (·.m) :=
  Clique_mem_FPT_iff.2 h

-- Compositional `fun_prop` clients using the `enc_structure`-generated rules and
-- `Cslib.Complexity.ColorCoding` scope.
example : ComputableInPolyTime (fun x : ColorfulPathInstance => x.length)
    encColorfulPathInstance encNat := by
  fun_prop

example : ComputableInPolyTime
    (fun x : ColorfulPathInstance × ℕ => (⟨x.1.graph, x.1.colors, x.2⟩ : ColorfulPathInstance))
    (encPair encColorfulPathInstance encNat) encColorfulPathInstance := by
  fun_prop

open scoped Cslib.Complexity.ColorCoding in
example : ComputableInPolyTime
    (fun x : ColorCoding.StepInput =>
      (⟨⟨x.input.graph, x.input.colors, x.input.numSets⟩, x.table, x.mask⟩ :
        ColorCoding.StepInput))
    ColorCoding.encStepInput ColorCoding.encStepInput := by
  fun_prop

open scoped Cslib.Complexity.ColorCoding in
example : ComputableInPolyTime
    (fun x : ColorfulPathInstance × ℕ =>
      ColorCoding.table x.1.graph (colorOf x.1.graph x.1.colors) x.2)
    (encPair encColorfulPathInstance encUnary) ColorCoding.encTable := by
  have ht : ComputableInPolyTime
      (fun x : ColorfulPathInstance × ℕ =>
        (⟨x.1.graph, x.1.colors, x.2⟩ : ColorCoding.TableInput))
      (encPair encColorfulPathInstance encUnary) ColorCoding.encTableInput := by
    fun_prop
  change ComputableInPolyTime
    (fun x : ColorfulPathInstance × ℕ =>
      (fun y : ColorCoding.TableInput =>
        ColorCoding.table y.graph (colorOf y.graph y.colors) y.numSets)
        ⟨x.1.graph, x.1.colors, x.2⟩)
    _ _
  exact ColorCoding.computableInPolyTime_table.comp ht

end CslibFrontierTests.ColorCoding
