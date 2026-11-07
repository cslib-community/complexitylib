/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Parameterized.Clique
import Complexity.Computability.Complexity.Parameterized.ColorCoding

/-!
# Tests: color coding and k-Path

Concrete instances of `LongPath` and `ColorfulPath` on the path `0 - 1 - 2 - 3`: the color-coding
decider accepts a colorful coloring and rejects a coloring with repeated colors, both evaluated by
`decide`; edge cases `k = 0`, `k` above the number of vertices, and colors at least `k`; and the
headline results with their encodings and parameters.
-/

namespace ComplexityTests.ColorCoding

open Cslib.Complexity Turing.MultiTapeTM

/-- The path `0 - 1 - 2 - 3`. -/
def P4 : Graph := ([0, 1, 2, 3], [(0, 1), (1, 2), (2, 3)])

/-! ### k-Path -/

example : P4.IsVertexPath [0, 1, 2, 3] :=
  ⟨by decide, by decide, by
    simp only [List.isChain_cons_cons, List.isChain_singleton, and_true,
      ← Graph.adjBool_eq_true_iff]
    decide⟩

example : (P4, 4) ∈ LongPath :=
  ⟨[0, 1, 2, 3], ⟨by decide, by decide, by
    simp only [List.isChain_cons_cons, List.isChain_singleton, and_true,
      ← Graph.adjBool_eq_true_iff]
    decide⟩, rfl⟩

-- `0 - 2` is not an edge.
example : ¬P4.IsVertexPath [0, 2] := fun ⟨_, _, h⟩ => by
  rw [List.isChain_pair, ← Graph.adjBool_eq_true_iff] at h
  exact absurd h (by decide)

example : (P4, 0) ∈ LongPath := mem_LongPath_zero P4

example : (P4, 5) ∉ LongPath := not_mem_LongPath_of_lt (by decide)

/-! ### Colorful paths, decided by the dynamic programming -/

-- A colorful coloring: the whole path is a colorful path on four vertices.
example : colorfulPathBool ((P4, [0, 1, 2, 3]), 4) = true := by decide

example : ((P4, [0, 1, 2, 3]), 4) ∈ ColorfulPath :=
  (colorfulPathBool_eq_true_iff _).1 (by decide)

-- Two alternating colors: no colorful path on four vertices, but one on two.
example : ((P4, [0, 1, 0, 1]), 4) ∉ ColorfulPath := fun h => by
  have := (colorfulPathBool_eq_true_iff _).2 h
  revert this
  decide

example : ((P4, [0, 1, 0, 1]), 2) ∈ ColorfulPath :=
  (colorfulPathBool_eq_true_iff _).1 (by decide)

-- `1 - 2 - 3` is colorful with colors `{0, 1, 2}`, although `0` and `3` share a color.
example : ((P4, [0, 1, 2, 0]), 3) ∈ ColorfulPath :=
  (colorfulPathBool_eq_true_iff _).1 (by decide)

-- Colors must be less than `k`: four distinct colors that are not `{0, 1, 2, 3}` are rejected.
example : ((P4, [1, 2, 3, 4]), 4) ∉ ColorfulPath := fun h => by
  have := (colorfulPathBool_eq_true_iff _).2 h
  revert this
  decide

-- `k = 0` is accepted by the empty path; `k` above the number of vertices is rejected.
example : ((P4, []), 0) ∈ ColorfulPath := (colorfulPathBool_eq_true_iff _).1 (by decide)

example : ((P4, [0, 1, 2, 3, 4]), 5) ∉ ColorfulPath := fun h => by
  have := (colorfulPathBool_eq_true_iff _).2 h
  revert this
  decide

-- The table entries are the endpoints of colorful paths with the given color set: with colors
-- `[0, 1, 2, 3]`, color set `{0, 1} = 3` is reached at `0` and `1`, and `{0, 2} = 5` nowhere.
example : (ColorCoding.table P4 (colorOf P4 [0, 1, 2, 3]) 16).getD 3 [] = [0, 1] := by decide
example : (ColorCoding.table P4 (colorOf P4 [0, 1, 2, 3]) 16).getD 5 [] = [] := by decide

example : ColorCoding.Reaches P4 (colorOf P4 [0, 1, 2, 3]) 15 3 :=
  (ColorCoding.mem_table_getD (by decide : 15 < 16)).1 (by decide)

/-! ### Headline results -/

example : ∃ δ : ℝ, DecidableInExpTime ColorfulPath
    (encPair (encPair encGraph (encList encNat)) encNat) Prod.snd δ :=
  ColorfulPath_decidableInExpTime

example : ColorfulPath ∈ FPT (encPair (encPair encGraph (encList encNat)) encNat) Prod.snd :=
  ColorfulPath_mem_FPT

example : ComputableInPolyTime
    (fun x : (Graph × List ℕ) × ℕ => ColorCoding.table x.1.1 (colorOf x.1.1 x.1.2) x.2)
    (encPair (encPair encGraph (encList encNat)) encUnary) (encList (encList encNat)) :=
  ColorCoding.computableInPolyTime_table

/-! ### Clique and Independent Set -/

example : FPTReducible (encPair encGraph encNat) (encPair encGraph encNat) Prod.snd Prod.snd
    Clique IndependentSet :=
  fptReducible_Clique_IndependentSet

-- `Clique` and `IndependentSet` stand or fall together in `FPT`.
example (h : IndependentSet ∈ FPT (encPair encGraph encNat) Prod.snd) :
    Clique ∈ FPT (encPair encGraph encNat) Prod.snd :=
  Clique_mem_FPT_iff.2 h

end ComplexityTests.ColorCoding
