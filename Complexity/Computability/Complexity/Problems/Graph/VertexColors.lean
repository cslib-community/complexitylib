/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.Graph
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Mathlib.Data.List.GetD

/-!
# Vertex colors given by a list

A coloring, or any other labeling of the vertices of a `Cslib.Complexity.Graph` by numbers, can be
given as a list of numbers parallel to the vertex list: the label of a vertex is the entry at its
first occurrence among the declared vertices (`Cslib.Complexity.colorOf`). The colored instances of
color coding take colors in this form, and `NP` verifiers with colorings or vertex ranks as
witnesses read them in this form.

## Main definitions

* `Cslib.Complexity.colorOf`: the color of a vertex in a list of colors.

## Main results

* `Cslib.Complexity.colorOf_map`: listing the colors of the declared vertices gives every
  declared vertex its color.
* `Cslib.Complexity.computableInPolyTime_colorOf`,
  `Cslib.Complexity.computableInPolyTime_colorOf_comp`: reading a color is polynomial-time.
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

/-- The color of the vertex `v` under a list of colors `cs` parallel to the vertex list of `G`:
the entry of `cs` at the first occurrence of `v`, and `0` when there is none. -/
@[expose]
def colorOf (G : Graph) (cs : List ℕ) (v : ℕ) : ℕ := cs.getD (G.1.idxOf v) 0

/-- The list of the colors of the declared vertices under `c` gives every declared vertex its
color. -/
@[simp]
theorem colorOf_map {G : Graph} {c : ℕ → ℕ} {v : ℕ} (hv : v ∈ G.1) :
    colorOf G (G.1.map c) v = c v := by
  have hlt : G.1.idxOf v < G.1.length := List.idxOf_lt_length_iff.2 hv
  rw [colorOf, List.getD_eq_getElem _ _ (by simpa using hlt), List.getElem_map,
    List.getElem_idxOf hlt]

/-- Reading a color from a list of colors is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_colorOf :
    ComputableInPolyTime (fun p : (Graph × List ℕ) × ℕ => colorOf p.1.1 p.1.2 p.2)
      (encPair (encPair encGraph (encList encNat)) encNat) encNat := by
  unfold colorOf encGraph
  fun_prop

/-- Reading computed colors of computed vertices is polynomial-time; the compositional form of
`Cslib.Complexity.computableInPolyTime_colorOf` used by `fun_prop`. -/
@[fun_prop]
theorem computableInPolyTime_colorOf_comp {γ : Type} {enc : γ ↪ List Bool} {G : γ → Graph}
    {cs : γ → List ℕ} {v : γ → ℕ} (hG : ComputableInPolyTime G enc encGraph)
    (hcs : ComputableInPolyTime cs enc (encList encNat)) (hv : ComputableInPolyTime v enc encNat) :
    ComputableInPolyTime (fun x => colorOf (G x) (cs x) (v x)) enc encNat :=
  computableInPolyTime_colorOf.comp ((hG.prod hcs).prod hv)

end Cslib.Complexity
