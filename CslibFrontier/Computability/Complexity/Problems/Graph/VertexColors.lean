/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LinearSpaceArith
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Mathlib.Data.List.GetD

/-!
# Vertex colors given by a list

A coloring, or any other labeling of the vertices of a `Cslib.Complexity.Graph` by numbers, can be
given as a list of numbers parallel to the vertex list: the label of a vertex is the entry at its
first occurrence among the declared vertices (`Cslib.Complexity.colorOf`). The colored instances of
color coding take colors in this form, and `NP` verifiers with colorings or vertex ranks as
witnesses read them in this form (`Cslib.Complexity.mem_NP_of_colorOf`).

## Main definitions

* `Cslib.Complexity.colorOf`: the color of a vertex in a list of colors.
* `Cslib.Complexity.encColoredGraph`: graphs with a list of vertex colors.

## Main results

* `Cslib.Complexity.colorOf_map`: listing the colors of the declared vertices gives every
  declared vertex its color.
* `Cslib.Complexity.computableInPolyTime_colorOf`,
  `Cslib.Complexity.computableInPolyTime_colorOf_comp`: reading a color is polynomial-time.
* `Cslib.Complexity.Graph.length_encList_map_le`: quadratic encoded-length bound for a bounded
  vertex labeling listed along `G.vertices`.
* `Cslib.Complexity.mem_NP_of_colorOf`: `NP` membership for graph problems verified from a bounded
  vertex labeling.
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

/-- The color of the vertex `v` under a list of colors `cs` parallel to the vertex list of `G`:
the entry of `cs` at the first occurrence of `v`, and `0` when there is none. -/
@[expose]
def colorOf (G : Graph) (cs : List ℕ) (v : ℕ) : ℕ := cs.getD (G.vertices.idxOf v) 0

/-- Graphs with vertex colors: the graph (`encGraph`), framed, then the list of colors parallel to
its vertex list (`Cslib.Complexity.colorOf`), each color framed and in binary. -/
abbrev encColoredGraph : Graph × List ℕ ↪ List Bool := encPair encGraph (encList encNat)

/-- The list of the colors of the declared vertices under `c` gives every declared vertex its
color. -/
@[simp]
theorem colorOf_map {G : Graph} {c : ℕ → ℕ} {v : ℕ} (hv : v ∈ G.vertices) :
    colorOf G (G.vertices.map c) v = c v := by
  simp [colorOf, List.getD_eq_getElem?_getD, hv]

/-- Reading a color from a list of colors is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_colorOf :
    ComputableInPolyTime (fun p : (Graph × List ℕ) × ℕ => colorOf p.1.1 p.1.2 p.2)
      (encPair encColoredGraph encNat) encNat := by
  unfold colorOf
  fun_prop

/-- Reading computed colors of computed vertices is polynomial-time; the compositional form of
`Cslib.Complexity.computableInPolyTime_colorOf` used by `fun_prop`. -/
@[fun_prop]
theorem computableInPolyTime_colorOf_comp {γ : Type} {enc : γ ↪ List Bool} {G : γ → Graph}
    {cs : γ → List ℕ} {v : γ → ℕ} (hG : ComputableInPolyTime G enc encGraph)
    (hcs : ComputableInPolyTime cs enc (encList encNat)) (hv : ComputableInPolyTime v enc encNat) :
    ComputableInPolyTime (fun x => colorOf (G x) (cs x) (v x)) enc encNat :=
  computableInPolyTime_colorOf.comp ((hG.prod hcs).prod hv)

/-- A labeling listed along the vertex list of a graph with at most `n` listed vertices, whose
values on the declared vertices are at most `n`, has an encoding of length at most `2 n ^ 2 + n`. -/
theorem Graph.length_encList_map_le {G : Graph} {f : ℕ → ℕ} {n : ℕ} (hG : G.vertices.length ≤ n)
    (hf : ∀ v ∈ G.vertices, f v ≤ n) :
    (encList encNat (G.vertices.map f)).length ≤ 2 * n ^ 2 + n := by
  have hentry : ∀ a ∈ G.vertices.map f, (encNat a).length ≤ n := by
    intro a ha
    obtain ⟨v, hv, rfl⟩ := List.mem_map.1 ha
    exact (length_encNat_le_self _).trans (hf v hv)
  have h := length_encList_le encNat _ hentry
  rw [List.length_map] at h
  nlinarith

/-- **NP membership from a bounded vertex labeling.** Let `check` be polynomial-time on instances
`x` paired with a list of vertex labels (`Cslib.Complexity.colorOf`). If every accepted list
certifies membership in `S`, and every member `x ∈ S` has a labeling `g` of the declared vertices
`(graph x).vertices` bounded by `(graph x).vertices.length` whose list
`(graph x).vertices.map g` is accepted by `check`, then `S ∈ NP enc`. -/
theorem mem_NP_of_colorOf {α : Type} {enc : α ↪ List Bool} (graph : α → Graph) {S : Set α}
    {check : α × List ℕ → Bool}
    (hcheck : ComputableInPolyTime check (encPair enc (encList encNat)) encBool)
    (hlen : ∀ x, (graph x).vertices.length ≤ (enc x).length)
    (hsound : ∀ x cs, check (x, cs) = true → x ∈ S)
    (hcomplete : ∀ x, x ∈ S →
      ∃ g : ℕ → ℕ, (∀ v ∈ (graph x).vertices, g v ≤ (graph x).vertices.length) ∧
        check (x, (graph x).vertices.map g) = true) :
    S ∈ NP enc := by
  have hset : S = {x | ∃ cs : List ℕ, check (x, cs) = true} := by
    ext x
    exact ⟨fun h => let ⟨g, _, hg⟩ := hcomplete x h; ⟨(graph x).vertices.map g, hg⟩,
      fun ⟨cs, hcs⟩ => hsound x cs hcs⟩
  rw [hset]
  refine mem_NP_of_witness (p := 2 * Polynomial.X ^ 2 + Polynomial.X) (.list .nat) hcheck
    (fun _ _ => Iff.rfl) ?_
  rintro x cs hcs
  obtain ⟨g, hgle, hg⟩ := hcomplete x (hsound x cs hcs)
  have hN : (graph x).vertices.length ≤ (enc x).length := hlen x
  refine ⟨(graph x).vertices.map g, hg, ?_⟩
  have h := Graph.length_encList_map_le hN fun v hv => (hgle v hv).trans hN
  simpa only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_ofNat] using h

end Cslib.Complexity
