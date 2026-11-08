/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.PCP.Encoded.Simple
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Pi
import Complexity.Computability.PCP.Encoded.Count
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Eq
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListMap

/-!
# Removing loops from binary constraint graphs

A loop of a binary constraint graph is an edge occurrence whose two ends are the same vertex `u`,
with a relation `R` on the label of `u` taken twice. `Cslib.PCP.Encoded.Graph.deloop` doubles
the vertex numbers: vertex `v` becomes `2 v`, every edge between distinct vertices keeps its
relation, and a loop at `u` becomes an edge from `2 u` to the fresh vertex `2 u + 1`. Its relation
checks `R` on the label of `2 u` alone and ignores the label of `2 u + 1`. The result is loopless,
and every labelling `τ` of it violates exactly as many edges as the labelling `v ↦ τ (2 v)` of the
original graph. So the two graphs have the same value (`unsatVal_deloop`).

Dinur's preprocessing deliberately adds loops, so the hard binary CSP instances of
`Cslib.Complexity.GapTwoCSP_npHard` are not loopless; loop removal prepares them for the incidence
construction of Label Cover, whose output is then simple. The construction is a library adaptation
to the executable graph API.

## Main definitions

* `Cslib.PCP.Encoded.Graph.deloop`: replace every loop by an edge to a fresh vertex.

## Main results

* `Cslib.PCP.Encoded.Graph.isLoopless_deloop`: the result is loopless.
* `Cslib.PCP.Encoded.Graph.unsatVal_deloop`: the value is unchanged.
* `Cslib.PCP.Encoded.Graph.satisfiable_deloop_iff`: so is satisfiability.
* `Cslib.PCP.Encoded.Graph.isPolyTime_deloop`: polynomial-time compilation for a fixed finite
  alphabet, under the framed graph and table encodings.
-/

@[expose] public section

namespace Cslib.PCP.Encoded.Graph

open Turing.MultiTapeTM

variable {α : Type}

/-- The image of an edge under loop removal: a loop at `u` becomes an edge from `2 u` to `2 u + 1`
whose relation reads the label of `2 u` twice; any other edge is renumbered by doubling. -/
def deloopEdge (d : Edge (α → α → Bool)) : Edge (α → α → Bool) :=
  if d.src == d.dst then ⟨2 * d.src, 2 * d.src + 1, fun a _ => d.constraint a a⟩
  else ⟨2 * d.src, 2 * d.dst, d.constraint⟩

/-- **Loop removal**: double the vertex numbers and redirect every loop to a fresh vertex. -/
def deloop (g : Graph (α → α → Bool)) : Graph (α → α → Bool) :=
  ⟨2 * g.vertices, g.edges.map deloopEdge⟩

/-- Loop removal keeps the number of edge occurrences. -/
@[simp]
theorem length_edges_deloop (g : Graph (α → α → Bool)) :
    (deloop g).edges.length = g.edges.length := by
  simp [deloop]

/-- Loop removal keeps the declared vertices: endpoints below `n` go below `2 n`. -/
theorem WellFormed.deloop {g : Graph (α → α → Bool)} (hg : g.WellFormed) :
    (deloop g).WellFormed := by
  intro d hd
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hd
  have h := hg e he
  change (deloopEdge e).src < 2 * g.vertices ∧ (deloopEdge e).dst < 2 * g.vertices
  unfold deloopEdge
  split <;> simp only <;> omega

/-- **The result of loop removal is loopless.** -/
theorem isLoopless_deloop (g : Graph (α → α → Bool)) : (deloop g).IsLoopless := by
  intro d hd
  obtain ⟨e, -, rfl⟩ := List.mem_map.mp hd
  unfold deloopEdge
  split
  · simp only
    omega
  · rename_i h
    have h' : e.src ≠ e.dst := by simpa using h
    simp only
    omega

/-- A labelling of the result violates exactly as many edges as its restriction `v ↦ τ (2 v)` to
the doubled original vertices violates in the original graph. -/
theorem countP_deloop (g : Graph (α → α → Bool)) (τ : ℕ → α) :
    (deloop g).edges.countP (fun d => !d.constraint (τ d.src) (τ d.dst)) =
      g.edges.countP (fun d => !d.constraint (τ (2 * d.src)) (τ (2 * d.dst))) := by
  rw [deloop, List.countP_map]
  congr 1
  funext d
  simp only [Function.comp_apply, deloopEdge]
  split
  · rename_i h
    have h' : d.src = d.dst := by simpa using h
    simp [h']
  · rfl

/-- **Loop removal keeps the value.** A labelling of the original graph lifts to the result by
reading the label of `v` at `2 v` and `2 v + 1`, and a labelling of the result restricts to the
even vertices; both keep the number of violated edges. -/
theorem unsatVal_deloop [Nonempty α] (g : Graph (α → α → Bool)) :
    ((deloop g).toGraph id).unsatVal = (g.toGraph id).unsatVal := by
  refine le_antisymm ?_ ((ConstraintGraph.le_unsatVal_iff _).2 fun τ => ?_)
  · obtain ⟨σ, hσ⟩ := (g.toGraph id).exists_unsatFrac_eq_unsatVal
    refine ((deloop g).toGraph id |>.unsatVal_le fun v => σ (v / 2)).trans (le_of_eq ?_)
    rw [← hσ, unsatFrac_toGraph, unsatFrac_toGraph]
    have hc := countP_deloop g fun v => σ (v / 2)
    simp only [Nat.mul_div_cancel_left _ two_pos] at hc
    simp only [id_eq]
    rw [hc, length_edges_deloop]
  · refine ((g.toGraph id).unsatVal_le fun v => τ (2 * v)).trans (le_of_eq ?_)
    rw [unsatFrac_toGraph, unsatFrac_toGraph]
    simp only [id_eq]
    rw [countP_deloop, length_edges_deloop]

/-- Loop removal keeps satisfiability. -/
theorem satisfiable_deloop_iff [Nonempty α] (g : Graph (α → α → Bool)) :
    ((deloop g).toGraph id).Satisfiable ↔ (g.toGraph id).Satisfiable := by
  rw [← ConstraintGraph.unsatVal_eq_zero_iff, ← ConstraintGraph.unsatVal_eq_zero_iff,
    unsatVal_deloop]

/-- Loop removal is polynomial-time for every fixed finite alphabet: it rewrites each edge
record, reading its unary endpoints and its complete relation table. -/
@[fun_prop]
theorem isPolyTime_deloop [Fintype α] :
    ComputableInPolyTime (deloop (α := α))
      (Graph.encoding (encPi (encPi encBool))) (Graph.encoding (encPi (encPi encBool))) := by
  let encE := Edge.encoding (encPi (encPi encBool) : (α → α → Bool) ↪ List Bool)
  have hd : ComputableInPolyTime (fun d : Edge (α → α → Bool) => d) encE encE := .id'
  have hdiag : ComputableInPolyTime (fun R : α → α → Bool => fun a (_ : α) => R a a)
      (encPi (encPi encBool)) (encPi (encPi encBool)) := .of_finite _
  have htwo : ComputableInPolyTime (fun _ : Edge (α → α → Bool) => 2) encE encUnary := .const _
  have hsrc := ComputableInPolyTime.unary_mul' htwo (Edge.isPolyTime_src hd)
  have hdst := ComputableInPolyTime.unary_mul' htwo (Edge.isPolyTime_dst hd)
  have hedge : ComputableInPolyTime (deloopEdge (α := α)) encE encE := by
    unfold deloopEdge
    exact ComputableInPolyTime.ite' (ComputableInPolyTime.unary_beq' (Edge.isPolyTime_src hd)
      (Edge.isPolyTime_dst hd))
      (Edge.isPolyTime_mk hsrc (ComputableInPolyTime.unary_add' hsrc (.const 1))
        (hdiag.comp (Edge.isPolyTime_constraint hd)))
      (Edge.isPolyTime_mk hsrc hdst (Edge.isPolyTime_constraint hd))
  have hg : ComputableInPolyTime (fun g : Graph (α → α → Bool) => g)
      (Graph.encoding (encPi (encPi encBool))) (Graph.encoding (encPi (encPi encBool))) := .id'
  have hedges := ComputableInPolyTime.mapWithInput (f := fun _ => deloopEdge (α := α))
    (Graph.isPolyTime_edges hg) (hedge.comp (.snd _ _))
  exact Graph.isPolyTime_mk
    (ComputableInPolyTime.unary_mul' (.const 2) (Graph.isPolyTime_vertices hg)) hedges

end Cslib.PCP.Encoded.Graph
