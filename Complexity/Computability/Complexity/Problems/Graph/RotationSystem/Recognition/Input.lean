/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.Graph.RotationSystem.Certificate
import Mathlib.Data.List.GetD

/-!
# Full fixed rotations on dense listed graphs

This auxiliary input uses the existing listed `Graph`, indexed darts and rotations. A vertex is
free (`none`) or has its entire clockwise cyclic dart order prescribed (`some word`). Binary
dart indices retain both ends of loops and every parallel occurrence. `some []` is the complete
order of an isolated point. Raw input is validated before algebraic queries or recovery.

`Feasible` asks for the existing componentwise numerical genus-zero rotation. No equivalence
with a geometric drawing, or with a parity system, is asserted here.

## Main definitions

* `Cslib.Complexity.Graph.RotationRecognition.FixedRotationInput`: raw fixed/free input.
* `Cslib.Complexity.Graph.RotationRecognition.Valid`: dense closed graph and complete orders.
* `Cslib.Complexity.Graph.RotationRecognition.Realizes`: literal cyclic successor equations.
* `Cslib.Complexity.Graph.RotationRecognition.Consecutive`: internal block successor equations.
-/

public section

namespace Cslib.Complexity.Graph.RotationRecognition

open Turing.MultiTapeTM

/-- Raw dense listed graph and one optional complete binary dart order per vertex. -/
structure FixedRotationInput where
  /-- The existing graph, retaining indexed edge occurrences. -/
  graph : Graph
  /-- `none` is free; `some word` prescribes the complete clockwise cyclic order. -/
  orders : List (Option (List ℕ))
  deriving DecidableEq, Repr

/-- Framed existing binary graph, then a framed list of optional framed binary dart words. -/
enc_structure encFixedRotationInput : FixedRotationInput where
  graph : encGraph, orders : (encList (encOption (encList encNat)))

/-- All binary dart indices at a vertex, in edge/end order. The scan uses the actual edge count. -/
@[expose] def fiber (G : Graph) (v : ℕ) : List ℕ :=
  (List.range (2 * G.2.length)).filter fun i => decide (G.incidenceVertices.getD i 0 = v)

/-- Raw validity: dense declared vertices, closed endpoints, exact order-table width, and every
prescribed word enumerating its entire endpoint fiber exactly once. -/
@[expose] def Valid (I : FixedRotationInput) : Prop :=
  I.graph.1 = List.range I.graph.1.length ∧
    (∀ v ∈ I.graph.incidenceVertices, v < I.graph.1.length) ∧
    I.orders.length = I.graph.1.length ∧
    ∀ v word, I.orders.getD v none = some word →
      word.Nodup ∧ ∀ d, d ∈ word ↔ d ∈ fiber I.graph v

/-- Total finite validity test; malformed binary names and indices are only compared/read. -/
@[expose] def validate (I : FixedRotationInput) : Bool :=
  decide (I.graph.1 = List.range I.graph.1.length) &&
    I.graph.incidenceVertices.all (fun v => decide (v < I.graph.1.length)) &&
    decide (I.orders.length = I.graph.1.length) &&
    I.orders.zipIdx.all fun entry =>
      entry.1.elim true fun word => enumeratesBool (fiber I.graph entry.2) word

/-- Validation implements the complete fixed/free contract on every raw input. -/
theorem validate_eq_true_iff (I : FixedRotationInput) : validate I = true ↔ Valid I := by
  simp only [validate, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Valid]
  constructor
  · rintro ⟨⟨⟨hd, he⟩, hw⟩, ho⟩
    refine ⟨hd, he, hw, fun v word hv => ?_⟩
    have hlt : v < I.orders.length := by
      by_contra h
      rw [List.getD_eq_default _ _ (by omega)] at hv
      contradiction
    have hx : (some word, v) ∈ I.orders.zipIdx := by
      apply List.mem_zipIdx_iff_getElem?.mpr
      rw [← hv, List.getD_eq_getElem _ _ hlt]
      simp
    exact enumeratesBool_eq_true_iff.mp (ho _ hx)
  · rintro ⟨hd, he, hw, ho⟩
    refine ⟨⟨⟨hd, he⟩, hw⟩, fun entry hentry => ?_⟩
    have hget := List.mem_zipIdx_iff_getElem?.mp hentry
    obtain ⟨hlt, hval⟩ := List.getElem?_eq_some_iff.mp hget
    have hread : I.orders.getD entry.2 none = entry.1 := by
      rw [List.getD_eq_getElem _ _ hlt, hval]
    cases hx : entry.1 with
    | none => rfl
    | some word =>
      exact enumeratesBool_eq_true_iff.mpr (ho entry.2 word (hread.trans hx))

/-- Next position in a complete cyclic word, with a total zero fallback. -/
@[expose] def nextInWord (word : List ℕ) (i : ℕ) : ℕ :=
  word.getD (if i + 1 < word.length then i + 1 else 0) 0

/-- A rotation follows every prescribed complete cyclic word literally, without reflection.
Empty prescribed words impose no successor equation. -/
@[expose] def Realizes (I : FixedRotationInput) (r : RotationSystem I.graph) : Prop :=
  ∀ v word, I.orders.getD v none = some word →
    ∀ i, i < word.length → ∀ d : Dart I.graph,
      d.index = word.getD i 0 → (r.rotate d).index = nextInWord word i

/-- The existing numerical feasibility predicate, with all prescribed full orders. This is an
internal target for a future proved algebraic criterion, not a new definition of planarity. -/
@[expose] def Feasible (I : FixedRotationInput) : Prop :=
  ∃ r : RotationSystem I.graph, r.NumericalGenusZero ∧ Realizes I r

/-- Only successive entries inside the directed block are constrained. In particular, a proper
block's last entry is not required to return to its first entry. -/
@[expose] def Consecutive {G : Graph} (r : RotationSystem G) (block : List ℕ) : Prop :=
  ∀ i, i + 1 < block.length → ∀ d : Dart G,
    d.index = block.getD i 0 → (r.rotate d).index = block.getD (i + 1) 0

/-- A singleton block has no internal successor equation. -/
theorem consecutive_singleton {G : Graph} (r : RotationSystem G) (d : ℕ) :
    Consecutive r [d] := by
  intro i hi
  simp only [List.length_singleton] at hi
  omega

/-- Fiber membership retains both the binary width and the exact endpoint. -/
theorem mem_fiber {G : Graph} {v d : ℕ} :
    d ∈ fiber G v ↔ d < 2 * G.2.length ∧ G.incidenceVertices.getD d 0 = v := by
  simp [fiber]

/-- A dart's own binary index belongs to exactly its endpoint fiber. -/
theorem index_mem_fiber {G : Graph} (d : Dart G) : d.index ∈ fiber G d.vertex :=
  mem_fiber.mpr ⟨(Dart.indexEquiv G d).isLt, Dart.vertex_index d⟩

/-- Raw fibers contain no repeated dart indices, even on loops or parallel edges. -/
theorem nodup_fiber (G : Graph) (v : ℕ) : (fiber G v).Nodup :=
  List.nodup_range.filter _

/-- Every raw fiber is bounded by the actual dart-list length. -/
theorem length_fiber_le (G : Graph) (v : ℕ) : (fiber G v).length ≤ 2 * G.2.length := by
  simpa only [fiber, List.length_range] using List.length_filter_le
    (fun i => decide (G.incidenceVertices.getD i 0 = v)) (List.range (2 * G.2.length))

end Cslib.Complexity.Graph.RotationRecognition
