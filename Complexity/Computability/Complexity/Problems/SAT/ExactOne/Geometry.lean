/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.SAT.ExactOne.GeometryData
public import Complexity.Foundations.Geometry.Orthogonal.Separation
public import Complexity.Foundations.Geometry.Orthogonal.Simple
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Nodup
import Mathlib.Data.Fintype.Pi

/-!
# Continuous geometry certificates for exact-one gadgets

Finite arithmetic checks certify the entire real supports of the fixed gadget routes,
including their isolated exterior accesses. These are local replacement certificates;
composition with an input drawing is a separate construction.

## Main definitions

* `LocalGeometry.Check`: decidable finite endpoint, simplicity, contact, and access checks.

## Main results

* `disjunctionGeometry_check`, `falseGeometry_check`, `complementGeometry_check`.
* `LocalGeometry.incidence_isSimple`, `LocalGeometry.routes_contact`,
  `LocalGeometry.access_contact`: continuous consequences of the finite checks.

## References

The incidence graphs are from [HuntMaratheRadhakrishnanStearns1998, Theorem 3.8,
Figures 3.4–3.5 and Lemma 3.6]. The orthogonal certificates are original.
-/

@[expose] public section

namespace Cslib.Complexity.SAT.ExactOne

open Orthogonal

namespace LocalGeometry

/-- Common listed endpoints of two segments are the permitted self-contacts. -/
def segmentEndpoints (a b : Point × Point) : List Point :=
  ([a.1, a.2].filter fun p => p = b.1 ∨ p = b.2)

/-- A decidable finite simplicity certificate for an individual polygonal route. -/
def SimpleCheck (r : Route) : Prop :=
  r.Nodup ∧ ∀ a ∈ r.consecutivePairs, ∀ b ∈ r.consecutivePairs, a ≠ b →
    segmentContactCheck (segmentEndpoints a b) a.1 a.2 b.1 b.2 = true

instance (r : Route) : Decidable (SimpleCheck r) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The finite certificate refers to graph endpoints, complete routes, and all exterior
accesses. The core lies strictly inside the square cell of side `g.size`. -/
def Check (g : LocalGeometry) : Prop :=
  (g.variablePositions ++ g.clausePositions).Nodup ∧
  (g.incidenceRoutes.map fun e => (e.1, e.2.1)).Nodup ∧
  g.accessRoutes.length = g.terminalVariables.length ∧
  g.accessRoutes.length = g.boundaryPorts.length ∧
  (∀ e ∈ g.incidenceRoutes,
    e.1 < g.clausePositions.length ∧ e.2.1 < g.variablePositions.length ∧
      e.2.2.head? = some (g.clausePosition e.1) ∧
      e.2.2.getLast? = some (g.variablePosition e.2.1) ∧
      IsOrthogonal e.2.2 ∧ SimpleCheck e.2.2 ∧
      ∀ p ∈ e.2.2, 20 ≤ p.1 ∧ p.1 ≤ (g.size : ℤ) - 20 ∧
        20 ≤ p.2 ∧ p.2 ≤ (g.size : ℤ) - 20) ∧
  (∀ e ∈ g.incidenceRoutes, ∀ f ∈ g.incidenceRoutes, e ≠ f →
    routeContactCheck (g.commonEndpoints e f) e.2.2 f.2.2 = true) ∧
  (∀ e ∈ g.incidenceRoutes, ∀ v : Fin g.variablePositions.length, v.val ≠ e.2.1 →
    routeContactCheck [] e.2.2 [g.variablePosition v] = true) ∧
  (∀ e ∈ g.incidenceRoutes, ∀ i : Fin g.clausePositions.length, i.val ≠ e.1 →
    routeContactCheck [] e.2.2 [g.clausePosition i] = true) ∧
  (∀ i : Fin g.accessRoutes.length,
    let r := g.accessRoutes.getD i []
    let v := g.terminalVariables.getD i 0
    v < g.variablePositions.length ∧
      r.head? = some (g.boundaryPorts.getD i (0, 0)) ∧
      r.getLast? = some (g.variablePosition v) ∧
      IsOrthogonal r ∧ SimpleCheck r ∧
      (∀ p ∈ r, 0 ≤ p.1 ∧ p.1 ≤ g.size ∧ 0 ≤ p.2 ∧ p.2 ≤ g.size) ∧
      (∀ p ∈ r.tail, 0 < p.1 ∧ p.1 < g.size ∧ 0 < p.2 ∧ p.2 < g.size) ∧
      (∀ e ∈ g.incidenceRoutes,
        routeContactCheck (if e.2.1 = v then [g.variablePosition v] else [])
          r e.2.2 = true) ∧
      (∀ j : Fin g.accessRoutes.length, i ≠ j →
        routeContactCheck [] r (g.accessRoutes.getD j []) = true) ∧
      (∀ w : Fin g.variablePositions.length, w.val ≠ v →
        routeContactCheck [] r [g.variablePosition w] = true) ∧
      ∀ p ∈ g.clausePositions, routeContactCheck [] r [p] = true)

instance (g : LocalGeometry) : Decidable (Check g) := by
  unfold Check
  repeat' refine @instDecidableAnd _ _ ?_ ?_
  all_goals infer_instance

/-- The finite simplicity certificate controls full real segment intersections. -/
theorem isSimple_of_check {r : Route} (h : SimpleCheck r) : IsSimple r := by
  refine ⟨h.1, ?_⟩
  intro a ha b hb hne p hp hq
  obtain ⟨q, hq, hpq⟩ := segmentContactCheck_sound (h.2 a ha b hb hne) hp hq
  have hq' := List.mem_filter.mp hq
  have hqa : q = a.1 ∨ q = a.2 := by simpa using hq'.1
  have hqb : q = b.1 ∨ q = b.2 := by simpa using hq'.2
  exact ⟨hqa.elim (fun h => Or.inl (h ▸ hpq)) (fun h => Or.inr (h ▸ hpq)),
    hqb.elim (fun h => Or.inl (h ▸ hpq)) (fun h => Or.inr (h ▸ hpq))⟩

/-- Every checked incidence has its prescribed clause and variable endpoints. -/
theorem incidence_endpoints {g : LocalGeometry} (h : Check g)
    {e : LocalIncidence} (he : e ∈ g.incidenceRoutes) :
    e.1 < g.clausePositions.length ∧ e.2.1 < g.variablePositions.length ∧
      e.2.2.head? = some (g.clausePosition e.1) ∧
      e.2.2.getLast? = some (g.variablePosition e.2.1) := by
  have he' := h.2.2.2.2.1 e he
  exact ⟨he'.1, he'.2.1, he'.2.2.1, he'.2.2.2.1⟩

/-- Every checked incidence is properly orthogonal. -/
theorem incidence_orthogonal {g : LocalGeometry} (h : Check g)
    {e : LocalIncidence} (he : e ∈ g.incidenceRoutes) : IsOrthogonal e.2.2 :=
  (h.2.2.2.2.1 e he).2.2.2.2.1

/-- Every checked incidence is simple over its full continuous support. -/
theorem incidence_isSimple {g : LocalGeometry} (h : Check g)
    {e : LocalIncidence} (he : e ∈ g.incidenceRoutes) : IsSimple e.2.2 :=
  isSimple_of_check (h.2.2.2.2.1 e he).2.2.2.2.2.1

/-- Checked incidence routes can meet only at a shared clause or variable vertex. -/
theorem routes_contact {g : LocalGeometry} (h : Check g)
    {e f : LocalIncidence} (he : e ∈ g.incidenceRoutes) (hf : f ∈ g.incidenceRoutes)
    (hne : e ≠ f) {p : ℝ × ℝ} (hp : p ∈ support e.2.2) (hq : p ∈ support f.2.2) :
    ∃ q ∈ g.commonEndpoints e f, p = realPoint q :=
  routeContactCheck_sound (h.2.2.2.2.2.1 e he f hf hne) hp hq

/-- Checked incidences avoid every nonincident variable vertex. -/
theorem variable_not_mem_support {g : LocalGeometry} (h : Check g)
    {e : LocalIncidence} (he : e ∈ g.incidenceRoutes)
    {v : Fin g.variablePositions.length} (hv : v.val ≠ e.2.1) :
    realPoint (g.variablePosition v) ∉ support e.2.2 :=
  not_mem_support_of_routeContactCheck (h.2.2.2.2.2.2.1 e he v hv)

/-- Checked incidences avoid every nonincident clause vertex. -/
theorem clause_not_mem_support {g : LocalGeometry} (h : Check g)
    {e : LocalIncidence} (he : e ∈ g.incidenceRoutes)
    {i : Fin g.clausePositions.length} (hi : i.val ≠ e.1) :
    realPoint (g.clausePosition i) ∉ support e.2.2 :=
  not_mem_support_of_routeContactCheck (h.2.2.2.2.2.2.2.1 e he i hi)

/-- Exterior access routes are simple over their full continuous support. -/
theorem access_isSimple {g : LocalGeometry} (h : Check g) (i : Fin g.accessRoutes.length) :
    IsSimple (g.accessRoutes.getD i []) :=
  isSimple_of_check (h.2.2.2.2.2.2.2.2 i).2.2.2.2.1

/-- Distinct checked accesses have disjoint full real supports. -/
theorem access_disjoint {g : LocalGeometry} (h : Check g)
    {i j : Fin g.accessRoutes.length} (hne : i ≠ j) :
    Disjoint (support (g.accessRoutes.getD i [])) (support (g.accessRoutes.getD j [])) :=
  disjoint_support_of_routeContactCheck
    ((h.2.2.2.2.2.2.2.2 i).2.2.2.2.2.2.2.2.1 j hne)

/-- A checked access meets the core only at its corresponding terminal. -/
theorem access_contact {g : LocalGeometry} (h : Check g)
    {i : Fin g.accessRoutes.length} {e : LocalIncidence} (he : e ∈ g.incidenceRoutes)
    {p : ℝ × ℝ} (hp : p ∈ support (g.accessRoutes.getD i []))
    (hq : p ∈ support e.2.2) :
    e.2.1 = g.terminalVariables.getD i 0 ∧
      p = realPoint (g.variablePosition (g.terminalVariables.getD i 0)) := by
  obtain ⟨q, hq, hpq⟩ := routeContactCheck_sound
    ((h.2.2.2.2.2.2.2.2 i).2.2.2.2.2.2.2.1 e he) hp hq
  split_ifs at hq with heq
  · have hq' := List.mem_singleton.mp hq
    exact ⟨heq, hq' ▸ hpq⟩
  · exact False.elim (List.not_mem_nil hq)

end LocalGeometry

/-- Complete finite certificate for the parsimonious disjunction replacement. -/
theorem disjunctionGeometry_check : LocalGeometry.Check disjunctionGeometry := by
  decide +kernel

/-- Complete finite certificate for the positive forced-false gadget. -/
theorem falseGeometry_check : LocalGeometry.Check falseGeometry := by
  decide +kernel

/-- Complete finite certificate for the positive complement gadget. -/
theorem complementGeometry_check : LocalGeometry.Check complementGeometry := by
  decide +kernel

end Cslib.Complexity.SAT.ExactOne
