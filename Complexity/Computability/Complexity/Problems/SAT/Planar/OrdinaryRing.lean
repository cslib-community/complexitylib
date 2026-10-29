/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Foundations.Geometry.Orthogonal.PairedPorts
public import Complexity.Logics.Propositional.CNF.ImplicationCycle
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.SplitIfs

/-!
# An eight-port ordinary signal ring

Eight binary implications follow the perimeter of `[20,220]²`, forcing all eight
variables to agree. Every variable has two internal literal occurrences, leaving
one external occurrence for its paired access. Unused accesses introduce no freedom.
The sixteen incidence routes are straight and have total Manhattan length 800.

## Main definitions

* `Variable`, `cyclicOrder`, `formula`: the fixed implication ring.
* `variablePosition`, `clausePositions`, `incidenceRoutes`: its explicit drawing.

## Main results

* `eval_formula_iff`, `eval_constant`: all ports carry one freely chosen bit.
* `internal_occurrences`: exactly two internal literal occurrences per port.

## References

This fixed template is original and reuses `CNF.implicationCycle`.
-/

@[expose] public section

namespace Cslib.Complexity.SAT.OrdinaryRing

open Cslib.Logic.PL Cslib.Logic.PL.CNF Orthogonal

/-- One variable for each side and lane of the common paired-port interface. -/
abbrev Variable := Fin 4 × Fin 2

/-- Cyclic geometric order, traversing the inner square clockwise. -/
def cyclicOrder : List Variable :=
  [(0, 0), (0, 1), (3, 0), (3, 1), (1, 1), (1, 0), (2, 1), (2, 0)]

/-- The eight directed implications closing the signal ring. -/
def formula : CNF Variable := implicationCycle cyclicOrder

/-- The eight common inner access positions. -/
def variablePosition (v : Variable) : Point := PairedPorts.variablePosition v.1 v.2

/-- Clause positions in precisely the order of the eight implications. -/
def clausePositions : List Point :=
  [(20, 120), (20, 220), (120, 220), (220, 220),
    (220, 120), (220, 20), (120, 20), (20, 20)]

/-- Indexed clause position, with an irrelevant out-of-range default. -/
def clausePosition (i : ℕ) : Point := clausePositions.getD i (0, 0)

/-- The sixteen clause-to-variable incidences, in clause and literal order. -/
def incidenceRoutes : List (ℕ × Variable × Route) :=
  [(0, (0, 0), [(20, 120), (20, 110)]),
    (0, (0, 1), [(20, 120), (20, 130)]),
    (1, (0, 1), [(20, 220), (20, 130)]),
    (1, (3, 0), [(20, 220), (110, 220)]),
    (2, (3, 0), [(120, 220), (110, 220)]),
    (2, (3, 1), [(120, 220), (130, 220)]),
    (3, (3, 1), [(220, 220), (130, 220)]),
    (3, (1, 1), [(220, 220), (220, 130)]),
    (4, (1, 1), [(220, 120), (220, 130)]),
    (4, (1, 0), [(220, 120), (220, 110)]),
    (5, (1, 0), [(220, 20), (220, 110)]),
    (5, (2, 1), [(220, 20), (130, 20)]),
    (6, (2, 1), [(120, 20), (130, 20)]),
    (6, (2, 0), [(120, 20), (110, 20)]),
    (7, (2, 0), [(20, 20), (110, 20)]),
    (7, (0, 0), [(20, 20), (20, 110)])]

/-- Common graph endpoints are the only permitted contacts between distinct incidences. -/
def commonEndpoints (e f : ℕ × Variable × Route) : List Point :=
  (if e.1 = f.1 then [clausePosition e.1] else []) ++
    (if e.2.1 = f.2.1 then [variablePosition e.2.1] else [])

/-- All eight port variables occur in the cycle. -/
theorem mem_cyclicOrder : ∀ v : Variable, v ∈ cyclicOrder := by decide +kernel

/-- The ring holds exactly when every port carries the value of the first port. -/
theorem eval_formula_iff (σ : Variable → Bool) :
    formula.eval σ = true ↔ ∀ v, σ v = σ (0, 0) := by
  rw [formula, eval_implicationCycle]
  constructor
  · intro h v
    exact h v (mem_cyclicOrder v) (0, 0) (mem_cyclicOrder (0, 0))
  · intro h x _ y _
    exact (h x).trans (h y).symm

/-- Either constant assignment satisfies the ring. -/
theorem eval_constant (b : Bool) : formula.eval (fun _ => b) = true :=
  (eval_formula_iff _).2 fun _ => rfl

/-- Every port has exactly two internal literal occurrences. -/
theorem internal_occurrences : ∀ v : Variable, formula.vars.count v = 2 := by decide +kernel

/-- The formula has eight clauses, each of width two. -/
theorem formula_sizes : formula.length = 8 ∧ ∀ c ∈ formula, c.length = 2 := by decide +kernel

/-- Every variable is actually used, including variables with no external access in a client. -/
theorem variables_used : ∀ v : Variable, v ∈ formula.vars := by decide +kernel

/-- All literal incidences occur exactly once, in formula order. -/
theorem incidenceRoutes_cover :
    incidenceRoutes.map (fun e => (e.1, e.2.1)) =
      formula.zipIdx.flatMap (fun ci => ci.1.map fun l => (ci.2, l.1)) := by decide +kernel

/-- There are eight clause positions and sixteen incidence routes. -/
theorem drawing_sizes : clausePositions.length = 8 ∧ incidenceRoutes.length = 16 := by
  decide +kernel

/-- Inner positions identify the eight variables. -/
theorem variablePosition_injective : Function.Injective variablePosition :=
  PairedPorts.variablePosition_injective

/-- Clause positions are distinct. -/
theorem clausePositions_nodup : clausePositions.Nodup := by decide +kernel

/-- Variables and clauses have different positions. -/
theorem variablePosition_not_mem_clauses :
    ∀ v : Variable, variablePosition v ∉ clausePositions := by decide +kernel

/-- The sixteen labeled incidences are distinct. -/
theorem incidenceEndpoints_nodup :
    (incidenceRoutes.map fun e => (e.1, e.2.1)).Nodup := by decide +kernel

/-- Every incidence has its prescribed clause and variable endpoints. -/
theorem incidence_endpoints : ∀ e ∈ incidenceRoutes,
    e.1 < 8 ∧ e.2.2.head? = some (clausePosition e.1) ∧
      e.2.2.getLast? = some (variablePosition e.2.1) := by decide +kernel

/-- All sixteen incidence routes are straight segments. -/
theorem incidence_pair : ∀ e ∈ incidenceRoutes,
    e.2.2 = [clausePosition e.1, variablePosition e.2.1] := by decide +kernel

/-- Every incidence is properly orthogonal. -/
theorem incidence_orthogonal : ∀ e ∈ incidenceRoutes, IsOrthogonal e.2.2 := by decide +kernel

/-- Listed incidence vertices are distinct within each route. -/
theorem incidence_points_nodup : ∀ e ∈ incidenceRoutes, e.2.2.Nodup := by decide +kernel

/-- Every incidence is continuously simple. -/
theorem incidence_isSimple {e : ℕ × Variable × Route} (he : e ∈ incidenceRoutes) :
    IsSimple e.2.2 := by
  refine ⟨incidence_points_nodup e he, ?_⟩
  intro a ha b hb hne
  rw [incidence_pair e he] at ha hb
  have ha' : a = (clausePosition e.1, variablePosition e.2.1) := by
    simpa only [List.consecutivePairs, List.tail_cons, List.tail_nil, List.zip_cons_cons,
      List.zip_nil_right, List.mem_singleton] using ha
  have hb' : b = (clausePosition e.1, variablePosition e.2.1) := by
    simpa only [List.consecutivePairs, List.tail_cons, List.tail_nil, List.zip_cons_cons,
      List.zip_nil_right, List.mem_singleton] using hb
  exact False.elim (hne (ha'.trans hb'.symm))

/-- All listed core points lie in `[20,220]²`. -/
theorem core_bounds : ∀ e ∈ incidenceRoutes, ∀ p ∈ e.2.2,
    20 ≤ p.1 ∧ p.1 ≤ 220 ∧ 20 ≤ p.2 ∧ p.2 ≤ 220 := by decide +kernel

/-- Every variable lies in the inner core square. -/
theorem variable_bounds : ∀ v : Variable,
    20 ≤ (variablePosition v).1 ∧ (variablePosition v).1 ≤ 220 ∧
      20 ≤ (variablePosition v).2 ∧ (variablePosition v).2 ≤ 220 := by decide +kernel

/-- Every clause lies in the inner core square. -/
theorem clause_bounds : ∀ p ∈ clausePositions,
    20 ≤ p.1 ∧ p.1 ≤ 220 ∧ 20 ≤ p.2 ∧ p.2 ≤ 220 := by decide +kernel

/-- The full continuous core support lies strictly inside the outer cell. -/
theorem core_support_interior {e : ℕ × Variable × Route} (he : e ∈ incidenceRoutes)
    {p : ℝ × ℝ} (hp : p ∈ support e.2.2) :
    0 < p.1 ∧ p.1 < 240 ∧ 0 < p.2 ∧ p.2 < 240 := by
  have hsub : support e.2.2 ⊆ openCell 120 (0, 0) := by
    apply support_subset_openCell
    intro q hq
    have hb := core_bounds e he q hq
    have hq' : 0 < q.1 ∧ q.1 < 240 ∧ 0 < q.2 ∧ q.2 < 240 := by omega
    have hreal : (0 : ℝ) < q.1 ∧ (q.1 : ℝ) < 240 ∧
        (0 : ℝ) < q.2 ∧ (q.2 : ℝ) < 240 := by exact_mod_cast hq'
    simpa [openCell, realPoint] using hreal
  simpa [openCell] using hsub hp

/-- Finite certificate of all permitted contacts between distinct incidences. -/
theorem routes_contact_check : ∀ e ∈ incidenceRoutes, ∀ f ∈ incidenceRoutes, e ≠ f →
    routeContactCheck (commonEndpoints e f) e.2.2 f.2.2 = true := by decide +kernel

/-- Continuous contacts between distinct incidences are shared graph endpoints. -/
theorem routes_contact {e f : ℕ × Variable × Route}
    (he : e ∈ incidenceRoutes) (hf : f ∈ incidenceRoutes) (hne : e ≠ f)
    {p : ℝ × ℝ} (hp : p ∈ support e.2.2) (hq : p ∈ support f.2.2) :
    ∃ q ∈ commonEndpoints e f, p = realPoint q :=
  routeContactCheck_sound (routes_contact_check e he f hf hne) hp hq

/-- Finite certificate excluding nonincident variable vertices. -/
theorem variable_avoidance_check : ∀ e ∈ incidenceRoutes, ∀ v : Variable, v ≠ e.2.1 →
    routeContactCheck [] e.2.2 [variablePosition v] = true := by decide +kernel

/-- Finite certificate excluding nonincident clause vertices. -/
theorem clause_avoidance_check : ∀ e ∈ incidenceRoutes, ∀ i : Fin 8, i.val ≠ e.1 →
    routeContactCheck [] e.2.2 [clausePosition i] = true := by decide +kernel

/-- Incidences avoid every nonincident variable over their full real support. -/
theorem variable_not_mem_support {e : ℕ × Variable × Route} (he : e ∈ incidenceRoutes)
    {v : Variable} (hv : v ≠ e.2.1) : realPoint (variablePosition v) ∉ support e.2.2 :=
  not_mem_support_of_routeContactCheck (variable_avoidance_check e he v hv)

/-- Incidences avoid every nonincident clause over their full real support. -/
theorem clause_not_mem_support {e : ℕ × Variable × Route} (he : e ∈ incidenceRoutes)
    {i : Fin 8} (hi : i.val ≠ e.1) : realPoint (clausePosition i) ∉ support e.2.2 :=
  not_mem_support_of_routeContactCheck (clause_avoidance_check e he i hi)

/-- Finite certificate that access touches the core only at its own variable. -/
theorem access_contact_check : ∀ s l, ∀ e ∈ incidenceRoutes,
    routeContactCheck (if e.2.1 = (s, l) then [variablePosition (s, l)] else [])
      (PairedPorts.accessRoute s l) e.2.2 = true := by decide +kernel

/-- Every access/core contact is its designated variable endpoint. -/
theorem access_contact {s : Fin 4} {l : Fin 2} {e : ℕ × Variable × Route}
    (he : e ∈ incidenceRoutes) {p : ℝ × ℝ}
    (hp : p ∈ support (PairedPorts.accessRoute s l)) (hq : p ∈ support e.2.2) :
    e.2.1 = (s, l) ∧ p = realPoint (variablePosition (s, l)) := by
  obtain ⟨q, hq, hpq⟩ := routeContactCheck_sound (access_contact_check s l e he) hp hq
  split_ifs at hq with h
  · have hq' : q = variablePosition (s, l) := List.mem_singleton.mp hq
    exact ⟨h, hq' ▸ hpq⟩
  · exact False.elim (List.not_mem_nil hq)

/-- Finite certificate excluding every other variable from an access. -/
theorem access_variable_avoidance_check : ∀ s l, ∀ v : Variable, v ≠ (s, l) →
    routeContactCheck [] (PairedPorts.accessRoute s l) [variablePosition v] = true := by
  decide +kernel

/-- Finite certificate excluding every clause from every access. -/
theorem access_clause_avoidance_check : ∀ s l, ∀ p ∈ clausePositions,
    routeContactCheck [] (PairedPorts.accessRoute s l) [p] = true := by decide +kernel

/-- Access avoids every other variable over its full real support. -/
theorem access_variable_not_mem {s : Fin 4} {l : Fin 2} {v : Variable} (hv : v ≠ (s, l)) :
    realPoint (variablePosition v) ∉ support (PairedPorts.accessRoute s l) :=
  not_mem_support_of_routeContactCheck (access_variable_avoidance_check s l v hv)

/-- Access avoids every clause over its full real support. -/
theorem access_clause_not_mem {s : Fin 4} {l : Fin 2} {p : Point} (hp : p ∈ clausePositions) :
    realPoint p ∉ support (PairedPorts.accessRoute s l) :=
  not_mem_support_of_routeContactCheck (access_clause_avoidance_check s l p hp)

/-- The sixteen incidence segments have total Manhattan length 800. -/
theorem route_sizes :
    (incidenceRoutes.map fun e => e.2.2.consecutivePairs.length).sum = 16 ∧
      (incidenceRoutes.map fun e => wireLength e.2.2).sum = 800 := by decide +kernel

end Cslib.Complexity.SAT.OrdinaryRing
