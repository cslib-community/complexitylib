/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.SAT.ExactOne.DrawingEndpoints
public import Complexity.Computability.Complexity.Problems.SAT.ExactOne.GeometryProfilesCollar
import Mathlib.Data.List.GetD
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Continuous local and exterior routes of the positive drawing compiler

Local prefixes lie in their closed clause boxes. Their inherited exterior routes touch those
boxes at the prescribed source ports only. These full-real-support facts justify the actual
route concatenations, including shared source variables and parallel source incidences.

## Main definitions

* `positiveStem`: the translated local part of an actual emitted incidence.

## Main results

* `positiveStem_in_box`, `positiveExterior_box_contact`: clause-box support isolation.
* `positiveIncidenceRoute_regular`: proper orthogonality and continuous simplicity of actual routes.
* `positiveIncidenceRoute_join_endpoints`: exact endpoint identity for additive route costs.
* `positiveStem_contacts`: finite local prefixes meet only at their actual shared endpoints.

## References

These finite drawing-composition and continuous-support proofs are original.
-/

@[expose] public section

namespace Cslib.Complexity.SAT.ExactOne

open Cslib.Logic.PL Orthogonal

private theorem collarPrefixRoute_points_bounds {s : PortAssignment} (hs : s.Distinct)
    (i : Fin 3) {r : Route}
    (hr : ∀ q ∈ r, 0 ≤ q.1 ∧ q.1 ≤ 180000 ∧ 0 ≤ q.2 ∧ q.2 ≤ 180000) :
    ∀ q ∈ collarPrefixRoute s i r,
      0 ≤ q.1 ∧ q.1 ≤ 540000 ∧ 0 ≤ q.2 ∧ q.2 ≤ 540000 := by
  intro q hq
  rw [collarPrefixRoute, List.mem_append] at hq
  rcases hq with hq | hq
  · exact collarRoute_points_bounds _ hr q hq
  · have hq' := List.mem_reverse.mp (List.mem_of_mem_tail hq)
    exact (((collar_check s hs).2 i).2.2.2.2.1) q hq'

/-- All listed points of an actual collared local incidence lie in the common clause square.
-/
theorem clauseGeometry_incidence_points_bounds {φ : CNF ℕ} {d : Graph.OrthogonalDrawing}
    (hd : Graph.IsPlanarOrthogonalDrawing (SAT.incidenceGraph φ) d) {i : ℕ}
    (hi : i < φ.length) (c : Clause ℕ) {e : LocalIncidence}
    (he : e ∈ (clauseGeometry φ d i c).incidenceRoutes) :
    ∀ q ∈ e.2.2, 0 ≤ q.1 ∧ q.1 ≤ 540000 ∧ 0 ≤ q.2 ∧ q.2 ≤ 540000 := by
  have hs := (clausePorts_spec hd hi).1
  obtain ⟨f, hf, rfl⟩ := List.mem_map.mp he
  dsimp only
  split_ifs with ht
  · exact collarPrefixRoute_points_bounds hs _
      (profile_prefix_incidence_points_bounds (clauseProfile c) f hf)
  · exact collarRoute_points_bounds _
      (profile_prefix_incidence_points_bounds (clauseProfile c) f hf)

/-- A common translation preserves membership in a closed local square. -/
theorem inPointBox_translate_iff (c v : Point) (radius : ℕ) (p : ℝ × ℝ) :
    inPointBox (c + v) radius (p + realPoint v) ↔ inPointBox c radius p := by
  simp only [inPointBox, Prod.fst_add, Prod.snd_add, realPoint, Int.cast_add]
  constructor <;> intro h
  all_goals
    constructor
    · linarith [h.1]
    constructor
    · linarith [h.2.1]
    constructor <;> linarith [h.2.2.1, h.2.2.2]

/-- The translated local prefix used by an actual output incidence. -/
def positiveStem (φ : CNF ℕ) (d : Graph.OrthogonalDrawing) (i : ℕ)
    (e : LocalIncidence) : Route := translate (positiveBoxOrigin φ d i) e.2.2

/-- Every real point of a local prefix lies in its source clause's closed replacement box. -/
theorem positiveStem_in_box {φ : CNF ℕ} {d : Graph.OrthogonalDrawing}
    (hd : Graph.IsPlanarOrthogonalDrawing (SAT.incidenceGraph φ) d) {i : ℕ}
    (hi : i < φ.length) (c : Clause ℕ) {e : LocalIncidence}
    (he : e ∈ (clauseGeometry φ d i c).incidenceRoutes)
    {p : ℝ × ℝ} (hp : p ∈ support (positiveStem φ d i e)) :
    inPointBox (positiveBoxOrigin φ d i + positiveTranslation) positiveRadius p := by
  rw [positiveStem, support_translate] at hp
  obtain ⟨q, hq, rfl⟩ := hp
  rw [add_comm (positiveBoxOrigin φ d i) positiveTranslation, inPointBox_translate_iff]
  apply support_inPointBox_of_points (r := e.2.2) ?_ hq
  intro a ha
  have hb := clauseGeometry_incidence_points_bounds hd hi c he a ha
  norm_num [inPointBox, positiveTranslation, positiveRadius, realPoint]
  exact_mod_cast hb

/-- The normalized inherited route remains properly orthogonal and continuously simple. -/
theorem positiveExterior_regular {φ : CNF ℕ} {d : Graph.OrthogonalDrawing}
    (hd : Graph.IsPlanarOrthogonalDrawing (SAT.incidenceGraph φ) d) {i j : ℕ}
    (hi : i < φ.length) (hj : j < φ[i].length) :
    IsOrthogonal (positiveExterior φ d i j) ∧ IsSimple (positiveExterior φ d i j) := by
  have h := exteriorRoute_regular hd (sourceEdgeIndex_lt φ hi hj)
    (by decide : positiveRadius < positiveScale)
  exact ⟨(isOrthogonal_translate_iff _ _).2 h.1, (isSimple_translate_iff _ _).2 h.2⟩

/-- The actual translated exterior route meets its own closed clause box only at the selected
local collar port. -/
theorem positiveExterior_box_contact {φ : CNF ℕ} {d : Graph.OrthogonalDrawing}
    (hd : Graph.IsPlanarOrthogonalDrawing (SAT.incidenceGraph φ) d) {i : ℕ}
    (hi : i < φ.length) (j : Fin 3) (hj : j.val < φ[i].length)
    {p : ℝ × ℝ} (hp : p ∈ support (positiveExterior φ d i j))
    (hb : inPointBox (positiveBoxOrigin φ d i + positiveTranslation) positiveRadius p) :
    p = realPoint (positiveBoxOrigin φ d i + collarOuterPort ((clausePorts φ d i).side j)) := by
  rw [positiveExterior, support_translate] at hp
  obtain ⟨q, hq, rfl⟩ := hp
  rw [inPointBox_translate_iff] at hb
  have hstart : sourceStart (SAT.incidenceGraph φ) d (sourceEdgeIndex φ i j) =
      Graph.drawingPosition (SAT.incidenceGraph φ) d (φ.distinctVars.length + i) := by
    rw [sourceStart, sourceEdgeIndex_edge φ hi hj]
  have hb' : inPointBox
      (positiveScale • sourceStart (SAT.incidenceGraph φ) d (sourceEdgeIndex φ i j))
      positiveRadius q := by simpa only [positiveBoxOrigin, hstart] using hb
  have hport := exteriorRoute_box_contact hd (sourceEdgeIndex_lt φ hi hj)
    (by decide : positiveRadius < positiveScale) hq hb'
  have hhead := positiveExterior_head hd hi j hj
  unfold positiveExterior translate at hhead
  rw [List.head?_map, (exteriorRoute_endpoints hd (sourceEdgeIndex_lt φ hi hj)
    positiveScale positiveRadius).1, Option.map_some] at hhead
  have hpoint := Option.some.inj hhead
  calc
    q + realPoint positiveTranslation =
        realPoint (exteriorPort positiveScale positiveRadius (SAT.incidenceGraph φ) d
          (sourceEdgeIndex φ i j)) + realPoint positiveTranslation :=
      congrArg (· + realPoint positiveTranslation) hport
    _ = realPoint (exteriorPort positiveScale positiveRadius (SAT.incidenceGraph φ) d
          (sourceEdgeIndex φ i j) + positiveTranslation) := (realPoint_add _ _).symm
    _ = _ := congrArg realPoint hpoint

private theorem head_join_of_some {q r : Route} {a : Point}
    (h : q.head? = some a) : (q ++ r).head? = some a := by
  obtain ⟨t, rfl⟩ := List.head?_eq_some_iff.mp h
  rfl

/-- A collared local incidence retains its clause endpoint and ends at its moved variable.
The indices remain valid in the actual collared tables. -/
theorem collaredProfile_incidence_endpoints (p : ClauseProfile)
    (h : LocalGeometry.PrefixCheck (profilePrefixGeometry p))
    {s : PortAssignment} (hs : s.Distinct) {e : LocalIncidence}
    (he : e ∈ (collaredPrefixGeometry (profilePrefixGeometry p) s).incidenceRoutes) :
    e.1 < (collaredPrefixGeometry (profilePrefixGeometry p) s).clausePositions.length ∧
      e.2.1 < (collaredPrefixGeometry (profilePrefixGeometry p) s).variablePositions.length ∧
      e.2.2.head? = some ((collaredPrefixGeometry (profilePrefixGeometry p) s).clausePosition e.1) ∧
      e.2.2.getLast? =
        some ((collaredPrefixGeometry (profilePrefixGeometry p) s).variablePosition e.2.1) := by
  obtain ⟨f, hf, rfl⟩ := List.mem_map.mp he
  have hfend := LocalGeometry.prefix_incidence_endpoints h hf
  refine ⟨by simpa only [collaredPrefixGeometry, List.length_map] using hfend.1,
    by simpa only [collaredPrefixGeometry, List.length_map, List.length_zipIdx] using hfend.2.1,
    ?_, ?_⟩
  · rw [collared_clausePoint _ _ hfend.1]
    have hhead : (collarRoute (collarReflected s) f.2.2).head? =
        some (collarPoint (collarReflected s) ((profilePrefixGeometry p).clausePosition f.1)) := by
      rw [collarRoute_eq_map, List.head?_map, hfend.2.2.1, Option.map_some]
    dsimp only
    split_ifs <;> first | exact head_join_of_some hhead | exact hhead
  · rw [collared_variablePoint _ _ hfend.2.1]
    dsimp only
    split_ifs with ht
    · have hend := hfend.2.2.2
      rw [profile_prefix_terminal_endpoint p f.2.1 ht] at hend
      have hleft : (collarRoute (collarReflected s) f.2.2).getLast? =
          some (collarInnerPort (collarReflected s)
            (terminalIndex (profilePrefixGeometry p) f.2.1)) := by
        rw [collarRoute_eq_map, List.getLast?_map, hend, Option.map_some,
          collarPoint_innerTemplatePort]
      have hright := ((collar_check s hs).2 (terminalIndex (profilePrefixGeometry p) f.2.1)).2.1
      rw [collarPrefixRoute, last_join hleft (by simpa only [List.head?_reverse] using hright),
        List.getLast?_reverse]
      exact ((collar_check s hs).2 (terminalIndex (profilePrefixGeometry p) f.2.1)).1
    · rw [collarRoute_eq_map, List.getLast?_map, hfend.2.2.2, Option.map_some]

/-- The actual translated local incidence is proper and simple, with its prescribed endpoints.
-/
theorem positiveStem_regular {φ : CNF ℕ} {d : Graph.OrthogonalDrawing}
    (hd : Graph.IsPlanarOrthogonalDrawing (SAT.incidenceGraph φ) d) {i : ℕ}
    (hi : i < φ.length) (c : Clause ℕ)
    (h : LocalGeometry.PrefixCheck (profilePrefixGeometry (clauseProfile c)))
    {e : LocalIncidence} (he : e ∈ (clauseGeometry φ d i c).incidenceRoutes) :
    IsOrthogonal (positiveStem φ d i e) ∧ IsSimple (positiveStem φ d i e) ∧
      (positiveStem φ d i e).head? =
        some (positiveBoxOrigin φ d i + (clauseGeometry φ d i c).clausePosition e.1) ∧
      (positiveStem φ d i e).getLast? =
        some (positiveBoxOrigin φ d i + (clauseGeometry φ d i c).variablePosition e.2.1) := by
  have hs := (clausePorts_spec hd hi).1
  have hept := collaredProfile_incidence_endpoints (clauseProfile c) h hs he
  refine ⟨(isOrthogonal_translate_iff _ _).2
    (collaredProfile_incidence_orthogonal _ h hs he),
    (isSimple_translate_iff _ _).2 (collaredProfile_incidence_isSimple _ h hs he), ?_, ?_⟩
  · unfold positiveStem translate
    rw [List.head?_map, hept.2.2.1, Option.map_some]
    exact congrArg some (add_comm _ _)
  · unfold positiveStem translate
    rw [List.getLast?_map, hept.2.2.2, Option.map_some]
    exact congrArg some (add_comm _ _)

/-- A local source-placeholder lookup identifies its unique terminal slot, including the
actual unmodded source position. -/
theorem profile_source_lookup (p : ClauseProfile) {v j : ℕ}
    (hv : v < (profilePrefixGeometry p).variablePositions.length)
    (hget : (profileVariables p).getD v (.inl (.inl 0)) = .inl (.inl j)) :
    j < (profileSource p).length ∧ j < 3 ∧
      v = (profileVariables p).idxOf (.inl (.inl j)) ∧
      v ∈ (profilePrefixGeometry p).terminalVariables ∧
      (terminalIndex (profilePrefixGeometry p) v).val = j := by
  have hlen : (profilePrefixGeometry p).variablePositions.length =
      (profileVariables p).length := by
    simpa only [profilePrefixGeometry, LocalGeometry.toPrefix, List.length_map,
      List.length_zipIdx] using profileGeometry_variable_length p
  have hv' : v < (profileVariables p).length := by omega
  have hget' : (profileVariables p)[v] = .inl (.inl j) := by
    simpa only [List.getD_eq_getElem _ _ hv'] using hget
  have hm : Sum.inl (Sum.inl j) ∈ profileVariables p := hget' ▸ List.getElem_mem hv'
  have hj := profileVariables_scope p _ hm
  have hp : (profileSource p).length ≤ 3 := by fin_cases p <;> decide +kernel
  have hj3 : j < 3 := by omega
  have hidx : v = (profileVariables p).idxOf (.inl (.inl j)) := by
    rw [← hget']
    exact ((CNF.nodup_distinctVars (profileFormula p)).idxOf_getElem v hv').symm
  have ht := profileSource_terminal_index p ⟨j, hj3⟩ hj
  refine ⟨hj, hj3, hidx, ?_, ?_⟩
  · rw [hidx]
    exact ht.2.1
  · change (profileGeometry p).terminalVariables.idxOf v % 3 = j
    rw [hidx, ht.2.2, Nat.mod_eq_of_lt hj3]

/-- Every actual emitted incidence is properly orthogonal and continuously simple.
Source placeholders are spliced at the sole contact of their clause box with the inherited
route; auxiliary incidences retain their finite prefix. -/
theorem positiveIncidenceRoute_regular {φ : CNF ℕ} {d : Graph.OrthogonalDrawing}
    (hd : Graph.IsPlanarOrthogonalDrawing (SAT.incidenceGraph φ) d) {i : ℕ}
    (hi : i < φ.length)
    (h : LocalGeometry.PrefixCheck (profilePrefixGeometry (clauseProfile φ[i])))
    {e : LocalIncidence} (he : e ∈ (clauseGeometry φ d i φ[i]).incidenceRoutes) :
    IsOrthogonal (positiveIncidenceRoute φ d i φ[i] e) ∧
      IsSimple (positiveIncidenceRoute φ d i φ[i] e) := by
  have hstem := positiveStem_regular hd hi φ[i] h he
  have hends := collaredProfile_incidence_endpoints (clauseProfile φ[i]) h
    (clausePorts_spec hd hi).1 he
  have hv : e.2.1 < (profilePrefixGeometry (clauseProfile φ[i])).variablePositions.length := by
    simpa only [collaredPrefixGeometry, List.length_map, List.length_zipIdx] using hends.2.1
  unfold positiveIncidenceRoute
  split
  next j hj =>
    have hm := profile_source_lookup _ hv hj
    let j' : Fin 3 := ⟨j, hm.2.1⟩
    have hjSource : j < φ[i].length :=
      lt_of_lt_of_le hm.1 (profileSource_length_le φ[i])
    have hlast : (positiveStem φ d i e).getLast? =
        some (positiveBoxOrigin φ d i + collarOuterPort ((clausePorts φ d i).side j')) := by
      rw [hstem.2.2.2, hm.2.2.1, clauseGeometry_source_point φ d i φ[i] j' hm.1]
    have hhead := positiveExterior_head hd hi j' hjSource
    have hext := positiveExterior_regular hd hi hjSource
    exact ⟨isOrthogonal_join hlast hhead hstem.1 hext.1,
      isSimple_join hlast hhead hstem.2.1 hext.2 (by
        intro z hz hw
        exact positiveExterior_box_contact hd hi j' hjSource hw
          (positiveStem_in_box hd hi φ[i] he hz))⟩
  next => exact ⟨hstem.1, hstem.2.1⟩

/-- Collaring preserves exactly the allowed local clause and auxiliary endpoint contacts.
Distinct incidences never share one of the removed source placeholders. -/
theorem collaredProfile_routes_contact (p : ClauseProfile)
    (h : LocalGeometry.PrefixCheck (profilePrefixGeometry p))
    {s : PortAssignment} (hs : s.Distinct) {e f : LocalIncidence}
    (he : e ∈ (collaredPrefixGeometry (profilePrefixGeometry p) s).incidenceRoutes)
    (hf : f ∈ (collaredPrefixGeometry (profilePrefixGeometry p) s).incidenceRoutes)
    (hne : e ≠ f) {z : ℝ × ℝ} (hz : z ∈ support e.2.2) (hw : z ∈ support f.2.2) :
    ∃ q ∈ (collaredPrefixGeometry (profilePrefixGeometry p) s).commonEndpoints e f,
      z = realPoint q := by
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp he
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hf
  have hab : a ≠ b := by intro heq; subst b; exact hne rfl
  have hz' : z ∈ support (profileCollarRoute p s a) := hz
  have hw' : z ∈ support (profileCollarRoute p s b) := hw
  obtain ⟨q, hq, hzq⟩ := profileCollarRoute_contact p h hs ha hb hab hz' hw'
  rw [LocalGeometry.commonEndpoints, List.mem_append] at hq
  rcases hq with hq | hq
  · split_ifs at hq with hc
    · simp only [List.mem_singleton] at hq
      subst q
      refine ⟨collarPoint (collarReflected s) ((profilePrefixGeometry p).clausePosition a.1),
        ?_, ?_⟩
      · apply List.mem_append_left
        simp only [hc, ↓reduceIte, List.mem_singleton]
        exact (collared_clausePoint _ _ (LocalGeometry.prefix_incidence_endpoints h hb).1).symm
      · exact hzq.trans (realPoint_collarPoint _ _).symm
    · exact False.elim (List.not_mem_nil hq)
  · split_ifs at hq with hv
    · simp only [List.mem_singleton] at hq
      subst q
      have ht := profile_prefix_shared_variable_not_terminal p ha hb hab hv
      refine ⟨collarPoint (collarReflected s) ((profilePrefixGeometry p).variablePosition a.2.1),
        ?_, ?_⟩
      · apply List.mem_append_right
        simp only [hv, ↓reduceIte, List.mem_singleton]
        rw [collared_variablePoint _ _ (LocalGeometry.prefix_incidence_endpoints h hb).2.1,
          ite_eq_right (hv ▸ ht)]
      · exact hzq.trans (realPoint_collarPoint _ _).symm
    · exact False.elim (List.not_mem_nil hq)

/-- Different local prefixes in one clause box meet only at their common actual endpoints. -/
theorem positiveStem_contacts {φ : CNF ℕ} {d : Graph.OrthogonalDrawing}
    (hd : Graph.IsPlanarOrthogonalDrawing (SAT.incidenceGraph φ) d) {i : ℕ}
    (hi : i < φ.length) (c : Clause ℕ)
    (h : LocalGeometry.PrefixCheck (profilePrefixGeometry (clauseProfile c)))
    {e f : LocalIncidence} (he : e ∈ (clauseGeometry φ d i c).incidenceRoutes)
    (hf : f ∈ (clauseGeometry φ d i c).incidenceRoutes) (hne : e ≠ f)
    {z : ℝ × ℝ} (hz : z ∈ support (positiveStem φ d i e))
    (hw : z ∈ support (positiveStem φ d i f)) :
    ∃ q ∈ (clauseGeometry φ d i c).commonEndpoints e f,
      z = realPoint (positiveBoxOrigin φ d i + q) := by
  rw [positiveStem, support_translate] at hz hw
  obtain ⟨x, hx, rfl⟩ := hz
  obtain ⟨y, hy, hyx⟩ := hw
  have hy' : y = x := add_right_cancel hyx
  subst y
  obtain ⟨q, hq, hxq⟩ := collaredProfile_routes_contact _ h (clausePorts_spec hd hi).1
    he hf hne hx hy
  refine ⟨q, hq, ?_⟩
  rw [hxq]
  change realPoint q + realPoint (positiveBoxOrigin φ d i) = _
  rw [← realPoint_add, add_comm q]

/-- Actual collared routes avoid every other local variable, including exposed source ports.
-/
theorem collaredProfile_variable_not_mem_support (p : ClauseProfile)
    (h : LocalGeometry.PrefixCheck (profilePrefixGeometry p))
    {s : PortAssignment} (hs : s.Distinct) {e : LocalIncidence}
    (he : e ∈ (collaredPrefixGeometry (profilePrefixGeometry p) s).incidenceRoutes)
    (v : Fin (profilePrefixGeometry p).variablePositions.length) (hv : v.val ≠ e.2.1) :
    realPoint ((collaredPrefixGeometry (profilePrefixGeometry p) s).variablePosition v) ∉
      support e.2.2 := by
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp he
  rw [collared_variablePoint _ _ v.isLt]
  by_cases ht : v.val ∈ (profilePrefixGeometry p).terminalVariables
  · rw [ite_eq_left ht]
    exact profileCollarRoute_source_not_mem_support p h hs ha ht hv
  · rw [ite_eq_right ht]
    exact profileCollarRoute_auxiliary_not_mem_support p h hs ha v ht hv

/-- Actual collared routes avoid every other local clause vertex. -/
theorem collaredProfile_clause_not_mem_support (p : ClauseProfile)
    (h : LocalGeometry.PrefixCheck (profilePrefixGeometry p))
    {s : PortAssignment} (hs : s.Distinct) {e : LocalIncidence}
    (he : e ∈ (collaredPrefixGeometry (profilePrefixGeometry p) s).incidenceRoutes)
    (j : Fin (profilePrefixGeometry p).clausePositions.length) (hj : j.val ≠ e.1) :
    realPoint ((collaredPrefixGeometry (profilePrefixGeometry p) s).clausePosition j) ∉
      support e.2.2 := by
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp he
  rw [collared_clausePoint _ _ j.isLt]
  exact profileCollarRoute_clause_not_mem_support p h hs ha j hj

/-- Distinct local incidences cannot contact the source port of one another. -/
theorem collaredProfile_other_terminal_not_mem_support (p : ClauseProfile)
    (h : LocalGeometry.PrefixCheck (profilePrefixGeometry p))
    {s : PortAssignment} (hs : s.Distinct) {e f : LocalIncidence}
    (he : e ∈ (collaredPrefixGeometry (profilePrefixGeometry p) s).incidenceRoutes)
    (hf : f ∈ (collaredPrefixGeometry (profilePrefixGeometry p) s).incidenceRoutes)
    (hne : e ≠ f) (ht : f.2.1 ∈ (profilePrefixGeometry p).terminalVariables) :
    realPoint ((collaredPrefixGeometry (profilePrefixGeometry p) s).variablePosition f.2.1) ∉
      support e.2.2 := by
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp he
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hf
  have hv : b.2.1 ≠ a.2.1 := by
    intro hv
    have hab := profile_prefix_terminal_unique p b hb ht a ha hv
    subst a
    exact hne rfl
  exact collaredProfile_variable_not_mem_support p h hs (List.mem_map_of_mem ha)
    ⟨b.2.1, profile_prefix_terminal_lt p _ ht⟩ hv

/-- A translated local incidence avoids the exposed endpoint of every other incidence. -/
theorem positiveStem_other_terminal_not_mem_support {φ : CNF ℕ}
    {d : Graph.OrthogonalDrawing}
    (hd : Graph.IsPlanarOrthogonalDrawing (SAT.incidenceGraph φ) d) {i : ℕ}
    (hi : i < φ.length) (c : Clause ℕ)
    (h : LocalGeometry.PrefixCheck (profilePrefixGeometry (clauseProfile c)))
    {e f : LocalIncidence} (he : e ∈ (clauseGeometry φ d i c).incidenceRoutes)
    (hf : f ∈ (clauseGeometry φ d i c).incidenceRoutes) (hne : e ≠ f)
    (ht : f.2.1 ∈ (profilePrefixGeometry (clauseProfile c)).terminalVariables) :
    realPoint (positiveBoxOrigin φ d i + (clauseGeometry φ d i c).variablePosition f.2.1) ∉
      support (positiveStem φ d i e) := by
  have hn := collaredProfile_other_terminal_not_mem_support _ h (clausePorts_spec hd hi).1
    he hf hne ht
  intro hz
  rw [positiveStem, support_translate] at hz
  obtain ⟨x, hx, hxp⟩ := hz
  have hx' : x = realPoint ((clauseGeometry φ d i c).variablePosition f.2.1) := by
    apply add_right_cancel (b := realPoint (positiveBoxOrigin φ d i))
    simpa only [realPoint_add, add_comm (realPoint (positiveBoxOrigin φ d i))] using hxp
  exact hn (hx' ▸ hx)

/-- Inside one clause box, an inherited exterior is disjoint from every other local prefix.
The shared clause center has already been cut away. -/
theorem positiveStem_other_exterior_disjoint {φ : CNF ℕ} {d : Graph.OrthogonalDrawing}
    (hd : Graph.IsPlanarOrthogonalDrawing (SAT.incidenceGraph φ) d) {i : ℕ}
    (hi : i < φ.length)
    (h : LocalGeometry.PrefixCheck (profilePrefixGeometry (clauseProfile φ[i])))
    {e f : LocalIncidence} (he : e ∈ (clauseGeometry φ d i φ[i]).incidenceRoutes)
    (hf : f ∈ (clauseGeometry φ d i φ[i]).incidenceRoutes) (hne : e ≠ f) {j : ℕ}
    (hget : (profileVariables (clauseProfile φ[i])).getD f.2.1 (.inl (.inl 0)) =
      .inl (.inl j)) :
    Disjoint (support (positiveStem φ d i e)) (support (positiveExterior φ d i j)) := by
  have hends := collaredProfile_incidence_endpoints _ h (clausePorts_spec hd hi).1 hf
  have hv : f.2.1 < (profilePrefixGeometry (clauseProfile φ[i])).variablePositions.length := by
    simpa only [collaredPrefixGeometry, List.length_map, List.length_zipIdx] using hends.2.1
  have hm := profile_source_lookup _ hv hget
  let j' : Fin 3 := ⟨j, hm.2.1⟩
  have hj : j < φ[i].length := lt_of_lt_of_le hm.1 (profileSource_length_le φ[i])
  rw [Set.disjoint_left]
  intro z hz hw
  have hzport := positiveExterior_box_contact hd hi j' hj hw
    (positiveStem_in_box hd hi φ[i] he hz)
  have hpoint : (clauseGeometry φ d i φ[i]).variablePosition f.2.1 =
      collarOuterPort ((clausePorts φ d i).side j') := by
    rw [hm.2.2.1, clauseGeometry_source_point φ d i φ[i] j' hm.1]
  apply positiveStem_other_terminal_not_mem_support hd hi φ[i] h he hf hne hm.2.2.2.1
  rw [hpoint, ← hzport]
  exact hz

/-- A source incidence's finite stem and inherited exterior have the same actual integer
endpoint. This identity also supports exact wire-length and segment-count bookkeeping. -/
theorem positiveIncidenceRoute_join_endpoints {φ : CNF ℕ} {d : Graph.OrthogonalDrawing}
    (hd : Graph.IsPlanarOrthogonalDrawing (SAT.incidenceGraph φ) d) {i : ℕ}
    (hi : i < φ.length)
    (h : LocalGeometry.PrefixCheck (profilePrefixGeometry (clauseProfile φ[i])))
    {e : LocalIncidence} (he : e ∈ (clauseGeometry φ d i φ[i]).incidenceRoutes) {j : ℕ}
    (hget : (profileVariables (clauseProfile φ[i])).getD e.2.1 (.inl (.inl 0)) =
      .inl (.inl j)) :
    ∃ q : Point, (positiveStem φ d i e).getLast? = some q ∧
      (positiveExterior φ d i j).head? = some q := by
  have hends := collaredProfile_incidence_endpoints _ h (clausePorts_spec hd hi).1 he
  have hv : e.2.1 < (profilePrefixGeometry (clauseProfile φ[i])).variablePositions.length := by
    simpa only [collaredPrefixGeometry, List.length_map, List.length_zipIdx] using hends.2.1
  have hm := profile_source_lookup _ hv hget
  let j' : Fin 3 := ⟨j, hm.2.1⟩
  have hj : j < φ[i].length := lt_of_lt_of_le hm.1 (profileSource_length_le φ[i])
  refine ⟨positiveBoxOrigin φ d i + collarOuterPort ((clausePorts φ d i).side j'), ?_,
    positiveExterior_head hd hi j' hj⟩
  rw [(positiveStem_regular hd hi φ[i] h he).2.2.2, hm.2.2.1,
    clauseGeometry_source_point φ d i φ[i] j' hm.1]

end Cslib.Complexity.SAT.ExactOne
