/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.SAT.ExactOne.GeometryProfilesPrefixData
public import Complexity.Computability.Complexity.Problems.SAT.ExactOne.GeometryProfiles
public import Complexity.Computability.Complexity.Problems.SAT.ExactOne.GeometryCollarGlue

/-!
# Collared positive exact-one profiles

The twenty-four ordered injections into the four exterior directions are handled by the common
annular collars. All geometry proofs reuse the fifteen inner-profile certificates and the
twenty-four collar certificates; they do not repeat an exhaustive route-pair audit for every
combination.

## Main results

* `collaredProfile_incidence_orthogonal`, `collaredProfile_incidence_isSimple`: actual placed
  incidence routes remain proper and continuously simple.

## References

These are original continuous gluing certificates for the exact-one replacement profiles.
-/

@[expose] public section

namespace Cslib.Complexity.SAT.ExactOne

open Orthogonal

/-- Every source endpoint of the actual inner prefix is its indexed north, west or east port. -/
theorem profile_prefix_terminal_endpoint (p : ClauseProfile) :
    ∀ v ∈ (profilePrefixGeometry p).terminalVariables,
      (profilePrefixGeometry p).variablePosition v =
        innerTemplatePort (terminalIndex (profilePrefixGeometry p) v) := by
  fin_cases p <;> decide +kernel

/-- Distinct exposed source variables have distinct collar indices. -/
theorem profile_prefix_terminalIndex_injective (p : ClauseProfile) :
    ∀ v ∈ (profilePrefixGeometry p).terminalVariables,
      ∀ w ∈ (profilePrefixGeometry p).terminalVariables,
        terminalIndex (profilePrefixGeometry p) v =
          terminalIndex (profilePrefixGeometry p) w → v = w := by
  fin_cases p <;> decide +kernel

/-- Every source placeholder has a valid local variable index. -/
theorem profile_prefix_terminal_lt (p : ClauseProfile) :
    ∀ v ∈ (profilePrefixGeometry p).terminalVariables,
      v < (profilePrefixGeometry p).variablePositions.length := by
  fin_cases p <;> decide +kernel

/-- Every listed variable of the inner template lies in its closed square. -/
theorem profile_prefix_variable_bounds (p : ClauseProfile) :
    ∀ v : Fin (profilePrefixGeometry p).variablePositions.length,
      let q := (profilePrefixGeometry p).variablePosition v
      0 ≤ q.1 ∧ q.1 ≤ 180000 ∧ 0 ≤ q.2 ∧ q.2 ≤ 180000 := by
  fin_cases p <;> decide +kernel

/-- An auxiliary variable never occupies a source boundary port. -/
theorem profile_prefix_auxiliary_ne_terminal (p : ClauseProfile) :
    ∀ v : Fin (profilePrefixGeometry p).variablePositions.length,
      v.val ∉ (profilePrefixGeometry p).terminalVariables →
        ∀ w ∈ (profilePrefixGeometry p).terminalVariables,
          (profilePrefixGeometry p).variablePosition v ≠
            (profilePrefixGeometry p).variablePosition w := by
  fin_cases p <;> decide +kernel

/-- Every listed clause position lies in the inner template's closed square. -/
theorem profile_prefix_clause_bounds (p : ClauseProfile) :
    ∀ i : Fin (profilePrefixGeometry p).clausePositions.length,
      let q := (profilePrefixGeometry p).clausePosition i
      0 ≤ q.1 ∧ q.1 ≤ 180000 ∧ 0 ≤ q.2 ∧ q.2 ≤ 180000 := by
  fin_cases p <;> decide +kernel

/-- All listed incidence points lie in the inner square, independently of the expensive
continuous pair-contact certificate. -/
theorem profile_prefix_incidence_points_bounds (p : ClauseProfile) :
    ∀ e ∈ (profilePrefixGeometry p).incidenceRoutes,
      ∀ q ∈ e.2.2, 0 ≤ q.1 ∧ q.1 ≤ 180000 ∧ 0 ≤ q.2 ∧ q.2 ≤ 180000 := by
  fin_cases p <;> decide +kernel

/-- No clause vertex occupies a source boundary port. -/
theorem profile_prefix_clause_ne_terminal (p : ClauseProfile) :
    ∀ i : Fin (profilePrefixGeometry p).clausePositions.length,
      ∀ w ∈ (profilePrefixGeometry p).terminalVariables,
        (profilePrefixGeometry p).clausePosition i ≠
          (profilePrefixGeometry p).variablePosition w := by
  fin_cases p <;> decide +kernel

/-- Each source placeholder belongs to exactly one local incidence. -/
theorem profile_prefix_terminal_unique (p : ClauseProfile) :
    ∀ e ∈ (profilePrefixGeometry p).incidenceRoutes,
      e.2.1 ∈ (profilePrefixGeometry p).terminalVariables →
        ∀ f ∈ (profilePrefixGeometry p).incidenceRoutes, e.2.1 = f.2.1 → e = f := by
  fin_cases p <;> decide +kernel

/-- Two different incidences can share only an actual auxiliary variable, never a source
placeholder that will be removed by the global drawing compiler. -/
theorem profile_prefix_shared_variable_not_terminal (p : ClauseProfile)
    {e f : LocalIncidence} (he : e ∈ (profilePrefixGeometry p).incidenceRoutes)
    (hf : f ∈ (profilePrefixGeometry p).incidenceRoutes) (hne : e ≠ f)
    (hv : e.2.1 = f.2.1) : e.2.1 ∉ (profilePrefixGeometry p).terminalVariables := by
  intro ht
  exact hne (profile_prefix_terminal_unique p e he ht f hf hv)

/-- The finite route actually used by the collared incidence constructor. -/
def profileCollarRoute (p : ClauseProfile) (s : PortAssignment) (e : LocalIncidence) : Route :=
  if e.2.1 ∈ (profilePrefixGeometry p).terminalVariables then
    collarPrefixRoute s (terminalIndex (profilePrefixGeometry p) e.2.1) e.2.2
  else collarRoute (collarReflected s) e.2.2

/-- Every actual inner prefix lies in the common side-180000 square. -/
theorem profile_prefix_incidence_bounds (p : ClauseProfile)
    (h : LocalGeometry.PrefixCheck (profilePrefixGeometry p))
    {e : LocalIncidence} (he : e ∈ (profilePrefixGeometry p).incidenceRoutes) :
    ∀ q ∈ e.2.2, 0 ≤ q.1 ∧ q.1 ≤ 180000 ∧ 0 ≤ q.2 ∧ q.2 ≤ 180000 := by
  have hsize : (profilePrefixGeometry p).size = 180000 :=
    (profileGeometry_costs p).2.2
  simpa only [hsize, Nat.cast_ofNat] using LocalGeometry.prefix_incidence_bounds h he

/-- The actual collared incidence routes are properly orthogonal in every ordered port
assignment. The profile certificate is supplied separately to keep the data compiler lightweight.
-/
theorem collaredProfile_incidence_orthogonal (p : ClauseProfile)
    (h : LocalGeometry.PrefixCheck (profilePrefixGeometry p))
    {s : PortAssignment} (hs : s.Distinct) {e : LocalIncidence}
    (he : e ∈ (collaredPrefixGeometry (profilePrefixGeometry p) s).incidenceRoutes) :
    IsOrthogonal e.2.2 := by
  obtain ⟨f, hf, rfl⟩ := List.mem_map.mp he
  dsimp only
  split_ifs with ht
  · have hend := (LocalGeometry.prefix_incidence_endpoints h hf).2.2.2
    rw [profile_prefix_terminal_endpoint p f.2.1 ht] at hend
    exact isOrthogonal_collarPrefixRoute hs hend
      (LocalGeometry.prefix_incidence_orthogonal h hf)
  · exact isOrthogonal_collarRoute _ (LocalGeometry.prefix_incidence_orthogonal h hf)

/-- The actual collared incidence routes are simple over their full real support. -/
theorem collaredProfile_incidence_isSimple (p : ClauseProfile)
    (h : LocalGeometry.PrefixCheck (profilePrefixGeometry p))
    {s : PortAssignment} (hs : s.Distinct) {e : LocalIncidence}
    (he : e ∈ (collaredPrefixGeometry (profilePrefixGeometry p) s).incidenceRoutes) :
    IsSimple e.2.2 := by
  obtain ⟨f, hf, rfl⟩ := List.mem_map.mp he
  dsimp only
  split_ifs with ht
  · have hend := (LocalGeometry.prefix_incidence_endpoints h hf).2.2.2
    rw [profile_prefix_terminal_endpoint p f.2.1 ht] at hend
    exact isSimple_collarPrefixRoute hs hend (LocalGeometry.prefix_incidence_isSimple h hf)
      (profile_prefix_incidence_bounds p h hf)
  · exact isSimple_collarRoute _ (LocalGeometry.prefix_incidence_isSimple h hf)

private theorem profile_collar_core_contact (p : ClauseProfile)
    (h : LocalGeometry.PrefixCheck (profilePrefixGeometry p))
    {s : PortAssignment} {e f : LocalIncidence}
    (he : e ∈ (profilePrefixGeometry p).incidenceRoutes)
    (hf : f ∈ (profilePrefixGeometry p).incidenceRoutes) (hne : e ≠ f)
    {z : ℝ × ℝ} (hz : z ∈ support (collarRoute (collarReflected s) e.2.2))
    (hw : z ∈ support (collarRoute (collarReflected s) f.2.2)) :
    ∃ q ∈ (profilePrefixGeometry p).commonEndpoints e f,
      z = collarReal (collarReflected s) (realPoint q) := by
  rw [support_collarRoute] at hz hw
  obtain ⟨x, hx, hxz⟩ := hz
  obtain ⟨y, hy, hyz⟩ := hw
  have hxy := collarReal_injective (collarReflected s) (hxz.trans hyz.symm)
  subst y
  obtain ⟨q, hq, hxq⟩ := LocalGeometry.prefix_routes_contact h he hf hne hx hy
  exact ⟨q, hq, hxz.symm.trans (congrArg (collarReal (collarReflected s)) hxq)⟩

private theorem profile_collar_connector_disjoint (p : ClauseProfile)
    (h : LocalGeometry.PrefixCheck (profilePrefixGeometry p))
    {s : PortAssignment} (hs : s.Distinct) {e f : LocalIncidence}
    (he : e ∈ (profilePrefixGeometry p).incidenceRoutes)
    (hf : f ∈ (profilePrefixGeometry p).incidenceRoutes)
    (ht : f.2.1 ∈ (profilePrefixGeometry p).terminalVariables) (hv : f.2.1 ≠ e.2.1) :
    Disjoint (support (collarRoute (collarReflected s) e.2.2))
      (support ((collarRoutes s).getD (terminalIndex (profilePrefixGeometry p) f.2.1) [])) := by
  apply disjoint_collarRoute_connector hs (profile_prefix_incidence_bounds p h he)
  rw [← profile_prefix_terminal_endpoint p f.2.1 ht]
  exact LocalGeometry.prefix_variable_not_mem_support h he
    (v := ⟨f.2.1, (LocalGeometry.prefix_incidence_endpoints h hf).2.1⟩) hv

/-- The annular connectors introduce no new contacts between different incidence routes.
Every contact is the common affine placement of an original permitted local endpoint. -/
theorem profileCollarRoute_contact (p : ClauseProfile)
    (h : LocalGeometry.PrefixCheck (profilePrefixGeometry p))
    {s : PortAssignment} (hs : s.Distinct) {e f : LocalIncidence}
    (he : e ∈ (profilePrefixGeometry p).incidenceRoutes)
    (hf : f ∈ (profilePrefixGeometry p).incidenceRoutes) (hne : e ≠ f)
    {z : ℝ × ℝ} (hz : z ∈ support (profileCollarRoute p s e))
    (hw : z ∈ support (profileCollarRoute p s f)) :
    ∃ q ∈ (profilePrefixGeometry p).commonEndpoints e f,
      z = collarReal (collarReflected s) (realPoint q) := by
  have hve (ht : e.2.1 ∈ (profilePrefixGeometry p).terminalVariables) : e.2.1 ≠ f.2.1 := by
    intro hv
    exact profile_prefix_shared_variable_not_terminal p he hf hne hv ht
  have hvf (ht : f.2.1 ∈ (profilePrefixGeometry p).terminalVariables) : f.2.1 ≠ e.2.1 := by
    intro hv
    exact profile_prefix_shared_variable_not_terminal p hf he (Ne.symm hne) hv ht
  unfold profileCollarRoute at hz hw
  split_ifs at hz with hte <;> split_ifs at hw with htf
  · have hle := (LocalGeometry.prefix_incidence_endpoints h he).2.2.2
    have hlf := (LocalGeometry.prefix_incidence_endpoints h hf).2.2.2
    rw [profile_prefix_terminal_endpoint p e.2.1 hte] at hle
    rw [profile_prefix_terminal_endpoint p f.2.1 htf] at hlf
    have hidx : terminalIndex (profilePrefixGeometry p) e.2.1 ≠
        terminalIndex (profilePrefixGeometry p) f.2.1 := by
      intro heq
      exact hve hte (profile_prefix_terminalIndex_injective p e.2.1 hte f.2.1 htf heq)
    obtain ⟨q, hqe, hqf, hzq⟩ := collarPrefixRoute_contact hs hidx hle hlf
      (profile_prefix_incidence_bounds p h he) (profile_prefix_incidence_bounds p h hf)
      (by
        rw [← profile_prefix_terminal_endpoint p f.2.1 htf]
        exact LocalGeometry.prefix_variable_not_mem_support h he
          (v := ⟨f.2.1, (LocalGeometry.prefix_incidence_endpoints h hf).2.1⟩) (hvf htf))
      (by
        rw [← profile_prefix_terminal_endpoint p e.2.1 hte]
        exact LocalGeometry.prefix_variable_not_mem_support h hf
          (v := ⟨e.2.1, (LocalGeometry.prefix_incidence_endpoints h he).2.1⟩) (hve hte)) hz hw
    obtain ⟨a, ha, hqa⟩ := LocalGeometry.prefix_routes_contact h he hf hne hqe hqf
    exact ⟨a, ha, hzq.trans (congrArg (collarReal (collarReflected s)) hqa)⟩
  · have hle := (LocalGeometry.prefix_incidence_endpoints h he).2.2.2
    rw [profile_prefix_terminal_endpoint p e.2.1 hte] at hle
    rw [support_collarPrefixRoute hs hle] at hz
    rcases hz with hz | hz
    · exact profile_collar_core_contact p h he hf hne hz hw
    · exact False.elim (Set.disjoint_left.mp
        (profile_collar_connector_disjoint p h hs hf he hte (hve hte)) hw hz)
  · have hlf := (LocalGeometry.prefix_incidence_endpoints h hf).2.2.2
    rw [profile_prefix_terminal_endpoint p f.2.1 htf] at hlf
    rw [support_collarPrefixRoute hs hlf] at hw
    rcases hw with hw | hw
    · exact profile_collar_core_contact p h he hf hne hz hw
    · exact False.elim (Set.disjoint_left.mp
        (profile_collar_connector_disjoint p h hs he hf htf (hvf htf)) hz hw)
  · exact profile_collar_core_contact p h he hf hne hz hw

/-- A collared incidence avoids every nonincident actual auxiliary vertex. -/
theorem profileCollarRoute_auxiliary_not_mem_support (p : ClauseProfile)
    (h : LocalGeometry.PrefixCheck (profilePrefixGeometry p))
    {s : PortAssignment} (hs : s.Distinct) {e : LocalIncidence}
    (he : e ∈ (profilePrefixGeometry p).incidenceRoutes)
    (v : Fin (profilePrefixGeometry p).variablePositions.length)
    (ht : v.val ∉ (profilePrefixGeometry p).terminalVariables) (hv : v.val ≠ e.2.1) :
    realPoint (collarPoint (collarReflected s) ((profilePrefixGeometry p).variablePosition v)) ∉
      support (profileCollarRoute p s e) := by
  have hn := LocalGeometry.prefix_variable_not_mem_support h he (v := v) hv
  unfold profileCollarRoute
  split_ifs with hsource
  · have hend := (LocalGeometry.prefix_incidence_endpoints h he).2.2.2
    rw [profile_prefix_terminal_endpoint p e.2.1 hsource] at hend
    apply collarPrefixRoute_not_mem_corePoint hs hend (profile_prefix_variable_bounds p v)
      ?_ hn
    rw [← profile_prefix_terminal_endpoint p e.2.1 hsource]
    exact profile_prefix_auxiliary_ne_terminal p v ht e.2.1 hsource
  · rw [realPoint_collarPoint]
    exact fun hp => hn ((mem_support_collarRoute_iff _ _ _).mp hp)

/-- A collared incidence avoids every nonincident actual clause vertex. -/
theorem profileCollarRoute_clause_not_mem_support (p : ClauseProfile)
    (h : LocalGeometry.PrefixCheck (profilePrefixGeometry p))
    {s : PortAssignment} (hs : s.Distinct) {e : LocalIncidence}
    (he : e ∈ (profilePrefixGeometry p).incidenceRoutes)
    (i : Fin (profilePrefixGeometry p).clausePositions.length) (hi : i.val ≠ e.1) :
    realPoint (collarPoint (collarReflected s) ((profilePrefixGeometry p).clausePosition i)) ∉
      support (profileCollarRoute p s e) := by
  have hn := LocalGeometry.prefix_clause_not_mem_support h he (i := i) hi
  unfold profileCollarRoute
  split_ifs with hsource
  · have hend := (LocalGeometry.prefix_incidence_endpoints h he).2.2.2
    rw [profile_prefix_terminal_endpoint p e.2.1 hsource] at hend
    apply collarPrefixRoute_not_mem_corePoint hs hend (profile_prefix_clause_bounds p i) ?_ hn
    rw [← profile_prefix_terminal_endpoint p e.2.1 hsource]
    exact profile_prefix_clause_ne_terminal p i e.2.1 hsource
  · rw [realPoint_collarPoint]
    exact fun hp => hn ((mem_support_collarRoute_iff _ _ _).mp hp)

/-- A collared incidence avoids every other exposed source endpoint. -/
theorem profileCollarRoute_source_not_mem_support (p : ClauseProfile)
    (h : LocalGeometry.PrefixCheck (profilePrefixGeometry p))
    {s : PortAssignment} (hs : s.Distinct) {e : LocalIncidence}
    (he : e ∈ (profilePrefixGeometry p).incidenceRoutes) {v : ℕ}
    (ht : v ∈ (profilePrefixGeometry p).terminalVariables) (hv : v ≠ e.2.1) :
    realPoint (collarOuterPort (s.side (terminalIndex (profilePrefixGeometry p) v))) ∉
      support (profileCollarRoute p s e) := by
  let i := terminalIndex (profilePrefixGeometry p) v
  have hhead := ((collar_check s hs).2 i).1
  have hm : collarOuterPort (s.side i) ∈ (collarRoutes s).getD i [] := by
    cases hr : (collarRoutes s).getD i [] with
    | nil => rw [hr] at hhead; cases hhead
    | cons a as =>
      have ha : a = collarOuterPort (s.side i) := by
        rw [hr] at hhead
        exact Option.some.inj hhead
      rw [← ha]
      exact List.mem_cons_self
  have hsupp : realPoint (collarOuterPort (s.side i)) ∈
      support ((collarRoutes s).getD i []) := Or.inl ⟨_, hm, rfl⟩
  have hd : Disjoint (support (collarRoute (collarReflected s) e.2.2))
      (support ((collarRoutes s).getD i [])) := by
    apply disjoint_collarRoute_connector hs (profile_prefix_incidence_bounds p h he)
    rw [← profile_prefix_terminal_endpoint p v ht]
    exact LocalGeometry.prefix_variable_not_mem_support h he
      (v := ⟨v, profile_prefix_terminal_lt p v ht⟩) hv
  intro hp
  unfold profileCollarRoute at hp
  split_ifs at hp with heterm
  · have hend := (LocalGeometry.prefix_incidence_endpoints h he).2.2.2
    rw [profile_prefix_terminal_endpoint p e.2.1 heterm] at hend
    rw [support_collarPrefixRoute hs hend] at hp
    rcases hp with hp | hp
    · exact Set.disjoint_left.mp hd hp hsupp
    · have hi : terminalIndex (profilePrefixGeometry p) e.2.1 ≠ i := by
        intro hi
        exact hv (profile_prefix_terminalIndex_injective p e.2.1 heterm v ht hi).symm
      exact Set.disjoint_left.mp (collar_disjoint hs hi) hp hsupp
  · exact Set.disjoint_left.mp hd hp hsupp

/-- A collared route can touch the complete outer perimeter only at its own source endpoint;
an incidence to an internal auxiliary never touches that perimeter. -/
theorem profileCollarRoute_outer_boundary_contact (p : ClauseProfile)
    (h : LocalGeometry.PrefixCheck (profilePrefixGeometry p))
    {s : PortAssignment} (hs : s.Distinct) {e : LocalIncidence}
    (he : e ∈ (profilePrefixGeometry p).incidenceRoutes)
    {z : ℝ × ℝ} (hz : z ∈ support (profileCollarRoute p s e))
    (hb : z ∈ support collarBoundaryRoute) :
    e.2.1 ∈ (profilePrefixGeometry p).terminalVariables ∧
      z = realPoint (collarOuterPort (s.side (terminalIndex (profilePrefixGeometry p) e.2.1))) := by
  unfold profileCollarRoute at hz
  split_ifs at hz with ht
  · have hend := (LocalGeometry.prefix_incidence_endpoints h he).2.2.2
    rw [profile_prefix_terminal_endpoint p e.2.1 ht] at hend
    exact ⟨ht, collarPrefixRoute_outer_boundary_contact hs hend
      (profile_prefix_incidence_bounds p h he) hz hb⟩
  · have hcheck : routeBoxContactCheck [] collarBoundaryRoute (270000, 270000) 90000 =
        true := by decide +kernel
    obtain ⟨q, hq, _⟩ := routeBoxContactCheck_sound hcheck hb
      (collarRoute_in_innerBox _ (profile_prefix_incidence_bounds p h he) hz)
    exact False.elim (List.not_mem_nil hq)

/-- If every point of a route lies in the `180000`-by-`180000` inner square, then every point of
its collared route lies in the `540000`-by-`540000` outer square. -/
theorem collarRoute_points_bounds (reflected : Bool) {r : Route}
    (hr : ∀ q ∈ r, 0 ≤ q.1 ∧ q.1 ≤ 180000 ∧ 0 ≤ q.2 ∧ q.2 ≤ 180000) :
    ∀ q ∈ collarRoute reflected r,
      0 ≤ q.1 ∧ q.1 ≤ 540000 ∧ 0 ≤ q.2 ∧ q.2 ≤ 540000 := by
  intro q hq
  rw [collarRoute_eq_map] at hq
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hq
  have hb := hr a ha
  cases reflected <;> dsimp [collarPoint, collarOffset, mirrorPoint] <;> omega

end Cslib.Complexity.SAT.ExactOne
