/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.SAT.ExactOne.DrawingRoutes
public import Complexity.Computability.Complexity.Problems.SAT.ExactOne.DrawingVertexBoxes
public import Complexity.Computability.Complexity.Problems.SAT.ExactOne.DrawingPositionLookup
import Mathlib.Data.List.GetD

/-!
# Global continuous contacts of the actual positive incidence routes

## Main results

* `positiveStem_different_boxes_disjoint`: closed replacement boxes stay disjoint.
* `positiveStem_foreign_exterior_disjoint`: exterior routes avoid other clause boxes.
* `positiveIncidenceRoute_endpoints`: actual clause and globally shared variable endpoints.
* `positiveIncidenceRoute_contacts`: full real-support contacts only at actual common endpoints.

## References

These continuous route-composition proofs are original.
-/

@[expose] public section

namespace Cslib.Complexity.SAT.ExactOne

open Cslib.Logic.PL Orthogonal

/-- Local prefixes belonging to different original clauses have disjoint full supports. -/
theorem positiveStem_different_boxes_disjoint {φ : CNF ℕ} {d : Graph.OrthogonalDrawing}
    (hd : Graph.IsPlanarOrthogonalDrawing (SAT.incidenceGraph φ) d) {i j : ℕ}
    (hi : i < φ.length) (hj : j < φ.length) (hij : i ≠ j)
    (c c' : Clause ℕ) {e f : LocalIncidence}
    (he : e ∈ (clauseGeometry φ d i c).incidenceRoutes)
    (hf : f ∈ (clauseGeometry φ d j c').incidenceRoutes) :
    Disjoint (support (positiveStem φ d i e)) (support (positiveStem φ d j f)) := by
  rw [Set.disjoint_left]
  intro z hz hw
  have hb := positiveStem_in_box hd hi c he hz
  have hc := positiveStem_in_box hd hj c' hf hw
  have hb' : inPointBox (positiveBoxOrigin φ d i) positiveRadius
      (z - realPoint positiveTranslation) := by
    apply (inPointBox_translate_iff _ positiveTranslation _ _).mp
    simpa only [sub_add_cancel] using hb
  have hc' : inPointBox (positiveBoxOrigin φ d j) positiveRadius
      (z - realPoint positiveTranslation) := by
    apply (inPointBox_translate_iff _ positiveTranslation _ _).mp
    simpa only [sub_add_cancel] using hc
  have heq := eq_of_inPointBoxes (by decide : 2 * positiveRadius < positiveScale) hb' hc'
  have hlabels := drawingPosition_injOn hd (sourceClause_declared φ hi)
    (sourceClause_declared φ hj) heq
  exact hij (Nat.add_left_cancel hlabels)

/-- An inherited exterior route avoids every other original clause's entire closed box. -/
theorem positiveExterior_foreign_box {φ : CNF ℕ} {d : Graph.OrthogonalDrawing}
    (hd : Graph.IsPlanarOrthogonalDrawing (SAT.incidenceGraph φ) d) {i j k : ℕ}
    (hi : i < φ.length) (hj : j < φ.length) (hk : k < φ[j].length) (hij : i ≠ j)
    {z : ℝ × ℝ} (hz : z ∈ support (positiveExterior φ d j k)) :
    ¬ inPointBox (positiveBoxOrigin φ d i + positiveTranslation) positiveRadius z := by
  rw [positiveExterior, support_translate] at hz
  obtain ⟨x, hx, rfl⟩ := hz
  rw [inPointBox_translate_iff]
  have hindex := sourceEdgeIndex_lt φ hj hk
  have hedge : (SAT.incidenceGraph φ).2[sourceEdgeIndex φ j k] =
      (φ.distinctVars.idxOf φ[j][k].1, φ.distinctVars.length + j) := by
    rw [← List.getD_eq_getElem _ _ hindex]
    exact sourceEdgeIndex_edge φ hj hk
  apply exteriorRoute_avoids_box hd hindex (sourceClause_declared φ hi) ?_ ?_
    (by decide : positiveRadius < positiveScale) hx
  · rw [hedge]
    have hv : φ[j][k].1 ∈ φ.distinctVars := CNF.mem_distinctVars.mpr (CNF.mem_vars.mpr
      ⟨φ[j], List.getElem_mem hj, φ[j][k].2, List.getElem_mem hk⟩)
    have hlt := List.idxOf_lt_length_of_mem hv
    omega
  · rw [hedge]
    omega

/-- A finite local prefix and an inherited route from another clause are disjoint. -/
theorem positiveStem_foreign_exterior_disjoint {φ : CNF ℕ}
    {d : Graph.OrthogonalDrawing}
    (hd : Graph.IsPlanarOrthogonalDrawing (SAT.incidenceGraph φ) d) {i j k : ℕ}
    (hi : i < φ.length) (hj : j < φ.length) (hk : k < φ[j].length) (hij : i ≠ j)
    (c : Clause ℕ) {e : LocalIncidence}
    (he : e ∈ (clauseGeometry φ d i c).incidenceRoutes) :
    Disjoint (support (positiveStem φ d i e)) (support (positiveExterior φ d j k)) := by
  rw [Set.disjoint_left]
  intro z hz hw
  exact positiveExterior_foreign_box hd hi hj hk hij hw (positiveStem_in_box hd hi c he hz)

/-- The actual global variable attached to one local incidence row. -/
def positiveIncidenceVariable (φ : CNF ℕ) (i : ℕ) (c : Clause ℕ)
    (e : LocalIncidence) : CNF.PositiveExactOneCompile.Variable ℕ :=
  profileVariableMap i (CNF.PositiveExactOneCompile.signedOffset φ i) c
    ((profileVariables (clauseProfile c)).getD e.2.1 (.inl (.inl 0)))

/-- Actual emitted incidences have their specified local clause and globally shared variable
endpoints. Private variables resolve through the actual finite position table. -/
theorem positiveIncidenceRoute_endpoints {φ : CNF ℕ} {d : Graph.OrthogonalDrawing}
    (hd : Graph.IsPlanarOrthogonalDrawing (SAT.incidenceGraph φ) d) {i : ℕ}
    (hi : i < φ.length)
    (h : LocalGeometry.PrefixCheck (profilePrefixGeometry (clauseProfile φ[i])))
    {e : LocalIncidence} (he : e ∈ (clauseGeometry φ d i φ[i]).incidenceRoutes) :
    (positiveIncidenceRoute φ d i φ[i] e).head? =
        some (positiveBoxOrigin φ d i + (clauseGeometry φ d i φ[i]).clausePosition e.1) ∧
      (positiveIncidenceRoute φ d i φ[i] e).getLast? =
        some (positiveVariablePoint φ d (positiveIncidenceVariable φ i φ[i] e)) := by
  have hstem := positiveStem_regular hd hi φ[i] h he
  have hends := collaredProfile_incidence_endpoints _ h (clausePorts_spec hd hi).1 he
  have hv : e.2.1 < (profilePrefixGeometry (clauseProfile φ[i])).variablePositions.length := by
    simpa only [collaredPrefixGeometry, List.length_map, List.length_zipIdx] using hends.2.1
  have hlen : (profilePrefixGeometry (clauseProfile φ[i])).variablePositions.length =
      (profileVariables (clauseProfile φ[i])).length := by
    simpa only [profilePrefixGeometry, LocalGeometry.toPrefix, List.length_map,
      List.length_zipIdx] using profileGeometry_variable_length (clauseProfile φ[i])
  unfold positiveIncidenceRoute
  split
  next j hj =>
    have hm := profile_source_lookup _ hv hj
    have hjSource : j < φ[i].length := lt_of_lt_of_le hm.1 (profileSource_length_le φ[i])
    obtain ⟨q, hq, hr⟩ := positiveIncidenceRoute_join_endpoints hd hi h he hj
    change (positiveStem φ d i e ++ (positiveExterior φ d i j).tail).head? = _ ∧
      (positiveStem φ d i e ++ (positiveExterior φ d i j).tail).getLast? = _
    refine ⟨(by
      obtain ⟨t, ht⟩ := List.head?_eq_some_iff.mp hstem.2.2.1
      rw [ht]
      rfl), ?_⟩
    rw [last_join hq hr, positiveExterior_last hd hi hjSource]
    unfold positiveIncidenceVariable
    rw [hj]
    simp only [profileVariableMap, List.getD_eq_getElem _ _ hjSource]
  next w hw =>
    change (positiveStem φ d i e).head? = _ ∧ (positiveStem φ d i e).getLast? = _
    refine ⟨hstem.2.2.1, ?_⟩
    rw [hstem.2.2.2]
    congr 1
    symm
    apply positiveVariablePoint_profile_auxiliary_getD φ d
      (List.mem_zipIdx_iff_getElem?.mpr (List.getElem?_eq_some_iff.mpr ⟨hi, rfl⟩))
      (by omega)
    exact hw

/-- Full support of an emitted route splits into its finite stem and, for a source
placeholder only, the inherited exterior support. -/
theorem mem_support_positiveIncidenceRoute_iff {φ : CNF ℕ} {d : Graph.OrthogonalDrawing}
    (hd : Graph.IsPlanarOrthogonalDrawing (SAT.incidenceGraph φ) d) {i : ℕ}
    (hi : i < φ.length)
    (h : LocalGeometry.PrefixCheck (profilePrefixGeometry (clauseProfile φ[i])))
    {e : LocalIncidence} (he : e ∈ (clauseGeometry φ d i φ[i]).incidenceRoutes)
    {z : ℝ × ℝ} :
    z ∈ support (positiveIncidenceRoute φ d i φ[i] e) ↔
      z ∈ support (positiveStem φ d i e) ∨
        ∃ j, (profileVariables (clauseProfile φ[i])).getD e.2.1 (.inl (.inl 0)) =
          .inl (.inl j) ∧ z ∈ support (positiveExterior φ d i j) := by
  unfold positiveIncidenceRoute
  split
  next j hj =>
    change z ∈ support (positiveStem φ d i e ++ (positiveExterior φ d i j).tail) ↔ _
    obtain ⟨q, hq, hr⟩ := positiveIncidenceRoute_join_endpoints hd hi h he hj
    rw [support_join hq hr, Set.mem_union]
    constructor
    · exact fun hz => hz.elim Or.inl (fun hz => Or.inr ⟨j, hj, hz⟩)
    · rintro (hz | ⟨k, hk, hz⟩)
      · exact Or.inl hz
      · have hkj : k = j := Sum.inl.inj (Sum.inl.inj (hk.symm.trans hj))
        exact Or.inr (hkj ▸ hz)
  next w hw =>
    change z ∈ support (positiveStem φ d i e) ↔ _
    constructor
    · exact Or.inl
    · rintro (hz | ⟨k, hk, _⟩)
      · exact hz
      · exact False.elim (hw k hk)

/-- Distinct inherited source incidences meet only at an actual common source-variable point,
including repeated literals and distinct occurrences with equal signed variable names. -/
theorem positiveExterior_contacts {φ : CNF ℕ} {d : Graph.OrthogonalDrawing}
    (hd : Graph.IsPlanarOrthogonalDrawing (SAT.incidenceGraph φ) d) {i j k l : ℕ}
    (hi : i < φ.length) (hj : j < φ.length) (hk : k < φ[i].length) (hl : l < φ[j].length)
    (hne : (i, k) ≠ (j, l)) {z : ℝ × ℝ}
    (hz : z ∈ support (positiveExterior φ d i k))
    (hw : z ∈ support (positiveExterior φ d j l)) :
    φ[i][k].1 = φ[j][l].1 ∧
      z = realPoint (positiveVariablePoint φ d (.inl (.inl φ[i][k].1))) := by
  have hne' : sourceEdgeIndex φ i k ≠ sourceEdgeIndex φ j l := by
    intro he
    have ho := (List.idxOf_inj (sourceOccurrence_mem φ hi hk)).mp he
    exact hne (congrArg (fun o : Occurrence ℕ => (o.1, o.2.1)) ho)
  rw [positiveExterior, support_translate] at hz hw
  obtain ⟨x, hx, rfl⟩ := hz
  obtain ⟨y, hy, hyx⟩ := hw
  have hy' : y = x := add_right_cancel hyx
  subst y
  obtain ⟨heq, hxq⟩ := exteriorRoute_contacts hd (sourceEdgeIndex_lt φ hi hk)
    (sourceEdgeIndex_lt φ hj hl) hne' (by decide : 0 < positiveRadius)
    (by decide : positiveRadius < positiveScale) hx hy
  have hedge₁ := sourceEdgeIndex_edge φ hi hk
  have hedge₂ := sourceEdgeIndex_edge φ hj hl
  rw [List.getD_eq_getElem _ _ (sourceEdgeIndex_lt φ hi hk)] at hedge₁
  rw [List.getD_eq_getElem _ _ (sourceEdgeIndex_lt φ hj hl)] at hedge₂
  rw [hedge₁, hedge₂] at heq
  have hmem₁ : φ[i][k].1 ∈ φ.vars := CNF.mem_vars.mpr
    ⟨φ[i], List.getElem_mem hi, φ[i][k].2, List.getElem_mem hk⟩
  have hmem₂ : φ[j][l].1 ∈ φ.vars := CNF.mem_vars.mpr
    ⟨φ[j], List.getElem_mem hj, φ[j][l].2, List.getElem_mem hl⟩
  refine ⟨(List.idxOf_inj (CNF.mem_distinctVars.mpr hmem₁)).mp heq, ?_⟩
  rw [positiveVariablePoint_source φ d hmem₁, realPoint_add]
  dsimp only
  rw [hxq]
  congr 2
  rw [sourceFinish, sourceEdgeIndex_edge φ hi hk]

/-- Source-placeholder metadata for an actual local row. -/
theorem positiveIncidence_source_lookup {φ : CNF ℕ} {d : Graph.OrthogonalDrawing}
    (hd : Graph.IsPlanarOrthogonalDrawing (SAT.incidenceGraph φ) d) {i : ℕ}
    (hi : i < φ.length)
    (h : LocalGeometry.PrefixCheck (profilePrefixGeometry (clauseProfile φ[i])))
    {e : LocalIncidence} (he : e ∈ (clauseGeometry φ d i φ[i]).incidenceRoutes) {j : ℕ}
    (hget : (profileVariables (clauseProfile φ[i])).getD e.2.1 (.inl (.inl 0)) =
      .inl (.inl j)) :
    j < φ[i].length ∧ j < 3 ∧
      e.2.1 ∈ (profilePrefixGeometry (clauseProfile φ[i])).terminalVariables ∧
      positiveIncidenceVariable φ i φ[i] e = .inl (.inl (φ[i].getD j (0, true)).1) := by
  have hends := collaredProfile_incidence_endpoints _ h (clausePorts_spec hd hi).1 he
  have hv : e.2.1 < (profilePrefixGeometry (clauseProfile φ[i])).variablePositions.length := by
    simpa only [collaredPrefixGeometry, List.length_map, List.length_zipIdx] using hends.2.1
  have hm := profile_source_lookup _ hv hget
  have hj : j < φ[i].length := lt_of_lt_of_le hm.1 (profileSource_length_le φ[i])
  refine ⟨hj, hm.2.1, hm.2.2.2.1, ?_⟩
  unfold positiveIncidenceVariable
  rw [hget]
  rfl

/-- Two distinct actual local rows cannot share a source placeholder. -/
theorem clauseGeometry_shared_variable_auxiliary {φ : CNF ℕ} {d : Graph.OrthogonalDrawing}
    (hd : Graph.IsPlanarOrthogonalDrawing (SAT.incidenceGraph φ) d) {i : ℕ}
    (hi : i < φ.length)
    (h : LocalGeometry.PrefixCheck (profilePrefixGeometry (clauseProfile φ[i])))
    {e f : LocalIncidence} (he : e ∈ (clauseGeometry φ d i φ[i]).incidenceRoutes)
    (hf : f ∈ (clauseGeometry φ d i φ[i]).incidenceRoutes) (hne : e ≠ f)
    (hv : e.2.1 = f.2.1) :
    ∀ j, (profileVariables (clauseProfile φ[i])).getD e.2.1 (.inl (.inl 0)) ≠
      .inl (.inl j) := by
  intro j hj
  have hmeta := positiveIncidence_source_lookup hd hi h he hj
  have ht : f.2.1 ∈ (profilePrefixGeometry (clauseProfile φ[i])).terminalVariables :=
    hv ▸ hmeta.2.2.1
  have hn := collaredProfile_other_terminal_not_mem_support _ h (clausePorts_spec hd hi).1
    he hf hne ht
  have hend := (collaredProfile_incidence_endpoints _ h (clausePorts_spec hd hi).1 he).2.2.2
  exact hn (Or.inl ⟨_, List.mem_of_getLast? hend, congrArg realPoint
    (congrArg (LocalGeometry.variablePosition (clauseGeometry φ d i φ[i])) hv).symm⟩)

/-- The last local point of a private incidence is its actual global variable vertex. -/
theorem positiveIncidenceVariable_auxiliary_point {φ : CNF ℕ} {d : Graph.OrthogonalDrawing}
    (hd : Graph.IsPlanarOrthogonalDrawing (SAT.incidenceGraph φ) d) {i : ℕ}
    (hi : i < φ.length)
    (h : LocalGeometry.PrefixCheck (profilePrefixGeometry (clauseProfile φ[i])))
    {e : LocalIncidence} (he : e ∈ (clauseGeometry φ d i φ[i]).incidenceRoutes)
    (ha : ∀ n, (profileVariables (clauseProfile φ[i])).getD e.2.1 (.inl (.inl 0)) ≠
      Sum.inl (Sum.inl n)) :
    positiveVariablePoint φ d (positiveIncidenceVariable φ i φ[i] e) =
      positiveBoxOrigin φ d i + (clauseGeometry φ d i φ[i]).variablePosition e.2.1 := by
  have hends := collaredProfile_incidence_endpoints _ h (clausePorts_spec hd hi).1 he
  have hlen : (clauseGeometry φ d i φ[i]).variablePositions.length =
      (profileVariables (clauseProfile φ[i])).length := by
    simp only [clauseGeometry, collaredPrefixGeometry, List.length_map, List.length_zipIdx,
      profilePrefixGeometry, LocalGeometry.toPrefix, profileGeometry_variable_length]
  exact positiveVariablePoint_profile_auxiliary_getD φ d
    (List.mem_zipIdx_iff_getElem?.mpr (List.getElem?_eq_some_iff.mpr ⟨hi, rfl⟩))
    (by
      have hvi := hends.2.1
      change e.2.1 < (clauseGeometry φ d i φ[i]).variablePositions.length at hvi
      omega) ha

private theorem clauseGeometry_source_lookup_injective {φ : CNF ℕ}
    {d : Graph.OrthogonalDrawing}
    (_hd : Graph.IsPlanarOrthogonalDrawing (SAT.incidenceGraph φ) d) {i : ℕ}
    (hi : i < φ.length)
    (h : LocalGeometry.PrefixCheck (profilePrefixGeometry (clauseProfile φ[i])))
    {e f : LocalIncidence} (he : e ∈ (clauseGeometry φ d i φ[i]).incidenceRoutes)
    (hf : f ∈ (clauseGeometry φ d i φ[i]).incidenceRoutes) {j : ℕ}
    (heget : (profileVariables (clauseProfile φ[i])).getD e.2.1 (.inl (.inl 0)) =
      .inl (.inl j))
    (hfget : (profileVariables (clauseProfile φ[i])).getD f.2.1 (.inl (.inl 0)) =
      .inl (.inl j)) : e = f := by
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp he
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hf
  have hma := profile_source_lookup _ (LocalGeometry.prefix_incidence_endpoints h ha).2.1 heget
  have hmb := profile_source_lookup _ (LocalGeometry.prefix_incidence_endpoints h hb).2.1 hfget
  have hab := profile_prefix_terminal_unique _ a ha hma.2.2.2.1 b hb
    (hma.2.2.1.trans hmb.2.2.1.symm)
  subst b
  rfl

/-- All continuous contacts between distinct emitted incidences are their actual common
clause or globally shared variable endpoints. -/
theorem positiveIncidenceRoute_contacts {φ : CNF ℕ} {d : Graph.OrthogonalDrawing}
    (hd : Graph.IsPlanarOrthogonalDrawing (SAT.incidenceGraph φ) d) {i j : ℕ}
    (hi : i < φ.length) (hj : j < φ.length)
    (h : ∀ k : ℕ, ∀ hk : k < φ.length,
      LocalGeometry.PrefixCheck (profilePrefixGeometry (clauseProfile φ[k])))
    {e f : LocalIncidence} (he : e ∈ (clauseGeometry φ d i φ[i]).incidenceRoutes)
    (hf : f ∈ (clauseGeometry φ d j φ[j]).incidenceRoutes) (hne : (i, e) ≠ (j, f))
    {z : ℝ × ℝ} (hz : z ∈ support (positiveIncidenceRoute φ d i φ[i] e))
    (hw : z ∈ support (positiveIncidenceRoute φ d j φ[j] f)) :
    (i = j ∧ e.1 = f.1 ∧
      z = realPoint (positiveBoxOrigin φ d i + (clauseGeometry φ d i φ[i]).clausePosition e.1)) ∨
      (positiveIncidenceVariable φ i φ[i] e = positiveIncidenceVariable φ j φ[j] f ∧
        z = realPoint (positiveVariablePoint φ d (positiveIncidenceVariable φ i φ[i] e))) := by
  rw [mem_support_positiveIncidenceRoute_iff hd hi (h i hi) he] at hz
  rw [mem_support_positiveIncidenceRoute_iff hd hj (h j hj) hf] at hw
  rcases hz with hz | ⟨k, hgetk, hz⟩ <;> rcases hw with hw | ⟨l, hgetl, hw⟩
  · by_cases hij : i = j
    · subst j
      have hef : e ≠ f := fun hef => hne (Prod.ext rfl hef)
      obtain ⟨q, hq, hzq⟩ := positiveStem_contacts hd hi φ[i] (h i hi) he hf hef hz hw
      rw [LocalGeometry.commonEndpoints, List.mem_append] at hq
      rcases hq with hq | hq
      · split_ifs at hq with hc
        · simp only [List.mem_singleton] at hq
          exact Or.inl ⟨rfl, hc, hq ▸ hzq⟩
        · exact False.elim (List.not_mem_nil hq)
      · split_ifs at hq with hv
        · simp only [List.mem_singleton] at hq
          have ha := clauseGeometry_shared_variable_auxiliary hd hi (h i hi) he hf hef hv
          refine Or.inr ⟨?_, ?_⟩
          · unfold positiveIncidenceVariable
            rw [hv]
          · rw [positiveIncidenceVariable_auxiliary_point hd hi (h i hi) he ha]
            exact hq ▸ hzq
        · exact False.elim (List.not_mem_nil hq)
    · exact False.elim (Set.disjoint_left.mp
        (positiveStem_different_boxes_disjoint hd hi hj hij φ[i] φ[j] he hf) hz hw)
  · have hm := positiveIncidence_source_lookup hd hj (h j hj) hf hgetl
    by_cases hij : i = j
    · subst j
      have hef : e ≠ f := fun hef => hne (Prod.ext rfl hef)
      exact False.elim (Set.disjoint_left.mp
        (positiveStem_other_exterior_disjoint hd hi (h i hi) he hf hef hgetl) hz hw)
    · exact False.elim (Set.disjoint_left.mp
        (positiveStem_foreign_exterior_disjoint hd hi hj hm.1 hij φ[i] he) hz hw)
  · have hm := positiveIncidence_source_lookup hd hi (h i hi) he hgetk
    by_cases hij : i = j
    · subst j
      have hfe : f ≠ e := fun hfe => hne (Prod.ext rfl hfe.symm)
      exact False.elim (Set.disjoint_left.mp
        (positiveStem_other_exterior_disjoint hd hi (h i hi) hf he hfe hgetk) hw hz)
    · exact False.elim (Set.disjoint_left.mp
        (positiveStem_foreign_exterior_disjoint hd hj hi hm.1 (Ne.symm hij) φ[j] hf) hw hz)
  · have hmk := positiveIncidence_source_lookup hd hi (h i hi) he hgetk
    have hml := positiveIncidence_source_lookup hd hj (h j hj) hf hgetl
    have hslots : (i, k) ≠ (j, l) := by
      intro heq
      have hij : i = j := congrArg Prod.fst heq
      have hkl : k = l := congrArg Prod.snd heq
      subst j
      subst l
      have hef := clauseGeometry_source_lookup_injective hd hi (h i hi) he hf hgetk hgetl
      exact hne (Prod.ext rfl hef)
    obtain ⟨hvars, hzvar⟩ := positiveExterior_contacts hd hi hj hmk.1 hml.1 hslots hz hw
    refine Or.inr ⟨?_, ?_⟩
    · rw [hmk.2.2.2, hml.2.2.2, List.getD_eq_getElem _ _ hmk.1,
        List.getD_eq_getElem _ _ hml.1, hvars]
    · rw [hmk.2.2.2, List.getD_eq_getElem _ _ hmk.1]
      exact hzvar

end Cslib.Complexity.SAT.ExactOne
