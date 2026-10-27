/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.SAT.ExactOne.Drawing
public import Complexity.Computability.Complexity.Problems.SAT.ExactOne.GeometryProfilesCollar
import Mathlib.Data.List.GetD
import Mathlib.Tactic.Linarith

/-!
# Constant-factor coordinate bounds for the actual positive drawing compiler

Every emitted vertex and route point is bounded on the actual drawing lists. The source drawing
is dilated by `1080000`, and every local replacement lies in a side-`540000` square. The source
axis translation and the endpoint cuts fit within the same constant margin. These bounds do
not require geometric validity of the input drawing.

## Main results

* `positiveDrawing_fits`: an input rectangle of width `W` and height `H` yields an actual output
  rectangle with sides `1080000 * (W + 1)` and `1080000 * (H + 1)`.

## References

The explicit coordinate and finite-output bounds are original.
-/

@[expose] public section

namespace Cslib.Complexity.SAT.ExactOne

open Cslib.Logic.PL Orthogonal

private def Rect (W H : ℕ) (p : Point) : Prop :=
  0 ≤ p.1 ∧ p.1 ≤ W ∧ 0 ≤ p.2 ∧ p.2 ≤ H

private theorem getD_property {A : Type*} (P : A → Prop) (xs : List A) (fallback : A)
    (hf : P fallback) (hxs : ∀ x ∈ xs, P x) (i : ℕ) : P (xs.getD i fallback) := by
  induction xs generalizing i with
  | nil => simpa using hf
  | cons a xs ih =>
    cases i with
    | zero => exact hxs a List.mem_cons_self
    | succ i =>
      exact ih (fun x hx => hxs x (List.mem_cons_of_mem _ hx)) i

private theorem zero_rect (W H : ℕ) : Rect W H (0, 0) := by simp [Rect]

private theorem input_position_bounds {d : Graph.OrthogonalDrawing} {W H : ℕ}
    (hd : Graph.drawingFits d W H) (G : Graph) (v : ℕ) :
    Rect W H (Graph.drawingPosition G d v) :=
  getD_property _ d.1 (0, 0) (zero_rect W H) hd.1 _

private theorem input_route_bounds {d : Graph.OrthogonalDrawing} {W H : ℕ}
    (hd : Graph.drawingFits d W H) (i : ℕ) :
    ∀ q ∈ d.2.getD i [], Rect W H q :=
  getD_property _ d.2 [] (by simp) hd.2 i

private theorem sourceRoute_points_bounds {d : Graph.OrthogonalDrawing} {W H : ℕ}
    (hd : Graph.drawingFits d W H) (G : Graph) (i : ℕ) :
    ∀ q ∈ sourceRoute G d i, Rect W H q := by
  unfold sourceRoute
  split
  · exact input_route_bounds hd i
  · intro q hq
    exact input_route_bounds hd i q (List.mem_reverse.mp hq)

private theorem collar_outer_bounds (side : Fin 4) :
    Rect 540000 540000 (collarOuterPort side) := by
  unfold Rect
  fin_cases side <;> decide +kernel

private theorem collar_points_bounds : ∀ (s : PortAssignment) (i : Fin 3),
    ∀ q ∈ (collarRoutes s).getD i [], Rect 540000 540000 q := by
  unfold Rect
  decide +kernel

private theorem collarPoint_bounds (reflected : Bool) {q : Point}
    (hq : Rect 180000 180000 q) : Rect 540000 540000 (collarPoint reflected q) := by
  cases reflected <;> dsimp [Rect, collarPoint, collarOffset, mirrorPoint] at * <;> omega

private theorem prefix_variable_bounds (p : ClauseProfile) :
    ∀ q ∈ (profilePrefixGeometry p).variablePositions, Rect 180000 180000 q := by
  intro q hq
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hq
  have h := profile_prefix_variable_bounds p ⟨i, hi⟩
  simpa only [Rect, Nat.cast_ofNat, LocalGeometry.variablePosition,
    List.getD_eq_getElem _ _ hi] using h

private theorem prefix_clause_bounds (p : ClauseProfile) :
    ∀ q ∈ (profilePrefixGeometry p).clausePositions, Rect 180000 180000 q := by
  intro q hq
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hq
  have h := profile_prefix_clause_bounds p ⟨i, hi⟩
  simpa only [Rect, Nat.cast_ofNat, LocalGeometry.clausePosition,
    List.getD_eq_getElem _ _ hi] using h

private theorem local_variable_bounds (p : ClauseProfile) (s : PortAssignment) (v : ℕ) :
    Rect 540000 540000
      ((collaredPrefixGeometry (profilePrefixGeometry p) s).variablePosition v) := by
  apply getD_property _ _ _ (zero_rect _ _)
  intro q hq
  obtain ⟨⟨a, i⟩, ha, rfl⟩ := List.mem_map.mp hq
  split_ifs
  · exact collar_outer_bounds _
  · exact collarPoint_bounds _ (prefix_variable_bounds p a (List.fst_mem_of_mem_zipIdx ha))

private theorem local_clause_bounds (p : ClauseProfile) (s : PortAssignment) (i : ℕ) :
    Rect 540000 540000 ((collaredPrefixGeometry (profilePrefixGeometry p) s).clausePosition i) := by
  apply getD_property _ _ _ (zero_rect _ _)
  intro q hq
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hq
  exact collarPoint_bounds _ (prefix_clause_bounds p a ha)

private theorem collarRoute_points_bounds (reflected : Bool) {r : Route}
    (hr : ∀ q ∈ r, Rect 180000 180000 q) :
    ∀ q ∈ collarRoute reflected r, Rect 540000 540000 q := by
  intro q hq
  rw [collarRoute_eq_map] at hq
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hq
  exact collarPoint_bounds _ (hr a ha)

private theorem local_route_bounds (p : ClauseProfile) (s : PortAssignment)
    {e : LocalIncidence}
    (he : e ∈ (collaredPrefixGeometry (profilePrefixGeometry p) s).incidenceRoutes) :
    ∀ q ∈ e.2.2, Rect 540000 540000 q := by
  obtain ⟨f, hf, rfl⟩ := List.mem_map.mp he
  dsimp only
  split_ifs
  · intro q hq
    rw [collarPrefixRoute, List.mem_append] at hq
    rcases hq with hq | hq
    · exact collarRoute_points_bounds _ (profile_prefix_incidence_points_bounds p f hf) q hq
    · exact collar_points_bounds s _ q (List.mem_reverse.mp (List.mem_of_mem_tail hq))
  · exact collarRoute_points_bounds _ (profile_prefix_incidence_points_bounds p f hf)

private theorem placed_point_bounds {W H : ℕ} {a q : Point}
    (ha : Rect W H a) (hq : Rect 540000 540000 q) :
    Rect (1080000 * (W + 1)) (1080000 * (H + 1)) (positiveScale • a + q) := by
  dsimp [Rect, positiveScale, Prod.smul_mk, Int.nsmul_eq_mul] at *
  omega

private theorem translation_bounds : Rect 540000 540000 positiveTranslation := by
  unfold Rect
  decide +kernel

private theorem cut_offset_bounds (a b : Point) :
    Rect 540000 540000 (positiveRadius • direction a b + positiveTranslation) := by
  rcases direction_unit a b with h | h | h | h <;> rw [h] <;>
    norm_num [Rect, positiveRadius, positiveTranslation, Prod.smul_mk]

private theorem cutStart_points_bounds {W H : ℕ} {r : Route}
    (hr : ∀ q ∈ r, Rect W H q) :
    ∀ q ∈ cutStart positiveScale positiveRadius r,
      Rect (1080000 * (W + 1)) (1080000 * (H + 1)) (q + positiveTranslation) := by
  cases r with
  | nil => simp [cutStart, dilateRoute]
  | cons a r =>
    cases r with
    | nil =>
      intro q hq
      have he : q = positiveScale • a := by simpa [cutStart, dilateRoute] using hq
      rw [he]
      exact placed_point_bounds (hr a List.mem_cons_self) translation_bounds
    | cons b r =>
      intro q hq
      change q ∈ cutPoint positiveScale positiveRadius a b :: dilateRoute positiveScale (b :: r)
        at hq
      rcases List.mem_cons.mp hq with rfl | hq
      · simpa only [cutPoint, add_assoc] using
          placed_point_bounds (hr a List.mem_cons_self) (cut_offset_bounds a b)
      · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hq
        exact placed_point_bounds (hr x (List.mem_cons_of_mem _ hx)) translation_bounds

/-- Every point of the actual inherited exterior route fits the enlarged source rectangle. -/
theorem positiveExterior_points_fits {φ : CNF ℕ} {d : Graph.OrthogonalDrawing} {W H : ℕ}
    (hd : Graph.drawingFits d W H) (i j : ℕ) :
    ∀ q ∈ positiveExterior φ d i j,
      0 ≤ q.1 ∧ q.1 ≤ 1080000 * (W + 1) ∧
        0 ≤ q.2 ∧ q.2 ≤ 1080000 * (H + 1) := by
  intro q hq
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hq
  exact cutStart_points_bounds (sourceRoute_points_bounds hd _ _) x hx

private theorem actual_variablePoint_bounds {φ : CNF ℕ} {d : Graph.OrthogonalDrawing}
    {W H : ℕ} (hd : Graph.drawingFits d W H) (v : CNF.PositiveExactOneCompile.Variable ℕ) :
    Rect (1080000 * (W + 1)) (1080000 * (H + 1)) (positiveVariablePoint φ d v) := by
  apply getD_property _ _ _ (zero_rect _ _)
  intro q hq
  obtain ⟨⟨w, q⟩, htable, rfl⟩ := List.mem_map.mp hq
  rcases List.mem_append.mp htable with hsource | haux
  · obtain ⟨n, _, he⟩ := List.mem_map.mp hsource
    have hq := congrArg Prod.snd he
    rw [← hq]
    exact placed_point_bounds (input_position_bounds hd _ _) translation_bounds
  · obtain ⟨⟨c, i⟩, _, hentry⟩ := List.mem_flatMap.mp haux
    obtain ⟨⟨w, j⟩, _, he⟩ := List.mem_filterMap.mp hentry
    rcases w with (_ | _) | _
    · simp at he
    all_goals
      have heq := congrArg (Option.map Prod.snd) he
      simp only [Option.map_some, Option.some.injEq] at heq
      rw [← heq]
      exact placed_point_bounds (input_position_bounds hd _ _)
        (local_variable_bounds (clauseProfile c) _ _)

private theorem actual_clausePoint_bounds {φ : CNF ℕ} {d : Graph.OrthogonalDrawing}
    {W H : ℕ} (hd : Graph.drawingFits d W H) {pc : PositivePlacedClause}
    (hpc : pc ∈ positivePlacedClauses φ d) :
    Rect (1080000 * (W + 1)) (1080000 * (H + 1)) pc.2.1 := by
  obtain ⟨⟨c, i⟩, _, hpc⟩ := List.mem_flatMap.mp hpc
  obtain ⟨⟨a, j⟩, _, rfl⟩ := List.mem_map.mp hpc
  exact placed_point_bounds (input_position_bounds hd _ _)
    (local_clause_bounds (clauseProfile c) _ _)

private theorem actual_incidenceRoute_bounds {φ : CNF ℕ} {d : Graph.OrthogonalDrawing}
    {W H : ℕ} (hd : Graph.drawingFits d W H) (i : ℕ) (c : Clause ℕ) {e : LocalIncidence}
    (he : e ∈ (clauseGeometry φ d i c).incidenceRoutes) :
    ∀ q ∈ positiveIncidenceRoute φ d i c e,
      Rect (1080000 * (W + 1)) (1080000 * (H + 1)) q := by
  have hlocal : ∀ q ∈ translate (positiveBoxOrigin φ d i) e.2.2,
      Rect (1080000 * (W + 1)) (1080000 * (H + 1)) q := by
    intro q hq
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hq
    rw [add_comm x]
    exact placed_point_bounds (input_position_bounds hd _ _)
      (local_route_bounds (clauseProfile c) _ he x hx)
  unfold positiveIncidenceRoute
  split
  · intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · exact hlocal q hq
    · exact positiveExterior_points_fits hd _ _ q (List.mem_of_mem_tail hq)
  · exact hlocal

/-- The actual emitted drawing expands both source grid sides by only a fixed factor. This
holds for every finite input drawing, including malformed inputs handled by default lookups. -/
theorem positiveDrawing_fits (φ : CNF ℕ) {d : Graph.OrthogonalDrawing} {W H : ℕ}
    (hd : Graph.drawingFits d W H) :
    Graph.drawingFits (positiveDrawing φ d) (1080000 * (W + 1)) (1080000 * (H + 1)) := by
  constructor
  · intro q hq
    rcases List.mem_append.mp hq with hv | hc
    · obtain ⟨v, _, rfl⟩ := List.mem_map.mp hv
      exact actual_variablePoint_bounds hd v
    · obtain ⟨pc, hpc, rfl⟩ := List.mem_map.mp hc
      exact actual_clausePoint_bounds hd hpc
  · intro r hr q hq
    obtain ⟨pc, hpc, hr⟩ := List.mem_flatMap.mp hr
    obtain ⟨⟨c, i⟩, _, hpc⟩ := List.mem_flatMap.mp hpc
    obtain ⟨⟨a, j⟩, _, rfl⟩ := List.mem_map.mp hpc
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hr
    exact actual_incidenceRoute_bounds hd i c (List.mem_filter.mp he).1 q hq

end Cslib.Complexity.SAT.ExactOne
