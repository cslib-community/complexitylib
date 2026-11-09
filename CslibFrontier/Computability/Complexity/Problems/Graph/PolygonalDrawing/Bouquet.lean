/-
Copyright (c) 2026 Erik Demaine, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Realization.Basic
public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Realization.BouquetOrder
public import CslibFrontier.Foundations.Geometry.Polygonal.Noncrossing
public import CslibFrontier.Foundations.Geometry.Polygonal.NoncrossingOrder
public import CslibFrontier.Foundations.Geometry.Polygonal.Translation

/-!
# Polygonal drawings of arbitrary bouquets of indexed loops

Every vertex receives a translated copy of the five-segment port-loop construction, with
ports in the literal clockwise rotation order. A common horizontal spacing separates all
natural-number vertex names, including sparse and repeated declarations and isolated names.
Each listed edge occurrence retains both of its own ends. The coordinate construction is an
original reconstruction and has no degree or component bound.
-/

public section

namespace Cslib.Complexity.Graph.PolygonalDrawing

open Polygonal

variable {G : Graph} (r : RotationSystem G)

open Classical in
private noncomputable def spacing : ℝ := ((Finset.univ.sup r.portRank : ℕ) : ℝ) + 2

private noncomputable def center (v : ℕ) : ℂ := ⟨spacing r * v, 0⟩

private noncomputable def port (d : Dart G) : ℝ := (r.portRank d : ℝ) + 1

/-- Explicit five-segment routes for any loop-only graph and any supplied rotation.
Each vertex cycle is cut once and its darts placed at positive horizontal ports in rank order.
Numerical genus zero is needed for embedding, not to define these actual coordinates. -/
noncomputable def bouquet
    (hloop : ∀ e : Fin G.2.length,
      (Dart.vertex (G := G) (e, false)) = Dart.vertex (e, true)) : PolygonalDrawing G where
  vertex := center r
  route := fun e => (portLoop (port r (e, false)) (port r (e, true))).translate
    (center r (Dart.vertex (G := G) (e, false)))
  endpoint_eq := by
    intro e b
    rw [Route.endpoint_translate, endpoint_portLoop, add_zero]
    cases b
    · rfl
    · rw [hloop e]

private theorem spacing_pos : 0 < spacing r := by
  unfold spacing
  positivity

private theorem port_bounds (d : Dart G) : 0 < port r d ∧ port r d < spacing r := by
  classical
  have h := Finset.le_sup (f := r.portRank) (Finset.mem_univ d)
  have h' : (r.portRank d : ℝ) ≤ Finset.univ.sup r.portRank := by exact_mod_cast h
  constructor
  · unfold port
    positivity
  · dsimp only [port, spacing]
    linarith

private theorem same_center_of_contact {u v : ℕ} {x y : ℝ}
    (hx : x ∈ Set.Ico 0 (spacing r)) (hy : y ∈ Set.Ico 0 (spacing r))
    (heq : spacing r * u + x = spacing r * v + y) : u = v := by
  rcases lt_trichotomy u v with h | h | h
  · have huv : (u : ℝ) + 1 ≤ v := by exact_mod_cast h
    have hmul := mul_le_mul_of_nonneg_left huv (spacing_pos r).le
    nlinarith [hx.1, hx.2, hy.1]
  · exact h
  · have hvu : (v : ℝ) + 1 ≤ u := by exact_mod_cast h
    have hmul := mul_le_mul_of_nonneg_left hvu (spacing_pos r).le
    nlinarith [hy.1, hy.2, hx.1]

private theorem eval_re_bounds (e : Fin G.2.length) (i : Fin 5) {t : ℝ}
    (ht : t ∈ Set.Icc 0 1) :
    ((portLoop (port r (e, false)) (port r (e, true))).eval i t).re ∈
      Set.Ico 0 (spacing r) := by
  have h := re_eval_portLoop_mem
    (B := max (port r (e, false)) (port r (e, true)))
    ⟨(port_bounds r _).1.le, le_max_left _ _⟩
    ⟨(port_bounds r _).1.le, le_max_right _ _⟩ i ht
  exact ⟨h.1, h.2.trans_lt (max_lt (port_bounds r _).2 (port_bounds r _).2)⟩

private theorem port_injective (a b : Dart G) (hv : a.vertex = b.vertex)
    (h : port r a = port r b) : a = b := by
  apply r.portRank_injective a b hv
  unfold port at h
  exact_mod_cast (add_right_cancel h)

/-- The two actual loop-end germs are the ports of those very indexed darts. -/
theorem germ_bouquet
    (hloop : ∀ e : Fin G.2.length,
      (Dart.vertex (G := G) (e, false)) = Dart.vertex (e, true)) (d : Dart G) :
    (bouquet r hloop).germ d = ⟨(r.portRank d : ℝ) + 1, 1⟩ := by
  rcases d with ⟨e, b⟩
  change ((portLoop (port r (e, false)) (port r (e, true))).translate _).germ b = _
  rw [Route.germ_translate, germ_portLoop]
  cases b <;> rfl

/-- The construction realizes the exact given clockwise rotation, without reflection.
This needs no numerical-genus assumption; `bouquet_isEmbedding` supplies embedding separately. -/
theorem bouquet_realizes
    (hloop : ∀ e : Fin G.2.length,
      (Dart.vertex (G := G) (e, false)) = Dart.vertex (e, true)) :
    (bouquet r hloop).Realizes r where
  nonzero d := by
    rw [germ_bouquet]
    intro h
    have := congrArg Complex.im h
    norm_num at this
  directions_injective a b hv heq := by
    change (((bouquet r hloop).germ a).arg : Real.Angle) =
      (((bouquet r hloop).germ b).arg : Real.Angle) at heq
    rw [germ_bouquet, germ_bouquet] at heq
    exact port_injective r a b hv (direction_port_injective
      (port_bounds r a).1 (port_bounds r b).1 heq)
  clockwise a b c hv hw hab hbc hac := by
    change sbtw (((bouquet r hloop).germ c).arg : Real.Angle)
      (((bouquet r hloop).germ b).arg : Real.Angle)
      (((bouquet r hloop).germ a).arg : Real.Angle) ↔ _
    rw [germ_bouquet, germ_bouquet, germ_bouquet]
    have hneab : port r a ≠ port r b := fun h => hab (port_injective r a b hv h)
    have hnebc : port r b ≠ port r c := fun h => hbc (port_injective r b c hw h)
    have hneac : port r a ≠ port r c := fun h => hac (port_injective r a c (hv.trans hw) h)
    change sbtw ((⟨port r c, 1⟩ : ℂ).arg : Real.Angle)
      ((⟨port r b, 1⟩ : ℂ).arg : Real.Angle) ((⟨port r a, 1⟩ : ℂ).arg : Real.Angle) ↔ _
    rw [clockwise_ports_iff (port_bounds r a).1 (port_bounds r b).1 (port_bounds r c).1
      hneab hnebc hneac, r.mem_rotationInterval_iff_portRank a b c hv hw hab hbc hac]
    unfold port
    norm_cast
    omega

private theorem eval_bouquet
    (hloop : ∀ e : Fin G.2.length,
      (Dart.vertex (G := G) (e, false)) = Dart.vertex (e, true))
    (e : Fin G.2.length) (i : Fin 5) (t : ℝ) :
    ((bouquet r hloop).route e).eval i t =
      center r (Dart.vertex (G := G) (e, false)) +
        (portLoop (port r (e, false)) (port r (e, true))).eval i t :=
  Route.eval_translate _ _ _ _

private theorem distinct_ports
    (hloop : ∀ e : Fin G.2.length,
      (Dart.vertex (G := G) (e, false)) = Dart.vertex (e, true)) (e : Fin G.2.length) :
    port r (e, false) ≠ port r (e, true) := by
  intro h
  exact Bool.false_ne_true (congrArg Prod.snd (port_injective r _ _ (hloop e) h))

/-- For every loop-only listed graph, numerical genus zero makes the constructed
five-segment drawing a genuine embedding. Degrees, repeated edge pairs, declared vertex
names, isolated vertices and disconnected components are unrestricted. -/
theorem bouquet_isEmbedding
    (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.1) (hr : r.NumericalGenusZero)
    (hloop : ∀ e : Fin G.2.length,
      (Dart.vertex (G := G) (e, false)) = Dart.vertex (e, true)) :
    (bouquet r hloop).IsEmbedding where
  vertices_injective := by
    intro u _ v _ h
    have hreal := congrArg Complex.re h
    change spacing r * (u : ℝ) = spacing r * (v : ℝ) at hreal
    exact_mod_cast mul_left_cancel₀ (ne_of_gt (spacing_pos r)) hreal
  simple e := (isSimple_portLoop (distinct_ports r hloop e)).translate _
  vertex_contacts := by
    intro e i t ht v _ heq
    change Fin 5 at i
    rw [eval_bouquet r hloop e i t] at heq
    have hreal := congrArg Complex.re heq
    change spacing r * (Dart.vertex (G := G) (e, false) : ℝ) +
      ((portLoop (port r (e, false)) (port r (e, true))).eval i t).re =
        spacing r * (v : ℝ) at hreal
    have hv := same_center_of_contact r (eval_re_bounds r e i ht)
      (show (0 : ℝ) ∈ Set.Ico 0 (spacing r) from ⟨le_rfl, spacing_pos r⟩)
      (by simpa only [add_zero] using hreal)
    have hz : (portLoop (port r (e, false)) (port r (e, true))).eval i t = 0 := by
      rw [hv] at heq
      exact add_left_cancel (heq.trans (add_zero _).symm)
    obtain ⟨b, hb⟩ := atEnd_of_eval_portLoop_eq_zero (distinct_ports r hloop e) i ht hz
    refine ⟨b, hb, ?_⟩
    cases b
    · exact hv
    · exact (hloop e).symm.trans hv
  edge_contacts := by
    intro e f hef i j s t hs ht heq
    change Fin 5 at i j
    rw [eval_bouquet r hloop e i s, eval_bouquet r hloop f j t] at heq
    have hreal := congrArg Complex.re heq
    change spacing r * (Dart.vertex (G := G) (e, false) : ℝ) +
      ((portLoop (port r (e, false)) (port r (e, true))).eval i s).re =
      spacing r * (Dart.vertex (G := G) (f, false) : ℝ) +
        ((portLoop (port r (f, false)) (port r (f, true))).eval j t).re at hreal
    have hv := same_center_of_contact r (eval_re_bounds r e i hs) (eval_re_bounds r f j ht)
      hreal
    have hlocal : (portLoop (port r (e, false)) (port r (e, true))).eval i s =
        (portLoop (port r (f, false)) (port r (f, true))).eval j t := by
      rw [hv] at heq
      exact add_left_cancel heq
    have hcross (b c : Bool) : port r (e, b) ≠ port r (f, c) := by
      intro h
      have hvertex : (Dart.vertex (G := G) (e, b)) = Dart.vertex (f, c) := by
        cases b <;> cases c <;> have he := hloop e <;> have hf := hloop f <;> omega
      exact hef (congrArg Prod.fst (port_injective r _ _ hvertex h))
    have hlam := r.portRank_loops_laminar hG hr e f hef (hloop e) (hloop f) hv
    have hzero := portLoop_contact_eq_zero (hcross false false) (hcross false true)
      (hcross true false) (hcross true true) (by
        dsimp only [port]
        simp only [min_add_add_right, max_add_add_right, add_lt_add_iff_right]
        exact_mod_cast hlam) i j hs ht hlocal
    obtain ⟨b, hb⟩ := atEnd_of_eval_portLoop_eq_zero (distinct_ports r hloop e) i hs hzero
    obtain ⟨c, hc⟩ := atEnd_of_eval_portLoop_eq_zero (distinct_ports r hloop f) j ht
      (hlocal.symm.trans hzero)
    refine ⟨b, c, hb, hc, ?_⟩
    cases b <;> cases c <;> have he := hloop e <;> have hf := hloop f <;> omega

end Cslib.Complexity.Graph.PolygonalDrawing
