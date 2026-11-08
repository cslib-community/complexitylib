/-
Copyright (c) 2026 Erik Demaine, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, OpenAI
-/

import Complexity.Computability.Complexity.Problems.Graph.PolygonalDrawing.Germs
import Complexity.Computability.Complexity.Problems.Graph.PolygonalDrawing.Neighborhood
import Complexity.Computability.Complexity.Problems.Graph.PolygonalDrawing.Points
import Complexity.Computability.Complexity.Problems.Graph.PolygonalDrawing.Star
import Complexity.Computability.Complexity.Problems.Graph.ClosedPassages.Loop
import Mathlib.Tactic.FinCases

/-!
Ordinary-import regression clients for genuine finite polygonal geometry. These test actual
real segment contacts, high degree, declared point separation and loop closure. They do not
assert the unproved numerical-genus / geometric-realization equivalence.
-/

namespace ComplexityTests.PolygonalDrawing

open Cslib Cslib.Complexity Cslib.Complexity.Graph
open Polygonal RotationSystem

-- The generic construction is valid beyond the orthogonal point-drawing degree bound.
example : (PolygonalDrawing.star 5).IsEmbedding := PolygonalDrawing.star_isEmbedding 5

example : (PolygonalDrawing.star 20).IsEmbedding := PolygonalDrawing.star_isEmbedding 20

-- The nullary star is its sole declared center point.
example : (PolygonalDrawing.star 0).IsEmbedding := PolygonalDrawing.star_isEmbedding 0

-- Repeated declarations are the same point; distinct sparse isolates stay separated.
example : (PolygonalDrawing.points [7, 7, 100, 3, 100]).IsEmbedding :=
  PolygonalDrawing.points_isEmbedding _

example : (PolygonalDrawing.points [7, 7, 100]).vertex 7 ≠
    (PolygonalDrawing.points [7, 7, 100]).vertex 100 :=
  (PolygonalDrawing.points_isEmbedding _).vertex_ne (by decide) (by decide) (by decide)

example (r : RotationSystem ([7, 7, 100], [])) :
    (PolygonalDrawing.points [7, 7, 100]).Realizes r := PolygonalDrawing.points_realizes _ r

-- Checking listed endpoints alone would accept this degenerate loop; simplicity rejects it.
example (z : ℂ) : ¬(Route.line z z).IsSimple := by
  rw [Route.isSimple_line_iff]
  exact not_not.mpr rfl

-- A nondegenerate oblique segment uses every real parameter, including irrational ones.
example : (Route.line 0 (1 + Complex.I)).IsSimple :=
  Route.isSimple_line (by intro h; have := congrArg Complex.im h; norm_num at this)

example : Complex.I / 2 ∈ (Route.line 0 Complex.I).support := by
  apply ((Route.line 0 Complex.I).mem_support_iff _).mpr
  refine ⟨(0 : Fin 1), (1 / 2 : ℝ), by constructor <;> norm_num, ?_⟩
  change AffineMap.lineMap (0 : ℂ) Complex.I (1 / 2 : ℝ) = Complex.I / 2
  rw [AffineMap.lineMap_apply_module']
  apply Complex.ext <;> norm_num [Complex.smul_re, Complex.smul_im]

-- The reversed argument order used in Realizes is literally clockwise: from -1 through I
-- to 1. The opposite order fails in the same fixed complex-plane orientation.
private theorem clockwise_axes :
    sbtw ((1 : ℂ).arg : Real.Angle) ((Complex.I).arg : Real.Angle)
      ((-1 : ℂ).arg : Real.Angle) := by
  rw [Complex.arg_one, Complex.arg_I, Complex.arg_neg_one]
  have hp : (0 : ℝ) < 2 * Real.pi := by linarith [Real.pi_pos]
  let : Fact ((0 : ℝ) < 2 * Real.pi) := ⟨hp⟩
  rw [sbtw_iff_not_btw]
  change ¬btw (Real.pi : ℝ ⧸ AddSubgroup.zmultiples (2 * Real.pi))
    ((Real.pi / 2 : ℝ) : ℝ ⧸ AddSubgroup.zmultiples (2 * Real.pi))
    ((0 : ℝ) : ℝ ⧸ AddSubgroup.zmultiples (2 * Real.pi))
  rw [QuotientAddGroup.btw_coe_iff]
  have hmid : toIcoMod hp Real.pi (Real.pi / 2) = Real.pi / 2 + 2 * Real.pi := by
    apply (toIcoMod_eq_iff hp).mpr
    refine ⟨⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩, -1, ?_⟩
    simp only [neg_one_zsmul]
    ring
  have hend : toIocMod hp Real.pi 0 = 2 * Real.pi := by
    apply (toIocMod_eq_iff hp).mpr
    refine ⟨⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩, -1, ?_⟩
    simp
  rw [hmid, hend]
  linarith [Real.pi_pos]

example : ¬sbtw ((-1 : ℂ).arg : Real.Angle) ((Complex.I).arg : Real.Angle)
    ((1 : ℂ).arg : Real.Angle) := clockwise_axes.not_sbtw

private def triangle : Route where
  bends := 2
  point := fun i => if i.val = 0 then 0 else if i.val = 1 then 1
    else if i.val = 2 then Complex.I else 0

-- Closing a loop at its intended end is permitted; all other contacts are excluded.
private theorem triangle_simple : triangle.IsSimple := by
  intro i j s t hs ht h
  have hr := congrArg Complex.re h
  have hi := congrArg Complex.im h
  fin_cases i <;> fin_cases j <;>
    dsimp [Route.eval, triangle] at hr hi <;>
    norm_num [AffineMap.lineMap_apply_module, Complex.smul_re,
      Complex.smul_im, smul_eq_mul] at hr hi <;>
    simp only [Route.position, Route.AtEnd, triangle, Route.segments,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, zero_add, Bool.false_eq_true, ↓reduceIte] <;>
    norm_num only [Nat.cast_add, Nat.cast_ofNat] <;>
    first
    | exact Or.inl (by linarith)
    | exact Or.inr (Or.inl ⟨by linarith [hs.1, hs.2, ht.1, ht.2], by linarith⟩)
    | exact Or.inr (Or.inr ⟨by linarith [hs.1, hs.2, ht.1, ht.2], by linarith⟩)

private abbrev loopGraph : Graph := ([7, 7], [(7, 7)])

private def loopDrawing : PolygonalDrawing loopGraph where
  vertex := fun _ => 0
  route := fun _ => triangle
  endpoint_eq := by intro e b; cases b <;> rfl

private theorem loop_embedding : loopDrawing.IsEmbedding where
  vertices_injective := by
    intro u hu v hv _
    have hu' : u = 7 := by simpa using hu
    have hv' : v = 7 := by simpa using hv
    exact hu'.trans hv'.symm
  simple := fun _ => triangle_simple
  vertex_contacts := by
    intro e i t ht v hv h
    have hv' : v = 7 := by simpa using hv
    subst v
    have hr := congrArg Complex.re h
    have hi := congrArg Complex.im h
    fin_cases i <;>
      dsimp [loopDrawing, Route.eval, triangle] at hr hi <;>
      norm_num [AffineMap.lineMap_apply_module,
        Complex.smul_re, Complex.smul_im, smul_eq_mul] at hr hi
    · refine ⟨false, ?_, ?_⟩
      · simpa [loopDrawing, Route.AtEnd, Route.position] using hr
      · fin_cases e; rfl
    · linarith
    · refine ⟨true, ?_, ?_⟩
      · simp only [loopDrawing, Route.AtEnd, Route.position, triangle, Route.segments,
          Nat.cast_ofNat, ↓reduceIte]
        norm_num only [Nat.cast_add, Nat.cast_ofNat]
        linarith
      · fin_cases e; rfl
  edge_contacts := by
    intro e f hef
    exact False.elim (hef (Subsingleton.elim (α := Fin 1) _ _))

example : loopDrawing.IsEmbedding := loop_embedding

private def loopRotation : RotationSystem loopGraph where
  rotate := Dart.reversal loopGraph
  sameCycle_iff := by decide

-- The loop has two indexed germs and realizes the actual two-dart rotation.
example : loopDrawing.Realizes loopRotation where
  nonzero := loop_embedding.germ_ne_zero
  directions_injective := loop_embedding.directions_injective
  clockwise := by
    intro a b c _ _ hab hbc hac
    have h : ∀ a b c : Dart loopGraph, a = b ∨ b = c ∨ a = c := by decide
    rcases h a b c with h | h | h
    · exact False.elim (hab h)
    · exact False.elim (hbc h)
    · exact False.elim (hac h)

-- A bridge's one incident germ at each endpoint realizes its singleton rotations.
example : (PolygonalDrawing.star 1).Realizes (starRotation 1) where
  nonzero := (PolygonalDrawing.star_isEmbedding 1).germ_ne_zero
  directions_injective := (PolygonalDrawing.star_isEmbedding 1).directions_injective
  clockwise := by
    intro a b _ hv _ hab _ _
    have h : ∀ a b : Dart (starGraph 1), a.vertex = b.vertex → a = b := by decide
    exact False.elim (hab (h a b hv))

private def bowed (upper : Bool) : Route where
  bends := 1
  point := fun i => if i.val = 0 then 0 else if i.val = 1
    then ⟨1, if upper then 1 else -1⟩ else 2

private theorem bowed_re (upper : Bool) (i : Fin (bowed upper).segments) (t : ℝ) :
    ((bowed upper).eval i t).re = (bowed upper).position i t := by
  fin_cases i <;> dsimp [Route.eval, Route.position, bowed] <;>
    norm_num [AffineMap.lineMap_apply_module, Complex.smul_re, smul_eq_mul]; ring

private theorem bowed_simple (upper : Bool) : (bowed upper).IsSimple := by
  intro i j s t _ _ h
  left
  rw [← bowed_re, ← bowed_re]
  exact congrArg Complex.re h

private abbrev digonGraph : Graph := ([7, 100, 7], [(7, 100), (7, 100)])

private def digonDrawing : PolygonalDrawing digonGraph where
  vertex := fun v => if v = 7 then 0 else 2
  route := fun e => bowed (decide (e.val = 0))
  endpoint_eq := by
    intro e b
    fin_cases e <;> cases b <;> rfl

private theorem digon_embedding : digonDrawing.IsEmbedding where
  vertices_injective := by
    intro u hu v hv h
    have hu' : u = 7 ∨ u = 100 := by simpa [or_assoc, or_left_comm, or_comm] using hu
    have hv' : v = 7 ∨ v = 100 := by simpa [or_assoc, or_left_comm, or_comm] using hv
    rcases hu' with rfl | rfl <;> rcases hv' with rfl | rfl
    · rfl
    · norm_num [digonDrawing] at h
    · norm_num [digonDrawing] at h
    · rfl
  simple := fun e => bowed_simple (decide (e.val = 0))
  vertex_contacts := by
    intro e i t _ v hv h
    have hr : (digonDrawing.route e).position i t = (digonDrawing.vertex v).re :=
      (bowed_re (decide (e.val = 0)) i t).symm.trans (congrArg Complex.re h)
    have hv' : v = 7 ∨ v = 100 := by simpa [or_assoc, or_left_comm, or_comm] using hv
    rcases hv' with rfl | rfl
    · refine ⟨false, ?_, ?_⟩
      · simpa [digonDrawing, Route.AtEnd] using hr
      · fin_cases e <;> rfl
    · refine ⟨true, ?_, ?_⟩
      · simpa [digonDrawing, Route.AtEnd, bowed, Route.segments] using hr
      · fin_cases e <;> rfl
  edge_contacts := by
    intro e f hef i j s t hs ht h
    have hr := congrArg Complex.re h
    have hi := congrArg Complex.im h
    fin_cases e <;> fin_cases f <;> try exact False.elim (hef rfl)
    all_goals
      fin_cases i <;> fin_cases j <;>
        dsimp [digonDrawing, Route.eval, bowed] at hr hi <;>
        norm_num [AffineMap.lineMap_apply_module, Complex.smul_re,
          Complex.smul_im, smul_eq_mul] at hr hi <;>
        first
        | (refine ⟨false, false, ?_, ?_, rfl⟩ <;>
            norm_num [Route.AtEnd, Route.position, digonDrawing, bowed] <;>
            linarith [hs.1, hs.2, ht.1, ht.2])
        | (refine ⟨true, true, ?_, ?_, rfl⟩ <;>
            norm_num [Route.AtEnd, Route.position, digonDrawing, bowed, Route.segments] <;>
            linarith [hs.1, hs.2, ht.1, ht.2])

private def digonRotation : RotationSystem digonGraph where
  rotate := Equiv.prodCongr (Equiv.swap (0 : Fin 2) 1) (Equiv.refl Bool)
  sameCycle_iff := by decide

-- Equal listed endpoint pairs remain two different edge routes and four different germs.
example : digonDrawing.IsEmbedding ∧ digonDrawing.Realizes digonRotation := by
  refine ⟨digon_embedding, digon_embedding.germ_ne_zero,
    digon_embedding.directions_injective, ?_⟩
  intro a b c hv hw hab hbc hac
  have h : ∀ a b c : Dart digonGraph, a.vertex = b.vertex → b.vertex = c.vertex →
      a = b ∨ b = c ∨ a = c := by decide
  rcases h a b c hv hw with h | h | h
  · exact False.elim (hab h)
  · exact False.elim (hbc h)
  · exact False.elim (hac h)

-- Loop germs are separated by the proved geometric contact argument.
example : loopDrawing.direction ((0 : Fin 1), false) ≠
    loopDrawing.direction ((0 : Fin 1), true) := by
  intro h
  have := loop_embedding.directions_injective ((0 : Fin 1), false) ((0 : Fin 1), true)
    (by rfl) h
  exact Bool.false_ne_true (congrArg Prod.snd this)

-- A local neighborhood is constructed internally, even at a repeated declared name.
example : ∃ ε > 0, ∀ e (i : Fin (loopDrawing.route e).segments) w,
    w ∈ Metric.ball (loopDrawing.vertex 7) ε →
    w ∈ segment ℝ ((loopDrawing.route e).point i.castSucc)
      ((loopDrawing.route e).point i.succ) →
      (i.val = 0 ∧ Dart.vertex (e, false) = 7) ∨
      (i.val + 1 = (loopDrawing.route e).segments ∧ Dart.vertex (e, true) = 7) :=
  loop_embedding.exists_vertex_ball 7 (by decide)

end ComplexityTests.PolygonalDrawing
