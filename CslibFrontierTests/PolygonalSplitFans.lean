/-
Copyright (c) 2026 Erik Demaine, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, OpenAI
-/

import CslibFrontier.Foundations.Geometry.Polygonal.CircleConnector
import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Realization.EdgeTransport
import CslibFrontier.Computability.Complexity.Problems.Graph.PolygonalDrawing.Star

/-!
Automatic two-fan geometry on actual finite circle points, including arbitrary degrees and
empty blocks. These clients choose no centers, affine separator or connector order. They
test all real spoke parameters. They do not assert general graph restoration.
-/

namespace CslibFrontierTests.PolygonalSplitFans

open Cslib Cslib.Polygonal Cslib.Complexity Cslib.Complexity.Graph

private noncomputable def angle (n : ℕ) (i : Fin n) : ℝ :=
  ((i.val : ℝ) + 1) * Real.pi / (n + 1)

private theorem angle_pos {n : ℕ} (i : Fin n) : 0 < angle n i := by
  unfold angle
  positivity

private theorem angle_lt_pi {n : ℕ} (i : Fin n) : angle n i < Real.pi := by
  have hi : (i.val : ℝ) < n := by exact_mod_cast i.isLt
  rw [angle, div_lt_iff₀ (by positivity)]
  nlinarith [Real.pi_pos]

private noncomputable def upper (n : ℕ) (i : Fin n) : ℂ := circlePoint 0 1 (angle n i)

private noncomputable def lower (n : ℕ) (i : Fin n) : ℂ := circlePoint 0 1 (-angle n i)

private theorem upper_im {n : ℕ} (i : Fin n) : 0 < (upper n i).im := by
  rw [upper, circlePoint, zero_add, Complex.ofReal_one, one_mul]
  simpa only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
    Complex.I_im, Complex.I_re, mul_one, mul_zero, zero_add, add_zero] using
    Real.sin_pos_of_pos_of_lt_pi (angle_pos i) (angle_lt_pi i)

private theorem lower_im {n : ℕ} (i : Fin n) : (lower n i).im < 0 := by
  rw [lower, circlePoint, zero_add, Complex.ofReal_one, one_mul]
  simpa only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
    Complex.I_im, Complex.I_re, mul_one, mul_zero, zero_add, add_zero, Real.sin_neg] using
    neg_lt_zero.mpr (Real.sin_pos_of_pos_of_lt_pi (angle_pos i) (angle_lt_pi i))

private noncomputable def upperPorts (n : ℕ) : Finset ℂ := Finset.univ.image (upper n)

private noncomputable def lowerPorts (n : ℕ) : Finset ℂ := Finset.univ.image (lower n)

-- There is no degree bound; n or m may be zero, and the full real segment is tested.
private theorem automatic_fans (n m : ℕ) :
    ∃ a ∈ Metric.ball (0 : ℂ) 1, ∃ b ∈ Metric.ball (0 : ℂ) 1,
      ∀ (i : Fin n) (j : Fin m) (s t : ℝ), s ∈ Set.Icc 0 1 → t ∈ Set.Icc 0 1 →
        AffineMap.lineMap a (upper n i) s ≠ AffineMap.lineMap b (lower m j) t := by
  classical
  have hA (x : ℂ) (hx : x ∈ upperPorts n) : x ∈ Metric.sphere (0 : ℂ) 1 ∧
      turnArg x ∈ Set.Ioo 0 (0 + 2 * Real.pi) ∧
      ((x - 0).arg : Real.Angle) = (turnArg x : Real.Angle) := by
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    refine ⟨circlePoint_mem_sphere 0 (by norm_num) _, ?_, ?_⟩
    · simpa only [zero_add] using turnArg_mem (upper_im i).ne'
    · simp only [sub_zero, turnArg_coe_angle]
  have hB (x : ℂ) (hx : x ∈ lowerPorts m) : x ∈ Metric.sphere (0 : ℂ) 1 ∧
      turnArg x ∈ Set.Ioo 0 (0 + 2 * Real.pi) ∧
      ((x - 0).arg : Real.Angle) = (turnArg x : Real.Angle) := by
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    refine ⟨circlePoint_mem_sphere 0 (by norm_num) _, ?_, ?_⟩
    · simpa only [zero_add] using turnArg_mem (lower_im i).ne
    · simp only [sub_zero, turnArg_coe_angle]
  have hAB : ∀ x ∈ upperPorts n, ∀ y ∈ lowerPorts m, turnArg x < turnArg y := by
    intro x hx y hy
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hy
    exact (turnArg_lt_iff (upper_im i).ne' (lower_im j).ne).mpr
      (Or.inl ⟨upper_im i, lower_im j⟩)
  obtain ⟨a, ha, b, hb, f, hsep, hpa, hpb, _, _⟩ :=
    exists_split_fans_of_finite_blocks (by norm_num) (upperPorts n) (lowerPorts m)
      turnArg 0 hA hB hAB
  refine ⟨a, ha, b, hb, fun i j s t hs ht => split_spokes_ne f hsep
    (hpa _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩))
    (hpb _ (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)) hs ht⟩

example : ∃ a ∈ Metric.ball (0 : ℂ) 1, ∃ b ∈ Metric.ball (0 : ℂ) 1,
    ∀ (i : Fin 9) (j : Fin 7) (s t : ℝ), s ∈ Set.Icc 0 1 → t ∈ Set.Icc 0 1 →
      AffineMap.lineMap a (upper 9 i) s ≠ AffineMap.lineMap b (lower 7 j) t :=
  automatic_fans 9 7

example : ∃ a ∈ Metric.ball (0 : ℂ) 1, ∃ b ∈ Metric.ball (0 : ℂ) 1,
    ∀ (i : Fin 0) (j : Fin 6) (s t : ℝ), s ∈ Set.Icc 0 1 → t ∈ Set.Icc 0 1 →
      AffineMap.lineMap a (upper 0 i) s ≠ AffineMap.lineMap b (lower 6 j) t :=
  automatic_fans 0 6

example : ∃ a ∈ Metric.ball (0 : ℂ) 1, ∃ b ∈ Metric.ball (0 : ℂ) 1,
    ∀ (i : Fin 0) (j : Fin 0) (s t : ℝ), s ∈ Set.Icc 0 1 → t ∈ Set.Icc 0 1 →
      AffineMap.lineMap a (upper 0 i) s ≠ AffineMap.lineMap b (lower 0 j) t :=
  automatic_fans 0 0

-- Moving an actual selected edge of a high-degree star last retains its embedding.
example : ∃ H u v, ∃ D : PolygonalDrawing (RotationSystem.lastEdgeGraph H u v),
    D.IsEmbedding ∧ H.2.length + 1 = (RotationSystem.starGraph 9).2.length := by
  obtain ⟨H, u, v, e, hV, hlength, hv, _⟩ :=
    exists_lastEdge_reindex (RotationSystem.starGraph 9) ⟨3, by decide⟩
  refine ⟨H, u, v, (PolygonalDrawing.star 9).edgeTransport e hv, ?_, hlength⟩
  exact (PolygonalDrawing.star_isEmbedding 9).edgeTransport e hv (fun w => by
    change w ∈ (RotationSystem.starGraph 9).1 ↔ w ∈ H.1
    rw [hV])

end CslibFrontierTests.PolygonalSplitFans
