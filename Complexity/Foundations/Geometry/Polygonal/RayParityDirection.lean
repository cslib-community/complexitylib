/-
Copyright (c) 2026 Erik Demaine, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, OpenAI
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic.Linarith

/-!
# A generic ray direction for finite planar data

Multiplication by a nonzero complex number makes the heights of every two distinct points
in a prescribed finite set different. The multiplier is constructed by avoiding finitely
many forbidden real slopes; no rational-coordinate or existing generic-position assumption
is used. In particular, every nondegenerate segment with ends in the set becomes
nonhorizontal. This is an original finite-avoidance argument.
-/

public section

namespace Cslib.Polygonal

/-- A complex rotation and positive scaling separates the heights of all distinct points
of any finite set. Coincident listed occurrences require no separation and remain coincident. -/
theorem exists_mul_im_injOn (s : Finset ℂ) :
    ∃ u : ℂ, u ≠ 0 ∧ Set.InjOn (fun z => (u * z).im) (↑s : Set ℂ) := by
  classical
  let bad := (s ×ˢ s).image (fun p => (p.2.im - p.1.im) / (p.1.re - p.2.re))
  obtain ⟨m, hm⟩ := bad.exists_notMem
  refine ⟨⟨1, m⟩, ?_, ?_⟩
  · intro h
    have := congrArg Complex.re h
    norm_num at this
  · intro a ha b hb h
    simp only [Complex.mul_im, one_mul] at h
    by_cases hre : a.re = b.re
    · apply Complex.ext hre
      rw [hre] at h
      linarith
    · exfalso
      have hmeq : m = (b.im - a.im) / (a.re - b.re) := by
        apply (eq_div_iff (sub_ne_zero.mpr hre)).mpr
        linarith
      apply hm
      exact Finset.mem_image.mpr ⟨(a, b), Finset.mem_product.mpr ⟨ha, hb⟩, hmeq.symm⟩

end Cslib.Polygonal
