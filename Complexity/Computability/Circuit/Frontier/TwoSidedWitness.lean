/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Frontier.Rectangle
public import Cslib.Foundations.Data.BitString
import Complexity.Computability.Circuit.Frontier.Witness

/-!
# Functions with two rectangle-free fibers

Bias strictly below `1 / 2` excludes monochromatic rectangles of positive size. Applying the
probabilistic existence theorem for rectangle bias with bias `1 / 4` and threshold `16 (n + 1)`
therefore gives Boolean functions whose two fibers are rectangle-free at that threshold.

This proves nonvacuity of the two-sided rectangle hypothesis used by the threshold-circuit
lower bounds. The existence statement is nonconstructive and asserts no evaluation-time bound.

## Main results

* `Cslib.Circuits.Frontier.RectangleBias.rectangleFree`: bias below one half implies
  rectangle-freeness.
* `Cslib.Circuits.Frontier.RectangleBias.rectangleFree_compl`: the complementary set is
  rectangle-free as well.
* `Cslib.Circuits.Frontier.exists_twoSided_rectangleFree`: both fibers can be
  `16 (n + 1)`-rectangle-free for every input length `n`.

## References

The probabilistic existence argument is in `Complexity.Computability.Circuit.Frontier.Witness`;
see [Alon and Spencer, *The Probabilistic Method*][AlonSpencer2016].
-/

@[expose] public section

namespace Cslib.Circuits.Frontier

open Set

variable {ι U : Type*} [Finite ι] [Finite U] {S : Set (ι → U)} {K : ℕ} {b : ℝ}

/-- A set with bias strictly below one half on large rectangles contains no such rectangle. -/
theorem RectangleBias.rectangleFree (hS : RectangleBias S K b) (hb : b < 1 / 2)
    (hK : 0 < K) : RectangleFree S K := by
  apply rectangleFree_iff.mpr
  intro X A B hAB
  by_contra h
  push Not at h
  have hpos : (0 : ℝ) < (rectangle X A B).ncard := by
    rw [ncard_rectangle]
    exact_mod_cast Nat.mul_pos (hK.trans_le h.1) (hK.trans_le h.2)
  have hbound := hS X A B h.1 h.2
  rw [inter_eq_left.mpr hAB, abs_of_nonneg (by linarith)] at hbound
  nlinarith

/-- The complement of a set with bias strictly below one half also contains no large rectangle. -/
theorem RectangleBias.rectangleFree_compl (hS : RectangleBias S K b) (hb : b < 1 / 2)
    (hK : 0 < K) : RectangleFree Sᶜ K := by
  apply rectangleFree_iff.mpr
  intro X A B hAB
  by_contra h
  push Not at h
  have hpos : (0 : ℝ) < (rectangle X A B).ncard := by
    rw [ncard_rectangle]
    exact_mod_cast Nat.mul_pos (hK.trans_le h.1) (hK.trans_le h.2)
  have hbound := hS X A B h.1 h.2
  have hempty : rectangle X A B ∩ S = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    exact hAB hx.1 hx.2
  rw [hempty, ncard_empty, Nat.cast_zero, zero_sub, abs_neg,
    abs_of_nonneg (by positivity)] at hbound
  nlinarith

/-- For every input length, there is a Boolean function whose two fibers are
`16 (n + 1)`-rectangle-free. This is nonconstructive; no evaluation-time bound is asserted. -/
theorem exists_twoSided_rectangleFree (n : ℕ) :
    ∃ f : Cslib.BooleanFunction n, ∀ a : Bool,
      RectangleFree {x | f x = a} (16 * (n + 1)) := by
  classical
  obtain ⟨S, hS⟩ := exists_rectangleBias (ι := Fin n) (K := 16 * (n + 1))
    (b := 1 / 4) (by norm_num) (by push_cast; norm_num; ring_nf; rfl)
  refine ⟨fun x => decide (x ∈ S), fun a => ?_⟩
  cases a
  · have hset : {x | decide (x ∈ S) = false} = Sᶜ := by
      ext x
      simp
    rw [hset]
    exact hS.rectangleFree_compl (by norm_num) (by omega)
  · have hset : {x | decide (x ∈ S) = true} = S := by
      ext x
      simp
    rw [hset]
    exact hS.rectangleFree (by norm_num) (by omega)

end Cslib.Circuits.Frontier
