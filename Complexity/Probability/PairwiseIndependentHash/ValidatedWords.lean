/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Foundations.Combinatorics.Expander.Lazy
public import Complexity.Probability.PairwiseIndependentHash.SliceGap

/-!
# Validated words of the lazy conditional walk

The conditional walk on a retention slice moves channels by affine moves that refer to the
identifier `y`. It is implemented by *validated variants* (`variantMove`), permutations of all
channels that do not refer to `y`, filtered by a wrap test on the value `A.eval y`
(`IsValidWrap`); for one step, the sum of the variants passing the test is the conditional move
(`walk_sliceGraph_ofPerms_eq`). This module extends this to words of every length, for the lazy
walk that the spectral-gap results use.

The **validated step** (`validatedStep`) maps a function `g` of the channel to
`A ↦ (g A + 𝔼 over generators and directions of ∑ over candidate wraps z of
[the wrap z passes at A] g (variant_z A)) / 2`. By induction on `t`, `t` steps of the lazy walk on
the slice, applied to a function of the channel, are the `t`-th iterate of the validated step,
evaluated at the channel (`walk_pow_sliceGraph_lazy_ofPerms_eq`). Unfolding the iterate, this is
the average over words of `t` moves (generators with directions, or stays) of the sum over words
of `t` wraps of `f` at the end of the variant path, counted only when every wrap passes its test:
exactly one word of wraps survives, and nothing is divided by the number of candidate wraps. For
the affine generators (`affineGenerator`), every valid wrap lies in the fixed box
`{-3, …, 3} ^ H`, independently of `P`, `L`, `y` and `t`
(`walk_pow_sliceGraph_lazy_affineMove_eq`).

This is Lemma 6.3 of the OpenAI preprint on derandomizing logarithmic space [OpenAI2026LogSpace],
items 1–4, for length-`t` words of the lazy walk on one channel: the variants form a
bounded-alphabet family described by `O(t)` symbols, independent of the identifiers, and the sum
of the valid variants is the conditional walk.

## Main definitions

* `Cslib.Probability.validatedStep`: one step of the validated lazy walk on all channels.

## Main results

* `Cslib.Probability.walk_pow_sliceGraph_lazy_ofPerms_eq`: validated words of every length
  compute the lazy conditional walk.
* `Cslib.Probability.walk_pow_sliceGraph_lazy_affineMove_eq`: the same for the affine generators,
  with the candidate wraps `{-3, …, 3} ^ H`.

## References

* [OpenAI, *Exact Derandomization of Logarithmic Space: L = RL = BPL*][OpenAI2026LogSpace]
-/

public section

namespace Cslib.Probability

open Finset RotationMap
open scoped BigOperators

variable {P H r L : ℕ} [NeZero P] {K : Type*} [Fintype K]

variable (L) in
/-- **One step of the validated lazy walk** on all channels: with probability `1 / 2` stay, and
otherwise pick a generator `σ k` and a direction, and sum the values at the variants whose wrap
passes the test at the identifier `y`, over the candidate wraps `Z`. It refers to `y` only through
the wrap test on the value `A.eval y`. -/
@[expose] noncomputable def validatedStep
    (σ : K → Matrix.SpecialLinearGroup (Fin H) ℤ × (Fin H → ℤ)) (Z : Finset (Fin H → ℤ))
    (y : ZMod P) (g : FrameChannel P H r → ℝ) (A : FrameChannel P H r) : ℝ :=
  (g A + 𝔼 kb : K × Bool, ∑ z ∈ Z,
    (if IsValidWrap L (signedMove (σ kb.1) kb.2).1 (signedMove (σ kb.1) kb.2).2 z (A.eval y)
      then g (variantMove L (signedMove (σ kb.1) kb.2).1 (signedMove (σ kb.1) kb.2).2 z A)
      else 0)) / 2

/-- **Validated words compute the conditional walk** (Lemma 6.3 for words of every length). For a
family `σ` of affine generators and a candidate set `Z` containing every valid wrap, `t` steps of
the lazy walk of their moves on the retention slice of `y`, applied to a function `f` of the
channel, equal `t` iterations of the validated step, evaluated at the channel. Unfolding the
iterations, this is the average over words of `t` generators and directions (or stays) of the sum,
over words of wraps, of `f` at the end of the variant path, counted only when every wrap passes
its test. -/
theorem walk_pow_sliceGraph_lazy_ofPerms_eq [Nonempty K] [NeZero L] (hL : L ≤ P) {y : ZMod P}
    (σ : K → Matrix.SpecialLinearGroup (Fin H) ℤ × (Fin H → ℤ)) {Z : Finset (Fin H → ℤ)}
    (hZ : ∀ k b, ∀ w ∈ retentionBox P H L,
      wrap L (signedMove (σ k) b).1 (signedMove (σ k) b).2 w ∈ Z)
    (f : FrameChannel P H r → ℝ) (t : ℕ) (A : RetentionSlice P H r L y) :
    ((sliceGraph L hL y (ofPerms fun k ↦ coordMove (σ k).1 (σ k).2).lazy).walk ^ t)
        (fun B ↦ f B.1) A =
      (validatedStep L σ Z y)^[t] f A.1 := by
  induction t generalizing A with
  | zero => rfl
  | succ t ih =>
    have hfun : ((sliceGraph L hL y (ofPerms fun k ↦ coordMove (σ k).1 (σ k).2).lazy).walk ^ t)
        (fun B ↦ f B.1) = fun B ↦ (validatedStep L σ Z y)^[t] f B.1 := funext ih
    rw [pow_succ', Module.End.mul_apply, hfun, Function.iterate_succ_apply']
    set h := (validatedStep L σ Z y)^[t] f
    have hstep := walk_sliceGraph_ofPerms_eq hL σ hZ h A
    simp only [sliceGraph, walk_reindex] at hstep ⊢
    rw [walk_lazy_apply, hstep, validatedStep]
    simp only [Function.comp_apply, Equiv.symm_symm, Equiv.symm_apply_apply]


/-- The row sums of absolute values of a transvection `1 + c E_ab` are at most `1 + |c|`. -/
private theorem sum_abs_transvection_le {a b : Fin H} (h : a ≠ b) (c : ℤ) (i : Fin H) :
    ∑ j, |(Matrix.SpecialLinearGroup.transvection h c : Matrix (Fin H) (Fin H) ℤ) i j| ≤
      1 + |c| := by
  calc _ ≤ ∑ j, ((if i = j then 1 else 0) + (if j = b then |c| else 0)) := by
        refine sum_le_sum fun j _ ↦ ?_
        rw [Matrix.SpecialLinearGroup.transvection_coe]
        simp only [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
        refine (abs_add_le _ _).trans (add_le_add (le_of_eq ?_) ?_)
        · split_ifs <;> simp
        · by_cases hij : a = i ∧ b = j
          · obtain ⟨rfl, rfl⟩ := hij
            simp
          · simp only [hij, ite_false, abs_zero]
            split_ifs <;> simp
    _ = 1 + |c| := by simp [sum_add_distrib]

/-- Every valid wrap of the affine generators and their inverses lies in `{-3, …, 3} ^ H`. -/
private theorem wrap_affineGenerator_mem (k : {p : Fin H × Fin H // p.1 ≠ p.2} ⊕ Fin H) (b : Bool)
    {w : Fin H → ZMod P} (hw : w ∈ retentionBox P H L) [NeZero L] :
    wrap L (signedMove (affineGenerator H k) b).1 (signedMove (affineGenerator H k) b).2 w ∈
      Fintype.piFinset fun _ ↦ Icc (-3 : ℤ) 3 := by
  rw [Fintype.mem_piFinset]
  intro i
  rw [mem_Icc, ← abs_le]
  refine (abs_wrap_le _ _ hw i).trans ?_
  rcases k with p | j <;> cases b
  · have := sum_abs_transvection_le p.2 1 i
    simp only [signedMove, affineGenerator, Sum.elim_inl, Bool.cond_false, Pi.zero_apply, abs_zero,
      add_zero]
    norm_num at this
    linarith
  · have := sum_abs_transvection_le p.2 (-1) i
    simp only [signedMove, affineGenerator, Sum.elim_inl, Bool.cond_true,
      Matrix.SpecialLinearGroup.transvection_inv, Matrix.mulVec_zero, neg_zero, Pi.zero_apply,
      abs_zero, add_zero]
    norm_num at this
    linarith
  · simp only [signedMove, affineGenerator, Sum.elim_inr, Bool.cond_false,
      Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply]
    have : |(Pi.single j 1 : Fin H → ℤ) i| ≤ 1 := by
      rw [Pi.single_apply]
      split_ifs <;> simp
    simp only [apply_ite, abs_one, abs_zero, sum_ite_eq, mem_univ, ite_true]
    linarith
  · simp only [signedMove, affineGenerator, Sum.elim_inr, Bool.cond_true, inv_one,
      Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply, Matrix.one_mulVec, Pi.neg_apply,
      abs_neg]
    have : |(Pi.single j 1 : Fin H → ℤ) i| ≤ 1 := by
      rw [Pi.single_apply]
      split_ifs <;> simp
    simp only [apply_ite, abs_one, abs_zero, sum_ite_eq, mem_univ, ite_true]
    linarith

/-- **Validated words of the affine walk**: `t` steps of the lazy affine walk on the retention slice
of `y` equal `t` iterations of the validated step of the affine generators, with the candidate
wraps `{-3, …, 3} ^ H`, a box independent of `P`, `L`, `y` and `t`. -/
theorem walk_pow_sliceGraph_lazy_affineMove_eq [NeZero H] [NeZero L] (hL : L ≤ P) {y : ZMod P}
    (f : FrameChannel P H r → ℝ) (t : ℕ) (A : RetentionSlice P H r L y) :
    ((sliceGraph L hL y (ofPerms (affineMove P H L r)).lazy).walk ^ t) (fun B ↦ f B.1) A =
      (validatedStep L (affineGenerator H) (Fintype.piFinset fun _ ↦ Icc (-3) 3) y)^[t] f A.1 := by
  have : Nonempty ({p : Fin H × Fin H // p.1 ≠ p.2} ⊕ Fin H) := ⟨.inr 0⟩
  exact walk_pow_sliceGraph_lazy_ofPerms_eq hL (affineGenerator H)
    (fun k b _ hw ↦ wrap_affineGenerator_mem k b hw) f t A

end Cslib.Probability
