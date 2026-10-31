/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Probability.PairwiseIndependentHash.RetentionChannel
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.LinearAlgebra.StdBasis

/-!
# Frame-conditioned retention channels and their retention slices

A *frame* is an ordered linearly independent family `F : Fin r → (Fin H → ZMod P)`. A
*frame-conditioned channel* is a pair `A = (a₀, F)` of a constant column `a₀ : Fin H → ZMod P`
and a frame `F`. It evaluates an identifier `y : ZMod P` as the polynomial

`A.eval y = a₀ + ∑ j, y ^ (j + 1) • F j`,

and retains `y` when `A.eval y` lies in the retention box `retentionBox P H L`. Drawing a
uniformly random frame-conditioned channel is drawing a uniformly random `H × (r + 1)` matrix
conditioned on its last `r` columns being linearly independent.

For a fixed identifier `y`, the map `A ↦ (F, A.eval y)` is a bijection, since `a₀` is recovered
from the value and the frame (`evalEquiv`). Hence the frame and the evaluation are independent,
the evaluation is uniform, and `y` is retained with probability exactly `(L / P) ^ H` for every
`y` and every `r ≤ H` (`dens_eval_mem_retentionBox`), as without frame conditioning. On the
*retention slice* of `y`, the channels retaining `y`, the same bijection gives coordinates
`(F, w)` with `w` in the box `{0, …, L - 1} ^ H`, which we identify with `ZMod L ^ H`
(`sliceEquiv`). Conditional averaging on the slice is done in these coordinates
(`Complexity.Probability.PairwiseIndependentHash.ConditionalAveraging`).

This follows the rank channels of Section 3 of the OpenAI preprint [OpenAI2026LogSpace]
(channel matrices conditioned on their non-constant columns forming a frame), the exact marginal
in the proof of its Lemma 3.1, and the coordinates `(F, w)` of the proof of its Lemma 6.2.

## Main definitions

* `Cslib.Probability.Frame`: ordered linearly independent `r`-tuples in `ZMod P ^ H`.
* `Cslib.Probability.Frame.mapSL`: an integer matrix of determinant one acting on frames.
* `Cslib.Probability.FrameChannel`, `Cslib.Probability.FrameChannel.eval`: frame-conditioned
  channels and their evaluation at an identifier.
* `Cslib.Probability.FrameChannel.evalEquiv`: a channel is its value at `y` and its frame.
* `Cslib.Probability.retentionBoxEquiv`: the retention box as `ZMod L ^ H`.
* `Cslib.Probability.RetentionSlice`, `Cslib.Probability.sliceEquiv`: the channels retaining
  `y`, and their coordinates `(F, w)`.

## Main results

* `Cslib.Probability.dens_eval_mem_retentionBox`: under frame conditioning, every identifier is
  retained with probability exactly `(L / P) ^ H`.
* `Cslib.Probability.card_retentionSlice`: the slice has `#frames · L ^ H` channels.

## References

* [OpenAI, *Exact Derandomization of Logarithmic Space: L = RL = BPL*][OpenAI2026LogSpace]
-/

public section

namespace Cslib.Probability

open Finset Matrix
open scoped BigOperators

variable (P H r : ℕ)

/-- A **frame**: an ordered linearly independent family of `r` vectors in `ZMod P ^ H`. -/
abbrev Frame : Type :=
  {F : Fin r → Fin H → ZMod P // LinearIndependent (ZMod P) F}

/-- Linear independence of a finite family over `ZMod P` is decided by testing all
coefficient vectors. -/
instance [NeZero P] : Fintype (Frame P H r) :=
  haveI : DecidablePred fun F : Fin r → Fin H → ZMod P ↦ LinearIndependent (ZMod P) F := fun F ↦
    decidable_of_iff (∀ g : Fin r → ZMod P, ∑ i, g i • F i = 0 → ∀ i, g i = 0)
      Fintype.linearIndependent_iff.symm
  Subtype.fintype _

variable {P H r}

/-- For `r ≤ H` the first `r` standard basis vectors form a frame. -/
theorem Frame.nonempty (hr : r ≤ H) : Nonempty (Frame P H r) :=
  ⟨⟨Pi.basisFun (ZMod P) (Fin H) ∘ Fin.castLE hr,
    (Pi.basisFun (ZMod P) (Fin H)).linearIndependent.comp _ (Fin.castLE_injective hr)⟩⟩

/-- An integer matrix of determinant one, reduced modulo `P`, maps frames to frames, column by
column. -/
@[expose] def Frame.mapSL (g : SpecialLinearGroup (Fin H) ℤ) : Frame P H r ≃ Frame P H r :=
  let e := SpecialLinearGroup.toLin' (SpecialLinearGroup.map (Int.castRingHom (ZMod P)) g)
  Equiv.subtypeEquiv (Equiv.piCongrRight fun _ ↦ e.toEquiv) fun _ ↦
    (e.toLinearMap.linearIndependent_iff e.ker).symm

@[simp]
theorem Frame.mapSL_apply (g : SpecialLinearGroup (Fin H) ℤ) (F : Frame P H r) (j : Fin r) :
    (Frame.mapSL g F).1 j = (SpecialLinearGroup.map (Int.castRingHom (ZMod P)) g : Matrix _ _ _)
      *ᵥ F.1 j :=
  rfl

variable (P H r)

/-- A **frame-conditioned channel**: a constant column and a frame. -/
abbrev FrameChannel : Type :=
  (Fin H → ZMod P) × Frame P H r

variable {P H r}

/-- The value `a₀ + ∑ j, y ^ (j + 1) • F j` of the channel `A = (a₀, F)` at the identifier
`y`. -/
@[expose] def FrameChannel.eval (A : FrameChannel P H r) (y : ZMod P) : Fin H → ZMod P :=
  A.1 + ∑ j : Fin r, y ^ (j.val + 1) • A.2.1 j

/-- **Coordinates of a channel at `y`**: its value at `y` and its frame. The constant column is
recovered as the value minus the frame part. -/
@[expose] def FrameChannel.evalEquiv (y : ZMod P) :
    FrameChannel P H r ≃ (Fin H → ZMod P) × Frame P H r where
  toFun A := (A.eval y, A.2)
  invFun p := (p.1 - ∑ j : Fin r, y ^ (j.val + 1) • p.2.1 j, p.2)
  left_inv A := by simp [FrameChannel.eval]
  right_inv p := by simp [FrameChannel.eval]

@[simp]
theorem FrameChannel.evalEquiv_apply (y : ZMod P) (A : FrameChannel P H r) :
    FrameChannel.evalEquiv y A = (A.eval y, A.2) :=
  rfl

variable {L : ℕ} [NeZero P]

/-- **Frame-conditioned retention rate**: for `r ≤ H` and `L ≤ P`, a uniformly random
frame-conditioned channel retains every identifier `y` with probability exactly
`(L / P) ^ H`. -/
theorem dens_eval_mem_retentionBox (hr : r ≤ H) (hL : L ≤ P) (y : ZMod P) :
    dens {A : FrameChannel P H r | A.eval y ∈ retentionBox P H L} = ((L : ℚ≥0) / P) ^ H := by
  have := Frame.nonempty (P := P) hr
  have hcard : #{A : FrameChannel P H r | A.eval y ∈ retentionBox P H L} =
      L ^ H * Fintype.card (Frame P H r) := by
    rw [← card_retentionBox (H := H) hL, ← card_univ (α := Frame P H r), ← card_product]
    refine card_bij (fun A _ ↦ FrameChannel.evalEquiv y A) (fun A hA ↦ ?_)
      (fun _ _ _ _ h ↦ (FrameChannel.evalEquiv y).injective h) fun p hp ↦ ?_
    · simpa using hA
    · refine ⟨(FrameChannel.evalEquiv y).symm p, ?_, by simp⟩
      have : ((FrameChannel.evalEquiv y).symm p).eval y = p.1 := by
        simp [FrameChannel.evalEquiv, FrameChannel.eval]
      simpa [this] using (mem_product.1 hp).1
  have hpos : (0 : ℚ≥0) < Fintype.card (Frame P H r) := by exact_mod_cast Fintype.card_pos
  rw [dens, hcard, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, ZMod.card, div_pow]
  push_cast
  rw [mul_div_mul_right _ _ hpos.ne']

variable (P H r L)

/-- The **retention slice** of `y`: the frame-conditioned channels retaining `y`. -/
abbrev RetentionSlice (y : ZMod P) : Type :=
  {A : FrameChannel P H r // A.eval y ∈ retentionBox P H L}

variable {P H r L}

/-- The retention box `{0, …, L - 1} ^ H` in `ZMod P ^ H` is `ZMod L ^ H` for `L ≤ P`, by
reading representatives. -/
@[expose] def retentionBoxEquiv [NeZero L] (hL : L ≤ P) :
    {w : Fin H → ZMod P // w ∈ retentionBox P H L} ≃ (Fin H → ZMod L) where
  toFun w i := ((w.1 i).val : ZMod L)
  invFun u := ⟨fun i ↦ ((u i).val : ZMod P), by
    simp only [mem_retentionBox]
    intro i
    rw [ZMod.val_cast_of_lt ((ZMod.val_lt _).trans_le hL)]
    exact ZMod.val_lt _⟩
  left_inv w := by
    have hw := w.2
    simp only [mem_retentionBox] at hw
    ext i
    simp only
    rw [ZMod.val_cast_of_lt (hw i), ZMod.natCast_zmod_val]
  right_inv u := by
    ext i
    simp only
    rw [ZMod.val_cast_of_lt ((ZMod.val_lt _).trans_le hL), ZMod.natCast_zmod_val]

@[simp]
theorem retentionBoxEquiv_apply [NeZero L] (hL : L ≤ P)
    (w : {w : Fin H → ZMod P // w ∈ retentionBox P H L}) (i : Fin H) :
    retentionBoxEquiv hL w i = ((w.1 i).val : ZMod L) :=
  rfl

@[simp]
theorem retentionBoxEquiv_symm_apply [NeZero L] (hL : L ≤ P) (u : Fin H → ZMod L) (i : Fin H) :
    ((retentionBoxEquiv hL).symm u).1 i = ((u i).val : ZMod P) :=
  rfl

/-- **Coordinates on a retention slice**: a channel retaining `y` is its frame together with its
value at `y`, which ranges over the whole box `ZMod L ^ H`. -/
@[expose] def sliceEquiv [NeZero L] (hL : L ≤ P) (y : ZMod P) :
    RetentionSlice P H r L y ≃ Frame P H r × (Fin H → ZMod L) :=
  ((FrameChannel.evalEquiv y).subtypeEquiv (p := fun A ↦ A.eval y ∈ retentionBox P H L)
      (q := fun p ↦ p.1 ∈ retentionBox P H L) fun _ ↦ Iff.rfl).trans <|
    (Equiv.prodSubtypeFstEquivSubtypeProd (p := (· ∈ retentionBox P H L))).trans <|
      ((retentionBoxEquiv hL).prodCongr (Equiv.refl _)).trans (Equiv.prodComm _ _)

@[simp]
theorem sliceEquiv_apply [NeZero L] (hL : L ≤ P) (y : ZMod P) (A : RetentionSlice P H r L y) :
    sliceEquiv hL y A = (A.1.2, fun i ↦ ((A.1.eval y i).val : ZMod L)) :=
  rfl

/-- The frame of a channel is its frame coordinate on the slice. -/
@[simp]
theorem sliceEquiv_symm_apply_snd [NeZero L] (hL : L ≤ P) (y : ZMod P)
    (p : Frame P H r × (Fin H → ZMod L)) : ((sliceEquiv hL y).symm p).1.2 = p.1 := by
  have h := congrArg Prod.fst ((sliceEquiv hL y).apply_symm_apply p)
  rwa [sliceEquiv_apply] at h

/-- The value at `y` of the channel with coordinates `(F, w)` is `w`, read in `ZMod P`. -/
@[simp]
theorem eval_sliceEquiv_symm [NeZero L] (hL : L ≤ P) (y : ZMod P)
    (p : Frame P H r × (Fin H → ZMod L)) (i : Fin H) :
    ((sliceEquiv hL y).symm p).1.eval y i = ((p.2 i).val : ZMod P) := by
  have h := congrArg (fun q ↦ q.2 i) ((sliceEquiv hL y).apply_symm_apply p)
  simp only [sliceEquiv_apply] at h
  rw [← h, ZMod.val_cast_of_lt (mem_retentionBox.1 ((sliceEquiv hL y).symm p).2 i),
    ZMod.natCast_zmod_val]

/-- A retention slice has `#frames · L ^ H` channels. -/
theorem card_retentionSlice [NeZero L] (hL : L ≤ P) (y : ZMod P) :
    Fintype.card (RetentionSlice P H r L y) = Fintype.card (Frame P H r) * L ^ H := by
  rw [Fintype.card_congr (sliceEquiv hL y), Fintype.card_prod, Fintype.card_fun,
    Fintype.card_fin, ZMod.card]

end Cslib.Probability
