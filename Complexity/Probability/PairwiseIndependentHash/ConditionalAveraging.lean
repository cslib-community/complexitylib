/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Foundations.Combinatorics.Expander.Mixing
public import Complexity.Foundations.Combinatorics.Expander.Perm
public import Complexity.Foundations.Combinatorics.Expander.Reindex
public import Complexity.Probability.PairwiseIndependentHash.FrameChannel

/-!
# Conditional averaging on retention slices

A *retention slice* (`Cslib.Probability.RetentionSlice`) is the set of frame-conditioned channels
`A = (a₀, F)` that retain a fixed identifier `y`; its uniform law is the channel law conditioned on
retaining `y`. In the coordinates `(F, w)` of `sliceEquiv`, with `w ∈ ZMod L ^ H` the value at `y`,
an integer matrix `g` of determinant one and an integer vector `c` act by the **affine move**

`coordMove g c (F, w) = (g F mod P, g w + c mod L)`.

Any regular multigraph `G` on the coordinates transports to a walk on every slice
(`sliceGraph`), with the same spectral expansion (`spectralExpansion_sliceGraph`). Hence a single
spectral-gap bound for `G`, independent of `y`, gives **conditional averaging**: on every slice, the
walk of length `t` contracts the conditional variance by `λ(G) ^ (2 t)`
(`expect_walk_pow_sliceGraph_sub_expect_sq_le`). The bound for the walk of the preprint's affine
moves on frames (the frame-lifted gap) is a hypothesis here; later work supplies it.

**Validated variants.** The move on a slice refers to `y`, but it is realized by permutations of
the full channel space that do not:

`variantMove L g c z (a₀, F) = (g a₀ + c + L z, g F) mod P`,

one for each integer *wrap* vector `z`. Each variant is a bijection of all channels. Computing
`x = g w + c` over the integers from the representatives `w` of `A.eval y`, the *wrap test*
`IsValidWrap L g c z (A.eval y)` checks that `x + L z` lies in `{0, …, L - 1} ^ H`. Exactly one
`z` passes, namely `wrap L g c (A.eval y) = -⌊x / L⌋` (`isValidWrap_iff`), and it lies in the
fixed box `|z i| ≤ ∑ j, |g i j| + |c i|` for every side length (`abs_wrap_le`). On a channel
retaining `y`, that variant is the affine move (`variantMove_wrap_eq`). So the sum of the passing
variants over any candidate set of wraps is the move (`sum_ite_isValidWrap`), and the walk of a
family of moves on a slice is the average over moves of these sums
(`walk_sliceGraph_ofPerms_eq`).

This formalizes ideas of Section 6 of the OpenAI preprint [OpenAI2026LogSpace]: the
coordinates and the action `(F, w) ↦ (MF, Mw + c)` in the proof of Lemma 6.2, and the variants
`A' = MA + (c + Lz) e₁ᵀ (mod P)` with their unique valid wrap `zᵢ = -⌊(Mw + c)ᵢ / L⌋` in the
proof of Lemma 6.3 (items 1–4 for a single step). The preprint's walk uses the elementary
generators of `SL_H(ℤ) ⋉ ℤ^H` and its gap comes from property (T) (Lemma 6.1); here the walk and
its gap are left abstract. Transitivity of the action, the product over several channels, and
`L^s` bounds for `s > 2` are not part of this module.

## Main definitions

* `Cslib.Probability.affineSL`: the affine permutation `v ↦ g v + c` of `R ^ n`, for `g` an integer
  matrix of determinant one.
* `Cslib.Probability.coordMove`: the affine move on slice coordinates.
* `Cslib.Probability.sliceGraph`: a graph on the coordinates, transported to a retention slice.
* `Cslib.Probability.variantMove`: a variant, a permutation of all channels.
* `Cslib.Probability.IsValidWrap`, `Cslib.Probability.wrap`: the wrap test and its solution.

## Main results

* `Cslib.Probability.coordMove_symm`: the inverse move is the move of the inverse.
* `Cslib.Probability.spectralExpansion_sliceGraph`: the transported walk keeps its gap.
* `Cslib.Probability.expect_walk_pow_sliceGraph_sub_expect_sq_le`: conditional averaging.
* `Cslib.Probability.eval_variantMove`: a variant acts affinely on every evaluation.
* `Cslib.Probability.isValidWrap_iff`, `Cslib.Probability.abs_wrap_le`: the valid wrap is unique
  and bounded independently of `L` and `P`.
* `Cslib.Probability.variantMove_wrap_eq`: on a slice, the valid variant is the affine move.
* `Cslib.Probability.sum_ite_isValidWrap`, `Cslib.Probability.walk_sliceGraph_ofPerms_eq`: the
  sum of the valid variants is the conditional move, and averages to the conditional walk.

## References

* [OpenAI, *Exact Derandomization of Logarithmic Space: L = RL = BPL*][OpenAI2026LogSpace]
-/

public section

namespace Cslib.Probability

open Finset Matrix
open scoped BigOperators

section Affine

variable {n : Type*} [Fintype n] [DecidableEq n] (R : Type*) [CommRing R]

/-- The affine permutation `v ↦ g v + c` of `R ^ n`, for an integer matrix `g` of determinant one
reduced into `R`. -/
@[expose] def affineSL (g : SpecialLinearGroup n ℤ) (c : n → R) : Equiv.Perm (n → R) :=
  (SpecialLinearGroup.toLin' (SpecialLinearGroup.map (Int.castRingHom R) g)).toEquiv.trans
    (Equiv.addRight c)

@[simp]
theorem affineSL_apply (g : SpecialLinearGroup n ℤ) (c : n → R) (v : n → R) :
    affineSL R g c v = (SpecialLinearGroup.map (Int.castRingHom R) g : Matrix n n R) *ᵥ v + c :=
  rfl

end Affine

variable {P H r L : ℕ} [NeZero P]

/-- The **affine move** `(F, w) ↦ (g F, g w + c)` on slice coordinates: `g` acts on the frame
modulo `P` and on the box coordinate modulo `L`. -/
@[expose] def coordMove (g : SpecialLinearGroup (Fin H) ℤ) (c : Fin H → ℤ) :
    Equiv.Perm (Frame P H r × (Fin H → ZMod L)) :=
  (Frame.mapSL g).prodCongr (affineSL (ZMod L) g fun i ↦ (c i : ZMod L))

omit [NeZero P] in
/-- The inverse of the move by `(g, c)` is the move by `(g⁻¹, -g⁻¹ c)`. -/
theorem coordMove_symm (g : SpecialLinearGroup (Fin H) ℤ) (c : Fin H → ℤ) :
    (coordMove (P := P) (r := r) (L := L) g c).symm =
      coordMove g⁻¹
        (-(((g⁻¹ : SpecialLinearGroup (Fin H) ℤ) : Matrix (Fin H) (Fin H) ℤ) *ᵥ c)) := by
  refine Equiv.ext fun p ↦ (coordMove (P := P) (r := r) (L := L) g c).injective ?_
  rw [Equiv.apply_symm_apply]
  obtain ⟨F, w⟩ := p
  ext j i
  · simp only [coordMove, Equiv.prodCongr_apply, Prod.map_fst, Frame.mapSL_apply, mulVec_mulVec,
      ← SpecialLinearGroup.coe_mul, ← map_mul, mul_inv_cancel, map_one, SpecialLinearGroup.coe_one,
      one_mulVec]
  · have hc : (fun i ↦ (((-(((g⁻¹ : SpecialLinearGroup (Fin H) ℤ) : Matrix (Fin H) (Fin H) ℤ) *ᵥ
        c)) i : ℤ) : ZMod L)) = -((SpecialLinearGroup.map (Int.castRingHom (ZMod L)) g⁻¹ :
          Matrix (Fin H) (Fin H) (ZMod L)) *ᵥ fun i ↦ (c i : ZMod L)) := by
      ext i
      rw [Pi.neg_apply, Pi.neg_apply, Int.cast_neg, SpecialLinearGroup.map_apply_coe,
        RingHom.mapMatrix_apply]
      exact congrArg Neg.neg (RingHom.map_mulVec (Int.castRingHom (ZMod L)) _ c i)
    simp only [coordMove, Equiv.prodCongr_apply, Prod.map_snd, affineSL_apply, hc, mulVec_add,
      mulVec_neg, mulVec_mulVec, ← SpecialLinearGroup.coe_mul, ← map_mul, mul_inv_cancel, map_one,
      SpecialLinearGroup.coe_one, one_mulVec]
    simp

variable (L) in
/-- A graph `G` on slice coordinates, transported to the retention slice of `y`. -/
@[expose] def sliceGraph [NeZero L] (hL : L ≤ P) (y : ZMod P) {D : Type*}
    (G : RotationMap (Frame P H r × (Fin H → ZMod L)) D) :
    RotationMap (RetentionSlice P H r L y) D :=
  G.reindex (sliceEquiv hL y).symm

/-- The walk on a slice has the spectral expansion of the walk on coordinates, for every
identifier `y`. -/
@[simp]
theorem spectralExpansion_sliceGraph [NeZero L] (hL : L ≤ P) (y : ZMod P) {D : Type*} [Fintype D]
    (G : RotationMap (Frame P H r × (Fin H → ZMod L)) D) :
    (sliceGraph L hL y G).spectralExpansion = G.spectralExpansion :=
  G.spectralExpansion_reindex _

/-- **Conditional averaging.** Let `G` be any regular multigraph on the slice coordinates, for
example the walk of affine moves, whose spectral expansion is at most `λ`. Then on the retention
slice of every identifier `y`, the walk of length `t` contracts the conditional variance by
`λ ^ (2 t)`, uniformly in `y`; the conditional mean is preserved (`expect_walk_pow`). The bound
`λ` is the hypothesis that the frame-lifted gap must supply. -/
theorem expect_walk_pow_sliceGraph_sub_expect_sq_le [NeZero L] (hL : L ≤ P) {D : Type*}
    [Fintype D] [Nonempty D] (G : RotationMap (Frame P H r × (Fin H → ZMod L)) D) {lam : ℝ}
    (hG : G.spectralExpansion ≤ lam) (y : ZMod P) (f : RetentionSlice P H r L y → ℝ) (t : ℕ) :
    𝔼 A, (((sliceGraph L hL y G).walk ^ t) f A - 𝔼 B, f B) ^ 2 ≤
      lam ^ (2 * t) * 𝔼 A, (f A - 𝔼 B, f B) ^ 2 := by
  refine ((sliceGraph L hL y G).expect_walk_pow_sub_expect_sq_le t f).trans ?_
  rw [spectralExpansion_sliceGraph]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ G.spectralExpansion_nonneg hG _)
    (expect_nonneg fun _ _ ↦ sq_nonneg _)

/-! ### Validated variants -/

variable (L) in
/-- A **validated-walk variant**: the permutation `(a₀, F) ↦ (g a₀ + c + L z, g F)` of all
channels, modulo `P`. It does not depend on any identifier. -/
@[expose] def variantMove (g : SpecialLinearGroup (Fin H) ℤ) (c z : Fin H → ℤ) :
    Equiv.Perm (FrameChannel P H r) :=
  (affineSL (ZMod P) g fun i ↦ ((c i + L * z i : ℤ) : ZMod P)).prodCongr (Frame.mapSL g)

omit [NeZero P] in
/-- A variant acts on the value at every identifier by the same affine map. -/
theorem eval_variantMove (g : SpecialLinearGroup (Fin H) ℤ) (c z : Fin H → ℤ)
    (A : FrameChannel P H r) (y : ZMod P) :
    (variantMove L g c z A).eval y =
      (SpecialLinearGroup.map (Int.castRingHom (ZMod P)) g : Matrix _ _ (ZMod P)) *ᵥ A.eval y +
        fun i ↦ ((c i + L * z i : ℤ) : ZMod P) := by
  simp only [variantMove, FrameChannel.eval, Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd,
    affineSL_apply, Frame.mapSL_apply, mulVec_add, mulVec_sum, mulVec_smul]
  abel

/-- The integer vector `g w + c`, computed from the representatives `w` of a value. -/
@[expose] def wrapTarget (g : SpecialLinearGroup (Fin H) ℤ) (c : Fin H → ℤ) (w : Fin H → ZMod P) :
    Fin H → ℤ :=
  (g : Matrix (Fin H) (Fin H) ℤ) *ᵥ (fun j ↦ ((w j).val : ℤ)) + c

variable (L) in
/-- The **wrap test** for a variant: `g w + c + L z`, computed over the integers from the
representatives `w` of the value, lies in `{0, …, L - 1} ^ H`. -/
@[expose] def IsValidWrap (g : SpecialLinearGroup (Fin H) ℤ) (c z : Fin H → ℤ)
    (w : Fin H → ZMod P) : Prop :=
  ∀ i, 0 ≤ wrapTarget g c w i + L * z i ∧ wrapTarget g c w i + L * z i < L

instance (g : SpecialLinearGroup (Fin H) ℤ) (c z : Fin H → ℤ) (w : Fin H → ZMod P) :
    Decidable (IsValidWrap L g c z w) :=
  inferInstanceAs (Decidable (∀ _, _))

variable (L) in
/-- The valid wrap `z = -⌊(g w + c) / L⌋`. -/
@[expose] def wrap (g : SpecialLinearGroup (Fin H) ℤ) (c : Fin H → ℤ) (w : Fin H → ZMod P) :
    Fin H → ℤ :=
  fun i ↦ -(wrapTarget g c w i / L)

omit [NeZero P] in
/-- **Uniqueness of the valid wrap**: exactly one wrap vector passes the test. -/
theorem isValidWrap_iff [NeZero L] {g : SpecialLinearGroup (Fin H) ℤ} {c z : Fin H → ℤ}
    {w : Fin H → ZMod P} : IsValidWrap L g c z w ↔ z = wrap L g c w := by
  have hL : (0 : ℤ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  refine ⟨fun h ↦ funext fun i ↦ ?_, fun h i ↦ ?_⟩
  · have := (Int.ediv_emod_unique hL).2
      ⟨show wrapTarget g c w i + L * z i + L * -z i = wrapTarget g c w i by ring, h i⟩
    simp only [wrap, this.1, neg_neg]
  · have hmod := Int.emod_def (wrapTarget g c w i) L
    simp only [h, wrap, mul_neg, ← sub_eq_add_neg, ← hmod]
    exact ⟨Int.emod_nonneg _ hL.ne', Int.emod_lt_of_pos _ hL⟩

/-- **The wrap box**: for a value in the retention box, the valid wrap satisfies
`|z i| ≤ ∑ j, |g i j| + |c i|`, a bound independent of `L` and `P`. So finitely many variants per
move suffice for every side length. -/
theorem abs_wrap_le [NeZero L] (g : SpecialLinearGroup (Fin H) ℤ) (c : Fin H → ℤ)
    {w : Fin H → ZMod P} (hw : w ∈ retentionBox P H L) (i : Fin H) :
    |wrap L g c w i| ≤ ∑ j, |g i j| + |c i| := by
  have hL : (0 : ℤ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  simp only [wrap, abs_neg]
  have hterm (j : Fin H) : |g i j * ((w j).val : ℤ)| ≤ |g i j| * L := by
    rw [abs_mul, abs_of_nonneg (Int.natCast_nonneg _)]
    have : ((w j).val : ℤ) ≤ L := by exact_mod_cast (mem_retentionBox.1 hw j).le
    exact mul_le_mul_of_nonneg_left this (abs_nonneg _)
  have hx : |wrapTarget g c w i| ≤ L * (∑ j, |g i j| + |c i|) := by
    have h1 : |∑ j, g i j * ((w j).val : ℤ)| ≤ ∑ j, |g i j| * L :=
      (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun j _ ↦ hterm j)
    have h2 : |c i| ≤ |c i| * L := le_mul_of_one_le_right (abs_nonneg _) hL
    calc |wrapTarget g c w i| = |∑ j, g i j * ((w j).val : ℤ) + c i| := rfl
      _ ≤ |∑ j, g i j * ((w j).val : ℤ)| + |c i| := abs_add_le _ _
      _ ≤ ∑ j, |g i j| * L + |c i| * L := add_le_add h1 h2
      _ = L * (∑ j, |g i j| + |c i|) := by rw [← sum_mul]; ring
  generalize wrapTarget g c w i = x at hx ⊢
  generalize ∑ j, |g i j| + |c i| = S at hx ⊢
  have hlo := Int.mul_ediv_self_le (x := x) hL.ne'
  have hhi := Int.lt_ediv_add_one_mul_self x hL
  rw [abs_le] at hx ⊢
  constructor
  · by_contra h
    have : x / L + 1 ≤ -S := by omega
    nlinarith
  · by_contra h
    have : S + 1 ≤ x / L := by omega
    nlinarith

/-- **The valid variant is the conditional move.** On a channel retaining `y`, the variant with the
valid wrap maps it to the channel with coordinates `coordMove g c (F, w)`. In particular it
retains `y` again. -/
theorem variantMove_wrap_eq [NeZero L] (hL : L ≤ P) {y : ZMod P}
    (g : SpecialLinearGroup (Fin H) ℤ) (c : Fin H → ℤ) (A : RetentionSlice P H r L y) :
    variantMove L g c (wrap L g c (A.1.eval y)) A.1 =
      ((sliceEquiv hL y).symm (coordMove g c (sliceEquiv hL y A))).1 := by
  refine (FrameChannel.evalEquiv y).injective (Prod.ext (funext fun i ↦ ?_) ?_)
  · have hrep : A.1.eval y = fun j ↦ (((A.1.eval y j).val : ℤ) : ZMod P) := by
      ext j
      simp
    have hP : ((SpecialLinearGroup.map (Int.castRingHom (ZMod P)) g : Matrix _ _ (ZMod P)) *ᵥ
        A.1.eval y) i = ((((g : Matrix _ _ ℤ) *ᵥ fun j ↦ ((A.1.eval y j).val : ℤ)) i : ℤ) :
          ZMod P) := by
      conv_lhs => rw [hrep]
      rw [SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]
      exact (RingHom.map_mulVec (Int.castRingHom (ZMod P)) _ _ i).symm
    have hLmod : (((SpecialLinearGroup.map (Int.castRingHom (ZMod L)) g : Matrix _ _ (ZMod L)) *ᵥ
        fun j ↦ (((A.1.eval y j).val : ℕ) : ZMod L)) i + (c i : ZMod L)) =
          ((wrapTarget g c (A.1.eval y) i : ℤ) : ZMod L) := by
      have hcast : (fun j ↦ (((A.1.eval y j).val : ℕ) : ZMod L)) =
          Int.castRingHom (ZMod L) ∘ fun j ↦ ((A.1.eval y j).val : ℤ) := by
        ext j
        simp
      rw [wrapTarget, Pi.add_apply, Int.cast_add, SpecialLinearGroup.map_apply_coe,
        RingHom.mapMatrix_apply, hcast]
      exact congrArg (· + (c i : ZMod L))
        (RingHom.map_mulVec (Int.castRingHom (ZMod L)) _ _ i).symm
    have hval : ((((wrapTarget g c (A.1.eval y) i : ℤ) : ZMod L).val : ℕ) : ZMod P) =
        ((wrapTarget g c (A.1.eval y) i % L : ℤ) : ZMod P) := by
      rw [← ZMod.val_intCast, Int.cast_natCast]
    simp only [FrameChannel.evalEquiv_apply, eval_variantMove, Pi.add_apply, hP,
      eval_sliceEquiv_symm, sliceEquiv_apply, coordMove, Equiv.prodCongr_apply, Prod.map_snd,
      affineSL_apply, hLmod, hval]
    rw [Int.emod_def]
    simp only [wrap, wrapTarget, Pi.add_apply]
    push_cast
    ring
  · rfl

/-- **Exactly one variant survives** (Lemma 6.3, items 3 and 4, for one step). For a channel
retaining `y` and any candidate set `Z` of wraps containing the valid one, the sum over `Z` of
the variants passing the wrap test is the value at the conditional move. -/
theorem sum_ite_isValidWrap [NeZero L] (hL : L ≤ P) {y : ZMod P} {M : Type*} [AddCommMonoid M]
    (g : SpecialLinearGroup (Fin H) ℤ) (c : Fin H → ℤ) (A : RetentionSlice P H r L y)
    {Z : Finset (Fin H → ℤ)} (hZ : wrap L g c (A.1.eval y) ∈ Z) (f : FrameChannel P H r → M) :
    ∑ z ∈ Z, (if IsValidWrap L g c z (A.1.eval y) then f (variantMove L g c z A.1) else 0) =
      f ((sliceEquiv hL y).symm (coordMove g c (sliceEquiv hL y A))).1 := by
  simp only [isValidWrap_iff, sum_ite_eq', hZ, ite_true]
  rw [variantMove_wrap_eq hL]

/-- The forward move of a generator `(g, c)` for `b = false`, and its inverse for `b = true`. -/
@[expose] def signedMove {H : ℕ} (m : SpecialLinearGroup (Fin H) ℤ × (Fin H → ℤ)) (b : Bool) :
    SpecialLinearGroup (Fin H) ℤ × (Fin H → ℤ) :=
  bif b then (m.1⁻¹, -(((m.1⁻¹ : SpecialLinearGroup (Fin H) ℤ) : Matrix (Fin H) (Fin H) ℤ) *ᵥ m.2))
  else m

/-- **The conditional walk as an average of valid variants.** For a family `σ` of affine
generators, the walk of `ofPerms` of their moves, transported to the slice of `y`, applied to a
function `f` of the channel, is the average over generators and directions of the sums of the
valid variants. -/
theorem walk_sliceGraph_ofPerms_eq [NeZero L] (hL : L ≤ P) {y : ZMod P} {K : Type*} [Fintype K]
    (σ : K → SpecialLinearGroup (Fin H) ℤ × (Fin H → ℤ)) {Z : Finset (Fin H → ℤ)}
    (hZ : ∀ k b, ∀ w ∈ retentionBox P H L,
      wrap L (signedMove (σ k) b).1 (signedMove (σ k) b).2 w ∈ Z)
    (f : FrameChannel P H r → ℝ) (A : RetentionSlice P H r L y) :
    (sliceGraph L hL y (RotationMap.ofPerms fun k ↦ coordMove (σ k).1 (σ k).2)).walk
        (fun B ↦ f B.1) A =
      𝔼 kb : K × Bool, ∑ z ∈ Z,
        (if IsValidWrap L (signedMove (σ kb.1) kb.2).1 (signedMove (σ kb.1) kb.2).2 z (A.1.eval y)
          then f (variantMove L (signedMove (σ kb.1) kb.2).1 (signedMove (σ kb.1) kb.2).2 z A.1)
          else 0) := by
  rw [RotationMap.walk_apply]
  refine expect_congr rfl fun ⟨k, b⟩ _ ↦ ?_
  rw [sum_ite_isValidWrap hL _ _ A (hZ k b _ A.2)]
  cases b
  · rfl
  · simp only [sliceGraph, RotationMap.neighbor_reindex, RotationMap.neighbor_ofPerms_true,
      Equiv.symm_symm, signedMove, Bool.cond_true, coordMove_symm]

end Cslib.Probability
