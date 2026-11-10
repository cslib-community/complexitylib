/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.DepthFive.PathCount
public import CslibFrontier.Computability.Circuit.Arithmetic.DepthFive.PathMatrix

/-!
# Four paths in the second trace moment

Let `F` be the matrix `pathMatrix` of the operator of `IMM_{n,n}` in the normalized monomial
bases. The trace of `(Fᵀ * F) * (Fᵀ * F)` is a sum over an exponent vector `M` and four paths
`P, Q, R, S` such that `P` and `Q` map `M` and a second exponent vector `M'` to a common image,
and so do `R` and `S`. In every layer the edges `p, q, r, s` of the four paths then satisfy
`p = q` and `r = s` (type `𝒩`), or `p = r` and `q = s` with `p ≠ q` (type `𝒟`), and the product
of the four coefficients is the product over the layers of

* `M p * M r` in a differentiated layer of type `𝒩`, and `M p * (M q + 1)` of type `𝒟`;
* `(M p + 1) * (M r + 1)` in a multiplied layer of type `𝒩`, and `(M p + 1) * M q` of type `𝒟`

[OpenAI, §4][OpenAI2026DepthFive]. `Quad.local` is this local polynomial and
`second_trace_le_sum_local` bounds the second trace by the sum of the products of the local
polynomials over the four paths that have a type.

## Main definitions

* `Quad.type`: the type word of four paths.
* `Quad.mate`: the second variable of the local polynomial of a layer.
* `Quad.local`: the local polynomial of a layer.

## Main results

* `second_trace_le_sum_local`: the four-path bound for the second trace.

## References

* [OpenAI, *Homogeneous depth-five lower bounds for iterated matrix
  multiplication*][OpenAI2026DepthFive], §4 (unrefereed preprint)
-/

@[expose] public section

open Finsupp
open scoped Matrix

namespace Cslib.Circuits.DepthFive

variable {p : Params} [NeZero p.n]

namespace Quad

variable (W : Quad p.n)

/-- The type word of four paths: a layer has type `𝒟` (`true`) if the edges of `P` and `Q`
differ, and type `𝒩` (`false`) otherwise. -/
def type (t : Fin p.n) : Bool := decide (W.1.1.edge t ≠ W.1.2.edge t)

/-- The second variable of the local polynomial of a layer: the edge of `R` in a layer of type
`𝒩` and the edge of `Q` in a layer of type `𝒟`. The first variable is the edge of `P`. -/
def mate (t : Fin p.n) : Fin p.n × Fin p.n × Fin p.n :=
  if W.1.1.edge t = W.1.2.edge t then W.2.1.edge t else W.1.2.edge t

theorem mate_fst (t : Fin p.n) : (W.mate t).1 = t := by
  rw [mate]
  split_ifs <;> rfl

variable (p) in
/-- The shift of the second factor of the local polynomial. -/
def shift (t : Fin p.n) : ℕ := if (W.1.1.edge t = W.1.2.edge t ↔ p.isV t) then 0 else 1

variable (p) in
/-- The local polynomial of a layer: the square root of the product of the four path
coefficients of the layer. -/
def «local» (M : Fin p.n × Fin p.n × Fin p.n →₀ ℕ) (t : Fin p.n) : ℕ :=
  (M (W.1.1.edge t) + if p.isV t then 0 else 1) * (M (W.mate t) + W.shift p t)

end Quad

/-- The four edges in a differentiated layer. -/
private theorem layer_diff {X : Type*} [DecidableEq X] {L : X → Prop} {M M' : X → ℕ}
    {a b c d : X} (ha : L a) (hb : L b) (hd : L d)
    (e₁ : ∀ x, L x → M x + (if b = x then 1 else 0) = M' x + (if a = x then 1 else 0))
    (e₂ : ∀ x, L x → M x + (if d = x then 1 else 0) = M' x + (if c = x then 1 else 0)) :
    (if a = b then c = d else a = c ∧ b = d) ∧
      M a * M' b * (M c * M' d) = (M a * if a = b then M c else M b + 1) ^ 2 := by
  by_cases hab : a = b
  · subst hab
    have hM (x : X) (hx : L x) : M' x = M x := by have := e₁ x hx; omega
    have hcd : c = d := by
      by_contra h
      have := e₂ d hd
      rw [hM d hd, ite_eq_left rfl, ite_eq_right h] at this
      omega
    subst hcd
    rw [hM a ha, hM c hd, ite_eq_left rfl, ite_eq_left rfl]
    exact ⟨rfl, by ring⟩
  · have h₁ := e₁ b hb
    have h₂ := e₁ a ha
    rw [ite_eq_left rfl, ite_eq_right hab] at h₁
    rw [ite_eq_right (Ne.symm hab), ite_eq_left rfl] at h₂
    have hbd : b = d := by
      by_contra h
      have := e₂ b hb
      rw [ite_eq_right (Ne.symm h)] at this
      split_ifs at this <;> omega
    subst hbd
    have hac : a = c := by
      by_contra h
      have := e₂ a ha
      rw [ite_eq_right (Ne.symm hab), ite_eq_right (Ne.symm h)] at this
      omega
    subst hac
    rw [ite_eq_right hab, ite_eq_right hab, show M' b = M b + 1 by omega]
    exact ⟨⟨rfl, rfl⟩, by ring⟩

/-- The four edges in a multiplied layer. -/
private theorem layer_mul {X : Type*} [DecidableEq X] {L : X → Prop} {M M' : X → ℕ}
    {a b c d : X} (ha : L a) (hb : L b) (hc : L c)
    (e₁ : ∀ x, L x → M x + (if a = x then 1 else 0) = M' x + (if b = x then 1 else 0))
    (e₂ : ∀ x, L x → M x + (if c = x then 1 else 0) = M' x + (if d = x then 1 else 0)) :
    (if a = b then c = d else a = c ∧ b = d) ∧
      (M a + 1) * (M' b + 1) * ((M c + 1) * (M' d + 1)) =
        ((M a + 1) * if a = b then M c + 1 else M b) ^ 2 := by
  by_cases hab : a = b
  · subst hab
    have hM (x : X) (hx : L x) : M' x = M x := by have := e₁ x hx; omega
    have hcd : c = d := by
      by_contra h
      have := e₂ c hc
      rw [hM c hc, ite_eq_left rfl, ite_eq_right (Ne.symm h)] at this
      omega
    subst hcd
    rw [hM a ha, hM c hc, ite_eq_left rfl, ite_eq_left rfl]
    exact ⟨rfl, by ring⟩
  · have h₁ := e₁ a ha
    have h₂ := e₁ b hb
    rw [ite_eq_left rfl, ite_eq_right (Ne.symm hab)] at h₁
    rw [ite_eq_right hab, ite_eq_left rfl] at h₂
    have hac : a = c := by
      by_contra h
      have := e₂ a ha
      rw [ite_eq_right (Ne.symm h)] at this
      split_ifs at this <;> omega
    subst hac
    have hbd : b = d := by
      by_contra h
      have := e₂ b hb
      rw [ite_eq_right hab, ite_eq_right (Ne.symm h)] at this
      omega
    subst hbd
    rw [ite_eq_right hab, ite_eq_right hab, show M' b + 1 = M b by omega]
    exact ⟨⟨rfl, rfl⟩, by ring⟩

/-- The paths `P` and `Q` map the exponent vectors `M` and `M'` to a common image. -/
private def Link (PQ : Path p.n × Path p.n) (M M' : Fin p.n × Fin p.n × Fin p.n →₀ ℕ) : Prop :=
  M + PQ.1.uPart p + PQ.2.vPart p = M' + PQ.2.uPart p + PQ.1.vPart p

private noncomputable instance (PQ : Path p.n × Path p.n)
    (M M' : Fin p.n × Fin p.n × Fin p.n →₀ ℕ) : Decidable (Link PQ M M') := by
  unfold Link
  infer_instance

private theorem link_apply {PQ : Path p.n × Path p.n} {M M' : Fin p.n × Fin p.n × Fin p.n →₀ ℕ}
    (h : Link PQ M M') (x : Fin p.n × Fin p.n × Fin p.n) :
    M x + ((if ¬ p.isV x.1 ∧ PQ.1.edge x.1 = x then 1 else 0) +
        if p.isV x.1 ∧ PQ.2.edge x.1 = x then 1 else 0) =
      M' x + ((if ¬ p.isV x.1 ∧ PQ.2.edge x.1 = x then 1 else 0) +
        if p.isV x.1 ∧ PQ.1.edge x.1 = x then 1 else 0) := by
  have := DFunLike.congr_fun h x
  simpa [Path.uPart, Path.vPart, Path.part_apply, add_assoc] using this

/-- If `P, Q` and `R, S` both link `M` to `M'`, the four paths have a type and the product of
their four coefficients is the square of the product of the local polynomials. -/
private theorem local_sq (W : Quad p.n) {M M' : Fin p.n × Fin p.n × Fin p.n →₀ ℕ}
    (h₁ : Link W.1 M M') (h₂ : Link W.2 M M') :
    W.HasType W.type ∧ W.1.1.coeff p M * W.1.2.coeff p M' *
      (W.2.1.coeff p M * W.2.2.coeff p M') = (∏ t, W.local p M t) ^ 2 := by
  have key (t : Fin p.n) :
      (if W.1.1.edge t = W.1.2.edge t then W.2.1.edge t = W.2.2.edge t
        else W.1.1.edge t = W.2.1.edge t ∧ W.1.2.edge t = W.2.2.edge t) ∧
      (if p.isV t then M (W.1.1.edge t) else M (W.1.1.edge t) + 1) *
          (if p.isV t then M' (W.1.2.edge t) else M' (W.1.2.edge t) + 1) *
        ((if p.isV t then M (W.2.1.edge t) else M (W.2.1.edge t) + 1) *
          (if p.isV t then M' (W.2.2.edge t) else M' (W.2.2.edge t) + 1)) =
        W.local p M t ^ 2 := by
    have e (PQ : Path p.n × Path p.n) (h : Link PQ M M') (x : Fin p.n × Fin p.n × Fin p.n)
        (hx : x.1 = t) :
        M x + ((if ¬ p.isV t ∧ PQ.1.edge t = x then 1 else 0) +
            if p.isV t ∧ PQ.2.edge t = x then 1 else 0) =
          M' x + ((if ¬ p.isV t ∧ PQ.2.edge t = x then 1 else 0) +
            if p.isV t ∧ PQ.1.edge t = x then 1 else 0) := hx ▸ link_apply h x
    by_cases ht : p.isV t
    · have := layer_diff (L := fun x => x.1 = t) (M := M) (M' := M') (a := W.1.1.edge t)
        (b := W.1.2.edge t) (c := W.2.1.edge t) (d := W.2.2.edge t) rfl rfl rfl
        (fun x hx => by simpa [ht] using e W.1 h₁ x hx)
        (fun x hx => by simpa [ht] using e W.2 h₂ x hx)
      simp only [Quad.local, Quad.mate, Quad.shift, ht, iff_true, ite_true, add_zero]
      refine ⟨this.1, this.2.trans ?_⟩
      split_ifs <;> rfl
    · have := layer_mul (L := fun x => x.1 = t) (M := M) (M' := M') (a := W.1.1.edge t)
        (b := W.1.2.edge t) (c := W.2.1.edge t) (d := W.2.2.edge t) rfl rfl rfl
        (fun x hx => by simpa [ht] using e W.1 h₁ x hx)
        (fun x hx => by simpa [ht] using e W.2 h₂ x hx)
      simp only [Quad.local, Quad.mate, Quad.shift, ht]
      refine ⟨this.1, this.2.trans ?_⟩
      split_ifs <;> simp_all
  refine ⟨fun t => ?_, ?_⟩
  · have := (key t).1
    by_cases h : W.1.1.edge t = W.1.2.edge t
    · simp only [Quad.type, h, ne_eq, not_true_eq_false, decide_false, ite_true] at this ⊢
      exact ⟨trivial, this⟩
    · simpa only [Quad.type, h, ne_eq, not_false_eq_true, decide_true, ite_false, ite_true]
        using this
  · simp only [Path.coeff, ← Finset.prod_mul_distrib, ← Finset.prod_pow]
    exact Finset.prod_congr rfl fun t _ => (key t).2

/-- The entry of `Fᵀ * F` is at most the sum over the pairs of paths that link its indices. -/
private theorem gram_le (M M' : Slice p (p.a, p.b)) :
    ((pathMatrix p)ᵀ * pathMatrix p) M M' ≤ ∑ PQ : Path p.n × Path p.n,
      if Link PQ M.1 M'.1 then √(PQ.1.coeff p M.1) * √(PQ.2.coeff p M'.1) else 0 := by
  classical
  simp only [Matrix.mul_apply, Matrix.transpose_apply, pathMatrix, Matrix.of_apply, pathEntry,
    Finset.sum_mul_sum, ← Finset.sum_product']
  rw [Finset.sum_product_right, Finset.univ_product_univ]
  refine Finset.sum_le_sum fun PQ _ => ?_
  dsimp only
  by_cases h : ∃ N : Slice p (p.a - p.k, p.b + p.m),
      N.1 + PQ.1.vPart p = M.1 + PQ.1.uPart p ∧ N.1 + PQ.2.vPart p = M'.1 + PQ.2.uPart p
  · obtain ⟨N, hN₁, hN₂⟩ := h
    have hl : Link PQ M.1 M'.1 := by
      rw [Link, ← hN₁, ← hN₂]
      abel
    rw [Finset.sum_eq_single N (fun N' _ hN' => ?_) (fun h => absurd (Finset.mem_univ _) h),
      ite_eq_left hN₁, ite_eq_left hN₂, ite_eq_left hl]
    rw [ite_eq_right fun h' => hN' (Subtype.ext (add_right_cancel (h'.trans hN₁.symm))), zero_mul]
  · refine le_trans (le_of_eq (Finset.sum_eq_zero fun N _ => ?_)) (by split_ifs <;> positivity)
    by_cases h₁ : N.1 + PQ.1.vPart p = M.1 + PQ.1.uPart p
    · rw [ite_eq_right fun h₂ => h ⟨N, h₁, h₂⟩, mul_zero]
    · rw [ite_eq_right h₁, zero_mul]

private theorem gram_nonneg (M M' : Slice p (p.a, p.b)) :
    0 ≤ ((pathMatrix p)ᵀ * pathMatrix p) M M' := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, pathMatrix, Matrix.of_apply, pathEntry]
  exact Finset.sum_nonneg fun N _ => mul_nonneg
    (Finset.sum_nonneg fun P _ => by split_ifs <;> positivity)
    (Finset.sum_nonneg fun P _ => by split_ifs <;> positivity)

/-- **The four-path bound.** The trace of `(Fᵀ * F) * (Fᵀ * F)` is at most the sum, over the
exponent vectors `M` of the slice and the four paths that have a type, of the product of the
local polynomials. -/
theorem second_trace_le_sum_local :
    (((pathMatrix p)ᵀ * pathMatrix p) * ((pathMatrix p)ᵀ * pathMatrix p)).trace ≤
      ∑ M : Slice p (p.a, p.b), ∑ W : Quad p.n,
        if W.HasType W.type then ((∏ t, W.local p M.1 t : ℕ) : ℝ) else 0 := by
  classical
  have hsymm (M M' : Slice p (p.a, p.b)) : ((pathMatrix p)ᵀ * pathMatrix p) M' M =
      ((pathMatrix p)ᵀ * pathMatrix p) M M' := by
    simp only [Matrix.mul_apply, Matrix.transpose_apply, mul_comm]
  generalize hG : (pathMatrix p)ᵀ * pathMatrix p = G at hsymm
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  subst hG
  refine Finset.sum_le_sum fun M _ => ?_
  calc ∑ M', ((pathMatrix p)ᵀ * pathMatrix p) M M' * ((pathMatrix p)ᵀ * pathMatrix p) M' M
      ≤ ∑ M' : Slice p (p.a, p.b), ∑ W : Quad p.n,
          (if Link W.1 M.1 M'.1 then √(W.1.1.coeff p M.1) * √(W.1.2.coeff p M'.1) else 0) *
            if Link W.2 M.1 M'.1 then √(W.2.1.coeff p M.1) * √(W.2.2.coeff p M'.1) else 0 := by
        refine Finset.sum_le_sum fun M' _ => ?_
        rw [hsymm M M']
        refine (mul_le_mul (gram_le M M') (gram_le M M') (gram_nonneg M M')
          ((gram_nonneg M M').trans (gram_le M M'))).trans (le_of_eq ?_)
        rw [Finset.sum_mul_sum, ← Finset.sum_product', Finset.univ_product_univ]
    _ ≤ _ := by
        rw [Finset.sum_comm]
        refine Finset.sum_le_sum fun W _ => ?_
        by_cases h : ∃ M' : Slice p (p.a, p.b), Link W.1 M.1 M'.1 ∧ Link W.2 M.1 M'.1
        · obtain ⟨M', h₁, h₂⟩ := h
          obtain ⟨hty, hsq⟩ := local_sq W h₁ h₂
          rw [Finset.sum_eq_single M' (fun N' _ hN' => ?_) (fun h => absurd (Finset.mem_univ _) h),
            ite_eq_left h₁, ite_eq_left h₂, ite_eq_left hty, mul_mul_mul_comm,
            ← Real.sqrt_mul (Nat.cast_nonneg _), ← Real.sqrt_mul (Nat.cast_nonneg _),
            ← Real.sqrt_mul (by positivity)]
          · refine le_of_eq ?_
            rw [← Real.sqrt_sq (Nat.cast_nonneg (∏ t, W.local p M.1 t))]
            congr 1
            rw [mul_mul_mul_comm]
            exact_mod_cast hsq
          · rw [ite_eq_right fun h' => hN' (Subtype.ext (add_right_cancel
              (a := N'.1) (b := W.1.2.uPart p + W.1.1.vPart p) (c := M'.1) (by
                rw [← add_assoc, ← add_assoc]
                exact h'.symm.trans h₁))), zero_mul]
        · refine le_trans (le_of_eq (Finset.sum_eq_zero fun M' _ => ?_))
            (by split_ifs <;> positivity)
          by_cases h₁ : Link W.1 M.1 M'.1
          · rw [ite_eq_right fun h₂ => h ⟨M', h₁, h₂⟩, mul_zero]
          · rw [ite_eq_right h₁, zero_mul]

end Cslib.Circuits.DepthFive
