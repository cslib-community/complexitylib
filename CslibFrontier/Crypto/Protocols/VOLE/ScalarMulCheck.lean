/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.VOLE.MulCheck
import CslibFrontier.Crypto.Protocols.VOLE.BatchMulCheck
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.PolynomialAgreement
import Mathlib.Algebra.Polynomial.OfFn

/-!
# Scalar-challenge QuickSilver multiplication checks

For `t` multiplication claims, the original QuickSilver arithmetic samples one public scalar
`chi` after the wire values and masks are fixed and weights gate `i : Fin t` by
`chi ^ (i.val + 1)`. The first exponent is one, matching the source convention
`[t] = {1, ..., t}`. The prover's pair is kept in source order: constant coefficient first and
linear coefficient second. The verifier checks `W = U + V * delta`.

QuickSilver types wire values over a base field `F_p` and MAC masks, tags, and the global key over
an extension field `F_{p^r}`. This API puts `x`, `y`, `z`, every mask and tag, and `delta` in one
field `F`. It therefore formalizes the source equation after embedding the wire values into the
extension field; it does not formalize that embedding, its image, or subfield-membership conditions.

The library's existing batched multiplication check instead samples one independent field element
per gate and stores its reply in linear-then-constant order. This module is the convention-preserving
bridge between those APIs. A single valid VOLE coordinate also supplies the source mask relation
`Bstar = A0star + A1star * delta`: its `v` component masks the constant coefficient, its `u`
component masks the linear coefficient, and its `w` component masks the verifier value.

For a false batch, scalar cancellation occurs with probability at most `t / |F|`. Conditional on
noncancellation, an arbitrary reply chosen after `chi` passes for at most two values of the
independent hidden key. The sequential experiment therefore has error at most `(t + 2) / |F|`.

This is the multiplication-gate arithmetic and check from [YangSarkarWengWang2021], Section 3.1,
printed pp. 6--7, and Section 4.2/Figure 5, printed pp. 12--13. The soundness argument immediately
after Figure 5, printed p. 14, gives the `2 / p^r` hidden-key term, `t / p^r` scalar-cancellation
term, and `(t + 2) / p^r` union bound. The explanatory check in [BaumEtAl2023FAEST], Section 2.3.2,
printed pp. 12--13, uses the same scalar powers. The concrete FAEST v2 and v3 verifiers instead use
universal hashing [BaumEtAl2025FAEST]; v3 additionally uses degree-seven constraints and CRT masks
[BaumEtAl2026FAEST]. This module does not formalize those hashes or masks.

## Main definitions

* `quickSilverWeight`: the exact one-based scalar challenge weight.
* `quickSilverMulCheckReply`: the unmasked source-order pair `(U, V)`.
* `quickSilverMaskedReply`: the source-order pair with one VOLE mask.
* `quickSilverMulCheckValue`, `quickSilverMaskedValue`: the corresponding verifier values.

## Main results

* `quickSilverMulCheck_sub_eq`: the scalar-weighted degree-two identity.
* `quickSilverMulCheck_complete`, `quickSilverMaskedReply_correct`: unmasked and masked
  completeness.
* `toOuterMeasure_quickSilverWeight_sum_eq_zero_le`: the `t / |F|` scalar-cancellation bound.
* `toOuterMeasure_quickSilverMulCheck_key_le`: the conditional `2 / |F|` hidden-key bound.
* `toOuterMeasure_quickSilverMulCheck_le`: the sequential `(t + 2) / |F|` bound.
* `toOuterMeasure_quickSilverMulCheck_bind_le`: the same bound for randomized sender state.

## References

* [K. Yang, P. Sarkar, C. Weng, X. Wang, *QuickSilver: Efficient and Affordable Zero-Knowledge
  Proofs for Circuits and Polynomials over Any Field*][YangSarkarWengWang2021]
* [C. Baum et al., *FAEST: Algorithm Specifications*, version 1.0][BaumEtAl2023FAEST]
* [C. Baum et al., *FAEST v2: Algorithm Specifications*, version 2.0][BaumEtAl2025FAEST]
* [C. Baum et al., *FAEST v3: Algorithm Specifications*, version 3.0][BaumEtAl2026FAEST]
-/

public section

namespace Cslib.Crypto.Protocols.VOLE

open Probability
open scoped BigOperators ENNReal

variable {F : Type} {t : ℕ}

/-- The scalar challenge weight of gate `i`, whose source index is `i.val + 1`. -/
@[expose]
def quickSilverWeight [Monoid F] (chi : F) (i : Fin t) : F :=
  chi ^ (i.val + 1)

/-- The verifier's scalar-weighted multiplication-check value. -/
@[expose]
def quickSilverMulCheckValue [CommRing F] (x y z v_x v_y v_z : Fin t → F)
    (chi delta : F) : F :=
  ∑ i, quickSilverWeight chi i *
    ((x i * delta + v_x i) * (y i * delta + v_y i) -
      (z i * delta + v_z i) * delta)

/-- The honest unmasked reply in QuickSilver source order `(constant, linear)`. -/
@[expose]
def quickSilverMulCheckReply [CommRing F] (x y v_x v_y v_z : Fin t → F)
    (chi : F) : F × F :=
  (∑ i, quickSilverWeight chi i * voleMulConstTerm (v_x i) (v_y i),
    ∑ i, quickSilverWeight chi i *
      voleMulCrossTerm (x i) (v_x i) (y i) (v_y i) (v_z i))

/-- The source-order reply masked by `A0star` and `A1star`. A valid VOLE coordinate supplies
`A0star = v 0`, `A1star = u 0`, and `Bstar = w 0`. -/
@[expose]
def quickSilverMaskedReply [CommRing F] (x y v_x v_y v_z : Fin t → F) (chi : F)
    (maskLinear maskConstant : F) : F × F :=
  let reply := quickSilverMulCheckReply x y v_x v_y v_z chi
  (reply.1 + maskConstant, reply.2 + maskLinear)

/-- The verifier value masked by the receiver's tag `Bstar`. -/
@[expose]
def quickSilverMaskedValue [CommRing F] (x y z v_x v_y v_z : Fin t → F)
    (chi delta maskTag : F) : F :=
  quickSilverMulCheckValue x y z v_x v_y v_z chi delta + maskTag

/-- The scalar-weighted check has leading coefficient equal to the scalar-weighted residual.
The remaining coefficients are exactly the source-order reply, reversed when written as a
polynomial in `delta`. -/
theorem quickSilverMulCheck_sub_eq [CommRing F] (x y z v_x v_y v_z : Fin t → F)
    (chi delta : F) :
    quickSilverMulCheckValue x y z v_x v_y v_z chi delta =
      (∑ i, quickSilverWeight chi i * (x i * y i - z i)) * delta ^ 2 +
        (quickSilverMulCheckReply x y v_x v_y v_z chi).2 * delta +
        (quickSilverMulCheckReply x y v_x v_y v_z chi).1 := by
  simpa only [quickSilverMulCheckValue, quickSilverMulCheckReply] using
    voleMulCheck_sum_sub_eq (fun i => quickSilverWeight chi i) x y z v_x v_y v_z delta

/-- Honest multiplication claims satisfy the unmasked source equation `W = U + V * delta`. -/
theorem quickSilverMulCheck_complete [CommRing F] (x y z v_x v_y v_z : Fin t → F)
    (chi delta : F) (htrue : ∀ i, x i * y i = z i) :
    quickSilverMulCheckValue x y z v_x v_y v_z chi delta =
      (quickSilverMulCheckReply x y v_x v_y v_z chi).1 +
        (quickSilverMulCheckReply x y v_x v_y v_z chi).2 * delta := by
  rw [quickSilverMulCheck_sub_eq]
  simp only [htrue, sub_self, mul_zero, Finset.sum_const_zero, zero_mul, zero_add]
  ring

/-- A valid fresh VOLE coordinate preserves the masked source equation. The sender-side
components `u 0` and `v 0` enter the reply, while the receiver-side component `w 0` enters the
verifier value. -/
theorem quickSilverMaskedReply_correct [CommRing F] (x y z v_x v_y v_z : Fin t → F)
    (chi : F) (mask : VOLECorrelation F 1) (hmask : mask.Valid)
    (htrue : ∀ i, x i * y i = z i) :
    quickSilverMaskedValue x y z v_x v_y v_z chi mask.delta (mask.w 0) =
      (quickSilverMaskedReply x y v_x v_y v_z chi (mask.u 0) (mask.v 0)).1 +
        (quickSilverMaskedReply x y v_x v_y v_z chi (mask.u 0) (mask.v 0)).2 *
          mask.delta := by
  have hbase := quickSilverMulCheck_complete x y z v_x v_y v_z chi mask.delta htrue
  simp only [quickSilverMaskedValue, quickSilverMaskedReply]
  rw [hbase, hmask 0]
  ring

section Soundness

variable [Field F] [Fintype F] [DecidableEq F]

private def quickSilverResidualPolynomial (residual : Fin t → F) : F[X] :=
  Polynomial.ofFn (t + 1) (Fin.cons 0 residual)

private theorem quickSilverResidualPolynomial_eval (residual : Fin t → F) (chi : F) :
    (quickSilverResidualPolynomial residual).eval chi =
      ∑ i, quickSilverWeight chi i * residual i := by
  rw [quickSilverResidualPolynomial, Polynomial.ofFn_eq_sum_monomial]
  change Polynomial.evalRingHom chi
    (∑ i : Fin (t + 1), Polynomial.monomial i (Fin.cons 0 residual i)) = _
  rw [map_sum, Fin.sum_univ_succ]
  simp [quickSilverWeight, Polynomial.eval_monomial, mul_comm]

private theorem quickSilverResidualPolynomial_ne_zero (residual : Fin t → F)
    (hne : ∃ i, residual i ≠ 0) : quickSilverResidualPolynomial residual ≠ 0 := by
  intro hp
  have hv : Fin.cons 0 residual = 0 :=
    Polynomial.injective_ofFn (t + 1) <| by
      rw [quickSilverResidualPolynomial] at hp
      simpa only [Polynomial.ofFn_zero] using hp
  obtain ⟨i, hi⟩ := hne
  have hvi := congrFun hv i.succ
  simp only [Fin.cons_succ, Pi.zero_apply] at hvi
  exact hi hvi

private theorem quickSilverResidualPolynomial_natDegree_le (residual : Fin t → F) :
    (quickSilverResidualPolynomial residual).natDegree ≤ t := by
  rw [quickSilverResidualPolynomial]
  exact Nat.le_of_lt_succ (Polynomial.ofFn_natDegree_lt (by omega) (Fin.cons 0 residual))

/-- If at least one fixed residual is nonzero, the scalar-power weighted sum vanishes for a
uniform challenge with probability at most `t / |F|`. The residuals are fixed before `chi` is
sampled. The bound includes the unavoidable cancellation at `chi = 0` for every nonempty batch. -/
theorem toOuterMeasure_quickSilverWeight_sum_eq_zero_le (residual : Fin t → F)
    (hne : ∃ i, residual i ≠ 0) :
    (PMF.uniformOfFintype F).toOuterMeasure
      {chi | ∑ i, quickSilverWeight chi i * residual i = 0} ≤
      (t : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) := by
  refine PMF.toOuterMeasure_uniformOfFintype_le_of_eval_eq
    (quickSilverResidualPolynomial_ne_zero residual hne)
    (quickSilverResidualPolynomial_natDegree_le residual) (by simp) ?_
  intro chi hchi
  rw [quickSilverResidualPolynomial_eval]
  simpa only [Polynomial.eval_zero, Set.mem_setOf_eq] using hchi

/-- Conditional on a nonzero scalar-weighted residual, an arbitrary source-order affine reply
passes the multiplication check for an independent uniform hidden key with probability at most
`2 / |F|`. -/
theorem toOuterMeasure_quickSilverMulCheck_key_le (x y z v_x v_y v_z : Fin t → F)
    (chi : F) (reply : F × F)
    (hne : ∑ i, quickSilverWeight chi i * (x i * y i - z i) ≠ 0) :
    (PMF.uniformOfFintype F).toOuterMeasure
      {delta | quickSilverMulCheckValue x y z v_x v_y v_z chi delta =
        reply.1 + reply.2 * delta} ≤
      2 / (Fintype.card F : ℝ≥0∞) := by
  simpa only [quickSilverMulCheckValue, add_comm] using
    toOuterMeasure_voleMulCheck_sum_le (fun i => quickSilverWeight chi i)
      x y z v_x v_y v_z reply.2 reply.1 hne

private theorem quickSilver_reply_key_le (x y z v_x v_y v_z : Fin t → F) (chi : F)
    (reply : PMF (F × F))
    (hne : ∑ i, quickSilverWeight chi i * (x i * y i - z i) ≠ 0) :
    (do
      let uv ← reply
      let delta ← PMF.uniformOfFintype F
      return decide (quickSilverMulCheckValue x y z v_x v_y v_z chi delta =
        uv.1 + uv.2 * delta)).toOuterMeasure {true} ≤
      2 / (Fintype.card F : ℝ≥0∞) := by
  simp only [PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure]
  rw [PMF.toOuterMeasure_bind_apply]
  refine PMF.tsum_mul_le_of_forall_le reply fun uv => ?_
  change ((PMF.uniformOfFintype F).map (fun delta => decide _)).toOuterMeasure {true} ≤ _
  rw [PMF.toOuterMeasure_map_apply]
  refine (MeasureTheory.measure_mono ?_).trans
    (toOuterMeasure_quickSilverMulCheck_key_le x y z v_x v_y v_z chi uv hne)
  intro delta hdelta
  exact of_decide_eq_true hdelta

/-- A false fixed batch, followed by a uniform scalar challenge, an arbitrary randomized reply
depending on that challenge, and an independent uniform hidden key, accepts with probability at
most `(t + 2) / |F|`. The two summands are the scalar-cancellation and hidden-key failures. -/
theorem toOuterMeasure_quickSilverMulCheck_le (x y z v_x v_y v_z : Fin t → F)
    (reply : F → PMF (F × F)) (hfalse : ∃ i, x i * y i ≠ z i) :
    (do
      let chi ← PMF.uniformOfFintype F
      let uv ← reply chi
      let delta ← PMF.uniformOfFintype F
      return decide (quickSilverMulCheckValue x y z v_x v_y v_z chi delta =
        uv.1 + uv.2 * delta)).toOuterMeasure {true} ≤
      ((t + 2 : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) := by
  let cancel : Set F :=
    {chi | ∑ i, quickSilverWeight chi i * (x i * y i - z i) = 0}
  let kernel (chi : F) : PMF Bool := do
    let uv ← reply chi
    let delta ← PMF.uniformOfFintype F
    return decide (quickSilverMulCheckValue x y z v_x v_y v_z chi delta =
      uv.1 + uv.2 * delta)
  have hresidual : ∃ i, x i * y i - z i ≠ 0 := by
    obtain ⟨i, hi⟩ := hfalse
    exact ⟨i, sub_ne_zero.mpr hi⟩
  have hcancel : (PMF.uniformOfFintype F).toOuterMeasure cancel ≤
      (t : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) :=
    toOuterMeasure_quickSilverWeight_sum_eq_zero_le
      (fun i => x i * y i - z i) hresidual
  change ((PMF.uniformOfFintype F).bind kernel).toOuterMeasure {true} ≤ _
  rw [PMF.toOuterMeasure_bind_apply]
  calc
    ∑' chi, PMF.uniformOfFintype F chi * (kernel chi).toOuterMeasure {true}
      ≤ ∑' chi, PMF.uniformOfFintype F chi *
          (if chi ∈ cancel then 1 else 2 / (Fintype.card F : ℝ≥0∞)) := by
        refine tsum_le_tsum fun chi => mul_le_mul_of_nonneg_left ?_ zero_le
        split_ifs with hchi
        · exact PMF.toOuterMeasure_le_one _ _
        · exact quickSilver_reply_key_le x y z v_x v_y v_z chi (reply chi) hchi
    _ = (PMF.uniformOfFintype F).toOuterMeasure cancel +
        (PMF.uniformOfFintype F).toOuterMeasure cancelᶜ *
          (2 / (Fintype.card F : ℝ≥0∞)) := by
        simp only [PMF.toOuterMeasure_apply, ← ENNReal.tsum_mul_right, ← tsum_add]
        apply tsum_congr
        intro chi
        by_cases hchi : chi ∈ cancel <;> simp [hchi]
    _ ≤ (t : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) +
        1 * (2 / (Fintype.card F : ℝ≥0∞)) :=
      add_le_add hcancel <| mul_le_mul_right'
        (PMF.toOuterMeasure_le_one (PMF.uniformOfFintype F) cancelᶜ) _
    _ = _ := by
      rw [one_mul, div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, Nat.cast_add,
        Nat.cast_ofNat]
      ring

/-- An arbitrary randomized sender fixes all wires and masks before the scalar challenge. Its
reply may depend on its state and on `chi`, but not on the subsequently sampled hidden key. The
bad event includes a false multiplication claim, so it is empty for `t = 0`. -/
theorem toOuterMeasure_quickSilverMulCheck_bind_le {S : Type} (sender : PMF S)
    (x y z v_x v_y v_z : S → Fin t → F) (reply : S → F → PMF (F × F)) :
    (do
      let s ← sender
      let chi ← PMF.uniformOfFintype F
      let uv ← reply s chi
      let delta ← PMF.uniformOfFintype F
      return decide ((∃ i, x s i * y s i ≠ z s i) ∧
        quickSilverMulCheckValue (x s) (y s) (z s) (v_x s) (v_y s) (v_z s) chi delta =
          uv.1 + uv.2 * delta)).toOuterMeasure {true} ≤
      ((t + 2 : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) := by
  simp only [PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure]
  rw [PMF.toOuterMeasure_bind_apply]
  refine PMF.tsum_mul_le_of_forall_le sender fun s => ?_
  by_cases hfalse : ∃ i, x s i * y s i ≠ z s i
  · simpa only [PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, hfalse, true_and] using
      toOuterMeasure_quickSilverMulCheck_le (x s) (y s) (z s) (v_x s) (v_y s) (v_z s)
        (reply s) hfalse
  · simp [hfalse]

end Soundness

end Cslib.Crypto.Protocols.VOLE
