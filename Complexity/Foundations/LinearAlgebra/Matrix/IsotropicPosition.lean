/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Order.Filter.Basic
public import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Separation.Basic

/-!
# Approximate isotropic position

Let `U : Matrix X (Fin d) ℝ` list `|X| = m` vectors `U x ∈ ℝᵈ` in *general position*: every `d`
of them are linearly independent, i.e. every `d × d` submatrix `U.submatrix e id` with
`e : Fin d ↪ X` is invertible. Forster's isotropic-position lemma [Forster, 2002][Forster2002],
in the form [Alon, Moran and Yehudayoff, Lemma 26][AlonMoranYehudayoff2016], says that some
invertible `B` puts them in isotropic position, `∑ₓ (B uₓ)(B uₓ)ᵀ / ‖B uₓ‖² = (m / d) I`.
Writing `A = ∑ₓ pₓ uₓ uₓᵀ` with `pₓ = 1 / ‖B uₓ‖²`, this is the statement that the *leverages*
`pₓ · uₓᵀ A⁻¹ uₓ` all equal `d / m` (they always sum to `d`, the trace of the identity).

`Matrix.exists_isotropic_weights` proves this up to an arbitrary `ε > 0`: for each `ε > 0` there
are positive weights `p` with `A = ∑ₓ pₓ uₓ uₓᵀ` positive definite and every leverage
`pₓ · uₓᵀ A⁻¹ uₓ ≤ d / m + ε`. This approximate form is what the applications (Forster's
sign-rank bound in `Cslib.Communication.Forster`) use; the exact (`ε = 0`) lemma, which
requires a compactness or minimizer-existence argument, is not formalized here.

The proof is a potential-function argument. With `A(t) = ∑ₓ exp(tₓ) uₓ uₓᵀ`, the function
`φ(t) = log det A(t) - (d / m) ∑ₓ tₓ` is bounded below: for each of the `m` cyclic windows
`e : Fin d ↪ X` the matrix `A(t)` dominates `∑ᵢ exp(t_{e i}) u_{e i} u_{e i}ᵀ`, whose determinant
is `det(U_e)² exp(∑ᵢ t_{e i})` (`Matrix.det_le_det_add_sum_smul_vecMulVec`), and the windows
cover every point `d` times. At a point `t` with `φ(t) < inf φ + δ²`, lowering one coordinate
`tₓ` by `δ` changes `det A` by the factor `1 + (e^{-δ} - 1) qₓ`, where `qₓ` is the leverage
(`Matrix.det_add_smul_vecMulVec`, the matrix determinant lemma), and near-minimality forces
`qₓ < d / m + ε` for `δ = ε / (1 + d / m + ε)`.

General position is generic: `Matrix.eventually_det_submatrix_add_smul_ne_zero` shows that
perturbing `U` by `ε` times a Vandermonde-type matrix makes every `d × d` submatrix invertible
for all small `ε ≠ 0`, because each such determinant is a polynomial in `ε` whose top
coefficient is a nonzero Vandermonde determinant.

## Main results

* `Matrix.det_add_smul_vecMulVec`: the matrix determinant lemma for `B + c • u vᵀ`.
* `Matrix.posDef_sum_smul_vecMulVec`: a positive combination of `uᵢ uᵢᵀ` over spanning vectors
  is positive definite.
* `Matrix.det_le_det_add_sum_smul_vecMulVec`: adding positive semidefinite rank-one terms to a
  positive definite matrix does not decrease the determinant.
* `Matrix.exists_isotropic_weights`: approximate isotropic position.
* `Matrix.eventually_det_submatrix_add_smul_ne_zero`: a generic perturbation is in general
  position.

## References

* [N. Alon, S. Moran and A. Yehudayoff, *Sign rank versus VC dimension*][AlonMoranYehudayoff2016]
* [J. Forster, *A linear lower bound on the unbounded error probabilistic communication
  complexity*][Forster2002]
-/

open Finset Filter Topology

public section

namespace Matrix

variable {n : Type*} [Fintype n]

/-- The bilinear form of a weighted sum of rank-one matrices `vᵢ vᵢᵀ`. -/
theorem dotProduct_sum_smul_vecMulVec_mulVec {R ι : Type*} [CommSemiring R] (s : Finset ι)
    (c : ι → R) (v : ι → n → R) (u w : n → R) :
    u ⬝ᵥ ((∑ i ∈ s, c i • vecMulVec (v i) (v i)) *ᵥ w) =
      ∑ i ∈ s, c i * (v i ⬝ᵥ u) * (v i ⬝ᵥ w) := by
  rw [sum_mulVec, dotProduct_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [smul_mulVec, vecMulVec_mulVec, dotProduct_smul, dotProduct_smul, dotProduct_comm u (v i)]
  simp only [smul_eq_mul, op_smul_eq_mul]
  ring

omit [Fintype n] in
/-- A weighted sum of rank-one matrices `wᵢ • vᵢ vᵢᵀ` over `Fin d` is `Wᵀ (diagonal w) W`, where
`W` has rows `vᵢ`. -/
theorem sum_smul_vecMulVec_eq_transpose_mul_diagonal_mul {R : Type*} [CommSemiring R] {d : ℕ}
    (w : Fin d → R) (W : Matrix (Fin d) n R) :
    ∑ i, w i • vecMulVec (W i) (W i) = Wᵀ * diagonal w * W := by
  ext j k
  simp only [Matrix.sum_apply, Matrix.smul_apply, vecMulVec_apply, smul_eq_mul, Matrix.mul_apply,
    transpose_apply, diagonal_apply, mul_ite, mul_zero, sum_ite_eq', mem_univ, ite_true]
  exact sum_congr rfl fun i _ => by ring

variable [DecidableEq n]

/-- **Matrix determinant lemma** for a rank-one update written with `vecMulVec`:
`det (B + c • u vᵀ) = det B · (1 + c · vᵀ B⁻¹ u)` for invertible `B`. -/
theorem det_add_smul_vecMulVec {R : Type*} [CommRing R] {B : Matrix n n R} (hB : IsUnit B.det)
    (c : R) (u v : n → R) :
    (B + c • vecMulVec u v).det = B.det * (1 + c * (v ⬝ᵥ (B⁻¹ *ᵥ u))) := by
  have h : c • vecMulVec u v = replicateCol (Fin 1) (c • u) * replicateRow (Fin 1) v := by
    ext i j
    simp [vecMulVec_apply, Matrix.mul_apply, mul_assoc]
  have h1 : (1 + replicateRow (Fin 1) v * B⁻¹ * replicateCol (Fin 1) (c • u) :
      Matrix (Fin 1) (Fin 1) R) = Matrix.of fun _ _ => 1 + c * (v ⬝ᵥ (B⁻¹ *ᵥ u)) := by
    ext i j
    fin_cases i
    fin_cases j
    simp only [Matrix.add_apply, Matrix.one_apply_eq, Matrix.mul_apply, replicateRow_apply,
      replicateCol_apply, Pi.smul_apply, smul_eq_mul, Matrix.of_apply, dotProduct, mulVec]
    congr 1
    simp only [sum_mul, mul_sum]
    rw [sum_comm]
    exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by ring
  calc (B + c • vecMulVec u v).det
      = B.det * (1 + replicateRow (Fin 1) v * B⁻¹ * replicateCol (Fin 1) (c • u)).det := by
        rw [h]; exact det_add_replicateCol_mul_replicateRow hB (c • u) v
    _ = B.det * (1 + c * (v ⬝ᵥ (B⁻¹ *ᵥ u))) := by
        rw [h1, det_fin_one]
        rfl

omit [DecidableEq n] in
/-- A positive combination of the rank-one matrices `vᵢ vᵢᵀ` is positive definite when the `vᵢ`
span `ℝⁿ`, i.e. only the zero vector is orthogonal to all of them. -/
theorem posDef_sum_smul_vecMulVec {ι : Type*} (s : Finset ι) (c : ι → ℝ)
    (hc : ∀ i ∈ s, 0 < c i) (v : ι → n → ℝ)
    (hv : ∀ w : n → ℝ, (∀ i ∈ s, v i ⬝ᵥ w = 0) → w = 0) :
    (∑ i ∈ s, c i • vecMulVec (v i) (v i)).PosDef := by
  have hpsd : (∑ i ∈ s, c i • vecMulVec (v i) (v i)).PosSemidef :=
    posSemidef_sum s fun i hi => by
      simpa using (posSemidef_vecMulVec_self_star (v i)).smul (hc i hi).le
  refine PosDef.of_dotProduct_mulVec_pos hpsd.isHermitian fun w hw => ?_
  rw [star_trivial, dotProduct_sum_smul_vecMulVec_mulVec]
  obtain ⟨i, hi, hne⟩ : ∃ i ∈ s, v i ⬝ᵥ w ≠ 0 := by
    by_contra h
    exact hw (hv w fun i hi => by_contra fun hne => h ⟨i, hi, hne⟩)
  exact sum_pos' (fun j hj => by nlinarith [(hc j hj).le, sq_nonneg (v j ⬝ᵥ w)])
    ⟨i, hi, by nlinarith [hc i hi, sq_pos_of_ne_zero hne]⟩

/-- Adding nonnegative multiples of rank-one matrices `vᵢ vᵢᵀ` to a positive definite matrix
does not decrease its determinant. -/
theorem det_le_det_add_sum_smul_vecMulVec {ι : Type*} (s : Finset ι) {B : Matrix n n ℝ}
    (hB : B.PosDef) (c : ι → ℝ) (hc : ∀ i ∈ s, 0 ≤ c i) (v : ι → n → ℝ) :
    B.det ≤ (B + ∑ i ∈ s, c i • vecMulVec (v i) (v i)).det := by
  classical
  suffices h : B.det ≤ (B + ∑ i ∈ s, c i • vecMulVec (v i) (v i)).det ∧
      (B + ∑ i ∈ s, c i • vecMulVec (v i) (v i)).PosDef from h.1
  induction s using Finset.induction_on with
  | empty => simpa using hB
  | insert a s ha ih =>
    obtain ⟨ih1, ih2⟩ := ih fun i hi => hc i (mem_insert_of_mem hi)
    have hca := hc a (mem_insert_self a s)
    rw [sum_insert ha, add_left_comm, add_comm _ (B + _)]
    refine ⟨?_, ih2.add_posSemidef (by
      simpa using (posSemidef_vecMulVec_self_star (v a)).smul hca)⟩
    rw [det_add_smul_vecMulVec ih2.det_pos.ne'.isUnit]
    have hq : 0 ≤ v a ⬝ᵥ ((B + ∑ i ∈ s, c i • vecMulVec (v i) (v i))⁻¹ *ᵥ v a) := by
      simpa using ih2.inv.posSemidef.dotProduct_mulVec_nonneg (v a)
    nlinarith [ih2.det_pos, mul_nonneg hca hq]

/-- The determinant of `∑ᵢ exp(sᵢ) • wᵢ wᵢᵀ` over the rows of a square matrix `W`. -/
private theorem det_sum_exp_smul_vecMulVec {d : ℕ} (s : Fin d → ℝ)
    (W : Matrix (Fin d) (Fin d) ℝ) :
    (∑ i, Real.exp (s i) • vecMulVec (W i) (W i)).det = W.det ^ 2 * Real.exp (∑ i, s i) := by
  rw [sum_smul_vecMulVec_eq_transpose_mul_diagonal_mul, det_mul, det_mul, det_transpose,
    det_diagonal, Real.exp_sum]
  ring

/-- **Approximate isotropic position** (Forster's lemma up to `ε`). If the `m = |X|` rows of
`U : Matrix X (Fin d) ℝ` are in general position (every `d × d` submatrix is invertible) and
`d ≤ m`, then for every `ε > 0` there are positive weights `p` such that
`A = ∑ₓ pₓ • uₓ uₓᵀ` is positive definite and every leverage `pₓ · uₓᵀ A⁻¹ uₓ` is at most
`d / m + ε`. The exact (`ε = 0`) statement is [Alon, Moran and Yehudayoff, Lemma 26]
[AlonMoranYehudayoff2016], due to [Forster][Forster2002]; this approximate form suffices for
Forster's sign-rank bound. -/
theorem exists_isotropic_weights {X : Type*} [Fintype X] {d : ℕ} (U : Matrix X (Fin d) ℝ)
    (hU : ∀ e : Fin d ↪ X, (U.submatrix e id).det ≠ 0) (hd : d ≤ Fintype.card X) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ p : X → ℝ, (∀ x, 0 < p x) ∧ (∑ x, p x • vecMulVec (U x) (U x)).PosDef ∧
      ∀ x, p x * (U x ⬝ᵥ ((∑ z, p z • vecMulVec (U z) (U z))⁻¹ *ᵥ U x)) ≤
        d / Fintype.card X + ε := by
  classical
  have hspan : ∀ w : Fin d → ℝ, (∀ x ∈ (univ : Finset X), U x ⬝ᵥ w = 0) → w = 0 := by
    intro w hw
    obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le (α := Fin d) (β := X)
      (by simpa using hd)
    exact eq_zero_of_mulVec_eq_zero (hU e) (funext fun i => hw (e i) (mem_univ _))
  set A : (X → ℝ) → Matrix (Fin d) (Fin d) ℝ :=
    fun t => ∑ x, Real.exp (t x) • vecMulVec (U x) (U x) with hA
  have hApd : ∀ t, (A t).PosDef := fun t =>
    posDef_sum_smul_vecMulVec univ _ (fun x _ => Real.exp_pos _) U hspan
  rcases isEmpty_or_nonempty X with hX | hX
  · exact ⟨fun _ => 1, fun _ => one_pos, by simpa [A] using hApd 0, fun x => isEmptyElim x⟩
  -- Each window `e` bounds `log det A(t)` below by `log det(U_e)² + ∑ᵢ t_{e i}`.
  have hwin : ∀ (t : X → ℝ) (e : Fin d ↪ X),
      Real.log ((U.submatrix e id).det ^ 2) + ∑ i, t (e i) ≤ Real.log (A t).det := by
    intro t e
    set W := U.submatrix e id
    have hsplit : A t = ∑ i, Real.exp (t (e i)) • vecMulVec (W i) (W i) +
        ∑ x ∈ (univ.map e)ᶜ, Real.exp (t x) • vecMulVec (U x) (U x) := by
      rw [hA]
      dsimp only
      rw [← sum_add_sum_compl (univ.map e), sum_map]
      rfl
    have hWpd : (∑ i, Real.exp (t (e i)) • vecMulVec (W i) (W i)).PosDef :=
      posDef_sum_smul_vecMulVec univ _ (fun i _ => Real.exp_pos _) W fun w hw =>
        eq_zero_of_mulVec_eq_zero (hU e) (funext fun i => hw i (mem_univ _))
    have hdet := det_le_det_add_sum_smul_vecMulVec (univ.map e)ᶜ hWpd
      (fun x => Real.exp (t x)) (fun x _ => (Real.exp_pos _).le) U
    rw [← hsplit, det_sum_exp_smul_vecMulVec] at hdet
    have hW2 : 0 < W.det ^ 2 := by positivity [hU e]
    calc Real.log (W.det ^ 2) + ∑ i, t (e i)
        = Real.log (W.det ^ 2 * Real.exp (∑ i, t (e i))) := by
          rw [Real.log_mul hW2.ne' (Real.exp_pos _).ne', Real.log_exp]
      _ ≤ Real.log (A t).det := Real.log_le_log (by positivity) hdet
  -- The `m` cyclic windows cover every point `d` times, so `φ` is bounded below.
  set m := Fintype.card X with hm
  have hm0 : 0 < m := Fintype.card_pos
  have : NeZero m := ⟨hm0.ne'⟩
  let σ : X ≃ Fin m := Fintype.equivFin X
  let e : Fin m → Fin d ↪ X := fun k =>
    ⟨fun i => σ.symm (k + Fin.castLE hd i), fun i j h => by
      simpa using (Fin.castLE_injective hd) (add_left_cancel (σ.symm.injective h))⟩
  set r : ℝ := d / m with hr
  have hmr : (m : ℝ) * r = d := by rw [hr]; field_simp
  set C : ℝ := (∑ k, Real.log ((U.submatrix (e k) id).det ^ 2)) / m with hC
  have hcount : ∀ t : X → ℝ, ∑ k, ∑ i, t (e k i) = d * ∑ x, t x := by
    intro t
    rw [sum_comm]
    have : ∀ i : Fin d, ∑ k : Fin m, t (e k i) = ∑ x, t x := fun i => by
      rw [← σ.symm.sum_comp]
      exact Fintype.sum_equiv (Equiv.addRight (Fin.castLE hd i)) _ _ fun k => rfl
    simp only [this, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hlow : ∀ t : X → ℝ, C ≤ Real.log (A t).det - r * ∑ x, t x := by
    intro t
    have hsum := sum_le_sum fun k (_ : k ∈ (univ : Finset (Fin m))) => hwin t (e k)
    rw [sum_add_distrib, hcount, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
    rw [hC, div_le_iff₀ (by exact_mod_cast hm0)]
    have h2 : (Real.log (A t).det - r * ∑ x, t x) * m =
        m * Real.log (A t).det - d * ∑ x, t x := by
      rw [← hmr]; ring
    linarith
  -- A `δ²`-near-minimizer of `φ` has all leverages below `r + ε`.
  set φ : (X → ℝ) → ℝ := fun t => Real.log (A t).det - r * ∑ x, t x with hφ
  have hbdd : BddBelow (Set.range φ) := ⟨C, by rintro _ ⟨t, rfl⟩; exact hlow t⟩
  set L := ⨅ t, φ t
  have hr0 : 0 ≤ r := by positivity
  set δ : ℝ := ε / (1 + r + ε) with hδ
  have hδ0 : 0 < δ := by positivity
  have hδ1 : δ < 1 := by rw [hδ, div_lt_one (by positivity)]; linarith
  obtain ⟨t, ht⟩ : ∃ t, φ t < L + δ ^ 2 :=
    exists_lt_of_ciInf_lt (by linarith [sq_pos_of_pos hδ0])
  refine ⟨fun x => Real.exp (t x), fun x => Real.exp_pos _, hApd t, fun x => ?_⟩
  change Real.exp (t x) * (U x ⬝ᵥ (A t)⁻¹ *ᵥ U x) ≤ r + ε
  set q := Real.exp (t x) * (U x ⬝ᵥ (A t)⁻¹ *ᵥ U x) with hq
  have hq0 : 0 ≤ q := mul_nonneg (Real.exp_pos _).le
    (by simpa using (hApd t).inv.posSemidef.dotProduct_mulVec_nonneg (U x))
  set t' := Function.update t x (t x - δ)
  have hLt' : L ≤ φ t' := ciInf_le hbdd t'
  have hAt' : A t' = A t + (Real.exp (t x - δ) - Real.exp (t x)) • vecMulVec (U x) (U x) := by
    simp only [hA, t']
    rw [← add_sum_erase _ _ (mem_univ x), ← add_sum_erase _ _ (mem_univ x),
      Function.update_self, sub_smul]
    rw [sum_congr rfl fun z hz => by rw [Function.update_of_ne (ne_of_mem_erase hz)]]
    abel
  have hsum' : ∑ z, t' z = ∑ z, t z - δ := by
    simp only [t']
    rw [← add_sum_erase _ _ (mem_univ x), ← add_sum_erase _ _ (mem_univ x),
      Function.update_self]
    rw [sum_congr rfl fun z hz => by rw [Function.update_of_ne (ne_of_mem_erase hz)]]
    ring
  have hdet' : (A t').det = (A t).det * (1 + (Real.exp (-δ) - 1) * q) := by
    rw [hAt', det_add_smul_vecMulVec (hApd t).det_pos.ne'.isUnit, hq, sub_eq_add_neg (t x),
      Real.exp_add]
    ring
  have hy : 0 < 1 + (Real.exp (-δ) - 1) * q := by
    have h1 := (hApd t').det_pos
    rw [hdet'] at h1
    exact pos_of_mul_pos_right h1 (hApd t).det_pos.le
  have hφ' : φ t' = φ t + Real.log (1 + (Real.exp (-δ) - 1) * q) + r * δ := by
    simp only [hφ]
    rw [hdet', Real.log_mul (hApd t).det_pos.ne' hy.ne', hsum']
    ring
  have hlog := Real.log_le_sub_one_of_pos hy
  have hexp : Real.exp (-δ) - 1 ≤ -δ + δ ^ 2 := by
    have := Real.abs_exp_sub_one_sub_id_le (x := -δ)
      (by rw [abs_neg, abs_of_pos hδ0]; exact hδ1.le)
    have := (abs_le.mp this).2
    nlinarith
  have key : δ * (1 - δ) * q < δ ^ 2 + r * δ := by
    nlinarith [mul_le_mul_of_nonneg_right hexp hq0]
  have key2 : (1 - δ) * q < δ + r := by
    by_contra hcon
    push Not at hcon
    nlinarith [mul_le_mul_of_nonneg_left hcon hδ0.le]
  have hδdef : δ * (1 + r + ε) = ε := by rw [hδ]; field_simp
  by_contra hcon
  push Not at hcon
  have : (1 - δ) * (r + ε) < δ + r :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_left hcon.le (by linarith)) key2
  nlinarith

/-- **General position is generic.** For any `U : Matrix X (Fin d) ℝ` there is a matrix `W` such
that for all sufficiently small `ε ≠ 0` every `d × d` submatrix of `U + ε • W` is invertible.
(`W` has rows `(1, k, k², …)` for distinct `k`, so each such determinant is a polynomial in `ε`
with a nonzero Vandermonde leading coefficient.) -/
theorem eventually_det_submatrix_add_smul_ne_zero {X : Type*} [Finite X] {d : ℕ}
    (U : Matrix X (Fin d) ℝ) :
    ∃ W : Matrix X (Fin d) ℝ,
      ∀ᶠ ε in 𝓝[≠] (0 : ℝ), ∀ e : Fin d ↪ X, ((U + ε • W).submatrix e id).det ≠ 0 := by
  classical
  have := Fintype.ofFinite X
  let σ : X ≃ Fin (Fintype.card X) := Fintype.equivFin X
  let W : Matrix X (Fin d) ℝ := fun x j => ((σ x : ℕ) : ℝ) ^ (j : ℕ)
  refine ⟨W, eventually_all.2 fun e => ?_⟩
  let P : Polynomial ℝ := det ((Polynomial.X : Polynomial ℝ) •
    (W.submatrix e id).map Polynomial.C + (U.submatrix e id).map Polynomial.C)
  have hWe : (W.submatrix e id).det ≠ 0 := by
    have : W.submatrix e id = vandermonde fun i => ((σ (e i) : ℕ) : ℝ) := by
      ext i j; rfl
    rw [this, det_vandermonde_ne_zero_iff]
    intro i j h
    exact e.injective (σ.injective (Fin.ext (by
      exact_mod_cast (show ((σ (e i) : ℕ) : ℝ) = ((σ (e j) : ℕ) : ℝ) from h))))
  have hP : P ≠ 0 := by
    intro h
    apply hWe
    rw [← Polynomial.coeff_det_X_add_C_card (W.submatrix e id) (U.submatrix e id)]
    change P.coeff _ = 0
    rw [h, Polynomial.coeff_zero]
  have heval : ∀ ε : ℝ, P.eval ε = ((U + ε • W).submatrix e id).det := by
    intro ε
    rw [← Polynomial.coe_evalRingHom, RingHom.map_det]
    congr 1
    ext i j
    simp only [Polynomial.coe_evalRingHom, RingHom.mapMatrix_apply, map_apply, Matrix.add_apply,
      Matrix.smul_apply, smul_eq_mul, submatrix_apply, id, Polynomial.eval_add,
      Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_C]
    ring
  filter_upwards [(Polynomial.eventually_eval_ne_zero_cofinite hP).filter_mono
    (nhdsNE_le_cofinite 0)] with ε hε
  rwa [← heval]

end Matrix

end
