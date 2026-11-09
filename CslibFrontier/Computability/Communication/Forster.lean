/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Communication.PaturiSimon
public import CslibFrontier.Foundations.Data.BitString.Basic
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.LinearAlgebra.Matrix.HadamardMatrix
import CslibFrontier.Computability.Communication.InnerProductRank
import CslibFrontier.Foundations.LinearAlgebra.Matrix.IsotropicPosition
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Forster's sign-rank lower bound

**Forster's theorem** [Forster, 2002][Forster2002] bounds the sign-rank of an `X × Y` sign matrix
`S` below by `√(|X| |Y|) / ‖S‖`, where `‖S‖` is the spectral (`ℓ²` operator) norm. Its
generalization to matrices `M` without zero entries [Sherstov and Wu, Theorem A.2]
[SherstovWu2019], attributed there to Forster, Krause, Lokam, Mubarakzjanov, Schmitt and Simon, is
`signRank(sign M) ≥ √(|X| |Y|) / ‖M‖ · minₓᵧ |Mₓᵧ|`.

`Cslib.Communication.mul_sqrt_card_mul_card_le_mul_signRank` proves the bilinear form of this
bound: if `μ ≤ (-1)^{f x y} M x y` for all `x, y` and
`|∑ₓᵧ pₓ Mₓᵧ qᵧ| ≤ λ ‖p‖₂ ‖q‖₂` for all real `p, q`, then `μ √(|X| |Y|) ≤ λ · signRank f`.
Taking `λ = ‖M‖` gives Theorem A.2
(`Cslib.Communication.mul_sqrt_card_mul_card_le_l2_opNorm_mul_signRank`) and `M` the sign
matrix gives Forster's bound (`Cslib.Communication.sqrt_card_mul_card_le_l2_opNorm_mul_signRank`).
An `N × N` Hadamard sign matrix has spectral norm `√N`, so its sign-rank is at least `√N`
(`Cslib.Communication.card_le_signRank_sq_of_isHadamard`). The sign matrix of the inner product
on `n` bits is the `2ⁿ × 2ⁿ` Sylvester–Hadamard matrix, so `2ⁿ ≤ signRank(IPₙ)²`
(`Cslib.Communication.two_pow_card_le_signRank_dotProduct_sq`), and by the Paturi–Simon lower
bound its unbounded-error communication complexity is at least `⌈n / 2⌉`
(`Cslib.Communication.PrivateCoin.card_add_one_div_two_le_uppComplexityFun_dotProduct`).

The proof follows [Alon, Moran and Yehudayoff, proof of Theorem 23][AlonMoranYehudayoff2016].
Factor a sign-representation of `f` as `U V` through `d = signRank f` dimensions, perturb the
rows of `U` into general position (`Matrix.eventually_det_submatrix_add_smul_ne_zero`), and
reweight them into approximate isotropic position (`Matrix.exists_isotropic_weights`): with
`A = ∑ₓ pₓ uₓ uₓᵀ` and leverages `pₓ uₓᵀ A⁻¹ uₓ ≤ d / |X| + ε`, the unit vectors
`aₓ ∝ (√p_z · u_zᵀ A⁻¹ uₓ)_z` and `bᵧ ∝ (√p_z · u_zᵀ vᵧ)_z` satisfy `⟨aₓ, bᵧ⟩ ∝ uₓᵀ vᵧ` and
`∑ₓ ⟨aₓ, bᵧ⟩² ≥ 1 / (d / |X| + ε)`. Double counting `∑ₓᵧ Mₓᵧ ⟨aₓ, bᵧ⟩` against the bilinear
bound then gives `|Y| μ / (d / |X| + ε) ≤ λ √(|X| |Y|)`, and `ε → 0` finishes. Using an
approximate isotropic position in place of Forster's exact one is the only departure from the
source argument.

## Main results

* `Cslib.Communication.mul_sqrt_card_mul_card_le_mul_signRank`: Forster's bound, bilinear form.
* `Cslib.Communication.mul_sqrt_card_mul_card_le_l2_opNorm_mul_signRank`: the bound for real
  matrices without zero entries [Sherstov and Wu, Theorem A.2][SherstovWu2019].
* `Cslib.Communication.sqrt_card_mul_card_le_l2_opNorm_mul_signRank`: Forster's theorem for sign
  matrices.
* `Cslib.Communication.card_le_signRank_sq_of_isHadamard`: a Hadamard sign matrix of size `N` has
  sign-rank at least `√N`.
* `Cslib.Communication.two_pow_card_le_signRank_dotProduct_sq`: the inner product on `n` bits has
  sign-rank at least `2^{n/2}`.
* `Cslib.Communication.PrivateCoin.card_add_one_div_two_le_uppComplexityFun_dotProduct`: its
  unbounded-error communication complexity is at least `⌈n / 2⌉`.

## References

* [N. Alon, S. Moran and A. Yehudayoff, *Sign rank versus VC dimension*][AlonMoranYehudayoff2016]
* [J. Forster, *A linear lower bound on the unbounded error probabilistic communication
  complexity*][Forster2002]
* [A. A. Sherstov and P. Wu, *Near-optimal lower bounds on the threshold degree and sign-rank of
  AC⁰*][SherstovWu2019]
-/

open Finset Matrix Filter Topology

public section

namespace Cslib.Communication

variable {X Y : Type*} [Fintype X] [Fintype Y]

/-- The double-counting step of Forster's argument: unit vectors `aₓ, bᵧ` correlated with `M`
(`μ ⟨aₓ, bᵧ⟩² ≤ Mₓᵧ ⟨aₓ, bᵧ⟩`) and spread out (`∑ₓ ⟨aₓ, bᵧ⟩² ≥ c`) force
`|Y| μ c ≤ λ √|X| √|Y|`. -/
private theorem card_mul_le_of_unit_vectors {K : Type*} [Fintype K] (M : Matrix X Y ℝ)
    {lam μ c : ℝ}
    (hspec : ∀ (p : X → ℝ) (q : Y → ℝ),
      |∑ x, ∑ y, p x * M x y * q y| ≤ lam * √(∑ x, p x ^ 2) * √(∑ y, q y ^ 2))
    (a : X → K → ℝ) (b : Y → K → ℝ) (ha : ∀ x, a x ⬝ᵥ a x = 1) (hb : ∀ y, b y ⬝ᵥ b y = 1)
    (hM : ∀ x y, μ * (a x ⬝ᵥ b y) ^ 2 ≤ M x y * (a x ⬝ᵥ b y)) (hμ : 0 ≤ μ)
    (hc : ∀ y, c ≤ ∑ x, (a x ⬝ᵥ b y) ^ 2) (hlam : 0 ≤ lam) :
    Fintype.card Y * (μ * c) ≤ lam * √(Fintype.card X) * √(Fintype.card Y) := by
  calc (Fintype.card Y : ℝ) * (μ * c) = ∑ _y : Y, μ * c := by
        rw [sum_const, card_univ, nsmul_eq_mul]
    _ ≤ ∑ y, ∑ x, μ * (a x ⬝ᵥ b y) ^ 2 := sum_le_sum fun y _ => by
        rw [← mul_sum]; exact mul_le_mul_of_nonneg_left (hc y) hμ
    _ ≤ ∑ y, ∑ x, M x y * (a x ⬝ᵥ b y) := sum_le_sum fun y _ => sum_le_sum fun x _ => hM x y
    _ = ∑ k, ∑ x, ∑ y, a x k * M x y * b y k := by
        simp only [dotProduct, mul_sum]
        rw [sum_comm]
        refine (sum_congr rfl fun x _ => ?_).trans sum_comm
        rw [sum_comm]
        exact sum_congr rfl fun y _ => sum_congr rfl fun k _ => by ring
    _ ≤ ∑ k, lam * √(∑ x, a x k ^ 2) * √(∑ y, b y k ^ 2) :=
        sum_le_sum fun k _ => (le_abs_self _).trans (hspec (fun x => a x k) (fun y => b y k))
    _ = lam * ∑ k, √(∑ x, a x k ^ 2) * √(∑ y, b y k ^ 2) := by
        rw [mul_sum]; exact sum_congr rfl fun k _ => by ring
    _ ≤ lam * (√(∑ k, ∑ x, a x k ^ 2) * √(∑ k, ∑ y, b y k ^ 2)) :=
        mul_le_mul_of_nonneg_left (Real.sum_sqrt_mul_sqrt_le _
          (fun k => sum_nonneg fun x _ => sq_nonneg _)
          (fun k => sum_nonneg fun y _ => sq_nonneg _)) hlam
    _ = lam * √(Fintype.card X) * √(Fintype.card Y) := by
        have hX : ∑ k, ∑ x, a x k ^ 2 = Fintype.card X := by
          rw [sum_comm]
          simp only [sq, ← dotProduct.eq_1, ha, sum_const, card_univ, nsmul_eq_mul, mul_one]
        have hY : ∑ k, ∑ y, b y k ^ 2 = Fintype.card Y := by
          rw [sum_comm]
          simp only [sq, ← dotProduct.eq_1, hb, sum_const, card_univ, nsmul_eq_mul, mul_one]
        rw [hX, hY, mul_assoc]

omit [Fintype X] [Fintype Y] in
/-- A sign-representation `U V` can be perturbed in `U` to one whose rows are in general
position. -/
private theorem exists_generalPosition_of_mul [Finite X] [Finite Y] {d : ℕ}
    (U : Matrix X (Fin d) ℝ) (V : Matrix (Fin d) Y ℝ) (s : X → Y → ℝ)
    (hUV : ∀ x y, 0 < s x y * (U * V) x y) :
    ∃ U' : Matrix X (Fin d) ℝ, (∀ e : Fin d ↪ X, (U'.submatrix e id).det ≠ 0) ∧
      ∀ x y, 0 < s x y * (U' * V) x y := by
  have := Fintype.ofFinite Y
  obtain ⟨W, hdet⟩ := Matrix.eventually_det_submatrix_add_smul_ne_zero U
  have hsign : ∀ᶠ ε in 𝓝 (0 : ℝ), ∀ x y, 0 < s x y * ((U + ε • W) * V) x y := by
    refine eventually_all.2 fun x => eventually_all.2 fun y => ?_
    have hc : Continuous fun ε : ℝ => s x y * ((U + ε • W) * V) x y := by
      simp only [Matrix.add_mul, Matrix.smul_mul, Matrix.add_apply, Matrix.smul_apply,
        smul_eq_mul]
      fun_prop
    exact hc.continuousAt.eventually (lt_mem_nhds (by simpa using hUV x y))
  obtain ⟨ε, hε1, hε2⟩ := (hdet.and (hsign.filter_mono nhdsWithin_le_nhds)).exists
  exact ⟨U + ε • W, hε1, hε2⟩

/-- **Forster's sign-rank bound, bilinear form.** Let `M` be a real `X × Y` matrix with
`μ ≤ (-1)^{f x y} M x y` for all `x, y` (so for `μ > 0`, `M` sign-represents `f` with margin `μ`)
and `|∑ₓᵧ pₓ Mₓᵧ qᵧ| ≤ λ ‖p‖₂ ‖q‖₂` for all real vectors `p, q`. Then
`μ √(|X| |Y|) ≤ λ · signRank f` [Sherstov and Wu, Theorem A.2][SherstovWu2019]; the proof follows
[Alon, Moran and Yehudayoff, proof of Theorem 23][AlonMoranYehudayoff2016], with an approximate
isotropic position (`Matrix.exists_isotropic_weights`) in place of Forster's exact one. -/
theorem mul_sqrt_card_mul_card_le_mul_signRank (f : X → Y → Bool) (M : Matrix X Y ℝ) {μ lam : ℝ}
    (hμ : ∀ x y, μ ≤ signMatrix ℝ f x y * M x y)
    (hspec : ∀ (p : X → ℝ) (q : Y → ℝ),
      |∑ x, ∑ y, p x * M x y * q y| ≤ lam * √(∑ x, p x ^ 2) * √(∑ y, q y ^ 2)) :
    μ * √(Fintype.card X * Fintype.card Y) ≤ lam * signRank f := by
  classical
  rcases isEmpty_or_nonempty X with hX | ⟨⟨x₀⟩⟩
  · have h := signRank_le_card_left f
    rw [Fintype.card_eq_zero, Nat.le_zero] at h
    simp [h, Fintype.card_eq_zero]
  rcases isEmpty_or_nonempty Y with hY | ⟨⟨y₀⟩⟩
  · have h := signRank_le_card_right f
    rw [Fintype.card_eq_zero, Nat.le_zero] at h
    simp [h, Fintype.card_eq_zero]
  have hm : (0 : ℝ) < Fintype.card X := by exact_mod_cast Fintype.card_pos_iff.2 ⟨x₀⟩
  have hn : (0 : ℝ) < Fintype.card Y := by exact_mod_cast Fintype.card_pos_iff.2 ⟨y₀⟩
  have hm' : 0 < √(Fintype.card X : ℝ) := Real.sqrt_pos.2 hm
  have hn' : 0 < √(Fintype.card Y : ℝ) := Real.sqrt_pos.2 hn
  have hlam : 0 ≤ lam := by
    have h := (abs_nonneg _).trans (hspec (fun _ => 1) (fun _ => 1))
    simp only [one_pow, sum_const, card_univ, nsmul_eq_mul, mul_one] at h
    by_contra hneg
    push Not at hneg
    have := mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hneg hm') hn'
    linarith
  rcases le_or_gt μ 0 with hμ0 | hμ0
  · nlinarith [Real.sqrt_nonneg (Fintype.card X * Fintype.card Y : ℝ),
      mul_nonneg hlam (Nat.cast_nonneg (α := ℝ) (signRank f))]
  have hdm : signRank f ≤ Fintype.card X := signRank_le_card_left f
  obtain ⟨U, V, hUV⟩ := exists_mul_signRepresents f
  obtain ⟨U', hgen, hU'V⟩ := exists_generalPosition_of_mul U V (signMatrix ℝ f) hUV
  -- For every `ε > 0`: `|Y| μ ≤ (d / |X| + ε) λ √|X| √|Y|`.
  have key : ∀ ε > 0, (Fintype.card Y : ℝ) * μ ≤
      ((signRank f : ℝ) / Fintype.card X + ε) *
        (lam * √(Fintype.card X : ℝ) * √(Fintype.card Y : ℝ)) := by
    intro ε hε
    obtain ⟨p, hp, hApd, hlev⟩ := Matrix.exists_isotropic_weights U' hgen hdm hε
    set R : ℝ := (signRank f : ℝ) / Fintype.card X + ε with hR
    have hR0 : 0 < R := by positivity
    set A := ∑ x, p x • vecMulVec (U' x) (U' x) with hA
    set B := A⁻¹ with hB
    have hBpd : B.PosDef := hApd.inv
    have hAB : A * B = 1 := mul_nonsing_inv A hApd.det_pos.ne'.isUnit
    have hAsymm : Aᵀ = A := by
      have := hApd.isHermitian
      rwa [IsHermitian, conjTranspose_eq_transpose_of_trivial] at this
    let v : Y → Fin (signRank f) → ℝ := fun y j => V j y
    have hUv : ∀ x y, (U' * V) x y = U' x ⬝ᵥ v y := fun x y => rfl
    have hbil : ∀ u w : Fin (signRank f) → ℝ,
        u ⬝ᵥ (A *ᵥ w) = ∑ z, p z * (U' z ⬝ᵥ u) * (U' z ⬝ᵥ w) :=
      fun u w => Matrix.dotProduct_sum_smul_vecMulVec_mulVec univ p U' u w
    have hcross : ∀ u w : Fin (signRank f) → ℝ, (B *ᵥ u) ⬝ᵥ (A *ᵥ w) = u ⬝ᵥ w := by
      intro u w
      rw [dotProduct_mulVec, ← mulVec_transpose, hAsymm, mulVec_mulVec, hAB, one_mulVec]
    set g : X → ℝ := fun x => U' x ⬝ᵥ (B *ᵥ U' x) with hg
    set h : Y → ℝ := fun y => v y ⬝ᵥ (A *ᵥ v y) with hh
    have hU0 : ∀ x, U' x ≠ 0 := fun x h0 => by
      have := hU'V x y₀
      rw [hUv, h0, zero_dotProduct, mul_zero] at this
      exact lt_irrefl _ this
    have hv0 : ∀ y, v y ≠ 0 := fun y h0 => by
      have := hU'V x₀ y
      rw [hUv, h0, dotProduct_zero, mul_zero] at this
      exact lt_irrefl _ this
    have hg0 : ∀ x, 0 < g x := fun x => by simpa using hBpd.dotProduct_mulVec_pos (hU0 x)
    have hh0 : ∀ y, 0 < h y := fun y => by simpa using hApd.dotProduct_mulVec_pos (hv0 y)
    have hsq : ∀ z, √(p z) * √(p z) = p z := fun z => Real.mul_self_sqrt (hp z).le
    have hpair : ∀ (F G : X → ℝ) (s s' : ℝ),
        ∑ z, √(p z) * F z / s * (√(p z) * G z / s') = (∑ z, p z * F z * G z) / (s * s') := by
      intro F G s s'
      rw [sum_div]
      refine sum_congr rfl fun z _ => ?_
      rw [div_mul_div_comm]
      congr 1
      linear_combination F z * G z * hsq z
    -- The normalized vectors of the isotropic configuration.
    let a : X → X → ℝ := fun x z => √(p z) * (U' z ⬝ᵥ (B *ᵥ U' x)) / √(g x)
    let b : Y → X → ℝ := fun y z => √(p z) * (U' z ⬝ᵥ v y) / √(h y)
    have hab : ∀ x y, a x ⬝ᵥ b y = (U' x ⬝ᵥ v y) / (√(g x) * √(h y)) := by
      intro x y
      calc a x ⬝ᵥ b y
          = (∑ z, p z * (U' z ⬝ᵥ (B *ᵥ U' x)) * (U' z ⬝ᵥ v y)) / (√(g x) * √(h y)) :=
            hpair (fun z => U' z ⬝ᵥ (B *ᵥ U' x)) (fun z => U' z ⬝ᵥ v y) _ _
        _ = (U' x ⬝ᵥ v y) / (√(g x) * √(h y)) := by rw [← hbil, hcross]
    have haa : ∀ x, a x ⬝ᵥ a x = 1 := by
      intro x
      calc a x ⬝ᵥ a x
          = (∑ z, p z * (U' z ⬝ᵥ (B *ᵥ U' x)) * (U' z ⬝ᵥ (B *ᵥ U' x))) /
              (√(g x) * √(g x)) :=
            hpair (fun z => U' z ⬝ᵥ (B *ᵥ U' x)) (fun z => U' z ⬝ᵥ (B *ᵥ U' x)) _ _
        _ = 1 := by
            rw [← hbil, hcross, Real.mul_self_sqrt (hg0 x).le]
            exact div_self (hg0 x).ne'
    have hbb : ∀ y, b y ⬝ᵥ b y = 1 := by
      intro y
      calc b y ⬝ᵥ b y
          = (∑ z, p z * (U' z ⬝ᵥ v y) * (U' z ⬝ᵥ v y)) / (√(h y) * √(h y)) :=
            hpair (fun z => U' z ⬝ᵥ v y) (fun z => U' z ⬝ᵥ v y) _ _
        _ = 1 := by
            rw [← hbil, Real.mul_self_sqrt (hh0 y).le]
            exact div_self (hh0 y).ne'
    have hc : ∀ y, 1 / R ≤ ∑ x, (a x ⬝ᵥ b y) ^ 2 := by
      intro y
      have hterm : ∀ x, p x * (U' x ⬝ᵥ v y) ^ 2 / (R * h y) ≤ (a x ⬝ᵥ b y) ^ 2 := by
        intro x
        rw [hab, div_pow, mul_pow, Real.sq_sqrt (hg0 x).le, Real.sq_sqrt (hh0 y).le,
          div_le_div_iff₀ (mul_pos hR0 (hh0 y)) (mul_pos (hg0 x) (hh0 y))]
        have hlev' : p x * g x ≤ R := hlev x
        nlinarith [mul_le_mul_of_nonneg_left hlev'
          (mul_nonneg (sq_nonneg (U' x ⬝ᵥ v y)) (hh0 y).le)]
      have hsum : ∑ x, p x * (U' x ⬝ᵥ v y) ^ 2 = h y := by
        change _ = v y ⬝ᵥ (A *ᵥ v y)
        rw [hbil]
        exact sum_congr rfl fun x _ => by ring
      have hhy := (hh0 y).ne'
      calc 1 / R = ∑ x, p x * (U' x ⬝ᵥ v y) ^ 2 / (R * h y) := by
            rw [← sum_div, hsum]
            field_simp
        _ ≤ ∑ x, (a x ⬝ᵥ b y) ^ 2 := sum_le_sum fun x _ => hterm x
    have hMab : ∀ x y, μ * (a x ⬝ᵥ b y) ^ 2 ≤ M x y * (a x ⬝ᵥ b y) := by
      intro x y
      set w := a x ⬝ᵥ b y with hw
      set s := signMatrix ℝ f x y with hs
      have hs2 : s * s = 1 := by rw [hs, signMatrix_apply]; split_ifs <;> norm_num
      have hsw : 0 < s * w := by
        rw [hw, hab, mul_div_assoc']
        exact div_pos (hU'V x y)
          (mul_pos (Real.sqrt_pos.2 (hg0 x)) (Real.sqrt_pos.2 (hh0 y)))
      have hw1 : w ^ 2 ≤ 1 := by
        have h1 := sum_mul_sq_le_sq_mul_sq univ (a x) (b y)
        have e1 : ∑ i, a x i ^ 2 = 1 := by rw [← haa x]; simp only [dotProduct, sq]
        have e2 : ∑ i, b y i ^ 2 = 1 := by rw [← hbb y]; simp only [dotProduct, sq]
        rw [e1, e2, mul_one] at h1
        exact h1
      have e : (s * w) ^ 2 = w ^ 2 := by linear_combination w ^ 2 * hs2
      have e' : (s * M x y) * (s * w) = M x y * w := by linear_combination M x y * w * hs2
      have hsw1 : s * w ≤ 1 := by nlinarith
      nlinarith [hμ x y, mul_le_mul_of_nonneg_left hsw1 (mul_nonneg hμ0.le hsw.le),
        mul_le_mul_of_nonneg_right (hμ x y) hsw.le]
    have hcore := card_mul_le_of_unit_vectors (K := X) M hspec a b haa hbb hMab hμ0.le hc hlam
    rw [mul_one_div, ← mul_div_assoc, div_le_iff₀ hR0] at hcore
    linarith
  -- Let `ε → 0`.
  set K := lam * √(Fintype.card X : ℝ) * √(Fintype.card Y : ℝ) with hK
  have hK0 : 0 ≤ K := by positivity
  have hlim : (Fintype.card Y : ℝ) * μ ≤ (signRank f : ℝ) / Fintype.card X * K := by
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have h0 := key (ε / (K + 1)) (by positivity)
    have h1 : ε / (K + 1) * K ≤ ε := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
      nlinarith
    nlinarith [h0, h1]
  rw [Real.sqrt_mul hm.le]
  set P := √(Fintype.card X : ℝ) * √(Fintype.card Y : ℝ) with hP
  have hP0 : 0 < P := mul_pos hm' hn'
  have hPP : P * P = Fintype.card X * Fintype.card Y := by
    rw [hP, mul_mul_mul_comm, Real.mul_self_sqrt hm.le, Real.mul_self_sqrt hn.le]
  have hm0 := hm.ne'
  have h3 : P * (P * μ) ≤ P * (lam * signRank f) := by
    calc P * (P * μ) = Fintype.card X * (Fintype.card Y * μ) := by
          rw [← mul_assoc, hPP, mul_assoc]
      _ ≤ Fintype.card X * ((signRank f : ℝ) / Fintype.card X * K) :=
          mul_le_mul_of_nonneg_left hlim hm.le
      _ = P * (lam * signRank f) := by
          rw [hK, mul_assoc lam, ← hP]
          field_simp
  have := le_of_mul_le_mul_left h3 hP0
  linarith

open scoped Matrix.Norms.L2Operator in
/-- The bilinear form of a matrix is bounded by its spectral norm:
`|∑ₓᵧ pₓ Mₓᵧ qᵧ| ≤ ‖M‖ ‖p‖₂ ‖q‖₂`. -/
private theorem abs_sum_mul_le_l2_opNorm [DecidableEq Y] (M : Matrix X Y ℝ) (p : X → ℝ)
    (q : Y → ℝ) :
    |∑ x, ∑ y, p x * M x y * q y| ≤ ‖M‖ * √(∑ x, p x ^ 2) * √(∑ y, q y ^ 2) := by
  have h1 : ∑ x, ∑ y, p x * M x y * q y = p ⬝ᵥ (M *ᵥ q) := by
    simp only [dotProduct, mulVec, mul_sum, mul_assoc]
  rw [h1]
  have hcs : |p ⬝ᵥ (M *ᵥ q)| ≤ √(∑ x, p x ^ 2) * √(∑ x, (M *ᵥ q) x ^ 2) := by
    rw [← Real.sqrt_mul (sum_nonneg fun x _ => sq_nonneg _)]
    exact Real.abs_le_sqrt (sum_mul_sq_le_sq_mul_sq _ _ _)
  have hop := Matrix.l2_opNorm_mulVec M (WithLp.toLp 2 q)
  simp only [EuclideanSpace.norm_eq, Real.norm_eq_abs, sq_abs] at hop
  calc _ ≤ _ := hcs
    _ ≤ √(∑ x, p x ^ 2) * (‖M‖ * √(∑ y, q y ^ 2)) :=
        mul_le_mul_of_nonneg_left (by simpa using hop) (Real.sqrt_nonneg _)
    _ = _ := by ring

open scoped Matrix.Norms.L2Operator in
/-- **Forster's bound for matrices without zero entries** [Sherstov and Wu, Theorem A.2]
[SherstovWu2019]: if `μ ≤ (-1)^{f x y} M x y` for all `x, y`, then
`μ √(|X| |Y|) ≤ ‖M‖ · signRank f`, where `‖M‖` is the spectral norm. For `M` without zero entries
and `f` its sign pattern, `μ = minₓᵧ |Mₓᵧ|`. -/
theorem mul_sqrt_card_mul_card_le_l2_opNorm_mul_signRank [DecidableEq Y] (f : X → Y → Bool)
    (M : Matrix X Y ℝ) {μ : ℝ} (hμ : ∀ x y, μ ≤ signMatrix ℝ f x y * M x y) :
    μ * √(Fintype.card X * Fintype.card Y) ≤ ‖M‖ * signRank f :=
  mul_sqrt_card_mul_card_le_mul_signRank f M hμ (abs_sum_mul_le_l2_opNorm M)

open scoped Matrix.Norms.L2Operator in
/-- **Forster's theorem** [Forster, 2002][Forster2002]: the sign-rank of an `X × Y` sign matrix is
at least `√(|X| |Y|) / ‖S‖`, where `‖S‖` is its spectral norm. -/
theorem sqrt_card_mul_card_le_l2_opNorm_mul_signRank [DecidableEq Y] (f : X → Y → Bool) :
    √(Fintype.card X * Fintype.card Y) ≤ ‖signMatrix ℝ f‖ * signRank f := by
  simpa using mul_sqrt_card_mul_card_le_l2_opNorm_mul_signRank f (signMatrix ℝ f) (μ := 1)
    fun x y => by rw [signMatrix_apply]; split_ifs <;> norm_num

/-- A real Hadamard matrix `H` (`Hᵀ H = N • 1`) scales Euclidean norms by `√N`. -/
private theorem sum_mulVec_sq_of_isHadamard [DecidableEq X] {H : Matrix X X ℝ}
    (hH : H.IsHadamard) (q : X → ℝ) :
    ∑ x, (H *ᵥ q) x ^ 2 = Fintype.card X * ∑ x, q x ^ 2 := by
  have h1 : ∑ x, (H *ᵥ q) x ^ 2 = (H *ᵥ q) ⬝ᵥ (H *ᵥ q) := by
    simp only [dotProduct, sq]
  have h2 : ∑ x, q x ^ 2 = q ⬝ᵥ q := by simp only [dotProduct, sq]
  have hHH : Hᵀ * H = (Fintype.card X : ℝ) • 1 := by
    have := hH.conjTranspose_mul
    rwa [conjTranspose_eq_transpose_of_trivial] at this
  rw [h1, h2, dotProduct_mulVec, ← mulVec_transpose, mulVec_mulVec, hHH, smul_mulVec,
    one_mulVec, smul_dotProduct, smul_eq_mul]

/-- **Forster's bound for Hadamard matrices** [Forster, 2002][Forster2002]: if the sign matrix of
`f : X → X → Bool` is a Hadamard matrix, then `signRank f ≥ √|X|`, i.e.
`|X| ≤ signRank f ^ 2`. Its spectral norm is `√|X|`. -/
theorem card_le_signRank_sq_of_isHadamard [DecidableEq X] {f : X → X → Bool}
    (hf : (signMatrix ℝ f).IsHadamard) : Fintype.card X ≤ signRank f ^ 2 := by
  set H := signMatrix ℝ f
  have hN : (0 : ℝ) ≤ Fintype.card X := Nat.cast_nonneg _
  have h := mul_sqrt_card_mul_card_le_mul_signRank f H (μ := 1) (lam := √(Fintype.card X))
    (fun x y => by simp only [H, signMatrix_apply]; split_ifs <;> norm_num)
    fun p q => by
      have h1 : ∑ x, ∑ y, p x * H x y * q y = p ⬝ᵥ (H *ᵥ q) := by
        simp only [dotProduct, mulVec, mul_sum, mul_assoc]
      rw [h1]
      have hcs : |p ⬝ᵥ (H *ᵥ q)| ≤ √(∑ x, p x ^ 2) * √(∑ x, (H *ᵥ q) x ^ 2) := by
        rw [← Real.sqrt_mul (sum_nonneg fun x _ => sq_nonneg _)]
        exact Real.abs_le_sqrt (sum_mul_sq_le_sq_mul_sq _ _ _)
      rw [sum_mulVec_sq_of_isHadamard hf, Real.sqrt_mul hN] at hcs
      linarith
  rw [one_mul, Real.sqrt_mul hN, Real.mul_self_sqrt hN] at h
  have hs := Real.mul_self_sqrt hN
  have hs0 := Real.sqrt_nonneg (Fintype.card X : ℝ)
  have hd := Nat.cast_nonneg (α := ℝ) (signRank f)
  have : (Fintype.card X : ℝ) ≤ (signRank f : ℝ) ^ 2 := by
    nlinarith [sq_nonneg (√(Fintype.card X : ℝ) - signRank f)]
  exact_mod_cast this

/-- **Forster's bound for the inner product** [Forster, 2002][Forster2002]: the inner product on
`n` bits, whose sign matrix is the `2ⁿ × 2ⁿ` Sylvester–Hadamard matrix
(`isHadamard_signMatrix_dotProduct`), has sign-rank at least `2^{n/2}`. -/
theorem two_pow_card_le_signRank_dotProduct_sq {ι : Type*} [Fintype ι] [DecidableEq ι] :
    2 ^ Fintype.card ι ≤ signRank (fun x y : ι → Bool => x ⬝ᵥ y) ^ 2 := by
  simpa using card_le_signRank_sq_of_isHadamard (isHadamard_signMatrix_dotProduct ℝ (ι := ι))

/-- **Unbounded-error complexity of the inner product**: computing the inner product on `n` bits
with unbounded error needs at least `⌈n / 2⌉` bits of communication, by Forster's bound and the
Paturi–Simon lower bound [Forster, 2002][Forster2002]. -/
theorem PrivateCoin.card_add_one_div_two_le_uppComplexityFun_dotProduct {ι : Type*} [Fintype ι] :
    (((Fintype.card ι + 1) / 2 : ℕ) : ℕ∞) ≤
      PrivateCoin.uppComplexityFun (fun x y : ι → Bool => x ⬝ᵥ y) := by
  classical
  refine le_trans ?_ (PrivateCoin.clog_signRank_le_uppComplexityFun _)
  have h1 := two_pow_card_le_signRank_dotProduct_sq (ι := ι)
  have h2 := Nat.le_pow_clog one_lt_two (signRank fun x y : ι → Bool => x ⬝ᵥ y)
  have h3 : 2 ^ Fintype.card ι ≤
      2 ^ (2 * Nat.clog 2 (signRank fun x y : ι → Bool => x ⬝ᵥ y)) := by
    rw [pow_mul']
    exact h1.trans (Nat.pow_le_pow_left h2 2)
  have h4 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 h3
  exact_mod_cast (by omega : (Fintype.card ι + 1) / 2 ≤ Nat.clog 2 _)

end Cslib.Communication

end
