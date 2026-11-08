/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Quantum.Bipartite
public import Mathlib.Analysis.InnerProductSpace.TensorProduct
public import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.LinearAlgebra.Dimension.RankNullity

/-!
# The no-cloning theorem

No physical process copies an unknown pure quantum state [Wootters, Zurek][WoottersZurek1982],
[Dieks][Dieks1982]; [de Wolf][deWolf2019], Chapter 1, Exercise 12. Formally, for pure states
in a Hilbert space `E` and a fixed blank state `e`:

* **Inner-product dichotomy.** If an isometry (in particular a unitary) `U` of `E ⊗ E` copies two
  unit states, `U(ψ ⊗ e) = ψ ⊗ ψ` and `U(φ ⊗ e) = φ ⊗ φ`, then `⟪ψ, φ⟫ = ⟪ψ, φ⟫²` because `U`
  preserves inner products, so `ψ` and `φ` are orthogonal or equal
  (`Cslib.Quantum.inner_eq_zero_or_eq_of_clone`). Copying is possible only for a set of mutually
  orthogonal states, such as a computational basis.
* **No linear cloner.** If `dim E ≥ 2`, no linear map `L` of `E ⊗ E` copies every unit state, even
  up to a nonzero factor: `L(ψ ⊗ e) = c_ψ (ψ ⊗ ψ)` with `c_ψ ≠ 0` fails for some unit `ψ`
  (`Cslib.Quantum.not_exists_linearMap_clone_smul`). For orthonormal `u, v` and
  `w = (u + v)/√2`, linearity makes `L(w ⊗ e)` a combination of `u ⊗ u` and `v ⊗ v`, orthogonal
  to `u ⊗ v`, while `c_w (w ⊗ w)` has component `c_w/2 ≠ 0` along `u ⊗ v`.

Both are stated for Mathlib's tensor product `E ⊗[ℂ] E` of inner product spaces and in
coordinates, for matrices acting on product states `ψ ⊗ φ ∈ ℂ^{ι × ι}`
(`Cslib.Quantum.prodState`). The coordinate impossibility needs no unitarity: it holds for every
matrix, in particular every unitary. All statements are about pure states; no-cloning for mixed
states (no-broadcasting) is not formalized here.

## Main results

* `Cslib.Quantum.inner_eq_zero_or_eq_of_clone`: an isometry of `E ⊗ E` copying two unit states
  forces them to be orthogonal or equal.
* `Cslib.Quantum.not_exists_linearMap_clone_smul`, `Cslib.Quantum.not_exists_linearMap_clone`: no
  linear map of `E ⊗ E` copies every unit state (up to a nonzero factor), if `dim E ≥ 2`.
* `Cslib.Quantum.inner_eq_zero_or_eq_of_unitary_clone`: the dichotomy for unitary matrices on
  `ℂ^{ι × ι}`.
* `Cslib.Quantum.not_exists_matrix_clone_smul`, `Cslib.Quantum.not_exists_matrix_clone`: no
  matrix on `ℂ^{ι × ι}` copies every unit state of `ℂ^ι` (up to a nonzero factor), if `|ι| ≥ 2`.

## References

* [W. K. Wootters, W. H. Zurek, *A single quantum cannot be cloned*][WoottersZurek1982]
* [D. Dieks, *Communication by EPR devices*][Dieks1982]
* [R. de Wolf, *Quantum Computing: Lecture Notes*][deWolf2019]
-/

public section

namespace Cslib.Quantum

open Matrix
open scoped TensorProduct InnerProductSpace

/-! ### The argument, for any multiplicative pairing -/

section Core

variable {E G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G]

private theorem inner_self_eq_one {x : E} (hx : ‖x‖ = 1) : ⟪x, x⟫_ℂ = 1 := by
  rw [inner_self_eq_norm_sq_to_K, hx]; simp

/-- The no-cloning dichotomy for a pairing `T` with `⟪T x y, T x' y'⟫ = ⟪x, x'⟫ ⟪y, y'⟫`. -/
private theorem inner_eq_zero_or_eq_of_clone_core (T : E → E → G)
    (hT : ∀ x y x' y', ⟪T x y, T x' y'⟫_ℂ = ⟪x, x'⟫_ℂ * ⟪y, y'⟫_ℂ)
    (U : G →ₗᵢ[ℂ] G) {ψ φ e : E} (hψ₁ : ‖ψ‖ = 1) (hφ₁ : ‖φ‖ = 1) (he : ‖e‖ = 1)
    (hψ : U (T ψ e) = T ψ ψ) (hφ : U (T φ e) = T φ φ) : ⟪ψ, φ⟫_ℂ = 0 ∨ ψ = φ := by
  have h := U.inner_map_map (T ψ e) (T φ e)
  rw [hψ, hφ, hT, hT, inner_self_eq_one he, mul_one] at h
  rcases eq_zero_or_one_of_sq_eq_self (by rw [sq]; exact h : ⟪ψ, φ⟫_ℂ ^ 2 = ⟪ψ, φ⟫_ℂ) with h0 | h1
  · exact Or.inl h0
  · exact Or.inr ((inner_eq_one_iff_of_norm_eq_one hψ₁ hφ₁).mp h1)

/-- No linear cloning, up to nonzero factors, for a pairing `T` that is multiplicative and
linear in its first argument, in the presence of an orthonormal pair `u, v`. -/
private theorem not_clone_core (T : E → E → G)
    (hT : ∀ x y x' y', ⟪T x y, T x' y'⟫_ℂ = ⟪x, x'⟫_ℂ * ⟪y, y'⟫_ℂ)
    (hadd : ∀ x x' y, T (x + x') y = T x y + T x' y)
    (hsmul : ∀ (c : ℂ) x y, T (c • x) y = c • T x y)
    {u v : E} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : ⟪u, v⟫_ℂ = 0)
    (e : E) (L : G →ₗ[ℂ] G) (c : E → ℂ) (hc : ∀ ψ, ‖ψ‖ = 1 → c ψ ≠ 0)
    (hL : ∀ ψ, ‖ψ‖ = 1 → L (T ψ e) = c ψ • T ψ ψ) : False := by
  have hvu : ⟪v, u⟫_ℂ = 0 := inner_eq_zero_symm.mp huv
  have huu := inner_self_eq_one hu
  have hvv := inner_self_eq_one hv
  set s : ℂ := (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) with hs_def
  have hs : starRingEnd ℂ s * s = 1 / 2 := by
    rw [hs_def, Complex.conj_ofReal, ← Complex.ofReal_mul, ← mul_inv,
      Real.mul_self_sqrt (by norm_num)]
    norm_num
  have hs0 : s ≠ 0 := by
    rw [hs_def]; exact_mod_cast inv_ne_zero (Real.sqrt_ne_zero'.mpr (by norm_num))
  have hw : ‖s • u + s • v‖ = 1 := by
    have h2 : ⟪s • u + s • v, s • u + s • v⟫_ℂ = 1 := by
      simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, huu, hvv,
        huv, hvu]
      linear_combination 2 * hs
    have h2' : ‖s • u + s • v‖ ^ 2 = 1 ^ 2 := by
      rw [norm_sq_eq_re_inner (𝕜 := ℂ), h2]; simp
    exact (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp h2'
  have h1 := hL _ hw
  rw [hadd, hsmul, hsmul, map_add, map_smul, map_smul, hL u hu, hL v hv] at h1
  have key := congrArg (fun z => ⟪T u v, z⟫_ℂ) h1
  simp only [inner_add_right, inner_smul_right, hT, huu, hvv, huv, hvu] at key
  have : c (s • u + s • v) * (s * s) = 0 := by linear_combination -key
  rcases mul_eq_zero.mp this with h | h
  · exact hc _ hw h
  · exact hs0 (mul_self_eq_zero.mp h)

private theorem exists_orthonormal_pair (h : 1 < Module.rank ℂ E) :
    ∃ u v : E, ‖u‖ = 1 ∧ ‖v‖ = 1 ∧ ⟪u, v⟫_ℂ = 0 := by
  obtain ⟨x, hx⟩ := rank_pos_iff_exists_ne_zero.mp (zero_lt_one.trans h)
  obtain ⟨y, hxy⟩ := exists_linearIndependent_pair_of_one_lt_rank h hx
  have ho := InnerProductSpace.gramSchmidtNormed_orthonormal hxy
  exact ⟨_, _, ho.1 0, ho.1 1, ho.2 (by decide : (0 : Fin 2) ≠ 1)⟩

end Core

/-! ### Tensor products of inner product spaces -/

section TensorProduct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- **No-cloning, inner-product form** [Wootters, Zurek][WoottersZurek1982],
[Dieks][Dieks1982]: if an isometry `U` of `E ⊗ E` (in particular a unitary) copies two unit
states `ψ` and `φ` onto a unit blank state `e`, then `ψ` and `φ` are orthogonal or equal. -/
theorem inner_eq_zero_or_eq_of_clone (U : E ⊗[ℂ] E →ₗᵢ[ℂ] E ⊗[ℂ] E) {ψ φ e : E}
    (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1) (he : ‖e‖ = 1)
    (hUψ : U (ψ ⊗ₜ e) = ψ ⊗ₜ ψ) (hUφ : U (φ ⊗ₜ e) = φ ⊗ₜ φ) : ⟪ψ, φ⟫_ℂ = 0 ∨ ψ = φ :=
  inner_eq_zero_or_eq_of_clone_core (fun x y => x ⊗ₜ[ℂ] y)
    (fun _ _ _ _ => TensorProduct.inner_tmul ℂ _ _ _ _) U hψ hφ he hUψ hUφ

/-- **No-cloning** [Wootters, Zurek][WoottersZurek1982], [Dieks][Dieks1982], up to nonzero
factors: if `dim E ≥ 2`, no linear map `L` of `E ⊗ E` maps `ψ ⊗ e` to a nonzero multiple of
`ψ ⊗ ψ` for every unit state `ψ`, whatever the blank state `e`. -/
theorem not_exists_linearMap_clone_smul (h : 1 < Module.rank ℂ E) (e : E) :
    ¬ ∃ (L : E ⊗[ℂ] E →ₗ[ℂ] E ⊗[ℂ] E) (c : E → ℂ),
      ∀ ψ : E, ‖ψ‖ = 1 → c ψ ≠ 0 ∧ L (ψ ⊗ₜ e) = c ψ • ψ ⊗ₜ ψ := by
  rintro ⟨L, c, hL⟩
  obtain ⟨u, v, hu, hv, huv⟩ := exists_orthonormal_pair h
  exact not_clone_core (fun x y => x ⊗ₜ[ℂ] y) (fun _ _ _ _ => TensorProduct.inner_tmul ℂ _ _ _ _)
    (fun _ _ _ => TensorProduct.add_tmul _ _ _)
    (fun c x y => (TensorProduct.smul_tmul' c x y).symm)
    hu hv huv e L c (fun ψ hψ => (hL ψ hψ).1) (fun ψ hψ => (hL ψ hψ).2)

/-- **No-cloning** [Wootters, Zurek][WoottersZurek1982], [Dieks][Dieks1982]: if `dim E ≥ 2`, no
linear map of `E ⊗ E` (in particular no unitary) maps `ψ ⊗ e` to `ψ ⊗ ψ` for every unit state
`ψ`. -/
theorem not_exists_linearMap_clone (h : 1 < Module.rank ℂ E) (e : E) :
    ¬ ∃ L : E ⊗[ℂ] E →ₗ[ℂ] E ⊗[ℂ] E, ∀ ψ : E, ‖ψ‖ = 1 → L (ψ ⊗ₜ e) = ψ ⊗ₜ ψ := by
  rintro ⟨L, hL⟩
  exact not_exists_linearMap_clone_smul h e
    ⟨L, fun _ => 1, fun ψ hψ => ⟨one_ne_zero, by rw [one_smul, hL ψ hψ]⟩⟩

end TensorProduct

/-! ### Coordinates -/

section Coordinates

variable {ι : Type*} [Fintype ι]

/-- **No-cloning, inner-product form**, for a unitary matrix `U` on `ℂ^{ι × ι}`: if `U` copies two
unit states `ψ` and `φ` of `ℂ^ι` onto a unit blank state `e`, then `ψ` and `φ` are orthogonal
or equal. -/
theorem inner_eq_zero_or_eq_of_unitary_clone [DecidableEq ι] {U : Matrix (ι × ι) (ι × ι) ℂ}
    (hU : U ∈ unitaryGroup (ι × ι) ℂ) {ψ φ e : EuclideanSpace ℂ ι}
    (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1) (he : ‖e‖ = 1)
    (hUψ : U *ᵥ (prodState ψ e).ofLp = (prodState ψ ψ).ofLp)
    (hUφ : U *ᵥ (prodState φ e).ofLp = (prodState φ φ).ofLp) : ⟪ψ, φ⟫_ℂ = 0 ∨ ψ = φ := by
  let V : EuclideanSpace ℂ (ι × ι) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (ι × ι) :=
    Unitary.linearIsometryEquiv ⟨toEuclideanCLM (n := ι × ι) (𝕜 := ℂ) U, Unitary.map_mem _ hU⟩
  have hV (x : EuclideanSpace ℂ (ι × ι)) : (V x).ofLp = U *ᵥ x.ofLp := rfl
  exact inner_eq_zero_or_eq_of_clone_core prodState (fun x y x' y' => inner_prodState x x' y y')
    V.toLinearIsometry hψ hφ he (WithLp.ofLp_injective 2 ((hV _).trans hUψ))
    (WithLp.ofLp_injective 2 ((hV _).trans hUφ))

/-- **No-cloning** in coordinates, up to nonzero factors: if `|ι| ≥ 2`, no matrix `U` on
`ℂ^{ι × ι}` maps `ψ ⊗ e` to a nonzero multiple of `ψ ⊗ ψ` for every unit state `ψ` of `ℂ^ι`,
whatever the blank state `e`. -/
theorem not_exists_matrix_clone_smul [Nontrivial ι] (e : EuclideanSpace ℂ ι) :
    ¬ ∃ (U : Matrix (ι × ι) (ι × ι) ℂ) (c : EuclideanSpace ℂ ι → ℂ),
      ∀ ψ : EuclideanSpace ℂ ι, ‖ψ‖ = 1 →
        c ψ ≠ 0 ∧ U *ᵥ (prodState ψ e).ofLp = c ψ • (prodState ψ ψ).ofLp := by
  classical
  rintro ⟨U, c, hU⟩
  obtain ⟨i, j, hij⟩ := exists_pair_ne ι
  obtain ⟨L, hL⟩ : ∃ L : EuclideanSpace ℂ (ι × ι) →ₗ[ℂ] EuclideanSpace ℂ (ι × ι),
      ∀ x, (L x).ofLp = U *ᵥ x.ofLp := ⟨Matrix.toEuclideanLin U, fun _ => rfl⟩
  have hL' (ψ : EuclideanSpace ℂ ι) (hψ : ‖ψ‖ = 1) : L (prodState ψ e) = c ψ • prodState ψ ψ := by
    apply WithLp.ofLp_injective 2
    rw [hL, WithLp.ofLp_smul, (hU ψ hψ).2]
  have hij' : ⟪ket i, ket j⟫_ℂ = 0 := by
    rw [ket, EuclideanSpace.inner_single_left]
    simp [hij]
  -- The linearity of `prodState` is restated at the `EuclideanSpace` instances; passing
  -- `prodState_add_left` directly makes the elaborator unify the `PiLp` and `WithLp` additions.
  exact not_clone_core prodState (fun x y x' y' => inner_prodState x x' y y')
    (fun x x' y => by ext p; simp [add_mul]) (fun a x y => by ext p; simp [mul_assoc])
    (norm_ket i) (norm_ket j) hij' e L c (fun ψ hψ => (hU ψ hψ).1) hL'

/-- **No-cloning** in coordinates [Wootters, Zurek][WoottersZurek1982], [Dieks][Dieks1982];
[de Wolf][deWolf2019], Chapter 1, Exercise 12: if `|ι| ≥ 2`, no matrix (in particular no unitary)
`U` on `ℂ^{ι × ι}` maps `ψ ⊗ e` to `ψ ⊗ ψ` for every unit state `ψ` of `ℂ^ι`. -/
theorem not_exists_matrix_clone [Nontrivial ι] (e : EuclideanSpace ℂ ι) :
    ¬ ∃ U : Matrix (ι × ι) (ι × ι) ℂ, ∀ ψ : EuclideanSpace ℂ ι, ‖ψ‖ = 1 →
      U *ᵥ (prodState ψ e).ofLp = (prodState ψ ψ).ofLp := by
  rintro ⟨U, hU⟩
  exact not_exists_matrix_clone_smul e
    ⟨U, fun _ => 1, fun ψ hψ => ⟨one_ne_zero, by rw [one_smul, hU ψ hψ]⟩⟩

end Coordinates

end Cslib.Quantum
