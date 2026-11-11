/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Analysis/InnerProductSpace/Spectrum.lean`)

public import CslibFrontier.Init
public import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Spectrum

/-!
# Spectral decomposition of finite-dimensional complex unitaries

Any linear isometry equivalence `R : E ≃ₗᵢ[ℂ] E` on a finite-dimensional complex inner product
space admits an orthonormal basis of eigenvectors with unit-modulus eigenvalues `μ k + I * ν k`
(`LinearIsometryEquiv.exists_orthonormalBasis_eigenvectors`), constructed by simultaneously
diagonalizing its commuting Hermitian part `(R + R⁻¹) / 2` and skew-Hermitian part
`-I (R - R⁻¹) / 2`.

## Main results

* `LinearIsometryEquiv.exists_orthonormalBasis_eigenvectors`: unitary diagonalization on
  finite-dimensional complex inner product spaces.
-/

public section

namespace LinearIsometryEquiv

/-- Any unitary on a finite-dimensional complex inner product space has an orthonormal basis of
eigenvectors with unit-modulus eigenvalues `μ k + I * ν k`. -/
theorem exists_orthonormalBasis_eigenvectors
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (R : E ≃ₗᵢ[ℂ] E) :
    ∃ (b : OrthonormalBasis (Fin (Module.finrank ℂ E)) ℂ E)
      (μ ν : Fin (Module.finrank ℂ E) → ℝ),
      (∀ k, (μ k) ^ 2 + (ν k) ^ 2 = 1) ∧
      (∀ k, R (b k) = ((μ k : ℂ) + Complex.I * (ν k : ℂ)) • b k) := by
  let U : E →ₗ[ℂ] E := R.toLinearMap
  let Um : E →ₗ[ℂ] E := R.symm.toLinearMap
  have hU : ∀ x, U x = R x := fun _ => rfl
  have hUm : ∀ x, Um x = R.symm x := fun _ => rfl
  let H : E →ₗ[ℂ] E := (1 / 2 : ℂ) • (U + Um)
  let K : E →ₗ[ℂ] E := (-Complex.I / 2 : ℂ) • (U - Um)
  have hRsa : ∀ x y : E, inner ℂ (R x) y = inner ℂ x (R.symm y) := fun x y => by
    calc
      inner ℂ (R x) y = inner ℂ (R x) (R (R.symm y)) := by rw [R.apply_symm_apply]
      _ = inner ℂ x (R.symm y) := R.inner_map_map x (R.symm y)
  have hRmsa : ∀ x y : E, inner ℂ (R.symm x) y = inner ℂ x (R y) := fun x y => by
    calc
      inner ℂ (R.symm x) y = inner ℂ (R (R.symm x)) (R y) := (R.inner_map_map _ _).symm
      _ = inner ℂ x (R y) := by rw [R.apply_symm_apply]
  have hHsym : H.IsSymmetric := fun x y => by
    simp only [H, LinearMap.smul_apply, LinearMap.add_apply, hU, hUm,
      inner_smul_left, inner_smul_right, inner_add_left, inner_add_right, hRsa, hRmsa]
    simp only [starRingEnd_apply, star_div₀, star_one, star_ofNat]
    ring
  have hKsym : K.IsSymmetric := fun x y => by
    calc
      inner ℂ (K x) y
          = (Complex.I / 2) * (inner ℂ (R x) y - inner ℂ (R.symm x) y) := by
            simp only [K, LinearMap.smul_apply, LinearMap.sub_apply, hU, hUm, inner_smul_left,
              inner_sub_left]
            have hstar : starRingEnd ℂ (-Complex.I / 2) = Complex.I / 2 := by
              simp only [map_div₀, map_neg, Complex.conj_I, map_ofNat, neg_neg]
            rw [hstar]
      _ = (Complex.I / 2) * (inner ℂ x (R.symm y) - inner ℂ x (R y)) := by rw [hRsa, hRmsa]
      _ = inner ℂ x (K y) := by
            simp only [K, LinearMap.smul_apply, LinearMap.sub_apply, hU, hUm, inner_smul_right,
              inner_sub_right]
            ring
  have hHK : ∀ x, H (K x) = K (H x) := fun x => by
    simp only [H, K, LinearMap.smul_apply, LinearMap.add_apply, LinearMap.sub_apply,
      map_smul, map_add, map_sub, hU, hUm, R.apply_symm_apply, R.symm_apply_apply]
    module
  have hR_decomp : ∀ x, R x = H x + Complex.I • K x := fun x => by
    simp only [H, K, LinearMap.smul_apply, LinearMap.add_apply, LinearMap.sub_apply, hU, hUm]
    rw [smul_smul]
    have hI : Complex.I * (-Complex.I / 2) = 1 / 2 := by
      rw [mul_div_assoc', mul_neg, Complex.I_mul_I]
      ring
    rw [hI, ← smul_add]
    have hsum : (R x + R.symm x) + (R x - R.symm x) = (2 : ℂ) • R x := by module
    rw [hsum, smul_smul]
    norm_num
  have hind : ∀ n : ℕ, ∀ (W : Submodule ℂ E),
      (∀ x ∈ W, H x ∈ W) → (∀ x ∈ W, K x ∈ W) → Module.finrank ℂ W = n →
      ∃ (v : Fin n → E) (μ ν : Fin n → ℝ),
        Orthonormal ℂ v ∧ (∀ k, v k ∈ W) ∧ (∀ k, H (v k) = (μ k : ℂ) • v k) ∧
          (∀ k, K (v k) = (ν k : ℂ) • v k) := by
    intro n
    induction n with
    | zero =>
      intro W _ _ _
      exact ⟨Fin.elim0, Fin.elim0, Fin.elim0, orthonormal_iff_ite.mpr fun i => Fin.elim0 i,
        fun i => Fin.elim0 i, fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
    | succ n ih =>
      intro W hHW hKW hdim
      let H_W : W →ₗ[ℂ] W := H.restrict hHW
      let K_W : W →ₗ[ℂ] W := K.restrict hKW
      have hH_W : H_W.IsSymmetric := hHsym.restrict_invariant hHW
      have hK_W : K_W.IsSymmetric := hKsym.restrict_invariant hKW
      let μ₀ : ℝ := hH_W.eigenvalues hdim ⟨0, Nat.zero_lt_succ n⟩
      have heig : Module.End.HasEigenvalue H_W (μ₀ : ℂ) :=
        hH_W.hasEigenvalue_eigenvalues hdim ⟨0, Nat.zero_lt_succ n⟩
      let S : Submodule ℂ W := Module.End.eigenspace H_W (μ₀ : ℂ)
      have hS_ne : S ≠ ⊥ := Module.End.hasEigenvalue_iff.mp heig
      have hS_pos : 0 < Module.finrank ℂ S :=
        Nat.pos_of_ne_zero fun h0 => hS_ne (Submodule.finrank_eq_zero.mp h0)
      have hKS : ∀ x ∈ S, K_W x ∈ S := by
        intro x hx
        rw [Module.End.mem_eigenspace_iff] at hx ⊢
        apply Subtype.ext
        have h1 : H (K (x : E)) = K (H (x : E)) := hHK (x : E)
        have h2 : H (x : E) = (μ₀ : ℂ) • (x : E) := congrArg Subtype.val hx
        change H (K (x : E)) = (μ₀ : ℂ) • K (x : E)
        rw [h1, h2, K.map_smul]
      let K_S : S →ₗ[ℂ] S := K_W.restrict hKS
      have hK_S := hK_W.restrict_invariant hKS
      let ν₀ : ℝ := hK_S.eigenvalues rfl ⟨0, hS_pos⟩
      let u₀ : S := hK_S.eigenvectorBasis rfl ⟨0, hS_pos⟩
      have hu₀_norm : ‖u₀‖ = 1 := (hK_S.eigenvectorBasis rfl).orthonormal.1 ⟨0, hS_pos⟩
      have hu₀_eig : K_S u₀ = (ν₀ : ℂ) • u₀ :=
        Module.End.mem_eigenspace_iff.mp (hK_S.hasEigenvector_eigenvectorBasis rfl ⟨0, hS_pos⟩).1
      let w₀ : W := (u₀ : W)
      let v₀ : E := (w₀ : E)
      have hv₀W : v₀ ∈ W := w₀.2
      have hv₀_norm : ‖v₀‖ = 1 := hu₀_norm
      have hv₀H : H v₀ = (μ₀ : ℂ) • v₀ := by
        have hw₀S : w₀ ∈ S := u₀.2
        rw [Module.End.mem_eigenspace_iff] at hw₀S
        exact congrArg Subtype.val hw₀S
      have hv₀K : K v₀ = (ν₀ : ℂ) • v₀ := by
        have h1 : K_W w₀ = (ν₀ : ℂ) • w₀ := congrArg Subtype.val hu₀_eig
        exact congrArg Subtype.val h1
      let L : Submodule ℂ W := Submodule.span ℂ ({w₀} : Set W)
      let L_orth : Submodule ℂ W := Lᗮ
      let W' : Submodule ℂ E := L_orth.map W.subtype
      have hw₀_ne : w₀ ≠ 0 := by
        intro h
        have h0 : ‖w₀‖ = 0 := by rw [h, norm_zero]
        have h1 : (1 : ℝ) = 0 := by simpa [v₀] using hv₀_norm.symm.trans h0
        norm_num at h1
      have hL_dim : Module.finrank ℂ L = 1 := finrank_span_singleton hw₀_ne
      have hL_orth_dim : Module.finrank ℂ L_orth = n := by
        have hsum := Submodule.finrank_add_finrank_orthogonal L
        rw [hL_dim, hdim] at hsum
        dsimp [L_orth]
        omega
      have hW'_dim : Module.finrank ℂ W' = n := by
        rw [Submodule.finrank_map_subtype_eq]
        exact hL_orth_dim
      have hv₀_orth_W' : ∀ x ∈ W', inner ℂ v₀ x = 0 := by
        intro x hx
        obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
        exact hy w₀ (Submodule.subset_span (Set.mem_singleton w₀))
      have hW'_sub : W' ≤ W := by
        intro x hx
        obtain ⟨y, _, rfl⟩ := Submodule.mem_map.mp hx
        exact y.2
      have hW'_inv : ∀ (T : E →ₗ[ℂ] E), T.IsSymmetric → (∀ x ∈ W, T x ∈ W) →
          ∀ x ∈ W', (∃ c : ℂ, T v₀ = c • v₀) → T x ∈ W' := by
        intro T hTsym hTW x hx ⟨c, hc⟩
        obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
        refine Submodule.mem_map.mpr ⟨⟨T (y : E), hTW (y : E) y.2⟩, ?_, rfl⟩
        intro z hz
        obtain ⟨d, rfl⟩ := Submodule.mem_span_singleton.mp hz
        change inner ℂ (d • v₀) (T (y : E)) = 0
        rw [inner_smul_left, ← hTsym v₀ (y : E), hc, inner_smul_left,
          hv₀_orth_W' (y : E) (Submodule.mem_map.mpr ⟨y, hy, rfl⟩)]
        simp
      have hHW' : ∀ x ∈ W', H x ∈ W' :=
        fun x hx => hW'_inv H hHsym hHW x hx ⟨μ₀, hv₀H⟩
      have hKW' : ∀ x ∈ W', K x ∈ W' :=
        fun x hx => hW'_inv K hKsym hKW x hx ⟨ν₀, hv₀K⟩
      obtain ⟨v', μ', ν', hv'_ortho, hv'W', hv'H, hv'K⟩ := ih W' hHW' hKW' hW'_dim
      refine ⟨Fin.cons v₀ v', Fin.cons μ₀ μ', Fin.cons ν₀ ν', ?_, ?_, ?_, ?_⟩
      · rw [orthonormal_iff_ite]
        intro i j
        refine Fin.cases ?_ (fun i' => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j
        · simp [inner_self_eq_norm_sq_to_K, hv₀_norm]
        · simp [Fin.cons_zero, Fin.cons_succ, (Fin.succ_ne_zero j').symm,
            hv₀_orth_W' _ (hv'W' j')]
        · simp [Fin.cons_zero, Fin.cons_succ, Fin.succ_ne_zero,
            inner_eq_zero_symm.mp (hv₀_orth_W' _ (hv'W' i'))]
        · simp only [Fin.cons_succ, Fin.succ_inj]
          exact (orthonormal_iff_ite.mp hv'_ortho) i' j'
      · intro k
        refine Fin.cases hv₀W (fun k' => hW'_sub (hv'W' k')) k
      · intro k
        refine Fin.cases hv₀H (fun k' => hv'H k') k
      · intro k
        refine Fin.cases hv₀K (fun k' => hv'K k') k
  obtain ⟨v, μ, ν, hv_ortho, _, hvH, hvK⟩ :=
    hind (Module.finrank ℂ E) ⊤ (fun _ _ => trivial) (fun _ _ => trivial) (by simp)
  have hunit : ∀ k, (μ k) ^ 2 + (ν k) ^ 2 = 1 := by
    intro k
    have hRv : R (v k) = ((μ k : ℂ) + Complex.I * (ν k : ℂ)) • v k := by
      rw [hR_decomp, hvH k, hvK k, smul_smul, ← add_smul]
    have hnorm : ‖((μ k : ℂ) + Complex.I * (ν k : ℂ))‖ = 1 := by
      have h1 : ‖R (v k)‖ = 1 := by rw [R.norm_map, hv_ortho.1 k]
      rw [hRv, norm_smul, hv_ortho.1 k, mul_one] at h1
      exact h1
    have hsq : ‖((μ k : ℂ) + Complex.I * (ν k : ℂ))‖ ^ 2 = 1 := by rw [hnorm, one_pow]
    have hnsq : Complex.normSq ((μ k : ℂ) + Complex.I * (ν k : ℂ)) =
        (μ k) ^ 2 + (ν k) ^ 2 := by
      rw [Complex.normSq_apply]
      simp [Complex.add_re, Complex.add_im, Complex.I_re, Complex.I_im, sq]
    rw [Complex.sq_norm] at hsq
    linarith
  rcases Nat.eq_zero_or_pos (Module.finrank ℂ E) with hdim0 | hdimpos
  · let b0 : Module.Basis (Fin (Module.finrank ℂ E)) ℂ E :=
      Module.Basis.mk (v := v) hv_ortho.linearIndependent (fun x _ => by
        have hsub : Subsingleton E := Module.finrank_zero_iff.mp hdim0
        rw [Subsingleton.elim x 0]
        exact zero_mem _)
    refine ⟨b0.toOrthonormalBasis (by simpa [b0] using hv_ortho), μ, ν, hunit, fun k =>
      Fin.elim0 (hdim0 ▸ k)⟩
  · have : Nonempty (Fin (Module.finrank ℂ E)) := ⟨⟨0, hdimpos⟩⟩
    let b := basisOfOrthonormalOfCardEqFinrank hv_ortho (by simp)
    refine ⟨b.toOrthonormalBasis (by simpa [b] using hv_ortho), μ, ν, hunit, fun k => ?_⟩
    have hb : (b.toOrthonormalBasis (by simpa [b] using hv_ortho)) k = v k := by
      simp [b, coe_basisOfOrthonormalOfCardEqFinrank]
    rw [hb, hR_decomp, hvH k, hvK k, smul_smul, ← add_smul]

end LinearIsometryEquiv
