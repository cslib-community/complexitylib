/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

import CslibFrontier.Crypto.Computational.Lattice.ShortestVector

/-!
# Tests for successive minima and shortest-vector problems

Witnesses on the standard lattice `ℤ²` in `Fin 2 → ℝ` with the supremum norm: its first minimum
and first successive minimum are `1`, so the attainment, Minkowski and `GapSVP` statements have
satisfiable hypotheses. Its rank is `2`, and the standard basis `![e₀, e₁]` solves `SIVP_1`. A
single nonzero vector is a `3/4`-reduced family, so the reduced-basis `SVP` bound applies with
factor `(√2)⁰ = 1`.
-/

namespace CslibFrontierTests.Crypto.LatticeGeometry

open ZLattice Cslib.Crypto

/-- The standard lattice `ℤ²` in `ℝ²` with the supremum norm. -/
private noncomputable abbrev stdLattice : Submodule ℤ (Fin 2 → ℝ) :=
  Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin 2)))

private theorem single_mem : (Pi.single 0 1 : Fin 2 → ℝ) ∈ stdLattice :=
  Submodule.subset_span ⟨0, by simp⟩

private theorem single_ne_zero : (Pi.single 0 1 : Fin 2 → ℝ) ≠ 0 := by
  simp

private theorem norm_single : ‖(Pi.single 0 1 : Fin 2 → ℝ)‖ = 1 := by
  rw [Pi.norm_single, norm_one]

private theorem stdLattice_ne_bot : stdLattice ≠ ⊥ :=
  (Submodule.ne_bot_iff _).2 ⟨_, single_mem, single_ne_zero⟩

/-- Nonzero vectors of `ℤ²` have supremum norm at least `1`. -/
private theorem one_le_norm {v : Fin 2 → ℝ} (hv : v ∈ stdLattice) (hv0 : v ≠ 0) : 1 ≤ ‖v‖ := by
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hv0
  obtain ⟨k, hk⟩ := ((Pi.basisFun ℝ (Fin 2)).mem_span_iff_repr_mem ℤ v).1 hv i
  simp only [Pi.basisFun_repr, algebraMap_int_eq, eq_intCast] at hk
  have hk0 : k ≠ 0 := by rintro rfl; simp_all
  calc (1 : ℝ) ≤ |(k : ℝ)| := by exact_mod_cast Int.one_le_abs hk0
    _ = ‖v i‖ := by rw [hk, Real.norm_eq_abs]
    _ ≤ ‖v‖ := norm_le_pi_norm v i

/-- The first minimum of `ℤ²` is `1`. -/
theorem minimum_stdLattice : minimum stdLattice = 1 :=
  le_antisymm (norm_single ▸ minimum_le_norm single_mem single_ne_zero)
    ((le_minimum_iff stdLattice_ne_bot).2 fun _ => one_le_norm)

example : successiveMinimum stdLattice 1 = 1 := by
  rw [successiveMinimum_one stdLattice stdLattice_ne_bot, minimum_stdLattice]

example : minimum stdLattice ≤ successiveMinimum stdLattice 2 :=
  minimum_le_successiveMinimum stdLattice stdLattice_ne_bot (by norm_num) (by simp)

example : 0 < minimum stdLattice := minimum_pos stdLattice_ne_bot

/-- Minkowski's bound in the supremum norm forces `det(ℤ²)^{1/2} ≥ 1`. -/
example : 1 ≤ covolume stdLattice ^ ((2 : ℝ)⁻¹) := by
  simpa [minimum_stdLattice] using minimum_le_covolume_rpow stdLattice

/-! ### Shortest-vector problems -/

theorem isSolution_single : SVP.IsSolution 1 stdLattice (Pi.single 0 1) :=
  ⟨single_mem, single_ne_zero, by rw [norm_single, minimum_stdLattice, one_mul]⟩

example : ∃ v, SVP.IsSolution 1 stdLattice v := SVP.exists_isSolution_one stdLattice_ne_bot

example {γ : ℝ} {v : Fin 2 → ℝ} (hv : SVP.IsSolution γ stdLattice v) : 1 ≤ γ := hv.one_le

/-- `(ℤ², 1)` is a YES instance and `(ℤ², 1/3)` a NO instance of `GapSVP_2`. -/
example : GapSVP.IsYes stdLattice 1 ∧ GapSVP.IsNo 2 stdLattice (1 / 3) := by
  simp only [GapSVP.IsYes, GapSVP.IsNo, minimum_stdLattice]
  norm_num

/-- The reduction accepts the YES instance and rejects the NO instance, using the `SVP_2`
solution `e₀`. -/
example : GapSVP.decideOfSVP 2 1 (Pi.single 0 1 : Fin 2 → ℝ) = true ∧
    GapSVP.decideOfSVP 2 (1 / 3) (Pi.single 0 1 : Fin 2 → ℝ) = false := by
  have hv := isSolution_single.mono (by norm_num : (1 : ℝ) ≤ 2)
  refine ⟨(GapSVP.isCorrect_decideOfSVP (by norm_num) hv 1).1 ?_,
    (GapSVP.isCorrect_decideOfSVP (by norm_num) hv (1 / 3)).2 ?_⟩
  · simp [GapSVP.IsYes, minimum_stdLattice]
  · simp only [GapSVP.IsNo, minimum_stdLattice]; norm_num

example : ¬ (GapSVP.IsYes stdLattice 1 ∧ GapSVP.IsNo 1 stdLattice 1) :=
  GapSVP.not_isYes_and_isNo le_rfl stdLattice 1

/-- `ℤ²` has rank `2`. -/
private theorem finrank_stdLattice : Module.finrank ℤ stdLattice = 2 := by
  rw [ZLattice.rank ℝ stdLattice, Module.finrank_fin_fun]

/-- The two standard basis vectors `![e₀, e₁]`, indexed by `Fin (finrank ℤ ℤ²)`, solve `SIVP_1`
on `ℤ²`. -/
example : SIVP.IsSolution 1 stdLattice
    ((![Pi.single 0 1, Pi.single 1 1] : Fin 2 → Fin 2 → ℝ) ∘ Fin.cast finrank_stdLattice) := by
  have he : (![Pi.single 0 1, Pi.single 1 1] : Fin 2 → Fin 2 → ℝ) =
      ⇑(Pi.basisFun ℝ (Fin 2)) := by
    funext i
    fin_cases i <;> simp
  have hmin : 1 ≤ successiveMinimum stdLattice (Module.finrank ℤ stdLattice) := by
    rw [finrank_stdLattice]
    calc (1 : ℝ) = minimum stdLattice := minimum_stdLattice.symm
      _ ≤ _ := minimum_le_successiveMinimum stdLattice stdLattice_ne_bot (by norm_num) (by simp)
  rw [he]
  refine ⟨(Pi.basisFun ℝ (Fin 2)).linearIndependent.comp _ (Fin.cast_injective _),
    fun i => ⟨Submodule.subset_span ⟨_, rfl⟩, ?_⟩⟩
  rw [one_mul]
  refine le_trans ?_ hmin
  simp [Pi.norm_single]

/-- A shortest vector of a full-rank lattice in the Euclidean plane solves `HSVP_{√2}`. -/
example {L : Submodule ℤ (EuclideanSpace ℝ (Fin 2))} [DiscreteTopology L] [IsZLattice ℝ L]
    {v : EuclideanSpace ℝ (Fin 2)} (hv : SVP.IsSolution 1 L v) :
    HSVP.IsSolution (Real.sqrt 2) L v := by
  simpa using hv.hsvp zero_le_one

/-! ### Reduced families -/

/-- A single vector is a `3/4`-reduced family: both conditions quantify over pairs of distinct
indices of `Fin 1`. -/
theorem isReduced_single (v : EuclideanSpace ℝ (Fin 2)) :
    Cslib.Algorithms.LatticeReduction.IsReduced (3 / 4) ![v] :=
  ⟨fun i j hji => absurd hji (by omega), fun i j hij => absurd hij (by omega)⟩

/-- The reduced-family bound with `n = 0`: a nonzero vector is a shortest vector of its integer
span. -/
example {v : EuclideanSpace ℝ (Fin 2)} (hv : v ≠ 0) :
    SVP.IsSolution 1 (Submodule.span ℤ (Set.range ![v])) v := by
  simpa using SVP.isSolution_of_isReduced (isReduced_single v) (by simpa using hv)

end CslibFrontierTests.Crypto.LatticeGeometry
