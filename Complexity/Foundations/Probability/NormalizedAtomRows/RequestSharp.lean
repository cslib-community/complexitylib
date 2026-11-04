/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/
module
-- upstream: candidate

public import Complexity.Foundations.Probability.NormalizedAtomRows.Request
public import Complexity.Foundations.Probability.NormalizedAtomRows.Sharp

/-!
# Sharp comparison on the existing full-environment request

This client applies the actual decoder theorem to the existing `normalizedRequest` using
its source/usage conditional mean and original terminal rank. True first entries only need
be nonnegative. The first-overflow client derives its actual mean range from bounded
preparation inputs,
including empty slices. Raw prefix errors and the overflow events remain explicit inputs; no
normalized-output certificate is assumed. Lower-child moments and recursive budgets remain open.
-/

public section
namespace Matrix.HierarchyParams.H4RankEnvironment
open Finset Cslib Cslib.Probability Matrix Matrix.HierarchyParams Cslib.RowCompression
open Matrix.FourthRootHierarchyParams
open Matrix.FourthRootHierarchyParams.NormalizedRow
open scoped BigOperators
variable {P J : ℕ} [Fact P.Prime] {V : Type*} [Fintype V]

/-- Actual full-environment output comparison on the no-overflow event. The final
coefficient is fixed before choosing compressionScale; no lower prep-mean bound is required. -/
theorem normalizedRequest_sharp_noOverflow
    (HP : FourthRootHierarchyParams 16 1 16 32 8)
    {ζ scale : ℝ} (hζ : 0 < ζ) (hs : 0 < scale) (hmargin : scale ≤ HP.η) :
    ∃ Cfinal : ℝ, 0 ≤ Cfinal ∧ ∀ δ : ℝ, 0 < δ → δ ≤ scale →
      ∃ Cpre : ℝ, 0 ≤ Cpre ∧ ∀ {k : ℕ} (D : ZMod P) (ident : V → ZMod P)
      (r : HierarchyTask.Request k (Fin J) (ZMod P)), Admissible r →
      ∀ (raw prep trueRaw truePrep : Environment P J → Matrix V V ℝ)
      (σ : Environment P J) (x : V) (n : ℕ → ℕ)
      (Δ : ℕ → V → Fin 2 → ℝ) (m : ℕ),
      let s := ({z | r.terminal.retains (channels D) σ (ident z)} : Finset V)
      let signals := requestSignals ζ D ident r raw prep σ x
      let truth := requestSignals ζ D ident r trueRaw truePrep σ x
      (∀ i < m, stepThreshold s n (fun _ => HP.K) (dyadicFloor δ m) Δ ⟨0, signals⟩ i ≤
        dyadicFloor δ m i) →
      (∀ y ∈ s, 0 ≤ trueRaw σ x y / r.terminal.rate) →
      ∀ ε : ℕ → ℝ, (∀ i < m, 0 ≤ ε i) →
      (∀ i < m, ∀ y ∈ s, δ / 2 ≤ truth y 0 →
        clippedError (truth y 0) (truth y 1) (uncompressedRow Δ signals (i + 1) y) ≤ ε i) →
      ∀ εfinal : ℝ, 0 ≤ εfinal →
      (∀ y ∈ s, clippedError (truth y 0) (truth y 1) (uncompressedRow Δ signals m y) ≤ εfinal) →
      ∀ y ∈ s,
      let a := iterate s n (fun _ => HP.K) (dyadicFloor δ m) Δ ⟨0, signals⟩ m
      |(if r.usage.retains (channels D) σ (ident y) then
          output HP ζ (a.row y 0) (a.row y 1) (firstRank s HP.K a.defaultValue a.row)
        else 0) ^ (4⁻¹ : ℝ) - normalizedRequest D ident r HP.toHierarchyParams.atomCutoff HP.ρ HP.K
          trueRaw truePrep σ x y ^ (4⁻¹ : ℝ)| ≤
        Cpre*∑ i ∈ range m, dyadicFloor δ m i * ε i + Cfinal * εfinal := by
  classical
  obtain ⟨Cf, hCf, hf⟩ := sharp_noOverflow HP ζ hζ hs hmargin
  refine ⟨Cf, hCf, ?_⟩
  intro δ hδ hδs
  obtain ⟨Cp, hCp, hp⟩ := hf δ hδ hδs
  refine ⟨Cp, hCp, ?_⟩
  intro k D ident r hr raw prep trueRaw truePrep σ x n Δ m s signals truth
    hno hd ε hε herr εf hεf herrf y hy
  have hh := hp s n Δ signals truth m hno hd ε hε herr εf hεf herrf y hy
  rw [normalizedRequest_eq_output HP hζ D ident r hr]
  split_ifs
  · exact hh
  · simp only [Real.zero_rpow (by norm_num : (4⁻¹ : ℝ) ≠ 0), sub_self, abs_zero]
    exact add_nonneg (mul_nonneg hCp (sum_nonneg fun i hi =>
      mul_nonneg (dyadicFloor_nonneg hδ.le _ _) (hε i (mem_range.mp hi)))) (mul_nonneg hCf hεf)


omit [Fintype V] in
private lemma request_mean_range {k : ℕ}
    (D : ZMod P) (ident : V → ZMod P) (r : HierarchyTask.Request k (Fin J) (ZMod P))
    (prep : Environment P J → Matrix V V ℝ) (hp : ∀ τ x y, prep τ x y ∈ Set.Icc 0 1)
    (x y : V) :
    rowSliceMean (fun τ v => r.source.retains (channels D) τ (ident v))
      (fun τ v => r.usage.retains (channels D) τ (ident v)) prep x y ∈ Set.Icc 0 1 := by
  classical
  unfold rowSliceMean
  refine ⟨expect_nonneg (fun τ _ => (hp τ x y).1), ?_⟩
  by_cases hs : ({τ | r.source.retains (channels D) τ (ident x) ∧
      r.usage.retains (channels D) τ (ident y)} : Finset (Environment P J)).Nonempty
  · exact expect_le hs (fun τ _ => (hp τ x y).2)
  · rw [not_nonempty_iff_eq_empty.mp hs]
    simp only [expect_empty]
    norm_num

omit [Fintype V] in
private lemma request_second_bound {k : ℕ} {ζ scale : ℝ} (hζ : 0 < ζ) (hsmall : ζ ≤ scale / 2)
    (D : ZMod P) (ident : V → ZMod P) (r : HierarchyTask.Request k (Fin J) (ZMod P))
    (raw prep : Environment P J → Matrix V V ℝ) (σ : Environment P J) (x y : V)
    (hc : rowSliceMean (fun τ v => r.source.retains (channels D) τ (ident v))
      (fun τ v => r.usage.retains (channels D) τ (ident v)) prep x y ∈ Set.Icc 0 1) :
    |requestSignals ζ D ident r raw prep σ x y 1| ≤ scale / 2 := by
  classical
  simp only [requestSignals, Fin.isValue, one_ne_zero, ↓reduceIte]
  split_ifs
  · rw [abs_mul, abs_of_pos hζ, abs_of_nonneg hc.1]
    exact (mul_le_of_le_one_right hζ.le hc.2).trans hsmall
  · simp only [mul_zero, abs_zero]; linarith

/-- The same actual request after its first overflow. The uncentered prep signal is bounded
using the one full-environment mean; no independent preparatory environment is introduced. -/
theorem normalizedRequest_sharp_firstOverflow
    (HP : FourthRootHierarchyParams 16 1 16 32 8)
    {ζ scale : ℝ} (hζ : 0 < ζ) (hs : 0 < scale) (hmargin : scale ≤ HP.η) (hsmall : ζ ≤ scale / 2)
    (hcapscale : scale ≤ HP.toHierarchyParams.atomCap / 10000) :
    ∃ Ctail : ℝ, 0 ≤ Ctail ∧ ∀ δ : ℝ, 0 < δ → δ ≤ scale →
      ∃ Cpre : ℝ, 0 ≤ Cpre ∧ ∀ {k : ℕ} (D : ZMod P) (ident : V → ZMod P)
      (r : HierarchyTask.Request k (Fin J) (ZMod P)), Admissible r →
      ∀ (raw prep trueRaw truePrep : Environment P J → Matrix V V ℝ)
      (σ : Environment P J) (x : V) (n : ℕ → ℕ)
      (Δ : ℕ → V → Fin 2 → ℝ) (m j : ℕ), j < m →
      let s := ({z | r.terminal.retains (channels D) σ (ident z)} : Finset V)
      let signals := requestSignals ζ D ident r raw prep σ x
      let truth := requestSignals ζ D ident r trueRaw truePrep σ x
      IsFirstOverflow s n (fun _ => HP.K) (dyadicFloor δ m) Δ ⟨0, signals⟩ j →
      (∀ y ∈ s, 0 ≤ trueRaw σ x y / r.terminal.rate) →
      (∀ τ x y, truePrep τ x y ∈ Set.Icc 0 1) →
      (∀ i, j ≤ i → i < m → HP.K ≤ n i) →
      ∀ ε : ℕ → ℝ, (∀ i < m, 0 ≤ ε i) →
      (∀ i < j, ∀ y ∈ s, δ / 2 ≤ truth y 0 →
        clippedError (truth y 0) (truth y 1) (uncompressedRow Δ signals (i + 1) y) ≤ ε i) →
      (∀ i, j ≤ i → i < m → ∀ y ∈ s,
        clippedError (truth y 0) (truth y 1) (uncompressedRow Δ signals (i + 1) y) ≤ ε i) →
      ∀ y ∈ s,
      let a := iterate s n (fun _ => HP.K) (dyadicFloor δ m) Δ ⟨0, signals⟩ m
      |(if r.usage.retains (channels D) σ (ident y) then
          output HP ζ (a.row y 0) (a.row y 1) (firstRank s HP.K a.defaultValue a.row)
        else 0) ^ (4⁻¹ : ℝ) - normalizedRequest D ident r HP.toHierarchyParams.atomCutoff HP.ρ HP.K
          trueRaw truePrep σ x y ^ (4⁻¹ : ℝ)| ≤
        Cpre*∑ i ∈ range j, dyadicFloor δ m i * ε i + Ctail*∑ i ∈ Ico j m, 28^(m - i) * ε i := by
  classical
  obtain ⟨Ct, hCt, ht⟩ := sharp_firstOverflow HP ζ hζ hs hmargin hcapscale
  refine ⟨Ct, hCt, ?_⟩
  intro δ hδ hδs
  obtain ⟨Cp, hCp, hp⟩ := ht δ hδ hδs
  refine ⟨Cp, hCp, ?_⟩
  intro k D ident r hr raw prep trueRaw truePrep σ x n Δ m j hj s signals truth
    hover hd hc hn ε hε herrpre herrtail y hy
  have hh := hp s n Δ signals truth m j hj hover hd
    (fun y _ => request_second_bound hζ hsmall D ident r trueRaw truePrep σ x y
      (request_mean_range D ident r truePrep hc x y))
    hn ε hε herrpre herrtail y hy
  rw [normalizedRequest_eq_output HP hζ D ident r hr]
  split_ifs
  · exact hh
  · simp only [Real.zero_rpow (by norm_num : (4⁻¹ : ℝ) ≠ 0), sub_self, abs_zero]
    exact add_nonneg (mul_nonneg hCp (sum_nonneg fun i hi =>
      mul_nonneg (dyadicFloor_nonneg hδ.le _ _) (hε i ((mem_range.mp hi).trans hj))))
      (mul_nonneg hCt (sum_nonneg fun i hi => mul_nonneg (by positivity) (hε i (mem_Ico.mp hi).2)))


end Matrix.HierarchyParams.H4RankEnvironment
