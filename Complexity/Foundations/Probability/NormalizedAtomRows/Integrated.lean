/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Probability.NormalizedAtomRows.Sharp
public import Complexity.Foundations.Probability.CompressionIntegrated
public import Complexity.Foundations.Analysis.RowCompression.FourthMoment
public import Complexity.Foundations.Probability.HeavyCountRarity

/-!
# Integrated support and false-event comparison for actual normalized rows

`sum_rootError_four` converts a uniform endpoint root error into a row fourth moment using
the union of the two actual output supports, of cardinality at most 2K.
`rowNormPow_falseFirstOverflowBefore_le` pays the complementary false-event union at the
already-added raw prefix j+1. `exists_compression_rowNormPow_le` combines this charge with
sharp no-overflow final error, weighted preloss and heavy first-overflow tails. All masks
and errors may depend on the same environment; true first entries are arbitrary nonnegative
reals. Comparison constants precede the later floor, except the stationary coefficient.

This is the conditional fourth-moment assembly corresponding to §8.2, Proposition 8.5
(printed pp. 45–49), of [OpenAI2026LogSpace], revision 7ef5c0cc. The generic sharp decoder
comparison comes from the existing NormalizedAtomRows API; stochastic prefix estimates,
recursive induction and native resource bounds are separate. Christian Reitwiessner supplied
the actual decoder specialization; Samuel Schlesinger supplied the adapted compression/norm
proof patterns.
-/

public section
open Matrix.FourthRootHierarchyParams
namespace Matrix.FourthRootHierarchyParams.NormalizedRow
open Finset Cslib Matrix Cslib.RowCompression
open scoped BigOperators
variable (HP : FourthRootHierarchyParams 16 1 16 32 8)

open Classical in
/-- Uniform bound for the difference of two actual output fourth roots. -/
@[expose] noncomputable def rangeBound := 2 * HP.Q HP.toHierarchyParams.atomCap ^ (4⁻¹ : ℝ)

open Classical in
/-- The root error has support below 2K, independently of row width and defaults. -/
lemma sum_rootError_four {ι : Type*} (S : Finset ι) (ζ : ℝ) (a b : State ι)
    {E : ℝ} (_hE : 0 ≤ E) (h : ∀ y ∈ S, |stateRootError (output HP.toHierarchyParams.atomCutoff
      HP.ρ ζ) S HP.K a b y| ≤ E) :
    ∑ y ∈ S, |stateRootError (output HP.toHierarchyParams.atomCutoff HP.ρ ζ) S HP.K a b y| ^ 4 ≤
      2 * (HP.K : ℝ) * E ^ 4 := by
  exact Cslib.RowCompression.sum_rootError_four _ HP.K
    (fun S a => support HP S a ζ) S a b _hE h

open Classical in
lemma rootError_range {ι : Type*} (S : Finset ι) (ζ : ℝ) (a b : State ι) (y : ι) :
    |stateRootError (output HP.toHierarchyParams.atomCutoff HP.ρ ζ) S HP.K a b y| ≤
      2 * HP.Q HP.toHierarchyParams.atomCap ^ (4⁻¹ : ℝ) := by
  exact Cslib.RowCompression.rootError_range _ HP.K _ (root_range HP ζ) S a b y

end Matrix.FourthRootHierarchyParams.NormalizedRow
namespace Matrix.FourthRootHierarchyParams.NormalizedRow

open Finset Cslib Cslib.RowCompression Cslib.Probability
open scoped BigOperators

variable {ι : Type*} (HP : Matrix.FourthRootHierarchyParams 16 1 16 32 8) (ζ : ℝ)

variable {Ω V : Type*} [Fintype Ω] [Fintype V]

open Classical in
/-- The final actual polynomial outputs on a specified false-first-overflow event are paid
for by the raw-prefix moment at `j + 1`. Every random quantity may share the environment. -/
theorem rowNormPow_falseFirstOverflow_le {η N u : ℝ}
    (hη : 0 < η) (hη1 : η ≤ 1) (hNu : 0 ≤ N * u)
    (X Y : Ω → V → Prop) [∀ σ x, Decidable (X σ x)] [∀ σ y, Decidable (Y σ y)]
    (n : ℕ → ℕ) (hK : 0 < HP.K) (m j : ℕ) (hj : j < m) (hn : 0 < n j)
    (Δ : Ω → V → ℕ → V → Fin 2 → ℝ) (a : Ω → V → State V)
    (truth : Ω → V → V → Fin 2 → ℝ)
    (ha : ∀ σ x, X σ x → (a σ x).defaultValue = 0)
    (hfirst : ∀ σ x y, X σ x → Y σ y → 0 ≤ truth σ x y 0)
    (hsecond : ∀ σ x y, X σ x → Y σ y →
      truth σ x y 0 ≤ dyadicFloor η m j / 4 → truth σ x y 1 = 0) :
    let S := fun σ => ({y | Y σ y} : Finset V)
    let b := fun σ x => iterate (S σ) n (fun _ => HP.K) (dyadicFloor η m) (Δ σ x) (a σ x) m
    let F := fun σ x => IsFirstOverflow (S σ) n (fun _ => HP.K)
      (dyadicFloor η m) (Δ σ x) (a σ x) j ∧
        ¬ heavyCountEvent Y univ (fun y => truth σ x y 0) (dyadicFloor η m j) (n j) σ
    rowNormPow 4 N u X Y (fun σ x y =>
      if F σ x then stateRootError (output HP.toHierarchyParams.atomCutoff HP.ρ ζ) (S σ) HP.K (b
        σ x) ⟨0, truth σ x⟩ y else 0) ≤
      (64 * (HP.K : ℝ) * (rangeBound HP) ^ 4 / ((n j : ℝ) * dyadicFloor η m j ^ 4)) *
        rowNormPow 4 N u X Y (fun σ x y => clippedError (truth σ x y 0) (truth σ x y 1)
          (uncompressedRow (Δ σ x) (a σ x).row (j + 1) y)) := by
  exact Cslib.RowCompression.rowNormPow_falseFirstOverflow_le (output
    HP.toHierarchyParams.atomCutoff HP.ρ ζ)
    HP.K (rangeBound HP) (mul_nonneg (by norm_num) (Real.rpow_nonneg (HP.Q_nonneg _) _))
    (fun S a => support HP S a ζ) (root_range HP ζ) hη hη1 hNu X Y n hK m j hj hn Δ a truth ha
      hfirst hsecond

open Classical in
/-- **The false-type contribution to actual final output error.** Taking the union of the
possible false first overflows gives the sum of their raw-prefix charges. Both sides use the
same `RootMetric` normalization, and no independence or final-output error premise is required. -/
theorem rowNormPow_falseFirstOverflowBefore_le {η N u : ℝ}
    (hη : 0 < η) (hη1 : η ≤ 1) (hNu : 0 ≤ N * u)
    (X Y : Ω → V → Prop) [∀ σ x, Decidable (X σ x)] [∀ σ y, Decidable (Y σ y)]
    (n : ℕ → ℕ) (hK : 0 < HP.K) (m : ℕ) (hn : ∀ j < m, 0 < n j)
    (Δ : Ω → V → ℕ → V → Fin 2 → ℝ) (a : Ω → V → State V)
    (truth : Ω → V → V → Fin 2 → ℝ)
    (ha : ∀ σ x, X σ x → (a σ x).defaultValue = 0)
    (hfirst : ∀ σ x y, X σ x → Y σ y → 0 ≤ truth σ x y 0)
    (hsecond : ∀ j < m, ∀ σ x y, X σ x → Y σ y →
      truth σ x y 0 ≤ dyadicFloor η m j / 4 → truth σ x y 1 = 0) :
    let S := fun σ => ({y | Y σ y} : Finset V)
    let b := fun σ x => iterate (S σ) n (fun _ => HP.K) (dyadicFloor η m) (Δ σ x) (a σ x) m
    let F := fun j σ x => IsFirstOverflow (S σ) n (fun _ => HP.K)
      (dyadicFloor η m) (Δ σ x) (a σ x) j ∧
        ¬ heavyCountEvent Y univ (fun y => truth σ x y 0) (dyadicFloor η m j) (n j) σ
    rowNormPow 4 N u X Y (fun σ x y =>
      if ∃ j < m, F j σ x then stateRootError (output HP.toHierarchyParams.atomCutoff HP.ρ ζ) (S
        σ) HP.K (b σ x) ⟨0, truth σ x⟩ y
        else 0) ≤
      ∑ j ∈ range m, (64 * (HP.K : ℝ) * (rangeBound HP) ^ 4 / ((n j : ℝ) * dyadicFloor η m j ^ 4))
 *
        rowNormPow 4 N u X Y (fun σ x y => clippedError (truth σ x y 0) (truth σ x y 1)
          (uncompressedRow (Δ σ x) (a σ x).row (j + 1) y)) := by
  exact Cslib.RowCompression.rowNormPow_falseFirstOverflowBefore_le (output
    HP.toHierarchyParams.atomCutoff HP.ρ ζ)
    HP.K (rangeBound HP) (mul_nonneg (by norm_num) (Real.rpow_nonneg (HP.Q_nonneg _) _))
    (fun S a => support HP S a ζ) (root_range HP ζ) hη hη1 hNu X Y n hK m hn Δ a truth ha hfirst
      hsecond

end Matrix.FourthRootHierarchyParams.NormalizedRow
namespace Matrix.FourthRootHierarchyParams.NormalizedRow
open Finset Cslib Cslib.RowCompression Cslib.Probability
open scoped BigOperators
variable (HP : Matrix.FourthRootHierarchyParams 16 1 16 32 8) (ζ : ℝ) (hζ : 0 < ζ)

include hζ
open Classical in
/-- The actual final output is bounded by weighted prefix, no-overflow final and true-overflow
budgets, plus the existing false-overflow raw-prefix charge. The masks and all errors may be
correlated. No final-output error premise or factor counting endpoints or groups is introduced. -/
theorem exists_compression_rowNormPow_le {scale : ℝ} (hs : 0 < scale) (hmargin : scale ≤ HP.η)
  (hcapscale : scale ≤ HP.toHierarchyParams.atomCap / 10000) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ η : ℝ, 0 < η → η ≤ scale → η ≤ 1 →
      ∃ A : ℝ, 0 ≤ A ∧ ∀ {Ω V : Type*} [Fintype Ω] [Fintype V]
        (N u : ℝ), 0 ≤ N * u → ∀ (X Y : Ω → V → Prop)
        [∀ σ x, Decidable (X σ x)] [∀ σ y, Decidable (Y σ y)]
        (n : ℕ → ℕ) (m : ℕ), (∀ i < m, HP.K ≤ n i) →
        ∀ (Δ : Ω → V → ℕ → V → Fin 2 → ℝ) (raw : Ω → V → V → Fin 2 → ℝ)
        (truth : Ω → V → V → Fin 2 → ℝ),
        (∀ σ x y, X σ x → Y σ y → 0 ≤ truth σ x y 0) →
        (∀ σ x y, X σ x → Y σ y → |truth σ x y 1| ≤ scale / 2) →
        (∀ j < m, ∀ σ x y, X σ x → Y σ y →
          truth σ x y 0 ≤ dyadicFloor η m j / 4 → truth σ x y 1 = 0) →
        ∀ (ε : ℕ → Ω → V → ℝ) (εfinal : Ω → V → ℝ),
        (∀ i < m, ∀ σ x, X σ x → 0 ≤ ε i σ x) →
        (∀ σ x, X σ x → 0 ≤ εfinal σ x) →
        (∀ i < m, ∀ σ x y, X σ x → Y σ y →
          clippedError (truth σ x y 0) (truth σ x y 1)
            (uncompressedRow (Δ σ x) (raw σ x) (i + 1) y) ≤ ε i σ x) →
        (∀ σ x y, X σ x → Y σ y →
          clippedError (truth σ x y 0) (truth σ x y 1)
            (uncompressedRow (Δ σ x) (raw σ x) m y) ≤ εfinal σ x) →
        let S := fun σ => ({y | Y σ y} : Finset V)
        let actual := fun σ x => iterate (S σ) n (fun _ => HP.K)
          (dyadicFloor η m) (Δ σ x) ⟨0, raw σ x⟩ m
        let Pre := fun σ x => ∑ i ∈ range m, dyadicFloor η m i * ε i σ x
        let No := fun σ x => if ∀ i < m,
          stepThreshold (S σ) n (fun _ => HP.K) (dyadicFloor η m) (Δ σ x) ⟨0, raw σ x⟩ i ≤
            dyadicFloor η m i then εfinal σ x else 0
        let Tail := fun σ x => ∑ j ∈ range m,
          if IsFirstOverflow (S σ) n (fun _ => HP.K) (dyadicFloor η m) (Δ σ x) ⟨0, raw σ x⟩ j ∧
            heavyCountEvent Y univ (fun y => truth σ x y 0) (dyadicFloor η m j) (n j) σ then
              ∑ i ∈ Ico j m, (28 : ℝ) ^ (m - i) * ε i σ x else 0
        rowNormPow 4 N u X Y (fun σ x y =>
          stateRootError (output HP.toHierarchyParams.atomCutoff HP.ρ ζ) (S σ) HP.K (actual σ x)
            ⟨0, truth σ x⟩ y) ≤
          128 * (HP.K : ℝ) * (A ^ 4 * vertexNormPow 4 N u X Pre +
            C ^ 4 * vertexNormPow 4 N u X No + C ^ 4 * vertexNormPow 4 N u X Tail) +
          ∑ j ∈ range m, (64 * (HP.K : ℝ) * (rangeBound HP) ^ 4 / ((n j : ℝ) * dyadicFloor η m j ^
            4)) *
            rowNormPow 4 N u X Y (fun σ x y => clippedError (truth σ x y 0) (truth σ x y 1)
              (uncompressedRow (Δ σ x) (raw σ x) (j + 1) y)) := by
  classical
  obtain ⟨C, hC, hscales⟩ := NormalizedRow.sharp_compression HP ζ hζ hs hmargin hcapscale
  refine ⟨C, hC, ?_⟩
  intro η hη hmargin hη1
  obtain ⟨A, hA, hbound⟩ := hscales η hη hmargin
  refine ⟨A, hA, ?_⟩
  exact Cslib.RowCompression.compression_rowNormPow_le
    (output HP.toHierarchyParams.atomCutoff HP.ρ ζ) HP.K (rangeBound HP)
    (mul_nonneg (by norm_num) (Real.rpow_nonneg (HP.Q_nonneg _) _)) (fun S a => support HP S a ζ)
      (root_range HP ζ)
    (rank_pos HP) hη hη1 hC hA hbound

end Matrix.FourthRootHierarchyParams.NormalizedRow
