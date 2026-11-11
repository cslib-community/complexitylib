/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.LogSpaceDerandomization.NormalizedAtomRows.Sharp
public import CslibFrontier.Computability.LogSpaceDerandomization.RowCompression.FourthMoment
public import CslibFrontier.Computability.LogSpaceDerandomization.HeavyCountRarity
import CslibFrontier.Computability.LogSpaceDerandomization.RowCompression.FalseOverflowNorm

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
/-- The root error has support below 2K, independently of row width and defaults. -/
lemma sum_rootError_four {ι : Type*} (S : Finset ι) (ζ : ℝ) (a b : State ι)
    {E : ℝ} (h : ∀ y ∈ S, |stateRootError (output HP ζ) S HP.K a b y| ≤ E) :
    ∑ y ∈ S, |stateRootError (output HP ζ) S HP.K a b y| ^ 4 ≤ 2 * (HP.K : ℝ) * E ^ 4 := by
  let T := {y ∈ S | output HP ζ (a.row y 0) (a.row y 1) (firstRank S HP.K a.defaultValue a.row) ≠
    0} ∪
    {y ∈ S | output HP ζ (b.row y 0) (b.row y 1) (firstRank S HP.K b.defaultValue b.row) ≠ 0}
  have hT : T ⊆ S := union_subset (filter_subset _ _) (filter_subset _ _)
  have hc : T.card ≤ 2 * HP.K := (card_union_le _ _).trans (by
    have ha := support HP S a ζ
    have hb := support HP S b ζ
    omega)
  calc
    _ = ∑ y ∈ T, |stateRootError (output HP ζ) S HP.K a b y| ^ 4 := by
      symm
      apply sum_subset hT
      intro y hy hyt
      have ha : output HP ζ (a.row y 0) (a.row y 1) (firstRank S HP.K a.defaultValue a.row) = 0 :=
        by
        by_contra hz
        exact hyt (mem_union_left _ (mem_filter.mpr ⟨hy, hz⟩))
      have hb : output HP ζ (b.row y 0) (b.row y 1) (firstRank S HP.K b.defaultValue b.row) = 0 :=
        by
        by_contra hz
        exact hyt (mem_union_right _ (mem_filter.mpr ⟨hy, hz⟩))
      simp only [stateRootError, ha, hb, Real.zero_rpow (by norm_num : (4⁻¹ : ℝ) ≠ 0), sub_self,
        abs_zero, zero_pow (by decide : 4 ≠ 0)]
    _ ≤ ∑ _y ∈ T, E ^ 4 := sum_le_sum fun y hy => pow_le_pow_left₀ (abs_nonneg _) (h y (hT hy)) 4
    _ = (T.card : ℝ) * E ^ 4 := by simp only [sum_const, nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hc) (by positivity)

open Classical in
lemma rootError_range {ι : Type*} (S : Finset ι) (ζ : ℝ) (a b : State ι) (y : ι) :
    |stateRootError (output HP ζ) S HP.K a b y| ≤ 2 * HP.Q HP.toHierarchyParams.atomCap ^ (4⁻¹ : ℝ)
      := by
  have ha := root_range HP ζ (a.row y 0) (a.row y 1) (firstRank S HP.K a.defaultValue a.row)
  have hb := root_range HP ζ (b.row y 0) (b.row y 1) (firstRank S HP.K b.defaultValue b.row)
  exact abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩
end Matrix.FourthRootHierarchyParams.NormalizedRow
namespace Matrix.FourthRootHierarchyParams.NormalizedRow

open Finset Cslib Cslib.RowCompression Cslib.Probability
open scoped BigOperators

variable {ι : Type*} (HP : Matrix.FourthRootHierarchyParams 16 1 16 32 8) (ζ : ℝ)
open Classical in
/-- Uniform bound for the difference of two actual output fourth roots. -/
@[expose] noncomputable def rangeBound := 2 * HP.Q HP.toHierarchyParams.atomCap ^ (4⁻¹ : ℝ)

variable {Ω V : Type*} [Fintype Ω] [Fintype V]

private theorem rangeBound_nonneg (HP : Matrix.FourthRootHierarchyParams 16 1 16 32 8) :
    0 ≤ rangeBound HP :=
  mul_nonneg (by norm_num) (Real.rpow_nonneg (HP.Q_nonneg _) _)

open Classical in
/-- The final actual polynomial outputs on a specified false-first-overflow event are paid
for by the raw-prefix moment at `j + 1`. Every random quantity may share the environment. -/
theorem rowNormPow_falseFirstOverflow_le {η N u : ℝ}
    (hη : 0 < η) (hη1 : η ≤ 1) (hNu : 0 ≤ N * u)
    (X Y : Ω → V → Prop) [∀ σ x, Decidable (X σ x)] [∀ σ y, Decidable (Y σ y)]
    (n : ℕ → ℕ) (_hK : 0 < HP.K) (m j : ℕ) (hj : j < m) (hn : 0 < n j)
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
      if F σ x then stateRootError (output HP ζ) (S σ) HP.K (b σ x) ⟨0, truth σ x⟩ y else 0) ≤
      (64 * (HP.K : ℝ) * (rangeBound HP) ^ 4 / ((n j : ℝ) * dyadicFloor η m j ^ 4)) *
        rowNormPow 4 N u X Y (fun σ x y => clippedError (truth σ x y 0) (truth σ x y 1)
          (uncompressedRow (Δ σ x) (a σ x).row (j + 1) y)) :=
  rowNormPow_falseFirstOverflow_le_of_bound hη hη1 hNu X Y n HP.K m j
    hj hn Δ a truth
    (fun σ x y => stateRootError (output HP ζ) ({y | Y σ y} : Finset V) HP.K
      (iterate ({y | Y σ y} : Finset V) n (fun _ => HP.K) (dyadicFloor η m) (Δ σ x) (a σ x) m)
      ⟨0, truth σ x⟩ y)
    (pow_nonneg (rangeBound_nonneg HP) 4)
    (fun _ _ _ => sum_rootError_four HP _ ζ _ _ fun y _ =>
      rootError_range HP _ ζ _ _ y)
    ha hfirst hsecond

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
      if ∃ j < m, F j σ x then stateRootError (output HP ζ) (S σ) HP.K (b σ x) ⟨0, truth σ x⟩ y
        else 0) ≤
      ∑ j ∈ range m, (64 * (HP.K : ℝ) * (rangeBound HP) ^ 4 / ((n j : ℝ) * dyadicFloor η m j ^ 4))
        * rowNormPow 4 N u X Y (fun σ x y => clippedError (truth σ x y 0) (truth σ x y 1)
          (uncompressedRow (Δ σ x) (a σ x).row (j + 1) y)) := by
  classical
  exact (rowNormPow_ite_exists_le_sum hNu X Y m _ _).trans <|
    sum_le_sum fun j hj => rowNormPow_falseFirstOverflow_le HP ζ hη hη1 hNu X Y n hK m j
      (mem_range.mp hj) (hn j (mem_range.mp hj)) Δ a truth ha hfirst
      (hsecond j (mem_range.mp hj))

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
          stateRootError (output HP ζ) (S σ) HP.K (actual σ x) ⟨0, truth σ x⟩ y) ≤
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
  intro Ω V _ _ N u hNu X Y _ _ n m hcapacity Δ raw truth hfirst hsecond
    hvanish ε εfinal hε hεfinal herr herrfinal
  dsimp only
  have hfalse := rowNormPow_falseFirstOverflowBefore_le HP ζ hη hη1 hNu X Y n
    (NormalizedRow.rank_pos HP) m
    (fun i hi => (NormalizedRow.rank_pos HP).trans_le (hcapacity i hi)) Δ (fun σ x => ⟨0, raw σ
      x⟩) truth (by intros; rfl) hfirst hvanish
  refine (rowNormPow_le_three_budgets_add_ite hNu X Y _ _ HP.K A C _ _ _
    fun σ x hx hf => ?_).trans (add_le_add_right hfalse _)
  exact sum_rootError_four HP _ ζ _ _
    (hbound _ n (Δ σ x) (raw σ x) (truth σ x) m
      (fun j => heavyCountEvent Y univ (fun y => truth σ x y 0) (dyadicFloor η m j) (n j) σ)
      (fun y hy => hfirst σ x y hx (mem_filter.mp hy).2)
      (fun y hy => hsecond σ x y hx (mem_filter.mp hy).2) hcapacity
      (fun i => ε i σ x) (fun i hi => hε i hi σ x hx)
      (fun i hi y hy => herr i hi σ x y hx (mem_filter.mp hy).2)
      (εfinal σ x) (hεfinal σ x hx)
      (fun y hy => herrfinal σ x y hx (mem_filter.mp hy).2) hf)

end Matrix.FourthRootHierarchyParams.NormalizedRow
