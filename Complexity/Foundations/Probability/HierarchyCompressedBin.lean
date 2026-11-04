/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
module
-- upstream: candidate

public import Complexity.Foundations.Probability.HierarchyBudgetEvaluator
public import Complexity.Foundations.Probability.NormalizedAtomRows.ActualMoment
public import Complexity.Foundations.Probability.NormalizedAtomRows.SecondSignal

/-!
# Compressed normalized bins from actual budget history

The first signal sums the actual completed initial groups on full terminal rank. The second
signal completes the selected bin preparation of each first prefix on source × usage. Both
use the original environment. Compression decodes with the selected bin numerator, not the
hierarchy's atom cutoff. The result has dense normalized-bin scope; it is not RAW or an
incoming/max-decorated correction.

This finite construction does not establish the lower-budget canonical-error invariant or
its mean/noise payments. Later RAW constructors remain unavailable in the underlying evaluator.
-/

public section
noncomputable section
namespace Matrix.HierarchyParams.H4RankEnvironment.BudgetData
open Finset Cslib Cslib.RowCompression
open NormalizedMoments
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {P : ℕ} [Fact P.Prime] {HP : FourthRootHierarchyParams 16 1 16 32 8}
  (B : BudgetData HP P)

/-- Prefixes of the actual completed groups, with zero at prefix length zero.
The history and all paired budgets are those of the public budget evaluator. -/
@[expose] def initialPrefixes (M : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) :
    Option (ℕ → Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ) := do
  let groups ← (List.range (Nat.log2 M + 1)).mapM fun j =>
    B.completedGroup (fun m q => if m < M then B.evaluate m q else none) M
      (dyadicSlack (Nat.log2 M + 1) j) (.pilotInput ⟨0, HP.k_pos⟩)
      { r with usage := r.terminal }
  pure fun j σ x y => ((groups.take j).map (fun A => A σ x y)).sum

/-- Selected dense preparation of a stochastic first prefix, before its actual usage walk.
The numerator's corresponding bin preparation is retained, including the full terminal rank. -/
@[expose] def binPreparation (bin : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (A : Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ) :
    Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ :=
  fun σ => densePreparation B.padding id r (B.auxiliary bin) HP.ρ HP.K (A σ) σ

/-- Actual paired-group first prefixes, computed preparatory second prefixes and compression.
The positive-budget guard preserves the unavailable coarse boundary. The return scope is the
selected dense normalized bin; no incoming or maximum gate is added. -/
@[expose] def compressedBin (M bin k : ℕ) (ζ floor : ℝ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) :
    Option (Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ) := do
  if M = 0 ∨ ¬ 0 < B.requestPrecision M r ∨ r.terminal.rate ≠ rate k then none else do
    let F ← B.initialPrefixes M r
    let m := Nat.log2 M + 1
    let walks ← (List.range m).mapM fun j =>
      B.complete M r (B.binPreparation bin r (F (j + 1))) (dyadicSlack m j)
    let W := fun j σ x y => (walks[j - 1]?.getD 0) σ x y
    let Δ := firstSignalIncrement F k (secondSignalIncrement W ζ)
    pure fun σ x y =>
      let S : Finset (ZMod P) := {z | r.terminal.retains (channels B.padding) σ z}
      let a := iterate S (compatibleCapacity HP.K m) (fun _ => HP.K)
        (dyadicFloor floor m) (Δ σ x) ⟨0, 0⟩ m
      if r.usage.retains (channels B.padding) σ y then
        FourthRootHierarchyParams.NormalizedRow.output (B.cutoff bin) HP.ρ ζ
          (a.row y 0) (a.row y 1) (firstRank S HP.K a.defaultValue a.row)
      else 0

/-- Successful compression retains the actual bin's range and usage mask. The separate
threshold premise proves terminal-row support after compression, without propagating support
through either of its walks. No child-error or final-accuracy premise is used. -/
theorem compressedBin_bounds (M bin k : ℕ) (ζ floor : ℝ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (A : Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
    (hA : B.compressedBin M bin k ζ floor r = some A)
    {e g : ℝ} (he : 0 ≤ e) (hge : g ≤ e)
    (hc : ∀ d, d ≤ e → B.cutoff bin d = 0) (hg : ∀ q, g ≤ q → HP.ρ q = 0) :
    (∀ σ x y, A σ x y ∈ Set.Icc 0 (2 * B.binCap)) ∧
    (∀ σ x y, ¬ r.usage.retains (channels B.padding) σ y → A σ x y = 0) ∧
    ∀ σ x, #{y ∈ ({y | r.terminal.retains (channels B.padding) σ y} : Finset _) |
      A σ x y ≠ 0} < HP.K := by
  unfold compressedBin at hA
  split at hA
  · contradiction
  · cases hF : B.initialPrefixes M r with
    | none => simp [hF] at hA
    | some F =>
      simp only [hF, bind, Option.bind_some] at hA
      cases hW : (List.range (Nat.log2 M + 1)).mapM (fun j =>
          B.complete M r (B.binPreparation bin r (F (j + 1)))
            (dyadicSlack (Nat.log2 M + 1) j)) with
      | none => simp [hW] at hA
      | some W =>
        simp only [hW, Option.bind_some, pure] at hA
        have ha := Option.some.inj hA
        subst A
        dsimp only
        refine ⟨?_, ?_, ?_⟩
        · intro σ x y
          split_ifs
          · exact FourthRootHierarchyParams.NormalizedRow.output_mem_Icc _ _ B.binCap_nonneg
              (B.cutoff_bounds bin) (fun q => ⟨HP.ρ_nonneg q, HP.ρ_le_one q⟩) _ _ _ _
          · exact ⟨le_rfl, mul_nonneg (by norm_num) B.binCap_nonneg⟩
        · intro σ x y hy
          exact ite_eq_right hy
        · intro σ x
          let a := iterate {z | r.terminal.retains (channels B.padding) σ z}
            (compatibleCapacity HP.K (Nat.log2 M + 1)) (fun _ => HP.K)
            (dyadicFloor floor (Nat.log2 M + 1))
            (firstSignalIncrement F k
              (secondSignalIncrement (fun j σ x y => W[j - 1]?.getD 0 σ x y) ζ) σ x)
            ⟨0, 0⟩ (Nat.log2 M + 1)
          apply lt_of_le_of_lt (card_le_card ?_)
            (FourthRootHierarchyParams.NormalizedRow.support_of_cutoff _ _
              (FourthRootHierarchyParams.NormalizedRow.rank_pos HP) he hge hc hg
              {z | r.terminal.retains (channels B.padding) σ z} a ζ)
          intro y hy
          simp only [mem_filter] at hy ⊢
          refine ⟨hy.1, ?_⟩
          split_ifs at hy with hu
          · exact hy.2
          · exact (hy.2 rfl).elim

end Matrix.HierarchyParams.H4RankEnvironment.BudgetData
