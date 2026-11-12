/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Computability.Complexity.Problems.MaxCut.Derandomized
public import CslibFrontier.Computability.Probabilistic.RejectionSampling
public import CslibFrontier.Probability.Product.ConditionalExpectation
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Tests for fair-bit block rejection sampling, product conditional expectations, and derandomization

Exercises the public module-system interfaces (`public import`, no `import all`) of:
1. `CslibFrontier.Probability.DDGTree.Rejection`,
   `CslibFrontier.Languages.Probabilistic.RejectionSampling`, and
   `CslibFrontier.Computability.Probabilistic.RejectionSampling`;
2. `CslibFrontier.Probability.Product.ConditionalExpectation`,
   `CslibFrontier.Algorithms.Lean.PessimisticEstimator`, and
   `CslibFrontier.Computability.PolyTime.PessimisticEstimator`;
3. `CslibFrontier.Algorithms.Lean.MaxCut.Derandomized` and
   `CslibFrontier.Computability.Complexity.Problems.MaxCut.Derandomized`.
-/

public section

namespace Cslib.Tests.FairBitRejectionAndCondExp

open scoped ENNReal Cslib.Probability.PMF
open Cslib.Probability Cslib.PessimisticEstimator Cslib.Algorithms.Lean.MaxCut
open Cslib.Algorithms.Lean Cslib.Algorithms.Lean.PessimisticEstimator
open Cslib.Complexity Cslib.Complexity.MaxCut
open Turing.MultiTapeTM

/-! ## 1. Strict `module` surface checks (`rfl`) -/

/-- Public `@[expose]` surface check for `uniformFinRejectionSpec.width`. -/
theorem strict_uniformFin_width_rfl (n : ℕ) :
    (uniformFinRejectionSpec n).width = Nat.clog 2 n :=
  rfl

/-- Public `@[expose]` surface check for `derandomizedCut` on the empty multigraph. -/
theorem strict_derandomizedCut_empty_rfl :
    derandomizedCut [] = [] :=
  rfl

/-! ## 2. Exact DDG-tree expected flips, capped failure, fallback distance, and degenerate cases -/

/-- Exact power-of-two flip counts: `2 ^ 0 = 1` uses `0` coin flips and `2 ^ 2 = 4` uses `2`. -/
theorem uniformFinTree_two_pow_examples :
    (uniformFinTree 1).expectedFlips = 0 ∧ (uniformFinTree 4).expectedFlips = 2 := by
  refine ⟨?_, ?_⟩
  · simpa using expectedFlips_uniformFinTree_two_pow 0
  · simpa using expectedFlips_uniformFinTree_two_pow 2

/-- Non-power-of-two exact closed forms: `Fin 3` (`width = 2`, `acceptProb = 3 / 4`) uses `8 / 3`
expected flips, and `Fin 5` (`width = 3`, `acceptProb = 5 / 8`) uses `24 / 5` expected flips. -/
theorem uniformFinTree_three_and_five_exact :
    (uniformFinTree 3).expectedFlips = (8 : ℝ≥0∞) / 3 ∧
      (uniformFinTree 5).expectedFlips = (24 : ℝ≥0∞) / 5 ∧
      (uniformFinTree 3).Generates (PMF.uniformOfFintype (Fin 3)) := by
  have hclog3 : Nat.clog 2 3 = 2 := by decide
  have hclog5 : Nat.clog 2 5 = 3 := by decide
  refine ⟨?_, ?_, uniformFinTree_generates 3⟩
  · rw [expectedFlips_uniformFinTree_of_two_le (by decide : 2 ≤ 3), hclog3]
    norm_num
  · rw [expectedFlips_uniformFinTree_of_two_le (by decide : 2 ≤ 5), hclog5]
    norm_num

/-- Capped 2-trial failure probability on `Fin 3` is at most `(1 / 2) ^ 2 = 1 / 4`, and fallback
statistical distance to `PMF.uniformOfFintype (Fin 3)` is at most `1 / 4` (in fact `1 / 24`, since
`rejectProb = 1 / 4` and `1 - 1 / 3 = 2 / 3`). -/
theorem uniformFin_capped_two_trials_bounds :
    (uniformFinRejectionSpec 3).runTrials 2 none ≤ ((1 : ℝ≥0∞) / 2) ^ 2 ∧
      dist ((uniformFinRejectionSpec 3).runCapped (0 : Fin 3) 2)
        (PMF.uniformOfFintype (Fin 3)) ≤ (1 : ℝ) / 4 := by
  refine ⟨runTrials_uniformFinRejectionSpec_none_le 3 2, ?_⟩
  have hd :=
    BlockRejectionSpec.dist_runCapped_le (singleLaw_uniformFinRejectionSpec_some 3) (0 : Fin 3) 2
  have hle :
      ((uniformFinRejectionSpec 3).rejectProb ^ 2).toReal ≤ (((1 : ℝ≥0∞) / 2) ^ 2).toReal :=
    ENNReal.toReal_mono (by norm_num) (by
      rw [← (uniformFinRejectionSpec 3).runTrials_none 2]
      exact runTrials_uniformFinRejectionSpec_none_le 3 2)
  refine hd.trans (hle.trans ?_)
  norm_num

/-- Degenerate boundary check: a block spec whose `attempt` always rejects has `acceptProb = 0`,
`rejectProb = 1`, `runTrials 5 none = 1`, and unbounded `toDDGTree.expectedFlips = ⊤`. -/
theorem neverAcceptSpec_boundary :
    let R : BlockRejectionSpec Unit := ⟨1, fun _ => none⟩
    R.acceptProb = 0 ∧ R.rejectProb = 1 ∧ R.runTrials 5 none = 1 ∧
      R.toDDGTree.expectedFlips = ⊤ := by
  intro R
  have hrej : R.rejectProb = 1 := by
    simp [R, BlockRejectionSpec.rejectProb, BlockRejectionSpec.singleLaw]
  have hacc : R.acceptProb = 0 := by
    simp [BlockRejectionSpec.acceptProb, hrej]
  refine ⟨hacc, hrej, ?_, ?_⟩
  · rw [R.runTrials_none 5, hrej, one_pow]
  · rw [R.expectedFlips_toDDGTree (by decide : 0 < R.width), hacc]
    simp [R]

/-- Subset rejection sampling on `{1, 3, 5} ⊆ Fin 6` generates `PMF.uniformOfFinset` with exact
expected flips `3 * 8 / 3 = 8`, and `sampleBlockTrials` satisfies `IsPPTOn` for unary parameters. -/
theorem subset_and_ppt_rejection_checks :
    let S : Finset (Fin 6) := {1, 3, 5}
    have hS : S.Nonempty := ⟨1, by decide⟩
    (subsetDyadicSpec 6 id S).toDDGTree.Generates (PMF.uniformOfFinset S hS) ∧
      (subsetDyadicSpec 6 id S).toDDGTree.expectedFlips = 8 ∧
      IsPPTOn (encPair encUnary encUnary) (encOption encBits)
        (fun p : ℕ × ℕ => ProbComp.sampleBlockTrials
          ⟨p.1, fun bits => some (bits.take 2)⟩ p.2) := by
  intro S hS
  have hcov : ∀ a ∈ S, ∃ i : Fin 6, id i = a := fun a _ => ⟨a, rfl⟩
  refine ⟨subsetDyadicSpec_generates Function.injective_id hS hcov, ?_, ?_⟩
  · rw [expectedFlips_subsetDyadicSpec Function.injective_id hS hcov]
    have hcard : S.card = 3 := by decide
    have hlog : Nat.log 2 6 = 2 := by decide
    have hdyad : dyadicSize 6 = 8 := by decide
    rw [hcard, hlog, hdyad]
    have h24 : ((2 + 1 : ℕ) : ℝ≥0∞) * ((8 : ℕ) : ℝ≥0∞) = 8 * ((3 : ℕ) : ℝ≥0∞) := by norm_num
    rw [h24, ENNReal.mul_div_cancel_right (by norm_num) (by norm_num)]
  · refine isPPTOn_sampleBlockTrials
      (spec := fun p : ℕ × ℕ => (⟨p.1, fun bits => some (bits.take 2)⟩ :
        BlockRejectionSpec (List Bool)))
      (trials := Prod.snd)
      (ComputableInPolyTime.snd encUnary encUnary)
      (ComputableInPolyTime.fst encUnary encUnary) ?_
    have hbits : ComputableInPolyTime (fun q : (ℕ × ℕ) × List Bool => q.2.take 2)
        (encPair (encPair encUnary encUnary) encBits) encBits := by
      fun_prop
    exact (ComputableInPolyTime.optionSome encBits).comp hbits

/-! ## 3. Non-Boolean finite-product conditional expectations and `CostedProductDerandomizer` -/

/-- Non-uniform rational PMF on `Fin 3` with weights `(1 / 2, 1 / 3, 1 / 6)` realized as a
pushforward of `PMF.uniformOfFintype (Fin 6)`. -/
noncomputable def weightedFin3PMF : PMF (Fin 3) :=
  (PMF.uniformOfFintype (Fin 6)).map fun k : Fin 6 =>
    match k.val with
    | 0 | 1 | 2 => 0
    | 3 | 4 => 1
    | _ => 2

private def fin3Weight6 (i : Fin 3) : ℕ :=
  match i.val with
  | 0 => 3
  | 1 => 2
  | _ => 1

/-- Nonnegative quadratic objective `(3 y₀ + 2 y₁ - 4)²` on `Fin 2 → Fin 3` (valued in `ℕ` via
`Int.natAbs`), attaining `0` at `(0, 2)` (`3 * 0 + 2 * 2 - 4 = 0`). -/
def prodPenaltyNat (y : Fin 2 → Fin 3) : ℕ :=
  ((3 : ℤ) * (y 0).val + 2 * (y 1).val - 4).natAbs ^ 2

/-- Costed conditional-expectation evaluator (scaled by `36`) over `Fin 2 → Fin 3`, charging `1`
tick per product point inspected. -/
def exactCondExp36M (fixed : Finset (Fin 2)) (x : Fin 2 → Fin 3) : TimeM ℕ ℕ :=
  (List.finRange 3).foldlM
    (fun acc0 a0 =>
      (List.finRange 3).foldlM
        (fun acc1 a1 =>
          let y : Fin 2 → Fin 3 := fun j => if j = 0 then a0 else a1
          let term : ℕ :=
            if (0 ∉ fixed ∨ a0 = x 0) ∧ (1 ∉ fixed ∨ a1 = x 1) then
              (if 0 ∈ fixed then 6 else fin3Weight6 a0) *
                (if 1 ∈ fixed then 6 else fin3Weight6 a1) * prodPenaltyNat y
            else 0
          do ✓[1] pure (acc1 + term))
        acc0)
    0

/-- Costed derandomizer over `Fin 2 → Fin 3` with exact scaled conditional expectations. -/
def fin2Fin3Derandomizer : CostedProductDerandomizer (Fin 2) (fun _ => Fin 3) ℕ where
  choices _ := [0, 1, 2]
  condExpM := exactCondExp36M
  compareCost := 1

/-- Concrete execution check on `Fin 2 → Fin 3`: although `(0, 2)` has global minimum `0`, its
`y₀ = 0` slice has conditional expectation `56 / 6 > 14 / 6`, so `fin2Fin3Derandomizer` selects
`(1, 1)` with `prodPenaltyNat = 1` (`36 * 1 < 276 = 36 * E[prodPenaltyNat]`) in `58` `TimeM`
ticks (`29` ticks per coordinate). -/
theorem fin2Fin3Derandomizer_concrete :
    let res := fin2Fin3Derandomizer.derandomizeM [0, 1] (fun _ => 0)
    prodPenaltyNat (fun i => if i = 0 then 0 else 2) = 0 ∧
      prodPenaltyNat res.ret = 1 ∧ res.ret 0 = 1 ∧ res.ret 1 = 1 ∧
      36 * prodPenaltyNat res.ret < (exactCondExp36M ∅ (fun _ => 0)).ret ∧
      res.time = 58 := by
  intro res
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- Tower law and `CostedProductDerandomizer.derandomizeM_spec` check on `PMF.condExpect` for the
non-Boolean product `Fin 2 → Fin 3`. -/
theorem fin2Fin3_tower_and_spec_check :
    (∑ a : Fin 3, (weightedFin3PMF a).toReal *
      PMF.condExpect (fun _ : Fin 2 => weightedFin3PMF)
        (fun y => (prodPenaltyNat y : ℝ)) (insert 0 ∅) (Function.update (fun _ => 0) 0 a) =
    ∑ y : Fin 2 → Fin 3,
      (PMF.pi (fun _ : Fin 2 => weightedFin3PMF) y).toReal * (prodPenaltyNat y : ℝ)) ∧
    (let D : CostedProductDerandomizer (Fin 2) (fun _ => Fin 3) ℝ :=
      { choices := fun _ => [0, 1, 2]
        condExpM := fun fixed x =>
          do ✓[1] pure (PMF.condExpect (fun _ : Fin 2 => weightedFin3PMF)
            (fun y => (prodPenaltyNat y : ℝ)) fixed x)
        compareCost := 1 }
     let out := D.derandomizeM [0, 1] (fun _ => 0)
     (prodPenaltyNat out.ret : ℝ) ≤
       ∑ y : Fin 2 → Fin 3,
         (PMF.pi (fun _ : Fin 2 => weightedFin3PMF) y).toReal * (prodPenaltyNat y : ℝ) ∧
       out.time ≤ 12) := by
  refine ⟨?_, ?_⟩
  · rw [PMF.sum_mul_condExpect_insert (fun _ : Fin 2 => weightedFin3PMF)
      (fun y => (prodPenaltyNat y : ℝ)) (Finset.notMem_empty 0) (fun _ => 0),
      PMF.condExpect_empty]
  · intro D out
    have hcov_fin3 : ∀ i : Fin 2, ∀ a : Fin 3, a ∈ [0, 1, 2] := by decide
    have hcov_fin2 : ∀ i : Fin 2, i ∈ ([0, 1] : List (Fin 2)) := by decide
    obtain ⟨hexp, htime⟩ :=
      D.derandomizeM_spec (fun _ : Fin 2 => weightedFin3PMF)
        (fun y => (prodPenaltyNat y : ℝ)) monotone_id (fun _ _ => rfl)
        (fun i a _ => hcov_fin3 i a) (fun _ => 1) (fun _ _ _ => le_rfl)
        [0, 1] (by decide) hcov_fin2 (fun _ => 0)
    exact ⟨hexp, htime.trans (by decide)⟩

/-! ## 4. Weighted `MaxCut` downstream client: multigraph with parallel edges and self-loop -/

/-- Test multigraph with parallel edges on `{0, 1}` (weights `4` and `2`), triangle edges `(1, 2)`
(weight `5`) and `(0, 2)` (weight `3`), plus a self-loop `(1, 1)` of weight `10`. -/
def testMultigraph : List WeightedEdge :=
  [⟨0, 1, 4⟩, ⟨0, 1, 2⟩, ⟨1, 2, 5⟩, ⟨0, 2, 3⟩, ⟨1, 1, 10⟩]

/-- Concrete verification of `derandomizedCut`, `derandomizedCutM`, `nonLoopWeight`, and the strict
gap between `nonLoopWeight` (`14`) and `totalWeight` (`24`) caused by the self-loop `(1, 1, 10)`. -/
theorem testMultigraph_derandomized_concrete :
    nonLoopWeight testMultigraph = 14 ∧
      loopWeight testMultigraph = 10 ∧
      totalWeight testMultigraph = 24 ∧
      cutWeight testMultigraph (derandomizedCutSide testMultigraph) = 11 ∧
      nonLoopWeight testMultigraph ≤
        2 * cutWeight testMultigraph (derandomizedCutSide testMultigraph) ∧
      (derandomizedCutM testMultigraph).ret = derandomizedCut testMultigraph ∧
      (derandomizedCutM testMultigraph).time = 39 := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, ?_, by decide⟩
  exact ret_derandomizedCutM testMultigraph

/-- Universal `1 / 2`-approximation and plain `ComputableInPolyTime` certificate on weighted
multigraphs. -/
theorem testMultigraph_universal_and_polyTime (σ : ℕ → Bool) :
    cutWeight testMultigraph σ ≤
        2 * cutWeight testMultigraph (derandomizedCutSide testMultigraph) ∧
      ComputableInPolyTime derandomizedCut (encList encWeightedEdge) (encList encNat) :=
  ⟨cutWeight_le_two_mul_derandomizedCutSide testMultigraph σ,
    computableInPolyTime_derandomizedCut⟩

end Cslib.Tests.FairBitRejectionAndCondExp
