/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
module
-- upstream: local-only (tests of canonical hierarchy target transport)

import Complexity.Computability.LogSpaceDerandomization.HierarchyCanonicalTargets
import all ComplexityTests.HierarchySourceSampling

/-! Nonzero true targets across actual residual request roles, different suffixes and
unequal source/rank/usage rates. These are target/one-child mean regressions, not a
shared-midpoint residual mean or perturbed-child error theorem. -/
set_option linter.privateModule false

namespace CanonicalRegression
open Finset Cslib Cslib.Probability Matrix Matrix.HierarchyParams
  Matrix.HierarchyParams.H4RankEnvironment
open scoped BigOperators
noncomputable section
local instance (p : Prop) : Decidable p := Classical.propDecidable p
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
variable (HP : FourthRootHierarchyParams 16 1 16 32 8)

/-- The actual residual request tuple; no endpoint or midpoint is baked into a child. -/
def requests := HierarchyTask.rawRequests (k := HP.k) 0 0 .residual
  (gridChannel (P := 5) (0 : Fin 3) 2 [1]) (gridChannel 1 1 [2])
  (gridChannel 2 3 [3]) (rate 1)

def leftRequest := (requests HP).left

def negativeRequest := (requests HP).negative.getD (leftRequest HP)

example : (requests HP).negative = some (negativeRequest HP) := rfl

lemma left_admissible : Admissible (leftRequest HP) := by
  exact ⟨by change (0 : Fin 3) ≠ 1; decide, rfl, rfl⟩

lemma negative_admissible : Admissible (negativeRequest HP) := by
  exact ⟨by change (0 : Fin 3) ≠ 2; decide, rfl, rfl⟩

/-- Both correction targets agree although their terminal roles/suffixes and usages differ.
The ambient role product is unchanged; each actual split keeps its spectators. -/
example (C : Matrix Unit Unit ℝ) (i : ℕ) :
    HP.toHierarchyParams.correctionIter
      (stageSource 2 SingleRegression.identifier (leftRequest HP) (left_admissible HP))
      (splitTerminal 2 SingleRegression.identifier (leftRequest HP)) (rate 1) C i =
    HP.toHierarchyParams.correctionIter
      (stageSource 2 SingleRegression.identifier (negativeRequest HP) (negative_admissible HP))
      (splitTerminal 2 SingleRegression.identifier (negativeRequest HP)) (rate 1) C i := by
  exact stage_correctionIter_eq_of_terminal_rate HP 2 SingleRegression.identifier
    (leftRequest HP) (left_admissible HP) (negativeRequest HP) (negative_admissible HP)
    (by decide) rfl C i

/-- Reset the whole source tuple exactly as the actual right request does. -/
def resetRequest := { negativeRequest HP with source := (requests HP).right.source }

lemma reset_admissible : Admissible (resetRequest HP) := by
  exact ⟨by change (1 : Fin 3) ≠ 2; decide, rfl, rfl⟩

/-- True targets survive release of the old source role, rate and suffix to the midpoint.
This tests deterministic target transport, not independence of stochastic children. -/
example (C : Matrix Unit Unit ℝ) (i : ℕ) :
    HP.toHierarchyParams.correctionIter
      (stageSource 2 SingleRegression.identifier (negativeRequest HP) (negative_admissible HP))
      (splitTerminal 2 SingleRegression.identifier (negativeRequest HP)) (rate 1) C i =
    HP.toHierarchyParams.correctionIter
      (stageSource 2 SingleRegression.identifier (resetRequest HP) (reset_admissible HP))
      (splitTerminal 2 SingleRegression.identifier (resetRequest HP)) (rate 1) C i := by
  exact stage_correctionIter_eq_of_terminal_rate HP 2 SingleRegression.identifier
    (negativeRequest HP) (negative_admissible HP) (resetRequest HP) (reset_admissible HP)
    (by decide) rfl C i

/-- This is a positive genuine correction target, with nontrivial radix-two padding and
a nonconstant rank channel. Thus the source-reset regression is not only a zero identity. -/
example : 0 < HP.toHierarchyParams.correctionIter
    (stageSource 2 SingleRegression.identifier (leftRequest HP) (left_admissible HP))
    (splitTerminal 2 SingleRegression.identifier (leftRequest HP)) (rate 1)
    (fun _ _ => rate 1 : Matrix Unit Unit ℝ) 1 () () := by
  have h := SourceRegression.positive_target HP
  erw [stage_correctionIter_eq_canonical HP 1 SingleRegression.identifier
    (SourceRegression.request HP) (SourceRegression.admissible HP) (by norm_num)] at h
  erw [← show (leftRequest HP).terminal.rate = rate 1 from rfl,
    stage_correctionIter_eq_canonical HP 2 SingleRegression.identifier
      (leftRequest HP) (left_admissible HP) (by decide)]
  exact h

/-- The complete actual one-child mean has the canonical target with source/rank/usage
exponents 2/1/3, different suffixes and a free spectator coordinate. -/
example :
    (𝔼 σ ∈ ({σ : Environment 5 3 | (SourceRegression.request HP).source.retains
      (channels 1) σ (SingleRegression.identifier ())} : Finset _),
      ((SourceRegression.request HP).terminal.rate / (dens {σ : Environment 5 3 |
        (SourceRegression.request HP).usage.retains (channels 1) σ
          (SingleRegression.identifier ())} : ℝ)) *
      correctionRequest 1 SingleRegression.identifier (SourceRegression.request HP)
        (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff HP.ρ HP.toHierarchyParams.atomCutoff
        HP.γ HP.K ⌈4 * (1 + 32 * HP.R)⌉₊
        (fun _ => stageRaw HP 1 SingleRegression.identifier (SourceRegression.request HP)
          (SourceRegression.admissible HP) (fun _ _ => rate 1) 0)
        (sourcePreparation HP 1 SingleRegression.identifier (SourceRegression.request HP)
          (SourceRegression.admissible HP) (fun _ _ => rate 1) 0)
        (fun _ => stageMaximum HP 1 SingleRegression.identifier (SourceRegression.request HP)
          (SourceRegression.admissible HP) (fun _ _ => rate 1)) σ () ()) =
    HP.toHierarchyParams.correctionIter (canonicalChannel SingleRegression.identifier (rate 1))
      (canonicalChannel SingleRegression.identifier (rate 1)) (rate 1)
      (fun _ _ => rate 1) 1 () () := by
  exact source_request_mean_canonical HP 1 SingleRegression.identifier
    (SourceRegression.request HP) (SourceRegression.admissible HP) (by norm_num)
    SingleRegression.identifier_injective SourceRegression.horizon (k := 1) (s := 2) (u := 3)
    (by decide) (by decide) rfl rfl rfl (fun _ _ => rate 1) (by intros; norm_num [rate])
    (by intro x; norm_num [Matrix.mulVec, dotProduct, rate]) (by intros; rfl) HP.k_pos () ()

/-- Zero correction iteration still has literal zero target after transport. -/
example : stageRaw HP 2 SingleRegression.identifier (leftRequest HP) (left_admissible HP)
    (fun _ _ => rate 1 : Matrix Unit Unit ℝ) 0 = fun _ _ => rate 1 := by
  erw [stageRaw_eq_canonical HP 2 SingleRegression.identifier
    (leftRequest HP) (left_admissible HP) (by decide)]
  ext x y
  change rate 1 + ∑ _ : Unit, (0 : ℝ) * rate 1 = rate 1
  simp

/-- Conditioning one Boolean coordinate leaves the other two as free spectators. -/
example : (𝔼 σ ∈ ({σ : Fin 3 → Bool | σ 1 = true} : Finset _),
    if σ 1 then (7 : ℝ) else -2) = 7 := by
  rw [expect_pi_eval_filter (1 : Fin 3) (fun b : Bool => b = true)
    (fun b => if b then (7 : ℝ) else -2)]
  norm_num [Finset.filter_insert, Finset.filter_singleton]

/-- Empty conditioning is transported exactly, with finite expectation zero. -/
example : (𝔼 σ ∈ ({_σ : Fin 3 → Bool | False} : Finset _),
    if σ 1 then (7 : ℝ) else -2) = 0 := by
  simp

end
end CanonicalRegression
