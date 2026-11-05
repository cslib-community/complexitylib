/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/
module
-- upstream: local-only (tests of conditional residual RAW noise)
import Complexity.Foundations.Probability.HierarchyRawNoise
import all ComplexityTests.HierarchyRawExecution

/-!
Actual nonzero signed residual execution consumes the new conditional-noise seam.
The literal zero boundary and an empty prefix need no manufactured recursive IH.
A separate two-point finite-length walk checks nonzero centered noise and correlation;
it is not asserted to be the production H4 graph or a successful recursive evaluator.
The existing production fixture and proof patterns are adapted from Samuel Schlesinger.
-/
set_option linter.privateModule false
noncomputable section
open Finset Cslib Cslib.Probability Cslib.RowCompression Matrix Matrix.HierarchyParams
open Matrix.HierarchyParams.H4RankEnvironment
open Matrix.HierarchyParams.H4RankEnvironment.BudgetData
open Matrix.HierarchyParams.H4RankEnvironment.NormalizedMoments
open RawExecutionRegression
open scoped BigOperators
attribute [local instance] Classical.propDecidable
attribute [local implicit_reducible] Matrix
set_option backward.isDefEq.respectTransparency false
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

-- A supplied nonzero history executes both positive product rays and one negative
-- ray. The new decoder consumer uses the ACTUAL production groups (zero, eleven).
example (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (G : Matrix (ZMod 5) (ZMod 5) ℝ) (hG : ∀ x y, 0 ≤ G x y) :
    let D := data HP
    let r := request HP
    let A := fun i bin => if i = 0 then 0 else amplitude bin
    D.completedGroup history 2 1 .residual r = some (fun _ _ _ => 11) ∧
      rowNormPow 4 5 r.source.rate
        (retainedMask 0 (side 5 0) D.padding [1])
        (retainedMask 2 (side 5 0) D.padding [2, 3])
        (actualNoiseEntry 0 2 (side 5 0) (side 5 0) (side 5 0) D.padding [1] [2, 3] 0 G
          (firstSignalIncrement (D.rawFirstPrefixes history 2 .residual r) 0
            (fun _ _ _ _ => 7)) 0 0 1) ≤
        D.rawRelativeNoiseBudget 2 r 0 2 (by decide) 0 0 [1] [2, 3]
          (fun i σ x y => ((D.rays .residual).map (fun bin => A i bin σ x y)).sum) G 2 := by
  dsimp only
  constructor
  · exact group_one HP
  · apply (data HP).rawFirstPrefixes_actualNoiseEntry history 2 (request HP)
      0 2 (by decide) 0 0 [1] [2, 3] rfl rfl rfl
      (fun i bin => if i = 0 then 0 else amplitude bin) 1 (by decide) _ G hG
    intro i hi bin _
    have hi' : i = 0 ∨ i = 1 := by norm_num at hi; omega
    rcases hi' with rfl | rfl
    · simpa [dyadicSlack] using pair_two HP bin
    · simpa [dyadicSlack] using pair_one HP bin

-- Even with no available positive-budget history, a completely exhausted group
-- has literal zero paired rays. The negative ray is still present in the residual.
example (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (hist : ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod 5) → Option (BudgetValue 5)) :
    (data HP).completedGroup hist 2 2 .residual (request HP) =
      some (conditionalWalk
        (X 0 (side 5 0) (CopyPadding.identifier (data HP).padding [1]))
        (Y 2 (side 5 0) (CopyPadding.identifier (data HP).padding [2, 3]))
        (graph 0 2 (by decide) (side 5 0) (side 5 0) (side_le 5 0) (side_le 5 0)
          (CopyPadding.identifier (data HP).padding [1])
          (CopyPadding.identifier (data HP).padding [2, 3]))
        (fun _ _ => (data HP).steps 2 (request HP) 2) 0) := by
  have hp (bin : Option ℕ) : (data HP).pairedSample hist 2 2 .residual (request HP) bin =
      some 0 := by
    unfold BudgetData.pairedSample
    rw [scale]
    norm_num [LogSpaceEstimation.lastBudget, LogSpaceEstimation.scaleCutoff,
      data, PolynomialBudgetHistory.data]
  have h := (data HP).completedGroup_residual_of_paired hist 2 2 (request HP)
    0 2 (by decide) 0 0 [1] [2, 3] rfl rfl (fun _ => 0) (fun bin _ => hp bin)
  have hin : (fun σ x y => (((data HP).rays .residual).map
      (fun _ => (0 : Environment 5 3 → Matrix (ZMod 5) (ZMod 5) ℝ) σ x y)).sum) = 0 := by
    funext σ x y
    simp
  rw [hin] at h
  exact h

-- The empty prefix has exactly zero noise obligation, at any budget or target.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) (M : ℕ)
    (G : Matrix (ZMod 5) (ZMod 5) ℝ)
    (A : ℕ → Environment 5 3 → Matrix (ZMod 5) (ZMod 5) ℝ) :
    (data HP).rawRelativeNoiseBudget M (request HP) 0 2 (by decide) 0 0 [1] [2, 3]
      A G 0 = 0 := by
  simp [rawRelativeNoiseBudget]

-- The same random atom occurs in both groups: after three genuine identity-walk
-- steps their centered sum has fourth moment 16, not the separate-moment sum 2.
example :
    let X := fun (_ : Bool) (_ : Unit) => True
    let graphV := fun (_ _ : Unit) => (⟨id, fun _ => rfl⟩ : RotationMap
      (RetainedPairSlice X X () ()) Unit)
    let F := fun (σ : Bool) (_ _ : Unit) => if σ then (1 : ℝ) else -1
    let W := conditionalWalk X X graphV (fun _ _ => 3) F
    rowNormPow 4 1 1 X X (fun σ x y => W σ x y + W σ x y -
      rowSliceMean X X (fun τ u v => W τ u v + W τ u v) x y) = 16 ∧
      rowNormPow 4 1 1 X X F + rowNormPow 4 1 1 X X F = 2 := by
  dsimp only
  let X := fun (_ : Bool) (_ : Unit) => True
  let graphV := fun (_ _ : Unit) => (⟨id, fun _ => rfl⟩ : RotationMap
    (RetainedPairSlice X X () ()) Unit)
  have hw (n : ℕ) (f : RetainedPairSlice X X () () → ℝ) :
      ((graphV () ()).walk ^ n) f = f := by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [pow_succ', Module.End.mul_apply, ih]
      funext σ
      simp [RotationMap.walk_apply, RotationMap.neighbor, graphV]
  dsimp only [X, graphV] at hw
  simp only [conditionalWalk, hw]
  norm_num [rowNormPow, rowSliceMean, expect_eq_sum_div_card, Fintype.sum_bool]
