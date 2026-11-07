/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/
module
-- upstream: local-only (tests of executed finite residual product transport)
import Complexity.Foundations.Probability.HierarchyProductTransport
import all ComplexityTests.PolynomialBudgetHistory

/-! The supplied history below executes `finiteInput`, with nonzero left and right
errors and a distinct reset source. It is not claimed to be a recursively available
compressed history or a genuine canonical hierarchy instance. Separate semantic tests
check fully correlated errors. Production compressed-call guards remain literal. -/
set_option linter.privateModule false
noncomputable section
open Finset Cslib Cslib.Probability Matrix Matrix.HierarchyParams
open Matrix.HierarchyParams.H4RankEnvironment
open scoped BigOperators
attribute [local instance] Classical.propDecidable
attribute [local implicit_reducible] Matrix
set_option backward.isDefEq.respectTransparency false
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
namespace ProductTransportRegression

private def data (HP : FourthRootHierarchyParams 16 1 16 32 8) : BudgetData HP 5 :=
  { PolynomialBudgetHistory.data HP with binRate := fun _ => rate 0 }
private def request (HP : FourthRootHierarchyParams 16 1 16 32 8) :=
  PolynomialBudgetHistory.request HP
private def estimate {k : ℕ} (q : HierarchyTask.Request k (Fin 3) (ZMod 5)) :
    Environment 5 3 → Matrix (ZMod 5) (ZMod 5) ℝ :=
  match q.task with
  | .baseNormalized _ _ => fun _ _ _ => 2
  | _ => fun _ _ _ => 3
private def history {k : ℕ} (_ : ℕ) (q : HierarchyTask.Request k (Fin 3) (ZMod 5)) :
    Option (BudgetValue 5) := some (.row (estimate q))

-- All three positive calls are actually looked up; the negative is executed once.
-- This is execution against supplied rows, not recursive compressed availability.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) (M : ℕ) :
    ∃ A, (data HP).finiteInput history M .residual (request HP) = some A ∧
      ∀ σ x y, A σ x y = 61 := by
  refine ⟨_, (data HP).finiteInput_residual_of_rows history M (request HP)
    (fun _ => estimate) (by intros; rfl) (by rfl), ?_⟩
  intro σ x y
  have hf (τ : Environment 5 3) (role : Fin 3) (suffix : List (ZMod 5)) (v : ZMod 5) :
      (gridChannel role 0 suffix).retains (channels (1 : ZMod 5)) τ v :=
    PolynomialBudgetHistory.full τ role suffix v
  have hm : BudgetData.midpoint (request HP) = gridChannel 1 0 [] := by
    norm_num [request, PolynomialBudgetHistory.request, BudgetData.midpoint,
      BudgetData.midpointRole, gridChannel]
  have hs : (request HP).source = gridChannel 0 0 [1] := rfl
  have ht : (request HP).terminal = gridChannel 2 0 [2, 3] := rfl
  simp only [data, PolynomialBudgetHistory.data, HierarchyTask.rawPositiveSample,
    HierarchyTask.rawNegativeSample, HierarchyTask.rawRequests,
    HierarchyTask.correctionAtomTask_last HP.k_pos, estimate, hs, ht, hm,
    HierarchyTask.usageRatio, hf]
  have hf' (τ : Environment 5 3) (role : Fin 3) (suffix : List (ZMod 5)) (v : ZMod 5) :
      (⟨role, 1, suffix⟩ : CorrectionRowTask.Channel (Fin 3) (List (ZMod 5))).retains
        (channels (1 : ZMod 5)) τ v := by
    simpa only [gridChannel, rate, pow_zero, inv_one, one_pow] using hf τ role suffix v
  norm_num [rate, gridChannel, hf']

-- Resetting changes the entire source tuple, not just a scalar source rate.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    let Q := HierarchyTask.rawRequests (k := HP.k) 0 0 .residual
      (request HP).source (BudgetData.midpoint (request HP))
      (request HP).terminal ((data HP).binRate 0)
    Q.right.source ≠ Q.direct.source ∧ Q.right.source.suffix = [] ∧
      Q.direct.source.suffix = [1] ∧ Q.left.task.rank <
        (HierarchyTask.RawTask.task (k := HP.k) 0 .residual).rank := by
  dsimp only
  refine ⟨?_, rfl, rfl, HierarchyTask.correctionAtomTask_rank_lt 0 .residual⟩
  intro h
  have ht := congrArg CorrectionRowTask.Channel.role h
  norm_num [HierarchyTask.rawRequests, request, PolynomialBudgetHistory.request,
    BudgetData.midpoint, BudgetData.midpointRole, gridChannel] at ht

-- Satisfiable complete consumer hypotheses, including the own-request allocation.
-- This zero-error boundary is separate from the nonzero execution and scalar tests.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) (M : ℕ) :
    ∃ A, (data HP).finiteInput (fun _ _ => some (.row 0)) M .residual (request HP) = some A ∧
      rowNormPow 4 5 (request HP).source.rate
        (fun σ x => (request HP).source.retains (channels (data HP).padding) σ x)
        (fun σ y => (request HP).terminal.retains (channels (data HP).padding) σ y)
        (fun _ => rowSliceMean
          (fun σ x => (request HP).source.retains (channels (data HP).padding) σ x)
          (fun σ y => (request HP).terminal.retains (channels (data HP).padding) σ y) A) ≤ 0 := by
  have hsource (i : ℕ) (q : HierarchyTask.Request HP.k (Fin 3) (ZMod 5))
      (hc : (i, q) ∈ HierarchyTask.residualErrorCalls (data HP).bins 0
        (request HP).source (BudgetData.midpoint (request HP))
        (request HP).terminal (data HP).binRate) : 0 < q.source.rate := by
    simp only [HierarchyTask.residualErrorCalls, mem_union, mem_biUnion,
      mem_insert, mem_singleton] at hc
    rcases hc with ⟨j, _, hq⟩ | hq
    · rcases hq with hq | hq | hq <;> cases hq <;>
        norm_num [HierarchyTask.rawRequests, request, PolynomialBudgetHistory.request,
          BudgetData.midpoint, gridChannel, rate]
    · cases hq
      norm_num [request, PolynomialBudgetHistory.request, gridChannel, rate]
  have hp := (data HP).finiteInput_residual_root_payment
    (fun _ _ => some (.row 0)) M (request HP) (fun _ _ => 0) (fun _ _ => 0)
    (by intros; rfl) (by rfl) (CA := 0) (CB := 0) (cap := 0) (δ := 0)
    (by norm_num) (by norm_num)
    (by norm_num [request, PolynomialBudgetHistory.request, gridChannel, rate])
    (by norm_num) hsource (by intros; exact ⟨⟨le_rfl, le_rfl⟩, ⟨le_rfl, le_rfl⟩⟩)
    (by intros; exact ⟨rfl, rfl⟩) (by intros; norm_num) (by intros; norm_num)
  dsimp only at hp
  specialize hp (by intros; simp only [rootDistPow_self (by decide : 4 ≠ 0), zero_div, le_refl])
  have hz (i : ℕ) : HierarchyTask.rawPositiveSample (channels (data HP).padding) 0 i
      .residual (request HP).source (BudgetData.midpoint (request HP)) (request HP).terminal
      ((data HP).binRate i) (fun (_ : HierarchyTask.Request HP.k (Fin 3) (ZMod 5)) => 0)
      = (0 : Matrix (ZMod 5) (ZMod 5) ℝ) := by
    funext x y
    simp only [HierarchyTask.rawPositiveSample, Matrix.zero_apply, mul_zero, sum_const_zero,
      add_zero]
  have hn : HierarchyTask.rawNegativeSample (channels (data HP).padding) 0 0
      .residual (request HP).source (BudgetData.midpoint (request HP)) (request HP).terminal
      ((data HP).binRate 0) (fun (_ : HierarchyTask.Request HP.k (Fin 3) (ZMod 5)) => 0)
      = (0 : Matrix (ZMod 5) (ZMod 5) ℝ) := by
    funext x y
    simp only [HierarchyTask.rawNegativeSample, HierarchyTask.rawRequests,
      Matrix.zero_apply, mul_zero]
  simpa only [hz, hn, Pi.zero_apply, Matrix.zero_apply, sum_const_zero, sub_zero,
    Nat.cast_ofNat] using hp


-- Finite semantic correlated errors: every child depends on the same coin.
-- Both terms in AL*(AR-CR)+(AL-CL)*CR and the direct perturbation are nonzero.
example (coin : Bool) :
    let a : ℝ := if coin then 2 else 1
    let AL := a + 1
    let AR := 2 * a
    let CL : ℝ := 1
    let CR : ℝ := 1
    AL * AR - CL * CR = AL * (AR - CR) + (AL - CL) * CR ∧
      AL ≠ 0 ∧ AR ≠ CR ∧ AL ≠ CL ∧ a ≠ 0 := by
  cases coin <;> norm_num

-- A finite own-request scalar IH can be nonzero and still hold with equality.
-- Both rows share one coin, so this check supplies no independence premise.
example :
    let X : Bool → Unit → Prop := fun _ _ => True
    let A : Bool → Unit → Unit → ℝ := fun σ _ _ => if σ then 16 else 1
    let C : Bool → Unit → Unit → ℝ := fun _ _ _ => 1
    rootDistPow 4 1 1 X X A C = 1 / 2 := by
  have h16 : (16 : ℝ) ^ (4⁻¹ : ℝ) = 2 := by
    convert Real.pow_rpow_inv_natCast (x := (2 : ℝ)) (n := 4)
      (by norm_num) (by decide) using 1; norm_num
  norm_num [rootDistPow, rowNormPow, h16, Fintype.sum_bool, Finset.expect]

-- All literal bin calls and the negative call remain strictly lower-budget.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) (M : ℕ) (hM : 0 < M) :
    (∀ i ∈ (data HP).bins, (data HP).binBudget M i (request HP) < M) ∧
      (data HP).childBudget M < M :=
  ⟨fun i _ => (data HP).binBudget_lt hM i (request HP), (data HP).childBudget_lt hM⟩

-- Invalid terminal exponents are rejected independently of child availability.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) (M bin k : ℕ) (ζ floor : ℝ)
    (hk : (request HP).terminal.rate ≠ rate k) :
    (data HP).compressedBin M bin k ζ floor (request HP) = none := by
  unfold BudgetData.compressedBin
  rw [ite_eq_left (Or.inr (Or.inr hk))]

-- Equal-budget groups and the literal residual zero boundary execute no children.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    (data HP).sample (fun _ _ => none) 0 .residual (request HP) (some 0) = some 0 := by
  simp only [BudgetData.sample, ↓reduceIte]
example (HP : FourthRootHierarchyParams 16 1 16 32 8) (d : ℕ) :
    (data HP).pairedSample (fun _ _ => none) 0 d .residual (request HP) (some 0) = some 0 := by
  simp [BudgetData.pairedSample, LogSpaceEstimation.lastBudget]
example (HP : FourthRootHierarchyParams 16 1 16 32 8) (bin k : ℕ) (ζ floor : ℝ) :
    (data HP).compressedBin 0 bin k ζ floor (request HP) = none := by
  simp only [BudgetData.compressedBin, true_or, ↓reduceIte]

end ProductTransportRegression
