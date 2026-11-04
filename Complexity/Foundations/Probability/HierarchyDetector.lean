/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
module
-- upstream: candidate

public import Complexity.Foundations.Probability.HierarchySourceSampling
public import Complexity.Foundations.Probability.PilotDetectorTransport

/-!
# Source-aware detection on the full hierarchy environment

The score is evaluated on the environment reconstructed from the actual terminal split.
All source and spectator coordinates remain integrated arguments. The fourth-moment
transport retains the literal width, rate and terminal-density factors. Both the initial
pilot client and the shared statistical-budget evaluator use this operation.

## Main definitions

* `environmentDetector`: detector on the actual integrated child environment.

## Main results

* `environmentDetector_row_moment`: transport from full-environment score error.
-/
public section
noncomputable section
open Finset Cslib Cslib.Probability
open scoped BigOperators
namespace Matrix.HierarchyParams.H4RankEnvironment
attribute [local instance] Classical.propDecidable
variable {P J : ℕ} [Fact P.Prime]

/-- Evaluate a score on precisely the environment described by the integration variables.
The source rank resets to the terminal rate; roles and copy suffixes are preserved. -/
@[expose] def environmentDetector
    {V : Type} [Fintype V] {k : ℕ}
    (HP : FourthRootHierarchyParams 16 1 16 32 8) (D : ZMod P) (ident : V → ZMod P)
    (r : HierarchyTask.Request k (Fin J) (ZMod P)) (hr : Admissible r)
    (A : Environment P J → Matrix V V ℝ) : V → ℝ :=
  PilotRowRecipe.sourceDetector HP.toHierarchyParams (stageSource D ident r hr)
    (splitTerminal D ident r) (fun s t => A ((terminalSplit r.terminal.role).symm (s, t)))

/-- Full-coordinate finite Fubini transports the literal detector payment. No
full-environment atom is extracted, and no child coordinate is discarded. -/
theorem environmentDetector_row_moment
    {V : Type} [Fintype V] {k : ℕ}
    (HP : FourthRootHierarchyParams 16 1 16 32 8) (D : ZMod P) (ident : V → ZMod P)
    (r : HierarchyTask.Request k (Fin J) (ZMod P)) (hr : Admissible r)
    {N u π : ℝ} (hN : 0 < N) (hu : 0 < u) (hf : 0 < r.terminal.rate) (hπ : 0 < π)
    (hY : ∀ y, π ≤ (dens {t | splitTerminal D ident r t y} : ℝ))
    (A B : Environment P J → Matrix V V ℝ) :
    rowNormPow 4 N u
      (fun σ x => r.source.retains (channels D) σ (ident x))
      (fun σ y => r.terminal.retains (channels D) σ (ident y))
      (fun _ _ y => environmentDetector HP D ident r hr A y -
        environmentDetector HP D ident r hr B y) ≤
    (Fintype.card V : ℝ) * r.terminal.rate / (u * π) *
      rowNormPow 4 N r.terminal.rate
        (fun σ x => ({r.source with rate := r.terminal.rate}).retains
          (channels D) σ (ident x))
        (fun σ y => r.terminal.retains (channels D) σ (ident y))
        (fun σ x y => A σ x y - B σ x y) := by
  have h := PilotRowRecipe.sourceDetector_row_moment_transport HP.toHierarchyParams
    (stageSource D ident r hr) (splitTerminal D ident r)
    (fun σ x => r.source.retains (channels D) σ (ident x))
    (fun σ y => r.terminal.retains (channels D) σ (ident y))
    hN hu hf hπ hY
    (fun (_ : Environment P J) s t => A ((terminalSplit r.terminal.role).symm (s, t)))
    (fun (_ : Environment P J) s t => B ((terminalSplit r.terminal.role).symm (s, t)))
  apply h.trans_eq
  congr 1
  unfold rowNormPow
  congr 1
  rw [← univ_product_univ, expect_product]
  simp only [Fintype.expect_const]
  apply Fintype.expect_equiv (terminalSplit r.terminal.role).symm
  intro p
  simp [hr.1, stageSource, splitTerminal, terminalSplit, coordinate,
    CorrectionRowTask.Channel.retains, channels]

end Matrix.HierarchyParams.H4RankEnvironment
