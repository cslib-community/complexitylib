/-
Copyright (c) 2026 Anton Kovsharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anton Kovsharov
-/

import Complexity.Computability.PolyTime.BooleanAnalysis.SparsePolyCounter

/-!
# Tests for the heavy-branched sparse `𝔽₂` polynomial-system zero counter

Kernel-checked (`decide`, `fun_prop`, `NativeCertificate`) regression tests for
`Cslib.Complexity.SubexponentialSAT.SparsePolyCounter` (§5.5 and §6.3 of [OpenAI2026ETH]).
-/

namespace Cslib.Complexity.SubexponentialSAT.SparsePolyCounter.Tests

open Finset Cslib Cslib.BitString Cslib.Complexity Cslib.GenericRAM Turing.MultiTapeTM
open Cslib.GenericRAM.HeavyBranchFold Cslib.Complexity.SubexponentialSAT.SparsePolyCounter

/-- Poison branch oracle returning `999999` if invoked on `n' < 20`, verifying fallback guards. -/
private def poisonBranchEval (inp : BranchEvalInput) : ℕ :=
  if inp.1.1 < 20 then 999999 else rootCount inp.1.1 inp.2.2.2

private theorem poisonBranchEval_exact (n' : ℕ) (eqs' : List (List (List ℕ)))
    (h : checkBranchFeasible 0 (n', eqs') = true) :
    poisonBranchEval (prepareBranchEvalInput (n', eqs')) = rootCount n' eqs' := by
  have h20 : 20 ≤ n' := (feasible_of_checkBranchFeasible h).2.2.2.twenty_le
  unfold poisonBranchEval prepareBranchEvalInput; simp only [Nat.not_lt.mpr h20, ↓reduceIte]

-- 1. Empty (`2 ^ n`, incl. `n = 0`), tautology `0 = 0` (`[[]]`), and `1 = 0` (`[[[]]]`).
example : countSparsePolySystem 0 0 poisonBranchEval (0, (0, 1, 1), []) = 1 ∧
    countSparsePolySystem 0 0 poisonBranchEval (4, (0, 2, 1), []) = 16 ∧
    countSparsePolySystem 10 0 poisonBranchEval (4, (0, 2, 1), []) = 16 ∧
    countSparsePolySystem 0 0 poisonBranchEval (3, (0, 1, 1), [[]]) = 8 ∧
    countSparsePolySystem 0 0 poisonBranchEval (3, (0, 1, 1), [[[]]]) = 0 ∧
    countSparsePolySystem 10 0 poisonBranchEval (3, (0, 1, 1), [[[]]]) = 0 := by decide

-- 2. Single-equation sparse `𝔽₂` system `x₀ ⊕ x₁ x₂ = 0` on `n = 4` (`S = [0, 1, 2]`, 8 branches).
private def singleEq4 : List (List (List ℕ)) := [[[0], [1, 2]]]
example : heavyVarList 4 0 singleEq4 = [0, 1, 2] ∧
    checkTopFeasible 0 (4, (2, 1, 0), singleEq4) = true ∧
    countSparsePolySystem 0 0 poisonBranchEval (4, (2, 1, 0), singleEq4) = 8 ∧
    rootCount 4 singleEq4 = 8 := by decide

-- 3. Multi-equation 4-variable system (`S = [1, 3]`, `.tautology`/`.contradiction`/`.reduced`).
private def multiSys4 : List (List (List ℕ)) := [[[1], [1, 3]], [[0, 3], [2, 3], [0, 1, 3]]]
example : heavyVarList 4 1 multiSys4 = [1, 3] ∧
    checkTopFeasible 0 (4, (3, 2, 1), multiSys4) = true ∧
    countSparsePolySystem 0 0 poisonBranchEval (4, (3, 2, 1), multiSys4) = 8 ∧
    commonZeroCount univ (fun i : Fin multiSys4.length => toFinsetEquation 4 multiSys4[i]) = 8 :=
  ⟨by decide, by decide, by decide, (countSparsePolySystem_eq_commonZeroCount (N₀_top := 0)
    poisonBranchEval_exact (4, (3, 2, 1), multiSys4)
    (checkCanonicalSystem_eq_true_iff.mp (by decide))
    (checkVarsLt_eq_true_iff.mp (by decide))).symm.trans (by decide)⟩

-- 4. Multi-equation 5-variable cubic system (`S = [4]`) + `mkPaperSparseInput` + scope metrics.
private def cubicSys5 : List (List (List ℕ)) :=
  [[[0, 1, 4], [1, 2], []], [[2, 3, 4]], [[0, 3], [3, 4]]]
example : heavyVarList 5 2 cubicSys5 = [4] ∧ checkTopFeasible 0 (5, (3, 2, 2), cubicSys5) = true ∧
    countSparsePolySystem 0 0 poisonBranchEval (5, (3, 2, 2), cubicSys5) = 6 ∧
    checkTopFeasible 2 (mkPaperSparseInput 4 3 multiSys4) = true ∧
    countSparsePolySystem 2 0 poisonBranchEval (mkPaperSparseInput 4 3 multiSys4) = 8 ∧
    scopeWidthOn 4 [[0, 3], [2, 3], [0, 1, 3]] = 4 ∧ sysMaxDegree multiSys4 = 3 ∧
    branchMaxFactorIncidence 4 multiSys4 = 3 ∧ branchMaxFactorWidth 4 multiSys4 = 4 ∧
    branchAugmentedIncidence 4 multiSys4 = 10 := by decide

-- 5. Fallback boundaries: small `n`, excess heavy variables, non-canonical / out-of-range inputs.
example : checkTopFeasible 5 (4, (3, 2, 1), multiSys4) = false ∧
    countSparsePolySystem 5 0 poisonBranchEval (4, (3, 2, 1), multiSys4) = 8 ∧
    checkTopFeasible 0 (4, (3, 3, 1), multiSys4) = false ∧
    countSparsePolySystem 0 0 poisonBranchEval (4, (3, 3, 1), multiSys4) = 8 ∧
    checkCanonicalSystem [[[1, 0]]] = false ∧ checkCanonicalSystem [[[0], [0]]] = false ∧
    countSparsePolySystem 0 0 poisonBranchEval (2, (2, 1, 1), [[[1, 0]]]) = 3 ∧
    countSparsePolySystem 0 0 poisonBranchEval (2, (1, 1, 1), [[[0], [0]]]) = 4 ∧
    checkVarsLt 2 [[[3]]] = false ∧
    countSparsePolySystem 0 0 poisonBranchEval (2, (1, 1, 1), [[[3]]]) = 4 := by decide

-- 6. Context-carrying §6.3 CNF parity-system wrapper (`countContextParity` = `numPassing`).
private def φ2Fin : Logic.PL.CNF (Fin 3) :=
  [[(⟨0, by decide⟩, true), (⟨1, by decide⟩, false)],
   [(⟨1, by decide⟩, true), (⟨2, by decide⟩, true)]]
private abbrev TestCtx := (ℕ × ℕ × ℕ) × Logic.PL.CNF ℕ
private def ctx2 : TestCtx := ((3, 1, 1), φ2Fin.map (List.map fun l => ((l.1 : ℕ), l.2)))
private def rows2 : List (List Bool) := [[true, false], [false, true]]
example : countContextParity 0 0 2 (fun c : TestCtx => c.1.1) (fun c => c.1.2.1) (fun c => c.1.2.2)
    Prod.snd poisonBranchEval (ctx2, rows2) =
      numPassing φ2Fin.violations (rows2.map (ofList φ2Fin.length)) ∧
    numPassing φ2Fin.violations (rows2.map (ofList φ2Fin.length)) = 4 :=
  ⟨countContextParity_eq_numPassing (nOf := fun c : TestCtx => c.1.1)
    (sDivOf := fun c => c.1.2.1) (b₀Of := fun c => c.1.2.2) (φOf := Prod.snd) (N₀_top := 0)
    (k_deg := 2) poisonBranchEval_exact ctx2 φ2Fin rows2 rfl (fun c hc => by
      rw [φ2Fin] at hc; cases hc with
      | head => decide
      | tail _ h => cases h with | head => decide | tail _ h => nomatch h), by decide⟩

-- 7. Compositional `ComputableInPolyTime`, `PolyBounded`, and `GreedyContext` certificate checks.
example : ComputableInPolyTime prepareBranchEvalInput
    (encPair encUnary (encList (encList (encList encNat)))) encBranchEvalInput := by fun_prop
example : ComputableInPolyTime (checkTopFeasible 20) encSparseSystemInput encBool := by fun_prop
private noncomputable def zeroBranchCert :
    NativeCertificate (fun _ : BranchEvalInput => 0) encBranchEvalInput encNat :=
  NativeCertificate.ofPolyTime (.of_tidy (.const 0))
example : PolyBounded (fun inp => (encSparseSystemInput inp).length)
    (sparsePolyCounterCertificate 20 20 zeroBranchCert (fun _ _ _ => Nat.zero_le _)).space :=
  polyBounded_sparsePolyCounterCertificate_space 20 20 zeroBranchCert
    (fun _ _ _ => Nat.zero_le _) (NativeCertificate.ofPolyTime_isPolynomial _).2
private def encTestCtx : TestCtx ↪ List Bool :=
  encPair (encPair encUnary (encPair encNat encNat)) encCNF
private noncomputable def ctxParityCert :
    NativeCertificate (countContextParity 20 20 3 (fun c : TestCtx => c.1.1) (fun c => c.1.2.1)
      (fun c => c.1.2.2) Prod.snd (fun _ => 0)) (encPair encTestCtx (encList encBits)) encNat :=
  contextParityCertificate (encC := encTestCtx) 20 20 3
    (by unfold encTestCtx; fun_prop) (by unfold encTestCtx; fun_prop)
    (by unfold encTestCtx; fun_prop) (by unfold encTestCtx; fun_prop)
    zeroBranchCert (fun _ _ _ => Nat.zero_le _)
noncomputable example :
    NativeCertificate (fun a : TestCtx × ℕ × ℕ × ℕ × List (List Bool) =>
      Logic.PL.CNF.greedyParityRows
        (fun rows => countContextParity 20 20 3 (fun c : TestCtx => c.1.1)
          (fun c => c.1.2.1) (fun c => c.1.2.2) Prod.snd (fun _ => 0) (a.1, rows))
        a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2)
      (Logic.PL.CNF.GreedyContext.encGreedyInput encTestCtx) (encList encBits) :=
  Logic.PL.CNF.GreedyContext.greedyCertificate ctxParityCert

end Cslib.Complexity.SubexponentialSAT.SparsePolyCounter.Tests
