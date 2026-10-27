/-
Copyright (c) 2026 Anton Kovsharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anton Kovsharov
-/

module

public import Complexity.Init
public import Complexity.Computability.PolyTime.CNF.BranchedSparseCNFCounter
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-! # Kernel-checked tests for `Cslib.Complexity.BranchedSparseCNFCounter` -/

@[expose] public section

namespace ComplexityTests.Computability.PolyTime.CNF.BranchedSparseCNFCounter

open Cslib.Complexity Cslib.Complexity.BranchedSparseCNFCounter Cslib.GenericRAM
open Cslib.Complexity.SparseCNFLeafCounter Cslib.Complexity.SubexponentialSAT
open Cslib.Complexity.SubexponentialSAT.SparsePolyCounter Cslib.GenericRAM.ExhaustiveCountFallback
open Cslib.Logic.PL Cslib.Logic.PL.CNF Cslib.Logic.PL.ClauseSet.Sparsification Turing.MultiTapeTM
open Turing.MultiTapeTM.Universal (encUnit)

local notation "encLeafIn" => encPair (encPair encUnit encUnary) encCNF

/-- Concrete branch evaluator executing streaming `countSystemExhaustive` on `(n', eqs')`. -/
abbrev exhBranchEval (inp : BranchEvalInput) : ℕ := countSystemExhaustive (inp.1.1, inp.2.2.2)
private abbrev declExh (k a b c : ℕ) := branchedSparseCNFDeclaredCounter k a b c exhBranchEval
private abbrev leafExh (k a b c : ℕ) := branchedSparseCNFLeafCounter k a b c exhBranchEval

-- 1. `N = 0` boundary (`[]` and `[[]]`, exercising the dense `B * N < ψ.length` outer guard).
example : declExh 3 0 0 0 (((), 0), []) = 1 ∧ leafExh 3 0 0 0 (((), 0), []) = 1 ∧
    declExh 3 0 0 0 (((), 0), [[]]) = 0 ∧ leafExh 3 0 0 0 (((), 0), [[]]) = 0 ∧
    ([[]] : CNF ℕ).length = leafOccBound 3 0 * 0 + 1 ∧
    leafDensityRatio 3 0 * 0 < ([[]] : CNF ℕ).length := by decide

-- 2. Repeated unit clauses exceeding `leafDensityRatio 3 2 * 2` on `N = 2`.
private theorem ratio_three_of_div {N : ℕ} (h : leafSearchDivisor N = 1) :
    leafDensityRatio 3 N = 525315 := by
  have hM : leafThresholdBase 3 N = 2 ^ 9 := by
    unfold leafThresholdBase; rw [h]
    exact countingThresholdBase_eq_two_pow (k := 3) (B := 1) (m := 9)
      (by decide) (by decide) (by decide) (by decide)
  unfold leafDensityRatio leafOccBound; rw [hM]; decide
theorem leafDensityRatio_three_two : leafDensityRatio 3 2 = 525315 :=
  ratio_three_of_div (by unfold leafSearchDivisor; rw [SparseCountingScale.numGroups_of_lt_three
    (by decide : 2 < 3)]; decide)
private def unit0 : CNF ℕ := [[(0, true)]]
private def denseUnits2 : CNF ℕ := List.replicate 1050631 [(0, true)]

example : leafDensityRatio 3 2 * 2 < denseUnits2.length ∧
    declExh 3 0 0 0 (((), 2), denseUnits2) = 2 ∧ leafExh 3 0 0 0 (((), 2), denseUnits2) = 1 := by
  have hw : ∀ c ∈ denseUnits2, c.length ≤ 3 := fun c hc => by
    rw [(List.mem_replicate.mp hc).2]; decide
  have hvset : denseUnits2.vars.toFinset = unit0.vars.toFinset := by
    ext v; simp only [denseUnits2, unit0, List.mem_toFinset, CNF.mem_vars, List.mem_replicate,
      ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, true_and, exists_eq_left, List.mem_singleton]
  have hsub : denseUnits2.vars.toFinset ⊆ Finset.range 2 := by rw [hvset]; decide
  have heval : ∀ σ, denseUnits2.eval σ = unit0.eval σ := fun σ => by
    simp only [denseUnits2, unit0, CNF.eval, List.all_replicate, OfNat.ofNat_ne_zero,
      ↓reduceIte, List.all_cons, List.all_nil, Bool.and_true]
  have hon : denseUnits2.modelCountOn (Finset.range 2) = 2 :=
    (show _ = unit0.modelCountOn (Finset.range 2) by simp only [CNF.modelCountOn, heval]).trans
      (by decide)
  have hmul := CNF.modelCountOn_eq_mul_modelCount denseUnits2 (Finset.range 2) hsub
  rw [hon, CNF.numVars, hvset, show (Finset.range 2).card - unit0.vars.toFinset.card = 1 by decide]
    at hmul
  refine ⟨by rw [leafDensityRatio_three_two, denseUnits2, List.length_replicate]; decide, ?_⟩
  unfold declExh leafExh exhBranchEval
  rw [branchedSparseCNFDeclaredCounter_exhaustive_eq_modelCountOn 3 0 0 0 () 2 _ hw hsub,
    branchedSparseCNFLeafCounter_exhaustive_eq_modelCount 3 0 0 0 () 2 _ hw hsub, hon]; omega

-- 3. Non-dense variable support (`N = 4`, variables `{0, 2}`) across fallback and fast paths.
theorem leafDensityRatio_three_four : leafDensityRatio 3 4 = 525315 :=
  ratio_three_of_div (by unfold leafSearchDivisor; rw [(SparseCountingScale.numGroups_eq_iff
    (s := 1) (by decide)).mpr (by decide)]; decide)
private def nonDense1 : CNF ℕ := [[(0, true), (2, false)]]
private def nonDense2 : CNF ℕ := [[(0, true), (2, false)], [(0, false), (2, false)]]

example : (declExh 3 5 0 0 (((), 4), nonDense1) = 12 ∧ leafExh 3 5 0 0 (((), 4), nonDense1) = 3 ∧
      declExh 3 5 0 0 (((), 4), nonDense2) = 8 ∧ leafExh 3 5 0 0 (((), 4), nonDense2) = 2) ∧
    entersSparseFastPath 3 1 4 (leafDensityRatio 3 4) nonDense2 = true ∧
    declExh 3 0 0 0 (((), 4), nonDense1) = 12 ∧ leafExh 3 0 0 0 (((), 4), nonDense1) = 3 ∧
    declExh 3 0 0 0 (((), 4), nonDense2) = 8 ∧ leafExh 3 0 0 0 (((), 4), nonDense2) = 2 := by
  refine ⟨?_, by rw [leafDensityRatio_three_four]; decide, ?_⟩
  · unfold declExh leafExh branchedSparseCNFLeafCounter normalizeDeclaredLeaf
      branchedSparseCNFDeclaredCounter sparseCNFDeclaredCounter
    dsimp only; rw [leafDensityRatio_three_four]; decide
  · have hd := branchedSparseCNFDeclaredCounter_exhaustive_eq_modelCountOn 3 0 0 0 () 4
    have hl := branchedSparseCNFLeafCounter_exhaustive_eq_modelCount 3 0 0 0 () 4
    unfold declExh leafExh exhBranchEval
    rw [hd nonDense1 (by decide) (by decide), hl nonDense1 (by decide) (by decide),
      hd nonDense2 (by decide) (by decide), hl nonDense2 (by decide) (by decide)]; decide

-- 4. Invalid width / out-of-range variables and unconditional global output caps.
example : declExh 3 0 0 0 (((), 5), [[(0, true), (1, true), (2, true), (3, true)]]) = 0 ∧
    leafExh 3 0 0 0 (((), 5), [[(0, true), (1, true), (2, true), (3, true)]]) = 0 ∧
    declExh 3 0 0 0 (((), 2), [[(2, true)]]) = 0 ∧
    leafExh 3 0 0 0 (((), 2), [[(2, true)]]) = 0 := by decide
example (x : (Unit × ℕ) × CNF ℕ) :
    branchedSparseCNFDeclaredCounter 3 2 2 2 (fun _ => 999999) x ≤ 2 ^ x.1.2 ∧
    branchedSparseCNFLeafCounter 3 2 2 2 (fun _ => 999999) x ≤ 2 ^ x.2.numVars :=
  ⟨branchedSparseCNFDeclaredCounter_le_two_pow 3 2 2 2 _ x,
    branchedSparseCNFLeafCounter_le_two_pow_numVars 3 2 2 2 _ x⟩

-- 5. Concrete `NativeCertificate`, `.isComputable`, and `PolyBounded` workspace checks.
private theorem computableInPolyTime_exhBranchProj :
    ComputableInPolyTime (fun inp : BranchEvalInput => (inp.1.1, inp.2.2.2))
      encBranchEvalInput (encPair encUnary (encList (encList (encList encNat)))) := by
  unfold encBranchEvalInput
  exact ((ComputableInPolyTime.fst _ _).comp (ComputableInPolyTime.fst _ _)).prod
    ((ComputableInPolyTime.snd _ _).comp
      ((ComputableInPolyTime.snd _ _).comp (ComputableInPolyTime.snd _ _)))
private noncomputable def exhBranchCert :
    NativeCertificate exhBranchEval encBranchEvalInput encNat :=
  countSystemExhaustiveCertificate.comp (.ofPolyTime computableInPolyTime_exhBranchProj)
private theorem exhBranchEval_le (n' : ℕ) (eqs' : List (List (List ℕ)))
    (_ : checkBranchFeasible 2 (n', eqs') = true) :
    exhBranchEval (prepareBranchEvalInput (n', eqs')) ≤ 2 ^ n' :=
  (countSystemExhaustive_eq_rootCount n' eqs').trans_le
    (HeavyBranchFold.rootCount_le_two_pow n' eqs')
private theorem polyBounded_exhBranchCert_space :
    PolyBounded (fun x => (encBranchEvalInput x).length) exhBranchCert.space :=
  (NativeCertificate.ofPolyTime_isPolynomial computableInPolyTime_exhBranchProj).2.add
    (polyBounded_countSystemExhaustive_space.comp
      computableInPolyTime_exhBranchProj.polyBounded_length)
private noncomputable abbrev cDeclTest :=
  branchedSparseCNFDeclaredCertificate 3 2 2 2 exhBranchCert exhBranchEval_le
private noncomputable abbrev cLeafTest :=
  branchedSparseCNFLeafCertificate 3 2 2 2 exhBranchCert exhBranchEval_le
example : ComputableInPolyTime (fun p : Unit × ℕ => leafDensityRatio 3 p.2)
      (encPair encUnit encUnary) encUnary ∧
    IsComputable (declExh 3 2 2 2) encLeafIn encNat ∧
    IsComputable (leafExh 3 2 2 2) encLeafIn encNat ∧
    PolyBounded (fun x => (encLeafIn x).length) cDeclTest.space ∧
    PolyBounded (fun x => (encLeafIn x).length) cLeafTest.space ∧
    ComputableInO (declExh 3 2 2 2) encLeafIn encNat cDeclTest.time cDeclTest.space ∧
    ComputableInO (leafExh 3 2 2 2) encLeafIn encNat cLeafTest.time cLeafTest.space :=
  ⟨computableInPolyTime_leafDensityRatio 3, cDeclTest.isComputable, cLeafTest.isComputable,
    polyBounded_branchedSparseCNFDeclaredCertificate_space 3 2 2 2 _ _
      polyBounded_exhBranchCert_space,
    polyBounded_branchedSparseCNFLeafCertificate_space 3 2 2 2 _ _ polyBounded_exhBranchCert_space,
    cDeclTest.computes, cLeafTest.computes⟩

end ComplexityTests.Computability.PolyTime.CNF.BranchedSparseCNFCounter
end
