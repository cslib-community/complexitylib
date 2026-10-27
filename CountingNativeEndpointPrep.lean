/-
Copyright (c) 2026 OpenAI, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Samuel Schlesinger
-/

module
-- upstream: candidate

import Complexity.Computability.Complexity.FineGrained.CountingSparsificationUniform
import Complexity.Computability.Complexity.FineGrained.CountingParameterBounds
import Complexity.Computability.PolyTime.FineGrained.ParameterCheck
import Complexity.Logics.Propositional.ClauseSet.Sparsification.CountingParametersPolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Universal.Complexity
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.Plain
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Complexity.Problems.SAT.PolyTime

/-!
# Private preparation for the native counting endpoint

Unaggregated author preparation under #1226: parameter computation, original-input encoding
charges, finite exceptions for the clamped divisor, and selected-branch guard resources.
Every declaration is private. This file supplies neither a leaf counter nor a counting endpoint.
The whole-search resource certificate remains the unchanged supplier in
`CountingSparsificationUniform`. These proofs are intended for later incorporation into the
unconditional endpoint, after the concrete leaf suppliers discharge its remaining premises.
-/

namespace Cslib.Complexity.CountingNativeEndpointPrep

open Cslib.Logic.PL Cslib.Logic.PL.CNF.Sparsification
open Cslib.Logic.PL.ClauseSet.Sparsification Turing.MultiTapeTM
open Turing.MultiTapeTM.Universal (encUnit encUnit_apply)
open CountingSparsify SubexponentialSAT SubexponentialSAT.ReplacementParams
open SubexponentialSAT.SparseCountingScale Filter

private abbrev Input := ℕ × CNF ℕ
private abbrev Context := Unit × ℕ
private abbrev FullInput := Unit × ℕ × CNF ℕ
private abbrev encInput := encPair encUnary encCNF
private abbrev encContext := encPair encUnit encUnary
private abbrev encFullInput := encPair encUnit encInput

private def inputSize (x : Input) : ℕ := (encInput x).length
private def width (k : ℕ) : ℕ := max 2 k
private def divisor (p : Context) : ℕ := max 1 (numGroups p.2)
private def thresholdBase (k : ℕ) (p : Context) : ℕ := countingThresholdBase (width k) (divisor p)
private def depthCoeff (k : ℕ) (p : Context) : ℕ := countingDepthCoeff (width k) (thresholdBase k p)
private def prepare (x : Input) : FullInput := ((), x)

private theorem two_le_width (k : ℕ) : 2 ≤ width k := le_max_left _ _
private theorem le_width (k : ℕ) : k ≤ width k := le_max_right _ _
private theorem one_le_divisor (p : Context) : 1 ≤ divisor p := le_max_left _ _
private theorem two_le_thresholdBase (k : ℕ) (p : Context) : 2 ≤ thresholdBase k p :=
  two_le_countingThresholdBase _ _

private theorem computableInPolyTime_divisor_unary :
    ComputableInPolyTime divisor encContext encUnary := by
  have hn : ComputableInPolyTime (fun p : Context => p.2) encContext encNat :=
    ComputableInPolyTime.unary_to_binary.comp (ComputableInPolyTime.snd _ _)
  have hs := ParameterCheck.computableInPolyTime_numGroups_unary.comp hn
  exact (ComputableInPolyTime.of_tidy ComputableTidilyInPolyTime.unary_max).comp
    ((ComputableInPolyTime.const 1).prod hs)

private theorem computableInPolyTime_divisor :
    ComputableInPolyTime divisor encContext encNat :=
  ComputableInPolyTime.unary_to_binary.comp computableInPolyTime_divisor_unary

private theorem computableInPolyTime_thresholdBase (k : ℕ) :
    ComputableInPolyTime (thresholdBase k) encContext encNat :=
  (computableInPolyTime_countingThresholdBase (width k)).comp computableInPolyTime_divisor

private theorem computableInPolyTime_thresholdCompare (k : ℕ) :
    ComputableInPolyTime
      (fun x : Context × ℕ × ℕ => decide (countingThreshold (thresholdBase k x.1) x.2.1 ≤ x.2.2))
      (encPair encContext (encPair encUnary encUnary)) encBool :=
  computableInPolyTime_countingThreshold_le_binary.comp
    (((computableInPolyTime_thresholdBase k).comp (ComputableInPolyTime.fst _ _)).prod
      (ComputableInPolyTime.snd _ _))

private theorem treeBound (k : ℕ) (p : Context) :
    CountingTreeBound (thresholdBase k p) (width k) (divisor p) (depthCoeff k p)
      ((by decide : 1 ≤ 2).trans (two_le_thresholdBase k p))
      ((by decide : 1 ≤ 2).trans (two_le_width k)) :=
  countingTreeBound_countingThresholdBase _ (one_le_divisor p)

private theorem declaredSize_le_inputSize (x : Input) : x.1 ≤ inputSize x := by
  simp only [inputSize, encInput, length_encPair, encUnary_apply, List.length_replicate]
  omega

private theorem polyBounded_depthCoeff (k : ℕ) :
    PolyBounded inputSize (fun x => depthCoeff k ((), x.1)) :=
  polyBounded_countingDepthCoeff_numGroups (two_le_width k)
    (PolyBounded.self.mono declaredSize_le_inputSize)

private theorem polyBounded_depthCoeff_full (k : ℕ) :
    PolyBounded (fun x : FullInput => (encFullInput x).length)
      (fun x => depthCoeff k (x.1, x.2.1)) :=
  polyBounded_countingDepthCoeff_numGroups_encPair encUnit encCNF (two_le_width k)

private theorem computableInPolyTime_prepare :
    ComputableInPolyTime prepare encInput encFullInput := by
  unfold prepare
  fun_prop

private theorem length_prepare (x : Input) : (encFullInput (prepare x)).length = inputSize x + 1 := by
  simp [encFullInput, prepare, inputSize, encUnit_apply]

private theorem length_leaf_input (N : ℕ) (ψ : CNF ℕ) :
    (encPair encContext encCNF (((), N), ψ)).length = 2 * N + 3 + (encCNF ψ).length := by
  simp only [encContext, length_encPair, encUnit_apply, List.length_nil, encUnary_apply,
    List.length_replicate]
  omega

private theorem divisor_eq_numGroups {p : Context} (h : 1 ≤ numGroups p.2) :
    divisor p = numGroups p.2 := max_eq_right h

private theorem finite_clamped_sizes : {N : ℕ | divisor ((), N) ≠ numGroups N}.Finite :=
  (finite_numGroups_lt 1).subset fun N h => by
    change numGroups N < 1
    by_contra hn
    exact h (divisor_eq_numGroups (p := ((), N)) (Nat.le_of_not_gt hn))

private theorem computableInPolyTime_valid (k : ℕ) :
    ComputableInPolyTime (fun x : Input => validDeclaredInput k x.1 x.2) encInput encBool := by
  have hN := ComputableInPolyTime.unary_to_binary.comp
    (ComputableInPolyTime.fst encUnary encCNF)
  have hlt : ComputableInPolyTime
      (fun x : Input × ℕ => decide (x.2 < x.1.1)) (encPair encInput encNat) encBool :=
    (ComputableInPolyTime.of_tidy ComputableTidilyInPolyTime.binary_lt).comp
      ((ComputableInPolyTime.snd _ _).prod (hN.comp (ComputableInPolyTime.fst _ _)))
  have hs : ComputableInPolyTime
      (fun x : Input => x.2.vars.all fun v => decide (v < x.1)) encInput encBool :=
    ComputableInPolyTime.allWithInput (by fun_prop) hlt
  unfold validDeclaredInput
  fun_prop

private theorem numVars_le_of_valid {k : ℕ} {x : Input}
    (hx : validDeclaredInput k x.1 x.2 = true) : x.2.numVars ≤ x.1 := by
  have hsub := (validDeclaredInput_eq_true_iff.mp hx).2
  simpa only [CNF.numVars, Finset.card_range] using Finset.card_le_card hsub

/-- Polynomial workspace in the full Unit context remains polynomial in the original external
encoding. Guarding the false branch adds only the external input-length charge. -/
private theorem polyBounded_selectedSpace (k d : ℕ) {S : FullInput → ℕ}
    (hS : PolyBounded (fun x => (encFullInput x).length) S) :
    PolyBounded inputSize (fun x => (inputSize x + 1) ^ d +
      if validDeclaredInput k x.1 x.2 then S (prepare x) else inputSize x) := by
  have hprepared : PolyBounded inputSize (fun x => S (prepare x)) :=
    hS.comp computableInPolyTime_prepare.polyBounded_length
  have hbranch : PolyBounded inputSize
      (fun x => if validDeclaredInput k x.1 x.2 then S (prepare x) else inputSize x) :=
    (hprepared.add PolyBounded.self).mono fun x => by split_ifs <;> omega
  exact ((PolyBounded.self.add (.const 1)).pow d).add hbranch

/-- Reapply the already-present input guard to retain the cost of only the selected branch.
This avoids charging an invalid-support input for its unbounded occurring-support clock. -/
private theorem exists_computableInO_selectedSearch (k : ℕ)
    (g : Context × CNF ℕ → ℕ) {T S : FullInput → ℕ}
    (hsearch : ComputableInO
      (fun x : FullInput => searchDeclaredWith Prod.snd (thresholdBase k) divisor (width k) k g
        (x.1, x.2.1) x.2.2) encFullInput encNat T S) :
    ∃ d, ComputableInO
      (fun x : Input => searchDeclaredWith Prod.snd (thresholdBase k) divisor (width k) k g
        ((), x.1) x.2) encInput encNat
      (fun x => (inputSize x + 1) ^ d +
        if validDeclaredInput k x.1 x.2 then T (prepare x) else inputSize x)
      (fun x => (inputSize x + 1) ^ d +
        if validDeclaredInput k x.1 x.2 then S (prepare x) else inputSize x) := by
  obtain ⟨dp, _, hp⟩ := computableInPolyTime_prepare.tidy.exists_degree
  obtain ⟨dv, _, hv⟩ := (computableInPolyTime_valid k).tidy.exists_degree
  have hcore := hsearch.comp (ComputableInO.of_tidy hp.inO)
  have hguard := (ComputableInO.of_tidy hv.inO).ite hcore
    (ComputableInO.const (encIn := encInput) 0)
  have hsum (x : Input) : (inputSize x + 1) ^ dv + (inputSize x + 1) ^ dp ≤
      2 * (inputSize x + 1) ^ (dv + dp) := by
    have hv' := Nat.pow_le_pow_right (by omega : 1 ≤ inputSize x + 1) (Nat.le_add_right dv dp)
    have hp' := Nat.pow_le_pow_right (by omega : 1 ≤ inputSize x + 1) (Nat.le_add_left dp dv)
    omega
  refine ⟨dv + dp, (hguard.mono 2 (fun x => ?_) (fun x => ?_)).of_enc_eq ?_⟩
  · change (inputSize x + 1) ^ dv +
      (if validDeclaredInput k x.1 x.2 then (inputSize x + 1) ^ dp + T (prepare x)
       else inputSize x) ≤ _
    split_ifs <;> have := hsum x <;> omega
  · change (inputSize x + 1) ^ dv +
      (if validDeclaredInput k x.1 x.2 then (inputSize x + 1) ^ dp + S (prepare x)
       else inputSize x) ≤ _
    split_ifs <;> have := hsum x <;> omega
  · intro x
    by_cases hx : validDeclaredInput k x.1 x.2 = true <;>
      simp [Function.comp_apply, prepare, searchDeclaredWith, hx]

end Cslib.Complexity.CountingNativeEndpointPrep
