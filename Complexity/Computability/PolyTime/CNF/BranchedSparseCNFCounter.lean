/-
Copyright (c) 2026 Anton Kovsharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anton Kovsharov
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.Complexity.FineGrained.CountingSparsification
public import Complexity.Computability.Complexity.FineGrained.GeneralCNFBranchSchedule
public import Complexity.Computability.Complexity.FineGrained.SparseBranchAsymptotics
public import Complexity.Computability.Complexity.FineGrained.SparseCountingScale
public import Complexity.Computability.Machines.Turing.MultiTape.Universal.Complexity
public import Complexity.Computability.PolyTime.BooleanAnalysis.SparsePolyCounter
public import Complexity.Computability.PolyTime.CNF.SparseCNFLeafCounter
public import Complexity.Logics.Propositional.ClauseSet.Sparsification.CountingParametersPolyTime
import all Complexity.Computability.PolyTime.CNF.SparseCNFLeafCounter
import Complexity.Computability.Complexity.Problems.SAT.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Complexity.Foundations.Data.List.Counting
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Heavy-branched sparse `k`-CNF leaf model counter (`BranchedSparseCNFCounter`)

Connects the heavy-branched sparse `𝔽₂` polynomial-system zero counter `countSparsePolySystem`
(§5.5, Theorem 2.2, pp. 38–39) to `sparseCNFDeclaredCounter` / `normalizeDeclaredLeaf` (§6.3, p. 43)
at the Proposition 6.4 leaf schedule (§6.4, pp. 43–44) of [OpenAI, *The Exponential Time Hypothesis
is False*][OpenAI2026ETH], parameterized solely over `branchEval : BranchEvalInput → ℕ`:

- **Encoded procedures vs. specification**: `leafDensityRatio` (`encPair encUnit encUnary →
  encUnary`) and `branchedPolyCounter`, `branchedSparseCNFDeclaredCounter`, and
  `branchedSparseCNFLeafCounter` carry uniform `NativeCertificate` witnesses with global
  `PolyBounded` workspace; `BranchPolylogTimeBound` states the unencoded Proposition 5.3 runtime
  hypothesis on `cBranch`.
- **Total fallback & exactness**: valid dense formulas (`leafDensityRatio k N * N < ψ.length`,
  including `[[]]` at `N = 0`) dispatch to `countCNFExhaustive`, sparse formulas dispatch to
  `sparseCNFDeclaredCounter` backed by `branchedPolyCounter`, invalid inputs (`validDeclaredInput =
  false`) return `0`. Assuming exact feasible-branch evaluation, exactness holds on all
  width-`≤ k` supported CNFs without a density restriction.

## Main definitions

* `leafSearchDivisor`, `leafThresholdBase`, `leafOccBound`, `leafDensityRatio`
* `branchedPolyCounter`, `branchedSparseCNFDeclaredCounter`, `branchedSparseCNFLeafCounter`
* `branchedPolyCertificate`, `branchedSparseCNFDeclaredCertificate`,
  `branchedSparseCNFLeafCertificate`, `BranchPolylogTimeBound`

## Main results

* `leafOccBound_eq_sum`, `leafOccBound_eq_occBound`, `leafDensityRatio_eq_prop64LeafClauseRatio`,
  `exists_leafDensityRatio_le_mul_clog_pow`, `computableInPolyTime_leafDensityRatio`
* `branchedSparseCNFDeclaredCounter_le_two_pow`, `branchedSparseCNFLeafCounter_le_two_pow_numVars`
* `branchedPolyCounter_eq_commonZeroCount`, `branchedSparseCNFDeclaredCounter_eq_modelCountOn`,
  `branchedSparseCNFLeafCounter_eq_modelCount`
* `polyBounded_branchedSparseCNFDeclaredCertificate_space`,
  `polyBounded_branchedSparseCNFLeafCertificate_space`
* `exists_threshold_branchedSparseCNF_time_bound`, `exists_branchedSparseCNF_time_bound`

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], §5.4 (Proposition 5.3,
  pp. 37–38), §5.5 (Theorem 2.2, pp. 38–39), §6.3 (eq. (6.4), p. 43), §6.4 (Proposition 6.4,
  pp. 43–44).
-/

namespace Cslib.Complexity.BranchedSparseCNFCounter

open Finset Cslib.BitString Cslib.Complexity.SparseCNFLeafCounter
open Cslib.Complexity.SubexponentialSAT Cslib.Complexity.SubexponentialSAT.SparsePolyCounter
open Cslib.GenericRAM Cslib.GenericRAM.ExhaustiveCountFallback
open Cslib.Logic.PL Cslib.Logic.PL.CNF Cslib.Logic.PL.ClauseSet.Sparsification
open Turing.MultiTapeTM
open Turing.MultiTapeTM.Universal (encUnit)

local notation "encSys" => encList (encList (encList encNat))
local notation "encLeafCtx" => encPair encUnit encUnary
local notation "encLeafIn" => encPair encLeafCtx encCNF

@[expose] public section

/-! ### 1. Proposition 6.4 / Section 6.3 Leaf Parameters and Total Counters -/

/-- Sparsification search divisor `max 1 ⌊√⌈log₂ N⌉ / ⌈log₂ ⌈log₂ N⌉⌉²⌋` (§6.4, Proposition 6.4). -/
def leafSearchDivisor (N : ℕ) : ℕ := max 1 (ReplacementParams.numGroups N)

/-- Appendix A.3 dyadic threshold base `countingThresholdBase (max 2 k) (leafSearchDivisor N)`. -/
def leafThresholdBase (k N : ℕ) : ℕ := countingThresholdBase (max 2 k) (leafSearchDivisor N)

/-- Sparse leaf clause-density sum `2 * ∑_{j < max 2 k} (leafThresholdBase k N) ^ j` (§6.4). -/
def leafOccBound (k N : ℕ) : ℕ :=
  2 * ((List.range (max 2 k)).map (leafThresholdBase k N ^ ·)).sum

/-- Promised sparse leaf clause-to-variable ratio `leafOccBound k N + 1` (§6.3–6.4). -/
def leafDensityRatio (k N : ℕ) : ℕ := leafOccBound k N + 1

/-- Heavy-branched sparse `𝔽₂` polynomial-system zero counter at `mkPaperSparseInput y.1 k y.2`. -/
def branchedPolyCounter (k N₀_top N₀_branch : ℕ) (branchEval : BranchEvalInput → ℕ)
    (y : ℕ × List (List (List ℕ))) : ℕ :=
  countSparsePolySystem N₀_top N₀_branch branchEval (mkPaperSparseInput y.1 k y.2)

/-- **Total declared-range sparse `k`-CNF leaf model counter** (§6.3–6.4): dispatches valid dense
formulas (`leafDensityRatio k N * N < ψ.length`, including `[[]]` at `N = 0`) to
`countCNFExhaustive` and sparse formulas (`ψ.length ≤ leafDensityRatio k N * N`) to
`sparseCNFDeclaredCounter` backed by `branchedPolyCounter`. -/
def branchedSparseCNFDeclaredCounter (k N₀_leaf N₀_top N₀_branch : ℕ)
    (branchEval : BranchEvalInput → ℕ) (x : (Unit × ℕ) × CNF ℕ) : ℕ :=
  let N := x.1.2; let B := leafDensityRatio k N; let ψ := x.2
  if validDeclaredInput k N ψ && decide (B * N < ψ.length) then countCNFExhaustive (N, ψ)
  else sparseCNFDeclaredCounter Prod.snd (fun p : Unit × ℕ => leafDensityRatio k p.2)
    k (max 1 N₀_leaf) (branchedPolyCounter k N₀_top N₀_branch branchEval) x

/-- **Total normalized occurring-support sparse `k`-CNF leaf model counter** (§6.3–6.4). -/
def branchedSparseCNFLeafCounter (k N₀_leaf N₀_top N₀_branch : ℕ)
    (branchEval : BranchEvalInput → ℕ) (x : (Unit × ℕ) × CNF ℕ) : ℕ :=
  normalizeDeclaredLeaf Prod.snd
    (branchedSparseCNFDeclaredCounter k N₀_leaf N₀_top N₀_branch branchEval) x

end

public section

/-! ### 2. Leaf Parameter Bounds & Unary `ComputableInPolyTime` Certificate -/

/-- `leafOccBound k N` equals `2 * ∑ j ∈ Finset.range (max 2 k), leafThresholdBase k N ^ j`. -/
theorem leafOccBound_eq_sum (k N : ℕ) :
    leafOccBound k N = 2 * ∑ j ∈ Finset.range (max 2 k), leafThresholdBase k N ^ j := by
  unfold leafOccBound; congr 1

/-- `leafOccBound k N` agrees with `CountingSparsify.occBound (max 2 k) (leafThresholdBase k N)`. -/
theorem leafOccBound_eq_occBound (k N : ℕ) :
    leafOccBound k N = CountingSparsify.occBound (max 2 k) (leafThresholdBase k N) := by
  rw [leafOccBound_eq_sum]; rfl

/-- When `1 ≤ ReplacementParams.numGroups N`, `leafDensityRatio` equals `prop64LeafClauseRatio`. -/
theorem leafDensityRatio_eq_prop64LeafClauseRatio {k N : ℕ}
    (hs : 1 ≤ ReplacementParams.numGroups N) :
    leafDensityRatio k N = CNF.prop64LeafClauseRatio (max 2 k) N := by
  simp only [leafDensityRatio, leafOccBound_eq_sum, leafThresholdBase, leafSearchDivisor,
    max_eq_right hs, CNF.prop64LeafClauseRatio, CNF.prop64ThresholdBase]

/-- For `1 ≤ N`, `leafOccBound k N * N + 1 ≤ leafDensityRatio k N * N`. -/
theorem leafOccBound_mul_succ_le_leafDensityRatio_mul {k N : ℕ} (hN : 1 ≤ N) :
    leafOccBound k N * N + 1 ≤ leafDensityRatio k N * N :=
  (Nat.add_le_add_left hN _).trans_eq (by unfold leafDensityRatio; ring)

/-- **Polylogarithmic leaf clause-density bound (§6.4, Proposition 6.4, p. 44)**:
`∃ C_B, ∀ N ≥ 2, leafDensityRatio k N ≤ C_B * (Nat.clog 2 N) ^ (2 * (max 2 k - 1))`. -/
theorem exists_leafDensityRatio_le_mul_clog_pow (k : ℕ) :
    ∃ C_B : ℕ, ∀ N : ℕ, 2 ≤ N →
      leafDensityRatio k N ≤ C_B * (Nat.clog 2 N) ^ (2 * (max 2 k - 1)) := by
  obtain ⟨C₀, _, hC₀⟩ := CNF.exists_prop64LeafClauseRatio_le_mul_clog_pow (le_max_left 2 k)
  let B₁ := 2 * (∑ j ∈ Finset.range (max 2 k), countingThresholdBase (max 2 k) 1 ^ j) + 1
  refine ⟨max C₀ B₁, fun N hN => ?_⟩
  rcases Nat.eq_zero_or_pos (ReplacementParams.numGroups N) with hs0 | hs_pos
  · have h0 : leafDensityRatio k N = B₁ := by
      simp only [leafDensityRatio, leafOccBound_eq_sum, leafThresholdBase, leafSearchDivisor,
        hs0, max_eq_left (Nat.zero_le 1), B₁]
    have hlam1 : 1 ≤ Nat.clog 2 N :=
      (Nat.lt_clog_iff_pow_lt Nat.one_lt_two).mpr (by omega : 2 ^ 0 < N)
    rw [h0]; exact (le_max_right C₀ B₁).trans (Nat.le_mul_of_pos_right _ (Nat.one_le_pow _ _ hlam1))
  · rw [leafDensityRatio_eq_prop64LeafClauseRatio hs_pos]
    exact (hC₀ N hN).trans (Nat.mul_le_mul_right _ (le_max_left C₀ B₁))

private theorem computableInPolyTime_leafDensityRatio_binary (k : ℕ) :
    ComputableInPolyTime (leafDensityRatio k) encNat encNat := by
  open ComputableInPolyTime in
  have hmax1 : ComputableInPolyTime (fun x : ℕ => max 1 x) encNat encNat :=
    ((binary_lt' id' (const 1)).ite (const 1) id').of_enc_eq fun x =>
      congrArg encNat (by
        split_ifs with hx <;> simp only [decide_eq_true_eq] at hx <;> omega)
  have hM : ComputableInPolyTime (leafThresholdBase k) encNat encNat :=
    (computableInPolyTime_countingThresholdBase (max 2 k)).comp
      (hmax1.comp ParameterCheck.computableInPolyTime_numGroups)
  have hgeom (n : ℕ) :
      ComputableInPolyTime (fun M : ℕ => ∑ j ∈ Finset.range n, M ^ j) encNat encNat := by
    induction n with
    | zero => simpa only [Finset.range_zero, Finset.sum_empty] using (const (encIn := encNat) 0)
    | succ n ih =>
      exact (binary_add.comp ((binary_mul' id' ih).prod (const 1))).of_enc_eq fun M =>
        congrArg encNat (by
          dsimp only [Function.comp_apply]
          rw [Finset.sum_range_succ', pow_zero, Finset.mul_sum]; simp only [pow_succ'])
  have hocc : ComputableInPolyTime (leafOccBound k) encNat encNat :=
    (binary_mul' (const 2) ((hgeom (max 2 k)).comp hM)).of_enc_eq fun N =>
      congrArg encNat (leafOccBound_eq_sum k N).symm
  exact binary_add.comp (hocc.prod (const 1))

private theorem exists_leafDensityRatio_le_poly (k : ℕ) :
    ∃ C_u d_u : ℕ, ∀ N : ℕ, leafDensityRatio k N ≤ C_u * (N + 1) ^ d_u := by
  obtain ⟨C_B, hCB⟩ := exists_leafDensityRatio_le_mul_clog_pow k
  set d_u := 2 * (max 2 k - 1)
  set C_u := max C_B (max (leafDensityRatio k 0) (leafDensityRatio k 1))
  refine ⟨C_u, d_u, fun N => ?_⟩
  rcases N with _ | _ | N'
  · have h0 : leafDensityRatio k 0 ≤ C_u :=
      (le_max_left _ (leafDensityRatio k 1)).trans (le_max_right C_B _)
    simpa only [Nat.zero_add, one_pow, mul_one] using h0
  · have h1 : leafDensityRatio k 1 ≤ C_u :=
      (le_max_right (leafDensityRatio k 0) _).trans (le_max_right C_B _)
    exact (h1.trans_eq (mul_one C_u).symm).trans
      (Nat.mul_le_mul_left C_u (Nat.one_le_pow d_u 2 Nat.zero_lt_two))
  · have hclog_le : Nat.clog 2 (N' + 2) ≤ N' + 2 + 1 :=
      ((Nat.clog_le_iff_le_pow Nat.one_lt_two).mpr (N' + 2).lt_two_pow_self.le).trans (by omega)
    exact (hCB (N' + 2) (by omega)).trans
      (Nat.mul_le_mul (le_max_left _ _) (Nat.pow_le_pow_left hclog_le d_u))

/-- **Unary `ComputableInPolyTime` certificate for `leafDensityRatio`** on `(Unit × ℕ)`
(`encPair encUnit encUnary → encUnary`), clamping the binary `countingThresholdBase` schedule by its
polynomial unary upper bound via `ComputableInPolyTime.binary_min_unary'`. -/
theorem computableInPolyTime_leafDensityRatio (k : ℕ) :
    ComputableInPolyTime (fun p : Unit × ℕ => leafDensityRatio k p.2)
      (encPair encUnit encUnary) encUnary := by
  open ComputableInPolyTime in
  obtain ⟨C_u, d_u, hCu⟩ := exists_leafDensityRatio_le_poly k
  have hN_u : ComputableInPolyTime (fun p : Unit × ℕ => p.2) encLeafCtx encUnary :=
    snd encUnit encUnary
  have hcap_u : ComputableInPolyTime (fun p : Unit × ℕ => C_u * (p.2 + 1) ^ d_u)
      encLeafCtx encUnary :=
    unary_mul' (const C_u) ((unary_pow d_u).comp (unary_add' hN_u (const 1)))
  have hval_b : ComputableInPolyTime (fun p : Unit × ℕ => leafDensityRatio k p.2)
      encLeafCtx encNat :=
    (computableInPolyTime_leafDensityRatio_binary k).comp (unary_to_binary.comp hN_u)
  exact (binary_min_unary' hcap_u hval_b).of_enc_eq fun p =>
    congrArg encUnary (Nat.min_eq_right (hCu p.2)).symm

/-! ### 3. Unconditional Output Caps & Semantic Exactness Across All Width-`≤ k` CNFs -/

/-- **Unconditional declared-range output cap**: `branchedSparseCNFDeclaredCounter ≤ 2 ^ x.1.2`. -/
theorem branchedSparseCNFDeclaredCounter_le_two_pow (k N₀_leaf N₀_top N₀_branch : ℕ)
    (branchEval : BranchEvalInput → ℕ) (x : (Unit × ℕ) × CNF ℕ) :
    branchedSparseCNFDeclaredCounter k N₀_leaf N₀_top N₀_branch branchEval x ≤ 2 ^ x.1.2 := by
  unfold branchedSparseCNFDeclaredCounter; dsimp only; split_ifs
  · rw [countCNFExhaustive_eq_modelCountOn_range, CNF.modelCountOn]
    refine (Finset.card_filter_le _ _).trans ?_
    simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_coe,
      Finset.card_range, le_rfl]
  · exact sparseCNFDeclaredCounter_le_two_pow Prod.snd _ k (max 1 N₀_leaf) _ x

/-- **Unconditional occurring-support output cap**:
`branchedSparseCNFLeafCounter ≤ 2 ^ x.2.numVars`. -/
theorem branchedSparseCNFLeafCounter_le_two_pow_numVars (k N₀_leaf N₀_top N₀_branch : ℕ)
    (branchEval : BranchEvalInput → ℕ) (x : (Unit × ℕ) × CNF ℕ) :
    branchedSparseCNFLeafCounter k N₀_leaf N₀_top N₀_branch branchEval x ≤ 2 ^ x.2.numVars := by
  rcases x with ⟨p, ψ⟩
  by_cases hv : validDeclaredInput k p.2 ψ = true
  · exact normalizeDeclaredLeaf_le_two_pow_numVars (validDeclaredInput_eq_true_iff.mp hv).2
      (branchedSparseCNFDeclaredCounter_le_two_pow k N₀_leaf N₀_top N₀_branch branchEval (p, ψ))
  · simp only [Bool.not_eq_true] at hv
    simp only [branchedSparseCNFLeafCounter, normalizeDeclaredLeaf,
      branchedSparseCNFDeclaredCounter, sparseCNFDeclaredCounter, hv, Bool.false_and,
      Bool.false_eq_true, ↓reduceIte, Nat.zero_shiftRight, Nat.zero_le]

/-- **Semantic bridge for `branchedPolyCounter` (§5.5 & §6.3)**: under exact feasible branch
evaluation, `branchedPolyCounter` equals `commonZeroCount` on `IsCompiledSparseSystem`. -/
theorem branchedPolyCounter_eq_commonZeroCount {k N₀_top N₀_branch N maxEqs maxTerms : ℕ}
    {branchEval : BranchEvalInput → ℕ}
    (hbranch : ∀ n' eqs', checkBranchFeasible N₀_branch (n', eqs') = true →
      branchEval (prepareBranchEvalInput (n', eqs')) = HeavyBranchFold.rootCount n' eqs')
    {sys : List (List (List ℕ))} (hsys : IsCompiledSparseSystem k N maxEqs maxTerms sys) :
    branchedPolyCounter k N₀_top N₀_branch branchEval (N, sys) =
      commonZeroCount (Finset.univ : Finset (Fin sys.length))
        (fun i : Fin sys.length => equationToFinset N sys[i]) :=
  countSparsePolySystem_eq_commonZeroCount hbranch (mkPaperSparseInput N k sys)
    (fun eq heq => (hsys.2 eq heq).1) (fun eq heq m hm v hv => ((hsys.2 eq heq).2.2 m hm).2 v hv)

/-- **Exactness of `branchedSparseCNFDeclaredCounter` without a density restriction**
(§5.5, §6.3, §6.4), assuming exact feasible-branch evaluation, on all width-`≤ k` formulas `ψ`
with `ψ.vars.toFinset ⊆ Finset.range N`. -/
theorem branchedSparseCNFDeclaredCounter_eq_modelCountOn {k N₀_leaf N₀_top N₀_branch : ℕ}
    {branchEval : BranchEvalInput → ℕ}
    (hbranch : ∀ n' eqs', checkBranchFeasible N₀_branch (n', eqs') = true →
      branchEval (prepareBranchEvalInput (n', eqs')) = HeavyBranchFold.rootCount n' eqs')
    (c : Unit) (N : ℕ) (ψ : CNF ℕ) (hw : ∀ cl ∈ ψ, cl.length ≤ k)
    (hsub : ψ.vars.toFinset ⊆ Finset.range N) :
    branchedSparseCNFDeclaredCounter k N₀_leaf N₀_top N₀_branch branchEval ((c, N), ψ) =
      ψ.modelCountOn (Finset.range N) := by
  have hv : validDeclaredInput k N ψ = true := validDeclaredInput_eq_true_iff.mpr ⟨hw, hsub⟩
  unfold branchedSparseCNFDeclaredCounter; dsimp only
  by_cases hgt : leafDensityRatio k N * N < ψ.length
  · simp only [hv, decide_eq_true hgt, Bool.and_true, ↓reduceIte]
    exact countCNFExhaustive_eq_modelCountOn_range N ψ
  · simp only [hv, decide_eq_false hgt, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
    exact sparseCNFDeclaredCounter_eq_modelCountOn hw hsub (Or.inl (Nat.le_of_not_lt hgt))
      fun _ _ hsys => branchedPolyCounter_eq_commonZeroCount hbranch hsys

/-- **Exactness of `branchedSparseCNFLeafCounter` without a density restriction**
(§5.5, §6.3, §6.4), assuming exact feasible-branch evaluation, on all width-`≤ k` formulas `ψ`
with `ψ.vars.toFinset ⊆ Finset.range N`. -/
theorem branchedSparseCNFLeafCounter_eq_modelCount {k N₀_leaf N₀_top N₀_branch : ℕ}
    {branchEval : BranchEvalInput → ℕ}
    (hbranch : ∀ n' eqs', checkBranchFeasible N₀_branch (n', eqs') = true →
      branchEval (prepareBranchEvalInput (n', eqs')) = HeavyBranchFold.rootCount n' eqs')
    (c : Unit) (N : ℕ) (ψ : CNF ℕ) (hw : ∀ cl ∈ ψ, cl.length ≤ k)
    (hsub : ψ.vars.toFinset ⊆ Finset.range N) :
    branchedSparseCNFLeafCounter k N₀_leaf N₀_top N₀_branch branchEval ((c, N), ψ) =
      ψ.modelCount :=
  normalizeDeclaredLeaf_eq_modelCount hsub
    (branchedSparseCNFDeclaredCounter_eq_modelCountOn hbranch c N ψ hw hsub)

/-- Concrete instantiation of `branchedSparseCNFDeclaredCounter_eq_modelCountOn` with
`countSystemExhaustive`. -/
theorem branchedSparseCNFDeclaredCounter_exhaustive_eq_modelCountOn
    (k N₀_leaf N₀_top N₀_branch : ℕ) (c : Unit) (N : ℕ) (ψ : CNF ℕ)
    (hw : ∀ cl ∈ ψ, cl.length ≤ k) (hsub : ψ.vars.toFinset ⊆ Finset.range N) :
    branchedSparseCNFDeclaredCounter k N₀_leaf N₀_top N₀_branch
        (fun inp => countSystemExhaustive (inp.1.1, inp.2.2.2)) ((c, N), ψ) =
      ψ.modelCountOn (Finset.range N) :=
  branchedSparseCNFDeclaredCounter_eq_modelCountOn
    (fun n' eqs' _ => countSystemExhaustive_eq_rootCount n' eqs') c N ψ hw hsub

/-- Concrete instantiation of `branchedSparseCNFLeafCounter_eq_modelCount` with
`countSystemExhaustive`. -/
theorem branchedSparseCNFLeafCounter_exhaustive_eq_modelCount
    (k N₀_leaf N₀_top N₀_branch : ℕ) (c : Unit) (N : ℕ) (ψ : CNF ℕ)
    (hw : ∀ cl ∈ ψ, cl.length ≤ k) (hsub : ψ.vars.toFinset ⊆ Finset.range N) :
    branchedSparseCNFLeafCounter k N₀_leaf N₀_top N₀_branch
        (fun inp => countSystemExhaustive (inp.1.1, inp.2.2.2)) ((c, N), ψ) =
      ψ.modelCount :=
  branchedSparseCNFLeafCounter_eq_modelCount
    (fun n' eqs' _ => countSystemExhaustive_eq_rootCount n' eqs') c N ψ hw hsub

/-! ### 4. Uniform Native Certificates & Global `PolyBounded` Workspace -/

private theorem computableInPolyTime_mkPaperInputConst (k : ℕ) :
    ComputableInPolyTime (fun y : ℕ × List (List (List ℕ)) => mkPaperSparseInput y.1 k y.2)
      (encPair encUnary encSys) encSparseSystemInput := by
  have hk : ComputableInPolyTime (fun _ : ℕ × List (List (List ℕ)) => k)
      (encPair encUnary encSys) encUnary := ComputableInPolyTime.const k
  exact computableInPolyTime_mkPaperSparseInput.comp
    (((ComputableInPolyTime.fst encUnary encSys).prod hk).prod
      (ComputableInPolyTime.snd encUnary encSys))

/-- **Native resource certificate for `branchedPolyCounter` (§5.5).** -/
noncomputable def branchedPolyCertificate (k N₀_top N₀_branch : ℕ)
    {branchEval : BranchEvalInput → ℕ}
    (cBranch : NativeCertificate branchEval encBranchEvalInput encNat)
    (hbound : ∀ n' eqs', checkBranchFeasible N₀_branch (n', eqs') = true →
      branchEval (prepareBranchEvalInput (n', eqs')) ≤ 2 ^ n') :
    NativeCertificate (branchedPolyCounter k N₀_top N₀_branch branchEval)
      (encPair encUnary encSys) encNat :=
  ((sparsePolyCounterCertificate N₀_top N₀_branch cBranch hbound).comp
    (NativeCertificate.ofPolyTime (computableInPolyTime_mkPaperInputConst k))).congr fun _ => rfl

/-- Polynomial workspace preservation for `branchedPolyCertificate`. -/
theorem polyBounded_branchedPolyCertificate_space (k N₀_top N₀_branch : ℕ)
    {branchEval : BranchEvalInput → ℕ}
    (cBranch : NativeCertificate branchEval encBranchEvalInput encNat)
    (hbound : ∀ n' eqs', checkBranchFeasible N₀_branch (n', eqs') = true →
      branchEval (prepareBranchEvalInput (n', eqs')) ≤ 2 ^ n')
    (hs_br : PolyBounded (fun x => (encBranchEvalInput x).length) cBranch.space) :
    PolyBounded (fun y => (encPair encUnary encSys y).length)
      (branchedPolyCertificate k N₀_top N₀_branch cBranch hbound).space := by
  unfold branchedPolyCertificate
  have hmk := computableInPolyTime_mkPaperInputConst k
  exact (NativeCertificate.ofPolyTime_isPolynomial hmk).2.add
    ((polyBounded_sparsePolyCounterCertificate_space N₀_top N₀_branch cBranch hbound hs_br).comp
      hmk.polyBounded_length)

private def denseFallbackGuard (k : ℕ) (x : (Unit × ℕ) × CNF ℕ) : Bool :=
  validDeclaredInput k x.1.2 x.2 && decide (leafDensityRatio k x.1.2 * x.1.2 < x.2.length)

private theorem computableInPolyTime_denseFallbackGuard (k : ℕ) :
    ComputableInPolyTime (denseFallbackGuard k) encLeafIn encBool := by
  have hN_u : ComputableInPolyTime (fun x : (Unit × ℕ) × CNF ℕ => x.1.2) encLeafIn encUnary :=
    (ComputableInPolyTime.snd encUnit encUnary).comp (ComputableInPolyTime.fst encLeafCtx encCNF)
  have hB_u : ComputableInPolyTime (fun x : (Unit × ℕ) × CNF ℕ => leafDensityRatio k x.1.2)
      encLeafIn encUnary :=
    (computableInPolyTime_leafDensityRatio k).comp (ComputableInPolyTime.fst encLeafCtx encCNF)
  have hm_u : ComputableInPolyTime (fun x : (Unit × ℕ) × CNF ℕ => x.2.length)
      encLeafIn encUnary :=
    SAT.computableInPolyTime_length (ComputableInPolyTime.snd encLeafCtx encCNF)
  have h1 :=
    computableInPolyTime_validDeclaredInput k (ComputableInPolyTime.snd encUnit encUnary)
  have h2 : ComputableInPolyTime
      (fun x : (Unit × ℕ) × CNF ℕ => decide (leafDensityRatio k x.1.2 * x.1.2 < x.2.length))
      encLeafIn encBool :=
    ComputableInPolyTime.binary_lt'
      (ComputableInPolyTime.binary_mul'
        (ComputableInPolyTime.unary_to_binary.comp hB_u)
        (ComputableInPolyTime.unary_to_binary.comp hN_u))
      (ComputableInPolyTime.unary_to_binary.comp hm_u)
  exact ComputableInPolyTime.bool_and' h1 h2

private theorem computableInPolyTime_leafExhProj :
    ComputableInPolyTime (fun x : (Unit × ℕ) × CNF ℕ => (x.1.2, x.2))
      encLeafIn (encPair encUnary encCNF) :=
  ((ComputableInPolyTime.snd encUnit encUnary).comp
    (ComputableInPolyTime.fst encLeafCtx encCNF)).prod (ComputableInPolyTime.snd encLeafCtx encCNF)

/-- **Uniform `NativeCertificate` for `branchedSparseCNFDeclaredCounter`** (§6.3–6.4). -/
noncomputable def branchedSparseCNFDeclaredCertificate (k N₀_leaf N₀_top N₀_branch : ℕ)
    {branchEval : BranchEvalInput → ℕ}
    (cBranch : NativeCertificate branchEval encBranchEvalInput encNat)
    (hbound : ∀ n' eqs', checkBranchFeasible N₀_branch (n', eqs') = true →
      branchEval (prepareBranchEvalInput (n', eqs')) ≤ 2 ^ n') :
    NativeCertificate (branchedSparseCNFDeclaredCounter k N₀_leaf N₀_top N₀_branch branchEval)
      (encPair (encPair encUnit encUnary) encCNF) encNat :=
  guardedTargetOfPolyTime (computableInPolyTime_denseFallbackGuard k)
    (countCNFExhaustiveCertificate.comp
      (NativeCertificate.ofPolyTime computableInPolyTime_leafExhProj))
    (sparseCNFDeclaredCertificate k (max 1 N₀_leaf) (ComputableInPolyTime.snd encUnit encUnary)
      (computableInPolyTime_leafDensityRatio k)
      (branchedPolyCertificate k N₀_top N₀_branch cBranch hbound))
    (fun x h => by
      simp only [Function.comp_apply, branchedSparseCNFDeclaredCounter, denseFallbackGuard] at h ⊢
      simp only [h, ↓reduceIte])
    (fun x h => by
      simp only [branchedSparseCNFDeclaredCounter, denseFallbackGuard] at h ⊢
      simp only [h, Bool.false_eq_true, ↓reduceIte])

/-- **Uniform `NativeCertificate` for `branchedSparseCNFLeafCounter`** (§6.3–6.4). -/
noncomputable def branchedSparseCNFLeafCertificate (k N₀_leaf N₀_top N₀_branch : ℕ)
    {branchEval : BranchEvalInput → ℕ}
    (cBranch : NativeCertificate branchEval encBranchEvalInput encNat)
    (hbound : ∀ n' eqs', checkBranchFeasible N₀_branch (n', eqs') = true →
      branchEval (prepareBranchEvalInput (n', eqs')) ≤ 2 ^ n') :
    NativeCertificate (branchedSparseCNFLeafCounter k N₀_leaf N₀_top N₀_branch branchEval)
      (encPair (encPair encUnit encUnary) encCNF) encNat :=
  (normalizeDeclaredLeafCertificate (ComputableInPolyTime.snd encUnit encUnary)
    (branchedSparseCNFDeclaredCertificate k N₀_leaf N₀_top N₀_branch cBranch hbound)).congr
    fun _ => rfl

/-- **Global `PolyBounded` workspace for `branchedSparseCNFDeclaredCertificate`.** -/
theorem polyBounded_branchedSparseCNFDeclaredCertificate_space (k N₀_leaf N₀_top N₀_branch : ℕ)
    {branchEval : BranchEvalInput → ℕ}
    (cBranch : NativeCertificate branchEval encBranchEvalInput encNat)
    (hbound : ∀ n' eqs', checkBranchFeasible N₀_branch (n', eqs') = true →
      branchEval (prepareBranchEvalInput (n', eqs')) ≤ 2 ^ n')
    (hs_br : PolyBounded (fun x => (encBranchEvalInput x).length) cBranch.space) :
    PolyBounded (fun x : (Unit × ℕ) × CNF ℕ =>
        (encPair (encPair encUnit encUnary) encCNF x).length)
      (branchedSparseCNFDeclaredCertificate k N₀_leaf N₀_top N₀_branch cBranch hbound).space := by
  unfold branchedSparseCNFDeclaredCertificate
  have hpr := NativeCertificate.ofPolyTime_isPolynomial computableInPolyTime_leafExhProj
  exact polyBounded_branch_space _ _ _
    (NativeCertificate.ofPolyTime_isPolynomial (computableInPolyTime_denseFallbackGuard k)).2
    (hpr.2.add (polyBounded_countCNFExhaustive_space.comp
      computableInPolyTime_leafExhProj.polyBounded_length))
    (polyBounded_sparseCNFDeclaredCertificate_space k (max 1 N₀_leaf)
      (ComputableInPolyTime.snd encUnit encUnary) (computableInPolyTime_leafDensityRatio k)
      (branchedPolyCertificate k N₀_top N₀_branch cBranch hbound)
      (polyBounded_branchedPolyCertificate_space k N₀_top N₀_branch cBranch hbound hs_br))

/-- **Global `PolyBounded` workspace for `branchedSparseCNFLeafCertificate`.** -/
theorem polyBounded_branchedSparseCNFLeafCertificate_space (k N₀_leaf N₀_top N₀_branch : ℕ)
    {branchEval : BranchEvalInput → ℕ}
    (cBranch : NativeCertificate branchEval encBranchEvalInput encNat)
    (hbound : ∀ n' eqs', checkBranchFeasible N₀_branch (n', eqs') = true →
      branchEval (prepareBranchEvalInput (n', eqs')) ≤ 2 ^ n')
    (hs_br : PolyBounded (fun x => (encBranchEvalInput x).length) cBranch.space) :
    PolyBounded (fun x : (Unit × ℕ) × CNF ℕ =>
        (encPair (encPair encUnit encUnary) encCNF x).length)
      (branchedSparseCNFLeafCertificate k N₀_leaf N₀_top N₀_branch cBranch hbound).space :=
  polyBounded_normalizeDeclaredLeafCertificate_space
    (ComputableInPolyTime.snd encUnit encUnary) _
    (polyBounded_branchedSparseCNFDeclaredCertificate_space k N₀_leaf N₀_top N₀_branch
      cBranch hbound hs_br)

/-! ### 5. Fast-Regime `2 ^ {O_k(interpolationScale N)}` Runtime Envelope (§5.5, §6.3, §6.4) -/

/-- **Proposition 5.3 per-branch subexponential runtime hypothesis (`BranchPolylogTimeBound`)**:
for every degree cap `k_deg`, polylogarithmic exponent `β`, and prefactor `C_inc`, above a constant
threshold `N₀_br`, every feasible reduced branch `(n', sys')` with `sysMaxDegree sys' ≤ k_deg`,
`sys'.length ≤ C_inc * n'`, and neutral-augmented incidence and scope width
`≤ C_inc * ⌈log₂ n'⌉ ^ β` runs in at most
`C_br * (|enc (n', sys')| + 1) ^ d_br * 2 ^ (A_br * interpolationScale n')` steps. -/
def BranchPolylogTimeBound (N₀_branch : ℕ) {branchEval : BranchEvalInput → ℕ}
    (cBranch : NativeCertificate branchEval encBranchEvalInput encNat) : Prop :=
  ∀ k_deg β C_inc : ℕ, ∃ N₀_br C_br d_br A_br : ℕ,
    ∀ n' : ℕ, ∀ sys' : List (List (List ℕ)),
      checkBranchFeasible N₀_branch (n', sys') = true → N₀_br ≤ n' →
      sysMaxDegree sys' ≤ k_deg →
      sys'.length ≤ C_inc * n' →
      branchMaxFactorIncidence n' sys' ≤ C_inc * Nat.clog 2 n' ^ β →
      branchMaxFactorWidth n' sys' ≤ C_inc * Nat.clog 2 n' ^ β →
      (cBranch.time (prepareBranchEvalInput (n', sys')) : ℝ) ≤
        (C_br : ℝ) * ((encPair encUnary encSys (n', sys')).length + 1 : ℝ) ^ d_br *
          (2 : ℝ) ^ ((A_br : ℝ) * interpolationScale n')

private theorem interpolationScale_le_two_mul_of_le_two_mul {n' N : ℕ}
    (hn'_le : n' ≤ N) (hN_le : N ≤ 2 * n') :
    interpolationScale n' ≤ 2 * interpolationScale N := by
  rcases Nat.eq_zero_or_pos n' with rfl | hn'_pos
  · simp only [interpolationScale_zero]; linarith [interpolationScale_nonneg N]
  have h1_lt : 1 < Real.log ((n' : ℝ) + 16) := by
    rw [← Real.log_exp 1]
    exact Real.log_lt_log (Real.exp_pos 1)
      (by linarith [Real.exp_one_lt_d9, (Nat.cast_nonneg n' : (0 : ℝ) ≤ n')])
  have hX'_pos : 0 < Real.log ((n' : ℝ) + 16) := zero_lt_one.trans h1_lt
  have hX'_le_X : Real.log ((n' : ℝ) + 16) ≤ Real.log ((N : ℝ) + 16) :=
    Real.log_le_log (by positivity) (by linarith [show (n' : ℝ) ≤ N from Nat.cast_le.mpr hn'_le])
  have hX_pos : 0 < Real.log ((N : ℝ) + 16) := hX'_pos.trans_le hX'_le_X
  have hL_sq : Real.log (Real.log ((n' : ℝ) + 16)) ^ 2 ≤
      Real.log (Real.log ((N : ℝ) + 16)) ^ 2 :=
    pow_le_pow_left₀ (Real.log_pos h1_lt).le (Real.log_le_log hX'_pos hX'_le_X) 2
  have hX_le_4 : Real.log ((N : ℝ) + 16) ≤ (2 : ℝ) ^ 2 * Real.log ((n' : ℝ) + 16) := by
    have hN_sq : (N : ℝ) + 16 ≤ ((n' : ℝ) + 16) ^ 2 := by
      have : (N : ℝ) ≤ 2 * (n' : ℝ) := by exact_mod_cast hN_le
      nlinarith [sq_nonneg (n' : ℝ)]
    have hlog := Real.log_le_log (by positivity) hN_sq
    rw [Real.log_pow, Nat.cast_ofNat] at hlog; linarith
  have hsqrt_le : Real.sqrt (Real.log ((N : ℝ) + 16)) ≤
      2 * Real.sqrt (Real.log ((n' : ℝ) + 16)) :=
    (Real.sqrt_le_sqrt hX_le_4).trans_eq
      (by rw [Real.sqrt_mul (sq_nonneg (2 : ℝ)), Real.sqrt_sq zero_le_two])
  have hsX' : 0 < Real.sqrt (Real.log ((n' : ℝ) + 16)) := Real.sqrt_pos.mpr hX'_pos
  have hsX : 0 < Real.sqrt (Real.log ((N : ℝ) + 16)) := Real.sqrt_pos.mpr hX_pos
  unfold interpolationScale
  rw [mul_div_assoc', div_le_div_iff₀ hsX' hsX]
  have hmul := mul_le_mul
    (mul_le_mul (Nat.cast_le.mpr hn'_le) hL_sq (by positivity) (Nat.cast_nonneg N))
    hsqrt_le hsX.le (by positivity)
  linarith

private theorem scopeWidthOn_le_mul (N k maxTerms : ℕ) (eq : List (List ℕ))
    (hlen : eq.length ≤ maxTerms) (hdeg : ∀ m ∈ eq, m.length ≤ k) :
    scopeWidthOn N eq ≤ maxTerms * k := by
  have hsub : ((List.range N).filter fun u => eq.any fun m => decide (u ∈ m)).toFinset ⊆
      (eq.flatMap id).toFinset := fun u hu => by
    simp only [List.mem_toFinset, List.mem_filter, List.any_eq_true, decide_eq_true_eq,
      List.mem_flatMap, id_eq] at hu ⊢
    exact hu.2
  calc scopeWidthOn N eq
      = (((List.range N).filter fun u => eq.any fun m => decide (u ∈ m)).toFinset).card := by
        rw [scopeWidthOn, List.countP_eq_length_filter,
          List.toFinset_card_of_nodup (List.nodup_range.filter _)]
    _ ≤ (eq.flatMap id).toFinset.card := Finset.card_le_card hsub
    _ ≤ (eq.flatMap id).length := List.toFinset_card_le _
    _ ≤ eq.length * k := List.length_flatMap_le hdeg
    _ ≤ maxTerms * k := Nat.mul_le_mul_right k hlen

private theorem compiled_system_incidence_bounds (k C_B β_B : ℕ) :
    ∃ C_inc : ℕ, 12 ≤ C_inc ∧ ∀ {N m B : ℕ} {sys : List (List (List ℕ))},
      2 ≤ N → B ≤ C_B * Nat.clog 2 N ^ β_B → m ≤ B * N →
      IsCompiledSparseSystem k N (6 * N) (initialRowWeightBound B m * 2 ^ k) sys →
      let inp := mkPaperSparseInput N k sys
      inp.2.1.2.2 + 1 ≤ C_inc * Nat.clog 2 N ^ (2 * β_B + 4) ∧
        branchMaxFactorWidth N sys ≤ C_inc * Nat.clog 2 N ^ (2 * β_B + 4) := by
  set K_W := CNF.initialRowWeightCoeff C_B β_B
  set C_inc := 6 * k * 2 ^ k * K_W + 12
  refine ⟨C_inc, by dsimp only [C_inc]; omega, fun {N m B sys} hN2 hB hm hsys => ?_⟩
  set lam := Nat.clog 2 N
  have hlam1 : 1 ≤ lam := (Nat.lt_clog_iff_pow_lt Nat.one_lt_two).mpr (by omega : 2 ^ 0 < N)
  have hcz : ¬ Nat.clog 2 N = 0 := by omega
  have hW_le : initialRowWeightBound B m ≤ K_W * lam ^ (2 * β_B + 3) :=
    CNF.initialRowWeightBound_le_mul_pow_clog hN2 hm hB
  set T := initialRowWeightBound B m * 2 ^ k * k
  have hsc_all : ∀ eq ∈ sys, scopeWidthOn N eq ≤ T := fun eq heq =>
    scopeWidthOn_le_mul N k (initialRowWeightBound B m * 2 ^ k) eq (hsys.2 eq heq).2.1
      fun mon hmon => ((hsys.2 eq heq).2.2 mon hmon).1
  have hT_le : T ≤ (k * 2 ^ k * K_W) * lam ^ (2 * β_B + 3) := by
    calc T = k * 2 ^ k * initialRowWeightBound B m := by dsimp only [T]; ring
      _ ≤ k * 2 ^ k * (K_W * lam ^ (2 * β_B + 3)) := Nat.mul_le_mul_left _ hW_le
      _ = (k * 2 ^ k * K_W) * lam ^ (2 * β_B + 3) := by ring
  have hpow1 : 1 ≤ lam ^ (2 * β_B + 4) := Nat.one_le_pow _ lam hlam1
  have hpow_step : lam ^ (2 * β_B + 3) ≤ lam ^ (2 * β_B + 4) :=
    Nat.pow_le_pow_right hlam1 (by omega)
  have hw_le : branchMaxFactorWidth N sys ≤ C_inc * lam ^ (2 * β_B + 4) := by
    unfold branchMaxFactorWidth
    refine foldl_max_le (Nat.mul_pos (by dsimp only [C_inc]; omega) hpow1) fun w hw => ?_
    obtain ⟨eq, heq, rfl⟩ := List.mem_map.mp hw
    have h1 := (hsc_all eq heq).trans (hT_le.trans (Nat.mul_le_mul_left _ hpow_step))
    dsimp only [C_inc]; nlinarith
  have hsum_le : (sys.map (scopeWidthOn N)).sum ≤ (6 * T) * N := by
    calc (sys.map (scopeWidthOn N)).sum
        ≤ (sys.map fun _ => T).sum := List.sum_le_sum fun eq heq => hsc_all eq heq
      _ = sys.length * T := by rw [List.map_const', List.sum_replicate_nat]
      _ ≤ (6 * T) * N := (Nat.mul_le_mul_right T hsys.1).trans_eq (by ring)
  set M := branchAugmentedIncidence N sys
  have hdiv_M : (M + N - 1) / N ≤ 6 * T + 2 :=
    Nat.div_le_of_le_mul ((Nat.sub_le (M + N) 1).trans
      (by change (sys.map (scopeWidthOn N)).sum + N + N ≤ N * (6 * T + 2); nlinarith))
  have hcut_le : ParameterCheck.heavyIncidenceCutoff M N ≤ (6 * T + 2) * lam := by
    unfold ParameterCheck.heavyIncidenceCutoff; simp only [hcz, ↓reduceIte]
    have hsq : (Nat.clog 2 N - 1).sqrt + 1 ≤ lam := by
      change (lam - 1).sqrt + 1 ≤ lam; have := Nat.sqrt_le_self (lam - 1); omega
    exact Nat.mul_le_mul hdiv_M hsq
  have hb0_le : max 1 (ParameterCheck.heavyIncidenceCutoff M N) + 1 ≤
      C_inc * lam ^ (2 * β_B + 4) := by
    have hp3 : 1 ≤ lam ^ (2 * β_B + 3) := Nat.one_le_pow _ lam hlam1
    have h6T : (6 * T + 2) * lam ≤ (6 * k * 2 ^ k * K_W + 2) * lam ^ (2 * β_B + 4) :=
      (Nat.mul_le_mul_right lam
        (show 6 * T + 2 ≤ (6 * (k * 2 ^ k * K_W) + 2) * lam ^ (2 * β_B + 3) by nlinarith)).trans_eq
        (by rw [pow_succ]; ring)
    have h1 : max 1 (ParameterCheck.heavyIncidenceCutoff M N) + 1 ≤ (6 * T + 2) * lam + 1 :=
      Nat.add_le_add_right (max_le (show 1 ≤ (6 * T + 2) * lam by nlinarith) hcut_le) 1
    dsimp only [C_inc]; nlinarith
  exact ⟨hb0_le, hw_le⟩

private theorem nat_poly_le_subexp {t C L d d_max : ℕ} {A X : ℝ}
    (ht : t ≤ C * (L + 1) ^ d) (hd : d ≤ d_max) (hA : 0 ≤ A) (hX : 0 ≤ X) :
    (t : ℝ) ≤ (C : ℝ) * (L + 1 : ℝ) ^ d_max * (2 : ℝ) ^ (A * X) := by
  have hc : (t : ℝ) ≤ (C : ℝ) * (L + 1 : ℝ) ^ d_max := by
    exact_mod_cast ht.trans (Nat.mul_le_mul_left C (Nat.pow_le_pow_right (Nat.succ_pos L) hd))
  exact (hc.trans_eq (mul_one _).symm).trans
    (mul_le_mul_of_nonneg_left (Real.one_le_rpow one_le_two (mul_nonneg hA hX)) (by positivity))

private theorem ceil_subexp_le {C L d d_max : ℕ} {A X : ℝ}
    (hd : d ≤ d_max) (hA : 0 ≤ A) (hX : 0 ≤ X) :
    (⌈((C : ℕ) : ℝ) * (L + 1 : ℝ) ^ d * (2 : ℝ) ^ (A * X)⌉₊ : ℝ) ≤
      ((C + 1 : ℕ) : ℝ) * (L + 1 : ℝ) ^ d_max * (2 : ℝ) ^ (A * X) := by
  have hbase : (1 : ℝ) ≤ (L + 1 : ℝ) := by exact_mod_cast Nat.succ_pos L
  have hd_le : (L + 1 : ℝ) ^ d ≤ (L + 1 : ℝ) ^ d_max := pow_le_pow_right₀ hbase hd
  have htwo : (1 : ℝ) ≤ (2 : ℝ) ^ (A * X) := Real.one_le_rpow one_le_two (mul_nonneg hA hX)
  have hceil := (Nat.ceil_lt_add_one
    (by positivity : 0 ≤ ((C : ℕ) : ℝ) * (L + 1 : ℝ) ^ d * (2 : ℝ) ^ (A * X))).le
  have hw := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hd_le (Nat.cast_nonneg C)) (zero_le_one.trans htwo)
  have h1 := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hbase (n := d_max)) htwo
  push_cast; linarith

private theorem comp_poly_pow_le {len C_l L d_l d d_all : ℕ}
    (hM : len + 1 ≤ (C_l + 1) * (L + 1) ^ d_l) (hd : d ≤ d_all) :
    (len + 1 : ℝ) ^ d ≤ (((C_l + 1) ^ d_all : ℕ) : ℝ) * (L + 1 : ℝ) ^ (d_l * d_all) := by
  have hnat : (len + 1) ^ d ≤ (C_l + 1) ^ d_all * (L + 1) ^ (d_l * d_all) :=
    (Nat.pow_le_pow_right (Nat.succ_pos len) hd).trans
      ((Nat.pow_le_pow_left hM d_all).trans_eq (by rw [mul_pow, ← pow_mul]))
  exact_mod_cast hnat

private theorem polySys_time_bound_of_branchPolylog (k N₀_top N₀_branch : ℕ)
    {branchEval : BranchEvalInput → ℕ}
    (cBranch : NativeCertificate branchEval encBranchEvalInput encNat)
    (hbound : ∀ n' eqs', checkBranchFeasible N₀_branch (n', eqs') = true →
      branchEval (prepareBranchEvalInput (n', eqs')) ≤ 2 ^ n')
    (hbr_time : BranchPolylogTimeBound N₀_branch cBranch) :
    ∃ N_sys C_sys d_sys A_sys : ℕ, 16384 ≤ N_sys ∧
      ∀ {N m : ℕ} {sys : List (List (List ℕ))},
        N_sys ≤ N → m ≤ leafDensityRatio k N * N →
        IsCompiledSparseSystem k N (6 * N)
          (initialRowWeightBound (leafDensityRatio k N) m * 2 ^ k) sys →
        ((branchedPolyCertificate k N₀_top N₀_branch cBranch hbound).time (N, sys) : ℝ) ≤
          (C_sys : ℝ) * ((encPair encUnary encSys (N, sys)).length + 1 : ℝ) ^ d_sys *
            (2 : ℝ) ^ ((A_sys : ℝ) * interpolationScale N) := by
  obtain ⟨C_B, hCB⟩ := exists_leafDensityRatio_le_mul_clog_pow k
  set β_B := 2 * (max 2 k - 1)
  obtain ⟨C_inc, hCinc12, hInc⟩ := compiled_system_incidence_bounds k C_B β_B
  set α_inc := 2 * β_B + 4; set β₀ := 2 * α_inc + 1
  obtain ⟨N₁, _, hBranchOk⟩ :=
    exists_threshold_checkBranchFeasible_eq_true N₀_branch (β₀ := β₀) (by dsimp only [β₀]; omega)
  obtain ⟨N₀_br, C_br, d_br, A_br, hBrT⟩ := hbr_time k (2 * α_inc) C_inc
  obtain ⟨C_g, d_g, hGuardT⟩ := exists_guardedBranchCertificate_time_le N₀_branch 0 cBranch
  obtain ⟨C_ov, d_ov, hFeasT⟩ :=
    sparsePolyCounterCertificate_time_le_of_feasible N₀_top N₀_branch cBranch hbound
  have hmk := computableInPolyTime_mkPaperInputConst k
  obtain ⟨C_mk, d_mk, hMkT⟩ := (NativeCertificate.ofPolyTime_isPolynomial hmk).1.exists_le
  obtain ⟨C_ml, d_ml, hMkLen⟩ := hmk.polyBounded_length.exists_le
  obtain ⟨C_bl, d_bl, hBrLen⟩ :=
    (computableInPolyTime_toBranchInput.polyBounded_length.comp hmk.polyBounded_length).exists_le
  set N_sys := max (max 16384 N₀_top) (max (2 * max N₁ N₀_br) (2 * 2 ^ C_inc))
  set d_br_all := max d_br d_g
  set d_in := max (d_ml * d_ov) (max (d_bl * d_br_all) d_mk)
  set C_p1 := C_ov * (C_ml + 1) ^ d_ov; set C_p2 := (C_br + C_g) * (C_bl + 1) ^ d_br_all
  set C_sys := C_mk + 2 * (C_p1 + C_p2 + 1); set A_sys := 2 * A_br + 32
  refine ⟨N_sys, C_sys, d_in, A_sys, le_trans (le_max_left 16384 N₀_top) (le_max_left _ _),
    fun {N m sys} hN hm hsys => ?_⟩
  have hN16 : 16384 ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hN_top : max N₀_top 2 ≤ N :=
    max_le (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN) (by omega)
  set inp := mkPaperSparseInput N k sys
  have hinp1 : inp.1 = N := rfl; have hinp_sys : inp.2.2 = sys := rfl
  have htop : checkTopFeasible N₀_top inp = true :=
    checkTopFeasible_mkPaperSparseInput_of_le hN_top (fun eq heq => (hsys.2 eq heq).1)
      (fun eq heq mon hmon v hv => ((hsys.2 eq heq).2.2 mon hmon).2 v hv)
      (fun eq heq mon hmon => ((hsys.2 eq heq).2.2 mon hmon).1)
  obtain ⟨hb0_inc, hw_inc⟩ := hInc (by omega : 2 ≤ N) (hCB N (by omega)) hm hsys
  set lam := Nat.clog 2 N
  have hlam14 : 14 ≤ lam := by
    have := (Nat.lt_clog_iff_pow_lt Nat.one_lt_two).mpr (show 2 ^ 13 < N by omega); omega
  have hs_eq : inp.2.1.2.1 = (lam - 1).sqrt + 1 := by
    have hcz : ¬ Nat.clog 2 N = 0 := by omega
    have hc : ParameterCheck.heavyIncidenceCutoff 1 N = (lam - 1).sqrt + 1 := by
      unfold ParameterCheck.heavyIncidenceCutoff; simp only [hcz, ↓reduceIte]
      rw [show 1 + N - 1 = N by omega, Nat.div_self (by omega : 0 < N), one_mul]
    change max 1 (ParameterCheck.heavyIncidenceCutoff 1 N) = _; rw [hc]; omega
  have hs2 : 2 ≤ inp.2.1.2.1 := by
    rw [hs_eq]; have := Nat.le_sqrt.mpr (show 1 * 1 ≤ lam - 1 by omega); omega
  have hsqrt_le_s : lam.sqrt ≤ inp.2.1.2.1 := by
    rw [hs_eq]; by_contra hgt
    have h1 : ((lam - 1).sqrt + 2) * ((lam - 1).sqrt + 2) ≤ lam := Nat.le_sqrt.mp (by omega)
    have h2 := Nat.lt_succ_sqrt (lam - 1); simp only [Nat.succ_eq_add_one] at h2
    nlinarith [show lam = (lam - 1) + 1 by omega]
  have hS_le_sqrt : (HeavyBranchFold.heavyVarList N inp.2.1.2.2 sys).length ≤ N / lam.sqrt :=
    (checkTopFeasible_eq_true_iff.mp htop).2.2.2.2.2.trans
      (Nat.div_le_div_left hsqrt_le_s (Nat.sqrt_pos.mpr (by omega)))
  set Ly := (encPair encUnary encSys (N, sys)).length
  have hinp_len : (encSparseSystemInput inp).length + 1 ≤ (C_ml + 1) * (Ly + 1) ^ d_ml := by
    have h := hMkLen (N, sys); have hp := Nat.one_le_pow d_ml (Ly + 1) (Nat.succ_pos Ly)
    dsimp only [inp]; nlinarith
  have hbr_in_len : (HeavyBranchFold.encBranchInput (toBranchInput inp)).length + 1 ≤
      (C_bl + 1) * (Ly + 1) ^ d_bl := by
    have h := hBrLen (N, sys); have hp := Nat.one_le_pow d_bl (Ly + 1) (Nat.succ_pos Ly)
    dsimp only [inp]; nlinarith
  have hrho_nn : 0 ≤ interpolationScale N := interpolationScale_nonneg N
  set R_branch : ℕ := ⌈((C_p2 : ℕ) : ℝ) * (Ly + 1 : ℝ) ^ (d_bl * d_br_all) *
    (2 : ℝ) ^ ((2 * (A_br : ℝ)) * interpolationScale N)⌉₊
  have hper_branch : ∀ idx < 2 ^ (HeavyBranchFold.heavyVarList inp.1 inp.2.1.2.2 inp.2.2).length,
      ∀ n' sys', HeavyBranchFold.prepareBranch inp.1
        (HeavyBranchFold.heavyVarList inp.1 inp.2.1.2.2 inp.2.2)
        (lowBits (HeavyBranchFold.heavyVarList inp.1 inp.2.1.2.2 inp.2.2).length idx)
        inp.2.2 = .reduced n' sys' →
        (guardedBranchCertificate N₀_branch cBranch).time (n', sys') ≤ R_branch := by
    intro idx _ n' sys' hred
    obtain ⟨hn'_eq, hN_2n', hcan', hvars', hdeg', hb', hw'⟩ :=
      reduced_branch_invariants htop hs2 hred
    rw [hinp1] at hn'_eq hN_2n'
    have hn'_le_N : n' ≤ N := hn'_eq.symm ▸ Nat.sub_le N _
    have hn'_N1_br : max N₁ N₀_br ≤ n' := by
      have : 2 * max N₁ N₀_br ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
      omega
    have hCinc_le_clog : C_inc ≤ Nat.clog 2 n' := by
      have : 2 * 2 ^ C_inc ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN
      exact (Nat.clog_pow 2 C_inc Nat.one_lt_two).symm.le.trans (Nat.clog_mono_right 2 (by omega))
    have hclog_tr := clog_pow_le_clog_pow_two_mul (by omega : 4 ≤ n') hN_2n' α_inc
    have hb_2a := hb'.trans (hb0_inc.trans (Nat.mul_le_mul_left C_inc hclog_tr))
    have hw_2a := hw'.trans (hw_inc.trans (Nat.mul_le_mul_left C_inc hclog_tr))
    have hb_b0 : branchMaxFactorIncidence n' sys' ≤ Nat.clog 2 n' ^ β₀ :=
      (hb_2a.trans (Nat.mul_le_mul_right _ hCinc_le_clog)).trans_eq
        (by dsimp only [β₀]; rw [pow_succ'])
    have hw_b0 : branchMaxFactorWidth n' sys' ≤ Nat.clog 2 n' ^ β₀ :=
      (hw_2a.trans (Nat.mul_le_mul_right _ hCinc_le_clog)).trans_eq
        (by dsimp only [β₀]; rw [pow_succ'])
    have hlen_sys' : sys'.length ≤ C_inc * n' := by
      obtain ⟨_, _, _, hsys'_eq⟩ := HeavyBranchFold.prepareBranch_eq_reduced_iff.mp hred
      have hle6 : sys'.length ≤ 6 * N := by
        rw [hsys'_eq, List.length_map]
        exact (List.length_filter_le _ _).trans (by rw [List.length_map, hinp_sys]; exact hsys.1)
      exact (hle6.trans (by omega : 6 * N ≤ 12 * n')).trans (Nat.mul_le_mul_right n' hCinc12)
    have hchk : checkBranchFeasible N₀_branch (n', sys') = true :=
      (hBranchOk ((le_max_left N₁ N₀_br).trans hn'_N1_br) hcan' hvars' hb_b0 hw_b0).2.2
    have hgt := hGuardT (n', sys') (by simp only [hchk, Bool.true_eq_false, IsEmpty.forall_iff])
    simp only [hchk, ↓reduceIte] at hgt
    have hc_br := hBrT n' sys' hchk ((le_max_right N₁ N₀_br).trans hn'_N1_br)
      (sysMaxDegree_le_iff.mpr hdeg') hlen_sys' hb_2a hw_2a
    have hlen_red := (Nat.add_le_add_right (HeavyBranchFold.length_enc_reduced_le hred) 1).trans
      hbr_in_len
    have hp_br := comp_poly_pow_le hlen_red (le_max_left d_br d_g)
    have hexp_tr : (2 : ℝ) ^ ((A_br : ℝ) * interpolationScale n') ≤
        (2 : ℝ) ^ ((2 * (A_br : ℝ)) * interpolationScale N) :=
      Real.rpow_le_rpow_of_exponent_le one_le_two (by
        have hsc := interpolationScale_le_two_mul_of_le_two_mul hn'_le_N hN_2n'
        nlinarith [(Nat.cast_nonneg A_br : (0 : ℝ) ≤ A_br)])
    have ht2_nat : C_g * ((encPair encUnary encSys (n', sys')).length + 1) ^ d_g ≤
        (C_g * (C_bl + 1) ^ d_br_all) * (Ly + 1) ^ (d_bl * d_br_all) :=
      (Nat.mul_le_mul_left C_g ((Nat.pow_le_pow_right (Nat.succ_pos _)
        (le_max_right d_br d_g)).trans
        ((Nat.pow_le_pow_left hlen_red d_br_all).trans_eq (by rw [mul_pow, ← pow_mul])))).trans_eq
        (mul_assoc _ _ _).symm
    have ht2 := nat_poly_le_subexp ht2_nat le_rfl (by positivity : (0 : ℝ) ≤ 2 * (A_br : ℝ)) hrho_nn
    have ht1 : (cBranch.time (prepareBranchEvalInput (n', sys')) : ℝ) ≤
        (C_br : ℝ) * (((C_bl + 1) ^ d_br_all : ℕ) : ℝ) * (Ly + 1 : ℝ) ^ (d_bl * d_br_all) *
          (2 : ℝ) ^ ((2 * (A_br : ℝ)) * interpolationScale N) :=
      (hc_br.trans (mul_le_mul (mul_le_mul_of_nonneg_left hp_br (Nat.cast_nonneg C_br))
        hexp_tr (by positivity) (by positivity))).trans_eq (by dsimp only [d_br_all]; ring)
    have htot_br : ((guardedBranchCertificate N₀_branch cBranch).time (n', sys') : ℝ) ≤
        (C_p2 : ℝ) * (Ly + 1 : ℝ) ^ (d_bl * d_br_all) *
          (2 : ℝ) ^ ((2 * (A_br : ℝ)) * interpolationScale N) := by
      have hgt_cast : ((guardedBranchCertificate N₀_branch cBranch).time (n', sys') : ℝ) ≤
          (cBranch.time (prepareBranchEvalInput (n', sys')) : ℝ) +
            ((C_g * ((encPair encUnary encSys (n', sys')).length + 1) ^ d_g : ℕ) : ℝ) := by
        exact_mod_cast hgt
      exact hgt_cast.trans ((add_le_add ht1 ht2).trans_eq (by dsimp only [C_p2]; push_cast; ring))
    exact Nat.cast_le.mp (htot_br.trans (Nat.le_ceil _))
  have hsp_t := hFeasT inp R_branch htop hper_branch
  have hcov_nat : C_ov * ((encSparseSystemInput inp).length + 1) ^ d_ov ≤
      C_p1 * (Ly + 1) ^ (d_ml * d_ov) :=
    (Nat.mul_le_mul_left C_ov (Nat.pow_le_pow_left hinp_len d_ov)).trans_eq
      (by dsimp only [C_p1]; rw [mul_pow, ← pow_mul, mul_assoc])
  have hcov_r := nat_poly_le_subexp hcov_nat (le_max_left _ _ : d_ml * d_ov ≤ d_in)
    (by positivity : (0 : ℝ) ≤ 2 * (A_br : ℝ)) hrho_nn
  have hRbr_r : (R_branch : ℝ) ≤ ((C_p2 + 1 : ℕ) : ℝ) * (Ly + 1 : ℝ) ^ d_in *
      (2 : ℝ) ^ ((2 * (A_br : ℝ)) * interpolationScale N) :=
    ceil_subexp_le ((le_max_left _ _).trans (le_max_right _ _)) (by positivity) hrho_nn
  have hinner_r :
      (((C_ov * ((encSparseSystemInput inp).length + 1) ^ d_ov + R_branch : ℕ)) : ℝ) ≤
        ((C_p1 + C_p2 + 1 : ℕ) : ℝ) * (Ly + 1 : ℝ) ^ d_in *
          (2 : ℝ) ^ ((2 * (A_br : ℝ)) * interpolationScale N) := by
    rw [Nat.cast_add, show ((C_p1 + C_p2 + 1 : ℕ) : ℝ) = (C_p1 : ℝ) + ((C_p2 + 1 : ℕ) : ℝ) by
      push_cast; ring, add_mul, add_mul]
    exact add_le_add hcov_r hRbr_r
  have hS_pow_r :
      ((2 ^ (HeavyBranchFold.heavyVarList inp.1 inp.2.1.2.2 inp.2.2).length + 1 : ℕ) : ℝ) ≤
        2 * (2 : ℝ) ^ (32 * interpolationScale N) := by
    have hpow_le : (2 ^ (HeavyBranchFold.heavyVarList N inp.2.1.2.2 sys).length : ℝ) ≤
        (2 : ℝ) ^ (32 * interpolationScale N) :=
      (pow_le_pow_right₀ one_le_two hS_le_sqrt).trans
        (ReplacementParams.two_pow_div_sqrt_clog_le_interpolationScale hN16)
    have h1_32 : (1 : ℝ) ≤ (2 : ℝ) ^ (32 * interpolationScale N) :=
      Real.one_le_rpow one_le_two (mul_nonneg (by positivity) hrho_nn)
    rw [hinp1, hinp_sys]; push_cast; linarith only [hpow_le, h1_32]
  have hsp_r : ((sparsePolyCounterCertificate N₀_top N₀_branch cBranch hbound).time inp : ℝ) ≤
      ((2 * (C_p1 + C_p2 + 1) : ℕ) : ℝ) * (Ly + 1 : ℝ) ^ d_in *
        (2 : ℝ) ^ ((A_sys : ℝ) * interpolationScale N) := by
    have hcast : ((sparsePolyCounterCertificate N₀_top N₀_branch cBranch hbound).time inp : ℝ) ≤
        ((2 ^ (HeavyBranchFold.heavyVarList inp.1 inp.2.1.2.2 inp.2.2).length + 1 : ℕ) : ℝ) *
          (((C_ov * ((encSparseSystemInput inp).length + 1) ^ d_ov + R_branch : ℕ)) : ℝ) := by
      exact_mod_cast hsp_t
    calc ((sparsePolyCounterCertificate N₀_top N₀_branch cBranch hbound).time inp : ℝ)
        ≤ (2 * (2 : ℝ) ^ (32 * interpolationScale N)) *
            (((C_p1 + C_p2 + 1 : ℕ) : ℝ) * (Ly + 1 : ℝ) ^ d_in *
              (2 : ℝ) ^ ((2 * (A_br : ℝ)) * interpolationScale N)) :=
          hcast.trans (mul_le_mul hS_pow_r hinner_r (by positivity) (by positivity))
      _ = ((2 * (C_p1 + C_p2 + 1) : ℕ) : ℝ) * (Ly + 1 : ℝ) ^ d_in *
            ((2 : ℝ) ^ (32 * interpolationScale N) *
              (2 : ℝ) ^ ((2 * (A_br : ℝ)) * interpolationScale N)) := by push_cast; ring
      _ = ((2 * (C_p1 + C_p2 + 1) : ℕ) : ℝ) * (Ly + 1 : ℝ) ^ d_in *
            (2 : ℝ) ^ ((A_sys : ℝ) * interpolationScale N) := by
          rw [← Real.rpow_add two_pos]; dsimp only [A_sys]; push_cast; ring_nf
  have hmk_r := nat_poly_le_subexp (hMkT (N, sys))
    ((le_max_right _ _).trans (le_max_right _ _) : d_mk ≤ d_in) (Nat.cast_nonneg A_sys) hrho_nn
  have htot : (branchedPolyCertificate k N₀_top N₀_branch cBranch hbound).time (N, sys) =
      (NativeCertificate.ofPolyTime hmk).time (N, sys) +
        (sparsePolyCounterCertificate N₀_top N₀_branch cBranch hbound).time inp := rfl
  rw [htot, Nat.cast_add,
    show (C_sys : ℝ) = (C_mk : ℝ) + ((2 * (C_p1 + C_p2 + 1) : ℕ) : ℝ) from Nat.cast_add _ _,
    add_mul, add_mul]
  exact add_le_add hmk_r hsp_r

private theorem exists_branchedSparseCNFLeafCertificate_time_le
    (k N₀_leaf N₀_top N₀_branch : ℕ) {branchEval : BranchEvalInput → ℕ}
    (cBranch : NativeCertificate branchEval encBranchEvalInput encNat)
    (hbound : ∀ n' eqs', checkBranchFeasible N₀_branch (n', eqs') = true →
      branchEval (prepareBranchEvalInput (n', eqs')) ≤ 2 ^ n')
    (hs_br : PolyBounded (fun x => (encBranchEvalInput x).length) cBranch.space) :
    ∃ C_nm d_nm : ℕ, ∀ x : (Unit × ℕ) × CNF ℕ,
      (branchedSparseCNFLeafCertificate k N₀_leaf N₀_top N₀_branch cBranch hbound).time x ≤
        (branchedSparseCNFDeclaredCertificate k N₀_leaf N₀_top N₀_branch cBranch hbound).time x +
          C_nm * ((encLeafIn x).length + 1) ^ d_nm := by
  obtain ⟨pNorm, hpNorm, _, hNormT⟩ := exists_normalizeDeclaredLeafCertificate_bounds
    (ComputableInPolyTime.snd encUnit encUnary)
    (branchedSparseCNFDeclaredCertificate k N₀_leaf N₀_top N₀_branch cBranch hbound)
    (polyBounded_branchedSparseCNFDeclaredCertificate_space k N₀_leaf N₀_top N₀_branch
      cBranch hbound hs_br)
  obtain ⟨C_nm, d_nm, hNm⟩ :=
    (PolyBounded.of_polynomiallyBounded (fun n : ℕ => n) hpNorm).exists_le
  refine ⟨C_nm, d_nm, fun x => ?_⟩
  have h1 : (branchedSparseCNFLeafCertificate k N₀_leaf N₀_top N₀_branch cBranch hbound).time x ≤
      (branchedSparseCNFDeclaredCertificate k N₀_leaf N₀_top N₀_branch cBranch hbound).time x +
        pNorm (encLeafIn x).length := by
    unfold branchedSparseCNFLeafCertificate; exact hNormT x
  exact h1.trans (Nat.add_le_add_left (hNm (encLeafIn x).length) _)

private theorem fast_path_arith_bound
    {C_B β_B C_qi d_qi C_i d_i N_init PowE C_pol d_pol C_R0 d_R0 A_sys d_t C_dg C_ex0 C_decl : ℕ}
    {N m B L poly_L q_val t_dg t_in : ℕ}
    (hCi : C_i = C_qi * (C_B + CNF.initialRowWeightCoeff (C_B + 1) β_B) ^ d_qi)
    (hdi : d_i = (2 * β_B + 3) * d_qi)
    (hPowE : PowE = 2 ^ (C_i * Nat.clog 2 N_init ^ d_i))
    (hNinit : ∀ n, N_init ≤ n →
      (2 : ℝ) ^ ((C_i : ℝ) * (Nat.clog 2 n : ℝ) ^ d_i) ≤ (2 : ℝ) ^ (1 * interpolationScale n))
    (hNq : ∀ m' B' P' : ℕ, m' ≤ B' * N → B' ≤ C_B * Nat.clog 2 N ^ β_B →
      P' ≤ 20000 * B' ^ 2 * Nat.clog 2 (2 * m' + 4) ^ 2 →
      3 * (N : ℝ) * (2 * (m' : ℝ) + 2) ^ P' + 1 ≤ (2 : ℝ) ^ (1 * interpolationScale N))
    (hN2 : 2 ≤ N) (hm1 : 1 ≤ m) (hmB : m ≤ B * N) (hB : B ≤ C_B * Nat.clog 2 N ^ β_B)
    (hQi : q_val ≤ C_qi * (B + Nat.log 2 (m + 2) + 1) ^ d_qi)
    (hPol : poly_L ≤ C_pol * (L + 1) ^ d_pol) (hd_pol : d_pol ≤ d_t) (hd_R0 : d_R0 ≤ d_t)
    (hdg_r : (t_dg : ℝ) ≤
      (C_dg : ℝ) * (L + 1 : ℝ) ^ d_t * (2 : ℝ) ^ (((A_sys + 1 : ℕ) : ℝ) * interpolationScale N))
    (hin_le : t_in ≤ 2 * (poly_L + 2 ^ q_val +
      (3 * N + 1) * (candidateTupleCount m (greedyRowListLength B m) + 1) *
        (poly_L + ⌈((C_R0 : ℕ) : ℝ) * (L + 1 : ℝ) ^ d_R0 *
          (2 : ℝ) ^ ((A_sys : ℝ) * interpolationScale N)⌉₊) + 1))
    (hC_decl : C_decl = C_dg + C_ex0 + 2 * (C_pol + PowE + 3 * (C_pol + C_R0 + 1) + 1)) :
    (t_dg : ℝ) + (t_in : ℝ) ≤
      (C_decl : ℝ) * (L + 1 : ℝ) ^ d_t *
        (2 : ℝ) ^ (((A_sys + 1 : ℕ) : ℝ) * interpolationScale N) := by
  set lam := Nat.clog 2 N; set A_t := A_sys + 1
  set R_x := ⌈((C_R0 : ℕ) : ℝ) * (L + 1 : ℝ) ^ d_R0 *
    (2 : ℝ) ^ ((A_sys : ℝ) * interpolationScale N)⌉₊
  have hrho_nn : 0 ≤ interpolationScale N := interpolationScale_nonneg N
  have h1_dt : (1 : ℝ) ≤ (L + 1 : ℝ) ^ d_t := one_le_pow₀ (by exact_mod_cast Nat.succ_pos L)
  have htwo_At : (1 : ℝ) ≤ (2 : ℝ) ^ ((A_t : ℝ) * interpolationScale N) :=
    Real.one_le_rpow one_le_two (mul_nonneg (Nat.cast_nonneg A_t) hrho_nn)
  have h1_to_At : (2 : ℝ) ^ (1 * interpolationScale N) ≤
      (2 : ℝ) ^ ((A_t : ℝ) * interpolationScale N) :=
    Real.rpow_le_rpow_of_exponent_le one_le_two
      (mul_le_mul_of_nonneg_right (by exact_mod_cast (Nat.succ_pos A_sys : 1 ≤ A_t)) hrho_nn)
  have hlam1 : 1 ≤ lam := (Nat.lt_clog_iff_pow_lt Nat.one_lt_two).mpr (by omega : 2 ^ 0 < N)
  have hinit_exp : q_val ≤ C_i * lam ^ d_i := by
    have hm2_le : m + 2 ≤ (B + 1) * N := by nlinarith only [hmB, hN2]
    have hB1_le : B + 1 ≤ (C_B + 1) * lam ^ β_B := by
      have hp := Nat.one_le_pow β_B lam hlam1; nlinarith only [hB, hp]
    have hW2 := CNF.initialRowWeightBound_le_mul_pow_clog hN2 hm2_le hB1_le
    have hlog_m2 : Nat.log 2 (m + 2) + 1 ≤
        CNF.initialRowWeightCoeff (C_B + 1) β_B * lam ^ (2 * β_B + 3) := by
      refine le_trans ?_ hW2; unfold initialRowWeightBound
      exact (Nat.le_self_pow (by decide : 3 ≠ 0) _).trans
        (Nat.le_mul_of_pos_left _ (by positivity))
    have hu_le : B + Nat.log 2 (m + 2) + 1 ≤
        (C_B + CNF.initialRowWeightCoeff (C_B + 1) β_B) * lam ^ (2 * β_B + 3) := by
      have hB' : B ≤ C_B * lam ^ (2 * β_B + 3) :=
        hB.trans (Nat.mul_le_mul_left C_B (Nat.pow_le_pow_right hlam1 (by omega)))
      rw [Nat.add_assoc]; exact (Nat.add_le_add hB' hlog_m2).trans_eq (Nat.add_mul _ _ _).symm
    exact hQi.trans ((Nat.mul_le_mul_left C_qi (Nat.pow_le_pow_left hu_le d_qi)).trans_eq
      (by rw [hCi, hdi, mul_pow, ← pow_mul, mul_assoc]))
  have hqinit_r : ((2 ^ q_val : ℕ) : ℝ) ≤
      (PowE : ℝ) * (L + 1 : ℝ) ^ d_t * (2 : ℝ) ^ ((A_t : ℝ) * interpolationScale N) := by
    have hbase_init : ((2 ^ q_val : ℕ) : ℝ) ≤
        (PowE : ℝ) * (2 : ℝ) ^ (1 * interpolationScale N) := by
      by_cases hNi : N_init ≤ N
      · have h1 : ((2 ^ q_val : ℕ) : ℝ) ≤ (2 : ℝ) ^ ((C_i : ℝ) * (lam : ℝ) ^ d_i) := by
          rw [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast]
          exact Real.rpow_le_rpow_of_exponent_le one_le_two (by exact_mod_cast hinit_exp)
        have h2 : (1 : ℝ) ≤ (PowE : ℝ) := by rw [hPowE]; exact_mod_cast Nat.one_le_two_pow
        exact (h1.trans (hNinit N hNi)).trans (le_mul_of_one_le_left (by positivity) h2)
      · have he_le : q_val ≤ C_i * Nat.clog 2 N_init ^ d_i :=
          hinit_exp.trans (Nat.mul_le_mul_left C_i
            (Nat.pow_le_pow_left (Nat.clog_mono_right 2 (by omega)) d_i))
        have h1 : ((2 ^ q_val : ℕ) : ℝ) ≤ (PowE : ℝ) := by
          rw [hPowE]; exact Nat.cast_le.mpr (Nat.pow_le_pow_right Nat.zero_lt_two he_le)
        exact h1.trans (le_mul_of_one_le_right (by positivity)
          (Real.one_le_rpow one_le_two (mul_nonneg zero_le_one hrho_nn)))
    exact ((hbase_init.trans (mul_le_mul_of_nonneg_left h1_to_At (by positivity))).trans
      (mul_le_mul_of_nonneg_left ((one_mul _).symm.le.trans
        (mul_le_mul_of_nonneg_right h1_dt (by positivity))) (by positivity))).trans_eq (by ring)
  set P := greedyRowListLength B m
  have hP_le : P ≤ 20000 * B ^ 2 * Nat.clog 2 (2 * m + 4) ^ 2 := by
    have hlt_clog : Nat.log 2 m < Nat.clog 2 (2 * m + 4) := by
      rw [Nat.lt_clog_iff_pow_lt Nat.one_lt_two]
      have := Nat.pow_log_le_self 2 (by omega : m ≠ 0); omega
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)
  have hcand_r : (((3 * N + 1) * (candidateTupleCount m P + 1) : ℕ) : ℝ) ≤
      3 * (2 : ℝ) ^ (1 * interpolationScale N) := by
    have hq_ev := hNq m B P hmB hB hP_le
    have hcand_le : candidateTupleCount m P ≤ (2 * m + 2) ^ P := Nat.pow_le_pow_left (by omega) P
    have hp_pos : 1 ≤ (2 * m + 2) ^ P := Nat.one_le_pow P _ (by omega)
    have hnat_ineq : (3 * N + 1) * (candidateTupleCount m P + 1) ≤
        3 * (3 * N * (2 * m + 2) ^ P + 1) :=
      (Nat.mul_le_mul (by omega : 3 * N + 1 ≤ 4 * N)
        (by omega : candidateTupleCount m P + 1 ≤ 2 * (2 * m + 2) ^ P)).trans
        (calc (4 * N) * (2 * (2 * m + 2) ^ P) = 8 * (N * (2 * m + 2) ^ P) := by ring
          _ ≤ 3 * (3 * N * (2 * m + 2) ^ P + 1) := by rw [mul_assoc 3 N]; omega)
    have hcast : (((3 * N + 1) * (candidateTupleCount m P + 1) : ℕ) : ℝ) ≤
        3 * (3 * (N : ℝ) * (2 * (m : ℝ) + 2) ^ P + 1) := by exact_mod_cast hnat_ineq
    exact hcast.trans (mul_le_mul_of_nonneg_left hq_ev zero_le_three)
  have hpolR_r : ((poly_L + R_x : ℕ) : ℝ) ≤ ((C_pol + C_R0 + 1 : ℕ) : ℝ) * (L + 1 : ℝ) ^ d_t *
      (2 : ℝ) ^ ((A_sys : ℝ) * interpolationScale N) := by
    rw [Nat.cast_add, show ((C_pol + C_R0 + 1 : ℕ) : ℝ) = (C_pol : ℝ) + ((C_R0 + 1 : ℕ) : ℝ) by
      push_cast; ring, add_mul, add_mul]
    exact add_le_add (nat_poly_le_subexp hPol hd_pol (Nat.cast_nonneg A_sys) hrho_nn)
      (ceil_subexp_le hd_R0 (Nat.cast_nonneg A_sys) hrho_nn)
  have hprod_r : (((3 * N + 1) * (candidateTupleCount m P + 1) * (poly_L + R_x) : ℕ) : ℝ) ≤
      ((3 * (C_pol + C_R0 + 1) : ℕ) : ℝ) * (L + 1 : ℝ) ^ d_t *
        (2 : ℝ) ^ ((A_t : ℝ) * interpolationScale N) := by
    calc (((3 * N + 1) * (candidateTupleCount m P + 1) * (poly_L + R_x) : ℕ) : ℝ)
        ≤ (3 * (2 : ℝ) ^ (1 * interpolationScale N)) *
            (((C_pol + C_R0 + 1 : ℕ) : ℝ) * (L + 1 : ℝ) ^ d_t *
              (2 : ℝ) ^ ((A_sys : ℝ) * interpolationScale N)) := by
          rw [Nat.cast_mul]; exact mul_le_mul hcand_r hpolR_r (by positivity) (by positivity)
      _ = ((3 * (C_pol + C_R0 + 1) : ℕ) : ℝ) * (L + 1 : ℝ) ^ d_t *
            ((2 : ℝ) ^ (1 * interpolationScale N) *
              (2 : ℝ) ^ ((A_sys : ℝ) * interpolationScale N)) := by push_cast; ring
      _ = ((3 * (C_pol + C_R0 + 1) : ℕ) : ℝ) * (L + 1 : ℝ) ^ d_t *
            (2 : ℝ) ^ ((A_t : ℝ) * interpolationScale N) := by
          rw [← Real.rpow_add two_pos]; dsimp only [A_t]; push_cast; ring_nf
  have hpol_At := nat_poly_le_subexp hPol hd_pol (Nat.cast_nonneg A_t) hrho_nn
  have h1_At := one_le_mul_of_one_le_of_one_le h1_dt htwo_At
  have hin_cast : (t_in : ℝ) ≤ 2 * ((poly_L : ℝ) + ((2 ^ q_val : ℕ) : ℝ) +
      (((3 * N + 1) * (candidateTupleCount m P + 1) * (poly_L + R_x) : ℕ) : ℝ) + 1) := by
    exact_mod_cast hin_le
  have hC_eq : (C_decl : ℝ) = (C_dg : ℝ) + (C_ex0 : ℝ) +
      2 * ((C_pol : ℝ) + (PowE : ℝ) + ((3 * (C_pol + C_R0 + 1) : ℕ) : ℝ) + 1) := by
    rw [hC_decl]; push_cast; ring
  have h0_ex : (0 : ℝ) ≤
      (C_ex0 : ℝ) * (L + 1 : ℝ) ^ d_t * (2 : ℝ) ^ ((A_t : ℝ) * interpolationScale N) := by
    positivity
  rw [hC_eq]; linarith only [hdg_r, hin_cast, hpol_At, hqinit_r, hprod_r, h1_At, h0_ex]

/-- **Threshold-parametric fast-regime `2 ^ {O_k(interpolationScale N)}` runtime bound
(§5.5, §6.3 eq. (6.4), §6.4 Proposition 6.4)**: above `N_min ≥ 16384`, both leaf certificates run
in `C_t * (|enc x| + 1) ^ d_t * 2 ^ (A_t * interpolationScale x.1.2)` steps on
`x.2.length ≤ leafOccBound k x.1.2 * x.1.2 + 1` (for all `N : ℕ`, including `N = 0`). -/
theorem exists_threshold_branchedSparseCNF_time_bound (k N₀_top N₀_branch : ℕ)
    {branchEval : BranchEvalInput → ℕ}
    (cBranch : NativeCertificate branchEval encBranchEvalInput encNat)
    (hbound : ∀ n' eqs', checkBranchFeasible N₀_branch (n', eqs') = true →
      branchEval (prepareBranchEvalInput (n', eqs')) ≤ 2 ^ n')
    (hs_br : PolyBounded (fun x => (encBranchEvalInput x).length) cBranch.space)
    (hbr_time : BranchPolylogTimeBound N₀_branch cBranch) :
    ∃ N_min : ℕ, 16384 ≤ N_min ∧ ∀ N₀_leaf : ℕ, N_min ≤ N₀_leaf →
      ∃ C_t d_t A_t : ℕ, 1 ≤ A_t ∧
        ∀ x : (Unit × ℕ) × CNF ℕ, x.2.length ≤ leafOccBound k x.1.2 * x.1.2 + 1 →
          ((branchedSparseCNFDeclaredCertificate k N₀_leaf N₀_top N₀_branch
              cBranch hbound).time x : ℝ) ≤
            (C_t : ℝ) * ((encPair (encPair encUnit encUnary) encCNF x).length + 1 : ℝ) ^ d_t *
              (2 : ℝ) ^ ((A_t : ℝ) * interpolationScale x.1.2) ∧
          ((branchedSparseCNFLeafCertificate k N₀_leaf N₀_top N₀_branch
              cBranch hbound).time x : ℝ) ≤
            (C_t : ℝ) * ((encPair (encPair encUnit encUnary) encCNF x).length + 1 : ℝ) ^ d_t *
              (2 : ℝ) ^ ((A_t : ℝ) * interpolationScale x.1.2) := by
  obtain ⟨N_sys, C_sys, d_sys, A_sys, hNsys16, hSysT⟩ :=
    polySys_time_bound_of_branchPolylog k N₀_top N₀_branch cBranch hbound hbr_time
  obtain ⟨C_B, hCB⟩ := exists_leafDensityRatio_le_mul_clog_pow k; set β_B := 2 * (max 2 k - 1)
  obtain ⟨N_q, hNq⟩ := Filter.eventually_atTop.mp
    (SparseCountingScale.eventually_query_overhead_poly_le C_B β_B 20000 2 2 one_pos)
  set N_min := max N_sys N_q
  refine ⟨N_min, hNsys16.trans (le_max_left _ _), fun N₀_leaf hN₀ => ?_⟩
  have hNOf := ComputableInPolyTime.snd encUnit encUnary
  have hBOf := computableInPolyTime_leafDensityRatio k
  obtain ⟨cPoly, hcPoly⟩ :
      ∃ c, c = branchedPolyCertificate k N₀_top N₀_branch cBranch hbound := ⟨_, rfl⟩
  have hcPoly_sp : PolyBounded (fun y => (encPair encUnary encSys y).length) cPoly.space :=
    hcPoly ▸ polyBounded_branchedPolyCertificate_space k N₀_top N₀_branch cBranch hbound hs_br
  obtain ⟨poly, qInit, polySys, hpoly, hqInit, hpolySys, _, hInnerDeclT⟩ :=
    exists_sparseCNFDeclaredCertificate_bounds k (max 1 N₀_leaf) hNOf hBOf cPoly hcPoly_sp
  obtain ⟨cInner, hcInner⟩ :
      ∃ c, c = sparseCNFDeclaredCertificate k (max 1 N₀_leaf) hNOf hBOf cPoly := ⟨_, rfl⟩
  rw [← hcInner] at hInnerDeclT
  obtain ⟨C_nm, d_nm, hLeafT⟩ := exists_branchedSparseCNFLeafCertificate_time_le
    k N₀_leaf N₀_top N₀_branch cBranch hbound hs_br
  obtain ⟨cDecl, hcDecl⟩ :
      ∃ c, c = branchedSparseCNFDeclaredCertificate k N₀_leaf N₀_top N₀_branch cBranch hbound :=
    ⟨_, rfl⟩
  obtain ⟨cLeaf, hcLeaf⟩ :
      ∃ c, c = branchedSparseCNFLeafCertificate k N₀_leaf N₀_top N₀_branch cBranch hbound :=
    ⟨_, rfl⟩
  have hcDecl_time : ∀ x, cDecl.time x =
      (NativeCertificate.ofPolyTime (computableInPolyTime_denseFallbackGuard k)).time x +
        if denseFallbackGuard k x then (countCNFExhaustiveCertificate.comp
          (NativeCertificate.ofPolyTime computableInPolyTime_leafExhProj)).time x
        else cInner.time x := fun x => by
    rw [hcDecl]; unfold branchedSparseCNFDeclaredCertificate guardedTargetOfPolyTime
    rw [guardedTargetCertificate_time _ _ _ _ _ x, ← hcPoly, ← hcInner]
  rw [← hcLeaf, ← hcDecl] at hLeafT ⊢
  obtain ⟨C_pol, d_pol, hPol⟩ := (PolyBounded.of_polynomiallyBounded (·) hpoly).exists_le
  obtain ⟨C_qi, d_qi, hQi⟩ := (PolyBounded.of_polynomiallyBounded (·) hqInit).exists_le
  obtain ⟨C_ps, d_ps, hPs⟩ := (PolyBounded.of_polynomiallyBounded (·) hpolySys).exists_le
  obtain ⟨C_dg, d_dg, hDg⟩ := (NativeCertificate.ofPolyTime_isPolynomial
    (computableInPolyTime_denseFallbackGuard k)).1.exists_le
  obtain ⟨P_ex, Q_ex, hP_ex, hQ_ex, hExhT⟩ := exists_countCNFExhaustive_time_le
  obtain ⟨C_ex0, d_ex0, hEx0⟩ :=
    ((NativeCertificate.ofPolyTime_isPolynomial computableInPolyTime_leafExhProj).1.add
      ((((PolyBounded.const 2).mul hP_ex).add hQ_ex).comp
        computableInPolyTime_leafExhProj.polyBounded_length)).exists_le
  set C_i := C_qi * (C_B + CNF.initialRowWeightCoeff (C_B + 1) β_B) ^ d_qi
  set d_i := (2 * β_B + 3) * d_qi
  obtain ⟨N_init, hNinit⟩ := Filter.eventually_atTop.mp
    (SparseCountingScale.eventually_two_pow_clog_pow_le (C_i : ℝ) d_i one_pos)
  obtain ⟨PowE, hPowE⟩ : ∃ n, n = 2 ^ (C_i * Nat.clog 2 N_init ^ d_i) := ⟨_, rfl⟩
  obtain ⟨C_R0, hC_R0⟩ : ∃ n, n = C_sys * (C_ps + 1) ^ d_sys := ⟨_, rfl⟩
  set d_R0 := d_ps * d_sys
  let R (x : (Unit × ℕ) × CNF ℕ) : ℕ := ⌈((C_R0 : ℕ) : ℝ) * ((encLeafIn x).length + 1 : ℝ) ^ d_R0 *
    (2 : ℝ) ^ ((A_sys : ℝ) * interpolationScale x.1.2)⌉₊
  have hValidR : ValidPolyTimeBound encLeafCtx Prod.snd
      (fun p : Unit × ℕ => leafDensityRatio k p.2) k (max 1 N₀_leaf) cPoly polySys R := by
    intro x hfast sys hsys hlen
    obtain ⟨_, _, _, hge, hmB⟩ := entersSparseFastPath_eq_true_iff.mp hfast
    have ht := hSysT
      (le_trans (le_max_left _ _) (hN₀.trans ((le_max_right 1 N₀_leaf).trans hge))) hmB hsys
    rw [← hcPoly] at ht; set L := (encLeafIn x).length
    have hps_bound : (encPair encUnary encSys (x.1.2, sys)).length + 1 ≤
        (C_ps + 1) * (L + 1) ^ d_ps := by
      have hp1 := Nat.one_le_pow d_ps (L + 1) (Nat.succ_pos L)
      have h1 := hlen.trans (hPs L); nlinarith only [hp1, h1]
    have ht' : (cPoly.time (x.1.2, sys) : ℝ) ≤
        (C_R0 : ℝ) * (L + 1 : ℝ) ^ d_R0 * (2 : ℝ) ^ ((A_sys : ℝ) * interpolationScale x.1.2) :=
      (ht.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (comp_poly_pow_le hps_bound (le_rfl : d_sys ≤ d_sys))
          (Nat.cast_nonneg C_sys)) (by positivity))).trans_eq
        (by rw [hC_R0]; dsimp only [d_R0]; push_cast; ring)
    exact Nat.cast_le.mp (ht'.trans (Nat.le_ceil _))
  set A_t := A_sys + 1; set d_t := max (max d_dg d_ex0) (max d_pol (max d_R0 d_nm))
  obtain ⟨C_decl, hC_decl⟩ :
      ∃ n, n = C_dg + C_ex0 + 2 * (C_pol + PowE + 3 * (C_pol + C_R0 + 1) + 1) := ⟨_, rfl⟩
  set C_t := C_decl + C_nm; refine ⟨C_t, d_t, A_t, Nat.succ_pos _, fun x hlen_x => ?_⟩
  set L := (encLeafIn x).length
  have hrho_nn : 0 ≤ interpolationScale x.1.2 := interpolationScale_nonneg x.1.2
  have hd_dg : d_dg ≤ d_t := (le_max_left _ _).trans (le_max_left _ _)
  have hd_ex0 : d_ex0 ≤ d_t := (le_max_right _ _).trans (le_max_left _ _)
  have hd_pol : d_pol ≤ d_t := (le_max_left _ _).trans (le_max_right _ _)
  have hd_R0 : d_R0 ≤ d_t := (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hd_nm : d_nm ≤ d_t := (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hdg_r := nat_poly_le_subexp (hDg x) hd_dg (Nat.cast_nonneg A_t) hrho_nn
  have hdecl_bound : (cDecl.time x : ℝ) ≤
      (C_decl : ℝ) * (L + 1 : ℝ) ^ d_t * (2 : ℝ) ^ ((A_t : ℝ) * interpolationScale x.1.2) := by
    rw [hcDecl_time x]; cases hd : denseFallbackGuard k x
    · simp only [Bool.false_eq_true, ↓reduceIte, Nat.cast_add]
      have hinner_t := hInnerDeclT R hValidR x
      unfold sparseCNFTimeBound at hinner_t; dsimp only at hinner_t
      cases hfast : entersSparseFastPath k (max 1 N₀_leaf) x.1.2 (leafDensityRatio k x.1.2) x.2
      · simp only [hfast, Bool.false_eq_true, ↓reduceIte] at hinner_t
        have hpol_nat : 2 * (poly L + 1) ≤ (2 * (C_pol + 1)) * (L + 1) ^ d_pol := by
          have hp1 := Nat.one_le_pow d_pol (L + 1) (Nat.succ_pos L)
          have h1 := hPol L; nlinarith only [hp1, h1]
        have hpol_r := nat_poly_le_subexp (hinner_t.trans hpol_nat) hd_pol
          (Nat.cast_nonneg A_t) hrho_nn
        have hle_C : (C_dg : ℝ) + ((2 * (C_pol + 1) : ℕ) : ℝ) ≤ (C_decl : ℝ) := by
          exact_mod_cast (show C_dg + 2 * (C_pol + 1) ≤ C_decl by rw [hC_decl]; omega)
        exact (add_le_add hdg_r hpol_r).trans (by
          rw [← add_mul, ← add_mul]
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hle_C (by positivity))
            (by positivity))
      · simp only [hfast, ↓reduceIte] at hinner_t
        obtain ⟨_, he, _, hge, hmB⟩ := entersSparseFastPath_eq_true_iff.mp hfast
        have hN_min : N_min ≤ x.1.2 := hN₀.trans ((le_max_right 1 N₀_leaf).trans hge)
        have hN2 : 2 ≤ x.1.2 :=
          (by omega : 2 ≤ 16384).trans ((hNsys16.trans (le_max_left _ _)).trans hN_min)
        have hm1 : 1 ≤ x.2.length := by
          rcases eq : x.2 with _ | ⟨_, _⟩
          · rw [eq] at he; cases he
          · exact Nat.succ_pos _
        exact fast_path_arith_bound rfl rfl hPowE hNinit
          (hNq x.1.2 ((le_max_right _ _).trans hN_min)) hN2 hm1 hmB (hCB x.1.2 hN2)
          (hQi _) (hPol L) hd_pol hd_R0 hdg_r hinner_t hC_decl
    · simp only [↓reduceIte, Nat.cast_add]
      have hgt_dense : leafDensityRatio k x.1.2 * x.1.2 < x.2.length := by
        simp only [denseFallbackGuard, Bool.and_eq_true, decide_eq_true_eq] at hd; exact hd.2
      have hN0 : x.1.2 = 0 := by
        rcases Nat.eq_zero_or_pos x.1.2 with h0 | hpos
        · exact h0
        · exact False.elim ((leafOccBound_mul_succ_le_leafDensityRatio_mul hpos).not_gt
            (lt_of_lt_of_le hgt_dense hlen_x))
      have hex_nat : (countCNFExhaustiveCertificate.comp
          (NativeCertificate.ofPolyTime computableInPolyTime_leafExhProj)).time x ≤
            C_ex0 * (L + 1) ^ d_ex0 := by
        rw [NativeCertificate.comp_time]; have hex := hExhT (x.1.2, x.2)
        have hpow0 : 2 ^ x.1.2 + 1 = 2 := by rw [hN0]; rfl
        dsimp only [computableInPolyTime_leafExhProj] at *; rw [hpow0] at hex
        exact (Nat.add_le_add_left hex _).trans (hEx0 x)
      have hex_r := nat_poly_le_subexp hex_nat hd_ex0 (Nat.cast_nonneg A_t) hrho_nn
      have hle_C : (C_dg : ℝ) + (C_ex0 : ℝ) ≤ (C_decl : ℝ) := by
        exact_mod_cast (show C_dg + C_ex0 ≤ C_decl by rw [hC_decl]; omega)
      exact (add_le_add hdg_r hex_r).trans (by
        rw [← add_mul, ← add_mul]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hle_C (by positivity))
          (by positivity))
  refine ⟨hdecl_bound.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Nat.le_add_right _ _)) (by positivity))
    (by positivity)), ?_⟩
  have hnt_r : (cLeaf.time x : ℝ) ≤
      (cDecl.time x : ℝ) + ((C_nm * (L + 1) ^ d_nm : ℕ) : ℝ) := by exact_mod_cast hLeafT x
  have hnm_r := nat_poly_le_subexp (le_rfl : C_nm * (L + 1) ^ d_nm ≤ C_nm * (L + 1) ^ d_nm)
    hd_nm (Nat.cast_nonneg A_t) hrho_nn
  rw [show (C_t : ℝ) = (C_decl : ℝ) + (C_nm : ℝ) from Nat.cast_add _ _, add_mul, add_mul]
  exact hnt_r.trans (add_le_add hdecl_bound hnm_r)

/-- **Existential fast-regime `2 ^ {O_k(interpolationScale N)}` runtime bound
(§5.5, §6.3 eq. (6.4), §6.4 Proposition 6.4)**:
under `BranchPolylogTimeBound N₀_branch cBranch` and polynomial branch workspace `hs_br`, there
exist `N₀_leaf N₀_top C_t d_t A_t : ℕ` (`1 ≤ A_t`) bounding both leaf certificates across all
`x = ((c, N), ψ)` satisfying `ψ.length ≤ leafOccBound k N * N + 1` (including `N = 0`). -/
theorem exists_branchedSparseCNF_time_bound (k N₀_branch : ℕ)
    {branchEval : BranchEvalInput → ℕ}
    (cBranch : NativeCertificate branchEval encBranchEvalInput encNat)
    (hbound : ∀ n' eqs', checkBranchFeasible N₀_branch (n', eqs') = true →
      branchEval (prepareBranchEvalInput (n', eqs')) ≤ 2 ^ n')
    (hs_br : PolyBounded (fun x => (encBranchEvalInput x).length) cBranch.space)
    (hbr_time : BranchPolylogTimeBound N₀_branch cBranch) :
    ∃ N₀_leaf N₀_top C_t d_t A_t : ℕ, 1 ≤ A_t ∧
      ∀ x : (Unit × ℕ) × CNF ℕ, x.2.length ≤ leafOccBound k x.1.2 * x.1.2 + 1 →
        ((branchedSparseCNFDeclaredCertificate k N₀_leaf N₀_top N₀_branch
            cBranch hbound).time x : ℝ) ≤
          (C_t : ℝ) * ((encPair (encPair encUnit encUnary) encCNF x).length + 1 : ℝ) ^ d_t *
            (2 : ℝ) ^ ((A_t : ℝ) * interpolationScale x.1.2) ∧
        ((branchedSparseCNFLeafCertificate k N₀_leaf N₀_top N₀_branch
            cBranch hbound).time x : ℝ) ≤
          (C_t : ℝ) * ((encPair (encPair encUnit encUnary) encCNF x).length + 1 : ℝ) ^ d_t *
            (2 : ℝ) ^ ((A_t : ℝ) * interpolationScale x.1.2) := by
  obtain ⟨N_min, _, hBound⟩ :=
    exists_threshold_branchedSparseCNF_time_bound k 0 N₀_branch cBranch hbound hs_br hbr_time
  obtain ⟨C_t, d_t, A_t, hA, hT⟩ := hBound N_min le_rfl
  exact ⟨N_min, 0, C_t, d_t, A_t, hA, hT⟩

end
end Cslib.Complexity.BranchedSparseCNFCounter
