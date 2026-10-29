/-
Copyright (c) 2026 Anton Kovsharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anton Kovsharov
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.Complexity.FineGrained.SparseBranchSchedule
public import Complexity.Computability.GenericRAM.Native.ExhaustiveCountFallback
public import Complexity.Computability.GenericRAM.Native.HeavyBranchFold
public import Complexity.Computability.PolyTime.CNF.GreedyParityContext
public import Complexity.Computability.PolyTime.CNF.SparsePolyCompile
public import Complexity.Computability.PolyTime.FineGrained.ParameterCheck
public import Complexity.Foundations.BooleanAnalysis.SparseReplacementDesign
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Fold
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Log
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Mathlib.Data.List.GetD
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Heavy-branched sparse `𝔽₂` polynomial-system zero counter (§5.5, Theorem 2.2)

Uniform native heavy-branched sparse `𝔽₂` common-zero counter of §5.5 (*Proof of Theorem 2.2*,
pp. 38–39) and §6.3 parity-system wrapper (p. 43) of [OpenAI, *The Exponential Time Hypothesis is
False*][OpenAI2026ETH], parameterized over a Proposition 5.3 branch evaluator (`branchEval`).

* **Encoded algorithms vs. specifications**: the checkers, metrics, schedule builders, and counters
  (`prepareBranchEvalInput`, `mkPaperSparseInput`, `toBranchInput`, `compileContextParityInput`,
  `guardedBranchSolver`, `countSparsePolySystem`, `countContextParity`) run on `encBranchEvalInput`,
  `encSparseSystemInput`, and `encPair encC (encList encBits)` with `ComputableInPolyTime` and
  `NativeCertificate` bounds (`guardedBranchCertificate`, `guardedBranchingCertificate`,
  `sparsePolyCounterCertificate`, `contextParityCertificate`), whereas `branchNeutralScope` and
  `maxReducedCost` are unencoded mathematical specification definitions.
* **Out-of-range and fallback conventions**: `scopeWidthOn n eq` ignores variables `≥ n`; both
  `checkTopFeasible = false` and `checkBranchFeasible = false` fall back to
  `ExhaustiveCountFallback.countSystemExhaustive`, evaluating indices `≥ n` (resp. `≥ n'`) as
  `false` and matching `HeavyBranchFold.rootCount` unconditionally on all inputs.

## Main definitions

* `checkVarsLt`, `checkCanonicalMonomial`, `checkCanonicalEquation`, `checkCanonicalSystem`,
  `scopeWidthOn`, `sysMaxDegree`, `branchMaxFactorIncidence`, `branchMaxFactorWidth`,
  `branchAugmentedIncidence`: canonicality checkers and neutral-augmented scope metrics.
* `BranchEvalInput`, `encBranchEvalInput`, `prepareBranchEvalInput`, `checkBranchFeasible`,
  `guardedBranchSolver`, `guardedBranchCertificate`: Proposition 5.3 branch bundle, exact guard,
  fallback-guarded branch solver, and `NativeCertificate`.
* `SparseSystemInput`, `encSparseSystemInput`, `mkPaperSparseInput`, `checkTopFeasible`,
  `toBranchInput`, `guardedBranchingCertificate`, `countSparsePolySystem`,
  `sparsePolyCounterCertificate`: top-level §5.5 heavy-branched counter and native certificates.
* `compileContextParityInput`, `countContextParity`, `contextParityCertificate`: §6.3
  context-carrying CNF parity-system counter and `NativeCertificate` for `GreedyContext`.
* `branchNeutralScope`, `maxReducedCost`: unencoded neutral-scope and reduced-branch cost specs.

## Main results

* `sum_card_branchNeutralScope`, `varIncidence_branchNeutralScope_le`, `card_branchNeutralScope_le`,
  `branchAugmentedIncidence_le_mul`, `feasible_of_checkBranchFeasible`,
  `exists_replacementDesign_of_checkBranchFeasible`,
  `emod_ediv_design_eq_rootCount_of_checkBranchFeasible`,
  `exists_threshold_checkBranchFeasible_eq_true`: neutral-scope bounds, `ReplacementDesign` bridge,
  cleared parity-quotient exactness, and eventual feasibility.
* `computableInPolyTime_prepareBranchEvalInput`, `computableInPolyTime_checkBranchFeasible`,
  `computableInPolyTime_checkTopFeasible`, `computableInPolyTime_toBranchInput`,
  `computableInPolyTime_mkPaperSparseInput`, `computableInPolyTime_compileContextParityInput`:
  `ComputableInPolyTime` certificates for schedule builders and guards.
* `countSystemExhaustive_eq_rootCount`, `guardedBranchSolver_eq_rootCount`,
  `countSparsePolySystem_eq_rootCount`, `countSparsePolySystem_eq_commonZeroCount`,
  `checkTopFeasible_mkPaperSparseInput_of_le`, `reduced_branch_invariants`,
  `clog_pow_le_clog_pow_two_mul`, `countContextParity_eq_numPassing`: unconditional exactness,
  `commonZeroCount` / `numPassing` bridges, and heavy-branching invariants.
* `polyBounded_guardedBranchCertificate_space`, `exists_guardedBranchCertificate_time_le`,
  `polyBounded_sparsePolyCounterCertificate_space`,
  `sparsePolyCounterCertificate_time_le_of_feasible`, `exists_real_exp_bound_countSparsePolySystem`,
  `polyBounded_contextParityCertificate_space`: polynomial workspace and fallback-absorbed time.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], §5.5 (pp. 38–39) & §6.3.
-/

namespace Cslib.Complexity.SubexponentialSAT.SparsePolyCounter

open Finset Cslib Cslib.BitString Cslib.Complexity Cslib.GenericRAM Cslib.LinearAlgebra
open Turing.MultiTapeTM

local notation "encEq" => encList (encList encNat)
local notation "encSys" => encList (encList (encList encNat))

@[expose] public section

/-! ### 1. Computable Checkers, Branch Preparation, and Heavy-Branched Counters -/

/-- Check that every variable occurring in `sys` satisfies `v < n`. -/
def checkVarsLt (n : ℕ) (sys : List (List (List ℕ))) : Bool :=
  sys.all fun eq => eq.all fun m => m.all fun v => decide (v < n)

/-- Check that a monomial `m : List ℕ` is strictly increasing (`IsCanonicalMonomial m`). -/
def checkCanonicalMonomial (m : List ℕ) : Bool :=
  (List.range m.length).all fun i => (List.range i).all fun j => decide (m.getD j 0 < m.getD i 0)

/-- Check that `eq` has duplicate-free strictly increasing monomials (`IsCanonicalEquation eq`). -/
def checkCanonicalEquation (eq : List (List ℕ)) : Bool :=
  ((List.range eq.length).all fun i => (List.range i).all fun j =>
    !decide (eq.getD j [] = eq.getD i [])) && eq.all checkCanonicalMonomial

/-- Check that every equation in `sys` satisfies `IsCanonicalEquation`. -/
def checkCanonicalSystem (sys : List (List (List ℕ))) : Bool := sys.all checkCanonicalEquation

/-- Number of variables `< n` occurring in at least one monomial of `eq`. -/
def scopeWidthOn (n : ℕ) (eq : List (List ℕ)) : ℕ :=
  (List.range n).countP fun v => eq.any fun m => decide (v ∈ m)

/-- Maximum monomial degree (`List.length`) across all equations in `sys` (`0` if empty). -/
def sysMaxDegree (sys : List (List (List ℕ))) : ℕ := (sys.flatten.map List.length).foldl max 0

/-- Maximum neutral-augmented factor incidence `b = max_{v < n'} (varDegree v eqs') + 1` (§5.5). -/
def branchMaxFactorIncidence (n' : ℕ) (eqs' : List (List (List ℕ))) : ℕ :=
  ((List.range n').map fun v => varDegree v eqs').foldl max 0 + 1

/-- Maximum neutral-augmented factor scope width `w = max (max_{eq ∈ eqs'} |I'_{eq}|) 1` (§5.5). -/
def branchMaxFactorWidth (n' : ℕ) (eqs' : List (List (List ℕ))) : ℕ :=
  (eqs'.map (scopeWidthOn n')).foldl max 1

/-- Total neutral-augmented factor–variable incidence `M' = ∑_{eq ∈ eqs'} |I'_{eq}| + n'` (§5.5). -/
def branchAugmentedIncidence (n' : ℕ) (eqs' : List (List (List ℕ))) : ℕ :=
  (eqs'.map (scopeWidthOn n')).sum + n'

/-- Input bundle `((n', k'), (b, w, M', β), (r, Q, R, A₀), eqs')` for Proposition 5.3 (§5.4–5.5). -/
abbrev BranchEvalInput := (ℕ × ℕ) × (ℕ × ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ × ℕ) × List (List (List ℕ))

/-- Native encoding of `BranchEvalInput` (`(n', k')` unary, parameter quadruples binary). -/
def encBranchEvalInput : BranchEvalInput ↪ List Bool :=
  let encQuad := encPair encNat (encPair encNat (encPair encNat encNat))
  encPair (encPair encUnary encUnary) (encPair encQuad (encPair encQuad encSys))

/-- Assemble the Proposition 5.3 branch input from a reduced system `(n', eqs')` (§5.5). -/
def prepareBranchEvalInput (p : ℕ × List (List (List ℕ))) : BranchEvalInput :=
  let n' := p.1; let eqs' := p.2; let k' := sysMaxDegree eqs'
  let b := branchMaxFactorIncidence n' eqs'; let w := branchMaxFactorWidth n' eqs'
  let M' := branchAugmentedIncidence n' eqs'; let β := ParameterCheck.chooseBeta (Nat.clog 2 n') b w
  let sched := ParameterCheck.computeScheduleParams β n'
  ((n', k'), (b, w, M', β), (sched.2.2.1, sched.2.2.2.1, sched.2.2.2.2.1, sched.2.2.2.2.2), eqs')

/-- Per-branch exact feasibility guard (§5.5): `N₀_branch ≤ n'`, canonical `< n'`, schedule ok. -/
def checkBranchFeasible (N₀_branch : ℕ) (p : ℕ × List (List (List ℕ))) : Bool :=
  let n' := p.1; let eqs' := p.2
  let b := branchMaxFactorIncidence n' eqs'; let w := branchMaxFactorWidth n' eqs'
  let M' := branchAugmentedIncidence n' eqs'; let β := ParameterCheck.chooseBeta (Nat.clog 2 n') b w
  decide (N₀_branch ≤ n') && checkVarsLt n' eqs' && checkCanonicalSystem eqs' &&
    ParameterCheck.checkScheduleFeasible n' M' b w β

/-- Guarded per-branch solver (§5.5): runs `branchEval` when feasible, else exhaustive fallback. -/
def guardedBranchSolver (N₀_branch : ℕ) (branchEval : BranchEvalInput → ℕ)
    (n' : ℕ) (eqs' : List (List (List ℕ))) : ℕ :=
  if checkBranchFeasible N₀_branch (n', eqs') then branchEval (prepareBranchEvalInput (n', eqs'))
  else ExhaustiveCountFallback.countSystemExhaustive (n', eqs')

/-- Top-level input `(n, (k_deg, s_div, b₀), eqs)` to the heavy-branched sparse `𝔽₂` counter. -/
abbrev SparseSystemInput : Type := ℕ × (ℕ × ℕ × ℕ) × List (List (List ℕ))

/-- Native encoding of `SparseSystemInput` (`n` and `k_deg` unary, `s_div` and `b₀` binary). -/
def encSparseSystemInput : SparseSystemInput ↪ List Bool :=
  encPair encUnary (encPair (encPair encUnary (encPair encNat encNat)) encSys)

/-- Construct the canonical §5.5 `SparseSystemInput` `(n, (k_deg, s_div, b₀), eqs)` (p. 38). -/
def mkPaperSparseInput (n k_deg : ℕ) (eqs : List (List (List ℕ))) : SparseSystemInput :=
  (n, (k_deg, max 1 (ParameterCheck.heavyIncidenceCutoff 1 n),
    max 1 (ParameterCheck.heavyIncidenceCutoff (branchAugmentedIncidence n eqs) n)), eqs)

/-- Top-level §5.5 feasibility guard: `N₀_top ≤ n`, `1 ≤ s_div`, canonical `< n`, `|S| ≤ n/s`. -/
def checkTopFeasible (N₀_top : ℕ) (inp : SparseSystemInput) : Bool :=
  let n := inp.1; let k_deg := inp.2.1.1; let s_div := inp.2.1.2.1
  let b₀ := inp.2.1.2.2; let eqs := inp.2.2
  decide (N₀_top ≤ n) && decide (1 ≤ s_div) && checkVarsLt n eqs && checkCanonicalSystem eqs &&
    decide (sysMaxDegree eqs ≤ k_deg) &&
    decide ((HeavyBranchFold.heavyVarList n b₀ eqs).length ≤ n / s_div)

/-- Assemble `HeavyBranchFold.BranchInput` `(n, heavyVarList n b₀ eqs, eqs)` from `inp`. -/
def toBranchInput (inp : SparseSystemInput) : HeavyBranchFold.BranchInput :=
  (inp.1, HeavyBranchFold.heavyVarList inp.1 inp.2.1.2.2 inp.2.2, inp.2.2)

/-- **Uniform heavy-branched sparse `𝔽₂` polynomial-system zero counter (§5.5, Theorem 2.2)**. -/
def countSparsePolySystem (N₀_top N₀_branch : ℕ) (branchEval : BranchEvalInput → ℕ)
    (inp : SparseSystemInput) : ℕ :=
  if checkTopFeasible N₀_top inp then
    HeavyBranchFold.countByBranching (guardedBranchSolver N₀_branch branchEval) (toBranchInput inp)
  else ExhaustiveCountFallback.countSystemExhaustive (inp.1, inp.2.2)

/-- Compile `(ctx, rows)` into `SparseSystemInput` via `compileParitySystemBounded k_deg` (§6.3). -/
def compileContextParityInput {C : Type} (k_deg : ℕ) (nOf sDivOf b₀Of : C → ℕ)
    (φOf : C → Logic.PL.CNF ℕ) (p : C × List (List Bool)) : SparseSystemInput :=
  (nOf p.1, (k_deg, sDivOf p.1, b₀Of p.1), compileParitySystemBounded k_deg (φOf p.1) p.2)

/-- Context-carrying parity-system counter `(ctx, rows) ↦ ℕ` matching `GreedyContext` (§6.3). -/
def countContextParity {C : Type} (N₀_top N₀_branch k_deg : ℕ) (nOf sDivOf b₀Of : C → ℕ)
    (φOf : C → Logic.PL.CNF ℕ) (branchEval : BranchEvalInput → ℕ) (p : C × List (List Bool)) : ℕ :=
  countSparsePolySystem N₀_top N₀_branch branchEval
    (compileContextParityInput k_deg nOf sDivOf b₀Of φOf p)

end

public section

/-! ### 2. Branch Scope Invariants and `ReplacementDesign` Bridge -/

/-- Neutral-augmented scope family on `Fin eqs'.length ⊕ Fin n'` associated to `(n', eqs')`. -/
def branchNeutralScope (n' : ℕ) (eqs' : List (List (List ℕ))) :
    Fin eqs'.length ⊕ Fin n' → Finset (Fin n') :=
  withNeutralScope fun i => equationScope (HeavyBranchFold.toFinsetEquation n' eqs'[i])

private theorem foldl_max_le_iff {l : List ℕ} {init B : ℕ} :
    l.foldl max init ≤ B ↔ init ≤ B ∧ ∀ x ∈ l, x ≤ B := by
  induction l generalizing init with
  | nil => simp only [List.foldl_nil, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  | cons a as ih =>
    simp only [List.foldl_cons, ih, Nat.max_le, List.mem_cons, forall_eq_or_imp, and_assoc]

private theorem le_foldl_max_init (init : ℕ) (l : List ℕ) : init ≤ l.foldl max init :=
  (foldl_max_le_iff.mp le_rfl).1

private theorem le_foldl_max_of_mem {init : ℕ} {l : List ℕ} {x : ℕ} (hx : x ∈ l) :
    x ≤ l.foldl max init := (foldl_max_le_iff.mp le_rfl).2 x hx

theorem checkVarsLt_eq_true_iff {n : ℕ} {sys : List (List (List ℕ))} :
    checkVarsLt n sys = true ↔ ∀ eq ∈ sys, ∀ m ∈ eq, ∀ v ∈ m, v < n := by
  simp only [checkVarsLt, List.all_eq_true, decide_eq_true_eq]

theorem checkCanonicalMonomial_eq_true_iff {m : List ℕ} :
    checkCanonicalMonomial m = true ↔ IsCanonicalMonomial m := by
  unfold checkCanonicalMonomial IsCanonicalMonomial; rw [List.pairwise_iff_getElem]
  simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq]
  refine ⟨fun h j i hj hi hji => ?_, fun h i hi j hji => ?_⟩
  · simpa only [List.getD_eq_getElem m 0 hj, List.getD_eq_getElem m 0 hi] using h i hi j hji
  · rw [List.getD_eq_getElem m 0 (lt_trans hji hi), List.getD_eq_getElem m 0 hi]
    exact h j i (lt_trans hji hi) hi hji

theorem checkCanonicalEquation_eq_true_iff {eq : List (List ℕ)} :
    checkCanonicalEquation eq = true ↔ IsCanonicalEquation eq := by
  unfold checkCanonicalEquation IsCanonicalEquation; rw [List.Nodup, List.pairwise_iff_getElem]
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.not_eq_true',
    decide_eq_false_iff_not, checkCanonicalMonomial_eq_true_iff]
  refine and_congr_left fun _ => ⟨fun h j i hj hi hji => ?_, fun h i hi j hji => ?_⟩
  · simpa only [List.getD_eq_getElem eq [] hj, List.getD_eq_getElem eq [] hi] using h i hi j hji
  · rw [List.getD_eq_getElem eq [] (lt_trans hji hi), List.getD_eq_getElem eq [] hi]
    exact h j i (lt_trans hji hi) hi hji

theorem checkCanonicalSystem_eq_true_iff {sys : List (List (List ℕ))} :
    checkCanonicalSystem sys = true ↔ ∀ eq ∈ sys, IsCanonicalEquation eq := by
  simp only [checkCanonicalSystem, List.all_eq_true, checkCanonicalEquation_eq_true_iff]

/-- Unconditional agreement between `countSystemExhaustive` and `HeavyBranchFold.rootCount`. -/
theorem countSystemExhaustive_eq_rootCount (n : ℕ) (sys : List (List (List ℕ))) :
    ExhaustiveCountFallback.countSystemExhaustive (n, sys) = HeavyBranchFold.rootCount n sys := by
  rw [ExhaustiveCountFallback.countSystemExhaustive_eq_card_filter, HeavyBranchFold.rootCount]
  congr 1; ext σ; simp only [mem_filter, mem_univ, true_and]
  have hfun : (fun v => (List.ofFn σ).getD v false) = HeavyBranchFold.extendAssignment σ := by
    funext v; by_cases hv : v < n
    · rw [List.getD_eq_getElem _ _ (by simp only [List.length_ofFn]; exact hv),
        List.getElem_ofFn, HeavyBranchFold.extendAssignment, dite_eq_left hv]
    · rw [List.getD_eq_default _ _ (by simp only [List.length_ofFn]; omega),
        HeavyBranchFold.extendAssignment, dite_eq_right hv]
  rw [hfun]

theorem scopeWidthOn_eq_length_equationVars {n : ℕ} {eq : List (List ℕ)}
    (hvars : ∀ m ∈ eq, ∀ v ∈ m, v < n) : scopeWidthOn n eq = (equationVars eq).length := by
  rw [scopeWidthOn, List.countP_eq_length_filter,
    ← List.toFinset_card_of_nodup (List.nodup_range.filter _),
    equationVars, ← List.toFinset_card_of_nodup (nodup_sortDedup _), toFinset_sortDedup]
  congr 1; ext v
  simp only [List.mem_toFinset, List.mem_filter, List.mem_range, List.any_eq_true,
    decide_eq_true_eq, List.mem_flatten]
  exact ⟨fun ⟨_, m, hm, hvm⟩ => ⟨m, hm, hvm⟩, fun ⟨m, hm, hvm⟩ => ⟨hvars m hm v hvm, m, hm, hvm⟩⟩

private theorem mem_equationScope_toFinsetEquation {n : ℕ} {eq : List (List ℕ)} {v : Fin n} :
    v ∈ equationScope (HeavyBranchFold.toFinsetEquation n eq) ↔
      (eq.any fun m => decide ((v : ℕ) ∈ m)) = true := by
  simp only [equationScope, HeavyBranchFold.toFinsetEquation, mem_biUnion, List.mem_toFinset,
    List.mem_map, List.any_eq_true, decide_eq_true_eq]
  exact ⟨fun ⟨_, ⟨m, hm, rfl⟩, hvm⟩ => ⟨m, hm, (mem_filter.mp hvm).2⟩,
    fun ⟨m, hm, hvm⟩ => ⟨univ.filter fun i : Fin n => (i : ℕ) ∈ m, ⟨m, hm, rfl⟩,
      mem_filter.mpr ⟨mem_univ _, hvm⟩⟩⟩

theorem card_equationScope_toFinsetEquation (n : ℕ) (eq : List (List ℕ)) :
    #(equationScope (HeavyBranchFold.toFinsetEquation n eq)) = scopeWidthOn n eq := by
  have heq_set : (equationScope (HeavyBranchFold.toFinsetEquation n eq)).map
      ⟨Fin.val, Fin.val_injective⟩ =
      ((List.range n).filter fun u => eq.any fun m => decide (u ∈ m)).toFinset := by
    ext u; simp only [mem_map, Function.Embedding.coeFn_mk, mem_equationScope_toFinsetEquation,
      List.mem_toFinset, List.mem_filter, List.mem_range]
    exact ⟨fun ⟨v, hv, hvu⟩ => hvu ▸ ⟨v.isLt, hv⟩, fun ⟨hu, hp⟩ => ⟨⟨u, hu⟩, hp, rfl⟩⟩
  rw [← card_map ⟨Fin.val, Fin.val_injective⟩, heq_set,
    List.toFinset_card_of_nodup (List.nodup_range.filter _), ← List.countP_eq_length_filter,
    scopeWidthOn]

theorem length_mem_le_sysMaxDegree {sys : List (List (List ℕ))} {eq : List (List ℕ)}
    (heq : eq ∈ sys) {m : List ℕ} (hm : m ∈ eq) : m.length ≤ sysMaxDegree sys :=
  le_foldl_max_of_mem (List.mem_map_of_mem (List.mem_flatten.mpr ⟨eq, heq, hm⟩))

theorem sysMaxDegree_le_iff {sys : List (List (List ℕ))} {k : ℕ} :
    sysMaxDegree sys ≤ k ↔ ∀ eq ∈ sys, ∀ m ∈ eq, m.length ≤ k := by
  simp only [sysMaxDegree, foldl_max_le_iff, Nat.zero_le, true_and, List.mem_map, List.mem_flatten]
  exact ⟨fun h eq heq m hm => h m.length ⟨m, ⟨eq, heq, hm⟩, rfl⟩,
    fun h _ ⟨m, ⟨eq, heq, hm⟩, hm_eq⟩ => hm_eq ▸ h eq heq m hm⟩

theorem one_le_branchMaxFactorIncidence (n' : ℕ) (eqs' : List (List (List ℕ))) :
    1 ≤ branchMaxFactorIncidence n' eqs' := Nat.succ_pos _

theorem one_le_branchMaxFactorWidth (n' : ℕ) (eqs' : List (List (List ℕ))) :
    1 ≤ branchMaxFactorWidth n' eqs' := le_foldl_max_init 1 _

theorem le_branchAugmentedIncidence (n' : ℕ) (eqs' : List (List (List ℕ))) :
    n' ≤ branchAugmentedIncidence n' eqs' := Nat.le_add_left _ _

private theorem varIncidence_toFinsetEquation_eq_varDegree (n' : ℕ) (eqs' : List (List (List ℕ)))
    (v : Fin n') :
    varIncidence (univ : Finset (Fin eqs'.length))
      (fun i : Fin eqs'.length => equationScope (HeavyBranchFold.toFinsetEquation n' eqs'[i])) v =
      varDegree (v : ℕ) eqs' := by
  have hfil : ({i ∈ (List.finRange eqs'.length).toFinset |
      v ∈ equationScope (HeavyBranchFold.toFinsetEquation n' eqs'[i])} :
        Finset (Fin eqs'.length)) =
      ((List.finRange eqs'.length).filter fun i =>
        decide ((v : ℕ) ∈ equationVars eqs'[i])).toFinset := by
    ext i; simp only [mem_filter, List.mem_toFinset, List.mem_filter,
      mem_equationScope_toFinsetEquation, List.any_eq_true, decide_eq_true_eq, mem_equationVars]
  rw [varIncidence, ← List.toFinset_finRange, hfil,
    List.toFinset_card_of_nodup ((List.nodup_finRange _).filter _),
    ← List.countP_eq_length_filter, varDegree]
  conv_rhs => rw [← (List.ofFn_eq_map.symm.trans (List.ofFn_getElem (xs := eqs'))), List.countP_map]
  exact List.countP_congr fun i _ => by simp only [Function.comp_apply, Fin.getElem_fin]

theorem sum_card_branchNeutralScope (n' : ℕ) (eqs' : List (List (List ℕ))) :
    (∑ f : Fin eqs'.length ⊕ Fin n', #(branchNeutralScope n' eqs' f)) =
      branchAugmentedIncidence n' eqs' := by
  change totalIncidence (univ : Finset (Fin eqs'.length ⊕ Fin n')) (branchNeutralScope n' eqs') = _
  rw [← withNeutralFactors_univ, branchNeutralScope, totalIncidence_withNeutralFactors,
    Fintype.card_fin, branchAugmentedIncidence]; congr 1
  rw [totalIncidence, ← List.toFinset_finRange, List.sum_toFinset _ (List.nodup_finRange _)]
  conv_rhs => rw [← (List.ofFn_eq_map.symm.trans (List.ofFn_getElem (xs := eqs'))), List.map_map]
  exact congrArg List.sum (List.map_congr_left fun i _ => by
    simp only [Function.comp_apply, Fin.getElem_fin, card_equationScope_toFinsetEquation])

theorem varIncidence_branchNeutralScope_le (n' : ℕ) (eqs' : List (List (List ℕ))) (v : Fin n') :
    #{f : Fin eqs'.length ⊕ Fin n' | v ∈ branchNeutralScope n' eqs' f} ≤
      branchMaxFactorIncidence n' eqs' := by
  change varIncidence (univ : Finset (Fin eqs'.length ⊕ Fin n'))
      (branchNeutralScope n' eqs') v ≤ _
  rw [← withNeutralFactors_univ, branchNeutralScope, varIncidence_withNeutralFactors,
    varIncidence_toFinsetEquation_eq_varDegree, branchMaxFactorIncidence]
  exact Nat.succ_le_succ (le_foldl_max_of_mem (List.mem_map_of_mem (List.mem_range.mpr v.isLt)))

theorem card_branchNeutralScope_le (n' : ℕ) (eqs' : List (List (List ℕ)))
    (f : Fin eqs'.length ⊕ Fin n') :
    #(branchNeutralScope n' eqs' f) ≤ branchMaxFactorWidth n' eqs' :=
  card_withNeutralScope_le (one_le_branchMaxFactorWidth n' eqs')
    (fun i : Fin eqs'.length => (card_equationScope_toFinsetEquation n' eqs'[i]).trans_le
      (le_foldl_max_of_mem (List.mem_map_of_mem (List.getElem_mem i.isLt)))) f

theorem branchAugmentedIncidence_le_mul (n' : ℕ) (eqs' : List (List (List ℕ))) :
    branchAugmentedIncidence n' eqs' ≤ branchMaxFactorIncidence n' eqs' * n' := by
  have hle := totalIncidence_withNeutralFactors_le (I := (univ : Finset (Fin eqs'.length)))
    (scope := fun i => equationScope (HeavyBranchFold.toFinsetEquation n' eqs'[i]))
    (b₀ := ((List.range n').map fun v => varDegree v eqs').foldl max 0)
    (fun v => (varIncidence_toFinsetEquation_eq_varDegree n' eqs' v).trans_le
      (le_foldl_max_of_mem (List.mem_map_of_mem (List.mem_range.mpr v.isLt))))
  rw [withNeutralFactors_univ, ← branchNeutralScope, Fintype.card_fin,
    ← branchMaxFactorIncidence, totalIncidence] at hle
  rwa [← sum_card_branchNeutralScope]

/-- Soundness of `checkBranchFeasible`: passing certifies `N₀_branch ≤ n'`, canonical `< n'`
equations, and `ReplacementParams.Feasible` at `prepareBranchEvalInput`. -/
theorem feasible_of_checkBranchFeasible {N₀_branch n' : ℕ} {eqs' : List (List (List ℕ))}
    (h : checkBranchFeasible N₀_branch (n', eqs') = true) :
    let out := prepareBranchEvalInput (n', eqs')
    N₀_branch ≤ n' ∧ (∀ eq ∈ eqs', IsCanonicalEquation eq) ∧
      (∀ eq ∈ eqs', ∀ m ∈ eq, ∀ v ∈ m, v < n') ∧
      ReplacementParams.Feasible out.2.1.2.2.2 n' out.2.1.1 out.2.1.2.1 out.2.1.2.2.1 := by
  unfold checkBranchFeasible at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, checkVarsLt_eq_true_iff,
    checkCanonicalSystem_eq_true_iff] at h
  exact ⟨h.1.1.1, h.1.2, h.1.1.2,
    ParameterCheck.feasible_of_checkScheduleFeasible_chooseBeta_eq_true h.2⟩

/-- Passing `checkBranchFeasible` yields a Section 4 `ReplacementDesign` on `branchNeutralScope`. -/
theorem exists_replacementDesign_of_checkBranchFeasible {N₀_branch n' : ℕ}
    {eqs' : List (List (List ℕ))} (h : checkBranchFeasible N₀_branch (n', eqs') = true) :
    let out := prepareBranchEvalInput (n', eqs'); let s := out.2.2.1
    Nonempty (ReplacementDesign (branchNeutralScope n' eqs') s.2.1 s.1 s.2.2.2 s.2.2.1
      (ReplacementParams.tauRat n')) := by
  obtain ⟨_, _, _, hF⟩ := feasible_of_checkBranchFeasible h
  have hF' : ReplacementParams.Feasible (prepareBranchEvalInput (n', eqs')).2.1.2.2.2 n'
      (branchMaxFactorIncidence n' eqs') (branchMaxFactorWidth n' eqs')
      (∑ f : Fin eqs'.length ⊕ Fin n', #(branchNeutralScope n' eqs' f)) := by
    rwa [sum_card_branchNeutralScope]
  exact ReplacementParams.Feasible.exists_replacementDesign (branchNeutralScope n' eqs') hF'
    (one_le_branchMaxFactorIncidence n' eqs') (one_le_branchMaxFactorWidth n' eqs')
    (varIncidence_branchNeutralScope_le n' eqs') (card_branchNeutralScope_le n' eqs')
    (by rw [sum_card_branchNeutralScope]; exact branchAugmentedIncidence_le_mul n' eqs')

/-- **Proposition 5.3 / §5.4–5.5 semantic bridge**: when `checkBranchFeasible` holds, `n' < ℓ`,
and `D` is any `ReplacementDesign` at `prepareBranchEvalInput (n', eqs')`, the cleared integer
truncated parity quotient modulo `2 ^ ℓ` equals `rootCount n' eqs'`. -/
theorem emod_ediv_design_eq_rootCount_of_checkBranchFeasible {N₀_branch n' ℓ : ℕ}
    {eqs' : List (List (List ℕ))} (h : checkBranchFeasible N₀_branch (n', eqs') = true)
    (hℓ : n' < ℓ) (D : ReplacementDesign (branchNeutralScope n' eqs')
      (prepareBranchEvalInput (n', eqs')).2.2.1.2.1 (prepareBranchEvalInput (n', eqs')).2.2.1.1
      (prepareBranchEvalInput (n', eqs')).2.2.1.2.2.2
      (prepareBranchEvalInput (n', eqs')).2.2.1.2.2.1 (ReplacementParams.tauRat n')) :
    let out := prepareBranchEvalInput (n', eqs')
    let P := fun i : Fin eqs'.length => HeavyBranchFold.toFinsetEquation n' eqs'[i]
    ((univariateClearedParityTruncatedSum univ P (commonDenom out.2.2.1.2.1 out.2.2.1.2.2.1 : ℤ)
        out.1.2 ℓ (designReplacementScaledIntMap D Sum.inl)).eval 0 /
      clearedProductDenom (commonDenom out.2.2.1.2.1 out.2.2.1.2.2.1 : ℤ) out.1.2 ℓ
        eqs'.length) % ((2 : ℤ) ^ ℓ) = (HeavyBranchFold.rootCount n' eqs' : ℤ) := by
  obtain ⟨_, hcan, hvars, _⟩ := feasible_of_checkBranchFeasible h
  have hk : ∀ i ∈ (univ : Finset (Fin eqs'.length)),
      ∀ M ∈ HeavyBranchFold.toFinsetEquation n' eqs'[i], #M ≤ sysMaxDegree eqs' := by
    intro i _ M hM
    simp only [HeavyBranchFold.toFinsetEquation, List.mem_toFinset, List.mem_map] at hM
    obtain ⟨m, hm, rfl⟩ := hM
    have hsub : (univ.filter fun j : Fin n' => (j : ℕ) ∈ m).map ⟨Fin.val, Fin.val_injective⟩ ⊆
        m.toFinset := fun u hu => by
      simp only [mem_map, mem_filter, mem_univ, true_and, Function.Embedding.coeFn_mk] at hu
      obtain ⟨j, hj, rfl⟩ := hu; exact List.mem_toFinset.mpr hj
    exact (card_map _).symm.trans_le ((card_le_card hsub).trans
      ((List.toFinset_card_le m).trans (length_mem_le_sysMaxDegree (List.getElem_mem i.isLt) hm)))
  have hrec := emod_ediv_eval_zero_clearedParityTruncatedSum_design_eq_commonZeroCount D Sum.inl
    univ (fun i : Fin eqs'.length => HeavyBranchFold.toFinsetEquation n' eqs'[i]) hℓ hk
  simp only [card_univ, Fintype.card_fin] at hrec
  rwa [HeavyBranchFold.rootCount_eq_commonZeroCount hcan hvars]

/-- **Uniform eventual passage of `checkBranchFeasible` (Lemma 4.8 & §5.5)**: for every `1 ≤ β₀`,
above a constant threshold `N₁ ≥ max N₀_branch 20`, every canonical `< n'` system with
`b, w ≤ (clog 2 n') ^ β₀` passes `checkBranchFeasible` with `1 ≤ β ≤ β₀`. -/
theorem exists_threshold_checkBranchFeasible_eq_true (N₀_branch : ℕ) {β₀ : ℕ} (hβ₀ : 1 ≤ β₀) :
    ∃ N₁ : ℕ, max N₀_branch 20 ≤ N₁ ∧ ∀ {n' : ℕ} {eqs' : List (List (List ℕ))}, N₁ ≤ n' →
      (∀ eq ∈ eqs', IsCanonicalEquation eq) → (∀ eq ∈ eqs', ∀ m ∈ eq, ∀ v ∈ m, v < n') →
      branchMaxFactorIncidence n' eqs' ≤ Nat.clog 2 n' ^ β₀ →
      branchMaxFactorWidth n' eqs' ≤ Nat.clog 2 n' ^ β₀ →
      let β := ParameterCheck.chooseBeta (Nat.clog 2 n')
        (branchMaxFactorIncidence n' eqs') (branchMaxFactorWidth n' eqs')
      1 ≤ β ∧ β ≤ β₀ ∧ checkBranchFeasible N₀_branch (n', eqs') = true := by
  have hall : ∃ n_all : ℕ, 20 ≤ n_all ∧ ∀ β, 1 ≤ β → β ≤ β₀ → ∀ ⦃n b w M : ℕ⦄, n_all ≤ n →
      1 ≤ b → b ≤ Nat.clog 2 n ^ β → 1 ≤ w → w ≤ Nat.clog 2 n ^ β →
      n ≤ M → M ≤ b * n → ParameterCheck.checkScheduleFeasible n M b w β = true := by
    induction β₀, hβ₀ using Nat.le_induction with
    | base =>
      obtain ⟨n₁, hn₁, hf₁⟩ := ParameterCheck.exists_checkScheduleFeasible_eq_true le_rfl
      exact ⟨n₁, hn₁, fun β h1 hle => (show β = 1 by omega) ▸ hf₁⟩
    | succ k _ ih =>
      obtain ⟨n_k, hn_k, hf_k⟩ := ih
      obtain ⟨n_s, _, hf_s⟩ := ParameterCheck.exists_checkScheduleFeasible_eq_true (Nat.succ_pos k)
      refine ⟨max n_k n_s, le_trans hn_k (le_max_left _ _), fun β h1 hle n b w M hn => ?_⟩
      rcases Nat.eq_or_lt_of_le hle with rfl | hlt
      · exact hf_s (le_trans (le_max_right _ _) hn)
      · exact hf_k β h1 (Nat.lt_succ_iff.mp hlt) (le_trans (le_max_left _ _) hn)
  obtain ⟨n_all, _, hchk_all⟩ := hall
  refine ⟨max (max N₀_branch 20) n_all, le_max_left _ _, fun {n' eqs'} hn' hcan hvars hb hw => ?_⟩
  have hn_guard : N₀_branch ≤ n' := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn'
  have hn_20 : 20 ≤ n' := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn'
  have hlam2 : 2 ≤ Nat.clog 2 n' :=
    (show 2 = Nat.clog 2 (2 ^ 2) from (Nat.clog_pow 2 2 Nat.one_lt_two).symm).trans_le
      (Nat.clog_mono_right 2 (by omega))
  obtain ⟨hβ1, hb_β, hw_β, hmin⟩ := ParameterCheck.chooseBeta_spec
    (b := branchMaxFactorIncidence n' eqs') (w := branchMaxFactorWidth n' eqs') hlam2
  have hβ_le : ParameterCheck.chooseBeta (Nat.clog 2 n')
      (branchMaxFactorIncidence n' eqs') (branchMaxFactorWidth n' eqs') ≤ β₀ := by
    by_contra hgt; exact hmin β₀ hβ₀ (Nat.lt_of_not_ge hgt) ⟨hb, hw⟩
  have hsched := hchk_all _ hβ1 hβ_le (le_trans (le_max_right _ _) hn')
    (one_le_branchMaxFactorIncidence n' eqs') hb_β (one_le_branchMaxFactorWidth n' eqs') hw_β
    (le_branchAugmentedIncidence n' eqs') (branchAugmentedIncidence_le_mul n' eqs')
  refine ⟨hβ1, hβ_le, ?_⟩; unfold checkBranchFeasible
  simp only [Bool.and_eq_true, decide_eq_true_eq, checkVarsLt_eq_true_iff,
    checkCanonicalSystem_eq_true_iff]
  exact ⟨⟨⟨hn_guard, hvars⟩, hcan⟩, hsched⟩

/-! ### 3. Polynomial-Time Certificates for Checkers and Schedule Builders -/

section PolyTimeHelpers

open ComputableInPolyTime
local notation "CPT" => ComputableInPolyTime

private theorem unaryToBin : CPT id encUnary encNat := by fun_prop

private theorem binLe {α : Type} {encIn : α ↪ List Bool} {l r : α → ℕ}
    (hl : CPT l encIn encNat) (hr : CPT r encIn encNat) :
    CPT (fun x => decide (l x ≤ r x)) encIn encBool :=
  (show CPT (fun p : ℕ × ℕ => decide (p.1 ≤ p.2)) (encPair encNat encNat) encBool by
    fun_prop).comp (hl.prod hr)

private theorem unaryFoldMax (init : ℕ) :
    CPT (fun l : List ℕ => l.foldl max init) (encList encUnary) encUnary := by
  refine foldl' (encA := encUnary) (encL := encList encUnary) (encB := encUnary)
    (list := id) (init := fun _ => init) (step := max)
    id' (const init) (by fun_prop) (B := fun l => init + (encList encUnary l).length)
    ((PolyBounded.const init).add .self) (fun l i _ => ?_)
  simp only [encUnary_apply, List.length_replicate]
  refine foldl_max_le_iff.mpr ⟨Nat.le_add_right _ _, fun x hx => ?_⟩
  have hsz := SizedListEncoding.length_elem_le (encA := encUnary) (encL := encList encUnary)
    l x (List.mem_of_mem_take hx)
  simp only [encUnary_apply, List.length_replicate] at hsz; omega

@[fun_prop]
theorem computableInPolyTime_checkVarsLt :
    CPT (fun p : ℕ × List (List (List ℕ)) => checkVarsLt p.1 p.2)
      (encPair encUnary encSys) encBool := by
  unfold checkVarsLt
  have hm : CPT (fun q : ℕ × List ℕ => q.2.all fun v => decide (v < q.1))
      (encPair encUnary (encList encNat)) encBool :=
    allWithInput (snd _ _) (binary_lt' (snd _ _) (unaryToBin.comp ((fst _ _).fst')))
  have heq : CPT (fun q : ℕ × List (List ℕ) => q.2.all fun m => m.all fun v => decide (v < q.1))
      (encPair encUnary encEq) encBool :=
    allWithInput (snd _ _) (hm.comp (((fst _ _).fst').prod (snd _ _)))
  exact allWithInput (snd _ _) (heq.comp (((fst _ _).fst').prod (snd _ _)))

private theorem computableInPolyTime_checkCanonicalMonomial :
    CPT checkCanonicalMonomial (encList encNat) encBool := by
  unfold checkCanonicalMonomial; let encP1 := encPair (encList encNat) encUnary
  have hget := listGetD (encA := encNat) (encL := encList encNat) 0
  have hinner : CPT
      (fun p : List ℕ × ℕ => (List.range p.2).all fun j => decide (p.1.getD j 0 < p.1.getD p.2 0))
      encP1 encBool :=
    allWithInput (range.comp (snd (encList encNat) encUnary))
      (binary_lt' (hget.comp (((fst encP1 encUnary).fst').prod (snd encP1 encUnary)))
        (hget.comp (((fst encP1 encUnary).fst').prod ((fst encP1 encUnary).snd'))))
  exact allWithInput (range.comp (length_list encNat)) hinner

private theorem computableInPolyTime_checkCanonicalEquation :
    CPT checkCanonicalEquation encEq encBool := by
  unfold checkCanonicalEquation; let encP1 := encPair encEq encUnary
  have hget := listGetD (encA := encList encNat) (encL := encEq) []
  have hneq := bool_not.comp (decide_eq'
    (hget.comp (((fst encP1 encUnary).fst').prod (snd encP1 encUnary)))
    (hget.comp (((fst encP1 encUnary).fst').prod ((fst encP1 encUnary).snd'))))
  have hinner : CPT (fun p : List (List ℕ) × ℕ =>
      (List.range p.2).all fun j => !decide (p.1.getD j [] = p.1.getD p.2 [])) encP1 encBool :=
    allWithInput (range.comp (snd encEq encUnary)) hneq
  exact bool_and' (allWithInput (range.comp (length_list (encList encNat))) hinner)
    (allWithInput id' (computableInPolyTime_checkCanonicalMonomial.comp
      (snd encEq (encList encNat))))

@[fun_prop]
theorem computableInPolyTime_checkCanonicalSystem : CPT checkCanonicalSystem encSys encBool :=
  allWithInput id' (computableInPolyTime_checkCanonicalEquation.comp (snd encSys encEq))

@[fun_prop]
theorem computableInPolyTime_scopeWidthOn :
    CPT (fun p : ℕ × List (List ℕ) => scopeWidthOn p.1 p.2) (encPair encUnary encEq) encUnary := by
  unfold scopeWidthOn; let encIn := encPair encUnary encEq
  have hmem := decide_mem (fst (encList encNat) encUnary)
    (unaryToBin.comp (snd (encList encNat) encUnary))
  have hany : CPT (fun q : (ℕ × List (List ℕ)) × ℕ => q.1.2.any fun m => decide (q.2 ∈ m))
      (encPair encIn encUnary) encBool :=
    anyWithInput ((fst encIn encUnary).snd')
      (hmem.comp ((snd (encPair encIn encUnary) (encList encNat)).prod
        ((fst (encPair encIn encUnary) (encList encNat)).snd')))
  exact countPWithInput (range.comp (fst encUnary encEq)) hany

@[fun_prop]
theorem computableInPolyTime_sysMaxDegree : CPT sysMaxDegree encSys encUnary := by
  unfold sysMaxDegree
  have hmap : CPT (List.map List.length) encEq (encList encUnary) :=
    mapWithInput (f := fun (_ : List (List ℕ)) (m : List ℕ) => m.length) id'
      ((length_list encNat).comp (snd encEq (encList encNat)))
  exact (unaryFoldMax 0).comp (hmap.comp (show CPT List.flatten encSys encEq by fun_prop))

@[fun_prop]
theorem computableInPolyTime_branchMaxFactorIncidence :
    CPT (fun p : ℕ × List (List (List ℕ)) => branchMaxFactorIncidence p.1 p.2)
      (encPair encUnary encSys) encNat := by
  unfold branchMaxFactorIncidence; let encIn := encPair encUnary encSys
  have hlist : CPT (fun p : ℕ × List (List (List ℕ)) => (List.range p.1).map fun v =>
      varDegree v p.2) encIn (encList encUnary) :=
    mapWithInput (range.comp (fst encUnary encSys)) (computableInPolyTime_varDegree.comp
      ((unaryToBin.comp (snd encIn encUnary)).prod ((fst encIn encUnary).snd')))
  exact unaryToBin.comp (unary_add.comp (((unaryFoldMax 0).comp hlist).prod (const 1)))

@[fun_prop]
theorem computableInPolyTime_branchMaxFactorWidth :
    CPT (fun p : ℕ × List (List (List ℕ)) => branchMaxFactorWidth p.1 p.2)
      (encPair encUnary encSys) encNat := by
  unfold branchMaxFactorWidth; let encIn := encPair encUnary encSys
  have hsc := computableInPolyTime_scopeWidthOn
  have hlist : CPT (fun p : ℕ × List (List (List ℕ)) => p.2.map (scopeWidthOn p.1))
      encIn (encList encUnary) :=
    mapWithInput (snd encUnary encSys) (hsc.comp (((fst encIn encEq).fst').prod (snd encIn encEq)))
  exact unaryToBin.comp ((unaryFoldMax 1).comp hlist)

@[fun_prop]
theorem computableInPolyTime_branchAugmentedIncidence :
    CPT (fun p : ℕ × List (List (List ℕ)) => branchAugmentedIncidence p.1 p.2)
      (encPair encUnary encSys) encNat := by
  unfold branchAugmentedIncidence; let encIn := encPair encUnary encSys
  have hlist : CPT (fun p : ℕ × List (List (List ℕ)) => p.2.map (scopeWidthOn p.1))
      encIn (encList encNat) :=
    mapWithInput (snd encUnary encSys) (unaryToBin.comp
      (computableInPolyTime_scopeWidthOn.comp
        (((fst encIn encEq).fst').prod (snd encIn encEq))))
  exact binary_add.comp (((show CPT List.sum (encList encNat) encNat by fun_prop).comp hlist).prod
    (unaryToBin.comp (fst encUnary encSys)))

@[fun_prop]
theorem computableInPolyTime_prepareBranchEvalInput :
    CPT prepareBranchEvalInput (encPair encUnary encSys) encBranchEvalInput := by
  have hn_u := fst encUnary encSys
  have hn_b := unaryToBin.comp hn_u
  have heqs := snd encUnary encSys
  have hk' := computableInPolyTime_sysMaxDegree.comp heqs
  have hβ := ParameterCheck.computableInPolyTime_chooseBeta_apply
    (binary_clog_two_nat.comp hn_b)
    computableInPolyTime_branchMaxFactorIncidence computableInPolyTime_branchMaxFactorWidth
  have hr := ParameterCheck.computableInPolyTime_numGroups.comp hn_b
  have hQ := ParameterCheck.computableInPolyTime_numNodes.comp hn_b
  have hR := ParameterCheck.computableInPolyTime_rowBound_apply hβ hn_b
  have hA := ParameterCheck.computableInPolyTime_intervalStart_apply hβ hn_b
  unfold prepareBranchEvalInput encBranchEvalInput ParameterCheck.computeScheduleParams
  exact ((hn_u.prod hk').prod ((computableInPolyTime_branchMaxFactorIncidence.prod
    (computableInPolyTime_branchMaxFactorWidth.prod
      (computableInPolyTime_branchAugmentedIncidence.prod hβ))).prod
    ((hr.prod (hQ.prod (hR.prod hA))).prod heqs))).of_enc_eq fun _ => rfl

@[fun_prop]
theorem computableInPolyTime_checkBranchFeasible (N₀_branch : ℕ) :
    CPT (checkBranchFeasible N₀_branch) (encPair encUnary encSys) encBool := by
  have hn_b := unaryToBin.comp (fst encUnary encSys)
  have hguard : CPT (fun p : ℕ × List (List (List ℕ)) =>
      decide (N₀_branch ≤ p.1) && checkVarsLt p.1 p.2 && checkCanonicalSystem p.2)
      (encPair encUnary encSys) encBool :=
    bool_and' (bool_and'
      (binLe (const N₀_branch) hn_b)
      computableInPolyTime_checkVarsLt)
      (computableInPolyTime_checkCanonicalSystem.comp (snd encUnary encSys))
  have hβ := ParameterCheck.computableInPolyTime_chooseBeta_apply
    (binary_clog_two_nat.comp hn_b)
    computableInPolyTime_branchMaxFactorIncidence computableInPolyTime_branchMaxFactorWidth
  have hsched := ParameterCheck.computableInPolyTime_checkScheduleFeasible_apply hn_b
    computableInPolyTime_branchAugmentedIncidence computableInPolyTime_branchMaxFactorIncidence
    computableInPolyTime_branchMaxFactorWidth hβ
  exact (hguard.bool_and' hsched).of_enc_eq fun _ => rfl

@[fun_prop]
theorem computableInPolyTime_checkTopFeasible (N₀_top : ℕ) :
    CPT (checkTopFeasible N₀_top) encSparseSystemInput encBool := by
  unfold encSparseSystemInput; let encP := encPair encUnary (encPair encNat encNat)
  have hn_u := fst encUnary (encPair encP encSys)
  have hn_b := unaryToBin.comp hn_u
  have hrest := snd encUnary (encPair encP encSys)
  have hparam := (fst encP encSys).comp hrest
  have heqs := (snd encP encSys).comp hrest
  have hk_b := unaryToBin.comp ((fst encUnary (encPair encNat encNat)).comp hparam)
  have hsb := (snd encUnary (encPair encNat encNat)).comp hparam
  have hs_b := (fst encNat encNat).comp hsb
  have hb₀ := (snd encNat encNat).comp hsb
  have hS_len := unaryToBin.comp ((length_list encNat).comp
    (HeavyBranchFold.computableInPolyTime_heavyVarList_comp hn_u hb₀ heqs))
  have hdeg_b := unaryToBin.comp (computableInPolyTime_sysMaxDegree.comp heqs)
  have hvars := computableInPolyTime_checkVarsLt.comp (hn_u.prod heqs)
  have hcan := computableInPolyTime_checkCanonicalSystem.comp heqs
  exact bool_and' (bool_and' (bool_and' (bool_and' (bool_and'
    (binLe (const N₀_top) hn_b) (binLe (const 1) hs_b)) hvars)
    hcan) (binLe hdeg_b hk_b))
    (binLe hS_len (binary_div.comp (hn_b.prod hs_b)))

@[fun_prop]
theorem computableInPolyTime_toBranchInput :
    CPT toBranchInput encSparseSystemInput HeavyBranchFold.encBranchInput := by
  unfold toBranchInput encSparseSystemInput HeavyBranchFold.encBranchInput
  let encParam := encPair encUnary (encPair encNat encNat)
  have hn_u := fst encUnary (encPair encParam encSys)
  have hrest := snd encUnary (encPair encParam encSys)
  have hb₀ := (snd encNat encNat).comp
    ((snd encUnary (encPair encNat encNat)).comp
      ((fst encParam encSys).comp hrest))
  have heqs := (snd encParam encSys).comp hrest
  exact hn_u.prod ((HeavyBranchFold.computableInPolyTime_heavyVarList_comp hn_u hb₀ heqs).prod heqs)

@[fun_prop]
theorem computableInPolyTime_mkPaperSparseInput :
    CPT (fun p : (ℕ × ℕ) × List (List (List ℕ)) => mkPaperSparseInput p.1.1 p.1.2 p.2)
      (encPair (encPair encUnary encUnary) encSys) encSparseSystemInput := by
  unfold mkPaperSparseInput encSparseSystemInput
  have hn_u := (fst encUnary encUnary).comp (fst (encPair encUnary encUnary) encSys)
  have hk_u := (snd encUnary encUnary).comp (fst (encPair encUnary encUnary) encSys)
  have heqs := snd (encPair encUnary encUnary) encSys
  have hn_b := unaryToBin.comp hn_u
  have hM := computableInPolyTime_branchAugmentedIncidence.comp (hn_u.prod heqs)
  have hmax1 : CPT (fun x : ℕ => max 1 x) encNat encNat :=
    ((binLe (const 1) id').ite' id' (const 1)).of_enc_eq fun x =>
      congrArg encNat (by split_ifs with hx <;> simp only [decide_eq_true_eq] at hx <;> omega)
  have hs := hmax1.comp (ParameterCheck.computableInPolyTime_heavyIncidenceCutoff_apply
    (const 1) hn_b)
  have hb₀ := hmax1.comp (ParameterCheck.computableInPolyTime_heavyIncidenceCutoff_apply hM hn_b)
  exact hn_u.prod ((hk_u.prod (hs.prod hb₀)).prod heqs)

end PolyTimeHelpers

/-! ### 4. Semantic Exactness & Heavy-Branching Invariants (§5.5, pp. 38–39) -/

section SemanticExactness

variable {N₀_top N₀_branch : ℕ} {branchEval : BranchEvalInput → ℕ}

/-- When `branchEval` is exact on feasible branches, `guardedBranchSolver = rootCount` always. -/
theorem guardedBranchSolver_eq_rootCount
    (hbranch : ∀ n' eqs', checkBranchFeasible N₀_branch (n', eqs') = true →
      branchEval (prepareBranchEvalInput (n', eqs')) = HeavyBranchFold.rootCount n' eqs')
    (n' : ℕ) (eqs' : List (List (List ℕ))) :
    guardedBranchSolver N₀_branch branchEval n' eqs' = HeavyBranchFold.rootCount n' eqs' := by
  unfold guardedBranchSolver; cases h : checkBranchFeasible N₀_branch (n', eqs')
  · simp only [Bool.false_eq_true, ↓reduceIte, countSystemExhaustive_eq_rootCount]
  · simp only [↓reduceIte]; exact hbranch n' eqs' h

/-- When `branchEval ≤ 2 ^ n'` on feasible inputs, `guardedBranchSolver ≤ 2 ^ n'` everywhere. -/
theorem guardedBranchSolver_le_two_pow
    (hbound : ∀ n' eqs', checkBranchFeasible N₀_branch (n', eqs') = true →
      branchEval (prepareBranchEvalInput (n', eqs')) ≤ 2 ^ n')
    (n' : ℕ) (eqs' : List (List (List ℕ))) :
    guardedBranchSolver N₀_branch branchEval n' eqs' ≤ 2 ^ n' := by
  unfold guardedBranchSolver; cases h : checkBranchFeasible N₀_branch (n', eqs')
  · simp only [Bool.false_eq_true, ↓reduceIte, countSystemExhaustive_eq_rootCount]
    exact HeavyBranchFold.rootCount_le_two_pow n' eqs'
  · simp only [↓reduceIte]; exact hbound n' eqs' h

theorem checkTopFeasible_eq_true_iff {inp : SparseSystemInput} :
    checkTopFeasible N₀_top inp = true ↔
      N₀_top ≤ inp.1 ∧ 1 ≤ inp.2.1.2.1 ∧
        (∀ eq ∈ inp.2.2, ∀ m ∈ eq, ∀ v ∈ m, v < inp.1) ∧ (∀ eq ∈ inp.2.2, IsCanonicalEquation eq) ∧
        (∀ eq ∈ inp.2.2, ∀ m ∈ eq, m.length ≤ inp.2.1.1) ∧
        (HeavyBranchFold.heavyVarList inp.1 inp.2.1.2.2 inp.2.2).length ≤ inp.1 / inp.2.1.2.1 := by
  unfold checkTopFeasible
  simp only [Bool.and_eq_true, decide_eq_true_eq, checkVarsLt_eq_true_iff,
    checkCanonicalSystem_eq_true_iff, sysMaxDegree_le_iff]; tauto

/-- **Pointwise unconditional exactness (§5.5)**: `countSparsePolySystem = rootCount` always. -/
theorem countSparsePolySystem_eq_rootCount
    (hbranch : ∀ n' eqs', checkBranchFeasible N₀_branch (n', eqs') = true →
      branchEval (prepareBranchEvalInput (n', eqs')) = HeavyBranchFold.rootCount n' eqs')
    (inp : SparseSystemInput) :
    countSparsePolySystem N₀_top N₀_branch branchEval inp =
      HeavyBranchFold.rootCount inp.1 inp.2.2 := by
  unfold countSparsePolySystem; cases hx : checkTopFeasible N₀_top inp
  · simp only [Bool.false_eq_true, ↓reduceIte, countSystemExhaustive_eq_rootCount]
  · simp only [↓reduceIte]; obtain ⟨_, _, hvars, _, _, _⟩ := checkTopFeasible_eq_true_iff.mp hx
    exact HeavyBranchFold.countByBranching_eq_rootCount (HeavyBranchFold.nodup_heavyVarList _ _ _)
      (fun _ hs => HeavyBranchFold.lt_of_mem_heavyVarList hs) hvars
      (fun _ _ n' sys' _ => guardedBranchSolver_eq_rootCount hbranch n' sys')

/-- **Semantic bridge to `Cslib.BitString.commonZeroCount` (§5.5, Theorem 2.2)** on `Fin n`. -/
theorem countSparsePolySystem_eq_commonZeroCount
    (hbranch : ∀ n' eqs', checkBranchFeasible N₀_branch (n', eqs') = true →
      branchEval (prepareBranchEvalInput (n', eqs')) = HeavyBranchFold.rootCount n' eqs')
    (inp : SparseSystemInput) (hcan : ∀ eq ∈ inp.2.2, IsCanonicalEquation eq)
    (hvars : ∀ eq ∈ inp.2.2, ∀ m ∈ eq, ∀ v ∈ m, v < inp.1) :
    countSparsePolySystem N₀_top N₀_branch branchEval inp =
      commonZeroCount (univ : Finset (Fin inp.2.2.length))
        (fun i : Fin inp.2.2.length => HeavyBranchFold.toFinsetEquation inp.1 inp.2.2[i]) := by
  rw [countSparsePolySystem_eq_rootCount hbranch inp,
    HeavyBranchFold.rootCount_eq_commonZeroCount hcan hvars]

end SemanticExactness

/-- Markov heavy-variable bound (§5.5, p. 38): `M_eqs * s_div ≤ b₀ * n → |S| ≤ n / s_div`. -/
theorem length_heavyVarList_le_div_of_incidence {n b₀ s_div : ℕ} {eqs : List (List (List ℕ))}
    (hb₀ : 1 ≤ b₀) (hs : 1 ≤ s_div) (hvars : ∀ eq ∈ eqs, ∀ m ∈ eq, ∀ v ∈ m, v < n)
    (hM : (eqs.map (scopeWidthOn n)).sum * s_div ≤ b₀ * n) :
    (HeavyBranchFold.heavyVarList n b₀ eqs).length ≤ n / s_div := by
  have heq_sum : (eqs.map fun eq => (equationVars eq).length) = eqs.map (scopeWidthOn n) :=
    List.map_congr_left fun eq heq => (scopeWidthOn_eq_length_equationVars (hvars eq heq)).symm
  have hdiv := HeavyBranchFold.length_heavyVarList_le_div hb₀ hvars; rw [heq_sum] at hdiv
  refine hdiv.trans ((Nat.le_div_iff_mul_le hs).mpr (Nat.le_of_mul_le_mul_right ?_ hb₀))
  have hqb : (eqs.map (scopeWidthOn n)).sum / b₀ * b₀ ≤ (eqs.map (scopeWidthOn n)).sum :=
    Nat.div_mul_le_self _ _
  calc ((eqs.map (scopeWidthOn n)).sum / b₀ * s_div) * b₀
      = ((eqs.map (scopeWidthOn n)).sum / b₀ * b₀) * s_div := by ring
    _ ≤ (eqs.map (scopeWidthOn n)).sum * s_div := Nat.mul_le_mul_right s_div hqb
    _ ≤ n * b₀ := hM.trans_eq (Nat.mul_comm b₀ n)

/-- `checkTopFeasible N₀_top (mkPaperSparseInput n k_deg eqs)` holds for canonical `< n` systems. -/
theorem checkTopFeasible_mkPaperSparseInput_of_le {N₀_top n k_deg : ℕ}
    {eqs : List (List (List ℕ))} (hn : max N₀_top 2 ≤ n)
    (hcan : ∀ eq ∈ eqs, IsCanonicalEquation eq) (hvars : ∀ eq ∈ eqs, ∀ m ∈ eq, ∀ v ∈ m, v < n)
    (hdeg : ∀ eq ∈ eqs, ∀ m ∈ eq, m.length ≤ k_deg) :
    checkTopFeasible N₀_top (mkPaperSparseInput n k_deg eqs) = true := by
  have hn2 : 2 ≤ n := le_trans (le_max_right _ _) hn
  have hlam_nz : ¬Nat.clog 2 n = 0 := by
    have := Nat.clog_pos Nat.one_lt_two (by omega : 1 < n); omega
  set M := branchAugmentedIncidence n eqs
  set s := max 1 (ParameterCheck.heavyIncidenceCutoff 1 n)
  set b₀ := max 1 (ParameterCheck.heavyIncidenceCutoff M n)
  have hs_eq : s = (Nat.clog 2 n - 1).sqrt + 1 := by
    have hc : ParameterCheck.heavyIncidenceCutoff 1 n = (Nat.clog 2 n - 1).sqrt + 1 := by
      unfold ParameterCheck.heavyIncidenceCutoff; simp only [hlam_nz, ↓reduceIte]
      rw [show 1 + n - 1 = n by omega, Nat.div_self (by omega : 0 < n), one_mul]
    dsimp only [s]; rw [hc]; omega
  have hM_le : M ≤ ((M + n - 1) / n) * n := by
    have := Nat.div_add_mod (M + n - 1) n; have := Nat.mod_lt (M + n - 1) (by omega : 0 < n)
    rw [Nat.mul_comm]; omega
  have hb₀_ge : ((M + n - 1) / n) * s ≤ b₀ := by
    refine le_trans ?_ (le_max_right 1 (ParameterCheck.heavyIncidenceCutoff M n))
    unfold ParameterCheck.heavyIncidenceCutoff; simp only [hlam_nz, ↓reduceIte, ← hs_eq, le_rfl]
  have hinc : (eqs.map (scopeWidthOn n)).sum * s ≤ b₀ * n :=
    calc (eqs.map (scopeWidthOn n)).sum * s ≤ M * s := Nat.mul_le_mul_right s (Nat.le_add_right _ _)
      _ ≤ (((M + n - 1) / n) * n) * s := Nat.mul_le_mul_right s hM_le
      _ = (((M + n - 1) / n) * s) * n := by ring
      _ ≤ b₀ * n := Nat.mul_le_mul_right n hb₀_ge
  exact checkTopFeasible_eq_true_iff.mpr
    ⟨le_trans (le_max_left _ _) hn, le_max_left _ _, hvars, hcan, hdeg,
      length_heavyVarList_le_div_of_incidence (le_max_left _ _) (le_max_left _ _) hvars hinc⟩

/-- Invariants of `.reduced n' sys'` branches (`n ≤ 2 * n'`, canonical `< n'`, `b ≤ b₀ + 1`). -/
theorem reduced_branch_invariants {N₀_top : ℕ} {inp : SparseSystemInput} {vals : List Bool}
    {n' : ℕ} {sys' : List (List (List ℕ))} (htop : checkTopFeasible N₀_top inp = true)
    (hs2 : 2 ≤ inp.2.1.2.1)
    (hred : HeavyBranchFold.prepareBranch inp.1
      (HeavyBranchFold.heavyVarList inp.1 inp.2.1.2.2 inp.2.2) vals inp.2.2 = .reduced n' sys') :
    n' = inp.1 - (HeavyBranchFold.heavyVarList inp.1 inp.2.1.2.2 inp.2.2).length ∧
      inp.1 ≤ 2 * n' ∧ (∀ eq' ∈ sys', IsCanonicalEquation eq') ∧
      (∀ eq' ∈ sys', ∀ m' ∈ eq', ∀ v' ∈ m', v' < n') ∧
      (∀ eq' ∈ sys', ∀ m' ∈ eq', m'.length ≤ inp.2.1.1) ∧
      branchMaxFactorIncidence n' sys' ≤ inp.2.1.2.2 + 1 ∧
      branchMaxFactorWidth n' sys' ≤ branchMaxFactorWidth inp.1 inp.2.2 := by
  obtain ⟨_, _, hvars, hcan, hdeg, hS_le⟩ := checkTopFeasible_eq_true_iff.mp htop
  have hS_nd := HeavyBranchFold.nodup_heavyVarList inp.1 inp.2.1.2.2 inp.2.2
  have hSn : ∀ s ∈ HeavyBranchFold.heavyVarList inp.1 inp.2.1.2.2 inp.2.2, s < inp.1 :=
    fun _ hs => HeavyBranchFold.lt_of_mem_heavyVarList hs
  obtain ⟨hn'_eq, _, _, _, hcan', hvars'⟩ :=
    HeavyBranchFold.prepareBranch_reduced_canonical hS_nd hSn hcan hvars hred
  have hS_half := hS_le.trans (Nat.div_le_div_left hs2 (by omega))
  have hvd' := HeavyBranchFold.prepareBranch_reduced_varDegree_le hS_nd hSn
    (fun u hun huS => HeavyBranchFold.varDegree_le_of_not_mem_heavyVarList hun huS) hred
  have hb' : branchMaxFactorIncidence n' sys' ≤ inp.2.1.2.2 + 1 :=
    Nat.succ_le_succ (foldl_max_le_iff.mpr ⟨Nat.zero_le _, fun x hx => by
      obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hx; exact hvd' v (List.mem_range.mp hv)⟩)
  have hw' : branchMaxFactorWidth n' sys' ≤ branchMaxFactorWidth inp.1 inp.2.2 :=
    foldl_max_le_iff.mpr ⟨one_le_branchMaxFactorWidth inp.1 inp.2.2, fun x hx => by
      obtain ⟨eq', heq', rfl⟩ := List.mem_map.mp hx
      obtain ⟨eq₀, heq₀, _, hsc⟩ :=
        (HeavyBranchFold.prepareBranch_reduced_length_le hred).2 eq' heq'
      rw [scopeWidthOn_eq_length_equationVars (hvars' eq' heq')]
      exact (hsc.trans_eq (scopeWidthOn_eq_length_equationVars (hvars eq₀ heq₀)).symm).trans
        (le_foldl_max_of_mem (List.mem_map_of_mem heq₀))⟩
  exact ⟨hn'_eq, by omega, hcan', hvars',
    HeavyBranchFold.prepareBranch_reduced_degree_le hdeg hred, hb', hw'⟩

/-- Polylogarithmic transfer (§5.5): `(clog 2 n) ^ α ≤ (clog 2 n') ^ (2 * α)` for `n ≤ 2 * n'`. -/
theorem clog_pow_le_clog_pow_two_mul {n n' : ℕ} (hn' : 4 ≤ n') (hn : n ≤ 2 * n') (α : ℕ) :
    Nat.clog 2 n ^ α ≤ Nat.clog 2 n' ^ (2 * α) := by
  set L' := Nat.clog 2 n'
  have hL'2 : 2 ≤ L' :=
    (show 2 = Nat.clog 2 (2 ^ 2) from (Nat.clog_pow 2 2 Nat.one_lt_two).symm).trans_le
      (Nat.clog_mono_right 2 (by omega))
  have hn_pow : n ≤ 2 ^ (L' + 1) :=
    (hn.trans (Nat.mul_le_mul_left 2 (Nat.le_pow_clog Nat.one_lt_two n'))).trans_eq (by ring)
  have hclog_le : Nat.clog 2 n ≤ L' ^ 2 := by
    have := (Nat.clog_le_iff_le_pow Nat.one_lt_two).mpr hn_pow; nlinarith
  exact (Nat.pow_le_pow_left hclog_le α).trans_eq (Nat.pow_mul L' 2 α).symm

/-! ### 5. Native Resource Certificates & Split Time / Polynomial-Space Bounds -/

section ResourceCertificates

variable {branchEval : BranchEvalInput → ℕ}

/-- Selected-branch `NativeCertificate` for `guardedBranchSolver N₀_branch branchEval`. -/
noncomputable def guardedBranchCertificate (N₀_branch : ℕ)
    (cBranch : NativeCertificate branchEval encBranchEvalInput encNat) :
    NativeCertificate (fun p : ℕ × List (List (List ℕ)) =>
      guardedBranchSolver N₀_branch branchEval p.1 p.2) (encPair encUnary encSys) encNat :=
  ExhaustiveCountFallback.guardedBranchOfPolyTime
    (computableInPolyTime_checkBranchFeasible N₀_branch)
    (cBranch.comp (NativeCertificate.ofPolyTime computableInPolyTime_prepareBranchEvalInput))
    ExhaustiveCountFallback.countSystemExhaustiveCertificate

/-- Polynomial workspace preservation for `guardedBranchCertificate`. -/
theorem polyBounded_guardedBranchCertificate_space (N₀_branch : ℕ)
    (cBranch : NativeCertificate branchEval encBranchEvalInput encNat)
    (hs : PolyBounded (fun x => (encBranchEvalInput x).length) cBranch.space) :
    PolyBounded (fun p : ℕ × List (List (List ℕ)) => (encPair encUnary encSys p).length)
      (guardedBranchCertificate N₀_branch cBranch).space := by
  have hprep :=
    NativeCertificate.ofPolyTime_isPolynomial computableInPolyTime_prepareBranchEvalInput
  exact ExhaustiveCountFallback.polyBounded_branch_space
    (NativeCertificate.ofPolyTime (computableInPolyTime_checkBranchFeasible N₀_branch)) _ _
    (NativeCertificate.ofPolyTime_isPolynomial _).2
    (hprep.2.add (hs.comp computableInPolyTime_prepareBranchEvalInput.polyBounded_length))
    ExhaustiveCountFallback.polyBounded_countSystemExhaustive_space

/-- Constant-threshold branch-fallback time bound when `checkBranchFeasible = false → p.1 < N₁`. -/
theorem exists_guardedBranchCertificate_time_le (N₀_branch N₁ : ℕ)
    (cBranch : NativeCertificate branchEval encBranchEvalInput encNat) :
    ∃ C_br d_br : ℕ, ∀ p : ℕ × List (List (List ℕ)),
      (checkBranchFeasible N₀_branch p = false → p.1 < N₁) →
      (guardedBranchCertificate N₀_branch cBranch).time p ≤
        (if checkBranchFeasible N₀_branch p then cBranch.time (prepareBranchEvalInput p) else 0) +
          C_br * ((encPair encUnary encSys p).length + 1) ^ d_br := by
  have hok := NativeCertificate.ofPolyTime_isPolynomial
    (computableInPolyTime_checkBranchFeasible N₀_branch)
  have hprep :=
    NativeCertificate.ofPolyTime_isPolynomial computableInPolyTime_prepareBranchEvalInput
  obtain ⟨P_ex, Q_ex, hP, hQ, ht_ex⟩ := ExhaustiveCountFallback.exists_countSystemExhaustive_time_le
  have hpoly : PolyBounded (fun p : ℕ × List (List (List ℕ)) => (encPair encUnary encSys p).length)
      (fun p => (NativeCertificate.ofPolyTime
          (computableInPolyTime_checkBranchFeasible N₀_branch)).time p +
        (NativeCertificate.ofPolyTime computableInPolyTime_prepareBranchEvalInput).time p +
        ((2 ^ N₁ + 1) * P_ex p + Q_ex p)) :=
    (hok.1.add hprep.1).add (((PolyBounded.const (2 ^ N₁ + 1)).mul hP).add hQ)
  obtain ⟨C_br, d_br, hCd⟩ := hpoly.exists_le
  refine ⟨C_br, d_br, fun ⟨n', eqs'⟩ hthresh => ?_⟩
  simp only [guardedBranchCertificate, ExhaustiveCountFallback.guardedBranchOfPolyTime,
    NativeCertificate.branch_time, NativeCertificate.comp_time]
  have hbound := hCd (n', eqs')
  cases h : checkBranchFeasible N₀_branch (n', eqs')
  · simp only [Bool.false_eq_true, ↓reduceIte, zero_add]
    have hpow : 2 ^ n' ≤ 2 ^ N₁ := Nat.pow_le_pow_right (by omega) (Nat.le_of_lt (hthresh h))
    have hex := (ht_ex (n', eqs')).trans
      (Nat.add_le_add_right (Nat.mul_le_mul_right _ (Nat.add_le_add_right hpow 1)) _)
    omega
  · simp only [↓reduceIte]; omega

/-- Maximum per-branch solver cost across all `.reduced` branches of `inp : BranchInput`. -/
noncomputable def maxReducedCost (cost : ℕ × List (List (List ℕ)) → ℕ)
    (inp : HeavyBranchFold.BranchInput) : ℕ :=
  ((List.range (2 ^ inp.2.1.length)).map fun idx =>
    match HeavyBranchFold.prepareBranch inp.1 inp.2.1 (lowBits inp.2.1.length idx) inp.2.2 with
    | .reduced n' sys' => cost (n', sys')
    | _ => 0).foldl max 0

private theorem le_maxReducedCost (cost : ℕ × List (List (List ℕ)) → ℕ)
    (inp : HeavyBranchFold.BranchInput) {idx : ℕ} (hidx : idx < 2 ^ inp.2.1.length)
    {n' : ℕ} {sys' : List (List (List ℕ))}
    (hred : HeavyBranchFold.prepareBranch inp.1 inp.2.1 (lowBits inp.2.1.length idx) inp.2.2 =
      .reduced n' sys') : cost (n', sys') ≤ maxReducedCost cost inp := by
  unfold maxReducedCost
  refine le_foldl_max_of_mem (List.mem_map.mpr ⟨idx, List.mem_range.mpr hidx, ?_⟩); rw [hred]

theorem maxReducedCost_le {cost : ℕ × List (List (List ℕ)) → ℕ}
    {inp : HeavyBranchFold.BranchInput} {B : ℕ}
    (hB : ∀ idx < 2 ^ inp.2.1.length, ∀ n' sys',
      HeavyBranchFold.prepareBranch inp.1 inp.2.1 (lowBits inp.2.1.length idx) inp.2.2 =
        .reduced n' sys' → cost (n', sys') ≤ B) : maxReducedCost cost inp ≤ B := by
  unfold maxReducedCost; refine foldl_max_le_iff.mpr ⟨Nat.zero_le B, fun x hx => ?_⟩
  obtain ⟨idx, hidx, rfl⟩ := List.mem_map.mp hx
  cases hout : HeavyBranchFold.prepareBranch inp.1 inp.2.1 (lowBits inp.2.1.length idx) inp.2.2 with
  | contradiction | tautology _ => exact Nat.zero_le B
  | reduced n' sys' => exact hB idx (List.mem_range.mp hidx) n' sys' hout

/-- Native certificate for `HeavyBranchFold.countByBranching (guardedBranchSolver ...)`. -/
noncomputable def guardedBranchingCertificate (N₀_branch : ℕ)
    (cBranch : NativeCertificate branchEval encBranchEvalInput encNat)
    (hbound : ∀ n' eqs', checkBranchFeasible N₀_branch (n', eqs') = true →
      branchEval (prepareBranchEvalInput (n', eqs')) ≤ 2 ^ n') :
    NativeCertificate (HeavyBranchFold.countByBranching (guardedBranchSolver N₀_branch branchEval))
      HeavyBranchFold.encBranchInput encNat :=
  let csolver := guardedBranchCertificate N₀_branch cBranch
  { time := fun inp => HeavyBranchFold.stepOverhead (HeavyBranchFold.encBranchInput inp).length +
      (2 ^ inp.2.1.length + 1) *
        (HeavyBranchFold.stepOverhead (HeavyBranchFold.encBranchInput inp).length +
          maxReducedCost csolver.time inp)
    space := fun inp => HeavyBranchFold.stepOverhead (HeavyBranchFold.encBranchInput inp).length +
      maxReducedCost csolver.space inp
    computes := HeavyBranchFold.countByBranching_computableInO csolver
      (maxReducedCost csolver.time) (maxReducedCost csolver.space)
      (fun _ _ _ n' sys' _ => guardedBranchSolver_le_two_pow hbound n' sys')
      (fun inp _ hidx _ _ hred => le_maxReducedCost csolver.time inp hidx hred)
      (fun inp _ hidx _ _ hred => le_maxReducedCost csolver.space inp hidx hred) }

private theorem polyBounded_maxReducedCost_space (N₀_branch : ℕ)
    (cBranch : NativeCertificate branchEval encBranchEvalInput encNat)
    (hs : PolyBounded (fun x => (encBranchEvalInput x).length) cBranch.space) :
    PolyBounded (fun b : HeavyBranchFold.BranchInput => (HeavyBranchFold.encBranchInput b).length)
      (maxReducedCost (guardedBranchCertificate N₀_branch cBranch).space) := by
  obtain ⟨cs, ds, hcs⟩ :=
    (polyBounded_guardedBranchCertificate_space N₀_branch cBranch hs).exists_le
  refine (NativeCertificate.polyBounded_pow_of_polyBounded PolyBounded.self cs ds).mono fun b => ?_
  refine maxReducedCost_le fun _ _ n' sys' hred => (hcs (n', sys')).trans ?_
  exact Nat.mul_le_mul_left cs
    (Nat.pow_le_pow_left (Nat.add_le_add_right (HeavyBranchFold.length_enc_reduced_le hred) 1) ds)

private theorem computableInPolyTime_exhaustProj :
    ComputableInPolyTime (fun inp : SparseSystemInput => (inp.1, inp.2.2))
      encSparseSystemInput (encPair encUnary encSys) := by
  unfold encSparseSystemInput
  exact (ComputableInPolyTime.fst _ _).prod
    ((ComputableInPolyTime.snd _ _).comp (ComputableInPolyTime.snd _ _))

/-- **Full native certificate for `countSparsePolySystem N₀_top N₀_branch branchEval`** (§5.5). -/
noncomputable def sparsePolyCounterCertificate (N₀_top N₀_branch : ℕ)
    (cBranch : NativeCertificate branchEval encBranchEvalInput encNat)
    (hbound : ∀ n' eqs', checkBranchFeasible N₀_branch (n', eqs') = true →
      branchEval (prepareBranchEvalInput (n', eqs')) ≤ 2 ^ n') :
    NativeCertificate (countSparsePolySystem N₀_top N₀_branch branchEval)
      encSparseSystemInput encNat :=
  ExhaustiveCountFallback.guardedBranchOfPolyTime (computableInPolyTime_checkTopFeasible N₀_top)
    ((guardedBranchingCertificate N₀_branch cBranch hbound).comp
      (NativeCertificate.ofPolyTime computableInPolyTime_toBranchInput))
    (ExhaustiveCountFallback.countSystemExhaustiveCertificate.comp
      (NativeCertificate.ofPolyTime computableInPolyTime_exhaustProj))

/-- **Independent polynomial workspace (§5.5, p. 39)** for `sparsePolyCounterCertificate`. -/
theorem polyBounded_sparsePolyCounterCertificate_space (N₀_top N₀_branch : ℕ)
    (cBranch : NativeCertificate branchEval encBranchEvalInput encNat)
    (hbound : ∀ n' eqs', checkBranchFeasible N₀_branch (n', eqs') = true →
      branchEval (prepareBranchEvalInput (n', eqs')) ≤ 2 ^ n')
    (hs : PolyBounded (fun x => (encBranchEvalInput x).length) cBranch.space) :
    PolyBounded (fun inp => (encSparseSystemInput inp).length)
      (sparsePolyCounterCertificate N₀_top N₀_branch cBranch hbound).space := by
  have hs_br := HeavyBranchFold.polyBounded_branchWorkspace
    (polyBounded_maxReducedCost_space N₀_branch cBranch hs)
  have hto := NativeCertificate.ofPolyTime_isPolynomial computableInPolyTime_toBranchInput
  have hpr := NativeCertificate.ofPolyTime_isPolynomial computableInPolyTime_exhaustProj
  exact ExhaustiveCountFallback.polyBounded_branch_space
    (NativeCertificate.ofPolyTime (computableInPolyTime_checkTopFeasible N₀_top))
    ((guardedBranchingCertificate N₀_branch cBranch hbound).comp
      (NativeCertificate.ofPolyTime computableInPolyTime_toBranchInput))
    _ (NativeCertificate.ofPolyTime_isPolynomial _).2
    (hto.2.add (hs_br.comp computableInPolyTime_toBranchInput.polyBounded_length))
    (hpr.2.add (ExhaustiveCountFallback.polyBounded_countSystemExhaustive_space.comp
      computableInPolyTime_exhaustProj.polyBounded_length))

/-- **Feasible-regime multi-branch time bound (§5.5)**: `≤ (2 ^ |S| + 1) * (poly + R)`. -/
theorem sparsePolyCounterCertificate_time_le_of_feasible (N₀_top N₀_branch : ℕ)
    (cBranch : NativeCertificate branchEval encBranchEvalInput encNat)
    (hbound : ∀ n' eqs', checkBranchFeasible N₀_branch (n', eqs') = true →
      branchEval (prepareBranchEvalInput (n', eqs')) ≤ 2 ^ n') :
    ∃ C_ov d_ov : ℕ, ∀ (inp : SparseSystemInput) (R_branch : ℕ),
      checkTopFeasible N₀_top inp = true →
      (∀ idx < 2 ^ (HeavyBranchFold.heavyVarList inp.1 inp.2.1.2.2 inp.2.2).length,
        ∀ n' sys', HeavyBranchFold.prepareBranch inp.1
          (HeavyBranchFold.heavyVarList inp.1 inp.2.1.2.2 inp.2.2)
          (lowBits (HeavyBranchFold.heavyVarList inp.1 inp.2.1.2.2 inp.2.2).length idx)
          inp.2.2 = .reduced n' sys' →
          (guardedBranchCertificate N₀_branch cBranch).time (n', sys') ≤ R_branch) →
      (sparsePolyCounterCertificate N₀_top N₀_branch cBranch hbound).time inp ≤
        (2 ^ (HeavyBranchFold.heavyVarList inp.1 inp.2.1.2.2 inp.2.2).length + 1) *
          (C_ov * ((encSparseSystemInput inp).length + 1) ^ d_ov + R_branch) := by
  have hok :=
    NativeCertificate.ofPolyTime_isPolynomial (computableInPolyTime_checkTopFeasible N₀_top)
  have hto := NativeCertificate.ofPolyTime_isPolynomial computableInPolyTime_toBranchInput
  have hstep : PolyBounded (fun inp => (encSparseSystemInput inp).length)
      (fun inp => HeavyBranchFold.stepOverhead
        (HeavyBranchFold.encBranchInput (toBranchInput inp)).length) :=
    (PolyBounded.of_polynomiallyBounded _ HeavyBranchFold.polynomiallyBounded_stepOverhead).comp
      computableInPolyTime_toBranchInput.polyBounded_length
  obtain ⟨C_ov, d_ov, hCov⟩ := ((hok.1.add hto.1).add (hstep.add hstep)).exists_le
  refine ⟨C_ov, d_ov, fun inp R_branch htop hR => ?_⟩
  have hmax := maxReducedCost_le (inp := toBranchInput inp)
    (cost := (guardedBranchCertificate N₀_branch cBranch).time) hR
  simp only [sparsePolyCounterCertificate, ExhaustiveCountFallback.guardedBranchOfPolyTime,
    NativeCertificate.branch_time, NativeCertificate.comp_time, guardedBranchingCertificate,
    htop, ↓reduceIte]
  set S_len := (HeavyBranchFold.heavyVarList inp.1 inp.2.1.2.2 inp.2.2).length
  set T_ok := (NativeCertificate.ofPolyTime (computableInPolyTime_checkTopFeasible N₀_top)).time inp
  set T_to := (NativeCertificate.ofPolyTime computableInPolyTime_toBranchInput).time inp
  set T_st := HeavyBranchFold.stepOverhead
    (HeavyBranchFold.encBranchInput (toBranchInput inp)).length
  set P := C_ov * ((encSparseSystemInput inp).length + 1) ^ d_ov
  have hbase : T_ok + T_to + (T_st + T_st) ≤ P := hCov inp
  have hmul := Nat.mul_le_mul_left (2 ^ S_len + 1) (Nat.add_le_add_left hmax T_st)
  have h1 : 1 ≤ 2 ^ S_len := Nat.one_le_two_pow
  change T_ok + (T_to + (T_st + (2 ^ S_len + 1) * (T_st + _))) ≤ (2 ^ S_len + 1) * (P + R_branch)
  nlinarith

/-- **Subexponential real-exponent constant absorption across families (§5.5, p. 39)**: absorbs
bounded-`n` fallback regimes into `O((|encI x| + 1) ^ e * ⌈(2 : ℝ) ^ E x⌉₊)` time and poly space. -/
theorem exists_real_exp_bound_countSparsePolySystem {ι : Type} {encI : ι ↪ List Bool}
    {mk : ι → SparseSystemInput} (N₀_top N₀_branch N_lim : ℕ)
    (cBranch : NativeCertificate branchEval encBranchEvalInput encNat)
    (hbound : ∀ n' eqs', checkBranchFeasible N₀_branch (n', eqs') = true →
      branchEval (prepareBranchEvalInput (n', eqs')) ≤ 2 ^ n')
    (hs : PolyBounded (fun y => (encBranchEvalInput y).length) cBranch.space)
    (hmk : ComputableInPolyTime mk encI encSparseSystemInput)
    {E : ι → ℝ} {C_f d_f : ℕ} (hE : ∀ x, 0 ≤ E x)
    (hthresh : ∀ x, checkTopFeasible N₀_top (mk x) = false → (mk x).1 < N_lim)
    (ht_fast : ∀ x, checkTopFeasible N₀_top (mk x) = true →
      (((guardedBranchingCertificate N₀_branch cBranch hbound).comp
        (NativeCertificate.ofPolyTime computableInPolyTime_toBranchInput)).time (mk x) : ℝ) ≤
        (C_f : ℝ) * ((encI x).length + 1 : ℝ) ^ d_f * (2 : ℝ) ^ E x) :
    ∃ e : ℕ, ∃ S : ι → ℕ, PolyBounded (fun x => (encI x).length) S ∧
      ComputableInO (fun x => countSparsePolySystem N₀_top N₀_branch branchEval (mk x))
        encI encNat (fun x => ((encI x).length + 1) ^ e * ⌈(2 : ℝ) ^ E x⌉₊) S := by
  let cMk := NativeCertificate.ofPolyTime hmk
  have hcMk := NativeCertificate.ofPolyTime_isPolynomial hmk
  let cFast0 := (guardedBranchingCertificate N₀_branch cBranch hbound).comp
    (NativeCertificate.ofPolyTime computableInPolyTime_toBranchInput)
  let cFast := cFast0.comp cMk
  let cEx := (ExhaustiveCountFallback.countSystemExhaustiveCertificate.comp
    (NativeCertificate.ofPolyTime computableInPolyTime_exhaustProj)).comp cMk
  have hok := (computableInPolyTime_checkTopFeasible N₀_top).comp hmk
  have hto := NativeCertificate.ofPolyTime_isPolynomial computableInPolyTime_toBranchInput
  have hs_fast : PolyBounded (fun x => (encI x).length) cFast.space :=
    hcMk.2.add ((hto.2.add ((HeavyBranchFold.polyBounded_branchWorkspace
      (polyBounded_maxReducedCost_space N₀_branch cBranch hs)).comp
      computableInPolyTime_toBranchInput.polyBounded_length)).comp hmk.polyBounded_length)
  have hpr := NativeCertificate.ofPolyTime_isPolynomial computableInPolyTime_exhaustProj
  have hs_ex : PolyBounded (fun x => (encI x).length) cEx.space :=
    hcMk.2.add ((hpr.2.add (ExhaustiveCountFallback.polyBounded_countSystemExhaustive_space.comp
      computableInPolyTime_exhaustProj.polyBounded_length)).comp hmk.polyBounded_length)
  obtain ⟨P_ex, Q_ex, hP0, hQ0, ht_ex0⟩ :=
    ExhaustiveCountFallback.exists_countSystemExhaustive_time_le
  have hproj_len := computableInPolyTime_exhaustProj.polyBounded_length.comp hmk.polyBounded_length
  have hQ : PolyBounded (fun x => (encI x).length)
      (fun x => cMk.time x + (NativeCertificate.ofPolyTime computableInPolyTime_exhaustProj).time
        (mk x) + Q_ex ((mk x).1, (mk x).2.2)) :=
    (hcMk.1.add (hpr.1.comp hmk.polyBounded_length)).add (hQ0.comp hproj_len)
  obtain ⟨cm, dm, hcm⟩ := hcMk.1.exists_le
  have ht_fast' (x : ι) (hx : checkTopFeasible N₀_top (mk x) = true) :
      (cFast.time x : ℝ) ≤
        ((C_f + cm : ℕ) : ℝ) * ((encI x).length + 1 : ℝ) ^ (d_f + dm) * (2 : ℝ) ^ E x := by
    have hm1 : (cMk.time x : ℝ) ≤ (cm : ℝ) * ((encI x).length + 1 : ℝ) ^ (d_f + dm) := by
      exact_mod_cast (hcm x).trans (Nat.mul_le_mul_left cm
        (Nat.pow_le_pow_right (Nat.succ_pos _) (Nat.le_add_left dm d_f)))
    have hp2 : ((encI x).length + 1 : ℝ) ^ d_f ≤ ((encI x).length + 1 : ℝ) ^ (d_f + dm) := by
      exact_mod_cast Nat.pow_le_pow_right (Nat.succ_pos _) (Nat.le_add_right d_f dm)
    have htwo : (1 : ℝ) ≤ (2 : ℝ) ^ E x := Real.one_le_rpow (by norm_num) (hE x)
    have hm_exp : (cMk.time x : ℝ) ≤
        (cm : ℝ) * ((encI x).length + 1 : ℝ) ^ (d_f + dm) * (2 : ℝ) ^ E x :=
      (hm1.trans_eq (mul_one _).symm).trans (mul_le_mul_of_nonneg_left htwo (by positivity))
    have hf_exp := (ht_fast x hx).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hp2 (Nat.cast_nonneg C_f)) (by positivity))
    have htime : cFast.time x = cMk.time x + cFast0.time (mk x) := rfl
    rw [htime]; push_cast; linarith
  obtain ⟨_, e, S, hS, _, hcomp⟩ :=
    ExhaustiveCountFallback.exists_real_exp_bound_of_guarded_fallback hok cFast cEx
      (f := fun x => countSparsePolySystem N₀_top N₀_branch branchEval (mk x))
      (fun x hx => by
        simp only [Function.comp_apply] at hx; simp only [countSparsePolySystem, hx, ↓reduceIte]
        rfl)
      (fun x hx => by
        simp only [Function.comp_apply] at hx
        simp only [countSparsePolySystem, hx, Bool.false_eq_true, ↓reduceIte]; rfl)
      hs_fast hs_ex hthresh (hP0.comp hproj_len) hQ hE ht_fast'
      (fun x _ => by
        have ht := ht_ex0 ((mk x).1, (mk x).2.2); dsimp only at ht
        change cMk.time x + ((NativeCertificate.ofPolyTime computableInPolyTime_exhaustProj).time
          (mk x) + ExhaustiveCountFallback.countSystemExhaustiveCertificate.time
            ((mk x).1, (mk x).2.2)) ≤ _; omega)
  exact ⟨e, S, hS, hcomp⟩

end ResourceCertificates

/-! ### 6. Context-Carrying §6.3 Parity-System Wrapper (`countContextParity`) -/

section ContextWrapper

variable {C : Type} {encC : C ↪ List Bool} {nOf sDivOf b₀Of : C → ℕ} {φOf : C → Logic.PL.CNF ℕ}
variable {branchEval : BranchEvalInput → ℕ}

/-- `compileContextParityInput` is computable in polynomial time from poly-time projections. -/
theorem computableInPolyTime_compileContextParityInput (k_deg : ℕ)
    (hn : ComputableInPolyTime nOf encC encUnary) (hs : ComputableInPolyTime sDivOf encC encNat)
    (hb : ComputableInPolyTime b₀Of encC encNat) (hφ : ComputableInPolyTime φOf encC encCNF) :
    ComputableInPolyTime (compileContextParityInput k_deg nOf sDivOf b₀Of φOf)
      (encPair encC (encList encBits)) encSparseSystemInput := by
  unfold compileContextParityInput encSparseSystemInput
  have hctx := ComputableInPolyTime.fst encC (encList encBits)
  have hrows := ComputableInPolyTime.snd encC (encList encBits)
  have hk : ComputableInPolyTime (fun _ : C × List (List Bool) => k_deg)
      (encPair encC (encList encBits)) encUnary :=
    ComputableInPolyTime.const k_deg
  have hsys := (computableInPolyTime_compileParitySystemBounded k_deg (encRow := encBits)).comp
    ((hφ.comp hctx).prod hrows)
  exact (hn.comp hctx).prod ((hk.prod ((hs.comp hctx).prod (hb.comp hctx))).prod hsys)

/-- **Uniform `NativeCertificate` for `countContextParity`** matching `GreedyContext` (§6.3). -/
noncomputable def contextParityCertificate (N₀_top N₀_branch k_deg : ℕ)
    (hn : ComputableInPolyTime nOf encC encUnary) (hs : ComputableInPolyTime sDivOf encC encNat)
    (hb : ComputableInPolyTime b₀Of encC encNat) (hφ : ComputableInPolyTime φOf encC encCNF)
    (cBranch : NativeCertificate branchEval encBranchEvalInput encNat)
    (hbound : ∀ n' eqs', checkBranchFeasible N₀_branch (n', eqs') = true →
      branchEval (prepareBranchEvalInput (n', eqs')) ≤ 2 ^ n') :
    NativeCertificate (countContextParity N₀_top N₀_branch k_deg nOf sDivOf b₀Of φOf branchEval)
      (encPair encC (encList encBits)) encNat :=
  (sparsePolyCounterCertificate N₀_top N₀_branch cBranch hbound).comp
    (NativeCertificate.ofPolyTime
      (computableInPolyTime_compileContextParityInput k_deg hn hs hb hφ))

/-- Polynomial workspace preservation for `contextParityCertificate` (§6.3). -/
theorem polyBounded_contextParityCertificate_space (N₀_top N₀_branch k_deg : ℕ)
    (hn : ComputableInPolyTime nOf encC encUnary) (hs : ComputableInPolyTime sDivOf encC encNat)
    (hb : ComputableInPolyTime b₀Of encC encNat) (hφ : ComputableInPolyTime φOf encC encCNF)
    (cBranch : NativeCertificate branchEval encBranchEvalInput encNat)
    (hbound : ∀ n' eqs', checkBranchFeasible N₀_branch (n', eqs') = true →
      branchEval (prepareBranchEvalInput (n', eqs')) ≤ 2 ^ n')
    (hs_br : PolyBounded (fun x => (encBranchEvalInput x).length) cBranch.space) :
    PolyBounded (fun p => (encPair encC (encList encBits) p).length)
      (contextParityCertificate N₀_top N₀_branch k_deg hn hs hb hφ cBranch hbound).space := by
  have hcomp := computableInPolyTime_compileContextParityInput k_deg hn hs hb hφ
  have hc := NativeCertificate.ofPolyTime_isPolynomial hcomp
  exact hc.2.add ((polyBounded_sparsePolyCounterCertificate_space N₀_top N₀_branch cBranch
    hbound hs_br).comp hcomp.polyBounded_length)

/-- **Exact agreement with `numPassing` (§6.3, Lemma 6.2)** on `Fin (nOf ctx)`. -/
theorem countContextParity_eq_numPassing {N₀_top N₀_branch k_deg : ℕ}
    (hbranch : ∀ n' eqs', checkBranchFeasible N₀_branch (n', eqs') = true →
      branchEval (prepareBranchEvalInput (n', eqs')) = HeavyBranchFold.rootCount n' eqs')
    (ctx : C) (φFin : Logic.PL.CNF (Fin (nOf ctx))) (rows : List (List Bool))
    (hφ_eq : φOf ctx = φFin.map (List.map fun l => ((l.1 : ℕ), l.2)))
    (hk : ∀ c ∈ φFin, c.length ≤ k_deg) :
    countContextParity N₀_top N₀_branch k_deg nOf sDivOf b₀Of φOf branchEval (ctx, rows) =
      numPassing φFin.violations (rows.map (ofList φFin.length)) := by
  have hk_nat : ∀ c ∈ φOf ctx, c.length ≤ k_deg := by
    rw [hφ_eq]; intro c hc
    obtain ⟨c₀, hc₀, rfl⟩ := List.mem_map.mp hc; simpa only [List.length_map] using hk c₀ hc₀
  have hlen : (φOf ctx).length = φFin.length := by rw [hφ_eq, List.length_map]
  rw [countContextParity, countSparsePolySystem_eq_rootCount hbranch]
  dsimp only [compileContextParityInput]
  rw [compileParitySystemBounded_eq_compileParitySystem hk_nat, HeavyBranchFold.rootCount,
    numPassing]
  congr 1; ext σ; simp only [mem_filter, mem_univ, true_and]
  rw [evalSystem_compileParitySystem_iff_passesTests]
  change PassesTests (φOf ctx).violations (rows.map (ofList (φOf ctx).length))
      (HeavyBranchFold.extendAssignment σ) ↔
    PassesTests φFin.violations (rows.map (ofList φFin.length)) σ
  simp only [PassesTests, List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  have hdot (r : List Bool) :
      ofList (φOf ctx).length r ⬝ᵥ (φOf ctx).violations (HeavyBranchFold.extendAssignment σ) =
        ofList φFin.length r ⬝ᵥ φFin.violations σ := by
    unfold dotProduct; rw [← (finCongr hlen.symm).sum_comp]; refine sum_congr rfl fun e _ => ?_
    simp only [finCongr_apply, ofList, Fin.val_cast, Logic.PL.CNF.violations]; congr 2
    have hget : (φOf ctx).get (e.cast hlen.symm) =
        (φFin.get e).map (fun l => ((l.1 : ℕ), l.2)) := by
      simp only [List.get_eq_getElem, Fin.val_cast, hφ_eq, List.getElem_map]
    rw [hget]; simp only [Logic.PL.Clause.eval, List.any_map]
    exact List.any_congr rfl fun l => by
      simp only [Function.comp_apply, Logic.PL.Literal.eval, HeavyBranchFold.extendAssignment_coe]
  exact forall_congr' fun r => imp_congr_right fun _ => by rw [hdot r]

end ContextWrapper

end
end Cslib.Complexity.SubexponentialSAT.SparsePolyCounter
