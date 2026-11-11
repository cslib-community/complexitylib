/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.FineGrained.Randomized
public import CslibFrontier.Computability.Complexity.FineGrained.ExhaustiveSearch
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
public import CslibFrontier.Computability.PCP.Approximation.MaxThreeSAT
import CslibFrontier.Computability.Complexity.FineGrained.BruteForce
import CslibFrontier.Computability.Complexity.Problems.SAT.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Foundations.Analysis.SublinearEnvelope
import CslibFrontier.Logics.Propositional.CNF.PolyTime

/-!
# Gap `k`-SAT exponents and the Gap Exponential Time Hypotheses

This module formalizes fixed-width gap satisfiability `GapKSAT`, its deterministic and bounded-error
randomized exponential-time rates `gapSatExponent` and `rGapSatExponent`, and the deterministic and
randomized **Gap Exponential Time Hypotheses** (`GapETH`, `rGapETH`) [Dinur2016],
[ManurangsiRaghavendra2017], [ImpagliazzoPaturi2001]:

1. **Gap specification (`GapKSATSpec`, `GapKSAT`).** A parameter record `P : GapKSATSpec` packages a
   clause width `P.width`, a completeness threshold `P.completeness`, and a soundness threshold
   `P.soundness` satisfying `0 ≤ P.soundness < P.completeness ≤ 1`. `GapKSAT P` restricts
   `PromiseProblem.gapMax (fun φ => 1 - φ.unsatVal)` to formulas of clause length at most `P.width`,
   specializing definitionally at `(3, 1, s)` (`GapKSATSpec.perfectThree`) to `GapThreeSAT s` from
   `CslibFrontier.Computability.PCP.Approximation.MaxThreeSAT`.
2. **Threshold MAX-`k`-SAT and rational-midpoint reduction (`MaxKSATThreshold`).** Choosing a
   strictly separating rational `num / den ∈ (P.soundness, P.completeness)` reduces `GapKSAT P` in
   polynomial time with zero variable blowup to `ofSet (MaxKSATThreshold P.width)`, even when
   `P.completeness < 1` or the thresholds are irrational. Exhaustive search over `2 ^ n` numbered
   assignments decides `MaxKSATThreshold k` in time `2 ^ n * poly(L)`, giving `0 ≤ rGapSatExponent P
   ≤ gapSatExponent P ≤ 1` for every `P : GapKSATSpec`.
3. **Hypothesis hierarchy.** On perfect-completeness specs `GapKSATSpec.perfect k s`, any exact
   `k`-SAT solver solves the gap problem, yielding the positive implications
   `rGapETH → GapETH → ETH` and `rGapETH → rETH → ETH`, together with threshold invariance of
   `rGapETH` across `(0, 1 / 2)`.

## Main definitions

* `Cslib.Complexity.GapKSATSpec`, `Cslib.Complexity.GapKSATSpec.perfect`,
  `Cslib.Complexity.GapKSATSpec.perfectThree`: gap `k`-SAT parameter specifications.
* `Cslib.Complexity.GapKSAT`: promise problem distinguishing `≤ k`-CNFs of value `≥ c` from `≤ s`.
* `Cslib.Complexity.MaxSATThresholdInput`, `Cslib.Complexity.encMaxSATThresholdInput`,
  `Cslib.Complexity.MaxKSATThreshold`: unary-cutoff threshold MAX-`k`-SAT decision language.
* `Cslib.Complexity.gapSatExponent`, `Cslib.Complexity.rGapSatExponent`: deterministic and
  bounded-error randomized exponential-time infimum exponents for `GapKSAT P`.
* `Cslib.Complexity.GapETH`, `Cslib.Complexity.rGapETH`: deterministic and randomized Gap-ETH.

## Main results

* `Cslib.Complexity.GapKSAT_zero_mem_PromiseP`: width-`0` `GapKSAT P` lies in `PromiseP` for all
  `0 ≤ s < c ≤ 1`.
* `Cslib.Complexity.MaxKSATThreshold_decidableInExpTime_one`,
  `Cslib.Complexity.exists_reduction_GapKSAT_to_MaxKSATThreshold`,
  `Cslib.Complexity.GapKSAT_solvesPromiseInExpTime_one`: `2 ^ n * poly(L)` solving for every
  `P : GapKSATSpec`.
* `Cslib.Complexity.gapSatExponent_mono`, `Cslib.Complexity.rGapSatExponent_mono`,
  `Cslib.Complexity.rGapSatExponent_le_gapSatExponent`, `Cslib.Complexity.gapSatExponent_le_one`,
  `Cslib.Complexity.gapSatExponent_perfect_le_satExponent`,
  `Cslib.Complexity.rGapSatExponent_perfect_le_rSatExponent`: monotonicity and rate inequalities.
* `Cslib.Complexity.rGapETH.gapETH`, `Cslib.Complexity.rGapETH.rETH`,
  `Cslib.Complexity.GapETH.eth`: positive conditional implications `rGapETH → GapETH → ETH` and
  `rGapETH → rETH`.

## References

* [I. Dinur, *Mildly exponential reduction from gap 3SAT to polynomial-gap label-cover*][Dinur2016]
* [P. Manurangsi, P. Raghavendra, *A birthday repetition theorem and complexity of approximating
  dense CSPs*][ManurangsiRaghavendra2017]
* [R. Impagliazzo, R. Paturi, *On the complexity of k-SAT*][ImpagliazzoPaturi2001]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Chapter 11][AroraBarak09]
-/

public section

namespace Cslib.Complexity

open Cslib.Logic.PL Cslib.Complexity.PromiseProblem Filter Topology Turing.MultiTapeTM

/-! ### 1. Gap `k`-SAT parameter specifications and promise problems -/

/-- Parameters `(k, c, s)` for fixed-width gap satisfiability `GapKSAT`: clause width bound `width`,
completeness threshold `completeness`, and soundness threshold `soundness`, with
`0 ≤ soundness < completeness ≤ 1`. -/
structure GapKSATSpec where
  /-- Maximum allowed clause length (`k`). -/
  width : ℕ
  /-- Minimum satisfied clause proportion on yes-instances (`c`). -/
  completeness : ℝ
  /-- Maximum satisfied clause proportion on no-instances (`s`). -/
  soundness : ℝ
  /-- Soundness is nonnegative. -/
  soundness_nonneg : 0 ≤ soundness
  /-- Soundness is strictly below completeness (`s < c`). -/
  soundness_lt_completeness : soundness < completeness
  /-- Completeness is at most `1`. -/
  completeness_le_one : completeness ≤ 1

namespace GapKSATSpec

/-- Positive additive gap `completeness - soundness`. -/
@[expose] def gap (P : GapKSATSpec) : ℝ := P.completeness - P.soundness

theorem gap_pos (P : GapKSATSpec) : 0 < P.gap :=
  sub_pos.mpr P.soundness_lt_completeness

theorem soundness_lt_one (P : GapKSATSpec) : P.soundness < 1 :=
  P.soundness_lt_completeness.trans_le P.completeness_le_one

theorem completeness_pos (P : GapKSATSpec) : 0 < P.completeness :=
  P.soundness_nonneg.trans_lt P.soundness_lt_completeness

/-- Perfect-completeness gap `k`-SAT specification `(k, 1, s)` for `0 ≤ s < 1`. -/
@[expose] def perfect (k : ℕ) (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s < 1) : GapKSATSpec where
  width := k
  completeness := 1
  soundness := s
  soundness_nonneg := hs0
  soundness_lt_completeness := hs1
  completeness_le_one := le_rfl

/-- Perfect-completeness gap 3-SAT specification `(3, 1, s)` for `0 ≤ s < 1`. -/
abbrev perfectThree (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s < 1) : GapKSATSpec :=
  perfect 3 s hs0 hs1

end GapKSATSpec

/-- **Gap `k`-SAT (`GapKSAT P`)**: distinguish formulas of clause length at most `P.width` in which
some assignment satisfies at least `P.completeness` of the clauses (`1 - φ.unsatVal ≥
P.completeness`) from those in which every assignment satisfies at most `P.soundness` of the
clauses (`1 - φ.unsatVal ≤ P.soundness`). -/
@[expose] noncomputable def GapKSAT (P : GapKSATSpec) : PromiseProblem (CNF ℕ) :=
  (PromiseProblem.gapMax (fun φ => 1 - φ.unsatVal)
    (fun _ => P.completeness) (fun _ => P.soundness)).restrict
    {φ | ∀ c ∈ φ, c.length ≤ P.width}

/-- At `(3, 1, s)`, `GapKSAT` is definitionally `GapThreeSAT s`. -/
@[simp] theorem GapKSAT_perfectThree_eq_GapThreeSAT (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s < 1) :
    GapKSAT (GapKSATSpec.perfectThree s hs0 hs1) = GapThreeSAT s := rfl

/-- Yes-instances of `GapKSAT P` are `≤ P.width`-CNFs with `φ.unsatVal ≤ 1 - P.completeness`. -/
theorem mem_yes_GapKSAT {P : GapKSATSpec} {φ : CNF ℕ} :
    φ ∈ (GapKSAT P).yes ↔ (∀ c ∈ φ, c.length ≤ P.width) ∧ φ.unsatVal ≤ 1 - P.completeness := by
  rw [GapKSAT, PromiseProblem.yes_restrict, Set.mem_inter_iff, PromiseProblem.mem_yes_gapMax]
  change (P.completeness ≤ 1 - φ.unsatVal) ∧ (∀ c ∈ φ, c.length ≤ P.width) ↔ _
  constructor <;> rintro ⟨h1, h2⟩
  · exact ⟨h2, by linarith⟩
  · exact ⟨by linarith, h1⟩

/-- No-instances of `GapKSAT P` are `≤ P.width`-CNFs with `1 - P.soundness ≤ φ.unsatVal`. -/
theorem mem_no_GapKSAT {P : GapKSATSpec} {φ : CNF ℕ} :
    φ ∈ (GapKSAT P).no ↔ (∀ c ∈ φ, c.length ≤ P.width) ∧ 1 - P.soundness ≤ φ.unsatVal := by
  rw [GapKSAT, PromiseProblem.no_restrict, Set.mem_inter_iff,
    PromiseProblem.mem_no_gapMax_of_lt (c := fun _ => P.completeness) (s := fun _ => P.soundness)
      P.soundness_lt_completeness]
  change (1 - φ.unsatVal ≤ P.soundness) ∧ (∀ c ∈ φ, c.length ≤ P.width) ↔ _
  constructor <;> rintro ⟨h1, h2⟩
  · exact ⟨h2, by linarith⟩
  · exact ⟨by linarith, h1⟩

/-- At perfect completeness `1`, the yes-instances of `GapKSAT` are `KSAT k`. -/
theorem yes_GapKSAT_perfect (k : ℕ) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    (GapKSAT (GapKSATSpec.perfect k s hs0 hs1)).yes = KSAT k := by
  ext φ
  rw [mem_yes_GapKSAT]
  simp only [GapKSATSpec.perfect, sub_self, KSAT, Set.mem_ofPred_eq, ← CNF.unsatVal_eq_zero_iff]
  have hnn := φ.unsatVal_nonneg
  constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by linarith⟩

/-- At perfect completeness `1`, every no-instance of `GapKSAT` is unsatisfiable (`∉ KSAT k`). -/
theorem no_GapKSAT_perfect_subset_compl (k : ℕ) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    (GapKSAT (GapKSATSpec.perfect k s hs0 hs1)).no ⊆ (KSAT k)ᶜ := by
  intro φ hno hsat
  rw [mem_no_GapKSAT] at hno
  simp only [GapKSATSpec.perfect] at hno
  have hzero : φ.unsatVal = 0 := (CNF.unsatVal_eq_zero_iff φ).mpr hsat.2
  linarith [hno.2]

/-- Enlarging clause width (`width₁ ≤ width₂`) or narrowing the gap
(`completeness₂ ≤ completeness₁`, `soundness₁ ≤ soundness₂`) enlarges both `yes` and `no`, so
`GapKSAT P₁` reduces via `id` to `GapKSAT P₂`. -/
theorem GapKSAT_subset_of_le {P₁ P₂ : GapKSATSpec} (hw : P₁.width ≤ P₂.width)
    (hc : P₂.completeness ≤ P₁.completeness) (hs : P₁.soundness ≤ P₂.soundness) :
    (GapKSAT P₁).yes ⊆ (GapKSAT P₂).yes ∧ (GapKSAT P₁).no ⊆ (GapKSAT P₂).no := by
  constructor
  · intro φ hφ
    rw [mem_yes_GapKSAT] at hφ ⊢
    exact ⟨fun c hmem => (hφ.1 c hmem).trans hw, by linarith [hφ.2]⟩
  · intro φ hφ
    rw [mem_no_GapKSAT] at hφ ⊢
    exact ⟨fun c hmem => (hφ.1 c hmem).trans hw, by linarith [hφ.2]⟩

/-- **Width-`0` `GapKSAT` lies in `PromiseP`** for all thresholds `0 ≤ s < c ≤ 1`: a width-`0`
formula consists solely of empty clauses `[]`, so it has value `1` (`unsatVal = 0`) when empty and
value `0` (`unsatVal = 1`) when nonempty. -/
theorem GapKSAT_zero_mem_PromiseP {P : GapKSATSpec} (h0 : P.width = 0) :
    GapKSAT P ∈ PromiseP encCNF := by
  have hlen : ComputableInPolyTime (fun φ : CNF ℕ => φ.length) encCNF encUnary :=
    CNF.computableInPolyTime_length (encV := encNat) ComputableInPolyTime.id'
  have hdec : ComputableInPolyTime (fun φ : CNF ℕ => decide (φ.length = 0)) encCNF encBool := by
    have heq : (fun φ : CNF ℕ => decide (φ.length = 0)) = fun φ => φ.length == 0 := rfl
    rw [heq]
    fun_prop
  refine mem_PromiseP_iff.mpr ⟨fun φ => decide (φ.length = 0), hdec,
    fun φ hφ => ?_, fun φ hφ => ?_⟩
  · rw [mem_yes_GapKSAT, h0] at hφ
    rw [decide_eq_true_eq]
    by_contra hne
    have hpos : 0 < φ.length := Nat.pos_of_ne_zero hne
    have hall_one : 1 ≤ φ.unsatVal := by
      refine (CNF.le_unsatVal_iff φ).mpr fun σ => ?_
      have hcount : φ.countUnsat σ = φ.length := by
        refine List.countP_eq_length.mpr fun c hc => ?_
        have hc0 : c = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp (hφ.1 c hc))
        subst hc0
        rfl
      rw [hcount, div_self (Nat.cast_ne_zero.mpr hne)]
    linarith [hφ.2, P.completeness_pos]
  · rw [mem_no_GapKSAT] at hφ
    rw [decide_eq_false_iff_not]
    have hpos_val : 0 < φ.unsatVal := by linarith [hφ.2, P.soundness_lt_one]
    exact (CNF.length_pos_of_unsatVal_pos hpos_val).ne'

/-! ### 2. Threshold MAX-`k`-SAT and rational-midpoint reduction -/

/-- Input to the threshold decision version of MAX-`k`-SAT: a CNF formula paired with a unary
clause-satisfaction threshold `cutoff`. -/
structure MaxSATThresholdInput where
  /-- Input CNF formula. -/
  formula : CNF ℕ
  /-- Required minimum number of satisfied clauses (counted with multiplicity). -/
  cutoff : ℕ
  deriving Inhabited

/-- Framed encoding of `MaxSATThresholdInput` (`encCNF` formula and `encUnary` cutoff). -/
enc_structure encMaxSATThresholdInput : MaxSATThresholdInput where
  formula : encCNF, cutoff : encUnary

/-- Number of distinct occurring variables of `x.formula`. -/
@[expose] def MaxSATThresholdInput.numVars (x : MaxSATThresholdInput) : ℕ :=
  x.formula.numVars

/-- **Threshold MAX-`k`-SAT (`MaxKSATThreshold k`)**: instances `(φ, cutoff)` where every clause of
`φ` has length at most `k` and some assignment satisfies at least `cutoff` clauses
(`cutoff ≤ φ.length - φ.countUnsat σ`). -/
@[expose] def MaxKSATThreshold (k : ℕ) : Set MaxSATThresholdInput :=
  {x | (∀ c ∈ x.formula, c.length ≤ k) ∧
    ∃ σ : ℕ → Bool, x.cutoff ≤ x.formula.length - x.formula.countUnsat σ}

namespace MaxSATThresholdSearch

/-- Leaf query for exhaustive search on `MaxKSATThreshold`: formula, cached distinct variables,
unary satisfaction cutoff, and binary assignment index. -/
structure Leaf where
  /-- Input CNF formula. -/
  formula : CNF ℕ
  /-- Cached duplicate-free variable list (`formula.distinctVars`). -/
  varsList : List ℕ
  /-- Unary minimum satisfied-clause threshold. -/
  cutoff : ℕ
  /-- Binary assignment index in `0, …, 2 ^ |varsList| - 1`. -/
  index : ℕ
  deriving Inhabited

/-- Framed encoding of `MaxSATThresholdSearch.Leaf`. -/
enc_structure encLeaf : Leaf where
  formula : encCNF, varsList : (encList encNat), cutoff : encUnary, index : encNat

/-- Check whether `bitsAssignment q.varsList q.index` satisfies at least `q.cutoff` clauses. -/
@[expose] def leafAccepts (q : Leaf) : Bool :=
  decide (q.cutoff ≤ q.formula.length - q.formula.countUnsat (bitsAssignment q.varsList q.index))

open ComputableInPolyTime in
theorem computableInPolyTime_leafAccepts :
    ComputableInPolyTime leafAccepts encLeaf encBool := by
  have heq : leafAccepts = fun q : Leaf =>
      decide (q.cutoff ≤
        q.formula.length -
          q.formula.countP fun c =>
            !Clause.eval (fun v => q.index.bits.getD (q.varsList.idxOf v) false) c) := by
    funext q
    have hfun : bitsAssignment q.varsList q.index =
        fun v => q.index.bits.getD (q.varsList.idxOf v) false := by
      funext v
      exact bitsAssignment_eq_getD q.varsList q.index v
    simp only [leafAccepts, CNF.countUnsat, hfun]
  rw [heq]
  have hlen : ComputableInPolyTime (fun q : Leaf => q.formula.length) encLeaf encUnary :=
    CNF.computableInPolyTime_length (encV := encNat) (by fun_prop)
  have hcl : ComputableInPolyTime (fun p : Leaf × Clause ℕ => p.2)
      (encPair encLeaf (encClause encNat)) (encClause encNat) := snd _ _
  have hbit : ComputableInPolyTime
      (fun p : (Leaf × Clause ℕ) × ℕ =>
        p.1.1.index.bits.getD (p.1.1.varsList.idxOf p.2) false)
      (encPair (encPair encLeaf (encClause encNat)) encNat) encBool := by
    fun_prop
  have heval : ComputableInPolyTime
      (fun p : Leaf × Clause ℕ =>
        !Clause.eval (fun v => p.1.index.bits.getD (p.1.varsList.idxOf v) false) p.2)
      (encPair encLeaf (encClause encNat)) encBool :=
    bool_not.comp (Clause.computableInPolyTime_eval hcl hbit)
  have hcnt : ComputableInPolyTime
      (fun q : Leaf =>
        q.formula.countP fun c =>
          !Clause.eval (fun v => q.index.bits.getD (q.varsList.idxOf v) false) c)
      encLeaf encUnary :=
    countPWithInput (encA := encClause encNat) (by fun_prop) heval
  fun_prop

end MaxSATThresholdSearch

/-- **Threshold MAX-`k`-SAT by exhaustive search**: `MaxKSATThreshold k` is decidable within time
`2 ^ n * poly(L)` where `n = x.numVars`. -/
theorem MaxKSATThreshold_decidableInExpTime_one (k : ℕ) :
    DecidableInExpTime (MaxKSATThreshold k) encMaxSATThresholdInput
      MaxSATThresholdInput.numVars 1 := by
  let BLeaf : Set MaxSATThresholdSearch.Leaf :=
    {q | MaxSATThresholdSearch.leafAccepts q = true}
  have hB : DecidableInExpTime BLeaf MaxSATThresholdSearch.encLeaf (fun _ => 0) 0 :=
    .of_computableInPolyTime MaxSATThresholdSearch.computableInPolyTime_leafAccepts
      fun _ => Iff.rfl
  let f (p : MaxSATThresholdInput × ℕ) : MaxSATThresholdSearch.Leaf :=
    { formula := p.1.formula
      varsList := p.1.formula.distinctVars
      cutoff := p.1.cutoff
      index := p.2 }
  have hf : ComputableInPolyTime f (encPair encMaxSATThresholdInput encNat)
      MaxSATThresholdSearch.encLeaf := by
    open MaxSATThresholdSearch in
    have := SAT.computableInPolyTime_distinctVars
    dsimp only [f]
    fun_prop
  have hν : ComputableInPolyTime MaxSATThresholdInput.numVars encMaxSATThresholdInput encUnary := by
    have := SAT.computableInPolyTime_distinctVars
    have heq : MaxSATThresholdInput.numVars = fun x => x.formula.distinctVars.length := by
      funext x
      exact x.formula.length_distinctVars.symm
    rw [heq]
    fun_prop
  let Aunb : Set MaxSATThresholdInput :=
    {x | ∃ σ : ℕ → Bool, x.cutoff ≤ x.formula.length - x.formula.countUnsat σ}
  have hfA (x : MaxSATThresholdInput) :
      x ∈ Aunb ↔ ∃ r < 2 ^ x.numVars, f (x, r) ∈ BLeaf := by
    simp only [Aunb, BLeaf, Set.mem_ofPred_eq, MaxSATThresholdSearch.leafAccepts,
      decide_eq_true_eq, f, MaxSATThresholdInput.numVars]
    constructor
    · rintro ⟨σ, hσ⟩
      obtain ⟨r, hr, hrσ⟩ :=
        exists_lt_two_pow_bitsAssignment_eq (vs := x.formula.distinctVars) σ
      rw [x.formula.length_distinctVars] at hr
      refine ⟨r, hr, ?_⟩
      rw [CNF.countUnsat_congr fun v hv => hrσ v (CNF.mem_distinctVars.mpr hv)]
      exact hσ
    · rintro ⟨r, -, hr⟩
      exact ⟨bitsAssignment x.formula.distinctVars r, hr⟩
  have hAunb : DecidableInExpTime Aunb encMaxSATThresholdInput MaxSATThresholdInput.numVars 1 := by
    simpa only [Nat.cast_one, div_one, Nat.cast_zero, zero_mul, add_zero] using
      hB.of_exhaustiveSearch hf hν hfA (c := 0) (fun _ _ => Nat.zero_le _)
        (M := 1) (K := 0) (fun x => by simp) le_rfl
  have hwidth : ComputableInPolyTime
      (fun x : MaxSATThresholdInput => x.formula.all fun c => decide (c.length ≤ k))
      encMaxSATThresholdInput encBool :=
    (computableInPolyTime_all_length_le k).comp (by fun_prop)
  have hinter : MaxKSATThreshold k =
      {x : MaxSATThresholdInput |
        (x.formula.all fun c => decide (c.length ≤ k)) = true} ∩ Aunb := by
    ext x
    simp only [MaxKSATThreshold, Aunb, Set.mem_inter_iff, Set.mem_ofPred_eq, List.all_eq_true,
      decide_eq_true_eq]
  rw [hinter]
  exact hAunb.inter hwidth zero_le_one

/-- **Rational-midpoint reduction from `GapKSAT P` to `MaxKSATThreshold P.width`.**
Choosing a rational `num / den` strictly inside `(P.soundness, P.completeness)` and setting
`cutoff(φ) = ⌊num * |φ| / den⌋ + 1` (or `0` when `φ = []`) maps yes-instances into
`MaxKSATThreshold P.width` and no-instances into its complement in polynomial time, keeping the
underlying formula unchanged (`(f φ).numVars = φ.numVars`). -/
theorem exists_reduction_GapKSAT_to_MaxKSATThreshold (P : GapKSATSpec) :
    ∃ f : CNF ℕ → MaxSATThresholdInput,
      ComputableInPolyTime f encCNF encMaxSATThresholdInput ∧
      (∀ φ, (f φ).numVars = φ.numVars) ∧
      (∀ φ ∈ (GapKSAT P).yes, f φ ∈ MaxKSATThreshold P.width) ∧
      (∀ φ ∈ (GapKSAT P).no, f φ ∉ MaxKSATThreshold P.width) := by
  have hgap : 0 < P.gap := P.gap_pos
  let den : ℕ := ⌈2 / P.gap⌉₊ + 1
  have hden_pos : 0 < den := Nat.succ_pos _
  have hdenR_pos : (0 : ℝ) < den := Nat.cast_pos.mpr hden_pos
  have htwo_lt_div : 2 / P.gap < (den : ℝ) := by
    have hceil : 2 / P.gap ≤ (⌈2 / P.gap⌉₊ : ℝ) := Nat.le_ceil _
    have hlt : (⌈2 / P.gap⌉₊ : ℝ) < (den : ℝ) := by
      dsimp only [den]
      push_cast
      linarith
    exact hceil.trans_lt hlt
  have hgap_den : 2 < (den : ℝ) * P.gap := (div_lt_iff₀ hgap).mp htwo_lt_div
  let num : ℕ := ⌊P.soundness * (den : ℝ)⌋₊ + 1
  have hs_den_nn : 0 ≤ P.soundness * (den : ℝ) :=
    mul_nonneg P.soundness_nonneg hdenR_pos.le
  have hs_lt_num : P.soundness * (den : ℝ) < (num : ℝ) := by
    have hlt := Nat.lt_floor_add_one (P.soundness * (den : ℝ))
    have hnum_eq : (num : ℝ) = (⌊P.soundness * (den : ℝ)⌋₊ : ℝ) + 1 := by
      dsimp only [num]; push_cast; rfl
    linarith
  have hnum_lt_c : (num : ℝ) < P.completeness * (den : ℝ) := by
    have hfl : (⌊P.soundness * (den : ℝ)⌋₊ : ℝ) ≤ P.soundness * (den : ℝ) :=
      Nat.floor_le hs_den_nn
    have hnum_eq : (num : ℝ) = (⌊P.soundness * (den : ℝ)⌋₊ : ℝ) + 1 := by
      dsimp only [num]; push_cast; rfl
    have hgap_eq : (den : ℝ) * P.gap = P.completeness * (den : ℝ) - P.soundness * (den : ℝ) := by
      rw [GapKSATSpec.gap]; ring
    linarith
  let cutoff (m : ℕ) : ℕ := if m == 0 then 0 else (num * m) / den + 1
  let f (φ : CNF ℕ) : MaxSATThresholdInput :=
    { formula := φ, cutoff := cutoff φ.length }
  have hf_poly : ComputableInPolyTime f encCNF encMaxSATThresholdInput := by
    have hlen : ComputableInPolyTime (fun φ : CNF ℕ => φ.length) encCNF encUnary :=
      CNF.computableInPolyTime_length (encV := encNat) ComputableInPolyTime.id'
    have hcut_u : ComputableInPolyTime cutoff encUnary encUnary := by
      dsimp only [cutoff]
      fun_prop
    have hcut : ComputableInPolyTime (fun φ : CNF ℕ => cutoff φ.length) encCNF encUnary :=
      hcut_u.comp hlen
    dsimp only [f]
    fun_prop
  refine ⟨f, hf_poly, fun _ => rfl, fun φ hφ => ?_, fun φ hφ hmem => ?_⟩
  · rw [mem_yes_GapKSAT] at hφ
    refine ⟨hφ.1, ?_⟩
    dsimp only [f, cutoff]
    rcases Nat.eq_zero_or_pos φ.length with hm0 | hm_pos
    · rw [hm0]
      exact ⟨fun _ => false, Nat.zero_le _⟩
    · have hbeq : (φ.length == 0) = false := beq_eq_false_iff_ne.mpr hm_pos.ne'
      simp only [hbeq, Bool.false_eq_true, ↓reduceIte]
      obtain ⟨σ, hσ_eq⟩ := φ.exists_countUnsat_div_eq_unsatVal
      refine ⟨σ, ?_⟩
      set sat : ℕ := φ.length - φ.countUnsat σ
      have hmR : (0 : ℝ) < φ.length := Nat.cast_pos.mpr hm_pos
      have hunsat_le : (φ.countUnsat σ : ℝ) ≤ (1 - P.completeness) * (φ.length : ℝ) :=
        (div_le_iff₀ hmR).mp (hσ_eq.trans_le hφ.2)
      have hsatR : (sat : ℝ) = (φ.length : ℝ) - (φ.countUnsat σ : ℝ) :=
        Nat.cast_sub (φ.countUnsat_le_length σ)
      have hc_le_sat : P.completeness * (φ.length : ℝ) ≤ (sat : ℝ) := by linarith
      have hreal_lt : (num : ℝ) * (φ.length : ℝ) < (sat : ℝ) * (den : ℝ) := by
        have h1 : (num : ℝ) * (φ.length : ℝ) < (P.completeness * (den : ℝ)) * (φ.length : ℝ) :=
          mul_lt_mul_of_pos_right hnum_lt_c hmR
        have h2 : (P.completeness * (φ.length : ℝ)) * (den : ℝ) ≤ (sat : ℝ) * (den : ℝ) :=
          mul_le_mul_of_nonneg_right hc_le_sat hdenR_pos.le
        linarith
      have hnat_lt : num * φ.length < sat * den := by exact_mod_cast hreal_lt
      have hdiv_lt : ((num * φ.length) / den) * den < sat * den :=
        (Nat.div_mul_le_self _ _).trans_lt hnat_lt
      exact Nat.succ_le_of_lt ((Nat.mul_lt_mul_right hden_pos).mp hdiv_lt)
  · rw [mem_no_GapKSAT] at hφ
    have hpos_val : 0 < φ.unsatVal := by linarith [hφ.2, P.soundness_lt_one]
    have hm_pos : 0 < φ.length := CNF.length_pos_of_unsatVal_pos hpos_val
    obtain ⟨-, σ, hσ⟩ := hmem
    dsimp only [f, cutoff] at hσ
    have hbeq : (φ.length == 0) = false := beq_eq_false_iff_ne.mpr hm_pos.ne'
    simp only [hbeq, Bool.false_eq_true, ↓reduceIte] at hσ
    set sat : ℕ := φ.length - φ.countUnsat σ
    have hmod_eq := Nat.mod_add_div (num * φ.length) den
    have hmod_lt : (num * φ.length) % den < den := Nat.mod_lt _ hden_pos
    have hmul_le : den * ((num * φ.length) / den + 1) ≤ den * sat :=
      Nat.mul_le_mul_left den hσ
    rw [Nat.mul_succ] at hmul_le
    have hnat_lt : num * φ.length < den * sat := by omega
    have hreal_lt : (num : ℝ) * (φ.length : ℝ) < (den : ℝ) * (sat : ℝ) := by
      exact_mod_cast hnat_lt
    have hmR : (0 : ℝ) < φ.length := Nat.cast_pos.mpr hm_pos
    have hunsat_ge : (1 - P.soundness) * (φ.length : ℝ) ≤ (φ.countUnsat σ : ℝ) :=
      (le_div_iff₀ hmR).mp (hφ.2.trans (φ.unsatVal_le σ))
    have hsatR : (sat : ℝ) = (φ.length : ℝ) - (φ.countUnsat σ : ℝ) :=
      Nat.cast_sub (φ.countUnsat_le_length σ)
    have hsat_le : (sat : ℝ) ≤ P.soundness * (φ.length : ℝ) := by linarith
    have h1 : (den : ℝ) * (sat : ℝ) ≤ (P.soundness * (den : ℝ)) * (φ.length : ℝ) := by
      have hm := mul_le_mul_of_nonneg_left hsat_le hdenR_pos.le
      linarith
    have h2 : (P.soundness * (den : ℝ)) * (φ.length : ℝ) < (num : ℝ) * (φ.length : ℝ) :=
      mul_lt_mul_of_pos_right hs_lt_num hmR
    linarith

/-- Any deterministic `2 ^ (δ * n) * poly(L)` decider for `MaxKSATThreshold P.width` (`δ ≥ 0`)
transfers to `GapKSAT P`. -/
theorem SolvesPromiseInExpTime.GapKSAT_of_MaxKSATThreshold (P : GapKSATSpec) {δ : ℝ} (hδ : 0 ≤ δ)
    (h : DecidableInExpTime (MaxKSATThreshold P.width) encMaxSATThresholdInput
      MaxSATThresholdInput.numVars δ) :
    SolvesPromiseInExpTime (GapKSAT P) encCNF CNF.numVars δ := by
  obtain ⟨f, hf, hvars, hyes, hno⟩ := exists_reduction_GapKSAT_to_MaxKSATThreshold P
  have hY : SolvesPromiseInExpTime (ofSet (MaxKSATThreshold P.width)) encMaxSATThresholdInput
      MaxSATThresholdInput.numVars δ := solvesPromiseInExpTime_ofSet_iff.mpr h
  simpa only [Nat.cast_one, one_mul] using
    hY.of_promiseReduction hf hyes hno (c := 1) (fun φ => by rw [hvars]; omega) hδ

/-- Any randomized `2 ^ (δ * n) * poly(L)` solver for `MaxKSATThreshold P.width` (`δ ≥ 0`) transfers
to `GapKSAT P` under the same error profile `E`. -/
theorem SolvesWithErrorInExpTime.GapKSAT_of_MaxKSATThreshold (P : GapKSATSpec) {E : ErrorModel}
    {δ : ℝ} (hδ : 0 ≤ δ)
    (h : SolvesWithErrorInExpTime (ofSet (MaxKSATThreshold P.width)) encMaxSATThresholdInput E
      MaxSATThresholdInput.numVars δ) :
    SolvesWithErrorInExpTime (GapKSAT P) encCNF E CNF.numVars δ := by
  obtain ⟨f, hf, hvars, hyes, hno⟩ := exists_reduction_GapKSAT_to_MaxKSATThreshold P
  simpa only [Nat.cast_one, one_mul] using
    h.of_promiseReduction hf hyes hno (c := 1) (fun φ => by rw [hvars]; omega) hδ

/-- **Every `GapKSAT P` (including imperfect completeness `c < 1`) is solvable deterministically in
time `2 ^ n * poly(L)`.** -/
theorem GapKSAT_solvesPromiseInExpTime_one (P : GapKSATSpec) :
    SolvesPromiseInExpTime (GapKSAT P) encCNF CNF.numVars 1 :=
  .GapKSAT_of_MaxKSATThreshold P zero_le_one (MaxKSATThreshold_decidableInExpTime_one P.width)

/-- **Every `GapKSAT P` is solvable in randomized time `2 ^ n * poly(L)` under any error profile.**
-/
theorem GapKSAT_solvesWithErrorInExpTime_one (P : GapKSATSpec) (E : ErrorModel) :
    SolvesWithErrorInExpTime (GapKSAT P) encCNF E CNF.numVars 1 :=
  (GapKSAT_solvesPromiseInExpTime_one P).solvesWithErrorInExpTime zero_le_one E

/-! ### 3. Perfect-completeness decision-to-gap transfers -/

/-- At perfect completeness `1`, any `2 ^ (δ * n) * poly(L)` decider (`δ ≥ 0`) for `KSAT k` solves
`GapKSAT (GapKSATSpec.perfect k s hs0 hs1)`. -/
theorem SolvesPromiseInExpTime.GapKSAT_perfect_of_KSAT {k : ℕ} {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1)
    {δ : ℝ} (hδ : 0 ≤ δ) (h : DecidableInExpTime (KSAT k) encCNF CNF.numVars δ) :
    SolvesPromiseInExpTime (GapKSAT (GapKSATSpec.perfect k s hs0 hs1)) encCNF CNF.numVars δ := by
  have hY : SolvesPromiseInExpTime (ofSet (KSAT k)) encCNF CNF.numVars δ :=
    solvesPromiseInExpTime_ofSet_iff.mpr h
  simpa only [Nat.cast_one, one_mul] using
    hY.of_promiseReduction ComputableInPolyTime.id'
      (fun φ hφ => by rwa [yes_GapKSAT_perfect] at hφ)
      (fun φ hφ => no_GapKSAT_perfect_subset_compl k hs0 hs1 hφ)
      (c := 1) (fun _ => by omega) hδ

/-- At perfect completeness `1`, any randomized `2 ^ (δ * n) * poly(L)` solver (`δ ≥ 0`) for
`KSAT k` solves `GapKSAT (GapKSATSpec.perfect k s hs0 hs1)` with the same error profile `E`. -/
theorem SolvesWithErrorInExpTime.GapKSAT_perfect_of_KSAT {k : ℕ} {s : ℝ} (hs0 : 0 ≤ s)
    (hs1 : s < 1) {E : ErrorModel} {δ : ℝ} (hδ : 0 ≤ δ)
    (h : SolvesWithErrorInExpTime (ofSet (KSAT k)) encCNF E CNF.numVars δ) :
    SolvesWithErrorInExpTime (GapKSAT (GapKSATSpec.perfect k s hs0 hs1)) encCNF E
      CNF.numVars δ := by
  simpa only [Nat.cast_one, one_mul] using
    h.of_promiseReduction ComputableInPolyTime.id'
      (fun φ hφ => by rwa [yes_GapKSAT_perfect] at hφ)
      (fun φ hφ => no_GapKSAT_perfect_subset_compl k hs0 hs1 hφ)
      (c := 1) (fun _ => by omega) hδ

/-! ### 4. `gapSatExponent`, `rGapSatExponent`, `GapETH`, and `rGapETH` -/

/-- **Deterministic gap `k`-SAT exponent (`gapSatExponent P`)**: infimum of `δ ≥ 0` such that
`GapKSAT P` is deterministically solvable within time `2 ^ (δ * n) * poly(L)`. -/
@[expose] noncomputable def gapSatExponent (P : GapKSATSpec) : ℝ :=
  sInf {δ : ℝ | 0 ≤ δ ∧ SolvesPromiseInExpTime (GapKSAT P) encCNF CNF.numVars δ}

/-- **Randomized gap `k`-SAT exponent (`rGapSatExponent P`)**: infimum of `δ ≥ 0` such that
`GapKSAT P` is solvable with two-sided bounded error (`1 / 3`) within time
`2 ^ (δ * n) * poly(L)`. -/
@[expose] noncomputable def rGapSatExponent (P : GapKSATSpec) : ℝ :=
  sInf {δ : ℝ | 0 ≤ δ ∧
    SolvesWithErrorInExpTime (GapKSAT P) encCNF ErrorModel.bounded CNF.numVars δ}

/-- **Gap Exponential Time Hypothesis (`GapETH`) variant**: this adaptation posits that
for some soundness threshold `0 ≤ s < 1` and rate `δ > 0`, `GapThreeSAT s` cannot be solved
deterministically within time `2 ^ (δ * n) * poly(L)` where `n = φ.numVars`.
This definition ranges over unrestricted clause density and existential `s` with a closed
no-promise. It explicitly quantifies over `ComputableInTimeO`, using occurring variables
`numVars`, the `encCNF` encoding, a polynomial factor in encoded length `L`, and the
deterministic time model. This is an explicitly documented adaptation and does not assert
equivalence to the sparse source formulations: [Dinur2016, Hypothesis 2.5, p.5] has fixed
soundness `< 0.9` and at most `D n` clauses, and [ManurangsiRaghavendra2017, §1.1, p.78:5]
states the approximation ETHA formulation. -/
@[expose] def GapETH : Prop :=
  ∃ s : ℝ, 0 ≤ s ∧ s < 1 ∧ ∃ δ : ℝ, 0 < δ ∧
    ¬SolvesPromiseInExpTime (GapThreeSAT s) encCNF CNF.numVars δ

/-- **Randomized Gap Exponential Time Hypothesis (`rGapETH`)**: for some soundness threshold
`0 ≤ s < 1` and rate `δ > 0`, `GapThreeSAT s` cannot be solved with two-sided bounded error
(`1 / 3`) within time `2 ^ (δ * n) * poly(L)` where `n = φ.numVars`. -/
@[expose] def rGapETH : Prop :=
  ∃ s : ℝ, 0 ≤ s ∧ s < 1 ∧ ∃ δ : ℝ, 0 < δ ∧
    ¬SolvesWithErrorInExpTime (GapThreeSAT s) encCNF ErrorModel.bounded CNF.numVars δ

/-- **Threshold invariance of `rGapSatExponent`.** Any `ε ∈ (0, 1 / 2)` yields the exact same
infimum exponent `rGapSatExponent P`. -/
theorem rGapSatExponent_eq_sInf_twoSided (P : GapKSATSpec) {ε : ℝ} (h0 : 0 < ε)
    (h1 : ε < 1 / 2) :
    rGapSatExponent P = sInf {δ : ℝ | 0 ≤ δ ∧
      SolvesWithErrorInExpTime (GapKSAT P) encCNF
        (ErrorModel.twoSided ε h0.le h1) CNF.numVars δ} := by
  rw [rGapSatExponent]
  congr 1
  ext δ
  exact and_congr_right fun _ => solvesWithErrorInExpTime_twoSided_iff
    (by norm_num) (by norm_num) h0 h1

private theorem bddBelow_gapSatExponents (P : GapKSATSpec) :
    BddBelow {δ : ℝ | 0 ≤ δ ∧ SolvesPromiseInExpTime (GapKSAT P) encCNF CNF.numVars δ} :=
  ⟨0, fun _ h => h.1⟩

private theorem nonempty_gapSatExponents (P : GapKSATSpec) :
    {δ : ℝ | 0 ≤ δ ∧ SolvesPromiseInExpTime (GapKSAT P) encCNF CNF.numVars δ}.Nonempty :=
  ⟨1, zero_le_one, GapKSAT_solvesPromiseInExpTime_one P⟩

private theorem bddBelow_rGapSatExponents (P : GapKSATSpec) :
    BddBelow {δ : ℝ | 0 ≤ δ ∧
      SolvesWithErrorInExpTime (GapKSAT P) encCNF ErrorModel.bounded CNF.numVars δ} :=
  ⟨0, fun _ h => h.1⟩

private theorem nonempty_rGapSatExponents (P : GapKSATSpec) :
    {δ : ℝ | 0 ≤ δ ∧
      SolvesWithErrorInExpTime (GapKSAT P) encCNF ErrorModel.bounded CNF.numVars δ}.Nonempty :=
  ⟨1, zero_le_one, GapKSAT_solvesWithErrorInExpTime_one P ErrorModel.bounded⟩

theorem gapSatExponent_nonneg (P : GapKSATSpec) : 0 ≤ gapSatExponent P :=
  le_csInf (nonempty_gapSatExponents P) fun _ h => h.1

theorem rGapSatExponent_nonneg (P : GapKSATSpec) : 0 ≤ rGapSatExponent P :=
  le_csInf (nonempty_rGapSatExponents P) fun _ h => h.1

theorem gapSatExponent_le {P : GapKSATSpec} {δ : ℝ} (hδ : 0 ≤ δ)
    (h : SolvesPromiseInExpTime (GapKSAT P) encCNF CNF.numVars δ) :
    gapSatExponent P ≤ δ :=
  csInf_le (bddBelow_gapSatExponents P) ⟨hδ, h⟩

theorem rGapSatExponent_le {P : GapKSATSpec} {δ : ℝ} (hδ : 0 ≤ δ)
    (h : SolvesWithErrorInExpTime (GapKSAT P) encCNF ErrorModel.bounded CNF.numVars δ) :
    rGapSatExponent P ≤ δ :=
  csInf_le (bddBelow_rGapSatExponents P) ⟨hδ, h⟩

theorem gapSatExponent_le_one (P : GapKSATSpec) : gapSatExponent P ≤ 1 :=
  gapSatExponent_le zero_le_one (GapKSAT_solvesPromiseInExpTime_one P)

theorem rGapSatExponent_le_one (P : GapKSATSpec) : rGapSatExponent P ≤ 1 :=
  rGapSatExponent_le zero_le_one (GapKSAT_solvesWithErrorInExpTime_one P ErrorModel.bounded)

/-- `gapSatExponent P` equals the infimum over strictly positive rates `δ > 0`. -/
theorem gapSatExponent_eq_sInf_pos (P : GapKSATSpec) :
    gapSatExponent P =
      sInf {δ : ℝ | 0 < δ ∧ SolvesPromiseInExpTime (GapKSAT P) encCNF CNF.numVars δ} :=
  csInf_nonneg_eq_csInf_pos (fun _ _ hle h => h.mono hle) (GapKSAT_solvesPromiseInExpTime_one P)

/-- `rGapSatExponent P` equals the infimum over strictly positive rates `δ > 0`. -/
theorem rGapSatExponent_eq_sInf_pos (P : GapKSATSpec) :
    rGapSatExponent P = sInf {δ : ℝ | 0 < δ ∧
      SolvesWithErrorInExpTime (GapKSAT P) encCNF ErrorModel.bounded CNF.numVars δ} :=
  csInf_nonneg_eq_csInf_pos (fun _ _ hle h => h.mono hle)
    (GapKSAT_solvesWithErrorInExpTime_one P ErrorModel.bounded)

theorem gapSatExponent_zero_eq_zero {P : GapKSATSpec} (h0 : P.width = 0) :
    gapSatExponent P = 0 :=
  le_antisymm
    (gapSatExponent_le le_rfl (.of_mem_PromiseP (GapKSAT_zero_mem_PromiseP h0)))
    (gapSatExponent_nonneg P)

theorem not_solvesPromiseInExpTime_of_lt_gapSatExponent {P : GapKSATSpec} {δ : ℝ}
    (hδ₀ : 0 ≤ δ) (hδ : δ < gapSatExponent P) :
    ¬SolvesPromiseInExpTime (GapKSAT P) encCNF CNF.numVars δ :=
  fun h => (gapSatExponent_le hδ₀ h).not_gt hδ

theorem le_gapSatExponent_of_not_solvesPromiseInExpTime {P : GapKSATSpec} {δ : ℝ}
    (h : ¬SolvesPromiseInExpTime (GapKSAT P) encCNF CNF.numVars δ) :
    δ ≤ gapSatExponent P :=
  le_csInf (nonempty_gapSatExponents P) fun _ h' =>
    le_of_not_gt fun hlt => h (h'.2.mono hlt.le)

theorem not_solvesWithErrorInExpTime_of_lt_rGapSatExponent {P : GapKSATSpec} {δ : ℝ}
    (hδ₀ : 0 ≤ δ) (hδ : δ < rGapSatExponent P) :
    ¬SolvesWithErrorInExpTime (GapKSAT P) encCNF ErrorModel.bounded CNF.numVars δ :=
  fun h => (rGapSatExponent_le hδ₀ h).not_gt hδ

theorem le_rGapSatExponent_of_not_solvesWithErrorInExpTime {P : GapKSATSpec} {δ : ℝ}
    (h : ¬SolvesWithErrorInExpTime (GapKSAT P) encCNF ErrorModel.bounded CNF.numVars δ) :
    δ ≤ rGapSatExponent P :=
  le_csInf (nonempty_rGapSatExponents P) fun _ h' =>
    le_of_not_gt fun hlt => h (h'.2.mono hlt.le)

/-- **Randomized vs. deterministic gap exponents (`rGapSatExponent P ≤ gapSatExponent P`).** -/
theorem rGapSatExponent_le_gapSatExponent (P : GapKSATSpec) :
    rGapSatExponent P ≤ gapSatExponent P :=
  le_csInf (nonempty_gapSatExponents P) fun _ ⟨hδ, h⟩ =>
    rGapSatExponent_le hδ (h.solvesWithErrorInExpTime hδ ErrorModel.bounded)

/-- **Parameter monotonicity of `gapSatExponent`**: increasing clause width (`width₁ ≤ width₂`) or
narrowing the gap (`completeness₂ ≤ completeness₁`, `soundness₁ ≤ soundness₂`) cannot decrease
`gapSatExponent`. -/
theorem gapSatExponent_mono {P₁ P₂ : GapKSATSpec} (hw : P₁.width ≤ P₂.width)
    (hc : P₂.completeness ≤ P₁.completeness) (hs : P₁.soundness ≤ P₂.soundness) :
    gapSatExponent P₁ ≤ gapSatExponent P₂ := by
  obtain ⟨hyes, hno⟩ := GapKSAT_subset_of_le hw hc hs
  refine le_csInf (nonempty_gapSatExponents P₂) fun δ ⟨hδ, h⟩ => gapSatExponent_le hδ ?_
  simpa only [Nat.cast_one, one_mul] using
    h.of_promiseReduction ComputableInPolyTime.id' (fun _ hφ => hyes hφ) (fun _ hφ => hno hφ)
      (c := 1) (fun _ => by omega) hδ

/-- **Parameter monotonicity of `rGapSatExponent`.** -/
theorem rGapSatExponent_mono {P₁ P₂ : GapKSATSpec} (hw : P₁.width ≤ P₂.width)
    (hc : P₂.completeness ≤ P₁.completeness) (hs : P₁.soundness ≤ P₂.soundness) :
    rGapSatExponent P₁ ≤ rGapSatExponent P₂ := by
  obtain ⟨hyes, hno⟩ := GapKSAT_subset_of_le hw hc hs
  refine le_csInf (nonempty_rGapSatExponents P₂) fun δ ⟨hδ, h⟩ => rGapSatExponent_le hδ ?_
  simpa only [Nat.cast_one, one_mul] using
    h.of_promiseReduction ComputableInPolyTime.id' (fun _ hφ => hyes hφ) (fun _ hφ => hno hφ)
      (c := 1) (fun _ => by omega) hδ

/-- At perfect completeness `1`, `gapSatExponent` is bounded above by `satExponent k`. -/
theorem gapSatExponent_perfect_le_satExponent (k : ℕ) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    gapSatExponent (GapKSATSpec.perfect k s hs0 hs1) ≤ satExponent k :=
  le_csInf ⟨1, zero_le_one, KSAT_decidableInExpTime_one k⟩ fun _ ⟨hδ, h⟩ =>
    gapSatExponent_le hδ (.GapKSAT_perfect_of_KSAT hs0 hs1 hδ h)

/-- At perfect completeness `1`, `rGapSatExponent` is bounded above by `rSatExponent k`. -/
theorem rGapSatExponent_perfect_le_rSatExponent (k : ℕ) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    rGapSatExponent (GapKSATSpec.perfect k s hs0 hs1) ≤ rSatExponent k :=
  le_csInf
    ⟨1, zero_le_one,
      (solvesPromiseInExpTime_ofSet_iff.mpr
        (KSAT_decidableInExpTime_one k)).solvesWithErrorInExpTime zero_le_one ErrorModel.bounded⟩
    fun _ ⟨hδ, h⟩ => rGapSatExponent_le hδ (.GapKSAT_perfect_of_KSAT hs0 hs1 hδ h)

/-! ### 5. Characterizations and conditional hierarchy for `GapETH` and `rGapETH` -/

theorem GapETH_iff_not_forall_solvesPromiseInSubexpTime :
    GapETH ↔
      ¬∀ s : ℝ, 0 ≤ s → s < 1 → SolvesPromiseInSubexpTime (GapThreeSAT s) encCNF CNF.numVars := by
  simp only [GapETH, SolvesPromiseInSubexpTime, not_forall, exists_prop]

theorem rGapETH_iff_not_forall_solvesWithErrorInSubexpTime :
    rGapETH ↔
      ¬∀ s : ℝ, 0 ≤ s → s < 1 →
        SolvesWithErrorInSubexpTime (GapThreeSAT s) encCNF ErrorModel.bounded CNF.numVars := by
  simp only [rGapETH, SolvesWithErrorInSubexpTime, not_forall, exists_prop]

/-- `GapETH` holds iff `gapSatExponent (GapKSATSpec.perfectThree s hs0 hs1) > 0` for some
`0 ≤ s < 1`. -/
theorem GapETH_iff_exists_gapSatExponent_pos :
    GapETH ↔
      ∃ (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s < 1),
        0 < gapSatExponent (GapKSATSpec.perfectThree s hs0 hs1) := by
  constructor
  · rintro ⟨s, hs0, hs1, δ, hδ, hnot⟩
    refine ⟨s, hs0, hs1, hδ.trans_le ?_⟩
    exact le_gapSatExponent_of_not_solvesPromiseInExpTime hnot
  · rintro ⟨s, hs0, hs1, hpos⟩
    refine ⟨s, hs0, hs1, gapSatExponent (GapKSATSpec.perfectThree s hs0 hs1) / 2,
      half_pos hpos, ?_⟩
    exact not_solvesPromiseInExpTime_of_lt_gapSatExponent
      (half_pos hpos).le (half_lt_self hpos)

/-- `rGapETH` holds iff `rGapSatExponent (GapKSATSpec.perfectThree s hs0 hs1) > 0` for some
`0 ≤ s < 1`. -/
theorem rGapETH_iff_exists_rGapSatExponent_pos :
    rGapETH ↔
      ∃ (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s < 1),
        0 < rGapSatExponent (GapKSATSpec.perfectThree s hs0 hs1) := by
  constructor
  · rintro ⟨s, hs0, hs1, δ, hδ, hnot⟩
    refine ⟨s, hs0, hs1, hδ.trans_le ?_⟩
    exact le_rGapSatExponent_of_not_solvesWithErrorInExpTime hnot
  · rintro ⟨s, hs0, hs1, hpos⟩
    refine ⟨s, hs0, hs1, rGapSatExponent (GapKSATSpec.perfectThree s hs0 hs1) / 2,
      half_pos hpos, ?_⟩
    exact not_solvesWithErrorInExpTime_of_lt_rGapSatExponent
      (half_pos hpos).le (half_lt_self hpos)

/-- **Threshold invariance of `rGapETH`.** Replacing `ErrorModel.bounded` (`1 / 3`) by any two-sided
error `ε ∈ (0, 1 / 2)` gives an equivalent hypothesis. -/
theorem rGapETH_iff_twoSided {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1 / 2) :
    rGapETH ↔ ∃ s : ℝ, 0 ≤ s ∧ s < 1 ∧ ∃ δ : ℝ, 0 < δ ∧
      ¬SolvesWithErrorInExpTime (GapThreeSAT s) encCNF
        (ErrorModel.twoSided ε h0.le h1) CNF.numVars δ := by
  simp only [rGapETH]
  refine exists_congr fun s => and_congr_right fun _ => and_congr_right fun _ =>
    exists_congr fun δ => and_congr_right fun _ => not_congr ?_
  exact solvesWithErrorInExpTime_twoSided_iff (by norm_num) (by norm_num) h0 h1

/-- **`rGapETH` implies `GapETH`** (`rGapETH → GapETH`). -/
theorem rGapETH.gapETH (h : rGapETH) : GapETH := by
  obtain ⟨s, hs0, hs1, hpos⟩ := rGapETH_iff_exists_rGapSatExponent_pos.mp h
  exact GapETH_iff_exists_gapSatExponent_pos.mpr
    ⟨s, hs0, hs1, hpos.trans_le (rGapSatExponent_le_gapSatExponent _)⟩

/-- **`rGapETH` implies `rETH`** (`rGapETH → rETH`). -/
theorem rGapETH.rETH (h : rGapETH) : rETH := by
  obtain ⟨s, hs0, hs1, hpos⟩ := rGapETH_iff_exists_rGapSatExponent_pos.mp h
  exact rETH_iff_rSatExponent_pos.mpr
    (hpos.trans_le (rGapSatExponent_perfect_le_rSatExponent 3 hs0 hs1))

/-- **`GapETH` implies `ETH`** (`GapETH → ETH`). -/
theorem GapETH.eth (h : GapETH) : ETH := by
  obtain ⟨s, hs0, hs1, hpos⟩ := GapETH_iff_exists_gapSatExponent_pos.mp h
  exact ETH_iff_satExponent_pos.mpr
    (hpos.trans_le (gapSatExponent_perfect_le_satExponent 3 hs0 hs1))

end Cslib.Complexity
