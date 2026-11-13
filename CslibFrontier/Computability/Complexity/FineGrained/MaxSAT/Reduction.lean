/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.BinarySearch
public import CslibFrontier.Computability.Complexity.FineGrained.MaxSAT.Histogram
public import CslibFrontier.Computability.Complexity.FineGrained.Reduction
public import CslibFrontier.Computability.Complexity.Reduction
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
public import CslibFrontier.Logics.Propositional.CSP.MaxCSPSampling
import CslibFrontier.Computability.Circuit.FanIn
import CslibFrontier.Computability.Complexity.FineGrained.BruteForce
import CslibFrontier.Computability.Complexity.FineGrained.CircuitCounting
import CslibFrontier.Computability.Complexity.Problems.SAT.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.Cases
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Length
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.NatPower
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.OCountedIteration
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.ToReal
import CslibFrontier.Probability.PMF.Uniform

/-!
# MAX-SAT / Max-CSP structures, subsampling specializations, and fixed-width SAT solver reductions

This module connects `MaxSAT` (`MaxSAT.thresholdCircuit`, `MaxSAT.optimum`) and general `Max-CSP`
(`MaxCSPInstance`, `MaxCSPSampling`) to supplied fixed-width `k`-SAT solvers (`3 ≤ k`):

1. **Structured encodings (`StructInstance`, `ThresholdQuery`, `encMaxCSPInstance`):**
   `#4391`-compliant documented structures with `enc_structure` (and a parameterized field-tuple
   embedding for `MaxCSPInstance Rel ℕ`), bridging directly to
   `MaxSAT.Instance`, `MaxCSPInstance.ofCNF`, and the `2 ^ (n + 1) * exp (-2 * s * δ ^ 2)`
   (and `1 - η` sample-size) subsampling concentration and `2 * δ * m` optimality-loss theorems.
2. **Threshold compilation (`thresholdToCNF`):** compiles a `ThresholdQuery` in polynomial time via
   `MaxSAT.thresholdCircuit` and `Compiler.toSatCNF` to a 3-CNF formula (`KSAT k` for every `3 ≤ k`)
   with at most `thresholdVarBudget workSize = 957 * workSize + 957` variables, satisfiable iff
   `cutoff ≤ optimum`.
3. **Resource transfer from a supplied fixed-width SAT solver:**
   * *Decision transfer:* `DecidableInExpTime`, `DecidableInSubexpTime`, and `P` membership transfer
     from `KSAT k` (`3 ≤ k`) to `ThresholdLanguage` (measured by `workSize`, and by `numVars` on
     sparse fixed-width instances).
   * *Exact native optimization (`FixedWidthSATSolver.exists_optimum_algorithm`,
     `computableInPolyTime_optimum_of_KSAT`):* any native `k`-SAT solver (`3 ≤ k`) with monotone
     variable-count factor `timeRate` and polynomial workspace (witnessed at `timeRate n = 2 ^ n` by
     `FixedWidthSATSolver.exists_bruteForce`) computes exact `MaxSAT` (and bounded-arity Boolean
     `Max-CSP`) optima at `timeRate (thresholdVarBudget workSize) * poly(L)` in polynomial space; a
     polynomial-time `k`-SAT decider computes exact optima in polynomial time.
   * *Binary search and witness recovery (`optimumByBinarySearchM`, `optimizeByBinarySearchM`):*
     bisection via `lowerBoundM` followed by unit-clause prefix pinning recovers both the exact
     optimum and an optimal assignment using at most `⌊log₂ m⌋ + 1 + n` queries to a supplied
     `k`-SAT oracle (`TimeM`), and on an `s`-clause subsample of a width-`w` instance queries
     `k`-SAT only on formulas of at most `thresholdVarBudget ((w + 1) * s + 2 * n)` variables while
     returning an assignment with at most `2 * δ * m` optimality loss with probability at least
     `1 - 2 ^ (n + 1) * exp (-2 * s * δ ^ 2)` (and `≥ 1 - η` under the `η` sample-size bound).

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
* [R. Impagliazzo, R. Paturi, *On the complexity of k-SAT*][ImpagliazzoPaturi2001]
-/

public section

namespace Cslib.Complexity.MaxSAT

open Cslib.Algorithms.Lean Cslib.Circuits Cslib.Circuits.Boolean Cslib.Circuits.Frontier
  Cslib.Logic.PL Turing.MultiTapeTM ComputableInPolyTime

/-! ### `#4391`-compliant `MaxSAT` structures, encodings, and `Max-CSP` bridges -/

/-- A MAX-SAT instance packaged as a structure with named `numVars` and `clauses` fields. -/
@[ext]
structure StructInstance where
  /-- Number of declared Boolean variables (`0, …, numVars - 1`). -/
  numVars : ℕ
  /-- Clause list counted with multiplicity. -/
  clauses : CNF ℕ
  deriving DecidableEq, Repr

/-- Unary declared variable count followed by `encCNF`, matching `MaxSAT.encInstance`. -/
enc_structure encStructInstance : StructInstance where
  numVars : encUnary, clauses : encCNF

attribute [fun_prop] encStructInstance_numVars_polyTime encStructInstance_clauses_polyTime
  encStructInstance_mk_polyTime

/-- A MAX-SAT threshold decision query packaged as a structure. -/
@[ext]
structure ThresholdQuery where
  /-- Underlying MAX-SAT instance. -/
  inst : StructInstance
  /-- Requested minimum number of satisfied clauses. -/
  cutoff : ℕ
  deriving DecidableEq, Repr

/-- Structured threshold query encoding, matching `MaxSAT.encQuery` bit-for-bit. -/
enc_structure encThresholdQuery : ThresholdQuery where
  inst : encStructInstance, cutoff : encUnary

attribute [fun_prop] encThresholdQuery_inst_polyTime encThresholdQuery_cutoff_polyTime
  encThresholdQuery_mk_polyTime

namespace StructInstance

/-- Underlying pair representation `MaxSAT.Instance`. -/
@[expose] def toPair (F : StructInstance) : Instance :=
  (F.numVars, F.clauses)

/-- Wrap a pair `MaxSAT.Instance` as a `StructInstance`. -/
@[expose] def ofPair (F : Instance) : StructInstance :=
  ⟨F.1, F.2⟩

/-- View a `StructInstance` as a Boolean `MaxCSPInstance (List Bool) ℕ`. -/
@[expose] def toMaxCSP (F : StructInstance) : MaxCSPInstance (List Bool) ℕ :=
  MaxCSPInstance.ofCNF F.numVars F.clauses

/-- Clause-satisfaction score of `x : BitString F.numVars`. -/
@[expose] def score (F : StructInstance) (x : BitString F.numVars) : ℕ :=
  MaxSAT.score F.toPair x

/-- Number of declared assignments achieving score at least `q`. -/
@[expose] def thresholdCount (F : StructInstance) (q : ℕ) : ℕ :=
  MaxSAT.thresholdCount F.toPair q

/-- Maximum number of simultaneously satisfied clauses. -/
@[expose] def optimum (F : StructInstance) : ℕ :=
  MaxSAT.optimum F.toPair

/-- Structural size: literal occurrences plus clauses. -/
@[expose] def workSize (F : StructInstance) : ℕ :=
  MaxSAT.workSize F.toPair

@[simp]
theorem score_toMaxCSP (F : StructInstance) (x : BitString F.numVars) :
    F.toMaxCSP.score MaxCSP.clauseSem x = F.score x :=
  MaxCSPInstance.score_ofCNF F.numVars F.clauses x

@[simp]
theorem thresholdCount_toMaxCSP (F : StructInstance) (q : ℕ) :
    F.toMaxCSP.thresholdCount MaxCSP.clauseSem q = F.thresholdCount q :=
  MaxCSPInstance.thresholdCount_ofCNF F.numVars F.clauses q

@[simp]
theorem optimum_toMaxCSP (F : StructInstance) :
    F.toMaxCSP.optimum MaxCSP.clauseSem = F.optimum :=
  MaxCSPInstance.optimum_ofCNF F.numVars F.clauses

@[simp]
theorem workSize_toMaxCSP (F : StructInstance) :
    F.toMaxCSP.workSize = F.workSize :=
  MaxCSPInstance.workSize_ofCNF F.numVars F.clauses

/-! #### Subsampling specializations for `StructInstance` -/

/-- Subsampled `s`-clause `StructInstance` indexed by `ω : Fin s → Fin F.clauses.length`. -/
@[expose] def sample (F : StructInstance) {s : ℕ} (ω : Fin s → Fin F.clauses.length) :
    StructInstance :=
  ⟨F.numVars, List.ofFn fun j => F.clauses[ω j]⟩

/-- Uniform distribution over `s`-clause subsamples of a nonempty `StructInstance`. -/
@[expose] noncomputable def samplePMF (F : StructInstance) (hm : 0 < F.clauses.length) (s : ℕ) :
    _root_.PMF (Fin s → Fin F.clauses.length) :=
  MaxCSP.uniformSamplePMF F.clauses.length hm s

private def castSampleIdx (F : StructInstance) {s : ℕ} (ω : Fin s → Fin F.clauses.length) :
    Fin s → Fin F.toMaxCSP.constraints.length :=
  fun j => ⟨(ω j).val, by simp only [toMaxCSP, MaxCSPInstance.length_constraints_ofCNF, (ω j).isLt]⟩

private theorem toMaxCSP_sample (F : StructInstance) {s : ℕ}
    (ω : Fin s → Fin F.clauses.length) :
    (F.sample ω).toMaxCSP = F.toMaxCSP.sample (F.castSampleIdx ω) := by
  refine MaxCSPInstance.ext rfl ?_
  simp only [MaxCSPInstance.sample, Fin.getElem_fin, castSampleIdx]
  simp only [toMaxCSP, sample, MaxCSPInstance.ofCNF, List.map_ofFn, Function.comp_def,
    Fin.getElem_fin, List.getElem_map]

private theorem score_toMaxCSP_sample (F : StructInstance) {s : ℕ}
    (ω : Fin s → Fin F.clauses.length) (x : BitString F.numVars) :
    (F.toMaxCSP.sample (F.castSampleIdx ω)).score MaxCSP.clauseSem x = (F.sample ω).score x := by
  have hcon : (F.toMaxCSP.sample (F.castSampleIdx ω)).constraints =
      (F.sample ω).toMaxCSP.constraints :=
    congrArg MaxCSPInstance.constraints (F.toMaxCSP_sample ω).symm
  rw [← (F.sample ω).score_toMaxCSP x]
  simp only [MaxCSPInstance.score, MaxCSPInstance.evalCount, hcon]
  rfl

private theorem optimum_toMaxCSP_sample (F : StructInstance) {s : ℕ}
    (ω : Fin s → Fin F.clauses.length) :
    (F.toMaxCSP.sample (F.castSampleIdx ω)).optimum MaxCSP.clauseSem = (F.sample ω).optimum :=
  Finset.sup_congr rfl fun x _ => F.score_toMaxCSP_sample ω x

theorem workSize_sample_le_of_width {w : ℕ} {F : StructInstance}
    (hw : ∀ c ∈ F.clauses, c.length ≤ w) {s : ℕ} (ω : Fin s → Fin F.clauses.length) :
    (F.sample ω).workSize ≤ (w + 1) * s := by
  rw [← workSize_toMaxCSP, toMaxCSP_sample]
  refine MaxCSPInstance.workSize_sample_le_of_width (fun c hc => ?_) _
  simp only [toMaxCSP, MaxCSPInstance.ofCNF, List.mem_map] at hc
  obtain ⟨cl, hcl, rfl⟩ := hc
  simpa only [Constraint.ofClause, List.length_map] using hw cl hcl

/-- **Uniform clause-subsampling concentration for MAX-SAT (`2 ^ (n + 1) * exp (-2 * s * δ ^ 2)`).**
-/
theorem exists_sample_score_abs_sub_ge_le (F : StructInstance) (hm : 0 < F.clauses.length)
    (s : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) :
    ((F.samplePMF hm s).toOuterMeasure
      {ω | ∃ x : BitString F.numVars,
        δ * (F.clauses.length : ℝ) ≤
          |(F.clauses.length : ℝ) / (s : ℝ) * ((F.sample ω).score x : ℝ) -
            (F.score x : ℝ)|}).toReal ≤
      2 ^ (F.numVars + 1) * Real.exp (-2 * (s : ℝ) * δ ^ 2) := by
  have hm' : 0 < F.toMaxCSP.constraints.length := by
    simpa only [toMaxCSP, MaxCSPInstance.length_constraints_ofCNF] using hm
  have h := F.toMaxCSP.boolean_exists_sample_score_abs_sub_ge_le MaxCSP.clauseSem hm' s hδ
  let e : (Fin s → Fin F.clauses.length) ≃ (Fin s → Fin F.toMaxCSP.constraints.length) :=
    Equiv.piCongrRight fun _ =>
      finCongr (MaxCSPInstance.length_constraints_ofCNF F.numVars F.clauses).symm
  have hpmf : (F.samplePMF hm s).map e = F.toMaxCSP.samplePMF hm' s := by
    have : Nonempty (Fin F.clauses.length) := ⟨⟨0, hm⟩⟩
    have : Nonempty (Fin F.toMaxCSP.constraints.length) := ⟨⟨0, hm'⟩⟩
    exact Cslib.Probability.PMF.uniformOfFintype_map_equiv e
  rw [← hpmf] at h
  refine (le_of_eq ?_).trans h
  congr 1
  rw [_root_.PMF.toOuterMeasure_map_apply]
  congr 1
  ext ω
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, toMaxCSP,
    MaxCSPInstance.length_constraints_ofCNF]
  refine exists_congr fun x => ?_
  have heq_idx : e ω = F.castSampleIdx ω := rfl
  have hsc : (F.toMaxCSP.sample (e ω)).score MaxCSP.clauseSem x = (F.sample ω).score x :=
    F.score_toMaxCSP_sample ω x
  have hfull : F.toMaxCSP.score MaxCSP.clauseSem x = F.score x := F.score_toMaxCSP x
  change _ ↔ δ * (F.clauses.length : ℝ) ≤
    |(F.clauses.length : ℝ) / (s : ℝ) *
      (((F.toMaxCSP.sample (e ω)).score MaxCSP.clauseSem x : ℕ) : ℝ) -
      ((F.toMaxCSP.score MaxCSP.clauseSem x : ℕ) : ℝ)|
  rw [hsc, hfull]

private theorem hunif_toMaxCSP (F : StructInstance) {s : ℕ}
    (ω : Fin s → Fin F.clauses.length) {ε : ℝ}
    (hunif : ∀ x : BitString F.numVars,
      |(F.clauses.length : ℝ) / (s : ℝ) * ((F.sample ω).score x : ℝ) - (F.score x : ℝ)| ≤ ε) :
    ∀ x : BitString F.toMaxCSP.numVars,
      |(F.toMaxCSP.constraints.length : ℝ) / (s : ℝ) *
          ((F.toMaxCSP.sample (F.castSampleIdx ω)).score MaxCSP.clauseSem x : ℝ) -
        (F.toMaxCSP.score MaxCSP.clauseSem x : ℝ)| ≤ ε := by
  intro x
  let x' : BitString F.numVars := x
  change |(F.toMaxCSP.constraints.length : ℝ) / (s : ℝ) *
      (((F.toMaxCSP.sample (F.castSampleIdx ω)).score MaxCSP.clauseSem x' : ℕ) : ℝ) -
    ((F.toMaxCSP.score MaxCSP.clauseSem x' : ℕ) : ℝ)| ≤ ε
  rw [F.score_toMaxCSP_sample ω x', F.score_toMaxCSP x']
  simpa only [toMaxCSP, MaxCSPInstance.length_constraints_ofCNF] using hunif x'

/-- **The `2 * δ * m` optimality loss bound for MAX-SAT.** -/
theorem optimum_sub_score_le_two_mul (F : StructInstance) {s : ℕ}
    (ω : Fin s → Fin F.clauses.length) {δ : ℝ}
    (hunif : ∀ x : BitString F.numVars,
      |(F.clauses.length : ℝ) / (s : ℝ) * ((F.sample ω).score x : ℝ) - (F.score x : ℝ)| ≤
        δ * (F.clauses.length : ℝ))
    {xHat : BitString F.numVars}
    (hmax : ∀ x : BitString F.numVars, (F.sample ω).score x ≤ (F.sample ω).score xHat) :
    (F.optimum : ℝ) - (F.score xHat : ℝ) ≤ 2 * δ * (F.clauses.length : ℝ) := by
  have hunif' : ∀ x : BitString F.toMaxCSP.numVars,
      |(F.toMaxCSP.constraints.length : ℝ) / (s : ℝ) *
          ((F.toMaxCSP.sample (F.castSampleIdx ω)).score MaxCSP.clauseSem x : ℝ) -
        (F.toMaxCSP.score MaxCSP.clauseSem x : ℝ)| ≤
        δ * (F.toMaxCSP.constraints.length : ℝ) := by
    simpa only [toMaxCSP, MaxCSPInstance.length_constraints_ofCNF] using F.hunif_toMaxCSP ω hunif
  have hmax' : ∀ x : BitString F.toMaxCSP.numVars,
      (F.toMaxCSP.sample (F.castSampleIdx ω)).score MaxCSP.clauseSem x ≤
        (F.toMaxCSP.sample (F.castSampleIdx ω)).score MaxCSP.clauseSem xHat := by
    intro x
    let x' : BitString F.numVars := x
    change (F.toMaxCSP.sample (F.castSampleIdx ω)).score MaxCSP.clauseSem x' ≤
      (F.toMaxCSP.sample (F.castSampleIdx ω)).score MaxCSP.clauseSem xHat
    rw [F.score_toMaxCSP_sample ω x', F.score_toMaxCSP_sample ω xHat]
    exact hmax x'
  have h := F.toMaxCSP.optimum_sub_score_le_two_mul MaxCSP.clauseSem (F.castSampleIdx ω) hunif'
    hmax'
  rw [F.optimum_toMaxCSP, F.score_toMaxCSP xHat] at h
  simpa only [toMaxCSP, MaxCSPInstance.length_constraints_ofCNF] using h

/-- **Deterministic rescaled sample optimum bound for MAX-SAT.** -/
theorem abs_rescaled_optimum_sub_le (F : StructInstance) {s : ℕ}
    (ω : Fin s → Fin F.clauses.length) {ε : ℝ}
    (hunif : ∀ x : BitString F.numVars,
      |(F.clauses.length : ℝ) / (s : ℝ) * ((F.sample ω).score x : ℝ) - (F.score x : ℝ)| ≤ ε) :
    |(F.clauses.length : ℝ) / (s : ℝ) * ((F.sample ω).optimum : ℝ) - (F.optimum : ℝ)| ≤ ε := by
  have h := F.toMaxCSP.abs_rescaled_optimum_sub_le MaxCSP.clauseSem (F.castSampleIdx ω)
    (F.hunif_toMaxCSP ω hunif)
  rw [F.optimum_toMaxCSP_sample ω, F.optimum_toMaxCSP] at h
  simpa only [toMaxCSP, MaxCSPInstance.length_constraints_ofCNF] using h

/-- **Success probability (`≥ 1 - 2 ^ (n + 1) * exp (-2 * s * δ ^ 2)`) for MAX-SAT subsampling.** -/
theorem one_sub_le_sample_good (F : StructInstance) (hm : 0 < F.clauses.length) (s : ℕ)
    {δ : ℝ} (hδ : 0 ≤ δ) :
    1 - 2 ^ (F.numVars + 1) * Real.exp (-2 * (s : ℝ) * δ ^ 2) ≤
      ((F.samplePMF hm s).toOuterMeasure
        {ω | (∀ xHat : BitString F.numVars,
            (∀ x, (F.sample ω).score x ≤ (F.sample ω).score xHat) →
              (F.optimum : ℝ) - (F.score xHat : ℝ) ≤ 2 * δ * (F.clauses.length : ℝ)) ∧
          |(F.clauses.length : ℝ) / (s : ℝ) * ((F.sample ω).optimum : ℝ) -
            (F.optimum : ℝ)| ≤ δ * (F.clauses.length : ℝ)}).toReal := by
  set good : Set (Fin s → Fin F.clauses.length) :=
    {ω | (∀ xHat : BitString F.numVars,
        (∀ x, (F.sample ω).score x ≤ (F.sample ω).score xHat) →
          (F.optimum : ℝ) - (F.score xHat : ℝ) ≤ 2 * δ * (F.clauses.length : ℝ)) ∧
      |(F.clauses.length : ℝ) / (s : ℝ) * ((F.sample ω).optimum : ℝ) -
        (F.optimum : ℝ)| ≤ δ * (F.clauses.length : ℝ)}
  set bad : Set (Fin s → Fin F.clauses.length) :=
    {ω | ∃ x : BitString F.numVars,
      δ * (F.clauses.length : ℝ) ≤
        |(F.clauses.length : ℝ) / (s : ℝ) * ((F.sample ω).score x : ℝ) - (F.score x : ℝ)|}
  have hsum := Cslib.Probability.PMF.toOuterMeasure_toReal_add_compl (F.samplePMF hm s) good
  have hsub : goodᶜ ⊆ bad := by
    intro ω hω
    by_contra hnb
    simp only [bad, Set.mem_ofPred_eq, not_exists, not_le] at hnb
    have hunif : ∀ x : BitString F.numVars,
        |(F.clauses.length : ℝ) / (s : ℝ) * ((F.sample ω).score x : ℝ) - (F.score x : ℝ)| ≤
          δ * (F.clauses.length : ℝ) := fun x => (hnb x).le
    exact hω ⟨fun _ hmax => F.optimum_sub_score_le_two_mul ω hunif hmax,
      F.abs_rescaled_optimum_sub_le ω hunif⟩
  have hcompl := (Cslib.Probability.PMF.toOuterMeasure_toReal_mono (F.samplePMF hm s) hsub).trans
    (F.exists_sample_score_abs_sub_ge_le hm s hδ)
  linarith

/-- **Success probability `≥ 1 - η` for MAX-SAT subsampling under
`(n + 1) * log 2 + log (1 / η) ≤ 2 * s * δ ^ 2`.** -/
theorem one_sub_le_sample_good_of_sample_size (F : StructInstance) (hm : 0 < F.clauses.length)
    {s : ℕ} {δ η : ℝ} (hδ : 0 ≤ δ) (hη : 0 < η)
    (hs : (F.numVars + 1 : ℝ) * Real.log 2 + Real.log (1 / η) ≤ 2 * (s : ℝ) * δ ^ 2) :
    1 - η ≤
      ((F.samplePMF hm s).toOuterMeasure
        {ω | (∀ xHat : BitString F.numVars,
            (∀ x, (F.sample ω).score x ≤ (F.sample ω).score xHat) →
              (F.optimum : ℝ) - (F.score xHat : ℝ) ≤ 2 * δ * (F.clauses.length : ℝ)) ∧
          |(F.clauses.length : ℝ) / (s : ℝ) * ((F.sample ω).optimum : ℝ) -
            (F.optimum : ℝ)| ≤ δ * (F.clauses.length : ℝ)}).toReal := by
  have h1 := MaxCSP.two_pow_succ_mul_exp_le_eta hη hs
  have h2 := F.one_sub_le_sample_good hm s hδ
  linarith

end StructInstance

/-! ### Parameterized encoding for `MaxCSPInstance` -/

/-- Encoding of `MaxCSPInstance Rel ℕ` as `(numVars, constraints)` with unary `numVars` and
constraints encoded by `encCSP` (`enc_structure` requires unparameterized structures, so this
parameterized structure defines the identical field-pair embedding). -/
@[expose] def encMaxCSPInstance {Rel : Type} (encRel : Rel ↪ List Bool) :
    MaxCSPInstance Rel ℕ ↪ List Bool :=
  ⟨fun F => encPair encUnary (encCSP encRel encNat) (F.numVars, F.constraints),
    fun a b h => by
      have h' := (encPair encUnary (encCSP encRel encNat)).injective h
      cases a; cases b; simp_all⟩

@[simp]
theorem encMaxCSPInstance_apply {Rel : Type} (encRel : Rel ↪ List Bool)
    (F : MaxCSPInstance Rel ℕ) :
    encMaxCSPInstance encRel F =
      encPair encUnary (encCSP encRel encNat) (F.numVars, F.constraints) :=
  rfl

@[fun_prop]
theorem computableInPolyTime_maxCSP_numVars {Rel γ : Type} {encIn : γ ↪ List Bool}
    {encRel : Rel ↪ List Bool} {g : γ → MaxCSPInstance Rel ℕ}
    (hg : ComputableInPolyTime g encIn (encMaxCSPInstance encRel)) :
    ComputableInPolyTime (fun a => (g a).numVars) encIn encUnary := by
  have hpair : ComputableInPolyTime (fun F : MaxCSPInstance Rel ℕ => (F.numVars, F.constraints))
      (encMaxCSPInstance encRel) (encPair encUnary (encCSP encRel encNat)) :=
    ComputableInPolyTime.of_eq fun _ => rfl
  exact (fst encUnary (encCSP encRel encNat)).comp (hpair.comp hg)

@[fun_prop]
theorem computableInPolyTime_maxCSP_constraints {Rel γ : Type} {encIn : γ ↪ List Bool}
    {encRel : Rel ↪ List Bool} {g : γ → MaxCSPInstance Rel ℕ}
    (hg : ComputableInPolyTime g encIn (encMaxCSPInstance encRel)) :
    ComputableInPolyTime (fun a => (g a).constraints) encIn (encCSP encRel encNat) := by
  have hpair : ComputableInPolyTime (fun F : MaxCSPInstance Rel ℕ => (F.numVars, F.constraints))
      (encMaxCSPInstance encRel) (encPair encUnary (encCSP encRel encNat)) :=
    ComputableInPolyTime.of_eq fun _ => rfl
  exact ((snd encUnary (encCSP encRel encNat)).comp hpair).comp hg

/-- Width-guarded compilation of a Boolean `MaxCSPInstance Rel ℕ` to a `StructInstance` via
forbidden-pattern `CSP.toCNFBounded`. -/
@[expose] def maxCSPToStruct {Rel : Type} (w : ℕ) (sem : Rel → List Bool → Bool)
    (F : MaxCSPInstance Rel ℕ) : StructInstance :=
  ⟨F.numVars, F.constraints.toCNFBounded w sem⟩

@[fun_prop]
theorem computableInPolyTime_maxCSPToStruct {Rel : Type} [Finite Rel] (encRel : Rel ↪ List Bool)
    (w : ℕ) (sem : Rel → List Bool → Bool) :
    ComputableInPolyTime (maxCSPToStruct w sem) (encMaxCSPInstance encRel) encStructInstance := by
  have hn : ComputableInPolyTime (fun F : MaxCSPInstance Rel ℕ => F.numVars)
      (encMaxCSPInstance encRel) encUnary :=
    computableInPolyTime_maxCSP_numVars ComputableInPolyTime.id'
  have hc : ComputableInPolyTime (fun F : MaxCSPInstance Rel ℕ => F.constraints.toCNFBounded w sem)
      (encMaxCSPInstance encRel) encCNF :=
    (CSP.computableInPolyTime_toCNFBounded_of_finite encRel encNat w sem).comp
      (computableInPolyTime_maxCSP_constraints ComputableInPolyTime.id')
  exact encStructInstance_mk_polyTime hn hc

theorem optimum_maxCSPToStruct_add_length {Rel : Type} {w : ℕ} (sem : Rel → List Bool → Bool)
    {F : MaxCSPInstance Rel ℕ} (hw : ∀ c ∈ F.constraints, c.scope.length ≤ w) :
    (maxCSPToStruct w sem F).optimum + F.constraints.length =
      (maxCSPToStruct w sem F).clauses.length + F.optimum sem := by
  dsimp only [maxCSPToStruct]
  rw [← StructInstance.optimum_toMaxCSP]
  dsimp only [StructInstance.toMaxCSP]
  rw [CSP.toCNFBounded_eq_toCNF hw]
  exact F.optimum_ofCNF_toCNF_add_length sem

/-! ### Polynomial-time threshold reduction to fixed-width `k`-SAT (`3 ≤ k`) -/

/-- The MAX-SAT threshold decision language: queries `q` whose cutoff is achievable. -/
@[expose] def ThresholdLanguage : Set ThresholdQuery :=
  {q | q.cutoff ≤ q.inst.optimum}

/-- Work-size parameter of a threshold query (`workSize` of its underlying instance). -/
@[expose] def ThresholdQuery.workSize (q : ThresholdQuery) : ℕ :=
  q.inst.workSize

/-- Compile a `ThresholdQuery` to a 3-CNF formula via `MaxSAT.thresholdCircuit` and
`Compiler.toSatCNF`. -/
@[expose] def thresholdToCNF (q : ThresholdQuery) : CNF ℕ :=
  Compiler.toSatCNF (thresholdCircuit q.inst.toPair q.cutoff) Boolean.interpretation

/-- Every clause of `thresholdToCNF q` has length at most `3`. -/
theorem length_clause_mem_thresholdToCNF (q : ThresholdQuery) {cl : Clause ℕ}
    (hcl : cl ∈ thresholdToCNF q) : cl.length ≤ 3 :=
  Compiler.length_le_of_mem_toCNF Boolean.interpretation (fun _ b => b)
    (Circuit.fanInAtMost_of_arity_le Boolean.arity_le_two _) hcl

/-- `thresholdToCNF q` is satisfiable iff `q.cutoff ≤ q.inst.optimum`. -/
theorem satisfiable_thresholdToCNF_iff (q : ThresholdQuery) :
    (thresholdToCNF q).Satisfiable ↔ q.cutoff ≤ q.inst.optimum := by
  rw [thresholdToCNF, Compiler.satisfiable_toSatCNF_iff, mem_SignatureCircuitSAT]
  simp only [eval_thresholdCircuit, decide_eq_true_eq]
  rw [← thresholdCount_pos_iff, thresholdCount_pos_iff_le_optimum]
  rfl

/-- For every fixed width `k ≥ 3`, `thresholdToCNF q` belongs to `KSAT k` iff `q` belongs to
`ThresholdLanguage`. -/
theorem thresholdToCNF_mem_KSAT_iff {k : ℕ} (hk : 3 ≤ k) (q : ThresholdQuery) :
    thresholdToCNF q ∈ KSAT k ↔ q ∈ ThresholdLanguage := by
  simp only [KSAT, ThresholdLanguage, Set.mem_ofPred_eq, satisfiable_thresholdToCNF_iff]
  exact ⟨fun h => h.2, fun h => ⟨fun _ hcl => (length_clause_mem_thresholdToCNF q hcl).trans hk, h⟩⟩

/-- The variable budget of `thresholdToCNF` on work size `w`: the compiled 3-CNF of a query of
work size `w` has at most `thresholdVarBudget w = 957 * w + 957` variables
(`numVars_thresholdToCNF_le`). -/
@[expose] def thresholdVarBudget (w : ℕ) : ℕ := 957 * w + 957

/-- A larger work size has a larger variable budget. -/
theorem thresholdVarBudget_mono : Monotone thresholdVarBudget := fun _ _ h => by
  unfold thresholdVarBudget
  omega

/-- `thresholdToCNF q` uses at most `thresholdVarBudget q.workSize` distinct variables. -/
theorem numVars_thresholdToCNF_le (q : ThresholdQuery) :
    (thresholdToCNF q).numVars ≤ thresholdVarBudget q.workSize := by
  have hnum := Compiler.numVars_toCNF_le (c := thresholdCircuit q.inst.toPair q.cutoff)
    Boolean.interpretation (fun _ b => b)
    (Circuit.fanInAtMost_of_arity_le Boolean.arity_le_two _)
  have hsize := size_thresholdCircuit_le q.inst.toPair q.cutoff
  change (Compiler.toCNF (thresholdCircuit q.inst.toPair q.cutoff)
      Boolean.interpretation (fun _ b => b)).numVars ≤
    957 * workSize q.inst.toPair + 957
  omega

/-- On an instance whose clauses all have width at most `w`, `thresholdToCNF q` uses at most
`thresholdVarBudget ((w + 1) * m)` distinct variables (`m = q.inst.clauses.length`). -/
theorem numVars_thresholdToCNF_le_of_width {w : ℕ} (q : ThresholdQuery)
    (hw : ∀ c ∈ q.inst.clauses, c.length ≤ w) :
    (thresholdToCNF q).numVars ≤ thresholdVarBudget ((w + 1) * q.inst.clauses.length) :=
  (numVars_thresholdToCNF_le q).trans
    (thresholdVarBudget_mono (workSize_le_of_width w q.inst.toPair hw))

/-- `thresholdToCNF q` has at most `8 * (numVars + 1)` clauses. -/
theorem length_thresholdToCNF_le (q : ThresholdQuery) :
    (thresholdToCNF q).length ≤ 8 * ((thresholdToCNF q).numVars + 1) :=
  Compiler.length_toCNF_le_numVars Boolean.interpretation (fun _ b => b)
    (Circuit.fanInAtMost_of_arity_le Boolean.arity_le_two _)

/-- `thresholdToCNF` is computable in native polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_thresholdToCNF :
    ComputableInPolyTime thresholdToCNF encThresholdQuery encCNF := by
  have hinst : ComputableInPolyTime ThresholdQuery.inst encThresholdQuery encStructInstance :=
    encThresholdQuery_inst_polyTime ComputableInPolyTime.id'
  have hpair : ComputableInPolyTime (fun q : ThresholdQuery => q.inst.toPair)
      encThresholdQuery encInstance :=
    (encStructInstance_numVars_polyTime hinst).prod (encStructInstance_clauses_polyTime hinst)
  have htoQuery : ComputableInPolyTime (fun q : ThresholdQuery => (q.inst.toPair, q.cutoff))
      encThresholdQuery encQuery :=
    hpair.prod (encThresholdQuery_cutoff_polyTime ComputableInPolyTime.id')
  have hsat : ComputableInPolyTime
      (fun p : Query => Compiler.toSatCNF (thresholdCircuit p.1 p.2) Boolean.interpretation)
      encQuery encCNF :=
    ((CircuitCounting.computableInPolyTime_toSatCNF (σ := Boolean.signature) Boolean.encOp
      Boolean.interpretation).comp computableInPolyTime_thresholdCircuit).of_enc_eq fun _ => rfl
  exact (hsat.comp htoQuery).of_enc_eq fun _ => rfl

/-- `ThresholdLanguage` reduces in polynomial time to `KSAT k` for every `k ≥ 3`. -/
theorem polyTimeReducible_thresholdLanguage_KSAT {k : ℕ} (hk : 3 ≤ k) :
    PolyTimeReducible encThresholdQuery encCNF ThresholdLanguage (KSAT k) :=
  ⟨thresholdToCNF, computableInPolyTime_thresholdToCNF,
    fun q => (thresholdToCNF_mem_KSAT_iff hk q).symm⟩

/-- `ThresholdLanguage` reduces in polynomial time to `ThreeSAT`. -/
theorem polyTimeReducible_thresholdLanguage_ThreeSAT :
    PolyTimeReducible encThresholdQuery encCNF ThresholdLanguage ThreeSAT :=
  polyTimeReducible_thresholdLanguage_KSAT le_rfl

/-! ### Resource transfer from a supplied fixed-width SAT solver -/

/-- **Exponential-time decision transfer:** a `2 ^ (δ * n)` decider for `KSAT k` (`3 ≤ k`) gives a
`2 ^ (957 * δ * workSize)` decider for `ThresholdLanguage`. -/
theorem decidableInExpTime_thresholdLanguage_of_KSAT {k : ℕ} (hk : 3 ≤ k) {δ : ℝ} (hδ : 0 ≤ δ)
    (hKSAT : DecidableInExpTime (KSAT k) encCNF CNF.numVars δ) :
    DecidableInExpTime ThresholdLanguage encThresholdQuery ThresholdQuery.workSize (957 * δ) :=
  hKSAT.of_reduction computableInPolyTime_thresholdToCNF
    (fun q => (thresholdToCNF_mem_KSAT_iff hk q).symm) numVars_thresholdToCNF_le hδ

/-- **Subexponential-time decision transfer:** subexponential decidability of `KSAT k` (`3 ≤ k`) in
`CNF.numVars` transfers to `ThresholdLanguage` in `ThresholdQuery.workSize`. -/
theorem decidableInSubexpTime_thresholdLanguage_of_KSAT {k : ℕ} (hk : 3 ≤ k)
    (hKSAT : DecidableInSubexpTime (KSAT k) encCNF CNF.numVars) :
    DecidableInSubexpTime ThresholdLanguage encThresholdQuery ThresholdQuery.workSize :=
  hKSAT.of_reduction computableInPolyTime_thresholdToCNF
    (fun q => (thresholdToCNF_mem_KSAT_iff hk q).symm) numVars_thresholdToCNF_le

/-- **Polynomial-time decision transfer:** if `KSAT k ∈ P encCNF` (`3 ≤ k`), then
`ThresholdLanguage ∈ P encThresholdQuery`. -/
theorem mem_P_thresholdLanguage_of_KSAT {k : ℕ} (hk : 3 ≤ k) (hKSAT : KSAT k ∈ P encCNF) :
    ThresholdLanguage ∈ P encThresholdQuery :=
  (polyTimeReducible_thresholdLanguage_KSAT hk).mem_P hKSAT

/-- A supplied native deterministic solver for `k`-SAT with a monotone parameter time factor
`timeRate` in `CNF.numVars` and polynomial workspace in the encoded formula length. -/
structure FixedWidthSATSolver (k : ℕ) where
  /-- Boolean decision procedure on CNF formulas. -/
  solve : CNF ℕ → Bool
  /-- Monotone parameter factor as a function of `CNF.numVars`. -/
  timeRate : ℕ → ℕ
  /-- Polynomial exponent in the time bound. -/
  timeExp : ℕ
  /-- Polynomial exponent in the workspace bound. -/
  spaceExp : ℕ
  /-- Correctness on all formulas of clause width at most `k`. -/
  correct : ∀ φ : CNF ℕ, (∀ c ∈ φ, c.length ≤ k) → (solve φ = true ↔ φ.Satisfiable)
  /-- Non-vanishing rate factor (`1 ≤ timeRate n`). -/
  one_le_timeRate : ∀ n, 1 ≤ timeRate n
  /-- Monotonicity of `timeRate` in `CNF.numVars`. -/
  mono_timeRate : Monotone timeRate
  /-- Native machine certificate for `solve`. -/
  computable : ComputableInO solve encCNF encBool
    (fun φ => timeRate φ.numVars * ((encCNF φ).length + 1) ^ timeExp)
    (fun φ => ((encCNF φ).length + 1) ^ spaceExp)

/-- **Classical `2 ^ n` exhaustive-search `FixedWidthSATSolver k`:** `BruteForce.search` yields a
native polynomial-space `FixedWidthSATSolver k` with `timeRate n = 2 ^ n` for every `k`. -/
theorem FixedWidthSATSolver.exists_bruteForce (k : ℕ) :
    ∃ solver : FixedWidthSATSolver k,
      solver.solve = BruteForce.search ∧ solver.timeRate = fun n => 2 ^ n := by
  let BfState := (CNF ℕ × ℕ) × Bool
  let encBf : BfState ↪ List Bool := encPair (encPair encCNF encNat) encBool
  let bfInit (φ : CNF ℕ) : BfState := ((φ, 0), false)
  let bfStep (s : BfState) : BfState :=
    ((s.1.1, s.1.2 + 1), s.2 || s.1.1.eval (bitsAssignment s.1.1.distinctVars s.1.2))
  let bfRounds (φ : CNF ℕ) : ℕ := 2 ^ φ.numVars
  have hiter : ∀ (φ : CNF ℕ) (m : ℕ), bfStep^[m] (bfInit φ) =
      ((φ, m), (List.range m).any fun i => φ.eval (bitsAssignment φ.distinctVars i)) := by
    intro φ m
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [Function.iterate_succ_apply', ih, List.range_succ, List.any_append, List.any_cons,
        List.any_nil, Bool.or_false]
  have hrounds_poly : ComputableInPolyTime bfRounds encCNF encNat :=
    ComputableInPolyTime.of_tidy
      (ComputableTidilyInPolyTime.binary_two_pow.comp SAT.computableInPolyTime_numVars.tidy)
  have hinit_poly : ComputableInPolyTime bfInit encCNF encBf :=
    (ComputableInPolyTime.id'.prod (const 0)).prod (const false)
  have hstep_poly : ComputableInPolyTime bfStep encBf encBf := by
    have hs1 : ComputableInPolyTime Prod.fst encBf (encPair encCNF encNat) := fst _ _
    have hφ : ComputableInPolyTime (fun s : BfState => s.1.1) encBf encCNF :=
      (fst encCNF encNat).comp hs1
    have hi : ComputableInPolyTime (fun s : BfState => s.1.2) encBf encNat :=
      (snd encCNF encNat).comp hs1
    have hb : ComputableInPolyTime Prod.snd encBf encBool := snd _ _
    have hnext_i := binary_add' hi (const 1)
    have heval := computableInPolyTime_eval_bitsAssignment.comp
      ((hφ.prod (SAT.computableInPolyTime_distinctVars.comp hφ)).prod hi)
    exact (hφ.prod hnext_i).prod (bool_or.comp (hb.prod heval))
  obtain ⟨dn, _, hdn⟩ := hrounds_poly.exists_degree
  obtain ⟨di, _, hdi⟩ := hinit_poly.exists_degree
  obtain ⟨ds, _, hds⟩ := hstep_poly.exists_degree
  obtain ⟨cn, en, hnum_le⟩ := SAT.computableInPolyTime_numVars.polyBounded_length.exists_le
  have hnv_le (φ : CNF ℕ) : φ.numVars ≤ cn * ((encCNF φ).length + 1) ^ en := by
    simpa only [encUnary_apply, List.length_replicate] using hnum_le φ
  have hrounds_len (φ : CNF ℕ) : (encNat (bfRounds φ)).length = φ.numVars + 1 := by
    dsimp only [bfRounds]
    rw [encNat_two_pow, List.length_append, List.length_replicate, List.length_singleton]
  let B (φ : CNF ℕ) : ℕ :=
    2 * (2 * (encCNF φ).length + (cn * ((encCNF φ).length + 1) ^ en + 1) + 2) + 4
  have hstate (φ : CNF ℕ) (m : ℕ) (hm : m ≤ bfRounds φ) :
      (encBf (bfStep^[m] (bfInit φ))).length ≤ B φ := by
    have hm_len : (encNat m).length ≤ φ.numVars + 1 :=
      (length_encNat_mono hm).trans_eq (hrounds_len φ)
    have hnv := hnv_le φ
    rw [hiter]
    dsimp only [encBf, B]
    rw [length_encPair, length_encPair, encBool_apply, List.length_singleton]
    dsimp only
    omega
  have hloop := ComputableInO.iterate hdn.inO hdi.inO hds.inO
    (R := fun φ => (B φ + 1) ^ ds) (Q := fun φ => (B φ + 1) ^ ds) (B := B)
    (fun φ m hm => Nat.pow_le_pow_left (Nat.add_le_add_right (hstate φ m hm) 1) ds)
    (fun φ m hm => Nat.pow_le_pow_left (Nat.add_le_add_right (hstate φ m hm) 1) ds)
    hstate
  have hB_poly : PolyBounded (fun φ : CNF ℕ => (encCNF φ).length) B := by
    have hL : PolyBounded (fun φ : CNF ℕ => (encCNF φ).length) (fun φ => (encCNF φ).length) := .self
    have hN : PolyBounded (fun φ : CNF ℕ => (encCNF φ).length)
        (fun φ => cn * ((encCNF φ).length + 1) ^ en + 1) :=
      ((PolyBounded.const cn).mul ((hL.add (.const 1)).pow en)).add (.const 1)
    exact ((PolyBounded.const 2).mul
      (((PolyBounded.const 2).mul hL).add hN |>.add (.const 2))).add (.const 4)
  have hU_poly : PolyBounded (fun φ : CNF ℕ => (encCNF φ).length)
      (fun φ => ((encCNF φ).length + 1) ^ dn + ((encCNF φ).length + 1) ^ di +
        2 * ((B φ + 1) ^ ds + B φ + (φ.numVars + 2) ^ 2)) := by
    have hL : PolyBounded (fun φ : CNF ℕ => (encCNF φ).length) (fun φ => (encCNF φ).length) := .self
    have hL1 := hL.add (.const 1)
    have hnvP : PolyBounded (fun φ : CNF ℕ => (encCNF φ).length) (fun φ => φ.numVars + 2) :=
      (SAT.computableInPolyTime_numVars.polyBounded_length.mono fun φ => by
        simp only [encUnary_apply, List.length_replicate, le_rfl]).add (.const 2)
    exact ((hL1.pow dn).add (hL1.pow di)).add
      ((PolyBounded.const 2).mul ((((hB_poly.add (.const 1)).pow ds).add hB_poly).add (hnvP.pow 2)))
  have hV_poly : PolyBounded (fun φ : CNF ℕ => (encCNF φ).length)
      (fun φ => ((encCNF φ).length + 1) ^ dn + ((encCNF φ).length + 1) ^ di +
        (B φ + 1) ^ ds + B φ + (φ.numVars + 1)) := by
    have hL : PolyBounded (fun φ : CNF ℕ => (encCNF φ).length) (fun φ => (encCNF φ).length) := .self
    have hL1 := hL.add (.const 1)
    have hnvP : PolyBounded (fun φ : CNF ℕ => (encCNF φ).length) (fun φ => φ.numVars + 1) :=
      (SAT.computableInPolyTime_numVars.polyBounded_length.mono fun φ => by
        simp only [encUnary_apply, List.length_replicate, le_rfl]).add (.const 1)
    exact ((((hL1.pow dn).add (hL1.pow di)).add ((hB_poly.add (.const 1)).pow ds)).add hB_poly).add
      hnvP
  obtain ⟨cU, dU, hU⟩ := hU_poly.exists_le
  obtain ⟨cV, dV, hV⟩ := hV_poly.exists_le
  have hloop_std : ComputableInO (fun φ => bfStep^[bfRounds φ] (bfInit φ)) encCNF encBf
      (fun φ => 2 ^ φ.numVars * ((encCNF φ).length + 1) ^ dU)
      (fun φ => ((encCNF φ).length + 1) ^ dV) := by
    refine hloop.mono (cU + cV + 1) (fun φ => ?_) (fun φ => ?_)
    · have hN1 : 1 ≤ 2 ^ φ.numVars := Nat.one_le_two_pow
      have h2N : bfRounds φ + 1 ≤ 2 * 2 ^ φ.numVars := by dsimp only [bfRounds]; omega
      have hrl : (encNat (bfRounds φ)).length + 1 = φ.numVars + 2 := by
        rw [hrounds_len φ]
      calc ((encCNF φ).length + 1) ^ dn + ((encCNF φ).length + 1) ^ di +
            (bfRounds φ + 1) * ((B φ + 1) ^ ds + B φ + ((encNat (bfRounds φ)).length + 1) ^ 2)
          ≤ 2 ^ φ.numVars * (((encCNF φ).length + 1) ^ dn + ((encCNF φ).length + 1) ^ di +
              2 * ((B φ + 1) ^ ds + B φ + (φ.numVars + 2) ^ 2)) := by
            rw [hrl,
              show 2 ^ φ.numVars * (((encCNF φ).length + 1) ^ dn + ((encCNF φ).length + 1) ^ di +
                  2 * ((B φ + 1) ^ ds + B φ + (φ.numVars + 2) ^ 2)) =
                2 ^ φ.numVars * (((encCNF φ).length + 1) ^ dn + ((encCNF φ).length + 1) ^ di) +
                  (2 * 2 ^ φ.numVars) * ((B φ + 1) ^ ds + B φ + (φ.numVars + 2) ^ 2) by ring]
            exact Nat.add_le_add (Nat.le_mul_of_pos_left _ hN1) (Nat.mul_le_mul_right _ h2N)
        _ ≤ 2 ^ φ.numVars * (cU * ((encCNF φ).length + 1) ^ dU) :=
            Nat.mul_le_mul_left (2 ^ φ.numVars) (hU φ)
        _ = cU * (2 ^ φ.numVars * ((encCNF φ).length + 1) ^ dU) := by ring
        _ ≤ (cU + cV + 1) * (2 ^ φ.numVars * ((encCNF φ).length + 1) ^ dU + 1) :=
            Nat.mul_le_mul (by omega) (by omega)
    · calc ((encCNF φ).length + 1) ^ dn + ((encCNF φ).length + 1) ^ di +
            (B φ + 1) ^ ds + B φ + (encNat (bfRounds φ)).length
          = ((encCNF φ).length + 1) ^ dn + ((encCNF φ).length + 1) ^ di +
              (B φ + 1) ^ ds + B φ + (φ.numVars + 1) := by rw [hrounds_len]
        _ ≤ cV * ((encCNF φ).length + 1) ^ dV := hV φ
        _ ≤ (cU + cV + 1) * (((encCNF φ).length + 1) ^ dV + 1) :=
            Nat.mul_le_mul (by omega) (by omega)
  obtain ⟨d, hsearch_inO⟩ := hloop_std.polynomial_postprocessing
    (snd (encPair encCNF encNat) encBool) (fun _ => Nat.one_le_two_pow)
  have hsearch_eq : BruteForce.search =
      Prod.snd ∘ fun φ : CNF ℕ => bfStep^[bfRounds φ] (bfInit φ) := by
    funext φ
    simp only [Function.comp_apply, hiter, BruteForce.search, bfRounds, CNF.length_distinctVars]
  refine ⟨⟨BruteForce.search, fun n => 2 ^ n, d, d, ?_, fun _ => Nat.one_le_two_pow,
    fun _ _ hxy => Nat.pow_le_pow_right (by norm_num) hxy,
    hsearch_inO.of_enc_eq fun φ => by rw [hsearch_eq]⟩, rfl, rfl⟩
  intro φ _
  exact BruteForce.search_eq_true_iff φ

/-- Recover the optimum from the list of feasibility booleans at cutoffs `0, …, m + 1`. -/
@[expose] def optimumFromDecisions (decisions : List Bool) : ℕ :=
  decisions.countP id - 1

theorem optimumFromDecisions_threshold (F : StructInstance) :
    optimumFromDecisions
      ((List.range (F.clauses.length + 2)).map fun q => decide (q ≤ F.optimum)) =
      F.optimum := by
  have hopt : F.optimum ≤ F.clauses.length := optimum_le (F.numVars, F.clauses)
  simp only [optimumFromDecisions, List.countP_map, Function.comp_def, id_eq]
  rw [countP_range_le, Nat.min_eq_right (by omega)]
  omega

@[fun_prop]
theorem computableInPolyTime_optimumFromDecisions :
    ComputableInPolyTime optimumFromDecisions (encList encBool) encNat := by
  have hcnt : ComputableInPolyTime (fun bs : List Bool => bs.countP id)
      (encList encBool) encUnary :=
    countPWithInput (encA := encBool) ComputableInPolyTime.id' (snd (encList encBool) encBool)
  exact unary_to_binary.comp (unary_sub' hcnt (const 1))

private theorem computableInPolyTime_structWorkSize :
    ComputableInPolyTime StructInstance.workSize encStructInstance encUnary := by
  have hcl : ComputableInPolyTime StructInstance.clauses encStructInstance
      (encList (encList (encPair encNat encBool))) :=
    encStructInstance_clauses_polyTime ComputableInPolyTime.id'
  have hvars_len : ComputableInPolyTime (fun F : StructInstance => F.clauses.vars.length)
      encStructInstance encUnary := by
    have hflat : ComputableInPolyTime (fun F : StructInstance => F.clauses.flatten)
        encStructInstance (encList (encPair encNat encBool)) :=
      (ComputableInPolyTime.of_tidy
        (ComputableTidilyInPolyTime.flatten (encPair encNat encBool))).comp hcl
    refine ((length_list (encPair encNat encBool)).comp hflat).of_enc_eq fun F => ?_
    simp only [Function.comp_apply, CNF.vars, List.length_map]
  exact unary_add' hvars_len ((length_list (encList (encPair encNat encBool))).comp hcl)

private theorem computableInPolyTime_thresholdQueries :
    ComputableInPolyTime
      (fun F : StructInstance =>
        (List.range (F.clauses.length + 2)).map fun q => thresholdToCNF ⟨F, q⟩)
      encStructInstance (encList encCNF) := by
  have hm : ComputableInPolyTime (fun F : StructInstance => F.clauses.length)
      encStructInstance encUnary :=
    (length_list (encList (encPair encNat encBool))).comp
      (encStructInstance_clauses_polyTime ComputableInPolyTime.id')
  have hrange : ComputableInPolyTime
      (fun F : StructInstance => List.range (F.clauses.length + 2))
      encStructInstance (encList encUnary) :=
    range.comp (unary_add' hm (const 2))
  have hthresh : ComputableInPolyTime
      (fun p : StructInstance × ℕ => thresholdToCNF ⟨p.1, p.2⟩)
      (encPair encStructInstance encUnary) encCNF :=
    computableInPolyTime_thresholdToCNF.comp
      (encThresholdQuery_mk_polyTime (fst encStructInstance encUnary)
        (snd encStructInstance encUnary))
  exact mapWithInput (f := fun F q => thresholdToCNF ⟨F, q⟩) hrange hthresh

/-- **Native MAX-SAT optimization from a supplied fixed-width SAT solver (`3 ≤ k`).** -/
theorem FixedWidthSATSolver.exists_optimum_algorithm {k : ℕ} (hk : 3 ≤ k)
    (solver : FixedWidthSATSolver k) :
    ∃ d : ℕ, ComputableInO StructInstance.optimum encStructInstance encNat
      (fun F => solver.timeRate (thresholdVarBudget F.workSize) *
        ((encStructInstance F).length + 1) ^ d)
      (fun F => ((encStructInstance F).length + 1) ^ d) := by
  let encP := encPair encStructInstance encCNF
  let guard (p : StructInstance × CNF ℕ) : Bool :=
    decide (p.2.numVars ≤ thresholdVarBudget p.1.workSize)
  have hguard : ComputableInPolyTime guard encP encBool := by
    have hlhs := SAT.computableInPolyTime_numVars.comp (snd encStructInstance encCNF)
    have hrhs : ComputableInPolyTime
        (fun p : StructInstance × CNF ℕ => thresholdVarBudget p.1.workSize) encP encUnary :=
      unary_add' (unary_mul' (const 957)
        (computableInPolyTime_structWorkSize.comp (fst encStructInstance encCNF))) (const 957)
    exact unary_le' hlhs hrhs
  obtain ⟨dg, _, hguard_deg⟩ := hguard.exists_degree
  have hsolve_snd : ComputableInO (fun p : StructInstance × CNF ℕ => solver.solve p.2)
      encP encBool
      (fun p => (encP p).length + solver.timeRate p.2.numVars * ((encCNF p.2).length + 1) ^
        solver.timeExp)
      (fun p => (encP p).length + ((encCNF p.2).length + 1) ^ solver.spaceExp) :=
    solver.computable.comp (ComputableInDegree.snd encStructInstance encCNF).inO_one
  have hite := hguard_deg.inO.ite hsolve_snd (ComputableInO.const false)
  let eMax := max dg (max solver.timeExp 1)
  let bMax := max dg (max solver.spaceExp 1)
  have henc_pow (p : StructInstance × CNF ℕ) (exp : ℕ) (hexp : exp ≤ max exp 1) :
      ((encCNF p.2).length + 1) ^ exp ≤ ((encP p).length + 1) ^ max dg (max exp 1) :=
    (Nat.pow_le_pow_left (Nat.add_le_add_right (length_le_encPair_right _ _ p) 1) _).trans
      (Nat.pow_le_pow_right (Nat.le_add_left 1 _) (hexp.trans (le_max_right dg _)))
  have hanswer : ComputableInO
      (fun p : StructInstance × CNF ℕ => if guard p then solver.solve p.2 else false)
      encP encBool
      (fun p => solver.timeRate (thresholdVarBudget p.1.workSize) * ((encP p).length + 1) ^ eMax)
      (fun p => ((encP p).length + 1) ^ bMax) := by
    refine hite.mono 3 (fun p => ?_) (fun p => ?_)
    · set L := (encP p).length
      have hL1 : 1 ≤ L + 1 := Nat.le_add_left 1 L
      have hR1 : 1 ≤ solver.timeRate (thresholdVarBudget p.1.workSize) :=
        solver.one_le_timeRate _
      have hdg : (L + 1) ^ dg ≤
          solver.timeRate (thresholdVarBudget p.1.workSize) * (L + 1) ^ eMax :=
        (Nat.pow_le_pow_right hL1 (le_max_left dg _)).trans (Nat.le_mul_of_pos_left _ hR1)
      have hLlin : L ≤ solver.timeRate (thresholdVarBudget p.1.workSize) * (L + 1) ^ eMax := by
        have h1 : L ≤ (L + 1) ^ 1 := by simp only [pow_one]; omega
        exact (h1.trans (Nat.pow_le_pow_right hL1
          ((le_max_right _ _).trans (le_max_right dg _)))).trans (Nat.le_mul_of_pos_left _ hR1)
      split_ifs with hg_true
      · have hnv : p.2.numVars ≤ thresholdVarBudget p.1.workSize := of_decide_eq_true hg_true
        have hmul := Nat.mul_le_mul (solver.mono_timeRate hnv)
          (henc_pow p solver.timeExp (le_max_left _ 1))
        nlinarith
      · nlinarith
    · set L := (encP p).length
      have hL1 : 1 ≤ L + 1 := Nat.le_add_left 1 L
      have hdg : (L + 1) ^ dg ≤ (L + 1) ^ bMax := Nat.pow_le_pow_right hL1 (le_max_left dg _)
      have hLlin : L ≤ (L + 1) ^ bMax := by
        have h1 : L ≤ (L + 1) ^ 1 := by simp only [pow_one]; omega
        exact h1.trans (Nat.pow_le_pow_right hL1 ((le_max_right _ _).trans (le_max_right dg _)))
      split_ifs
      · have hpow : ((encCNF p.2).length + 1) ^ solver.spaceExp ≤ (L + 1) ^ bMax :=
          henc_pow p solver.spaceExp (le_max_left _ 1)
        omega
      · omega
  obtain ⟨d₁, hlist⟩ := ComputableInO.polynomial_queries
    (T := fun F : StructInstance => solver.timeRate (thresholdVarBudget F.workSize))
    hanswer computableInPolyTime_thresholdQueries (fun _ => solver.one_le_timeRate _)
  obtain ⟨d₂, hpost⟩ := hlist.polynomial_postprocessing
    computableInPolyTime_optimumFromDecisions (fun _ => solver.one_le_timeRate _)
  refine ⟨d₂, hpost.of_enc_eq fun F => ?_⟩
  have hmap_eq :
      ((List.range (F.clauses.length + 2)).map (fun q => thresholdToCNF ⟨F, q⟩)).map
        (fun φ => if guard (F, φ) then solver.solve φ else false) =
      (List.range (F.clauses.length + 2)).map (fun q => decide (q ≤ F.optimum)) := by
    rw [List.map_map]
    refine List.map_congr_left fun q _ => ?_
    have hgq : guard (F, thresholdToCNF ⟨F, q⟩) = true :=
      decide_eq_true (numVars_thresholdToCNF_le ⟨F, q⟩)
    simp only [Function.comp_apply, hgq, ↓reduceIte]
    rw [Bool.eq_iff_iff, solver.correct _ (fun _ hcl =>
      (length_clause_mem_thresholdToCNF ⟨F, q⟩ hcl).trans hk),
      satisfiable_thresholdToCNF_iff, decide_eq_true_eq]
  simp only [Function.comp_apply, hmap_eq, optimumFromDecisions_threshold]

/-- **Polynomial-time exact MAX-SAT optimization from a polynomial-time `k`-SAT decider (`3 ≤ k`).**
-/
theorem computableInPolyTime_optimum_of_KSAT {k : ℕ} (hk : 3 ≤ k) {solveKSAT : CNF ℕ → Bool}
    (hpoly : ComputableInPolyTime solveKSAT encCNF encBool)
    (hspec : ∀ φ : CNF ℕ, (∀ c ∈ φ, c.length ≤ k) → (solveKSAT φ = true ↔ φ.Satisfiable)) :
    ComputableInPolyTime StructInstance.optimum encStructInstance encNat := by
  have hmap := (ComputableInPolyTime.map hpoly).comp computableInPolyTime_thresholdQueries
  refine (computableInPolyTime_optimumFromDecisions.comp hmap).of_enc_eq fun F => ?_
  have hdec : ((List.range (F.clauses.length + 2)).map fun q => thresholdToCNF ⟨F, q⟩).map solveKSAT
      = (List.range (F.clauses.length + 2)).map (fun q => decide (q ≤ F.optimum)) := by
    rw [List.map_map]
    refine List.map_congr_left fun q _ => ?_
    rw [Function.comp_apply, Bool.eq_iff_iff, hspec _ (fun _ hcl =>
      (length_clause_mem_thresholdToCNF ⟨F, q⟩ hcl).trans hk),
      satisfiable_thresholdToCNF_iff, decide_eq_true_eq]
  simp only [Function.comp_apply, hdec, optimumFromDecisions_threshold]

/-! ### `O(log m)`-query `TimeM` binary-search optimization and sparse-subsampling transfer -/

/-- Exact MAX-SAT optimization by binary search on `[1, m + 1)` using a supplied `k`-SAT oracle
`solveM : CNF ℕ → TimeM ℕ Bool`. -/
def optimumByBinarySearchM (solveM : CNF ℕ → TimeM ℕ Bool) (F : StructInstance) : TimeM ℕ ℕ := do
  let k ← lowerBoundM (fun q => solveM (thresholdToCNF ⟨F, q⟩)) 1 (F.clauses.length + 1)
  return k - 1

/-- **Correctness of binary-search optimization:** for any `k`-SAT oracle (`3 ≤ k`),
`optimumByBinarySearchM` returns `F.optimum`. -/
theorem optimumByBinarySearchM_ret {k : ℕ} (hk : 3 ≤ k) {solveM : CNF ℕ → TimeM ℕ Bool}
    (hspec : ∀ φ : CNF ℕ, (∀ c ∈ φ, c.length ≤ k) → ((solveM φ).ret = true ↔ φ.Satisfiable))
    (F : StructInstance) :
    (optimumByBinarySearchM solveM F).ret = F.optimum := by
  let probe (q : ℕ) : TimeM ℕ Bool := solveM (thresholdToCNF ⟨F, q⟩)
  have hprobe (q : ℕ) : (probe q).ret = true ↔ q ≤ F.optimum := by
    rw [hspec _ (fun _ hcl => (length_clause_mem_thresholdToCNF ⟨F, q⟩ hcl).trans hk),
      satisfiable_thresholdToCNF_iff]
  have hmono : ∀ m m', 1 ≤ m → m ≤ m' → m' < F.clauses.length + 1 →
      (probe m').ret = true → (probe m).ret = true := by
    intro m m' _ hmm' _ hm'
    exact (hprobe m).mpr (hmm'.trans ((hprobe m').mp hm'))
  obtain ⟨hlo, hhi, htrue, hfalse⟩ :=
    lowerBoundM_spec probe (lo := 1) (hi := F.clauses.length + 1) hmono
  have hopt_le : F.optimum ≤ F.clauses.length := optimum_le (F.numVars, F.clauses)
  simp only [optimumByBinarySearchM, TimeM.ret_bind, TimeM.ret_pure]
  set r := (lowerBoundM probe 1 (F.clauses.length + 1)).ret
  have hr_hi : r ≤ F.clauses.length + 1 := by omega
  by_cases hr1 : r = 1
  · rw [hr1]
    rcases Nat.eq_zero_or_pos F.clauses.length with hm0 | hmpos
    · omega
    · have hf := hfalse 1 (by omega) (by omega)
      have hnot : ¬ (1 ≤ F.optimum) := fun h => by
        rw [(hprobe 1).mpr h] at hf
        exact Bool.noConfusion hf
      omega
  · have hr_gt : 1 < r := by omega
    have hge : r - 1 ≤ F.optimum := (hprobe (r - 1)).mp (htrue (r - 1) (by omega) (by omega))
    by_cases hrm : r = F.clauses.length + 1
    · omega
    · have hf := hfalse r le_rfl (by omega)
      have hnot : ¬ (r ≤ F.optimum) := fun h => by
        rw [(hprobe r).mpr h] at hf
        exact Bool.noConfusion hf
      omega

/-- **Query-cost bound for binary-search optimization:** if `solveM` costs at most `C` ticks on
every 3-CNF of at most `thresholdVarBudget F.workSize` variables, then `optimumByBinarySearchM`
costs at most `C * (Nat.log 2 F.clauses.length + 1)` ticks (`≤ ⌊log₂ m⌋ + 1` solver calls). -/
theorem optimumByBinarySearchM_time_le {solveM : CNF ℕ → TimeM ℕ Bool} (F : StructInstance)
    {C : ℕ}
    (hcost : ∀ φ : CNF ℕ, (∀ c ∈ φ, c.length ≤ 3) → φ.numVars ≤ thresholdVarBudget F.workSize →
      (solveM φ).time ≤ C) :
    (optimumByBinarySearchM solveM F).time ≤ C * (Nat.log 2 F.clauses.length + 1) := by
  simp only [optimumByBinarySearchM, TimeM.time_bind, TimeM.time_pure, add_zero]
  have h := lowerBoundM_time_le (fun q => solveM (thresholdToCNF ⟨F, q⟩))
    (fun q => hcost _ (fun _ hcl => length_clause_mem_thresholdToCNF ⟨F, q⟩ hcl)
      (numVars_thresholdToCNF_le ⟨F, q⟩))
    1 (F.clauses.length + 1)
  simpa only [Nat.add_sub_cancel_right] using h

/-- **End-to-end subsampled sparse MAX-`w`-SAT optimization via a supplied fixed-width SAT solver.**
Drawing `s` clauses uniformly from `F` (`0 < F.clauses.length`, clause width `≤ w`) and running
`optimumByBinarySearchM solveM (F.sample ω)` (`3 ≤ k`):
1. invokes `solveM` only on 3-CNFs of at most `thresholdVarBudget ((w + 1) * s)` variables, within
   total cost
   `C * (Nat.log 2 s + 1)` when `solveM` costs `≤ C` on such formulas; and
2. with probability at least `1 - 2 ^ (F.numVars + 1) * exp (-2 * s * δ ^ 2)`, estimates `F.optimum`
   within `δ * m` after `(m / s)` rescaling and certifies `2 * δ * m` optimality loss for every
   sampled maximizer. -/
theorem sample_optimumByBinarySearchM_spec {k w : ℕ} (hk : 3 ≤ k)
    {solveM : CNF ℕ → TimeM ℕ Bool}
    (hspec : ∀ φ : CNF ℕ, (∀ c ∈ φ, c.length ≤ k) → ((solveM φ).ret = true ↔ φ.Satisfiable))
    {F : StructInstance} (hm : 0 < F.clauses.length) (hw : ∀ c ∈ F.clauses, c.length ≤ w)
    (s : ℕ) {C : ℕ}
    (hcost : ∀ φ : CNF ℕ, (∀ c ∈ φ, c.length ≤ 3) → φ.numVars ≤ thresholdVarBudget ((w + 1) * s) →
      (solveM φ).time ≤ C)
    {δ : ℝ} (hδ : 0 ≤ δ) :
    (∀ ω : Fin s → Fin F.clauses.length,
      (optimumByBinarySearchM solveM (F.sample ω)).time ≤ C * (Nat.log 2 s + 1)) ∧
    1 - 2 ^ (F.numVars + 1) * Real.exp (-2 * (s : ℝ) * δ ^ 2) ≤
      ((F.samplePMF hm s).toOuterMeasure
        {ω | (∀ xHat : BitString F.numVars,
            (∀ x, (F.sample ω).score x ≤ (F.sample ω).score xHat) →
              (F.optimum : ℝ) - (F.score xHat : ℝ) ≤ 2 * δ * (F.clauses.length : ℝ)) ∧
          |(F.clauses.length : ℝ) / (s : ℝ) *
              ((optimumByBinarySearchM solveM (F.sample ω)).ret : ℝ) -
            (F.optimum : ℝ)| ≤ δ * (F.clauses.length : ℝ)}).toReal := by
  refine ⟨fun ω => ?_, ?_⟩
  · have ht := optimumByBinarySearchM_time_le (F.sample ω) (C := C) fun φ h3 hvars =>
      hcost φ h3 (hvars.trans (thresholdVarBudget_mono (F.workSize_sample_le_of_width hw ω)))
    simpa only [StructInstance.sample, List.length_ofFn] using ht
  · have hret : ∀ ω : Fin s → Fin F.clauses.length,
        (optimumByBinarySearchM solveM (F.sample ω)).ret = (F.sample ω).optimum :=
      fun ω => optimumByBinarySearchM_ret hk hspec (F.sample ω)
    simp_rw [hret]
    exact F.one_sub_le_sample_good hm s hδ

/-! ### Witness recovery by unit-clause prefix pinning (`⌊log₂ m⌋ + 1 + n` solver queries) -/

private theorem eval_unit_clause_iff {n : ℕ} (x : BitString n) {j : ℕ} (hj : j < n) (bit : Bool) :
    Clause.eval (assignment n x) [(j, bit)] = true ↔ x ⟨j, hj⟩ = bit := by
  simp only [Clause.eval, List.any_cons, List.any_nil, Bool.or_false, Literal.eval_mk, assignment,
    hj, ↓reduceDIte, beq_iff_eq]

private theorem le_optimum_append_iff (F : StructInstance) (acc : CNF ℕ) :
    acc.length + F.optimum ≤ (StructInstance.mk F.numVars (acc ++ F.clauses)).optimum ↔
      ∃ x : BitString F.numVars, F.score x = F.optimum ∧
        ∀ c ∈ acc, Clause.eval (assignment F.numVars x) c = true := by
  rw [show (StructInstance.mk F.numVars (acc ++ F.clauses)).optimum =
      optimum (F.numVars, acc ++ F.clauses) from rfl,
    ← thresholdCount_pos_iff_le_optimum, thresholdCount_pos_iff]
  refine exists_congr fun x => ?_
  have hscore : score (F.numVars, acc ++ F.clauses) x =
      acc.countP (Clause.eval (assignment F.numVars x)) + F.score x := by
    simp only [StructInstance.score, score, StructInstance.toPair, List.countP_append]
  have hle_acc : acc.countP (Clause.eval (assignment F.numVars x)) ≤ acc.length :=
    List.countP_le_length
  have hle_opt : F.score x ≤ F.optimum := score_le_optimum F.toPair x
  rw [hscore]
  refine ⟨fun h => ?_, fun ⟨hopt, hall⟩ => ?_⟩
  · have heq_acc : acc.countP (Clause.eval (assignment F.numVars x)) = acc.length := by omega
    exact ⟨by omega, List.countP_eq_length.mp heq_acc⟩
  · rw [List.countP_eq_length.mpr hall, hopt]

private def recoverWitnessLoopM (solveM : CNF ℕ → TimeM ℕ Bool) (F : StructInstance)
    (opt : ℕ) : ℕ → ℕ → CNF ℕ → (ℕ → Bool) → TimeM ℕ (ℕ → Bool)
  | _, 0, _, σ => return σ
  | i, rem + 1, acc, σ => do
    let cand : CNF ℕ := [(i, true)] :: acc
    let b ← solveM (thresholdToCNF ⟨⟨F.numVars, cand ++ F.clauses⟩, cand.length + opt⟩)
    recoverWitnessLoopM solveM F opt (i + 1) rem ([(i, b)] :: acc)
      (fun v => if v = i then b else σ v)

private theorem recoverWitnessLoopM_spec {k : ℕ} (hk : 3 ≤ k)
    {solveM : CNF ℕ → TimeM ℕ Bool}
    (hspec : ∀ φ : CNF ℕ, (∀ c ∈ φ, c.length ≤ k) → ((solveM φ).ret = true ↔ φ.Satisfiable))
    (F : StructInstance) {i rem : ℕ} (hi_rem : i + rem = F.numVars)
    (acc : CNF ℕ) (σ : ℕ → Bool)
    (hacc_mem : ∀ j < i, [(j, σ j)] ∈ acc)
    (hinv : ∃ x : BitString F.numVars, F.score x = F.optimum ∧
      ∀ c ∈ acc, Clause.eval (assignment F.numVars x) c = true) :
    let σOut := (recoverWitnessLoopM solveM F F.optimum i rem acc σ).ret
    F.score (fun j => σOut j.val) = F.optimum := by
  induction rem generalizing i acc σ with
  | zero =>
    obtain ⟨x, hx_opt, hx_acc⟩ := hinv
    have hi_eq : i = F.numVars := by omega
    have hxeq : (fun j : Fin F.numVars => σ j.val) = x := by
      funext j
      have hj_mem : [(j.val, σ j.val)] ∈ acc := hacc_mem j.val (by omega)
      exact ((eval_unit_clause_iff x j.isLt (σ j.val)).mp (hx_acc _ hj_mem)).symm
    simp only [recoverWitnessLoopM, TimeM.ret_pure, hxeq, hx_opt]
  | succ rem ih =>
    have hi_lt : i < F.numVars := by omega
    let cand : CNF ℕ := [(i, true)] :: acc
    let qInst : StructInstance := ⟨F.numVars, cand ++ F.clauses⟩
    have hprobe : (solveM (thresholdToCNF ⟨qInst, cand.length + F.optimum⟩)).ret = true ↔
        ∃ x : BitString F.numVars, F.score x = F.optimum ∧
          ∀ c ∈ cand, Clause.eval (assignment F.numVars x) c = true := by
      rw [hspec _ (fun _ hcl => (length_clause_mem_thresholdToCNF _ hcl).trans hk),
        satisfiable_thresholdToCNF_iff]
      exact le_optimum_append_iff F cand
    simp only [recoverWitnessLoopM, TimeM.ret_bind]
    set b := (solveM (thresholdToCNF ⟨qInst, cand.length + F.optimum⟩)).ret
    let σ' : ℕ → Bool := fun v => if v = i then b else σ v
    have hacc' : ∀ j < i + 1, [(j, σ' j)] ∈ ([(i, b)] :: acc) := by
      intro j hj
      by_cases hji : j = i
      · subst hji
        simp only [σ', ↓reduceIte, List.mem_cons, true_or]
      · have hj_lt : j < i := by omega
        simp only [σ', hji, ↓reduceIte, List.mem_cons]
        exact Or.inr (hacc_mem j hj_lt)
    have hinv' : ∃ x : BitString F.numVars, F.score x = F.optimum ∧
        ∀ c ∈ ([(i, b)] :: acc), Clause.eval (assignment F.numVars x) c = true := by
      cases hb : b
      · obtain ⟨x, hx_opt, hx_acc⟩ := hinv
        have hxi : x ⟨i, hi_lt⟩ = false := by
          by_contra hne
          have hxtrue : x ⟨i, hi_lt⟩ = true := Bool.eq_true_of_not_eq_false hne
          have hcand : ∀ c ∈ cand, Clause.eval (assignment F.numVars x) c = true := by
            intro c hc
            rcases List.mem_cons.mp hc with rfl | hmem
            · exact (eval_unit_clause_iff x hi_lt true).mpr hxtrue
            · exact hx_acc c hmem
          have hbt : b = true := hprobe.mpr ⟨x, hx_opt, hcand⟩
          rw [hb] at hbt
          exact Bool.noConfusion hbt
        refine ⟨x, hx_opt, fun c hc => ?_⟩
        rcases List.mem_cons.mp hc with rfl | hmem
        · exact (eval_unit_clause_iff x hi_lt false).mpr hxi
        · exact hx_acc c hmem
      · exact hprobe.mp hb
    exact ih (by omega) ([(i, b)] :: acc) σ' hacc' hinv'

private theorem recoverWitnessLoopM_time_le {solveM : CNF ℕ → TimeM ℕ Bool}
    (F : StructInstance) (opt : ℕ) {C : ℕ}
    (hcost : ∀ φ : CNF ℕ, (∀ c ∈ φ, c.length ≤ 3) →
      φ.numVars ≤ thresholdVarBudget (F.workSize + 2 * F.numVars) → (solveM φ).time ≤ C)
    {i rem : ℕ} (hi_rem : i + rem ≤ F.numVars) (acc : CNF ℕ) (hacc_len : acc.length = i)
    (hacc_vars : acc.vars.length = i) (σ : ℕ → Bool) :
    (recoverWitnessLoopM solveM F opt i rem acc σ).time ≤ C * rem := by
  induction rem generalizing i acc σ with
  | zero => simp only [recoverWitnessLoopM, TimeM.time_pure, Nat.mul_zero, le_rfl]
  | succ rem ih =>
    let q : ThresholdQuery :=
      ⟨⟨F.numVars, ([(i, true)] :: acc) ++ F.clauses⟩, ([(i, true)] :: acc).length + opt⟩
    have hws_q : q.workSize ≤ F.workSize + 2 * F.numVars := by
      dsimp only [q]
      simp only [ThresholdQuery.workSize, StructInstance.workSize, MaxSAT.workSize,
        StructInstance.toPair, CNF.vars, List.flatten_cons, List.flatten_append,
        List.map_append, List.length_append, List.map_cons, List.map_nil, List.length_cons,
        List.length_nil] at hacc_vars ⊢
      omega
    have hnv_q : (thresholdToCNF q).numVars ≤ thresholdVarBudget (F.workSize + 2 * F.numVars) :=
      (numVars_thresholdToCNF_le q).trans (thresholdVarBudget_mono hws_q)
    have hstep : (solveM (thresholdToCNF q)).time ≤ C :=
      hcost (thresholdToCNF q) (fun _ hcl => length_clause_mem_thresholdToCNF q hcl) hnv_q
    dsimp only [q] at hstep
    simp only [recoverWitnessLoopM, TimeM.time_bind]
    set b := (solveM (thresholdToCNF
      ⟨⟨F.numVars, ([(i, true)] :: acc) ++ F.clauses⟩, ([(i, true)] :: acc).length + opt⟩)).ret
    have hrec := ih (i := i + 1) (by omega) ([(i, b)] :: acc)
      (by simp only [List.length_cons, hacc_len])
      (by simp only [CNF.vars, List.flatten_cons, List.map_append, List.length_append,
            List.map_cons, List.map_nil, List.length_cons, List.length_nil] at hacc_vars ⊢
          omega)
      (fun v => if v = i then b else σ v)
    rw [Nat.mul_succ]
    omega

/-- Exact MAX-SAT optimization with witness recovery: finds `opt = F.optimum` by bisection and
constructs an assignment `xHat : BitString F.numVars` achieving `F.score xHat = F.optimum` using at
most `⌊log₂ m⌋ + 1 + n` calls to a supplied `k`-SAT oracle (`3 ≤ k`). -/
def optimizeByBinarySearchM (solveM : CNF ℕ → TimeM ℕ Bool) (F : StructInstance) :
    TimeM ℕ (ℕ × BitString F.numVars) := do
  let opt ← optimumByBinarySearchM solveM F
  let σ ← recoverWitnessLoopM solveM F opt 0 F.numVars [] (fun _ => false)
  return (opt, fun j => σ j.val)

/-- **Correctness of `optimizeByBinarySearchM`:** returns `(F.optimum, xHat)` with
`F.score xHat = F.optimum` (`3 ≤ k`). -/
theorem optimizeByBinarySearchM_ret {k : ℕ} (hk : 3 ≤ k) {solveM : CNF ℕ → TimeM ℕ Bool}
    (hspec : ∀ φ : CNF ℕ, (∀ c ∈ φ, c.length ≤ k) → ((solveM φ).ret = true ↔ φ.Satisfiable))
    (F : StructInstance) :
    (optimizeByBinarySearchM solveM F).ret.1 = F.optimum ∧
      F.score (optimizeByBinarySearchM solveM F).ret.2 = F.optimum := by
  refine ⟨?_, ?_⟩
  · simp only [optimizeByBinarySearchM, TimeM.ret_bind, TimeM.ret_pure]
    exact optimumByBinarySearchM_ret hk hspec F
  · simp only [optimizeByBinarySearchM, TimeM.ret_bind, TimeM.ret_pure,
      optimumByBinarySearchM_ret hk hspec F]
    obtain ⟨xStar, hxStar⟩ := exists_score_eq_optimum F.toPair
    exact recoverWitnessLoopM_spec hk hspec F (Nat.zero_add F.numVars) [] (fun _ => false)
      (fun _ hj => absurd hj (Nat.not_lt_zero _))
      ⟨xStar, hxStar, fun _ hc => absurd hc List.not_mem_nil⟩

/-- **Query-cost bound for `optimizeByBinarySearchM`:** at most
`C * (Nat.log 2 F.clauses.length + 1 + F.numVars)` ticks when `solveM` costs `≤ C` on 3-CNFs of at
most `thresholdVarBudget (F.workSize + 2 * F.numVars)` variables. -/
theorem optimizeByBinarySearchM_time_le {solveM : CNF ℕ → TimeM ℕ Bool} (F : StructInstance)
    {C : ℕ}
    (hcost : ∀ φ : CNF ℕ, (∀ c ∈ φ, c.length ≤ 3) →
      φ.numVars ≤ thresholdVarBudget (F.workSize + 2 * F.numVars) → (solveM φ).time ≤ C) :
    (optimizeByBinarySearchM solveM F).time ≤
      C * (Nat.log 2 F.clauses.length + 1 + F.numVars) := by
  simp only [optimizeByBinarySearchM, TimeM.time_bind, TimeM.time_pure, add_zero]
  have ht1 := optimumByBinarySearchM_time_le F (C := C) fun φ h3 hnv =>
    hcost φ h3 (hnv.trans (thresholdVarBudget_mono (Nat.le_add_right _ _)))
  have ht2 := recoverWitnessLoopM_time_le F (optimumByBinarySearchM solveM F).ret hcost
    (Nat.zero_add F.numVars).le [] rfl rfl (fun _ => false)
  rw [Nat.mul_add]
  omega

/-- **Sample-optimization reduction with witness recovery (`3 ≤ k`):** on an `s`-clause subsample of
a width-`w` instance `F`, `optimizeByBinarySearchM solveM (F.sample ω)` queries `solveM` only on
3-CNFs of at most `thresholdVarBudget ((w + 1) * s + 2 * F.numVars)` variables within cost
`C * (Nat.log 2 s + 1 + F.numVars)`, and with probability at least
`1 - 2 ^ (F.numVars + 1) * exp (-2 * s * δ ^ 2)` the returned pair `(optS, xHat)` estimates
`F.optimum` within `δ * m` (after `(m / s)` rescaling) and satisfies
`(F.optimum : ℝ) - (F.score xHat : ℝ) ≤ 2 * δ * m`. -/
theorem sample_optimizeByBinarySearchM_spec {k w : ℕ} (hk : 3 ≤ k)
    {solveM : CNF ℕ → TimeM ℕ Bool}
    (hspec : ∀ φ : CNF ℕ, (∀ c ∈ φ, c.length ≤ k) → ((solveM φ).ret = true ↔ φ.Satisfiable))
    {F : StructInstance} (hm : 0 < F.clauses.length) (hw : ∀ c ∈ F.clauses, c.length ≤ w)
    (s : ℕ) {C : ℕ}
    (hcost : ∀ φ : CNF ℕ, (∀ c ∈ φ, c.length ≤ 3) →
      φ.numVars ≤ thresholdVarBudget ((w + 1) * s + 2 * F.numVars) → (solveM φ).time ≤ C)
    {δ : ℝ} (hδ : 0 ≤ δ) :
    (∀ ω : Fin s → Fin F.clauses.length,
      (optimizeByBinarySearchM solveM (F.sample ω)).time ≤
        C * (Nat.log 2 s + 1 + F.numVars)) ∧
    1 - 2 ^ (F.numVars + 1) * Real.exp (-2 * (s : ℝ) * δ ^ 2) ≤
      ((F.samplePMF hm s).toOuterMeasure
        {ω | (F.optimum : ℝ) -
              (F.score (optimizeByBinarySearchM solveM (F.sample ω)).ret.2 : ℝ) ≤
              2 * δ * (F.clauses.length : ℝ) ∧
          |(F.clauses.length : ℝ) / (s : ℝ) *
              ((optimizeByBinarySearchM solveM (F.sample ω)).ret.1 : ℝ) -
            (F.optimum : ℝ)| ≤ δ * (F.clauses.length : ℝ)}).toReal := by
  refine ⟨fun ω => ?_, ?_⟩
  · have hbound := thresholdVarBudget_mono
      (Nat.add_le_add_right (F.workSize_sample_le_of_width hw ω) (2 * F.numVars))
    have ht := optimizeByBinarySearchM_time_le (F.sample ω) (C := C) fun φ h3 hnv =>
      hcost φ h3 (hnv.trans hbound)
    simpa only [StructInstance.sample, List.length_ofFn] using ht
  · refine (F.one_sub_le_sample_good hm s hδ).trans ?_
    refine Cslib.Probability.PMF.toOuterMeasure_toReal_mono (F.samplePMF hm s) fun ω hω => ?_
    obtain ⟨hopt_ret, hscore_ret⟩ := optimizeByBinarySearchM_ret hk hspec (F.sample ω)
    have hmax : ∀ x : BitString F.numVars,
        (F.sample ω).score x ≤
          (F.sample ω).score (optimizeByBinarySearchM solveM (F.sample ω)).ret.2 := by
      intro x
      rw [hscore_ret]
      exact score_le_optimum (F.sample ω).toPair x
    refine ⟨hω.1 _ hmax, ?_⟩
    rw [hopt_ret]
    exact hω.2

/-- **Sample-optimization reduction with witness recovery under the `η` sample-size condition:**
when `0 < η` and `(F.numVars + 1) * log 2 + log (1 / η) ≤ 2 * s * δ ^ 2`,
`optimizeByBinarySearchM solveM (F.sample ω)` succeeds with probability at least `1 - η`. -/
theorem sample_optimizeByBinarySearchM_spec_of_sample_size {k w : ℕ} (hk : 3 ≤ k)
    {solveM : CNF ℕ → TimeM ℕ Bool}
    (hspec : ∀ φ : CNF ℕ, (∀ c ∈ φ, c.length ≤ k) → ((solveM φ).ret = true ↔ φ.Satisfiable))
    {F : StructInstance} (hm : 0 < F.clauses.length) (hw : ∀ c ∈ F.clauses, c.length ≤ w)
    {s C : ℕ}
    (hcost : ∀ φ : CNF ℕ, (∀ c ∈ φ, c.length ≤ 3) →
      φ.numVars ≤ thresholdVarBudget ((w + 1) * s + 2 * F.numVars) → (solveM φ).time ≤ C)
    {δ η : ℝ} (hδ : 0 ≤ δ) (hη : 0 < η)
    (hs : (F.numVars + 1 : ℝ) * Real.log 2 + Real.log (1 / η) ≤ 2 * (s : ℝ) * δ ^ 2) :
    (∀ ω : Fin s → Fin F.clauses.length,
      (optimizeByBinarySearchM solveM (F.sample ω)).time ≤
        C * (Nat.log 2 s + 1 + F.numVars)) ∧
    1 - η ≤
      ((F.samplePMF hm s).toOuterMeasure
        {ω | (F.optimum : ℝ) -
              (F.score (optimizeByBinarySearchM solveM (F.sample ω)).ret.2 : ℝ) ≤
              2 * δ * (F.clauses.length : ℝ) ∧
          |(F.clauses.length : ℝ) / (s : ℝ) *
              ((optimizeByBinarySearchM solveM (F.sample ω)).ret.1 : ℝ) -
            (F.optimum : ℝ)| ≤ δ * (F.clauses.length : ℝ)}).toReal := by
  obtain ⟨ht, hprob⟩ := sample_optimizeByBinarySearchM_spec hk hspec hm hw s hcost hδ
  have heta := MaxCSP.two_pow_succ_mul_exp_le_eta hη hs
  exact ⟨ht, by linarith⟩

/-- Width-guarded exact Boolean `Max-CSP` optimum recovered via `maxCSPToStruct`. -/
@[expose] def maxCSPOptimumBounded {Rel : Type} (w : ℕ) (sem : Rel → List Bool → Bool)
    (F : MaxCSPInstance Rel ℕ) : ℕ :=
  (maxCSPToStruct w sem F).optimum + F.constraints.length - (maxCSPToStruct w sem F).clauses.length

/-- When every constraint has scope length at most `w`, `maxCSPOptimumBounded w sem F` equals
`F.optimum sem`. -/
theorem maxCSPOptimumBounded_eq_optimum {Rel : Type} {w : ℕ} (sem : Rel → List Bool → Bool)
    {F : MaxCSPInstance Rel ℕ} (hw : ∀ c ∈ F.constraints, c.scope.length ≤ w) :
    maxCSPOptimumBounded w sem F = F.optimum sem := by
  have h := optimum_maxCSPToStruct_add_length sem hw
  dsimp only [maxCSPOptimumBounded]
  omega

/-- **Polynomial-time exact bounded-arity Boolean `Max-CSP` optimization from a polynomial-time
`k`-SAT decider (`3 ≤ k`).** -/
theorem computableInPolyTime_maxCSPOptimumBounded_of_KSAT {Rel : Type} [Finite Rel]
    (encRel : Rel ↪ List Bool) (w : ℕ) (sem : Rel → List Bool → Bool) {k : ℕ} (hk : 3 ≤ k)
    {solveKSAT : CNF ℕ → Bool} (hpoly : ComputableInPolyTime solveKSAT encCNF encBool)
    (hspec : ∀ φ : CNF ℕ, (∀ c ∈ φ, c.length ≤ k) → (solveKSAT φ = true ↔ φ.Satisfiable)) :
    ComputableInPolyTime (maxCSPOptimumBounded w sem) (encMaxCSPInstance encRel) encNat := by
  have hstruct := computableInPolyTime_maxCSPToStruct encRel w sem
  have hopt := (computableInPolyTime_optimum_of_KSAT hk hpoly hspec).comp hstruct
  have hlenF_u : ComputableInPolyTime (fun F : MaxCSPInstance Rel ℕ => F.constraints.length)
      (encMaxCSPInstance encRel) encUnary := by
    exact (length_list (encConstraint encRel encNat)).comp
      (computableInPolyTime_maxCSP_constraints ComputableInPolyTime.id')
  have hlenC_u : ComputableInPolyTime
      (fun F : MaxCSPInstance Rel ℕ => (maxCSPToStruct w sem F).clauses.length)
      (encMaxCSPInstance encRel) encUnary :=
    (length_list (encList (encPair encNat encBool))).comp
      (encStructInstance_clauses_polyTime hstruct)
  exact binary_sub' (binary_add' hopt (unary_to_binary.comp hlenF_u))
    (unary_to_binary.comp hlenC_u)

/-- Exact bounded-arity Boolean `Max-CSP` optimization by binary search (`TimeM`) via
`maxCSPToStruct` and a supplied `k`-SAT oracle. -/
def optimumMaxCSPByBinarySearchM {Rel : Type} (w : ℕ) (sem : Rel → List Bool → Bool)
    (solveM : CNF ℕ → TimeM ℕ Bool) (F : MaxCSPInstance Rel ℕ) : TimeM ℕ ℕ := do
  let optCNF ← optimumByBinarySearchM solveM (maxCSPToStruct w sem F)
  return optCNF + F.constraints.length - (maxCSPToStruct w sem F).clauses.length

/-- **Correctness of `Max-CSP` binary-search optimization:** on any width-`≤ w` Boolean
`MaxCSPInstance`, `optimumMaxCSPByBinarySearchM` returns `F.optimum sem` (`3 ≤ k`). -/
theorem optimumMaxCSPByBinarySearchM_ret {Rel : Type} {w k : ℕ} (hk : 3 ≤ k)
    (sem : Rel → List Bool → Bool) {solveM : CNF ℕ → TimeM ℕ Bool}
    (hspec : ∀ φ : CNF ℕ, (∀ c ∈ φ, c.length ≤ k) → ((solveM φ).ret = true ↔ φ.Satisfiable))
    {F : MaxCSPInstance Rel ℕ} (hw : ∀ c ∈ F.constraints, c.scope.length ≤ w) :
    (optimumMaxCSPByBinarySearchM w sem solveM F).ret = F.optimum sem := by
  simp only [optimumMaxCSPByBinarySearchM, TimeM.ret_bind, TimeM.ret_pure,
    optimumByBinarySearchM_ret hk hspec]
  exact maxCSPOptimumBounded_eq_optimum sem hw

/-- **Query-cost bound for `Max-CSP` binary-search optimization.** -/
theorem optimumMaxCSPByBinarySearchM_time_le {Rel : Type} (w : ℕ) (sem : Rel → List Bool → Bool)
    {solveM : CNF ℕ → TimeM ℕ Bool} (F : MaxCSPInstance Rel ℕ) {C : ℕ}
    (hcost : ∀ φ : CNF ℕ, (∀ c ∈ φ, c.length ≤ 3) →
      φ.numVars ≤ thresholdVarBudget (maxCSPToStruct w sem F).workSize → (solveM φ).time ≤ C) :
    (optimumMaxCSPByBinarySearchM w sem solveM F).time ≤
      C * (Nat.log 2 (maxCSPToStruct w sem F).clauses.length + 1) := by
  simp only [optimumMaxCSPByBinarySearchM, TimeM.time_bind, TimeM.time_pure, add_zero]
  exact optimumByBinarySearchM_time_le (maxCSPToStruct w sem F) hcost

end Cslib.Complexity.MaxSAT
