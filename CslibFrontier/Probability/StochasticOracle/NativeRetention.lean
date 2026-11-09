/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.StochasticOracle.PartialCover
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Unary
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Rat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeLoops
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListPrimitives
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListToBits
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List.Size
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Tactic.PolyTime
import Mathlib.Tactic

/-!
# Uniform native rational retention and output phase

[Wang2027], Lemma 1 and Theorem 5(1), PDF pp. 9,12, Appendix A.3/A.5 pp. 15,16.
The runtime input contains a rational weighted set system, a proposed dual vector,
a rational certification factor and decoded proposal index lists. The algorithm
actually computes coverage differences, rational certification and retention. No
acceptance table, native machine or output-correctness certificate is an input.

## Main results

* `computable_decision`: uniform native completion and retention/output computation.
* `compiled_output`: the derived machine halts and writes the actual mask.

This is the native local phase of the upper selector. Reading raw concurrent
reports from native query channels and executing the adaptive query/stopping loop
remain separate obligations. An offline proposal list is not a realized oracle policy.
-/

public section
namespace Cslib.Probability.StochasticOracle.NativeRetention
open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime

/-- Runtime finite rational set system and chronological decoded proposals.
Element and candidate indices are unary; weights, dual prices and factor are binary rationals. -/
structure Input where
  /-- Candidate incidence rows. -/
  rows : List (List ℕ)
  /-- Candidate weights, defaulting to zero beyond the supplied list. -/
  weights : List ℚ
  /-- Element prices; their list length defines the finite ground. -/
  dual : List ℚ
  /-- Requested local approximation factor. -/
  rho : ℚ
  /-- Actual proposed subfamilies, to be normalized to valid candidate indices. -/
  proposals : List (List ℕ)
  deriving DecidableEq

/-- Concrete framed runtime encoding; no certificate or computation witness is encoded. -/
@[expose] def encInput : Input ↪ List Bool :=
  (⟨fun x => (x.rows, x.weights, x.dual, x.rho, x.proposals), fun x y h => by
    cases x; cases y; simpa using h⟩ :
      Input ↪ List (List ℕ) × List ℚ × List ℚ × ℚ × List (List ℕ)).trans
    (encPair (encList (encList encUnary)) (encPair (encList encRatBin)
      (encPair (encList encRatBin) (encPair encRatBin (encList (encList encUnary))))))

/-- All legal candidate indices, enumerated from runtime incidence data. -/
@[expose] def population (x : Input) : List ℕ := List.range x.rows.length
/-- All ground elements, enumerated from the runtime dual vector. -/
@[expose] def ground (x : Input) : List ℕ := List.range x.dual.length
/-- Normalize proposals without counting duplicate or out-of-range candidates. -/
@[expose] def normalize (x : Input) (P : List ℕ) : List ℕ :=
  (population x).filter fun j => decide (j ∈ P)
/-- Actual covered-element scan; out-of-range rows are empty. -/
@[expose] def covered (x : Input) (C : List ℕ) : List ℕ :=
  (ground x).filter fun e => C.any fun j => decide (e ∈ x.rows.getD j [])
/-- Newly covered elements relative to the already retained family. -/
@[expose] def newly (x : Input) (C P : List ℕ) : List ℕ :=
  (covered x (normalize x P)).filter fun e => !(decide (e ∈ covered x C))
/-- Sum actual binary rational candidate weights, counting each proposed candidate once. -/
@[expose] def cost (x : Input) (P : List ℕ) : ℚ :=
  ((normalize x P).map fun j => x.weights.getD j 0).sum
/-- Sum actual dual prices on newly covered elements. -/
@[expose] def price (x : Input) (C P : List ℕ) : ℚ :=
  ((newly x C P).map fun e => x.dual.getD e 0).sum
/-- Executable local dual test, rather than a supplied certification predicate. -/
@[expose] def certified (x : Input) (C P : List ℕ) : Bool :=
  !(newly x C P).isEmpty && decide (cost x P ≤ x.rho * price x C P)
/-- Accept exactly locally certified proposals and retain the union once. -/
@[expose] def step (x : Input) (C P : List ℕ) : List ℕ :=
  if certified x C P then (population x).filter fun j => decide (j ∈ C) || decide (j ∈ P) else C
/-- Execute the local retention phase from an empty family. -/
@[expose] def retain (x : Input) : List ℕ := x.proposals.foldl (step x) []
/-- Emit the actual candidate membership mask used by the native source output codec. -/
@[expose] def output (x : Input) : List Bool := (population x).map fun j => decide (j ∈ retain x)

/-- Actual completion test for a subsequent query/stop decision. This does not
assume that the proposed families cover the ground. -/
@[expose] def complete (x : Input) : Bool :=
  (ground x).all fun e => decide (e ∈ covered x (retain x))

private theorem fields_computable : ComputableInPolyTime
    (fun x : Input => (x.rows,x.weights,x.dual,x.rho,x.proposals)) encInput
    (encPair (encList (encList encUnary)) (encPair (encList encRatBin)
      (encPair (encList encRatBin) (encPair encRatBin (encList (encList encUnary)))))) :=
  .of_eq fun _ => rfl

private theorem rows_computable : ComputableInPolyTime Input.rows encInput
    (encList (encList encUnary)) := fields_computable.fst'
private theorem weights_computable : ComputableInPolyTime Input.weights encInput
    (encList encRatBin) := fields_computable.snd'.fst'
private theorem dual_computable : ComputableInPolyTime Input.dual encInput
    (encList encRatBin) := fields_computable.snd'.snd'.fst'
private theorem rho_computable : ComputableInPolyTime Input.rho encInput encRatBin :=
  fields_computable.snd'.snd'.snd'.fst'
private theorem proposals_computable : ComputableInPolyTime Input.proposals encInput
    (encList (encList encUnary)) := fields_computable.snd'.snd'.snd'.snd'
attribute [local fun_prop] rows_computable weights_computable dual_computable
  rho_computable proposals_computable

private theorem population_computable : ComputableInPolyTime population encInput
    (encList encUnary) := by unfold population; fun_prop
private theorem ground_computable : ComputableInPolyTime ground encInput
    (encList encUnary) := by unfold ground; fun_prop
attribute [local fun_prop] population_computable ground_computable

private theorem normalize_computable : ComputableInPolyTime
    (fun p : Input × List ℕ => normalize p.1 p.2) (encPair encInput (encList encUnary))
    (encList encUnary) := by
  unfold normalize
  apply filterWithInput (by fun_prop)
  fun_prop

private theorem covered_computable : ComputableInPolyTime
    (fun p : Input × List ℕ => covered p.1 p.2) (encPair encInput (encList encUnary))
    (encList encUnary) := by
  unfold covered
  apply filterWithInput (by fun_prop)
  apply anyWithInput (by fun_prop)
  fun_prop

attribute [local fun_prop] normalize_computable covered_computable

private theorem newly_computable : ComputableInPolyTime
    (fun p : (Input × List ℕ) × List ℕ => newly p.1.1 p.1.2 p.2)
    (encPair (encPair encInput (encList encUnary)) (encList encUnary)) (encList encUnary) := by
  unfold newly
  apply filterWithInput (by fun_prop)
  fun_prop

private theorem cost_computable : ComputableInPolyTime (fun p : Input × List ℕ => cost p.1 p.2)
    (encPair encInput (encList encUnary)) encRatBin := by unfold cost; fun_prop

attribute [local fun_prop] newly_computable cost_computable

private theorem price_computable : ComputableInPolyTime
    (fun p : (Input × List ℕ) × List ℕ => price p.1.1 p.1.2 p.2)
    (encPair (encPair encInput (encList encUnary)) (encList encUnary)) encRatBin := by
  unfold price
  fun_prop

attribute [local fun_prop] price_computable

private theorem certified_computable : ComputableInPolyTime
    (fun p : (Input × List ℕ) × List ℕ => certified p.1.1 p.1.2 p.2)
    (encPair (encPair encInput (encList encUnary)) (encList encUnary)) encBool := by
  have hl : ComputableInPolyTime (fun p : (Input × List ℕ) × List ℕ => cost p.1.1 p.2)
      (encPair (encPair encInput (encList encUnary)) (encList encUnary)) encRatBin := by fun_prop
  have hr : ComputableInPolyTime
      (fun p : (Input × List ℕ) × List ℕ => p.1.1.rho * price p.1.1 p.1.2 p.2)
      (encPair (encPair encInput (encList encUnary)) (encList encUnary)) encRatBin := by fun_prop
  have hc := ratBin_le.comp (hl.prod hr)
  have hn : ComputableInPolyTime
      (fun p : (Input × List ℕ) × List ℕ => !(newly p.1.1 p.1.2 p.2).isEmpty)
      (encPair (encPair encInput (encList encUnary)) (encList encUnary)) encBool := by fun_prop
  have hb : ComputableInPolyTime (fun p : Bool × Bool => p.1 && p.2)
      (encPair encBool encBool) encBool := by fun_prop
  exact hb.comp (hn.prod hc)

private theorem step_computable : ComputableInPolyTime
    (fun p : (Input × List ℕ) × List ℕ => step p.1.1 p.1.2 p.2)
    (encPair (encPair encInput (encList encUnary)) (encList encUnary)) (encList encUnary) := by
  have hc := certified_computable
  have hu : ComputableInPolyTime
      (fun p : (Input × List ℕ) × List ℕ =>
        (population p.1.1).filter fun j => decide (j ∈ p.1.2) || decide (j ∈ p.2))
      (encPair (encPair encInput (encList encUnary)) (encList encUnary)) (encList encUnary) := by
    apply filterWithInput (by fun_prop)
    fun_prop
  exact hc.ite hu (by fun_prop)

/-- The retention loop is compiled uniformly, including its state-size bound.
No intermediate accumulator-size certificate is supplied by the caller. -/
theorem computable_retain : ComputableInPolyTime retain encInput (encList encUnary) := by
  apply foldlWithInput_of_bounded_growth (by fun_prop)
    ⟨proposals_computable, step_computable, inferInstance, inferInstance⟩
    (growth := fun x => (encList encUnary (population x)).length)
  refine ⟨population_computable.polyBounded_length, ?_⟩
  intro x C P _
  unfold step
  split_ifs
  · exact (length_encList_sublist encUnary (List.filter_sublist)).trans (Nat.le_add_left _ _)
  · omega

/-- One actual binary-alphabet finite-control native algorithm computes the
retained output mask on every runtime input, with polynomial local time and space.
This is a derived native compiler certificate, not an assumed machine witness. -/
theorem computable_output : ComputableInPolyTime output encInput encBits := by
  have hr := computable_retain
  unfold output
  exact listToBits.comp
    (mapWithInput (f := fun x j => decide (j ∈ retain x)) population_computable (by fun_prop))

/-- Native compilation of the actual completion test, for use between oracle
turns. Composition with a query loop remains a separate construction. -/
theorem computable_complete : ComputableInPolyTime complete encInput encBool := by
  have hr := computable_retain
  unfold complete
  apply allWithInput ground_computable
  fun_prop

/-- One native computation emits the completion decision and retained mask from
runtime data, with no supplied success flag. -/
theorem computable_decision : ComputableInPolyTime (fun x => (complete x, output x)) encInput
    (encPair encBool encBits) := computable_complete.prod computable_output

/-- The compiled local-phase machine and its derived resource certificate.
This package is constructed below; no package is requested from a caller. -/
structure Compiled where
  /-- Number of work tapes. -/
  tapes : ℕ
  /-- Native finite control. -/
  Control : Type
  /-- Control is finite even though runtime incidence/proposal inputs are unbounded. -/
  finiteControl : Finite Control
  /-- Actual binary-alphabet deterministic multitape machine. -/
  machine : Turing.MultiTapeTM tapes Bool Control
  /-- Uniform time bound on encoded input length. -/
  time : ℕ → ℕ
  /-- Uniform work-space bound on encoded input length. -/
  space : ℕ → ℕ
  /-- Derived polynomial time bound. -/
  time_polynomial : Cslib.PolynomiallyBounded time
  /-- Derived polynomial space bound. -/
  space_polynomial : Cslib.PolynomiallyBounded space
  /-- The machine actually computes the output on every input. -/
  correct : machine.ComputesFunInTimeAndSpace encInput encBits output
    (fun x => time (encInput x).length) (fun x => space (encInput x).length)

private theorem compiled_exists : Nonempty Compiled := by
  obtain ⟨t, s, ht, hs, k, S, hS, M, hM⟩ := computable_output
  exact ⟨⟨k, S, hS, M, t, s, ht, hs, hM⟩⟩

/-- One fixed native machine compiled from the executable retention algorithm.
Choice extracts the witness proved by native composition; existence is not assumed. -/
noncomputable def compiled : Compiled := Classical.choice compiled_exists

/-- The generated native code halts and writes the computed mask on every runtime
input; time and space are provided independently by `compiled.correct`. -/
theorem compiled_output (x : Input) : ∃ t,
    (compiled.machine.runFrom (compiled.machine.initCfg (encInput x)) t).Halted ∧
      (compiled.machine.runFrom (compiled.machine.initCfg (encInput x)) t).output = output x :=
  (compiled.correct x).1

end Cslib.Probability.StochasticOracle.NativeRetention
