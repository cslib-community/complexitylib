/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.StochasticOracle.TwoBatchIntegral
import CslibFrontier.Computability.GenericRAM.Native.Certificate
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.Constructible
import CslibFrontier.Computability.GenericRAM.Native.Combinators
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Tactic.PolyTime
import Mathlib.Tactic

/-!
# Native pseudopolynomial runtime for exact integer-cost selection

[Wang2027], Theorem 3(2), PDF p. 9, Appendix A.2, p. 15.
The external input contains binary probabilities, integer costs, cutoffs and
deadline. The algorithm computes the cost sum in binary and pays to write its
precision budget in unary before running the certified minimum-product selector.
One fixed native machine has polynomial time and workspace in input bit length
plus the numerical total cost. Both batches are explicitly emitted.
## Main results

* `runtime`: uniform native binary implementation with pseudopolynomial bounds.
* `infeasible`: a false flag excludes every maximum-success policy.
* `optimizer`: exact output feasibility, success and global minimum, including empty input.
* `selectedProgram_law`: stopped oracle execution of the emitted batches.
-/

public section
namespace Cslib.Probability.StochasticOracle.TwoBatchIntegral
open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime
open Cslib.GenericRAM

/-- External data; no unary cost advice, precision or desired runtime certificate. -/
structure Input where
  /-- Ordered success probability, integer cost and cutoff triples. -/
  calls : List (ℚ × ℕ × ℚ)
  /-- Deadline in prescribed cutoffs, excluding local computation. -/
  deadline : ℚ
  deriving DecidableEq

/-- Binary encoding of every numeric input field. -/
@[expose] def encInput : Input ↪ List Bool :=
  (⟨fun x => (x.calls,x.deadline), fun x y h => by cases x; cases y; simp_all⟩ :
    Input ↪ List (ℚ × ℕ × ℚ) × ℚ).trans
      (encPair (encList (encPair encRatBin (encPair encNat encRatBin))) encRatBin)

private theorem fields_computable : ComputableInPolyTime
    (fun x : Input => (x.calls,x.deadline)) encInput
    (encPair (encList (encPair encRatBin (encPair encNat encRatBin))) encRatBin) :=
  .of_eq fun _ => rfl

private theorem calls_computable : ComputableInPolyTime Input.calls encInput
    (encList (encPair encRatBin (encPair encNat encRatBin))) := fields_computable.fst'
private theorem deadline_computable : ComputableInPolyTime Input.deadline encInput encRatBin :=
  fields_computable.snd'

attribute [local fun_prop] calls_computable deadline_computable

/-- Exact numerical sum of the externally supplied binary costs. -/
@[expose] def totalCost (x : Input) : ℕ := (x.calls.map (fun (_,c,_) => c)).sum

/-- A sufficient precision budget, computed by the algorithm. -/
@[expose] def budget (x : Input) : ℕ := totalCost x + 2

/-- Convert positive integer costs to binary rationals and supply computed precision. -/
@[expose] def prepare (x : Input) (m : ℕ) : TwoBatchNative.Input :=
  ⟨1 / ((totalCost x : ℚ) + 1),x.deadline,m,
    x.calls.map (fun (p,c,l) => (p,(c : ℚ),l))⟩

/-- The complete algorithm, including cost summation and explicit batch reconstruction. -/
@[expose] def runSchedule (x : Input) : List ℕ × List ℕ :=
  TwoBatchNative.schedule (prepare x (budget x))

/-- Pseudopolynomial size: binary input length plus numerical total cost and two. -/
@[expose] def runtimeSize (x : Input) : ℕ := (encInput x).length + budget x

private theorem totalCost_binary : ComputableInPolyTime totalCost encInput encNat := by
  have hc : ComputableInPolyTime (fun x : Input => x.calls.map (fun (_,c,_) => c))
      encInput (encList encNat) := by fun_prop
  exact (ComputableInPolyTime.of_tidy ComputableTidilyInPolyTime.binary_sum).comp hc

private theorem budget_binary : ComputableInPolyTime budget encInput encNat := by
  exact binary_add.comp (totalCost_binary.prod (const 2))

attribute [local fun_prop] totalCost_binary

private theorem tolerance_binary : ComputableInPolyTime
    (fun x : Input => 1 / ((totalCost x : ℚ) + 1)) encInput encRatBin := by
  have hn : ComputableInPolyTime (fun x : Input => (totalCost x : ℚ)) encInput encRatBin :=
    ratBin_natCast.comp totalCost_binary
  have ha := ratBin_add.comp (hn.prod (const (1 : ℚ)))
  simpa only [Function.comp_def] using
    ratBin_div.comp ((const (1 : ℚ)).prod ha)

private theorem convertCall : ComputableInPolyTime
    (fun t : ℚ × ℕ × ℚ => (t.1,(t.2.1 : ℚ),t.2.2))
    (encPair encRatBin (encPair encNat encRatBin))
    (encPair encRatBin (encPair encRatBin encRatBin)) :=
  (fst _ _).prod ((ratBin_natCast.comp (snd _ _).fst').prod (snd _ _).snd')

private theorem converted_calls : ComputableInPolyTime
    (fun x : Input => x.calls.map (fun (q,c,l) => (q,(c : ℚ),l))) encInput
    (encList (encPair encRatBin (encPair encRatBin encRatBin))) :=
  convertCall.map.comp calls_computable

private theorem padded_schedule : ComputableInPolyTime
    (fun p : Input × ℕ => TwoBatchNative.schedule (prepare p.1 p.2))
    (encPair encInput encUnary) (encPair (encList encUnary) (encList encUnary)) := by
  have ht := tolerance_binary.comp (fst encInput encUnary)
  have hc := converted_calls.comp (fst encInput encUnary)
  have hd := deadline_computable.comp (fst encInput encUnary)
  have hfields := ht.prod (hd.prod ((snd encInput encUnary).prod hc))
  have hmk : ComputableInPolyTime
      (fun p : ℚ × ℚ × ℕ × List (ℚ × ℚ × ℚ) =>
        (⟨p.1,p.2.1,p.2.2.1,p.2.2.2⟩ : TwoBatchNative.Input))
      (encPair encRatBin (encPair encRatBin
        (encPair encUnary (encList (encPair encRatBin (encPair encRatBin encRatBin))))))
      TwoBatchNative.encInput := .of_eq fun _ => rfl
  simpa only [prepare,Function.comp_def] using
    TwoBatchNative.computable_schedule.comp (hmk.comp hfields)

/-- Derived native binary runtime, polynomial in input length and the numerical
cost sum. Binary-to-unary conversion is charged; the machine is uniform over
all populations and inputs, including invalid probability/cutoff values. -/
theorem run_runtime : ∃ t s : Input → ℕ,
    ComputableInO runSchedule encInput (encPair (encList encUnary) (encList encUnary)) t s ∧
      PolyBounded runtimeSize t ∧ PolyBounded runtimeSize s := by
  let cb := NativeCertificate.ofPolyTime budget_binary
  let ca := NativeCertificate.ofPolyTime padded_schedule
  have hcb := NativeCertificate.ofPolyTime_isPolynomial budget_binary
  have hca := NativeCertificate.ofPolyTime_isPolynomial padded_schedule
  have hlength : PolyBounded runtimeSize (fun x => (encInput x).length) :=
    (PolyBounded.self (size := runtimeSize)).mono (by intro x; exact Nat.le_add_right _ _)
  have hp : PolyBounded runtimeSize budget :=
    (PolyBounded.self (size := runtimeSize)).mono (by intro x; exact Nat.le_add_left _ _)
  have hword : PolyBounded runtimeSize
      (fun x => (encPair encInput encUnary (x,budget x)).length) := by
    simp only [length_encPair,encUnary_apply,List.length_replicate]
    exact (((PolyBounded.const 2).mul hlength).add (.const 1)).add hp
  have ht : PolyBounded runtimeSize
      (fun x => (encInput x).length + (cb.time x + budget x) +
        ca.time (x,budget x)) :=
    (hlength.add ((hcb.1.comp hlength).add hp)).add (hca.1.comp hword)
  have hs : PolyBounded runtimeSize
      (fun x => (encInput x).length + (cb.space x + budget x) +
        ca.space (x,budget x)) :=
    (hlength.add ((hcb.2.comp hlength).add hp)).add (hca.2.comp hword)
  have hb := ComputableInO.natToUnary.comp cb.computes
  have hid : ComputableInO (id : Input → Input) encInput encInput
      (fun x => (encInput x).length) (fun x => (encInput x).length) :=
    ComputableInO.of_linear (.of_eq fun _ => rfl)
  have h := ca.computes.comp (hid.prod hb)
  exact ⟨_,_,h,ht,hs⟩

/-- Serialize an actual indexed instance with integer costs. -/
@[expose] def Input.ofInstance {k : ℕ} (I : FullCoverInstance (Fin k) ℚ)
    (c : Fin k → ℕ) (D : ℚ) : Input :=
  ⟨(List.finRange k).map (fun i => (I.success i,c i,I.cutoff i)),D⟩

/-- The numerical cost sum is exactly that of the indexed instance. -/
theorem totalCost_ofInstance {k : ℕ} (I : FullCoverInstance (Fin k) ℚ)
    (c : Fin k → ℕ) (D : ℚ) : totalCost (Input.ofInstance I c D) = ∑ i, c i := by
  simp only [totalCost,Input.ofInstance,List.map_map,Function.comp_def]
  rw [← List.sum_toFinset c (List.nodup_finRange k)]
  simp

/-- Both emitted batches decode to the exact integral-cost selector. -/
theorem schedule_eq {k : ℕ} (I : FullCoverInstance (Fin k) ℚ) (c : Fin k → ℕ)
    (hc : I.cost = fun i => (c i : ℚ)) (D : ℚ) :
    let (first,second) := runSchedule (Input.ofInstance I c D)
    (TwoBatchNative.decode first,TwoBatchNative.decode second) =
      (choose I c D,(choose I c D)ᶜ) := by
  have hprep : prepare (Input.ofInstance I c D) (budget (Input.ofInstance I c D)) =
      TwoBatchNative.Input.ofInstance I (tolerance c) D ((∑ i, c i) + 2) := by
    unfold prepare budget
    rw [totalCost_ofInstance]
    simp only [Input.ofInstance,TwoBatchNative.Input.ofInstance,tolerance,
      List.map_map,Function.comp_def,hc]
  have hm : (1 : ℚ) ≤ tolerance c * ((∑ i, c i : ℕ) + 2) := by
    unfold tolerance
    rw [one_div_mul_eq_div,le_div_iff₀ (by positivity)]
    linarith
  have hm' : (1 : ℚ) ≤ tolerance c * (((∑ i, c i) + 2 : ℕ) : ℚ) := by
    exact_mod_cast hm
  have h := TwoBatchNative.schedule_eq I (tolerance_pos c) D ((∑ i, c i) + 2) hm'
  simpa only [runSchedule,hprep,choose] using h

/-- Feasibility flag. Every call must fit even in the concurrent batch; an empty
population is feasible exactly when the deadline is nonnegative. -/
@[expose] def admissible (x : Input) : Bool :=
  decide (0 ≤ x.deadline) && x.calls.all (fun (_,_,l) => decide (l ≤ x.deadline))

/-- Emit feasibility and both explicitly reconstructed batches. On false, no
maximum-success policy meets the deadline; the batch lists carry no feasibility claim. -/
@[expose] def run (x : Input) : Bool × (List ℕ × List ℕ) := (admissible x,runSchedule x)

private theorem admissible_computable : ComputableInPolyTime admissible encInput encBool := by
  have hz := ratBin_le.comp ((const (0 : ℚ)).prod deadline_computable)
  have hl : ComputableInPolyTime
      (fun p : Input × (ℚ × ℕ × ℚ) => p.2.2.2)
      (encPair encInput (encPair encRatBin (encPair encNat encRatBin))) encRatBin :=
    (snd _ _).snd'.snd'
  have hd := deadline_computable.comp
    (fst encInput (encPair encRatBin (encPair encNat encRatBin)))
  have ht := ratBin_le.comp (hl.prod hd)
  have ha := allWithInput (test := fun x : Input => fun (_,_,l) => decide (l ≤ x.deadline))
    calls_computable ht
  apply (hz.ite ha (const false)).of_enc_eq
  intro x
  change encBool (admissible x) = encBool
    (if decide (0 ≤ x.deadline) = true then
      x.calls.all (fun (_,_,l) => decide (l ≤ x.deadline)) else false)
  cases hb : decide (0 ≤ x.deadline) <;> simp [admissible,hb]

/-- The full feasibility/output algorithm has native pseudopolynomial runtime. -/
theorem runtime : ∃ t s : Input → ℕ,
    ComputableInO run encInput
      (encPair encBool (encPair (encList encUnary) (encList encUnary))) t s ∧
      PolyBounded runtimeSize t ∧ PolyBounded runtimeSize s := by
  obtain ⟨t,s,h,ht,hs⟩ := run_runtime
  let ca := NativeCertificate.ofPolyTime admissible_computable
  have hca := NativeCertificate.ofPolyTime_isPolynomial admissible_computable
  have hl : PolyBounded runtimeSize (fun x => (encInput x).length) :=
    (PolyBounded.self (size := runtimeSize)).mono (by intro x; exact Nat.le_add_right _ _)
  exact ⟨_,_,ca.computes.prod h,(hca.1.comp hl).add ht,(hca.2.comp hl).add hs⟩

/-- The flag checks the original exact deadline, including empty populations. -/
theorem admissible_ofInstance {k : ℕ} (I : FullCoverInstance (Fin k) ℚ)
    (c : Fin k → ℕ) (D : ℚ) :
    admissible (Input.ofInstance I c D) = true ↔ I.batchDuration Finset.univ ≤ D := by
  rw [I.batchDuration_le_iff]
  simp only [admissible,Input.ofInstance,Bool.and_eq_true,List.all_map,List.all_eq_true,
    List.mem_finRange,true_implies,Finset.mem_univ,Function.comp_def]
  constructor
  · rintro ⟨hz,hl⟩
    exact ⟨of_decide_eq_true hz,fun i => of_decide_eq_true (hl i)⟩
  · rintro ⟨hz,hl⟩
    exact ⟨decide_eq_true hz,fun i => decide_eq_true (hl i)⟩

/-- No false flag can hide a feasible real-randomized maximum-success policy. -/
theorem infeasible {k : ℕ} (I : FullCoverInstance (Fin k) ℚ) (c : Fin k → ℕ) (D : ℚ)
    (h : admissible (Input.ofInstance I c D) = false) :
    ¬ ∃ π : Policy (Fin k) ℝ 2, π.Feasible I.realify (D : ℝ) ∧
      (π.execution I.realify).mean executionSuccess = 1 - I.realify.batchFailure Finset.univ := by
  classical
  rintro ⟨π,hπ,hp⟩
  obtain ⟨⟨A,C,u⟩,hf,hu,_⟩ := deterministic_max_success I.realify π (D : ℝ) hπ hp
  have hA := (I.realify.batchDuration_le_iff A (I.realify.batchDuration A)).mp le_rfl
  have hC := (I.realify.batchDuration_le_iff C (I.realify.batchDuration C)).mp le_rfl
  have hD : I.realify.batchDuration Finset.univ ≤ (D : ℝ) := by
    apply (I.realify.batchDuration_le_iff _ _).mpr
    have htime : I.realify.batchDuration A + I.realify.batchDuration C ≤ (D : ℝ) := by
      simpa [Plan.duration] using hf.2
    refine ⟨by linarith [hA.1,hC.1],?_⟩
    intro i _
    have hi : i ∈ A ∨ i ∈ C := by
      have hi' : i ∈ Plan.used (n := 2) (A,(C,u)) := by
        rw [hu]
        exact Finset.mem_univ i
      simpa only [Plan.used,Finset.mem_union,Finset.notMem_empty,or_false] using hi'
    rcases hi with hi | hi
    · linarith [hA.2 i hi,hC.1]
    · linarith [hC.2 i hi,hA.1]
  rw [I.batchDuration_realify] at hD
  have hDq : I.batchDuration Finset.univ ≤ D := by exact_mod_cast hD
  have hh := (admissible_ofInstance I c D).mpr hDq
  simp [h] at hh

/-- Decode the complete native output into an executable oracle schedule. -/
@[expose] def selectedPlan {k : ℕ} (I : FullCoverInstance (Fin k) ℚ)
    (c : Fin k → ℕ) (D : ℚ) : Plan (Fin k) 2 :=
  let (first,second) := runSchedule (Input.ofInstance I c D)
  (TwoBatchNative.decode first,(TwoBatchNative.decode second,()))

private theorem selectedPlan_eq {k : ℕ} (I : FullCoverInstance (Fin k) ℚ)
    (c : Fin k → ℕ) (hc : I.cost = fun i => (c i : ℚ)) (D : ℚ) :
    selectedPlan I c D = (choose I c D,((choose I c D)ᶜ,())) := by
  have h : (TwoBatchNative.decode (k := k) (runSchedule (Input.ofInstance I c D)).1,
      TwoBatchNative.decode (k := k) (runSchedule (Input.ofInstance I c D)).2) =
      (choose I c D,(choose I c D)ᶜ) := schedule_eq I c hc D
  change (TwoBatchNative.decode (runSchedule (Input.ofInstance I c D)).1,
    (TwoBatchNative.decode (runSchedule (Input.ofInstance I c D)).2,())) = _
  exact congrArg (fun p : Finset (Fin k) × Finset (Fin k) => (p.1,(p.2,()))) h

/-- Theorem 3(2)'s exact optimum: the actual reconstructed output meets the
cutoff deadline, attains maximum success and costs no more than any feasible
maximum-success real-randomized policy. The empty instance has cost zero. -/
theorem optimizer {k : ℕ} (I : FullCoverInstance (Fin k) ℚ) (c : Fin k → ℕ)
    (hc : I.cost = fun i => (c i : ℚ)) (D : ℚ)
    (hD : admissible (Input.ofInstance I c D) = true) :
    Plan.Feasible I (selectedPlan I c D) D ∧
    Plan.success I (selectedPlan I c D) = 1 - I.batchFailure Finset.univ ∧
    ∀ π : Policy (Fin k) ℝ 2, π.Feasible I.realify (D : ℝ) →
      (π.execution I.realify).mean executionSuccess = 1 - I.realify.batchFailure Finset.univ →
      ((Plan.expectedCost I (selectedPlan I c D) : ℚ) : ℝ) ≤
        (π.execution I.realify).mean (executionCost I.realify) := by
  classical
  rw [selectedPlan_eq I c hc D]
  have hDq := (admissible_ofInstance I c D).mp hD
  by_cases hk : 0 < k
  · refine ⟨TwoBatchApproximation.choose_schedule_feasible I hk hDq,
      TwoBatchApproximation.choose_success I _ _,?_⟩
    intro π hπ hp
    have hm := choose_policy_minimum I c hc hk π hπ hp
    convert hm using 1;
      simp only [Plan.expectedCost,FullCoverInstance.twoBatchCost,mul_zero,add_zero]
    congr 3
    congr 1
    ext i
    simp
  · have hk0 : k = 0 := by omega
    subst k
    have he (A : Finset (Fin 0)) : A = ∅ := Subsingleton.elim _ _
    have ht : 0 ≤ D := by simpa [FullCoverInstance.batchDuration] using hDq
    refine ⟨?_,?_,?_⟩
    · simp [Plan.Feasible,Plan.NoReuse,Plan.used,Plan.duration,
        FullCoverInstance.batchDuration,he,ht]
    · simp [Plan.success,Plan.failure,FullCoverInstance.batchFailure,he]
    · intro π _ _
      have hzero : Plan.expectedCost I.realify (n := 2) = fun _ => 0 := by
        funext ⟨A,C,u⟩
        simp [Plan.expectedCost,FullCoverInstance.batchCost,he]
      rw [(execution_equivalence I.realify π).2,hzero]
      simp [Plan.expectedCost,FullCoverInstance.batchCost,he,
        Cslib.Optimization.OneConstraint.Distribution.mean]

/-- Execute the exact output as an oracle program, stopping at the first success. -/
noncomputable def selectedProgram {k : ℕ} (I : FullCoverInstance (Fin k) ℚ)
    (c : Fin k → ℕ) (D : ℚ) :
    ProbOracleComp (fun _ : Finset (Fin k) => Bool) (Bool × Plan (Fin k) 2) :=
  followProgram (selectedPlan I c D)

/-- The emitted schedule's actual stopped execution has the law used in `optimizer`. -/
theorem selectedProgram_law {k : ℕ} (I : FullCoverInstance (Fin k) ℚ)
    (c : Fin k → ℕ) (D : ℚ) :
    programLaw I.realify (selectedProgram I c D) =
      ((followPlan (K := ℝ) (selectedPlan I c D)).execution I.realify).toPMF :=
  follow_program_law I.realify (selectedPlan I c D)

end Cslib.Probability.StochasticOracle.TwoBatchIntegral
