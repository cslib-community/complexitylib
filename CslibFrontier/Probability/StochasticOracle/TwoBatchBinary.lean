/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.StochasticOracle.TwoBatchNativeCorrectness
public import CslibFrontier.Probability.StochasticOracle.TwoBatchResources
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.Bounds
import CslibFrontier.Computability.GenericRAM.Native.Certificate
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.Constructible
import CslibFrontier.Computability.GenericRAM.Native.Combinators
import CslibFrontier.Tactic.PolyTime
import Mathlib.Tactic

/-!
# Binary-input runtime of two-batch approximation

The external input consists only of binary rational tolerance, deadline and the
ordered opportunity triples. The algorithm computes an inverse-tolerance budget
in binary, writes that budget in unary with a charged native conversion, and
runs the uniform native selector. No runtime certificate is an input field.

This is the binary-input composition for [Wang2027], Theorem 2(2), PDF pp. 7–8.
The time and workspace bounds are polynomial in input bit length and inverse
tolerance, not in the numerical input costs or probability denominators. The
input length explicitly charges the rational tolerance's binary representation.

## Main definitions

* `BinaryInput`, `encBinaryInput`: the external binary rational input.
* `runSchedule`: precision preparation and explicit native output of both batches.
* `run`: its first-batch selector.
* `selectedProgram`: oracle execution of the batches returned by the selector.

## Main results

* `run_runtime`, `runtimeSize_ofInstance`: derived native binary-input resource bounds.
* `run_eq`: exact agreement with the indexed selector on valid inputs.
* `selectedProgram_law`: actual stopped execution of the returned schedule.
* `fptas`: runtime, attained optimum, savings, cost, deadline and maximum success.
-/

public section
namespace Cslib.Probability.StochasticOracle.TwoBatchNative
open Cslib.Algorithms.Lean.DynamicProgramming.MinProduct
open Cslib.GenericRAM
open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime

/-- The external binary input. The population length and precision budget are
computed by the algorithm; neither is supplied as auxiliary advice. -/
structure BinaryInput where
  /-- Rational approximation tolerance. -/
  epsilon : ℚ
  /-- Prescribed cutoff deadline. -/
  deadline : ℚ
  /-- Ordered probability/cost/cutoff triples. -/
  calls : List (ℚ × ℚ × ℚ)
  deriving DecidableEq

/-- Exactly the paper's binary input, with standard pair/list framing. -/
@[expose] def encBinaryInput : BinaryInput ↪ List Bool :=
  (⟨fun x => (x.epsilon,x.deadline,x.calls), fun x y h => by
    cases x; cases y
    simpa using h⟩ : BinaryInput ↪ ℚ × ℚ × List (ℚ × ℚ × ℚ)).trans
      (encPair encRatBin (encPair encRatBin
        (encList (encPair encRatBin (encPair encRatBin encRatBin)))))

private theorem binary_fields : ComputableInPolyTime
    (fun x : BinaryInput => (x.epsilon,x.deadline,x.calls)) encBinaryInput
    (encPair encRatBin (encPair encRatBin
      (encList (encPair encRatBin (encPair encRatBin encRatBin))))) := .of_eq fun _ => rfl

/-- A total inverse-accuracy budget, computed from the rational tolerance.
For positive tolerance it exceeds its reciprocal by at most one. -/
@[expose] def precision (x : BinaryInput) : ℕ := (⌊x.epsilon⁻¹⌋₊ : ℕ) + 1

/-- Construct the internal input once the charged unary budget is available. -/
@[expose] def prepare (x : BinaryInput) : Input :=
  ⟨x.epsilon,x.deadline,precision x,x.calls⟩

/-- The complete deterministic algorithm on the external binary input. -/
@[expose] def run (x : BinaryInput) : List ℕ := choose (prepare x)

/-- Emit both batches, including the charged final complement scan. -/
@[expose] def runSchedule (x : BinaryInput) : List ℕ × List ℕ := schedule (prepare x)

/-- Size measure for the FPTAS, separating binary input length from the numerical
inverse-tolerance budget. The algorithm computes the budget itself. -/
@[expose] def runtimeSize (x : BinaryInput) : ℕ :=
  (encBinaryInput x).length + precision x

private theorem precision_binary : ComputableInPolyTime precision encBinaryInput encNat := by
  have he := binary_fields.fst'
  have hi := ratBin_inv.comp he
  have hf := ratBin_floor.comp hi
  have h := binary_add.comp (hf.prod (const 1))
  change ComputableInPolyTime (fun x => (⌊x.epsilon⁻¹⌋₊ : ℕ) + 1) encBinaryInput encNat
  simpa only [Function.comp_def] using h

private theorem padded_choose : ComputableInPolyTime
    (fun p : BinaryInput × ℕ => schedule (⟨p.1.epsilon,p.1.deadline,p.2,p.1.calls⟩ : Input))
    (encPair encBinaryInput encUnary) (encPair (encList encUnary) (encList encUnary)) := by
  have hx := binary_fields.comp (fst encBinaryInput encUnary)
  have hfields := hx.fst'.prod (hx.snd'.fst'.prod ((snd _ _).prod hx.snd'.snd'))
  have hmk : ComputableInPolyTime
      (fun p : ℚ × ℚ × ℕ × List (ℚ × ℚ × ℚ) =>
        (⟨p.1,p.2.1,p.2.2.1,p.2.2.2⟩ : Input))
      (encPair encRatBin (encPair encRatBin
        (encPair encUnary (encList (encPair encRatBin (encPair encRatBin encRatBin))))))
      encInput := .of_eq fun _ => rfl
  have h := computable_schedule.comp (hmk.comp hfields)
  simpa only [Function.comp_def] using h

/-- The actual binary-input implementation has time and workspace bounded by
polynomials in `runtimeSize`. The proof composes the complete selector with
native rational precision computation and binary-to-unary conversion. The
machine and polynomial bounds are derived, not assumed as a compiler field. -/
theorem run_runtime : ∃ t s : BinaryInput → ℕ,
    ComputableInO runSchedule encBinaryInput (encPair (encList encUnary) (encList encUnary)) t s ∧
      PolyBounded runtimeSize t ∧ PolyBounded runtimeSize s := by
  let cb := NativeCertificate.ofPolyTime precision_binary
  let ca := NativeCertificate.ofPolyTime padded_choose
  have hcb := NativeCertificate.ofPolyTime_isPolynomial precision_binary
  have hca := NativeCertificate.ofPolyTime_isPolynomial padded_choose
  have hlength : PolyBounded runtimeSize (fun x => (encBinaryInput x).length) :=
    (PolyBounded.self (size := runtimeSize)).mono (by intro x; exact Nat.le_add_right _ _)
  have hp : PolyBounded runtimeSize precision :=
    (PolyBounded.self (size := runtimeSize)).mono (by intro x; exact Nat.le_add_left _ _)
  have hword : PolyBounded runtimeSize
      (fun x => (encPair encBinaryInput encUnary (x,precision x)).length) := by
    simp only [length_encPair, encUnary_apply, List.length_replicate]
    exact (((PolyBounded.const 2).mul hlength).add (.const 1)).add hp
  have ht : PolyBounded runtimeSize
      (fun x => (encBinaryInput x).length + (cb.time x + (precision x + 1) ^ 2) +
        ca.time (x,precision x)) :=
    (hlength.add ((hcb.1.comp hlength).add ((hp.add (.const 1)).pow 2))).add
      (hca.1.comp hword)
  have hs : PolyBounded runtimeSize
      (fun x => (encBinaryInput x).length + (cb.space x + precision x) +
        ca.space (x,precision x)) :=
    (hlength.add ((hcb.2.comp hlength).add hp)).add (hca.2.comp hword)
  have hb := ComputableInO.natToUnary.comp cb.computes
  have hid : ComputableInO (id : BinaryInput → BinaryInput) encBinaryInput encBinaryInput
      (fun x => (encBinaryInput x).length) (fun x => (encBinaryInput x).length) :=
    ComputableInO.of_linear (.of_eq fun _ => rfl)
  have h := ca.computes.comp (hid.prod hb)
  refine ⟨_,_,?_,ht,hs⟩
  unfold runSchedule prepare
  simpa only [Function.comp_def, id_eq] using h

/-- Positive tolerance makes the computed budget sufficient and bounds its
numerical magnitude by inverse tolerance plus one. -/
theorem precision_bounds (x : BinaryInput) (hε : 0 < x.epsilon) :
    1 ≤ x.epsilon * precision x ∧ (precision x : ℚ) ≤ x.epsilon⁻¹ + 1 := by
  have hlo := Nat.floor_le (inv_nonneg.mpr hε.le)
  have hhi := Nat.lt_floor_add_one (x.epsilon⁻¹)
  simp only [precision, Nat.cast_add, Nat.cast_one]
  constructor
  · have h := mul_lt_mul_of_pos_left hhi hε
    rw [mul_inv_cancel₀ (ne_of_gt hε)] at h
    exact h.le
  · linarith

/-- External binary input for an indexed scheduling instance. -/
@[expose] def BinaryInput.ofInstance {k : ℕ} (I : FullCoverInstance (Fin k) ℚ) (ε D : ℚ) :
    BinaryInput := ⟨ε,D,(List.finRange k).map (fun i => (I.success i,I.cost i,I.cutoff i))⟩

/-- The runtime size is the original binary input length plus a computed budget
at most inverse tolerance plus one. -/
theorem runtimeSize_ofInstance {k : ℕ} (I : FullCoverInstance (Fin k) ℚ)
    {ε : ℚ} (hε : 0 < ε) (D : ℚ) :
    (runtimeSize (BinaryInput.ofInstance I ε D) : ℚ) ≤
      TwoBatchApproximation.inputSize I ε D + ε⁻¹ + 1 := by
  have h := (precision_bounds (BinaryInput.ofInstance I ε D) hε).2
  change (precision (BinaryInput.ofInstance I ε D) : ℚ) ≤ ε⁻¹ + 1 at h
  have heq : (encBinaryInput (BinaryInput.ofInstance I ε D)).length =
      TwoBatchApproximation.inputSize I ε D := rfl
  unfold runtimeSize
  push_cast
  rw [heq]
  linarith

/-- On valid input the external binary algorithm has exactly the reviewed
selector's output, with all preprocessing executed by the runtime certificate. -/
theorem run_eq {k : ℕ} (I : FullCoverInstance (Fin k) ℚ) {ε : ℚ}
    (hε : 0 < ε) (D : ℚ) :
    decode (run (BinaryInput.ofInstance I ε D)) = TwoBatchApproximation.choose I ε D := by
  let x := BinaryInput.ofInstance I ε D
  exact choose_eq I hε D (precision x) (precision_bounds x hε).1

/-- The first batch in the complete emitted schedule is the selector output. -/
@[simp] theorem runSchedule_first (x : BinaryInput) : (runSchedule x).1 = run x := rfl

/-- The complementary schedule emitted by the binary-input selector. -/
@[expose] def selectedPlan {k : ℕ} (I : FullCoverInstance (Fin k) ℚ) (ε D : ℚ) :
    Plan (Fin k) 2 :=
  let (first,second) := runSchedule (BinaryInput.ofInstance I ε D)
  (decode first,(decode second,()))

/-- Both explicitly emitted batches decode to the reviewed complementary schedule. -/
theorem selectedPlan_eq {k : ℕ} (I : FullCoverInstance (Fin k) ℚ) {ε : ℚ}
    (hε : 0 < ε) (D : ℚ) : selectedPlan I ε D =
      (TwoBatchApproximation.choose I ε D,((TwoBatchApproximation.choose I ε D)ᶜ,())) := by
  let x := BinaryInput.ofInstance I ε D
  have h := schedule_eq I hε D (precision x) (precision_bounds x hε).1
  have hfirst := congrArg Prod.fst h
  have hsecond := congrArg Prod.snd h
  exact Prod.ext hfirst (Prod.ext hsecond rfl)

/-- Execute the selected batches, stopping on the first accepted full cover.
Private randomness is unnecessary for the deterministic approximation selector. -/
noncomputable def selectedProgram {k : ℕ} (I : FullCoverInstance (Fin k) ℚ) (ε D : ℚ) :
    ProbOracleComp (fun _ : Finset (Fin k) => Bool) (Bool × Plan (Fin k) 2) :=
  followProgram (selectedPlan I ε D)

/-- The actual selected oracle program has the stopped execution law used by
the success, deadline and billed-cost guarantees. -/
theorem selectedProgram_law {k : ℕ} (I : FullCoverInstance (Fin k) ℚ) (ε D : ℚ) :
    programLaw I.realify (selectedProgram I ε D) =
      ((followPlan (K := ℝ) (selectedPlan I ε D)).execution I.realify).toPMF :=
  follow_program_law I.realify (selectedPlan I ε D)

/-- Theorem 2(2) of [Wang2027], PDF pp. 7–8, on the finite failure-oblivious
full-cover model: one uniform binary-input algorithm has polynomial runtime in
input bit length and inverse tolerance, and its actual output meets the deadline,
attains maximum success and approximates optimal two-turn savings. The optimum
is derived over arbitrary real private randomization. Local computation time is
excluded from the cutoff deadline, as in the source model. -/
theorem fptas :
    (∃ t s : BinaryInput → ℕ,
      ComputableInO runSchedule encBinaryInput (encPair (encList encUnary) (encList encUnary)) t s ∧
        PolyBounded runtimeSize t ∧ PolyBounded runtimeSize s) ∧
    ∀ {k : ℕ} (I : FullCoverInstance (Fin k) ℚ) {ε D : ℚ},
      0 < k → 0 < ε → ε < 1 → I.batchDuration Finset.univ ≤ D →
      let A : Finset (Fin k) := decode (run (BinaryInput.ofInstance I ε D))
      ∃ cstar : ℝ,
        (∃ π : Policy (Fin k) ℝ 2, π.Feasible I.realify (D : ℝ) ∧
          (π.execution I.realify).mean executionSuccess =
            1 - I.realify.batchFailure Finset.univ ∧
          (π.execution I.realify).mean (executionCost I.realify) = cstar) ∧
        (∀ π : Policy (Fin k) ℝ 2, π.Feasible I.realify (D : ℝ) →
          (π.execution I.realify).mean executionSuccess =
            1 - I.realify.batchFailure Finset.univ →
          cstar ≤ (π.execution I.realify).mean (executionCost I.realify)) ∧
        Plan.Feasible I (n := 2) (A,(Aᶜ,())) D ∧
        Plan.success I (n := 2) (A,(Aᶜ,())) = 1 - I.batchFailure Finset.univ ∧
        (1 - (ε : ℝ)) * ((I.batchCost Finset.univ : ℝ) - cstar) ≤
          (TwoBatchApproximation.gain I A : ℝ) ∧
        ((Plan.expectedCost I (n := 2) (A,(Aᶜ,())) : ℚ) : ℝ) ≤
          cstar + (ε : ℝ) * ((I.batchCost Finset.univ : ℝ) - cstar) := by
  refine ⟨run_runtime,?_⟩
  intro k I ε D hk hε hε' hD
  dsimp only
  rw [run_eq I hε D]
  exact TwoBatchApproximation.choose_optimum_guarantees I hk hε hε' hD

end Cslib.Probability.StochasticOracle.TwoBatchNative
