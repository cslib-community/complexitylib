/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.PP.Time
public import Complexity.Computability.Complexity.Classes.Promise.Basic

/-!
# Bounded-error promise computation at a prescribed time

`PromiseBPTIME enc T` fixes a native fair-coin machine and an affine clock `c₁ * T n + c₂`
before the input. Every run halts within that clock, including off-promise runs. On yes-instances
the output is `[true]` with probability at least `2/3`, and on no-instances it is `[false]` with
probability at least `2/3`. No probability gap or answer is required outside the promise.

This is the library's time-indexed native-machine convention, extending `BPTIME` to partial
promises: a decision problem is in `PromiseBPTIME` exactly when it is in `BPTIME`. It does not
define the class through bounded-error total completions. A strict-majority completion belongs to
`PPTIME` at the same caller-supplied clock, with ties rejecting; this is not a bounded-error
completion in `BPTIME`.

The characterization by sample-and-verify and coin replay at the same clock, up to constant
factors, is in `Complexity.Computability.Complexity.Classes.Promise.Time.Verifier`.

## Main definitions

* `Turing.MultiTapePTM.SolvesPromiseWithBoundedErrorInTime`: native clock and error contract.
* `Cslib.Complexity.PromiseBPTIME`: bounded-error promise computation in affine time.

## Main results

* `Turing.MultiTapePTM.solvesPromiseWithBoundedErrorInTime_ofSet_iff`,
  `ofSet_mem_PromiseBPTIME`: on decision problems, the notions are
  `Turing.MultiTapePTM.DecidesWithBoundedErrorInTime` and `BPTIME`.
* `PromiseBPTIME_mono`: increasing the time bound preserves membership.
* `mem_PromiseBPTIME_of_subset`: shrinking either side of the promise preserves membership.
* `promiseClass_BPTIME_subset_PromiseBPTIME`: total bounded-error completions give witnesses.
* `PromiseBPTIME_subset_promiseClass_PPTIME`: a strict-majority completion at the same time scale.
-/

public section

namespace Turing.MultiTapePTM

open Cslib.Complexity

variable {α : Type} {k : ℕ} {State : Type}

/-- Every run halts by `t`; bounded error is required only on the two sides of the promise. -/
@[expose] def SolvesPromiseWithBoundedErrorInTime (machine : MultiTapePTM k Bool State)
    (enc : α ↪ List Bool) (Q : PromiseProblem α) (t : α → ℕ) : Prop :=
  ∀ a, (∀ final ∈ (Cslib.ProbComp.eval
      (machine.runClosedConfigFrom (t a) (machine.initialConfig (enc a)))).support,
      final.tapes.state = none) ∧
    (a ∈ Q.yes → 2 / 3 ≤ Cslib.ProbComp.eval (machine.runClosed (t a) (enc a)) [true]) ∧
    (a ∈ Q.no → 2 / 3 ≤ Cslib.ProbComp.eval (machine.runClosed (t a) (enc a)) [false])

/-- A sufficiently long clock may be enlarged without changing the output law. -/
theorem SolvesPromiseWithBoundedErrorInTime.mono
    {machine : MultiTapePTM k Bool State} {enc : α ↪ List Bool} {Q : PromiseProblem α}
    {t t' : α → ℕ} (h : machine.SolvesPromiseWithBoundedErrorInTime enc Q t)
    (ht : ∀ a, t a ≤ t' a) : machine.SolvesPromiseWithBoundedErrorInTime enc Q t' := by
  intro a
  obtain ⟨hhalt, hyes, hno⟩ := h a
  refine ⟨?_, ?_⟩
  · rw [machine.eval_runClosedConfigFrom_eq_of_halted _ (ht a) hhalt]
    exact hhalt
  · rw [machine.eval_runClosed_eq_of_halted _ (ht a) hhalt]
    exact ⟨hyes, hno⟩

/-- A machine solving a promise problem solves every promise problem with fewer yes-instances and
fewer no-instances. -/
theorem SolvesPromiseWithBoundedErrorInTime.of_subset
    {machine : MultiTapePTM k Bool State} {enc : α ↪ List Bool} {Q Q' : PromiseProblem α}
    {t : α → ℕ} (h : machine.SolvesPromiseWithBoundedErrorInTime enc Q t)
    (hyes : Q'.yes ⊆ Q.yes) (hno : Q'.no ⊆ Q.no) :
    machine.SolvesPromiseWithBoundedErrorInTime enc Q' t := fun a =>
  let ⟨hhalt, hQyes, hQno⟩ := h a
  ⟨hhalt, fun ha => hQyes (hyes ha), fun ha => hQno (hno ha)⟩

/-- On a decision problem, solving with bounded error is deciding with bounded error. -/
theorem solvesPromiseWithBoundedErrorInTime_ofSet_iff {machine : MultiTapePTM k Bool State}
    {enc : α ↪ List Bool} {A : Set α} {t : α → ℕ} :
    machine.SolvesPromiseWithBoundedErrorInTime enc (PromiseProblem.ofSet A) t ↔
      machine.DecidesWithBoundedErrorInTime enc A t := by
  refine forall_congr' fun a => and_congr_right fun _ => ?_
  by_cases ha : a ∈ A
  · have hno : a ∉ (PromiseProblem.ofSet A).no := fun h => h ha
    simp only [MultiTapeTM.indicator, ha, ite_true]
    exact ⟨fun h => h.1 ha, fun h => ⟨fun _ => h, fun h' => absurd h' hno⟩⟩
  · simp only [MultiTapeTM.indicator, ha, ite_false]
    exact ⟨fun h => h.2 ha, fun h => ⟨fun h' => absurd h' ha, fun _ => h⟩⟩

end Turing.MultiTapePTM

namespace Cslib.Complexity

open _root_.Turing _root_.Turing.MultiTapeTM
open scoped ENNReal

variable {α : Type} {enc : α ↪ List Bool} {T : ℕ → ℕ}

/-- Native bounded-error promise problems with fixed machine parameters and affine time `T`.
All encoded inputs terminate, but the error conditions only constrain promised inputs. -/
@[expose] def PromiseBPTIME (enc : α ↪ List Bool) (T : ℕ → ℕ) : Set (PromiseProblem α) :=
  {Q | ∃ c₁ c₂ : ℕ, ∃ (k : ℕ) (State : Type) (_ : Finite State)
    (machine : MultiTapePTM k Bool State),
      machine.SolvesPromiseWithBoundedErrorInTime enc Q fun a => c₁ * T (enc a).length + c₂}

/-- Membership is monotone in the caller's time bound. -/
theorem PromiseBPTIME_mono {T₁ T₂ : ℕ → ℕ} (h : ∀ n, T₁ n ≤ T₂ n) :
    PromiseBPTIME enc T₁ ⊆ PromiseBPTIME enc T₂ := by
  rintro Q ⟨c₁, c₂, k, State, hfinite, machine, hQ⟩
  exact ⟨c₁, c₂, k, State, hfinite, machine, hQ.mono fun a =>
    Nat.add_le_add_right (Nat.mul_le_mul_left _ (h _)) _⟩

/-- A promise problem with fewer yes-instances and fewer no-instances than one in `PromiseBPTIME`
is in `PromiseBPTIME`. -/
theorem mem_PromiseBPTIME_of_subset {Q Q' : PromiseProblem α} (hQ : Q ∈ PromiseBPTIME enc T)
    (hyes : Q'.yes ⊆ Q.yes) (hno : Q'.no ⊆ Q.no) : Q' ∈ PromiseBPTIME enc T :=
  let ⟨c₁, c₂, k, State, hfinite, machine, hQ⟩ := hQ
  ⟨c₁, c₂, k, State, hfinite, machine, hQ.of_subset hyes hno⟩

/-- A decision problem, as a promise problem, is in `PromiseBPTIME` exactly when it is in
`BPTIME`. -/
@[simp]
theorem ofSet_mem_PromiseBPTIME {A : Set α} :
    PromiseProblem.ofSet A ∈ PromiseBPTIME enc T ↔ A ∈ BPTIME enc T := by
  simp only [PromiseBPTIME, BPTIME, Set.mem_ofPred_eq,
    MultiTapePTM.solvesPromiseWithBoundedErrorInTime_ofSet_iff]

/-- A bounded-error total completion supplies a native bounded-error promise solver. -/
theorem promiseClass_BPTIME_subset_PromiseBPTIME :
    promiseClass (BPTIME enc T) ⊆ PromiseBPTIME enc T := by
  rintro Q ⟨L, ⟨c₁, c₂, k, State, hfinite, machine, hL⟩, hyes, hno⟩
  refine ⟨c₁, c₂, k, State, hfinite, machine, fun a => ⟨(hL a).1, ?_, ?_⟩⟩
  · intro ha
    simpa only [indicator, hyes ha, ↓reduceIte] using (hL a).2
  · intro ha
    have hnot : a ∉ L := fun h => Set.disjoint_right.mp hno ha h
    simpa only [indicator, hnot, ↓reduceIte] using (hL a).2

/-- Accepting by strict majority completes the promise in `PPTIME` without changing its clock.
The completion may have an exact tie outside the promise; it need not belong to `BPTIME`. -/
theorem PromiseBPTIME_subset_promiseClass_PPTIME :
    PromiseBPTIME enc T ⊆ promiseClass (PPTIME enc T) := by
  rintro Q ⟨c₁, c₂, k, State, hfinite, machine, hQ⟩
  let L : Set α := {a | 1 / 2 <
    ProbComp.eval (machine.runClosed (c₁ * T (enc a).length + c₂) (enc a)) [true]}
  have hhalf : (1 / 2 : ℝ≥0∞) < 2 / 3 := by
    refine (ENNReal.toReal_lt_toReal (ENNReal.div_ne_top (by norm_num) (by norm_num))
      (ENNReal.div_ne_top (by norm_num) (by norm_num))).mp ?_
    simp only [ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat]
    norm_num
  refine ⟨L, ⟨c₁, c₂, k, State, hfinite, machine,
    fun a => ⟨(hQ a).1, Iff.rfl⟩⟩, ?_, ?_⟩
  · intro a ha
    exact hhalf.trans_le ((hQ a).2.1 ha)
  · refine Set.disjoint_right.mpr fun a ha hL => ?_
    let p := ProbComp.eval (machine.runClosed (c₁ * T (enc a).length + c₂) (enc a))
    have hsum : p [true] + p [false] ≤ 1 := by
      simpa only [Finset.sum_pair (by decide : ([true] : List Bool) ≠ [false]), PMF.tsum_coe] using
        (sum_le_tsum ({[true], [false]} : Finset (List Bool)) (f := fun w => p w))
    have hfalse : (1 / 2 : ℝ≥0∞) ≤ p [false] := hhalf.le.trans ((hQ a).2.2 ha)
    have hlt := ENNReal.add_lt_add_right (by norm_num : (1 / 2 : ℝ≥0∞) ≠ ⊤) hL
    rw [ENNReal.add_halves] at hlt
    exact (hlt.trans_le ((add_le_add le_rfl hfalse).trans hsum)).false

end Cslib.Complexity
