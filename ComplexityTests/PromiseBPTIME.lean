/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Complexity.Computability.Complexity.Classes.Promise.Time.Verifier
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Quantitative
import Complexity.Computability.Machines.Turing.MultiTape.Internal.OCombinators

/-! The explicit-time verifier characterization of `PromiseBPTIME` on concrete bounds. A
deterministic linear-time decider is a sample-and-verify machine with no coins, so it solves every
promise problem it separates, and its problem is in `BPTIME`. A promise problem in linear time
survives the round trip through its linear-time coin-replay verifier and sample and verify, at the
same linear bound, so both explicit-time hypotheses are satisfiable together. -/

public section

namespace ComplexityTests.PromiseBPTIME

open Cslib Cslib.Complexity Turing Turing.MultiTapeTM

/-- `c * n + c` in unary, within linear time and space. -/
private theorem computableInO_linear_unary (c : ℕ) :
    ComputableInO (fun x : List Bool => c * x.length + c) encBits encUnary
      (fun x => x.length) (fun x => x.length) := by
  induction c with
  | zero =>
    simpa using ComputableInO.const (encIn := encBits) (encMid := encUnary) 0
  | succ c ih =>
    have hstep := ComputableInO.lengthUnary.append
      (ComputableInO.const (encIn := encBits) (encMid := encUnary) 1)
      (g := fun x : List Bool => x.length + 1) (encOut := encUnary)
      fun x => by simp [encUnary_apply, List.replicate_add]
    have h := ih.append hstep (g := fun x : List Bool => (c + 1) * x.length + (c + 1))
      (encOut := encUnary) fun x => by
        simp only [encUnary_apply, ← List.replicate_add]
        congr 1
        ring
    exact h.mono 3 (fun x => by simp only [encBits_apply]; omega)
      (fun x => by simp only [encBits_apply]; omega)

/-- **A deterministic linear-time decider, with no coins.** Every promise problem separated by a
problem in `DTIME n` is in `PromiseBPTIME n`. -/
theorem mem_PromiseBPTIME_of_mem_DTIME {A : Set (List Bool)} {Q : PromiseProblem (List Bool)}
    (hA : A ∈ DTIME encBits fun n => n) (hyes : Q.yes ⊆ A) (hno : Q.no ⊆ Aᶜ) :
    Q ∈ PromiseBPTIME encBits fun n => n := by
  have hV := (computableInO_indicator_of_mem_DTIME hA).comp (ComputableInO.fst encBits encBits)
  refine mem_PromiseBPTIME_of_verifier (ℓ := fun _ => 0) (t := fun n => n) (C := 6)
    (ComputableInO.const (encIn := encBits) (encMid := encUnary) 0) hV (fun x w hw => ?_)
    (fun x hx => ?_) fun x hx => ?_
  · simp only [List.length_eq_zero_iff] at hw
    subst hw
    simp only [encBits_apply, encPair_apply, List.length_append, length_frame, List.length_nil]
    omega
  · simp [acceptCount_zero, indicator, hyes hx]
  · simp [acceptCount_zero, indicator, show x ∉ A from hno hx]

/-- Through the bridge with `BPTIME`, a problem in `DTIME n` is in `BPTIME n`. -/
example {A : Set (List Bool)} (hA : A ∈ DTIME encBits fun n => n) :
    A ∈ BPTIME encBits fun n => n :=
  ofSet_mem_PromiseBPTIME.mp
    (mem_PromiseBPTIME_of_mem_DTIME hA le_rfl fun _ h => h)

/-- The promise problem with every word a yes-instance, solved by sampling no coins and
accepting: a concrete member of `PromiseBPTIME n`. -/
example : (⟨Set.univ, ∅, Set.disjoint_empty _⟩ : PromiseProblem (List Bool)) ∈
    PromiseBPTIME encBits fun n => n := by
  refine mem_PromiseBPTIME_of_verifier (V := fun _ => true) (ℓ := fun _ => 0) (t := fun n => n)
    (C := 4) (ComputableInO.const (encIn := encBits) (encMid := encUnary) 0)
    (ComputableInO.const (encIn := encPair encBits encBits) (encMid := encBool) true)
    (fun x w hw => ?_) (fun x _ => by simp) fun x hx => absurd hx (Set.notMem_empty x)
  simp only [List.length_eq_zero_iff] at hw
  subst hw
  simp only [encBits_apply, encPair_apply, List.length_append, length_frame, List.length_nil]
  omega

/-- **Round trip at linear time.** A promise problem in linear time has a linear-time coin-replay
verifier, and sampling strings of length `c * n + c` for it solves the problem in linear time
again. Both explicit-time hypotheses are satisfiable together. -/
theorem mem_PromiseBPTIME_linear_of_verifier_roundTrip {Q : PromiseProblem (List Bool)}
    (hQ : Q ∈ PromiseBPTIME encBits fun n => n) : Q ∈ PromiseBPTIME encBits fun n => n := by
  obtain ⟨V, c, hV, hbound⟩ := exists_verifier_of_mem_PromiseBPTIME hQ
  exact mem_PromiseBPTIME_of_verifier (ℓ := fun x : List Bool => c * x.length + c)
    (t := fun n => n) (C := c + 4) (computableInO_linear_unary c) hV
    (fun x w hw => by
      simp only [encBits_apply, encPair_apply, List.length_append, length_frame, hw]
      nlinarith)
    (fun x hx => (hbound x _ (by simp [encBits_apply])).1 hx)
    fun x hx => (hbound x _ (by simp [encBits_apply])).2 hx

/-- The lift of `BPTIME` is contained in `PromiseBPTIME`, at a concrete bound. -/
example : promiseClass (BPTIME encBits fun n => n) ⊆ PromiseBPTIME encBits fun n => n :=
  promiseClass_BPTIME_subset_PromiseBPTIME

end ComplexityTests.PromiseBPTIME
