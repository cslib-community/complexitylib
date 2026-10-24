/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

import Complexity.Computability.TreeEval.Reader.Correct
import Complexity.Computability.TreeEval.Space

/-!
# Tree Evaluation

A small instance evaluated directly, and the Cook–Mertz procedure over `ZMod 7` on two-bit values:
the field-size hypothesis `2ℓ < |K| - 1` holds, as `4 < 6`, so the correctness theorem is not
vacuous. The read machine computes the same value.
-/

namespace ComplexityTests.TreeEval

open Cslib.TreeEval

instance : Fact (Nat.Prime 7) := ⟨by decide⟩

/-- Bitwise exclusive or of two two-bit values. -/
def xorGate (x y : Fin 2 → Bool) : Fin 2 → Bool := fun i => x i ^^ y i

/-- Bitwise conjunction of two two-bit values. -/
def andGate (x y : Fin 2 → Bool) : Fin 2 → Bool := fun i => x i && y i

/-- A height-two instance: `(10 ⊕ 11) ∧ (01 ⊕ 00) = 01 ∧ 01`. -/
def sample : Tree 2 2 :=
  .node andGate (.node xorGate (.leaf ![true, false]) (.leaf ![true, true]))
    (.node xorGate (.leaf ![false, true]) (.leaf ![false, false]))

example : sample.eval = ![false, true] := by decide

/-- The Cook–Mertz procedure over `ZMod 7` computes the value of the sample instance. -/
example : proc (Finset.univ : Finset (ZMod 7)ˣ).toList sample 1 2 0 2 =
    embed ![false, true] := by
  rw [← embed_eval_eq_proc (by simp) sample 2]
  congr 1
  decide

/-- Any two-bit instance over `ZMod 7` is computed by the procedure, for every target register. -/
example {h : ℕ} (T : Tree 2 h) (t : Fin 3) :
    embed T.eval = proc (Finset.univ : Finset (ZMod 7)ˣ).toList T 1 t 0 t :=
  embed_eval_eq_proc (by simp) T t

/-- The encoding of the sample instance starts with the header `11 0 11 0`. -/
example : sample.encode.take 6 = [true, true, false, true, true, false] := by decide

/-- The read machine halts on the encoding of the sample instance with its value. -/
example : ∃ n s, Reader.machine.run sample.encode n = ⟨s, [false, true]⟩ ∧
    Reader.machine.halt s = true := by
  obtain ⟨n, s, h, hs⟩ := Reader.exists_run_eq sample
  exact ⟨n, s, by rw [h]; congr 1, hs⟩

open Reader in
/-- The reader's space parameter on `sample` (`ℓ = 2`, `H = 2`) is `(2 + 2 + 1) * (2 + 1) = 15`. -/
example : spaceBound 2 2 = 15 := by decide

open Reader in
/-- Along the run on `sample`, the reader state's encoded bit budget never exceeds
`2 ^ 12 * spaceBound 2 2 = 61440`. -/
example (step : ℕ) :
    stateBudget (machine.run sample.encode step).state ≤ 61440 := by
  calc stateBudget (machine.run sample.encode step).state
    _ ≤ 2 ^ 12 * spaceBound 2 2 :=
      stateBudget_le (bounds_of_inv (inv_run (T := sample) step))
    _ = 61440 := by decide

/-- The encoding of instances tells the sample instance apart from a leaf with its value. -/
example : encInstance ⟨2, 2, sample⟩ ≠ encInstance ⟨2, 0, .leaf ![false, true]⟩ :=
  encInstance.injective.ne (by simp)

open Turing MultiTapeTM Reader in
/-- **Tree Evaluation in small space**: `O((ℓ + H + 1) · log (ℓ + 2) + log (n + 2))`. -/
example : ∃ t, ComputableInBigO (fun I : Instance => List.ofFn I.tree.eval) encInstance
    encBits t fun I => spaceBound I.ell I.height + (encNat ((encInstance I).length + 1)).length :=
  computableInSpace_eval

open Turing MultiTapeTM Reader in
/-- Instantiating `computableInSpace_eval` on `sample` (`spaceBound 2 2 + 7 = 22`) yields a
finite-state multi-tape machine that computes `[false, true]` from
`encInstance ⟨2, 2, sample⟩` within `c * 23` space cells. -/
example : ∃ (t c k : ℕ) (State : Type) (_ : Finite State) (tm : MultiTapeTM k Bool State),
    tm.ComputesInTimeAndSpace (encInstance ⟨2, 2, sample⟩) [false, true]
      (c * (t + 1)) (c * 23) := by
  obtain ⟨t, c, k, State, hfinite, tm, htm⟩ := computableInSpace_eval
  have h : tm.ComputesInTimeAndSpace (encInstance ⟨2, 2, sample⟩)
      (List.ofFn sample.eval) (c * (t ⟨2, 2, sample⟩ + 1))
      (c * (spaceBound 2 2 + (encNat ((encInstance ⟨2, 2, sample⟩).length + 1)).length + 1)) :=
    htm ⟨2, 2, sample⟩
  have hval : List.ofFn sample.eval = [false, true] := by decide
  have hspace : spaceBound 2 2 + (encNat ((encInstance ⟨2, 2, sample⟩).length + 1)).length + 1 =
      23 := by decide
  rw [hval, hspace] at h
  exact ⟨t ⟨2, 2, sample⟩, c, k, State, hfinite, tm, h⟩

/-- The sample instance packaged as a nontrivial instance (`1 ≤ ℓ` and `1 ≤ H`). -/
def sampleNontrivial : NontrivialInstance := ⟨⟨2, 2, sample⟩, by decide, by decide⟩

/-- The encoded sample instance has `110` bits (`6` header bits, `3 * 32` gate bits, `4 * 2` leaf
bits). -/
example : (encInstance sampleNontrivial.1).length = 110 := by decide

open Turing MultiTapeTM in
example : sampleNontrivial.1.ell < (encNat (encInstance sampleNontrivial.1).length).length :=
  ell_lt_length_encNat_length_encInstance sampleNontrivial.2.2

open Turing MultiTapeTM in
example : sampleNontrivial.1.height < (encNat (encInstance sampleNontrivial.1).length).length :=
  height_lt_length_encNat_length_encInstance sampleNontrivial.2.1

open Turing MultiTapeTM Reader in
/-- On `sampleNontrivial`, the raw space bound is `15 + 7 = 22` and the `6 · log n · log log n`
upper bound is `6 * (7 * 3) = 126`. -/
example : spaceBound sampleNontrivial.1.ell sampleNontrivial.1.height +
      (encNat ((encInstance sampleNontrivial.1).length + 1)).length = 22 ∧
    6 * ((encNat (encInstance sampleNontrivial.1).length).length *
      (encNat (encNat (encInstance sampleNontrivial.1).length).length).length) = 126 := by
  decide

open Turing MultiTapeTM Reader in
example : spaceBound sampleNontrivial.1.ell sampleNontrivial.1.height +
      (encNat ((encInstance sampleNontrivial.1).length + 1)).length ≤
    6 * ((encNat (encInstance sampleNontrivial.1).length).length *
      (encNat (encNat (encInstance sampleNontrivial.1).length).length).length) :=
  spaceBound_add_length_le_log_mul_log_log sampleNontrivial.2.1 sampleNontrivial.2.2

open Turing MultiTapeTM in
/-- **Tree Evaluation in space `O(log n · log log n)`** on nontrivial instances. -/
example : ∃ t, ComputableInBigO
    (fun I : NontrivialInstance => List.ofFn I.1.tree.eval) encNontrivialInstance encBits t
    fun I => (encNat (encNontrivialInstance I).length).length *
      (encNat (encNat (encNontrivialInstance I).length).length).length :=
  computableInSpace_eval_log_mul_log_log

open Turing MultiTapeTM in
/-- Instantiating `computableInSpace_eval_log_mul_log_log` on `sampleNontrivial`
(`7 * 3 = 21`) yields a finite-state multi-tape machine that computes `[false, true]` from
`encNontrivialInstance sampleNontrivial` within `c * 22` space cells. -/
example : ∃ (t c k : ℕ) (State : Type) (_ : Finite State) (tm : MultiTapeTM k Bool State),
    tm.ComputesInTimeAndSpace (encNontrivialInstance sampleNontrivial) [false, true]
      (c * (t + 1)) (c * 22) := by
  obtain ⟨t, c, k, State, hfinite, tm, htm⟩ := computableInSpace_eval_log_mul_log_log
  have h : tm.ComputesInTimeAndSpace (encNontrivialInstance sampleNontrivial)
      (List.ofFn sampleNontrivial.1.tree.eval) (c * (t sampleNontrivial + 1))
      (c * ((encNat (encNontrivialInstance sampleNontrivial).length).length *
        (encNat (encNat (encNontrivialInstance sampleNontrivial).length).length).length + 1)) :=
    htm sampleNontrivial
  have hval : List.ofFn sampleNontrivial.1.tree.eval = [false, true] := by decide
  have hspace : (encNat (encNontrivialInstance sampleNontrivial).length).length *
      (encNat (encNat (encNontrivialInstance sampleNontrivial).length).length).length + 1 =
      22 := by decide
  rw [hval, hspace] at h
  exact ⟨t sampleNontrivial, c, k, State, hfinite, tm, h⟩

end ComplexityTests.TreeEval

/--
info: 'Cslib.TreeEval.proc_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.TreeEval.proc_eq

/--
info: 'Cslib.TreeEval.embed_eval_eq_proc' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.TreeEval.embed_eval_eq_proc

/--
info: 'Cslib.TreeEval.Reader.exists_run_eq' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.TreeEval.Reader.exists_run_eq

/--
info: 'Turing.ReadMachine.computes_toStepMachine' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.ReadMachine.computes_toStepMachine

/--
info: 'Turing.ReadMachine.tidy_toStepMachine' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.ReadMachine.tidy_toStepMachine

/--
info: 'Cslib.TreeEval.Reader.tidy_machine' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.TreeEval.Reader.tidy_machine

/--
info: 'Cslib.TreeEval.Reader.inv_run' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.TreeEval.Reader.inv_run

/--
info: 'Cslib.TreeEval.Reader.stateBudget_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.TreeEval.Reader.stateBudget_le

/--
info: 'Cslib.TreeEval.encode_injective' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.TreeEval.encode_injective

/--
info: 'Cslib.TreeEval.computableInSpace_eval' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.TreeEval.computableInSpace_eval

/--
info: 'Cslib.TreeEval.ell_lt_length_encNat_length_encInstance' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.TreeEval.ell_lt_length_encNat_length_encInstance

/--
info: 'Cslib.TreeEval.height_lt_length_encNat_length_encInstance' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.TreeEval.height_lt_length_encNat_length_encInstance

/--
info: 'Cslib.TreeEval.spaceBound_add_length_le_log_mul_log_log' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.TreeEval.spaceBound_add_length_le_log_mul_log_log

/--
info: 'Cslib.TreeEval.computableInSpace_eval_log_mul_log_log' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.TreeEval.computableInSpace_eval_log_mul_log_log
