/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.ConfigurationGraph.Correctness

/-!
# Compact configuration IDs identify canonical views

The radix encoding stores the full input-free configuration except for the output, which it
summarizes as empty, accepting, or rejecting. On views with already summarized output and a fixed
input, fitting IDs are injective. This lets a local query on IDs represent an individual matrix
entry, rather than an entire fiber of the encoding.

## Main results

* `Turing.MultiTapeNTM.ConfigurationGraph.stackCode_injective`: normalized ternary tape codes
  distinguish stack tapes.
* `Turing.MultiTapeNTM.ConfigurationGraph.vertexID_injective`: equal fitting IDs, on the same
  input and with canonical output, identify the same view.
-/

public section

namespace Turing.MultiTapeNTM.ConfigurationGraph

open Cslib.Turing

/-- The normalized stack representation has a unique ternary code. -/
theorem stackCode_injective : Function.Injective stackCode := by
  suffices h : ∀ n : ℕ, ∀ a b : StackTape Bool,
      a.toList.length + b.toList.length = n → stackCode a = stackCode b → a = b from
    fun a b hab => h _ a b rfl hab
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro a b hn hab
    by_cases hz : n = 0
    · have ha : a.toList = [] := List.length_eq_zero_iff.mp (by omega)
      have hb : b.toList = [] := List.length_eq_zero_iff.mp (by omega)
      exact StackTape.ext (ha.trans hb.symm)
    · have hlt : a.tail.toList.length + b.tail.toList.length < n := by
        simp only [StackTape.tail_toList, List.length_tail]
        omega
      apply (StackTape.eq_iff a b).mpr
      refine ⟨symbolCode_injective ?_, ih _ hlt a.tail b.tail rfl ?_⟩
      · rw [stackCode_head, stackCode_head, hab]
      · rw [stackCode_tail, stackCode_tail, hab]

private theorem outputClass_eq_of_outputCode_eq {a b : List Bool}
    (h : outputCode a = outputCode b) : outputClass a = outputClass b := by
  unfold outputClass
  unfold outputCode at h
  split_ifs at h ⊢ <;> simp_all

variable {k : ℕ} {State : Type} [Fintype State]

/-- The input-free registers distinguish views with the same input and canonical output. -/
theorem registers_injective {a b : FiniteCfg k Bool State}
    (hinput : a.input = b.input) (ha : outputClass a.output = a.output)
    (hb : outputClass b.output = b.output) (h : registers a = registers b) : a = b := by
  have hpos : a.inputPos.val = b.inputPos.val := congrFun h .inputPos
  have hstate : a.state = b.state := stateCode_injective (congrFun h .control)
  have hout : a.output = b.output :=
    ha.symm.trans ((outputClass_eq_of_outputCode_eq (congrFun h .output)).trans hb)
  have hwork : a.workTapes = b.workTapes := by
    funext i
    exact BiTape.ext (symbolCode_injective (congrFun h (.head i)))
      (stackCode_injective (congrFun h (.left i)))
      (stackCode_injective (congrFun h (.right i)))
  apply coreCode_injective hinput
  change encCore (a.inputPos.val, a.state, a.workTapes, a.output) =
    encCore (b.inputPos.val, b.state, b.workTapes, b.output)
  rw [hpos, hstate, hwork, hout]

/-- Equal IDs determine fitting views with the same input and already summarized output. -/
theorem vertexID_injective {B : ℕ} {a b : FiniteCfg k Bool State}
    (hinput : a.input = b.input) (ha : outputClass a.output = a.output)
    (hb : outputClass b.output = b.output)
    (hfitA : Fits B (registers a)) (hfitB : Fits B (registers b))
    (h : vertexID B a = vertexID B b) : a = b := by
  apply registers_injective hinput ha hb
  rw [← readRegisters_vertexID hfitA, ← readRegisters_vertexID hfitB, h]

end Turing.MultiTapeNTM.ConfigurationGraph
