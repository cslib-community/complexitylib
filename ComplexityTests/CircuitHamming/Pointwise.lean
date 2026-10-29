/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Circuit.Pointwise
import Complexity.Computability.Circuit.Boolean.Synthesis

/-! Truth tables of small De Morgan circuits under the pointwise lift, on two and three inputs,
with zero inputs and with an empty set of points. -/

namespace ComplexityTests.CircuitHamming.Pointwise

open Cslib Cslib.Circuits Cslib.Circuits.Boolean

/-! ### The lift and evaluation at a point -/

/-- Conjunction lifted pointwise and evaluation at `true` on lifted negation of `id`. -/
example (f g : Bool → Bool) :
    interpretation.pointwise Bool .and ![f, g] = (fun b => f b && g b) ∧
      (interpretation.evalAt true).map (interpretation.pointwise Bool .not ![id]) = false :=
  ⟨rfl, rfl⟩

/-! ### Two inputs -/

/-- NAND on two inputs: a conjunction followed by a negation. -/
private def nand : Circuit signature 2 1 :=
  ⟨.gate (.gate .empty ⟨.and, fun a => .input a⟩) ⟨.not, fun _ => .gate 0⟩, fun _ => .gate 1⟩

/-- Lifted output of `nand` at projections, truth-table values, wire traces, `available`
membership, and `Computes` characterization. -/
example (b : Bool) :
    nand.eval (interpretation.pointwise (BitString 2)) (fun j x => x j) 0 =
      (fun x => !(x 0 && x 1)) ∧
    nand.eval (interpretation.pointwise (BitString 2)) (fun j x => x j) 0 ![true, true] = false ∧
    nand.eval (interpretation.pointwise (BitString 2)) (fun j x => x j) 0 ![true, false] = true ∧
    nand.program.trace (interpretation.pointwise (BitString 2)) (fun j x => x j)
      (.gate ⟨0, by decide⟩) = (fun x => x 0 && x 1) ∧
    nand.program.trace (interpretation.pointwise Bool) ![id, not] (.gate ⟨0, by decide⟩) b =
      false ∧
    (fun x : BitString 2 => x 0 && x 1) ∈ available interpretation nand.program ∧
    nand.Computes interpretation (single fun x => !(x 0 && x 1)) ∧
    ¬nand.Computes interpretation (single fun x => x 0 && x 1) := by
  refine ⟨by rw [Circuit.eval_pointwise_proj]; rfl, by decide, by decide,
    by rw [Program.trace_pointwise_proj]; rfl,
    by rw [Program.trace_pointwise_apply]; cases b <;> rfl,
    by rw [available_eq_range_trace_pointwise]; exact ⟨.gate ⟨0, by decide⟩, rfl⟩,
    by rw [Circuit.computes_iff_eval_pointwise_proj]; rfl, ?_⟩
  rw [Circuit.computes_iff_eval_pointwise_proj]
  intro h
  have := congrFun (congrFun h 0) ![true, true]
  exact absurd this (by decide)

/-! ### Three inputs and boundary cases -/

/-- A chain of two conjunctions on three inputs. -/
private def and3 : Circuit signature 3 1 :=
  ⟨.gate (.gate .empty ⟨.and, ![.input 0, .input 1]⟩) ⟨.and, ![.gate 0, .input 2]⟩,
    fun _ => .gate 1⟩

/-- The constant `true` on zero inputs. -/
private def trueConst : Circuit signature 0 1 :=
  ⟨.gate .empty ⟨.const true, Fin.elim0⟩, fun _ => .gate 0⟩

/-- Three-input conjunction chain, zero-input constant `true`, and empty-domain pointwise lift. -/
example (a : Fin 2 → Empty → Bool) :
    and3.eval (interpretation.pointwise (BitString 3)) (fun j x => x j) 0 =
      (fun x => x 0 && x 1 && x 2) ∧
    and3.Computes interpretation (single fun x => x 0 && x 1 && x 2) ∧
    trueConst.eval (interpretation.pointwise (BitString 0)) Fin.elim0 0 = (fun _ => true) ∧
    trueConst.Computes interpretation (single fun _ => true) ∧
    nand.eval (interpretation.pointwise Empty) a 0 = Empty.elim :=
  ⟨by rw [Circuit.eval_pointwise_proj]; rfl,
    by rw [Circuit.computes_iff_eval_pointwise_proj]; rfl,
    Circuit.eval_pointwise_proj trueConst interpretation 0 ▸ rfl,
    (Circuit.computes_iff_eval_pointwise_proj _ _ _).2 rfl,
    funext fun e => e.elim⟩

end ComplexityTests.CircuitHamming.Pointwise
