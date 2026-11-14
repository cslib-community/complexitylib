/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.PopulationCount.PolyTime
public import CslibFrontier.Computability.Circuit.Boolean.Comparison.OrderPolyTime
public import CslibFrontier.Computability.Circuit.Boolean.WordConstant.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Log
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Native generation of the threshold comparison

A unary-width loop generates the existing linear-size comparator, and binary digit selection
generates its constant threshold word. Together with the population-count generator these give
a native polynomial-time certificate for the full linear-size threshold circuit.
-/

public section

namespace Cslib.Circuits.Boolean

open Turing.MultiTapeTM ComputableInPolyTime

/-- A native polynomial-time compiler for the whole linear-size threshold circuit. The number
of inputs and the cutoff are supplied in unary; all output circuit references are binary. -/
theorem computableInPolyTime_linearThresholdCircuit :
    ComputableInPolyTime (fun p : ℕ × ℕ => (linearThresholdCircuit p.1 p.2).code)
      (encPair encUnary encUnary) encCode := by
  have hn := fst encUnary encUnary
  have hq := snd encUnary encUnary
  have hn' := unary_to_binary.comp hn
  have hq' := unary_to_binary.comp hq
  have hw : ComputableInPolyTime (fun p : ℕ × ℕ => Nat.clog 2 (p.1 + 1) + 1)
      (encPair encUnary encUnary) encUnary := by
    have hc := (unary_clog_const 2).comp
      (show ComputableInPolyTime (fun p : ℕ × ℕ => p.1 + 1)
        (encPair encUnary encUnary) encUnary from by fun_prop)
    fun_prop
  have hp := computableInPolyTime_compCode hn' (computableInPolyTime_leCircuit.comp hw)
    (computableInPolyTime_appendCode hn'
      (computableInPolyTime_wordConstCode hn' hw hq')
      (computableInPolyTime_populationCountCircuit.comp hn))
  have hz : ComputableInPolyTime (fun p : ℕ × ℕ => ([(Op.const false, [])], [p.1]))
      (encPair encUnary encUnary) encCode := by fun_prop
  have ht : ComputableInPolyTime (fun p : ℕ × ℕ => decide (p.2 ≤ p.1))
      (encPair encUnary encUnary) encBool := by fun_prop
  have h := ite_decide ht hp hz
  apply h.of_enc_eq
  intro p
  dsimp only [linearThresholdCircuit, Function.comp_apply]
  split_ifs with hq
  · rw [← compCode_code, ← appendCode_code, ← wordConstCode_eq]
  · rfl

end Cslib.Circuits.Boolean
