/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Frontier.TensorNetwork.ExplicitTables
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.List
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Nat
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Unary
public import Complexity.Computability.Machines.Turing.MultiTape.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeNatFrontends

/-!
# Tables of explicit tensor networks in polynomial time

The vertices of an explicit network written by a polynomial-time construction list their ports in
binary and their tables as bounded tables. Ports computed in unary are rewritten in binary
(`ExplicitTensorNetwork.ports_unary_to_binary`), and a bounded table is polynomial-time whenever
each of its entries is, since it is a map over the first `2 ^ B` numbers, a constant list
(`ExplicitTensorNetwork.computableInPolyTime_boundedTable`).

## Main results

* `Cslib.Circuits.Frontier.ExplicitTensorNetwork.ports_unary_to_binary`: a list of numbers in unary
  can be rewritten in binary.
* `Cslib.Circuits.Frontier.ExplicitTensorNetwork.computableInPolyTime_boundedTable`: bounded tables
  with polynomial-time entries.
-/

public section

namespace Cslib.Circuits.Frontier.ExplicitTensorNetwork

open Turing.MultiTapeTM ComputableInPolyTime

variable {α : Type} {inp : α ↪ List Bool}

/-- A list of numbers computed in unary, such as the ports of a vertex, is computed in binary. -/
theorem ports_unary_to_binary {ps : α → List ℕ}
    (hps : ComputableInPolyTime ps inp (encList encUnary)) :
    ComputableInPolyTime ps inp (encList encNat) := by
  simpa only [Function.comp_def, List.map_id'] using (map unary_to_binary).comp hps

/-- A bounded table whose entries are polynomial-time at every fixed position. -/
theorem computableInPolyTime_boundedTable (B : ℕ) {w : α → ℕ} {f : α → ℕ → ℕ}
    (hw : ComputableInPolyTime w inp encUnary)
    (hf : ∀ idx, ComputableInPolyTime (fun a => f a idx) inp encNat) :
    ComputableInPolyTime (fun a => boundedTable B (w a) (f a)) inp (encList encNat) := by
  unfold boundedTable
  exact mapFilterConst _ (fun idx _ => binary_lt' (const idx) (binary_pow' (const 2) hw))
    fun idx _ => hf idx

end Cslib.Circuits.Frontier.ExplicitTensorNetwork
