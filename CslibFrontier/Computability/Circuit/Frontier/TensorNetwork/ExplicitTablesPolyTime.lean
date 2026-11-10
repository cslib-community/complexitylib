/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.ExplicitTables
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Unary
public import CslibFrontier.Computability.Machines.Turing.MultiTape.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeNatFrontends

/-!
# Tables of explicit tensor networks in polynomial time

The vertices of an explicit network written by a polynomial-time construction list their ports in
binary and their tables as bounded tables. Ports computed in unary are rewritten in binary
(`ExplicitTensorNetwork.ports_unary_to_binary`), and a bounded table is polynomial-time whenever
each of its entries is, since it is a map over the first `2 ^ B` numbers, a constant list
(`ExplicitTensorNetwork.computableInPolyTime_boundedTable`). Such a vertex is written as
`ExplicitTensorNetwork.encVertex`.

## Main definitions

* `Cslib.Circuits.Frontier.ExplicitTensorNetwork.encVertex`: the encoding of a vertex of an explicit
  network over `ℕ`.

## Main results

* `Cslib.Circuits.Frontier.ExplicitTensorNetwork.ports_unary_to_binary`: a list of numbers in unary
  can be rewritten in binary.
* `Cslib.Circuits.Frontier.ExplicitTensorNetwork.computableInPolyTime_boundedTable`: bounded tables
  with polynomial-time entries.
-/

public section

namespace Cslib.Circuits.Frontier.ExplicitTensorNetwork

open Turing.MultiTapeTM ComputableInPolyTime

/-- The encoding of a vertex `(ports, table)` of an explicit network over `ℕ`: its list of ports,
framed, then its table, the entries of both framed binary numbers (`encNat`). This is
`DescribedNetwork.encVertex (encList encNat)`, named here so that clients need not import
`DescribedContraction`. -/
abbrev encVertex : List ℕ × List ℕ ↪ List Bool := encPair (encList encNat) (encList encNat)

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
