/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.CarrySave.CountingQuery
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
public import CslibFrontier.Foundations.Data.BitString.Counter
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.NatLength
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary

/-!
# Native evaluation of padded counting leaves

The executable query decodes its most-significant-first path, tests padding and the requested
component, and calls the supplied native predicate. All input data, including the predicate's
context, are charged. This is a function certificate on an encoded query; assembling that query
from the persistent traversal tapes and obtaining graph endpoints remain separate operations.
-/

public section

namespace Cslib.CountingLeaf

open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime
open Cslib.Circuits.Boolean.CarrySaveQuery

/-- Encoded local data for a zero-layer predicate-count query. -/
structure Input where
  /-- Explicit data used by the predicate. -/
  context : List Bool
  /-- Number of genuine leaves, excluding padding. -/
  count : ℕ
  /-- Precision of each carry-save word. -/
  width : ℕ
  /-- Most-significant-first address from the root. -/
  path : List Bool
  /-- Whether the second carry-save word is requested. -/
  carry : Bool
  /-- Requested bit index. -/
  bit : ℕ

/-- Context and path are raw bits; all numbers are binary. -/
enc_structure encInput : Input where
  context : encBits, count : encNat, width : encNat, path : encBits, carry : encBool, bit : encNat

/-- Exact serialized query length, including framing and the carry selector. -/
theorem length_encInput (q : Input) :
    (encInput q).length = 2 * q.context.length + 2 * (encNat q.count).length +
      2 * (encNat q.width).length + 2 * q.path.length + (encNat q.bit).length + 7 := by
  simp only [encInput_apply, length_encPair, encBits_apply, encBool_apply,
    List.length_singleton]
  omega

/-- The traversal's raw counter width bounds the serialized index, including redundant zeroes.
This bounds the target representation; constructing it still requires a charged serializer. -/
theorem length_encInput_of_counter_le (context path bits : List Bool) (count width : ℕ)
    (carry : Bool) :
    (encInput ⟨context, count, width, path, carry, BitString.lsbValue bits⟩).length ≤
      2 * context.length + 2 * (encNat count).length + 2 * (encNat width).length +
        2 * path.length + bits.length + 7 := by
  rw [length_encInput]
  have := length_encNat_le_of_lt_two_pow (BitString.lsbValue_lt bits)
  dsimp only
  omega

/-- Evaluate a zero-layer counting query, including precision and domain padding. -/
@[expose] def run (predicate : List Bool × ℕ → Bool) (q : Input) : Bool :=
  if q.bit < q.width ∧ q.bit = 0 ∧ q.carry = false ∧ BitString.binaryValue q.path < q.count
  then predicate (q.context, BitString.binaryValue q.path) else false

/-- The complete encoded leaf query is native polynomial-time when its predicate is. -/
theorem computableInPolyTime_run (predicate : List Bool × ℕ → Bool)
    (hp : ComputableInPolyTime predicate (encPair encBits encNat) encBool) :
    ComputableInPolyTime (run predicate) encInput encBool := by
  have hpath : ComputableInPolyTime (fun q : Input => BitString.binaryValue q.path)
      encInput encNat := bitsBinaryValue.comp (by fun_prop)
  have hb : ComputableInPolyTime (fun q : Input => decide (q.bit < q.width))
      encInput encBool := binary_lt' (by fun_prop) (by fun_prop)
  have hz : ComputableInPolyTime (fun q : Input => decide (q.bit = 0))
      encInput encBool := decide_eq' (by fun_prop) (const 0)
  have hc : ComputableInPolyTime (fun q : Input => decide (q.carry = false))
      encInput encBool := decide_eq' (by fun_prop) (const false)
  have hn := binary_lt' hpath (right := Input.count) (by fun_prop)
  have hand := of_tidy (ComputableTidilyInPolyTime.decide_and hb.tidy
    (ComputableTidilyInPolyTime.decide_and hz.tidy
      (ComputableTidilyInPolyTime.decide_and hc.tidy hn.tidy)))
  have hctx : ComputableInPolyTime Input.context encInput encBits := by fun_prop
  unfold run
  simpa only [decide_eq_true_eq, Function.comp_apply] using
    ComputableInPolyTime.ite hand (hp.comp (hctx.prod hpath)) (const false)

/-- The executable result is exactly the semantic leaf of the existing counting tree. -/
theorem run_eq_value (predicate : List Bool × ℕ → Bool) (q : Input) :
    run predicate q = value
      (fun path => Counting.leafPair q.count q.width (fun j => predicate (q.context, j))
        (BitString.binaryValue path)) ⟨q.path, 0, q.carry, q.bit⟩ := by
  unfold value
  split_ifs with hw
  · rw [tree, Counting.component_leafPair]
    cases hc : q.carry <;> simp [run, hw, hc, and_comm]
  · simp [run, hw]

end Cslib.CountingLeaf
