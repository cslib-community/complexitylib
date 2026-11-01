/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.TreeEval.Ary.Packed
public import Complexity.Computability.TreeEval.Ary.Packed.GateInterpolation

/-!
# Counter implementation of packed gate extensions

The existing finite-grid gate extension is computed by the counter-based interpolation loop.
A table query decodes one assignment index, calls the Boolean gate and encodes one output chunk.
This connects the packed algebra to the gate update of the iterative controller, without
constructing a truth table or a polynomial representation at runtime.

## Main definitions

* `Cslib.TreeEval.Ary.Packed.counterGateExtension`: the counter-based gate extension.

## Main results

* `Cslib.TreeEval.Ary.Packed.counterGateExtension_eq`: equality with `gateExtension` for an
  alphabet embedded by unsigned casts in a prime field.

This is functional correctness of the inner loop. Native gate queries and their composition
with the caller's original input still require a separate resource certificate.
-/

@[expose] public section

namespace Cslib.TreeEval.Ary.Packed

open Cslib.BitString

/-- Read the low `n` base-`s` digits of an assignment counter. -/
private def counterAssignment {s n : ℕ} (hs : 0 < s) (k : ℕ) : Fin n → Fin s :=
  fun i => ⟨gridDigit s k i, Nat.mod_lt _ hs⟩

private theorem counterAssignment_number {s n : ℕ} (hs : 0 < s) (a : Fin n → Fin s) :
    counterAssignment hs (finFunctionFinEquiv a) = a := by
  funext i
  apply Fin.ext
  exact (finFunctionFinEquiv_symm_apply_val (finFunctionFinEquiv a) i).symm.trans
    (congrArg Fin.val (congrFun (finFunctionFinEquiv.symm_apply_apply a) i))

/-- Compute one chunk of a gate extension using the finite-grid counter loops. The point and
one requested table value are passed to the arithmetic loop; no table is materialized. -/
def counterGateExtension {p s b d r : ℕ} (hs : 0 < s)
    (encode : (Fin b → Bool) → Fin r → Fin s)
    (decode : (Fin r → Fin s) → Fin b → Bool) (f : Gate d b)
    (x : Fin d → Fin r → ZMod p) (i : Fin r) : ZMod p :=
  (interpolateGrid p s (d * r)
    (fun k => (encode (f fun j => decode (blocksEquiv (fun q : Fin (d * r) =>
      (⟨gridDigit s k q, Nat.mod_lt _ hs⟩ : Fin s)) j)) i).val)
    (List.ofFn fun q : Fin (d * r) => (blocksEquiv.symm x q).val) : ℕ)

/-- The counter loop computes the same packed extension as the existing low-degree algebra.
The full alphabet, not only the encoded values, must embed in the selected field. -/
theorem counterGateExtension_eq {p s b d r : ℕ} [Fact p.Prime] (hs : 0 < s) (hsp : s ≤ p)
    (h : Fin s ↪ ZMod p) (hh : ∀ a, h a = (a.val : ZMod p))
    (encode : (Fin b → Bool) → Fin r → Fin s)
    (decode : (Fin r → Fin s) → Fin b → Bool) (f : Gate d b)
    (x : Fin d → Fin r → ZMod p) (i : Fin r) :
    counterGateExtension hs encode decode f x i = gateExtension h encode decode f x i := by
  rw [counterGateExtension, cast_interpolateGrid hs hsp h hh]
  have htable :
      (fun a : Fin (d * r) → Fin s =>
        ((encode (f fun j => decode
          (blocksEquiv (counterAssignment hs (finFunctionFinEquiv a)) j)) i).val : ZMod p)) =
      (fun a => h (encode (f fun j => decode (blocksEquiv a j)) i)) := by
    funext a
    rw [counterAssignment_number, hh]
  have hpoint :
      (fun q : Fin (d * r) =>
        (((List.ofFn fun j : Fin (d * r) => (blocksEquiv.symm x j).val).getD q.val 0 : ℕ) :
          ZMod p)) = blocksEquiv.symm x := by
    funext q
    simp [List.getD_eq_getElem?_getD]
  change Code.lowDegreeExtension h
    (fun a : Fin (d * r) → Fin s =>
      ((encode (f fun j => decode
        (blocksEquiv (counterAssignment hs (finFunctionFinEquiv a)) j)) i).val : ZMod p))
    (fun q : Fin (d * r) =>
      (((List.ofFn fun j : Fin (d * r) => (blocksEquiv.symm x j).val).getD q.val 0 : ℕ) :
        ZMod p)) = _
  rw [htable, hpoint]
  rfl

end Cslib.TreeEval.Ary.Packed
