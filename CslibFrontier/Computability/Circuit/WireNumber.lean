/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (addition to `Cslib/Computability/Circuit/Wire.lean`)

public import Cslib.Computability.Circuit.Wire
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Wire numbers

Wires are numbered inputs first, as in `Cslib.Circuits.Circuit.trace`: input `i` is wire `i` and
gate `j` is wire `n + j`, where `n` is the number of inputs.

## Main definitions

* `Cslib.Circuits.Wire.equivFin`: wires as `Fin (inputCount + gateCount)`.
* `Cslib.Circuits.Wire.toNat`, `Cslib.Circuits.Wire.ofNat`: wire numbers and their inverse.

## Main results

* `Cslib.Circuits.Wire.toNat_lt`, `Cslib.Circuits.Wire.toNat_injective`: wire numbers are distinct
  and below the wire count.
* `Cslib.Circuits.Wire.ofNat_toNat`, `Cslib.Circuits.Wire.toNat_ofNat`: the numbering is a
  bijection.
-/

@[expose] public section

namespace Cslib.Circuits

variable {n k : ℕ}

namespace Wire

/-- Wires numbered inputs first: input `i` is `i` and gate `j` is `inputCount + j`, the order of
`Circuit.trace`. -/
def equivFin (inputCount gateCount : ℕ) :
    Wire inputCount gateCount ≃ Fin (inputCount + gateCount) :=
  (equiv inputCount gateCount).trans finSumFinEquiv

/-- Input wire `i` maps to `Fin.castAdd k i` under `equivFin`. -/
@[simp] theorem equivFin_input (i : Fin n) : equivFin n k (input i) = Fin.castAdd k i := rfl

/-- Gate wire `j` maps to `Fin.natAdd n j` under `equivFin`. -/
@[simp] theorem equivFin_gate (j : Fin k) : equivFin n k (gate j) = Fin.natAdd n j := rfl

/-- The number of a wire: input `i` is `i` and gate `j` is `inputCount + j`. -/
def toNat (w : Wire n k) : ℕ := (equivFin n k w).val

/-- Input wire `i` has wire number `i`. -/
@[simp] theorem toNat_input (i : Fin n) : (input i : Wire n k).toNat = i := rfl

/-- Gate wire `j` has wire number `n + j`. -/
@[simp] theorem toNat_gate (j : Fin k) : (gate j : Wire n k).toNat = n + j := rfl

/-- Every wire in a circuit with `n` inputs and `k` gates has wire number strictly less than
`n + k`. -/
theorem toNat_lt (w : Wire n k) : w.toNat < n + k := (equivFin n k w).isLt

/-- The wire with number `i`, for `i < inputCount + gateCount`. -/
def ofNat (i : ℕ) (h : i < n + k) : Wire n k := (equivFin n k).symm ⟨i, h⟩

/-- Decoding the wire number of `w` recovers `w`. -/
@[simp] theorem ofNat_toNat (w : Wire n k) : ofNat w.toNat w.toNat_lt = w :=
  (equivFin n k).symm_apply_apply w

/-- The wire number of `ofNat i h` is `i`. -/
@[simp] theorem toNat_ofNat (i : ℕ) (h : i < n + k) : (ofNat i h : Wire n k).toNat = i := by
  simp [ofNat, toNat]

/-- Wire numbering `toNat` is injective. -/
theorem toNat_injective : Function.Injective (toNat : Wire n k → ℕ) :=
  fun _ _ h => (equivFin n k).injective (Fin.ext h)

/-- Widening a wire by `castSucc` preserves its wire number. -/
@[simp] theorem toNat_castSucc (w : Wire n k) : w.castSucc.toNat = w.toNat := by
  cases w <;> rfl

end Wire

end Cslib.Circuits
