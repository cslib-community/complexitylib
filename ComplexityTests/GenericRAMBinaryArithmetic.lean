/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.GenericRAM.Native.Nat

/-! Direct binary arithmetic supplies the actual bounded-natural model.
Its existing public APIs are not restated here. -/

open Turing.MultiTapeTM Cslib.GenericRAM.BoundedNat
open Turing.MultiTapeTM.ComputableInPolyTime

example (c : ℕ) : ComputableInPolyTime (model.checkedConstant c)
    encNat (encOption encNat) := by
  change ComputableInPolyTime
    (fun k => if decide (c < k) then some c else none) _ _
  simpa only [decide_eq_true_eq, Function.comp_def] using
    (binary_lt.comp ((const c).prod (of_eq (encIn := encNat) fun _ => rfl))).ite_decide
      (const (some c)) (const none)

example (op : model.operations.Op) : ComputableInPolyTime (model.checkedOp op)
    (encPair encNat (encPi encNat)) (encOption encNat) := by
  have hx := (pi_apply encNat (0 : Fin 2)).comp (snd encNat (encPi encNat))
  have hy := (pi_apply encNat (1 : Fin 2)).comp (snd encNat (encPi encNat))
  have hadd := binary_add.comp (hx.prod hy)
  change ComputableInPolyTime
    (fun p : ℕ × (Fin 2 → ℕ) => if decide (p.2 0 + p.2 1 < p.1)
      then some (p.2 0 + p.2 1) else none)
    (encPair encNat (encPi encNat (Index := Fin 2))) (encOption encNat)
  simp only [decide_eq_true_eq]
  exact (binary_lt.comp (hadd.prod (fst encNat (encPi encNat)))).ite_decide
    ((optionSome encNat).comp hadd) (const none)

-- Boundary evaluation of `checkedConstant` and proof-irrelevance of `NativeCertificate.ofPolyTime`.
example {α β : Type} {f : α → β} {ei : α ↪ List Bool} {eo : β ↪ List Bool}
    (h₁ h₂ : ComputableInPolyTime f ei eo) :
    model.checkedConstant 0 0 = none ∧
    model.checkedConstant 0 1 = some 0 ∧
    Cslib.GenericRAM.NativeCertificate.ofPolyTime h₁ =
      Cslib.GenericRAM.NativeCertificate.ofPolyTime h₂ :=
  ⟨rfl, rfl, rfl⟩
