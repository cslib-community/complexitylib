/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div

/-!
# Normalizing unary indices into fixed finite ranges

Reducing a unary natural modulo a fixed positive bound gives an index in `Fin bound`. The output
encoding is arbitrary: changing an encoding on a fixed finite type has constant cost. The modulus
and encoding are fixed independently of the runtime input.

## Main results

* `Turing.MultiTapeTM.ComputableInPolyTime.unary_finMod`: modular finite indices.
-/

@[expose] public section

namespace Turing.MultiTapeTM.ComputableInPolyTime

/-- Normalize a unary index into a fixed positive finite range, using any fixed output encoding. -/
@[fun_prop]
theorem unary_finMod {bound : ℕ} (hbound : 0 < bound) (output : Fin bound ↪ List Bool) :
    ComputableInPolyTime (fun index : ℕ =>
      (⟨index % bound, Nat.mod_lt _ hbound⟩ : Fin bound)) encUnary output := by
  let unary : Fin bound ↪ List Bool :=
    ⟨fun index => encUnary index.val, fun _ _ h => Fin.val_injective (encUnary.injective h)⟩
  have hmod : ComputableInPolyTime (fun index : ℕ =>
      (⟨index % bound, Nat.mod_lt _ hbound⟩ : Fin bound)) encUnary unary :=
    (unary_mod.comp (id'.prod (const bound))).of_enc_eq (fun _ => rfl)
  exact (of_finite (encIn := unary) (encOut := output) id).comp hmod

end Turing.MultiTapeTM.ComputableInPolyTime
