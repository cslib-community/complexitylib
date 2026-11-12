/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (addition to `Cslib/Computability/Circuit/Complexity.lean`)

public import Cslib.Computability.Circuit.Complexity

/-!
# Composition with retained inputs

A form of the composition rule `complexity_comp_le` for circuits that keep their inputs: computing
`f` and then a function `g` of both the inputs and the values of `f` costs at most the sum of their
complexities (`Cslib.Circuits.complexity_comp_append_le`). The inputs reach `g` by wiring, which
costs nothing, alongside a circuit for `f`.

## Main results

* `Cslib.Circuits.complexity_comp_append_le`: a function of the inputs and of the values of `f`
  costs at most the complexity of `f` plus its own complexity.
-/

public section

namespace Cslib.Circuits

variable {σ : Signature} {U : Type*} {I : Interpretation σ U} [I.IsComplete] {n m p : ℕ}

/-- Computing `f` and then a function `g` of the inputs and of the values of `f` costs at most the
sum of their complexities: the inputs reach `g` by wiring. -/
theorem complexity_comp_append_le (f : (Fin n → U) → Fin m → U)
    (g : (Fin (n + m) → U) → Fin p → U) :
    complexity I (fun x => g (Fin.append x (f x))) ≤ complexity I f + complexity I g := by
  have h := complexity_comp_le (I := I) (fun x => Fin.append (x ∘ id) (f x)) g
  have happ := complexity_append_le (I := I) (fun x : Fin n → U => x ∘ id) f
  rw [complexity_wiring, zero_add] at happ
  exact h.trans (Nat.add_le_add_right happ _)

end Cslib.Circuits
