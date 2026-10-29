/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolySpace.Fold

/-! Binary fold clients: a growing natural accumulator, a captured Boolean input, and zero
iterations. The iteration count uses `encNat`, so its value can be exponential in input length. -/

namespace ComplexityTests.PolySpaceFold

open Turing.MultiTapeTM

/-- Count from zero to a binary input using the invariant-based interface. -/
theorem count_spec :
    ComputableInPolySpace (fun n : ℕ => n.fold (fun _ _ a => a + 1) 0) encNat encNat ∧
      ∀ n : ℕ, n.fold (fun _ _ a => a + 1) 0 = n := by
  apply ComputableInPolySpace.natFold_spec
    (step := fun (_ : ℕ) _ a => a + 1) ComputableInPolyTime.id'
    (ComputableInPolySpace.of_polyTime (ComputableInPolyTime.const 0))
    (ComputableInPolySpace.of_polyTime (by fun_prop))
    (fun _ k a => a = k) (fun _ => rfl) (fun _ _ _ _ h => congrArg (· + 1) h)
    ComputableInPolyTime.id'.tidy.polyBounded_length
  intro n k a hk ha
  rw [ha]
  exact ComputableTidilyInO.length_encNat_mono hk

/-- The raw bound interface retains the original input across all iterations. -/
def copyFlag (p : ℕ × Bool) : Bool := p.1.fold (fun _ _ _ => p.2) false

theorem copyFlag_computable :
    ComputableInPolySpace copyFlag (encPair encNat encBool) encBool := by
  apply ComputableInPolySpace.natFold
    (step := fun p _ _ => p.2) (ComputableInPolyTime.fst encNat encBool)
    (ComputableInPolySpace.of_polyTime (ComputableInPolyTime.const false))
    (ComputableInPolySpace.of_polyTime (by fun_prop)) (PolyBounded.const 1)
  intro p k hk
  simp only [encBool_apply, List.length_singleton, le_refl]

example (n : ℕ) (b : Bool) :
    copyFlag (0, b) = false ∧ copyFlag (n + 1, b) = b ∧ n.fold (fun _ _ a => a + 1) 0 = n :=
  ⟨by simp only [copyFlag, Nat.fold_zero], by simp only [copyFlag, Nat.fold_succ], count_spec.2 n⟩

end ComplexityTests.PolySpaceFold
