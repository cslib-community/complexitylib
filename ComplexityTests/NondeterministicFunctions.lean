/-
Copyright (c) 2026 András Z. Salamon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: András Z. Salamon
-/

import Complexity.Computability.Communication.Nondeterministic.Functions

/-! Tests for the nondeterministic complexity of the standard functions: `N⁰(IP_1) = 1`, from the
lower bound and the cover of the zeros of `x₀ ∧ y₀` by two rectangles; the bound `N¹(IP_v) ≥ v - 1`
at `v = 2`, the smallest case where it is positive; and deterministic lower bounds for equality,
disjointness and inner product obtained through `ecomplexityFun_le_protocol`. -/

namespace ComplexityTests.NondeterministicFunctions

open Cslib Cslib.Communication Cslib.Communication.Nondeterministic

-- `N⁰(IP_1) = 1`: the zeros of `x₀ ∧ y₀` are covered by `{x₀ = 0} × univ` and `univ × {y₀ = 0}`.
example : ecomplexityFun false (fun x y : BitString 1 => x ⬝ᵥ y) Set.univ Set.univ = 1 := by
  refine le_antisymm (ecomplexityFun_le_iff.mpr ?_) (le_ecomplexityFun_false_dotProduct 1)
  refine ⟨fun w => if w 0 then ({x | x 0 = false}, Set.univ) else (Set.univ, {y | y 0 = false}),
    isCover_fun_iff.mpr ⟨fun w x _ hx y _ hy => ?_, fun x _ y _ h => ?_⟩⟩
  · cases hw : w 0 <;> simp only [hw, ite_true, ite_false, Bool.false_eq_true, Set.mem_ofPred_eq,
      Set.mem_univ] at hx hy <;> simp [dotProduct, Bool.mul_eq_and, hx, hy]
  · cases hx : x 0
    · exact ⟨fun _ => true, by simp [hx], trivial⟩
    · refine ⟨fun _ => false, trivial, ?_⟩
      simpa [dotProduct, Bool.mul_eq_and, hx] using h

-- `N¹(IP_v) ≥ v - 1` is positive from `v = 2` on.
example : (1 : ℕ∞) ≤ ecomplexityFun true (fun x y : BitString 2 => x ⬝ᵥ y) Set.univ Set.univ :=
  le_ecomplexityFun_true_dotProduct 2

-- Deterministic lower bounds follow, since a protocol gives a cover.
example (v : ℕ) :
    (v : ℕ∞) ≤ Protocol.ecomplexityFun (equality : BitString v → BitString v → Bool) :=
  (ecomplexityFun_equality v).ge.trans (ecomplexityFun_le_protocol true)

example (v : ℕ) :
    (v : ℕ∞) ≤ Protocol.ecomplexityFun (disjointness : BitString v → BitString v → Bool) :=
  (ecomplexityFun_disjointness v).ge.trans (ecomplexityFun_le_protocol true)

example (v : ℕ) : (v : ℕ∞) ≤ Protocol.ecomplexityFun fun x y : BitString v => x ⬝ᵥ y :=
  (le_ecomplexityFun_false_dotProduct v).trans (ecomplexityFun_le_protocol false)

end ComplexityTests.NondeterministicFunctions
