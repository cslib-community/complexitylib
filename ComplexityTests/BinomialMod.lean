/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests of Complexity.Computability.Arithmetic.BinomialMod)

public import Complexity.Computability.Arithmetic.BinomialMod

/-!
# Modular binomial regression tests

The examples cover upper indices above the modulus, the last permitted lower index, malformed
moduli, and the early zero guard. A shifted binomial client exercises composition of the native
space certificate with binary arithmetic.
-/

public section

namespace ComplexityTests.BinomialMod

open Cslib.Arithmetic Turing MultiTapeTM ComputableInSpace

instance : Fact (Nat.Prime 7) := ⟨by decide⟩

example : binomialMod 7 5 2 = 3 := by decide
example : binomialMod 7 1000 3 = 6 := by decide
example : binomialMod 7 13 6 = 1 := by decide
example : binomialMod 7 15 6 = 0 := by decide
example : binomialMod 2 7 1 = 1 := by decide
example : binomialMod 7 2 3 = 0 := by decide
example : binomialMod 7 0 0 = 1 := by decide
example : binomialMod 0 0 0 = 0 := by decide
example : binomialMod 0 1000 3 = 0 := by decide
example : binomialMod 1 1000 3 = 0 := by decide

/-- The strict lower-index restriction is necessary: the recurrence cannot invert `p`. -/
example : binomialMod 7 7 7 ≠ Nat.choose 7 7 % 7 := by decide

/-- A typical shifted coefficient used in power-series expansion. -/
def shiftedBinomial (args : ℕ × ℕ) : ℕ :=
  let (n, k) := args
  binomialMod 7 (n + k) k

example : shiftedBinomial (9, 3) = 3 := by decide

/-- The scalar coefficient client inherits the native space bound through argument preparation. -/
theorem shiftedBinomial_inSpace :
    ComputableInSpace shiftedBinomial (encPair encNat encNat) encNat
      fun args => (encPair encNat encNat args).length := by
  have hn := fst encNat encNat
  have hk := snd encNat encNat
  have hargs : ComputableInSpace (fun (n, k) => (7, n + k, k))
      (encPair encNat encNat) encNat3 (fun args => (encPair encNat encNat args).length) :=
    budget_prod (budget_const 7 (.refl _)) (budget_prod (budget_natAdd hn hk) hk)
  exact (budget_comp_linear binomialMod_inSpace hargs).of_enc_eq fun _ => rfl

example (n k : ℕ) (hk : k < 7) : shiftedBinomial (n, k) = Nat.choose (n + k) k % 7 :=
  binomialMod_eq (n + k) k hk

end ComplexityTests.BinomialMod
