/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

import CslibFrontier.Crypto.Computational.MLDSA.KeyOnly

/-! Concrete decompositions, the standard parameter sets, and a toy instance on which signing,
verification and the forgery-to-self-target map are all exercised. -/

open Cslib.Crypto Cslib.Crypto.MLDSA

namespace MLDSATests

/-! ### `Decompose` with `q = 17`, `γ₂ = 2` (rounding range `4`, high bits in `[0, 4)`) -/

example : decompose 17 2 5 = (1, 1) := by decide +kernel
example : decompose 17 2 7 = (2, -1) := by decide +kernel
example : decompose 17 2 13 = (3, 1) := by decide +kernel
-- The wrap-around rule: `16 - 0 = q - 1` and `15 - (-1) = q - 1` both give high bits `0`.
example : decompose 17 2 16 = (0, -1) := by decide +kernel
example : decompose 17 2 15 = (0, -2) := by decide +kernel
-- Without the wrap-around rule, `16` would get the out-of-range high bits `4`.
example : (((16 : ZMod 17).val : ℤ) - 0) / 4 = 4 := by decide +kernel

-- Stability: `LowBits 12 = 0`, so adding `±1` keeps `HighBits = 3`.
example : highBits 17 2 (12 + 1) = highBits 17 2 12 :=
  highBits_add_of_abs_lowBits_lt (q := 17) (γ₂ := 2) (β := 1) (r := 12) (s := 1) (by decide)
    (by decide) (by decide) (by decide +kernel) (by decide +kernel)
example : highBits 17 2 (12 + -1) = highBits 17 2 12 :=
  highBits_add_of_abs_lowBits_lt (q := 17) (γ₂ := 2) (β := 1) (r := 12) (s := -1) (by decide)
    (by decide) (by decide) (by decide +kernel) (by decide +kernel)
-- ... while a value with `LowBits = 2` can change high bits under a perturbation of size `1`.
example : highBits 17 2 (2 + 1) ≠ highBits 17 2 2 := by decide +kernel

/-! ### Standard parameter sets -/

example : Params.mldsa44.γ₂ = 95232 ∧ Params.mldsa65.γ₂ = 261888 ∧ Params.mldsa87.γ₂ = 261888 :=
  ⟨rfl, rfl, rfl⟩
example : Params.mldsa44.β = Params.mldsa44.τ * Params.mldsa44.η ∧
    Params.mldsa65.β = Params.mldsa65.τ * Params.mldsa65.η ∧
    Params.mldsa87.β = Params.mldsa87.τ * Params.mldsa87.η := ⟨rfl, rfl, rfl⟩
example : (Params.mldsa44.q - 1) / (2 * Params.mldsa44.γ₂) = 44 := by decide
example : (Params.mldsa65.q - 1) / (2 * Params.mldsa65.γ₂) = 16 := by decide
example : Params.mldsa44.Valid ∧ Params.mldsa65.Valid ∧ Params.mldsa87.Valid :=
  ⟨Params.valid_mldsa44, Params.valid_mldsa65, Params.valid_mldsa87⟩

/-! ### A toy instance: `R_17 = ℤ_17[X] / (X^2 + 1)`, `k = ℓ = 1` -/

/-- Toy parameters: `n = 2`, `q = 17`, `γ₁ = 6`, `γ₂ = 2`, `τ = η = β = 1`. -/
abbrev toy : Params where
  n := 2
  q := 17
  k := 1
  ℓ := 1
  η := 1
  γ₁ := 6
  γ₂ := 2
  τ := 1
  β := 1

theorem toy_valid : toy.Valid := ⟨by decide, by decide, by decide, by decide, by decide⟩

/-- A hash that depends on the high bits: challenge `1` on `w₁ = (3, 0)` and `X` otherwise. -/
def toyHash : Hash toy := fun x => if x.1 = fun _ => ![3, 0] then ![1, 0] else ![0, 1]

theorem toyHash_inBall (x) : InBall toy.τ (toyHash x) := by
  unfold toyHash
  split <;> decide +kernel

/-- `A = 3 + 2X`, `s₁ = 1`, `s₂ = 1`. -/
def toySk : SecretKey toy := ⟨Matrix.of fun _ _ => ![3, 2], fun _ => ![1, 0], fun _ => ![1, 0]⟩

theorem toySk_short : ∀ i j, |(toySk.s₂ i j).valMinAbs| ≤ toy.η := by decide +kernel

/-- The mask `y = 3 - 2X`: `A y = 13`, `HighBits(A y) = (3, 0)`, and the attempt is accepted. -/
def toyMask : Fin toy.ℓ → Fin toy.n → ZMod toy.q := fun _ => ![3, -2]

theorem toy_signAttempt :
    signAttempt toy toyHash toySk [] toyMask = some (fun _ => ![4, -2], ![1, 0]) := by
  decide +kernel

theorem toy_verify : verify toy toyHash toySk.publicKey [] (fun _ => ![4, -2], ![1, 0]) = true :=
  verify_signAttempt toy_valid toyHash_inBall toySk_short toy_signAttempt

-- Verification is not trivial: changing the response to `z = 1` changes the high bits.
example : verify toy toyHash toySk.publicKey [] (fun _ => ![1, 0], ![1, 0]) = false := by
  decide +kernel

-- Signing with this mask and one attempt can output the signature.
example : some ((fun _ => ![4, -2], ![1, 0]) : Signature toy) ∈
    (Cslib.ProbComp.eval (sign toy toyHash toySk (pure toyMask) [] 1)).support := by
  simp [sign, toy_signAttempt]

-- An aborting mask: `y = 0` gives `z = s₁ = 1`, but `LowBits(-c s₂) = LowBits(-1) = -1`.
example : signAttempt toy toyHash toySk [] (fun _ => ![0, 0]) = none := by decide +kernel

/-- The verifying signature, read as a self-target MSIS solution. -/
example : IsSelfTargetSolution toy (selfTargetHash toy toyHash) (max toy.γ₁ toy.γ₂)
    toySk.publicKey [] (forgeryLowPart toy toySk.publicKey (fun _ => ![4, -2], ![1, 0]))
    (fun _ => ![4, -2]) ![1, 0] :=
  isSelfTargetSolution_of_verify toy_valid toy_verify

end MLDSATests
