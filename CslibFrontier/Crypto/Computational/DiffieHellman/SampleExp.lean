/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.DiffieHellman

/-!
# Two-draw approximate exponent sampling bound

`Cslib.Crypto.PrimeOrderGroupFamily.sampleExp` samples an exponent modulo `F.order d` within
statistical distance `1 / 2 ^ n` of exact uniform on `ZMod (F.order d)`. By a single intermediate
hybrid hop, replacing two independent `sampleExp n d` draws by two independent exact uniform draws
changes `Game.advantage` by at most `2 / 2 ^ n`.

## Main results

* `Cslib.Crypto.PrimeOrderGroupFamily.advantage_bind_sampleExp_pair_le`: replacing two independent
  `sampleExp n d` draws by two independent uniform draws on `ZMod (F.order d)` changes
  `Game.advantage` by at most `2 / 2 ^ n`.
-/

public section

namespace Cslib.Crypto.PrimeOrderGroupFamily

open Probability
open scoped NNReal

variable (F : PrimeOrderGroupFamily)

/-- Replacing two independent `sampleExp n d` draws by two independent exact uniform draws on
`ZMod (F.order d)` changes `Game.advantage` by at most `2 / 2 ^ n`. -/
theorem advantage_bind_sampleExp_pair_le (n : ℕ) (d : F.Desc)
    (k : ZMod (F.order d) → ZMod (F.order d) → Game) :
    Game.advantage
      ((ProbComp.eval (F.sampleExp n d)).bind fun a =>
        (ProbComp.eval (F.sampleExp n d)).bind fun b =>
          k (a : ZMod (F.order d)) (b : ZMod (F.order d)))
      ((PMF.uniformOfFintype (ZMod (F.order d))).bind fun α =>
        (PMF.uniformOfFintype (ZMod (F.order d))).bind fun β => k α β) ≤
      2 / 2 ^ n := by
  refine (Game.advantage_triangle _
    ((PMF.uniformOfFintype (ZMod (F.order d))).bind fun α =>
      (ProbComp.eval (F.sampleExp n d)).bind fun b =>
        k α (b : ZMod (F.order d))) _).trans ?_
  have h1 := F.advantage_bind_sampleExp_le n d (fun α =>
    (ProbComp.eval (F.sampleExp n d)).bind fun b => k α (b : ZMod (F.order d)))
  have h2 := Game.advantage_bind_le_nnreal (PMF.uniformOfFintype (ZMod (F.order d))) _ _
    (fun α => F.advantage_bind_sampleExp_le n d (k α))
  calc _ ≤ (1 : ℝ≥0) / 2 ^ n + 1 / 2 ^ n := add_le_add h1 h2
    _ = 2 / 2 ^ n := by rw [← add_div, one_add_one_eq_two]

end Cslib.Crypto.PrimeOrderGroupFamily
