/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.DiffieHellman

/-!
# Two-, three- and six-draw approximate exponent sampling bounds

`Cslib.Crypto.PrimeOrderGroupFamily.sampleExp` samples an exponent modulo `F.order d` within
statistical distance `1 / 2 ^ n` of exact uniform on `ZMod (F.order d)`. By intermediate hybrid
hops, replacing two (three, six) independent `sampleExp n d` draws by as many independent exact
uniform draws changes `Game.advantage` by at most `2 / 2 ^ n` (`3 / 2 ^ n`, `6 / 2 ^ n`).

## Main results

* `Cslib.Crypto.PrimeOrderGroupFamily.advantage_bind_sampleExp_pair_le`: replacing two independent
  `sampleExp n d` draws by two independent uniform draws on `ZMod (F.order d)` changes
  `Game.advantage` by at most `2 / 2 ^ n`.
* `Cslib.Crypto.PrimeOrderGroupFamily.advantage_bind_sampleExp_triple_le`: the same for three
  draws, with loss at most `3 / 2 ^ n`.
* `Cslib.Crypto.PrimeOrderGroupFamily.advantage_bind_sampleExp_six_le`: the same for six draws,
  with loss at most `6 / 2 ^ n`.
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

/-- Replacing three independent `sampleExp n d` draws by three independent exact uniform draws on
`ZMod (F.order d)` changes `Game.advantage` by at most `3 / 2 ^ n`. -/
theorem advantage_bind_sampleExp_triple_le (n : ℕ) (d : F.Desc)
    (k : ZMod (F.order d) → ZMod (F.order d) → ZMod (F.order d) → Game) :
    Game.advantage
      ((ProbComp.eval (F.sampleExp n d)).bind fun a =>
        (ProbComp.eval (F.sampleExp n d)).bind fun b =>
          (ProbComp.eval (F.sampleExp n d)).bind fun c =>
            k (a : ZMod (F.order d)) (b : ZMod (F.order d)) (c : ZMod (F.order d)))
      ((PMF.uniformOfFintype (ZMod (F.order d))).bind fun α =>
        (PMF.uniformOfFintype (ZMod (F.order d))).bind fun β =>
          (PMF.uniformOfFintype (ZMod (F.order d))).bind fun γ => k α β γ) ≤
      3 / 2 ^ n := by
  refine (Game.advantage_triangle _
    ((PMF.uniformOfFintype (ZMod (F.order d))).bind fun α =>
      (ProbComp.eval (F.sampleExp n d)).bind fun b =>
        (ProbComp.eval (F.sampleExp n d)).bind fun c =>
          k α (b : ZMod (F.order d)) (c : ZMod (F.order d))) _).trans ?_
  have h1 := F.advantage_bind_sampleExp_le n d (fun α =>
    (ProbComp.eval (F.sampleExp n d)).bind fun b =>
      (ProbComp.eval (F.sampleExp n d)).bind fun c =>
        k α (b : ZMod (F.order d)) (c : ZMod (F.order d)))
  have h2 := Game.advantage_bind_le_nnreal (PMF.uniformOfFintype (ZMod (F.order d))) _ _
    (fun α => F.advantage_bind_sampleExp_pair_le n d (k α))
  calc _ ≤ (1 : ℝ≥0) / 2 ^ n + 2 / 2 ^ n := add_le_add h1 h2
    _ = 3 / 2 ^ n := by rw [← add_div]; norm_num

/-- Replacing six independent `sampleExp n d` draws by six independent exact uniform draws on
`ZMod (F.order d)` changes `Game.advantage` by at most `6 / 2 ^ n`. -/
theorem advantage_bind_sampleExp_six_le (n : ℕ) (d : F.Desc)
    (k : ZMod (F.order d) → ZMod (F.order d) → ZMod (F.order d) → ZMod (F.order d) →
      ZMod (F.order d) → ZMod (F.order d) → Game) :
    Game.advantage
      ((ProbComp.eval (F.sampleExp n d)).bind fun a₁ =>
        (ProbComp.eval (F.sampleExp n d)).bind fun a₂ =>
          (ProbComp.eval (F.sampleExp n d)).bind fun a₃ =>
            (ProbComp.eval (F.sampleExp n d)).bind fun a₄ =>
              (ProbComp.eval (F.sampleExp n d)).bind fun a₅ =>
                (ProbComp.eval (F.sampleExp n d)).bind fun a₆ =>
                  k a₁ a₂ a₃ a₄ a₅ a₆)
      ((PMF.uniformOfFintype (ZMod (F.order d))).bind fun α₁ =>
        (PMF.uniformOfFintype (ZMod (F.order d))).bind fun α₂ =>
          (PMF.uniformOfFintype (ZMod (F.order d))).bind fun α₃ =>
            (PMF.uniformOfFintype (ZMod (F.order d))).bind fun α₄ =>
              (PMF.uniformOfFintype (ZMod (F.order d))).bind fun α₅ =>
                (PMF.uniformOfFintype (ZMod (F.order d))).bind fun α₆ =>
                  k α₁ α₂ α₃ α₄ α₅ α₆) ≤
      6 / 2 ^ n := by
  let S := ProbComp.eval (F.sampleExp n d)
  let U := PMF.uniformOfFintype (ZMod (F.order d))
  have h1 : Game.advantage
      (S.bind fun a₁ => S.bind fun a₂ => S.bind fun a₃ =>
        S.bind fun a₄ => S.bind fun a₅ => S.bind fun a₆ =>
          k a₁ a₂ a₃ a₄ a₅ a₆)
      (S.bind fun a₁ => S.bind fun a₂ => S.bind fun a₃ =>
        U.bind fun α₄ => U.bind fun α₅ => U.bind fun α₆ => k a₁ a₂ a₃ α₄ α₅ α₆) ≤ 3 / 2 ^ n :=
    Game.advantage_bind_le_nnreal _ _ _ fun a₁ => Game.advantage_bind_le_nnreal _ _ _ fun a₂ =>
      Game.advantage_bind_le_nnreal _ _ _ fun a₃ =>
        F.advantage_bind_sampleExp_triple_le n d (k a₁ a₂ a₃)
  have h2 : Game.advantage
      (S.bind fun a₁ => S.bind fun a₂ => S.bind fun a₃ =>
        U.bind fun α₄ => U.bind fun α₅ => U.bind fun α₆ => k a₁ a₂ a₃ α₄ α₅ α₆)
      (U.bind fun α₁ => U.bind fun α₂ => U.bind fun α₃ =>
        U.bind fun α₄ => U.bind fun α₅ => U.bind fun α₆ => k α₁ α₂ α₃ α₄ α₅ α₆) ≤ 3 / 2 ^ n :=
    F.advantage_bind_sampleExp_triple_le n d fun α₁ α₂ α₃ =>
      U.bind fun α₄ => U.bind fun α₅ => U.bind fun α₆ => k α₁ α₂ α₃ α₄ α₅ α₆
  calc _ ≤ (3 : ℝ≥0) / 2 ^ n + 3 / 2 ^ n := (Game.advantage_triangle _ _ _).trans (add_le_add h1 h2)
    _ = 6 / 2 ^ n := by rw [← add_div]; norm_num

end Cslib.Crypto.PrimeOrderGroupFamily
