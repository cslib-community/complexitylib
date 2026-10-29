/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Crypto.Protocols.Cipher.LubyRackoff
import Mathlib.Data.ZMod.Basic

/-!
# Tests for Feistel networks and the Luby–Rackoff theorem

Checks concrete round and network evaluation, inversion, and swap-reversal conjugation over
`ZMod 7` and `BitString 4`, instantiates a two-query adaptive distinguisher with proved query
bound `Q = 2`, exercises the 3-round Luby–Rackoff CPA bounds, the 3-round CCA insecurity attack,
the 4-round strong PRF-to-random-round reduction, and the full 4-round strong PRP Luby–Rackoff
theorem, and audits the axiom dependencies of the headline theorems in
`Complexity.Crypto.Protocols.Cipher.LubyRackoff`.
-/

namespace ComplexityTests.Crypto.LubyRackoff

open Cslib Cslib.Probability Cslib.Crypto Cslib.Crypto.LubyRackoff
open scoped ENNReal

/-- Toy first round function over `ZMod 7`: `f₁(x) = 2x + 1`. -/
def f₁ (x : ZMod 7) : ZMod 7 := 2 * x + 1

/-- Toy second round function over `ZMod 7`: `f₂(x) = 3x + 4`. -/
def f₂ (x : ZMod 7) : ZMod 7 := 3 * x + 4

/-- Toy third round function over `ZMod 7`: `f₃(x) = x + 5`. -/
def f₃ (x : ZMod 7) : ZMod 7 := x + 5

/-- Toy fourth round function over `ZMod 7`: `f₄(x) = 4x + 2`. -/
def f₄ (x : ZMod 7) : ZMod 7 := 4 * x + 2

-- Concrete single-round evaluation and inversion over `ZMod 7`:
-- `feistelRound f₁ (3, 5) = (5, 3 + (2*5 + 1)) = (5, 0) (mod 7)`.
example : feistelRound f₁ (3, 5) = (5, 0) := by decide

example : feistelInvRound f₁ (5, 0) = (3, 5) := by decide

-- Concrete 3-round evaluation and inversion over `ZMod 7`:
-- Round 1: `(3, 5) ↦ (5, 3 + f₁ 5) = (5, 0)`
-- Round 2: `(5, 0) ↦ (0, 5 + f₂ 0) = (0, 2)`
-- Round 3: `(0, 2) ↦ (2, 0 + f₃ 2) = (2, 0)`
example : feistel3 f₁ f₂ f₃ (3, 5) = (2, 0) := by decide

example : (feistel3 f₁ f₂ f₃).symm (2, 0) = (3, 5) := by decide

-- Concrete 4-round evaluation and inversion over `ZMod 7`:
-- Round 4: `(2, 0) ↦ (0, 2 + f₄ 0) = (0, 4)`
example : feistel4 f₁ f₂ f₃ f₄ (3, 5) = (0, 4) := by decide

example : (feistel4 f₁ f₂ f₃ f₄).symm (0, 4) = (3, 5) := by decide

-- Concrete swap-reversal conjugation on `BitString 4` (an additive group of exponent two):
-- `(feistelNetwork [g₁, g₂, g₃]).symm = swap ∘ feistelNetwork [g₁, g₂, g₃].reverse ∘ swap`.
example (g₁ g₂ g₃ : BitString 4 → BitString 4) :
    (Equiv.prodComm (BitString 4) (BitString 4)).trans
      ((feistelNetwork [g₁, g₂, g₃].reverse).trans (Equiv.prodComm (BitString 4) (BitString 4))) =
      (feistelNetwork [g₁, g₂, g₃]).symm :=
  prodComm_trans_feistelNetwork_reverse_trans_prodComm
    (fun x => funext fun i => BooleanRing.neg_eq (x i)) [g₁, g₂, g₃]

-- Concrete 3-round evaluation and inversion on `BitString 4`.
example (g₁ g₂ g₃ : BitString 4 → BitString 4) (p : BitString 4 × BitString 4) :
    (feistel3 g₁ g₂ g₃).symm (feistel3 g₁ g₂ g₃ p) = p :=
  (feistel3 g₁ g₂ g₃).symm_apply_apply p

/-- Concrete two-query adaptive distinguisher over `ZMod 7 × ZMod 7`: queries `(0, 1)`, then
adaptively queries the returned pair `vw₁`, and outputs whether the two right outputs agree. -/
def sampleDistinguisher : OracleComp (fun _ : ZMod 7 × ZMod 7 => ZMod 7 × ZMod 7) Bool := do
  let vw₁ ← OracleComp.query (spec := fun _ : ZMod 7 × ZMod 7 => ZMod 7 × ZMod 7) (0, 1)
  let vw₂ ← OracleComp.query (spec := fun _ : ZMod 7 × ZMod 7 => ZMod 7 × ZMod 7) vw₁
  return decide (vw₁.2 = vw₂.2)

theorem isQueryBounded_sampleDistinguisher :
    OracleComp.IsQueryBounded sampleDistinguisher 2 := by
  refine ((OracleComp.IsCostBounded.query (0, 1)).bind fun vw₁ =>
    (OracleComp.IsCostBounded.query vw₁).bind fun vw₂ =>
      OracleComp.IsCostBounded.pure _ 0).mono (by omega)

-- Concrete instantiation of the 3-round Luby–Rackoff random-round security bound over `ZMod 7`
-- for `sampleDistinguisher` (`Q = 2`, `Q.choose 2 = 1`, bound `2 * 1 * 7⁻¹`).
example :
    (Game.advantage (feistel3RandomRoundsGame sampleDistinguisher)
      (randomFunctionGame sampleDistinguisher) : ℝ) ≤
      2 * ((2 : ℕ).choose 2 : ℝ) * (Fintype.card (ZMod 7) : ℝ)⁻¹ :=
  advantage_feistel3RandomRoundsGame_randomFunctionGame_le isQueryBounded_sampleDistinguisher

-- Concrete instantiation of the Δ-universal Round-1 Luby–Rackoff bound over `ZMod 7`.
example :
    (Game.advantage
      (feistel3HashIdealGame (PMF.uniformOfFintype (ZMod 7 → ZMod 7)) id sampleDistinguisher)
      (randomFunctionGame sampleDistinguisher) : ℝ) ≤
      ((2 : ℕ).choose 2 : ℝ) * ((Fintype.card (ZMod 7) : ℝ≥0∞)⁻¹).toReal +
        ((2 : ℕ).choose 2 : ℝ) * (Fintype.card (ZMod 7) : ℝ)⁻¹ := by
  refine advantage_feistel3HashIdealGame_randomFunctionGame_le
    isDeltaUniversalHash_uniformOfFintype ?_ isQueryBounded_sampleDistinguisher
  exact ENNReal.inv_ne_top.mpr (by simp)

-- Concrete instantiation of the full keyed 3-round Luby–Rackoff PRF theorem over `ZMod 7`.
example (keyGen : PMF (ZMod 7)) (F : ZMod 7 → ZMod 7 → ZMod 7) {ε₁ ε₂ ε₃ : ℝ}
    (h₁ : ∀ g₂ g₃,
      (Game.advantage (prfSingleRealGame keyGen F (feistel3Reduction₁ g₂ g₃ sampleDistinguisher))
        (prfSingleIdealGame (feistel3Reduction₁ g₂ g₃ sampleDistinguisher)) : ℝ) ≤ ε₁)
    (h₂ : ∀ g₁ g₃,
      (Game.advantage (prfSingleRealGame keyGen F (feistel3Reduction₂ g₁ g₃ sampleDistinguisher))
        (prfSingleIdealGame (feistel3Reduction₂ g₁ g₃ sampleDistinguisher)) : ℝ) ≤ ε₂)
    (h₃ : ∀ g₁ g₂,
      (Game.advantage (prfSingleRealGame keyGen F (feistel3Reduction₃ g₁ g₂ sampleDistinguisher))
        (prfSingleIdealGame (feistel3Reduction₃ g₁ g₂ sampleDistinguisher)) : ℝ) ≤ ε₃) :
    (Game.advantage (feistel3KeyedGame keyGen F sampleDistinguisher)
      (randomFunctionGame sampleDistinguisher) : ℝ) ≤
      ε₁ + ε₂ + ε₃ + 2 * ((2 : ℕ).choose 2 : ℝ) * (Fintype.card (ZMod 7) : ℝ)⁻¹ :=
  advantage_feistel3KeyedGame_randomFunctionGame_le isQueryBounded_sampleDistinguisher h₁ h₂ h₃

-- Concrete instantiation of the 3-round Luby–Rackoff PRP bound against a uniform random
-- permutation (`idealPermGame`) over `ZMod 7 × ZMod 7`.
example :
    (Game.advantage (feistel3RandomRoundsGame sampleDistinguisher)
      (idealPermGame sampleDistinguisher) : ℝ) ≤
      2 * ((2 : ℕ).choose 2 : ℝ) * (Fintype.card (ZMod 7) : ℝ)⁻¹ +
        ((2 : ℕ).choose 2 : ℝ) * ((Fintype.card (ZMod 7) : ℝ)⁻¹) ^ 2 :=
  advantage_feistel3RandomRoundsGame_idealPermGame_le isQueryBounded_sampleDistinguisher

-- Concrete instantiation of the full keyed 3-round Luby–Rackoff PRP theorem over `ZMod 7`.
example (keyGen : PMF (ZMod 7)) (F : ZMod 7 → ZMod 7 → ZMod 7) {ε₁ ε₂ ε₃ : ℝ}
    (h₁ : ∀ g₂ g₃,
      (Game.advantage (prfSingleRealGame keyGen F (feistel3Reduction₁ g₂ g₃ sampleDistinguisher))
        (prfSingleIdealGame (feistel3Reduction₁ g₂ g₃ sampleDistinguisher)) : ℝ) ≤ ε₁)
    (h₂ : ∀ g₁ g₃,
      (Game.advantage (prfSingleRealGame keyGen F (feistel3Reduction₂ g₁ g₃ sampleDistinguisher))
        (prfSingleIdealGame (feistel3Reduction₂ g₁ g₃ sampleDistinguisher)) : ℝ) ≤ ε₂)
    (h₃ : ∀ g₁ g₂,
      (Game.advantage (prfSingleRealGame keyGen F (feistel3Reduction₃ g₁ g₂ sampleDistinguisher))
        (prfSingleIdealGame (feistel3Reduction₃ g₁ g₂ sampleDistinguisher)) : ℝ) ≤ ε₃) :
    (Game.advantage (feistel3KeyedGame keyGen F sampleDistinguisher)
      (idealPermGame sampleDistinguisher) : ℝ) ≤
      ε₁ + ε₂ + ε₃ + 2 * ((2 : ℕ).choose 2 : ℝ) * (Fintype.card (ZMod 7) : ℝ)⁻¹ +
        ((2 : ℕ).choose 2 : ℝ) * ((Fintype.card (ZMod 7) : ℝ)⁻¹) ^ 2 :=
  advantage_feistel3KeyedGame_idealPermGame_le isQueryBounded_sampleDistinguisher h₁ h₂ h₃

-- Concrete instantiation of the bit-string specialization on `BitString 4`.
example (D : OracleComp (fun _ : BitString 4 × BitString 4 => BitString 4 × BitString 4) Bool)
    (hQ : OracleComp.IsQueryBounded D 2) :
    (Game.advantage (feistel3RandomRoundsGame D) (randomFunctionGame D) : ℝ) ≤
      2 * ((2 : ℕ).choose 2 : ℝ) * ((2 : ℝ) ^ 4)⁻¹ :=
  advantage_feistel3RandomRoundsGame_bitString_le 4 hQ

-- Concrete instantiation of the 3-round CCA attack over `ZMod 7` with `l₀ = 0`, `l₁ = 1`, `r₀ = 2`.
example :
    OracleComp.interpret (feistelStrongOracle (feistel3 f₁ f₂ f₃))
      (feistel3CCAAttack (0 : ZMod 7) 1 2) = PMF.pure true :=
  eval_feistel3_feistel3CCAAttack f₁ f₂ f₃ 0 1 2

-- Equal-input (`l₀ = l₁ = 0`) sanity check: both 3-round Feistel and the permutation-ideal
-- `idealStrongGame` accept with probability `1`, giving advantage `0`.
example :
    idealStrongGame (feistel3CCAAttack (0 : ZMod 7) 0 2) = PMF.pure true :=
  idealStrongGame_feistel3CCAAttack_self 0 2

example :
    Game.advantage
      (OracleComp.interpret (feistelStrongOracle (feistel3 f₁ f₂ f₃))
        (feistel3CCAAttack (0 : ZMod 7) 0 2))
      (idealStrongGame (feistel3CCAAttack (0 : ZMod 7) 0 2)) = 0 :=
  advantage_feistel3CCAAttack_self f₁ f₂ f₃ 0 2

-- Separation against the true bidirectional random-permutation game `idealStrongGame` over
-- `ZMod 7` (`l₀ = 0, l₁ = 1, l₂ = 2, r₀ = 2`).
example :
    (Fintype.card (Equiv.Perm (ZMod 7 × ZMod 7)) : ℝ)⁻¹ ≤
      (Game.advantage
        (OracleComp.interpret (feistelStrongOracle (feistel3 f₁ f₂ f₃))
          (feistel3CCAAttack (0 : ZMod 7) 1 2))
        (idealStrongGame (feistel3CCAAttack (0 : ZMod 7) 1 2)) : ℝ) :=
  le_advantage_feistel3CCAAttack_idealStrongGame f₁ f₂ f₃
    (l₂ := (2 : ZMod 7)) (by decide) (by decide) (by decide)

example :
    0 < (Game.advantage
      (OracleComp.interpret (feistelStrongOracle (feistel3 f₁ f₂ f₃))
        (feistel3CCAAttack (0 : ZMod 7) 1 2))
      (idealStrongGame (feistel3CCAAttack (0 : ZMod 7) 1 2)) : ℝ) :=
  advantage_feistel3CCAAttack_idealStrongGame_pos f₁ f₂ f₃
    (l₂ := (2 : ZMod 7)) (by decide) (by decide) (by decide)

-- Quantitative nonnegligible lower bound `1 - 1 / |G| - 4 / |G|²` against `idealStrongGame`
-- over `ZMod 7` (`l₀ = 0 ≠ 1 = l₁, r₀ = 2`, giving advantage at least `38 / 49`).
example :
    1 - (Fintype.card (ZMod 7) : ℝ)⁻¹ - 4 * ((Fintype.card (ZMod 7) : ℝ)⁻¹) ^ 2 ≤
      (Game.advantage
        (OracleComp.interpret (feistelStrongOracle (feistel3 f₁ f₂ f₃))
          (feistel3CCAAttack (0 : ZMod 7) 1 2))
        (idealStrongGame (feistel3CCAAttack (0 : ZMod 7) 1 2)) : ℝ) :=
  le_advantage_feistel3CCAAttack_idealStrongGame_of_ne f₁ f₂ f₃ (by decide)

-- Concrete `Fin 3` instance for `RandomPermutation.uniform_interpret_eq_lazy` and
-- `RandomPermutation.abs_sub_uniformPerm_forgetful_le`.
example (program : OracleComp (RandomPermutation.PermOracleSpec (Fin 3)) Bool) :
    (do
      let π ← PMF.uniformOfFintype (Equiv.Perm (Fin 3))
      OracleComp.interpret (fun q => PMF.pure (RandomPermutation.evalPerm π q)) program) =
    (((OracleComp.interpret RandomPermutation.answer program).run []).map Prod.fst) :=
  RandomPermutation.uniform_interpret_eq_lazy program

example (program : OracleComp (RandomPermutation.PermOracleSpec (Fin 3)) Bool)
    (hQ : OracleComp.IsQueryBounded program 2) :
    |(((do
        let π ← PMF.uniformOfFintype (Equiv.Perm (Fin 3))
        OracleComp.interpret (fun q => PMF.pure (RandomPermutation.evalPerm π q)) program).bind
          PMF.pure) true).toReal -
      (((((OracleComp.interpret RandomPermutation.forgetfulAnswer program).run []).map
        Prod.fst).bind PMF.pure) true).toReal| ≤
      ((2 : ℕ).choose 2 : ℝ) * (Fintype.card (Fin 3) : ℝ)⁻¹ :=
  RandomPermutation.abs_sub_uniformPerm_forgetful_le hQ PMF.pure true

-- Separation against the independent-table game `independentTableStrongGame` over `ZMod 7`.
example :
    independentTableStrongGame (feistel3CCAAttack (0 : ZMod 7) 1 2) true =
      (Fintype.card (ZMod 7) : ℝ≥0∞)⁻¹ :=
  eval_independentTableStrongGame_feistel3CCAAttack 0 1 2

example :
    (Game.advantage
      (OracleComp.interpret (feistelStrongOracle (feistel3 f₁ f₂ f₃))
        (feistel3CCAAttack (0 : ZMod 7) 1 2))
      (independentTableStrongGame (feistel3CCAAttack (0 : ZMod 7) 1 2)) : ℝ) =
      1 - (Fintype.card (ZMod 7) : ℝ)⁻¹ :=
  advantage_feistel3CCAAttack_independentTable f₁ f₂ f₃ 0 1 2

-- Concrete instantiation of the 4-round strong PRF-to-random-round hybrid bound over `ZMod 7`.
example (keyGen : PMF (ZMod 7)) (F : ZMod 7 → ZMod 7 → ZMod 7) {ε₁ ε₂ ε₃ ε₄ : ℝ}
    (h₁ : ∀ g₂ g₃ g₄,
      (Game.advantage
        (prfSingleRealGame keyGen F
          (feistel4StrongReduction₁ g₂ g₃ g₄ (feistel3CCAAttack (0 : ZMod 7) 1 2)))
        (prfSingleIdealGame
          (feistel4StrongReduction₁ g₂ g₃ g₄ (feistel3CCAAttack (0 : ZMod 7) 1 2))) : ℝ) ≤ ε₁)
    (h₂ : ∀ g₁ g₃ g₄,
      (Game.advantage
        (prfSingleRealGame keyGen F
          (feistel4StrongReduction₂ g₁ g₃ g₄ (feistel3CCAAttack (0 : ZMod 7) 1 2)))
        (prfSingleIdealGame
          (feistel4StrongReduction₂ g₁ g₃ g₄ (feistel3CCAAttack (0 : ZMod 7) 1 2))) : ℝ) ≤ ε₂)
    (h₃ : ∀ g₁ g₂ g₄,
      (Game.advantage
        (prfSingleRealGame keyGen F
          (feistel4StrongReduction₃ g₁ g₂ g₄ (feistel3CCAAttack (0 : ZMod 7) 1 2)))
        (prfSingleIdealGame
          (feistel4StrongReduction₃ g₁ g₂ g₄ (feistel3CCAAttack (0 : ZMod 7) 1 2))) : ℝ) ≤ ε₃)
    (h₄ : ∀ g₁ g₂ g₃,
      (Game.advantage
        (prfSingleRealGame keyGen F
          (feistel4StrongReduction₄ g₁ g₂ g₃ (feistel3CCAAttack (0 : ZMod 7) 1 2)))
        (prfSingleIdealGame
          (feistel4StrongReduction₄ g₁ g₂ g₃ (feistel3CCAAttack (0 : ZMod 7) 1 2))) : ℝ) ≤ ε₄) :
    (Game.advantage
      (feistel4StrongKeyedGame keyGen F (feistel3CCAAttack (0 : ZMod 7) 1 2))
      (feistel4StrongRandomRoundsGame (feistel3CCAAttack (0 : ZMod 7) 1 2)) : ℝ) ≤
      ε₁ + ε₂ + ε₃ + ε₄ :=
  advantage_feistel4StrongKeyedGame_feistel4StrongRandomRoundsGame_le h₁ h₂ h₃ h₄

-- Concrete instantiation of the 4-round strong Luby–Rackoff random-round collision bound over
-- `ZMod 7` for `feistel3CCAAttack 0 1 2` (`Q = 3`, `Q.choose 2 = 3`).
example :
    (Game.advantage
      (feistel4StrongRandomRoundsGame (feistel3CCAAttack (0 : ZMod 7) 1 2))
      (idealStrongGame (feistel3CCAAttack (0 : ZMod 7) 1 2)) : ℝ) ≤
      2 * ((3 : ℕ).choose 2 : ℝ) * (Fintype.card (ZMod 7) : ℝ)⁻¹ +
        2 * ((3 : ℕ).choose 2 : ℝ) * ((Fintype.card (ZMod 7) : ℝ)⁻¹) ^ 2 :=
  advantage_feistel4StrongRandomRoundsGame_idealStrongGame_le
    (isQueryBounded_feistel3CCAAttack 0 1 2)

-- Concrete instantiation of the full 4-round strong PRP Luby–Rackoff theorem over `ZMod 7`.
example (keyGen : PMF (ZMod 7)) (F : ZMod 7 → ZMod 7 → ZMod 7) {ε₁ ε₂ ε₃ ε₄ : ℝ}
    (h₁ : ∀ g₂ g₃ g₄,
      (Game.advantage
        (prfSingleRealGame keyGen F
          (feistel4StrongReduction₁ g₂ g₃ g₄ (feistel3CCAAttack (0 : ZMod 7) 1 2)))
        (prfSingleIdealGame
          (feistel4StrongReduction₁ g₂ g₃ g₄ (feistel3CCAAttack (0 : ZMod 7) 1 2))) : ℝ) ≤ ε₁)
    (h₂ : ∀ g₁ g₃ g₄,
      (Game.advantage
        (prfSingleRealGame keyGen F
          (feistel4StrongReduction₂ g₁ g₃ g₄ (feistel3CCAAttack (0 : ZMod 7) 1 2)))
        (prfSingleIdealGame
          (feistel4StrongReduction₂ g₁ g₃ g₄ (feistel3CCAAttack (0 : ZMod 7) 1 2))) : ℝ) ≤ ε₂)
    (h₃ : ∀ g₁ g₂ g₄,
      (Game.advantage
        (prfSingleRealGame keyGen F
          (feistel4StrongReduction₃ g₁ g₂ g₄ (feistel3CCAAttack (0 : ZMod 7) 1 2)))
        (prfSingleIdealGame
          (feistel4StrongReduction₃ g₁ g₂ g₄ (feistel3CCAAttack (0 : ZMod 7) 1 2))) : ℝ) ≤ ε₃)
    (h₄ : ∀ g₁ g₂ g₃,
      (Game.advantage
        (prfSingleRealGame keyGen F
          (feistel4StrongReduction₄ g₁ g₂ g₃ (feistel3CCAAttack (0 : ZMod 7) 1 2)))
        (prfSingleIdealGame
          (feistel4StrongReduction₄ g₁ g₂ g₃ (feistel3CCAAttack (0 : ZMod 7) 1 2))) : ℝ) ≤ ε₄) :
    (Game.advantage
      (feistel4StrongKeyedGame keyGen F (feistel3CCAAttack (0 : ZMod 7) 1 2))
      (idealStrongGame (feistel3CCAAttack (0 : ZMod 7) 1 2)) : ℝ) ≤
      ε₁ + ε₂ + ε₃ + ε₄ +
        2 * ((3 : ℕ).choose 2 : ℝ) * (Fintype.card (ZMod 7) : ℝ)⁻¹ +
        2 * ((3 : ℕ).choose 2 : ℝ) * ((Fintype.card (ZMod 7) : ℝ)⁻¹) ^ 2 :=
  advantage_feistel4StrongKeyedGame_idealStrongGame_le
    (isQueryBounded_feistel3CCAAttack 0 1 2) h₁ h₂ h₃ h₄

-- Concrete instantiation of the 4-round strong Luby–Rackoff bit-string specialization on
-- `BitString 4`.
example
    (D : OracleComp (fun _ : Bool × (BitString 4 × BitString 4) => BitString 4 × BitString 4) Bool)
    (hQ : OracleComp.IsQueryBounded D 2) :
    (Game.advantage (feistel4StrongRandomRoundsGame D) (idealStrongGame D) : ℝ) ≤
      2 * ((2 : ℕ).choose 2 : ℝ) * ((2 : ℝ) ^ 4)⁻¹ +
        2 * ((2 : ℕ).choose 2 : ℝ) * (((2 : ℝ) ^ 4)⁻¹) ^ 2 :=
  advantage_feistel4StrongRandomRoundsGame_bitString_le 4 hQ

-- Concrete 3-round vs. 4-round CCA separation on `BitString 4`: for the 3-query attack
-- `feistel3CCAAttack 0 (fun _ => true) 0`, 4-round random-round Feistel has strong-PRP advantage
-- strictly below `1 / 2` (`51 / 128`), whereas every 3-round Feistel network `feistel3 f₁ f₂ f₃`
-- has CCA advantage strictly above `1 / 2` (`59 / 64`).
example (f₁ f₂ f₃ : BitString 4 → BitString 4) :
    (Game.advantage
      (feistel4StrongRandomRoundsGame
        (feistel3CCAAttack (0 : BitString 4) (fun _ => true) 0))
      (idealStrongGame
        (feistel3CCAAttack (0 : BitString 4) (fun _ => true) 0)) : ℝ) <
    (Game.advantage
      (OracleComp.interpret (feistelStrongOracle (feistel3 f₁ f₂ f₃))
        (feistel3CCAAttack (0 : BitString 4) (fun _ => true) 0))
      (idealStrongGame
        (feistel3CCAAttack (0 : BitString 4) (fun _ => true) 0)) : ℝ) := by
  have hne : (0 : BitString 4) ≠ (fun _ => true) := by
    intro h
    have := congrFun h 0
    revert this
    decide
  have h4 := advantage_feistel4StrongRandomRoundsGame_bitString_le 4
    (isQueryBounded_feistel3CCAAttack (0 : BitString 4) (fun _ => true) 0)
  have h3 := le_advantage_feistel3CCAAttack_idealStrongGame_of_ne f₁ f₂ f₃ (r₀ := (0 : BitString 4))
    hne
  simp only [Fintype.card_pi, Fintype.card_fin, Fintype.card_bool, Finset.prod_const,
    Finset.card_univ, Nat.cast_pow, Nat.cast_ofNat] at h3
  have hchoose : ((3 : ℕ).choose 2 : ℝ) = 3 := by norm_num
  rw [hchoose] at h4
  linarith

/--
info: 'Cslib.Crypto.LubyRackoff.prodComm_trans_feistelNetwork_reverse_trans_prodComm' depends on
axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.LubyRackoff.prodComm_trans_feistelNetwork_reverse_trans_prodComm

end ComplexityTests.Crypto.LubyRackoff
