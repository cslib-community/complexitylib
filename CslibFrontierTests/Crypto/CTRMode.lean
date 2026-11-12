/-
Copyright (c) 2026 Karn Seth, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth, Samuel Schlesinger
-/
import CslibFrontier.Crypto.Computational.Encryption.CTRMode

/-!
# Tests for Counter (CTR) Mode CPA Security

Concrete evaluations and non-vacuity witnesses for
`CslibFrontier/Crypto/Computational/Encryption/CTRMode.lean`. The headline bounds are instantiated
on a concrete left-or-right adversary (`ctrOneQueryAdversary`) with proven hypotheses at parameters
(`n = 8`, `ℓ = 2`, `K = 2`) where every collision term is strictly below `1`.
-/
namespace CslibFrontierTests.Crypto.CTRMode
open Cslib Cslib.Probability Cslib.Crypto

/-! ### CTR queries and block costs -/

/-- A valid left-or-right query: two messages of two 8-bit blocks each. -/
def ctrQueryLR : BlockModeQuery 8 := ([0, 1], [1, 1])

/-- Answering keystream calls starting at offset `i` evaluates `f (counter iv j)` along
`i, i + 1, …, i + k - 1`. -/
example (f : BitString 8 → BitString 8) (counter : BitString 8 → ℕ → BitString 8)
    (iv : BitString 8) :
    OracleComp.interpret (OracleComp.sumHandler ProbComp.unifFin fun y => pure (f y))
        (ctrMaskQueriesFrom counter iv 3 2) =
      (pure [f (counter iv 3), f (counter iv 4)] : ProbComp (List (BitString 8))) := by
  simpa [List.range'_succ] using interpret_ctrMaskQueriesFrom f counter iv 3 2

/-! ### Modular counter schedule checks -/

/-- For `ℓ ≤ 2 ^ n`, `ctrModCounter` has distinct offsets below `ℓ` and is injective in the IV. -/
example : ctrModCounter (n := 4) 0 0 ≠ ctrModCounter (n := 4) 0 1 ∧
    ctrModCounter (n := 4) 15 0 ≠ ctrModCounter (n := 4) 15 15 ∧
    ctrModCounter (n := 4) 0 7 ≠ ctrModCounter (n := 4) 1 7 :=
  ⟨ctrModCounter_injOn (n := 4) (ℓ := 16) le_rfl 0 (by decide) (by decide) (by decide),
   ctrModCounter_injOn (n := 4) (ℓ := 16) le_rfl 15 (by decide) (by decide) (by decide),
   fun h => by have := ctrModCounter_injective_left (n := 4) 7 h; revert this; decide⟩

/-! ### Concrete adversary and non-vacuous security bounds -/

/-- A one-query adversary: asks `ctrQueryLR` and outputs `true` when the first ciphertext block is
zero. -/
def ctrOneQueryAdversary : BlockModeAdversary 8 := do
  let r ← ProbOracleComp.query (spec := BlockModeSpec 8) ctrQueryLR
  return decide (r.2.head? = some 0)

/-- The adversary asks for two blocks in total, with at most two blocks per query. -/
theorem isCostBounded_ctrOneQueryAdversary :
    OracleComp.IsCostBounded (blockModeCost 2) ctrOneQueryAdversary 2 := by
  unfold ctrOneQueryAdversary ProbOracleComp.query
  exact OracleComp.IsCostBounded.mono
    (OracleComp.IsCostBounded.bind (OracleComp.IsCostBounded.query (Sum.inr ctrQueryLR)) fun _ =>
      OracleComp.IsCostBounded.pure _ 0)
    (by decide)

/-- The PRF reduction for the adversary makes at most two oracle calls. -/
example :
    ProbOracleComp.IsQueryBounded (ctrReduction ctrModCounter 2 true ctrOneQueryAdversary) 2 :=
  isQueryBounded_ctrReduction ctrModCounter 2 true isCostBounded_ctrOneQueryAdversary

/-- Simple keyed block function `F k x = k + x` on 8-bit blocks. -/
def xorKeyed (k x : BitString 8) : BitString 8 := k + x

/-- The CTR experiment for `xorKeyed` equals the real PRF experiment for the reduction. -/
example : ctrCpaGame ctrModCounter xorKeyed 2 true ctrOneQueryAdversary =
    PRF.realGame xorKeyed (ctrReduction ctrModCounter 2 true ctrOneQueryAdversary) :=
  ctrCpaGame_eq_realGame ctrModCounter xorKeyed 2 true ctrOneQueryAdversary

/-- Against a uniform random function on 8-bit blocks, the reduction's view is within
`2 ^ 2 / 2 ^ 8 = 1 / 64` of the ideal CTR experiment. -/
example :
    (Game.advantage
        (PRF.idealGame (ctrReduction ctrModCounter 2 false ctrOneQueryAdversary))
        (blockModeIdealGame 2 ctrOneQueryAdversary) : ℝ) ≤ 1 / 64 :=
  (advantage_idealGame_ctrReduction_le ctrModCounter 2 false isCostBounded_ctrOneQueryAdversary
    (fun iv _ _ hi hj hij => ctrModCounter_injOn (by decide) iv hi hj hij)
    (fun i _ => ctrModCounter_injective_left i)).trans_eq (by norm_num)

/-- Modular CTR mode with a uniform random function on 8-bit blocks (`ℓ = 2`, `K = 2`):
the left-or-right advantage is at most `2 * 2 ^ 2 / 2 ^ 8 = 1 / 32`. -/
example :
    (Game.advantage
        (ctrCpaGame ctrModCounter (fun f : BitString 8 → BitString 8 => f) 2 false
          ctrOneQueryAdversary)
        (ctrCpaGame ctrModCounter (fun f : BitString 8 → BitString 8 => f) 2 true
          ctrOneQueryAdversary) : ℝ) ≤ 1 / 32 :=
  (advantage_ctrCpaGame_ctrModCounter_randomFunction_le (by decide)
    isCostBounded_ctrOneQueryAdversary).trans_eq (by norm_num)

/-- Modular CTR mode with the keyed function `xorKeyed` (`ℓ = 2`, `K = 2`): the left-or-right
advantage is at most the two PRF advantages plus `1 / 32`. -/
example :
    (Game.advantage
        (ctrCpaGame ctrModCounter xorKeyed 2 false ctrOneQueryAdversary)
        (ctrCpaGame ctrModCounter xorKeyed 2 true ctrOneQueryAdversary) : ℝ) ≤
      PRF.advantage xorKeyed (ctrReduction ctrModCounter 2 false ctrOneQueryAdversary) +
        PRF.advantage xorKeyed (ctrReduction ctrModCounter 2 true ctrOneQueryAdversary) +
        1 / 32 :=
  (advantage_ctrCpaGame_ctrModCounter_le xorKeyed (by decide)
    isCostBounded_ctrOneQueryAdversary).trans_eq (by norm_num)

end CslibFrontierTests.Crypto.CTRMode
