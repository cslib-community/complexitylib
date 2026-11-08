/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Crypto.Computational.TargetCollisionResistant

/-!
# Tests for target collision resistance and `uowhfTreeHash`

Provides concrete nonvacuous instances of `KeyedCompressionFamily` and `KeyedHashFamily`, tests
level-keyed binary-tree hashing and `exists_uowhfCandidateInput_collision` on both distinct-length
and equal-length colliding message pairs, checks plain `ComputableInPolyTime` and `IsPPTOn`
certificates, and verifies that `TargetCollisionResistantOn` rejects insecure families via explicit
two-stage PPT adversaries.
-/

namespace CslibFrontierTests.Crypto.TargetCollisionResistant

open Cslib Cslib.Crypto Cslib.Probability Turing.MultiTapeTM
open scoped NNReal

/-- Concrete keyed `2(n + 1) → (n + 1)` compression function with `n`-bit keys
(`keyLen ≠ blockLen`): XOR the two `(n + 1)`-bit halves of `x` with `padOrTake (n + 1) k`. -/
def xorKeyedEval (n : ℕ) (k x : List Bool) : List Bool :=
  let M := n + 1
  let halvesXor := (padOrTake M (x.take M)).zipWith Bool.xor (padOrTake M (x.drop M))
  halvesXor.zipWith Bool.xor (padOrTake M k)

theorem length_xorKeyedEval (n : ℕ) (k x : List Bool) :
    (xorKeyedEval n k x).length = n + 1 := by
  simp [xorKeyedEval]

theorem computableInPolyTime_xorKeyedEval :
    ComputableInPolyTime (fun ⟨n, k, x⟩ => xorKeyedEval n k x)
      (encPair encUnary (encPair encBits encBits)) encBits := by
  unfold xorKeyedEval padOrTake
  polytime

/-- Concrete nonvacuous `KeyedCompressionFamily` (`keyLen n = n`, `blockLen n = n + 1`). -/
def xorKeyedCompression : KeyedCompressionFamily where
  keyLen := id
  blockLen := fun n => n + 1
  eval := xorKeyedEval
  keyLen_polyTime := ComputableInPolyTime.id'
  blockLen_polyTime := by polytime
  polyTime := computableInPolyTime_xorKeyedEval
  le_blockLen := fun n => Nat.le_succ n
  length_eq := fun n k x _ _ => length_xorKeyedEval n k x

/-- Concrete nonvacuous `KeyedHashFamily` obtained via `KeyedCompressionFamily.treeHash`. -/
def xorTreeHashFamily : KeyedHashFamily :=
  xorKeyedCompression.treeHash

example (n : ℕ) (K msg : List Bool) (hK : K.length = (n + 1) * n) :
    (xorTreeHashFamily.eval n K msg).length = n + 1 :=
  xorTreeHashFamily.length_eq n K msg hK

-- Leaf encoding examples at block width M = 3:
example : uowhfLeaves 3 [] = [[false, false, false]] := rfl

example : uowhfLeaves 3 [true, false] = [[true, false, false], [false, false, false]] := rfl

-- Equal-length tree collision at n = 2 (`M = 3`, `κ = 2`, `K = replicate 6 false`):
-- `m₀ = [false, false]` and `m₁ = [true, true]` collide already at level `i = 0`, pair `j = 0`.
example :
    uowhfTreeHash xorKeyedEval id (fun m => m + 1) 2 (List.replicate 6 false) [false, false] =
      [false, true, false] := rfl

example :
    uowhfTreeHash xorKeyedEval id (fun m => m + 1) 2 (List.replicate 6 false) [true, true] =
      [false, true, false] := rfl

example :
    ∃ i ≤ 2, ∃ j < 2,
      let x₀ := uowhfCandidateInput xorKeyedEval 2 2 3 i j (List.replicate 6 false) [false, false]
      let x₁ := uowhfCandidateInput xorKeyedEval 2 2 3 i j (List.replicate 6 false) [true, true]
      x₀ ≠ x₁ ∧
        xorKeyedEval 2 (BitString.listRow 2 i (List.replicate 6 false)) x₀ =
          xorKeyedEval 2 (BitString.listRow 2 i (List.replicate 6 false)) x₁ :=
  exists_uowhfCandidateInput_collision (h := xorKeyedEval) (keyLen := id)
    (blockLen := fun m => m + 1) (n := 2) (B := 2)
    (K := List.replicate 6 false) (m₀ := [false, false]) (m₁ := [true, true])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun k x _ _ => length_xorKeyedEval 2 k x) (by decide) rfl

-- Distinct-length tree collision at n = 2 (`M = 3`, `κ = 2`, `K = replicate 6 false`):
-- `m₀ = []` (root `[false, false, false]`, lowBits `[false, false, false]`) and
-- `m₁ = [true]` (root `[true, false, false]`, lowBits `[true, false, false]`) collide at the
-- final length-block compression `i = 2`.
example :
    uowhfTreeHash xorKeyedEval id (fun m => m + 1) 2 (List.replicate 6 false) [] =
      [false, false, false] := rfl

example :
    uowhfTreeHash xorKeyedEval id (fun m => m + 1) 2 (List.replicate 6 false) [true] =
      [false, false, false] := rfl

example :
    ∃ i ≤ 2, ∃ j < 1,
      let x₀ := uowhfCandidateInput xorKeyedEval 2 2 3 i j (List.replicate 6 false) []
      let x₁ := uowhfCandidateInput xorKeyedEval 2 2 3 i j (List.replicate 6 false) [true]
      x₀ ≠ x₁ ∧
        xorKeyedEval 2 (BitString.listRow 2 i (List.replicate 6 false)) x₀ =
          xorKeyedEval 2 (BitString.listRow 2 i (List.replicate 6 false)) x₁ :=
  exists_uowhfCandidateInput_collision (h := xorKeyedEval) (keyLen := id)
    (blockLen := fun m => m + 1) (n := 2) (B := 1)
    (K := List.replicate 6 false) (m₀ := []) (m₁ := [true])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun k x _ _ => length_xorKeyedEval 2 k x) (by decide) rfl

/-- Explicit two-stage PPT adversary breaking `xorKeyedCompression` with probability `1` at every
security parameter `n` by choosing `0^{2(n+1)}` before seeing the key and returning `1^{2(n+1)}`. -/
def xorBreakAdversary : TargetCollisionFinder where
  choose n := pure (List.replicate (2 * (n + 1)) false, [])
  find n _ _ := pure (List.replicate (2 * (n + 1)) true)

theorem isPPT_xorBreakAdversary : xorBreakAdversary.IsPPT where
  choose := by
    dsimp only [xorBreakAdversary]
    ppt
  find := by
    dsimp only [xorBreakAdversary]
    ppt

-- Plain `IsPPTOn` certificate for `targetCollisionGame` and `uowhfTreeAdversary`:
example :
    IsPPTOn encUnary encBool
      (targetCollisionGame xorKeyedCompression.keyLen xorKeyedCompression.eval
        xorKeyedCompression.validInput xorBreakAdversary) :=
  isPPTOn_targetCollisionGame xorKeyedCompression.keyLen_polyTime xorKeyedCompression.polyTime
    xorKeyedCompression.computableInPolyTime_validInput isPPT_xorBreakAdversary

example :
    (uowhfTreeAdversary xorKeyedCompression.eval xorKeyedCompression.keyLen
      xorKeyedCompression.blockLen (fun n => n + 1) xorBreakAdversary).IsPPT :=
  isPPT_uowhfTreeAdversary xorKeyedCompression.polyTime xorKeyedCompression.keyLen_polyTime
    xorKeyedCompression.blockLen_polyTime (by polytime) isPPT_xorBreakAdversary

private theorem zipWith_xor_self (bs : List Bool) :
    bs.zipWith Bool.xor bs = List.replicate bs.length false := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.zipWith_cons_cons, Bool.xor_self, ih, List.length_cons, List.replicate_succ]

/-- `xorKeyedCompression` is not target collision-resistant: `xorBreakAdversary` succeeds with
probability `1` at every security parameter `n`. -/
theorem not_targetCollisionResistant_xorKeyedCompression :
    ¬ xorKeyedCompression.TargetCollisionResistant := by
  refine not_targetCollisionResistantOn_of_le_succProbability one_ne_zero
    xorBreakAdversary isPPT_xorBreakAdversary fun n => ?_
  have hm_ne :
      (List.replicate (2 * (n + 1)) false != List.replicate (2 * (n + 1)) true) = true := by
    rw [bne_iff_ne]
    intro heq
    have h2 : 2 * (n + 1) = (2 * n + 1) + 1 := by omega
    rw [h2, List.replicate_succ, List.replicate_succ] at heq
    injection heq with head_eq
    exact Bool.noConfusion head_eq
  have heval_eq : ∀ k : List Bool,
      xorKeyedEval n k (List.replicate (2 * (n + 1)) false) =
        xorKeyedEval n k (List.replicate (2 * (n + 1)) true) := by
    intro k
    have htake_f : (List.replicate (2 * (n + 1)) false).take (n + 1) =
        List.replicate (n + 1) false := by
      rw [List.take_replicate, Nat.min_eq_left (by omega)]
    have hdrop_f : (List.replicate (2 * (n + 1)) false).drop (n + 1) =
        List.replicate (n + 1) false := by
      rw [List.drop_replicate]
      congr 1
      omega
    have htake_t : (List.replicate (2 * (n + 1)) true).take (n + 1) =
        List.replicate (n + 1) true := by
      rw [List.take_replicate, Nat.min_eq_left (by omega)]
    have hdrop_t : (List.replicate (2 * (n + 1)) true).drop (n + 1) =
        List.replicate (n + 1) true := by
      rw [List.drop_replicate]
      congr 1
      omega
    simp only [xorKeyedEval, htake_f, hdrop_f, htake_t, hdrop_t,
      padOrTake_eq_self List.length_replicate, zipWith_xor_self, List.length_replicate]
  have heval :
      ProbComp.eval
        (targetCollisionGame xorKeyedCompression.keyLen xorKeyedCompression.eval
          xorKeyedCompression.validInput xorBreakAdversary n) = PMF.pure true := by
    simp only [targetCollisionGame, xorBreakAdversary, xorKeyedCompression,
      KeyedCompressionFamily.validInput, isCollision, List.length_replicate, beq_self_eq_true,
      hm_ne, heval_eq, Bool.and_self, pure_bind, ProbComp.eval_bind,
      BitString.eval_sampleList, ProbComp.eval_pure, PMF.bind_const]
  rw [Game.succProbability, heval, PMF.pure_apply_self, ENNReal.toNNReal_one]

-- Finite-parameter boundary check: at `n = 1` (`2^1 = 2`-bit tree capacity), 3-bit messages
-- sharing their first pair and length collide regardless of `h`, `keyLen`, `blockLen`, and `K`
-- because `top.headD []` discards the second root.
example (h : ℕ → List Bool → List Bool → List Bool) (keyLen blockLen : ℕ → ℕ) (K : List Bool) :
    uowhfTreeHash h keyLen blockLen 1 K [false, false, false] =
      uowhfTreeHash h keyLen blockLen 1 K [false, false, true] := by
  simp [uowhfTreeHash, uowhfTreeLevels, uowhfTreeStep, uowhfLeaves, uowhfPairInput,
    BitString.listRows, List.range_succ]

-- Bridges from `CompressionFamily` / `HashFamily` and `treeHash` security endpoint type-check:
example {h : List Bool → List Bool → List Bool} (hh : CompressionFamily h) :
    hh.toKeyedCompressionFamily.treeHash.TargetCollisionResistant :=
  KeyedCompressionFamily.targetCollisionResistant_treeHash
    hh.targetCollisionResistant_toKeyedCompressionFamily

end CslibFrontierTests.Crypto.TargetCollisionResistant
