/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Crypto.Computational.TreeSignature.CoinHybrid
import CslibFrontier.Tactic.PolyTime
import CslibFrontier.Tactic.PPT

/-!
# Tests for the tree-signature PRF coin hybrid

Behavioral checks for `CslibFrontier.Crypto.Computational.TreeSignature.CoinHybrid`:

1. `coinParam` and `coinParamInv` on a non-monotone budget (`oscBudget 0 = 5`, `oscBudget 1 = 2`),
   verifying exact parameter recovery even when `coinParam oscBudget 1 < coinParam oscBudget 0`,
   and rejection (`pure false`) by `treeCoinAdversary` at parameters outside `Set.range N`.
2. A coin-consuming toy indexed scheme `seededToy` (`keyGenBudget _ = 2`, `signBudget _ _ _ = 1`)
   whose keys equal their 2-bit seed (`pk = sk`):
   - `cheatForger` recovers `rootPk = rootSk` at depth `1` and forges on `0^n` with zero queries,
     achieving exact success probability `1` in `coinRealGame` at every parameter `n`, while
     scoring `0` in `coinIdealGame` at out-of-range PRF parameter `M = 5`.
   - `replayForger` queries `0^n` and replays the returned signature on `0^n`, achieving exact
     success probability `0` because `!queried.contains msg` rejects queried messages.
   - `exists_negligible_treeGame_coinParam_le` instantiates end-to-end on `seededToy`.
-/

namespace CslibFrontierTests.Crypto.TreeCoinHybrid

open Cslib Cslib.Crypto Cslib.Crypto.TreeSignature Cslib.Probability Turing.MultiTapeTM

/-! ### Non-monotone coin-budget parameter schedule -/

/-- A non-monotone budget (`oscBudget 0 = 5 > oscBudget 1 = 2`) exercising `coinParam` without
monotonicity. -/
def oscBudget : ℕ → ℕ
  | 0 => 5
  | 1 => 2
  | n + 2 => n

theorem computableInPolyTime_oscBudget : ComputableInPolyTime oscBudget encUnary encUnary := by
  have heq : oscBudget = fun n => if n == 0 then 5 else if n == 1 then 2 else n - 2 := by
    funext n
    rcases n with _ | _ | n <;> rfl
  rw [heq]
  polytime

-- Even though `coinParam oscBudget 1 < coinParam oscBudget 0`, `coinParamInv` recovers both.
example : coinParam oscBudget 0 = 36 := by decide
example : coinParam oscBudget 1 = 10 := by decide
example : coinParamInv oscBudget 36 = 0 := by decide
example : coinParamInv oscBudget 10 = 1 := by decide
example : oscBudget 0 < coinParam oscBudget 0 ∧ oscBudget 1 < coinParam oscBudget 1 := by decide
-- `M = 5` is outside `Set.range (coinParam oscBudget)`:
-- `coinParam oscBudget (coinParamInv _ 5) ≠ 5`.
example : coinParam oscBudget (coinParamInv oscBudget 5) ≠ 5 := by decide

/-! ### A coin-consuming toy indexed signature scheme -/

private def padCoins (k : ℕ) (coins : List Bool) : List Bool :=
  (coins ++ List.replicate k false).take k

private theorem length_padCoins (k : ℕ) (coins : List Bool) : (padCoins k coins).length = k := by
  simp only [padCoins, List.length_take, List.length_append, List.length_replicate]
  omega

private theorem map_uniformList_padCoins {k length : ℕ} (h : k ≤ length) :
    (BitString.uniformList length).map (padCoins k) = BitString.uniformList k := by
  have hcongr : (BitString.uniformList length).map (padCoins k) =
      (BitString.uniformList length).map (List.take k) := by
    simp only [PMF.map]
    refine PMF.bind_congr_on_support _ _ _ fun coins hcoins => ?_
    have hlen := BitString.length_of_mem_support_uniformList hcoins
    simp only [Function.comp_apply, padCoins, List.take_append_of_le_length (hlen ▸ h)]
  rw [hcongr, BitString.uniformList_take h]

private def sigEnc :=
  encPair encBits (encPair encUnary (encPair encBits encBits))

private def sigDec : Decoder sigEnc :=
  Decoder.bits.pair (Decoder.unary.pair (Decoder.bits.pair Decoder.bits))

/-- A toy indexed scheme whose keys consume 2 coin bits (`pk = sk`) and whose signatures consume
1 coin bit. -/
noncomputable def seededToy : IndexedSignatureScheme where
  capacity _ := 2
  keyGen _ := do
    let c ← BitString.sampleList 2
    return (c, c)
  sign sk u msg := do
    let r ← BitString.sampleList 1
    return sigEnc (sk, u, msg, r)
  verify pk u msg sig :=
    let decoded := sigDec.decode sig
    (decoded.1 == pk) && (decoded.2.1 == u) && (decoded.2.2.1 == msg)
  capacity_polyTime := ComputableInPolyTime.const 2
  keyGen_ppt := by ppt
  sign_ppt := by
    unfold sigEnc
    ppt
  verify_polyTime := by
    have hdec := sigDec.computableInPolyTime
    polytime
  verify_sign _ keys hkeys _ _ msg sig hsig := by
    simp only [ProbComp.eval_bind, ProbComp.eval_pure, BitString.eval_sampleList,
      PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hkeys hsig
    obtain ⟨c, _, rfl⟩ := hkeys
    obtain ⟨r, _, rfl⟩ := hsig
    simp [sigDec.decode_enc]

/-- Concrete seeded algorithms of `seededToy` consuming 2 key bits and 1 signing bit. -/
noncomputable def seededToySeeded : seededToy.Seeded where
  keyGenWith _ coins := (padCoins 2 coins, padCoins 2 coins)
  keyGenBudget _ := 2
  signWith sk u msg coins := sigEnc (sk, u, msg, padCoins 1 coins)
  signBudget _ _ _ := 1
  keyGenWith_polyTime := by
    unfold padCoins
    polytime
  keyGenBudget_polyTime := ComputableInPolyTime.const 2
  keyGenWith_mem_support _ coins := by
    simp only [seededToy, ProbComp.eval_bind, ProbComp.eval_pure, BitString.eval_sampleList,
      PMF.mem_support_bind_iff, PMF.mem_support_pure_iff]
    exact ⟨padCoins 2 coins, BitString.mem_support_uniformList_iff.mpr (length_padCoins 2 coins),
      rfl⟩
  eval_keyGen _ length h := by
    simp only [seededToy, ProbComp.eval_bind, ProbComp.eval_pure, BitString.eval_sampleList]
    rw [← map_uniformList_padCoins h, PMF.bind_map]
    rfl
  signWith_polyTime := by
    unfold sigEnc padCoins
    polytime
  signBudget_polyTime := ComputableInPolyTime.const 1
  signWith_mem_support sk u msg coins := by
    simp only [seededToy, ProbComp.eval_bind, ProbComp.eval_pure, BitString.eval_sampleList,
      PMF.mem_support_bind_iff, PMF.mem_support_pure_iff]
    exact ⟨padCoins 1 coins, BitString.mem_support_uniformList_iff.mpr (length_padCoins 1 coins),
      rfl⟩
  eval_sign sk u msg length h := by
    simp only [seededToy, ProbComp.eval_bind, ProbComp.eval_pure, BitString.eval_sampleList]
    rw [← map_uniformList_padCoins h, PMF.bind_map]
    rfl

/-! ### Concrete coin-dependent node keys and deterministic oracle simulation -/

def maskFamily (key query : List Bool) : List Bool := List.zipWith xor key query

-- Derived root keys under distinct PRF secrets differ because `seededToy` consumes the coin bits.
example :
    nodeKey seededToy seededToySeeded (prfCoins maskFamily) 2 [false, false, false, false] [] ≠
      nodeKey seededToy seededToySeeded (prfCoins maskFamily) 2 [true, true, false, false] [] := by
  decide +kernel

/-! ### Zero-query forger (probability 1) vs. out-of-range parameter (probability 0) -/

/-- Because `seededToy` publishes `pk = sk`, at depth `1` a zero-query forger extracts `rootPk`
and signs `0^n` at leaf `[false]` directly. -/
def cheatForger : Forger := fun n pk =>
  let rootPk := (keyDecoder.decode pk).2
  let msg := List.replicate n false
  pure (msg, encodeSignature [false] [] (sigEnc (rootPk, 0, msg, [false])))

theorem isOraclePPT_cheatForger : IsOraclePPT (encPair encBits encBits) cheatForger := by
  have hdec := keyDecoder.computableInPolyTime
  refine IsOraclePPTOn.isOraclePPT ?_
  unfold cheatForger encodeSignature sigEnc
  exact ComputableInPolyTime.isOraclePPTOn (by polytime)

-- At `M = 5` (outside `Set.range (coinParam oscBudget)`), `treeCoinAdversary` outputs `false`
-- with success probability `0`.
example : Game.succProbability (ProbComp.eval
    (coinIdealGame (treeCoinAdversary seededToy seededToySeeded (fun _ => 1)
      (coinParam oscBudget) (coinParamInv oscBudget) cheatForger) 5)) = 0 := by
  have h5 : coinParam oscBudget (coinParamInv oscBudget 5) ≠ 5 := by decide
  simp [coinIdealGame, ProbOracleComp.run, treeCoinAdversary, h5, Game.succProbability]

-- At every `N n = coinParam oscBudget n`, `cheatForger` wins `coinRealGame` with exact
-- probability `1`.
example (n : ℕ) : Game.succProbability (ProbComp.eval
    (coinRealGame maskFamily (treeCoinAdversary seededToy seededToySeeded (fun _ => 1)
      (coinParam oscBudget) (coinParamInv oscBudget) cheatForger)
      (coinParam oscBudget n))) = 1 := by
  rw [eval_coinRealGame_treeCoinAdversary maskFamily (coinParamInv_coinParam oscBudget)]
  have heval : ProbComp.eval (treeGame seededToy seededToySeeded (fun _ => 1) (coinParam oscBudget)
      (prfCoins maskFamily) cheatForger n) = PMF.pure true := by
    rw [eval_treeGame]
    refine (congrArg (PMF.bind _) (funext fun k => ?_)).trans (PMF.bind_const _ _)
    rw [treeGameWith, treeScheme, Forger.eval_eufCmaExperiment_restrict_toTyped]
    simp only [cheatForger, OracleComp.interpret_pure, StateT.run_pure,
      ProbComp.eval_bind, ProbComp.eval_pure, PMF.pure_bind, verify, encodeSignature,
      keyDecoder.decode_enc, signatureDecoder.decode_enc]
    simp [seededToy, sigDec.decode_enc]
  simp [heval, Game.succProbability]

/-! ### Replay rejection and end-to-end hybrid instantiation -/

/-- A 1-query forger that queries `0^n` and replays the returned signature prefix on `0^n`. -/
def replayForger : Forger := fun n _ => do
  let msg := List.replicate n false
  let sig ← List.take (2 * n + 20) <$> ProbOracleComp.query ((), msg)
  return (msg, sig)

theorem isOraclePPT_replayForger : IsOraclePPT (encPair encBits encBits) replayForger := by
  refine IsOraclePPTOn.isOraclePPT ?_
  unfold replayForger
  have hq := IsOraclePPTOn.query_take' (input := encPair encUnary encBits) ()
    (request := fun p : ℕ × List Bool => List.replicate p.1 false)
    (limit := fun p => 2 * p.1 + 20) (by polytime) (by polytime)
  exact hq.bind_with
    (second := fun (p : ℕ × List Bool) (sig : List Bool) =>
      (pure (List.replicate p.1 false, sig) : WordOracleComp Unit (List Bool × List Bool)))
    ((ComputableInPolyTime.isOraclePPTOn (by polytime)))

-- Replaying the queried message `0^n` is rejected (`!queried.contains msg = false`), so the
-- success probability in `treeIdealGame` is `0`.
example (n : ℕ) : Game.succProbability (ProbComp.eval
    (treeIdealGame seededToy seededToySeeded (fun _ => 1) (coinParam oscBudget)
      replayForger n)) = 0 := by
  have hzero : (ProbComp.eval (treeIdealGame seededToy seededToySeeded (fun _ => 1)
      (coinParam oscBudget) replayForger n)) true = 0 := by
    rw [PMF.apply_eq_zero_iff]
    intro hb
    simp only [treeIdealGame, ProbComp.eval_bind, treeGameWith, treeScheme,
      Forger.eval_eufCmaExperiment_restrict_toTyped] at hb
    simp only [replayForger, OracleComp.interpret_bind,
      OracleComp.interpret_map, OracleComp.interpret_pure, ProbOracleComp.interpret_query,
      StateT.run_bind, StateT.run_map, StateT.run_pure] at hb
    simp only [StateT.run, ProbComp.eval_bind, ProbComp.eval_map, ProbComp.eval_pure,
      PMF.mem_support_bind_iff, PMF.mem_support_map_iff, PMF.mem_support_pure_iff] at hb
    obtain ⟨_, -, _, ⟨_, ⟨_, ⟨_, -, rfl⟩, rfl⟩, rfl⟩, htrue⟩ := hb
    simp at htrue
  simp [Game.succProbability, hzero]

-- End-to-end instantiation of the parameter-shifted PRF coin hybrid on `seededToy`.
example {F : List Bool → List Bool → List Bool} (hF : PseudorandomFunction F) :
    ∃ ε, Negligible ε ∧ ∀ n,
      Game.succProbability (ProbComp.eval
        (treeGame seededToy seededToySeeded (· + 1) (coinParam oscBudget) (prfCoins F)
          cheatForger n)) ≤
        Game.succProbability (ProbComp.eval
          (treeIdealGame seededToy seededToySeeded (· + 1) (coinParam oscBudget)
            cheatForger n)) + ε n :=
  exists_negligible_treeGame_coinParam_le seededToy seededToySeeded (· + 1) hF (by polytime)
    computableInPolyTime_oscBudget isOraclePPT_cheatForger

end CslibFrontierTests.Crypto.TreeCoinHybrid
