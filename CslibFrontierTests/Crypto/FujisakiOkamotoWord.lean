/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import CslibFrontier.Crypto.Protocols.KEM.FujisakiOkamoto.Word
public import CslibFrontier.Crypto.Protocols.KEM.FujisakiOkamoto.WordGame
import CslibFrontier.Languages.Probabilistic.Oracle.Norm
import CslibFrontier.Languages.Probabilistic.Norm
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option

/-!
# Tests for the word-level Fujisaki–Okamoto family

`identityPKE` encrypts a message as itself and ignores its coins. It is a concrete
`WordPKE` with an `IsEfficient` proof, so the native certificates of `FO-notbot` and `FO^⊥`
apply to it. Its native decapsulations are run against fixed oracles `G` and `H`:

* an honest ciphertext of a message of the right length decapsulates to `H(false, m, c)`;
* a ciphertext whose decryption has the wrong length is a decryption failure, so `FO-notbot`
  returns the fallback key `H(true, s, c)` and `FO^⊥` returns `none`;
* a word longer than the ciphertext bound is rejected with `none` by both.

The native keyless simulator of the IND-CPA reduction caches an in-domain `G` request, rejects a
`G` request of the wrong length and the challenge ciphertext, and answers another decapsulation
request from its ciphertext table. The reduction of an adversary that queries `G` on its
challenge word is uniform strict PPT. In the word ROM IND-CCA game, decapsulation of the challenge
ciphertext and a `G` request of the wrong length get the empty word and leave the random oracles
unchanged, and an in-domain `G` request is answered and cached.
-/

public section

namespace CslibFrontierTests.Crypto.FujisakiOkamotoWord

open Cslib Cslib.Crypto.Protocols Cslib.Crypto.Protocols.FujisakiOkamoto
open Cslib.Probability Turing.MultiTapeTM

/-- The identity scheme: messages, coins and ciphertexts at parameter `n` have length `n`, `0`
and at most `n`; encryption returns the message and decryption returns the ciphertext. -/
def identityPKE : WordPKE where
  msgLen n := n
  coinLen _ := 0
  ctLen n := n
  keyGen _ := pure ([], [])
  encDet _ _ m _ := m
  dec _ _ c := some c

/-- The identity scheme is an efficient word-level PKE family. -/
theorem identityPKE_isEfficient : identityPKE.IsEfficient where
  msgLen := by simp only [identityPKE]; fun_prop
  coinLen := by simp only [identityPKE]; fun_prop
  ctLen := by simp only [identityPKE]; fun_prop
  keyGen := (ComputableInPolyTime.const (([], []) : List Bool × List Bool)).isPPTOn
  encDet := by simp only [identityPKE]; fun_prop
  dec := by simp only [identityPKE]; fun_prop

/-- With keys of length `n`, native `FO-notbot` decapsulation of the identity scheme is uniform
strict oracle PPT. -/
example : IsOraclePPTOn encDecapsNotBotInput (encOption encBits)
    (fun (n, dk, c) => identityPKE.decapsNotBot (fun n => n) n dk c) :=
  identityPKE_isEfficient.isOraclePPTOn_decapsNotBot
    (by fun_prop : ComputableInPolyTime (fun n : ℕ => n) encUnary encUnary)

/-- Fixed oracles: `G` answers the empty word and `H` answers its request word. -/
noncomputable def fixedOracle (q : RO × List Bool) : StateT Unit PMF (List Bool) :=
  fun s => PMF.pure ((match q.1 with
    | .G => []
    | .H => q.2), s)

/-- The secret key with fallback seed `[true]`. -/
def dk : ImplicitSK (List Bool) (List Bool) (List Bool) := ⟨[], [], [true]⟩

/-- An honest ciphertext `c = m = [false]` at parameter `1` decapsulates to `H(false, m, c)`,
read to `keyLen 1 = 20` bits. -/
example : ProbOracleComp.runWith fixedOracle
      (identityPKE.decapsNotBot (fun _ => 20) 1 dk [false]) () =
    PMF.pure (some ((encHQuery (false, [false], [false])).take 20), ()) := by
  simp [WordPKE.decapsNotBot, identityPKE, WordPKE.scheme, WordPKE.toExplicitCoin,
    Scheme.decapsNotBotM_eq, Option.filter_some, WordPKE.queryG, queryH, fixedOracle, dk,
    runWith_norm, pmf_norm]

/-- At parameter `2`, the ciphertext `[false]` decrypts to a word of the wrong length, so
`FO-notbot` returns the fallback key `H(true, s, c)`. -/
example : ProbOracleComp.runWith fixedOracle
      (identityPKE.decapsNotBot (fun _ => 20) 2 dk [false]) () =
    PMF.pure (some ((encHQuery (true, [true], [false])).take 20), ()) := by
  simp [WordPKE.decapsNotBot, identityPKE, WordPKE.scheme, WordPKE.toExplicitCoin,
    Scheme.decapsNotBotM_eq, Option.filter_some, queryH, fixedOracle, dk, runWith_norm, pmf_norm]

/-- At parameter `2`, `FO^⊥` rejects the same ciphertext with `none`. -/
example : ProbOracleComp.runWith fixedOracle
      (identityPKE.decapsBot (fun _ => 20) 2 [] [] [false]) () = PMF.pure (none, ()) := by
  simp [WordPKE.decapsBot, identityPKE, WordPKE.scheme, WordPKE.toExplicitCoin,
    Scheme.decapsBotM_eq, Option.filter_some, runWith_norm, pmf_norm]

/-- A word longer than the ciphertext bound is rejected by both decapsulations, without any
oracle call. -/
example : identityPKE.decapsNotBot (fun _ => 20) 1 dk [false, false] = pure none ∧
    identityPKE.decapsBot (fun _ => 20) 1 [] [] [false, false] = pure none := by
  simp [WordPKE.decapsNotBot, WordPKE.decapsBot, identityPKE]

/-! ### The native simulator and the reduction -/

theorem stateT_pure_apply {σ α : Type} (a : α) (s : σ) :
    (pure a : StateT σ ProbComp α) s = pure (a, s) := rfl

theorem stateT_bind_apply {σ α β : Type} (x : StateT σ ProbComp α)
    (f : α → StateT σ ProbComp β) (s : σ) : (x >>= f) s = x s >>= fun p => f p.1 p.2 :=
  StateT.run_bind x f s

/-- An in-domain `G` request is cached: at parameter `1` with empty coins, `G([true])` answers the
empty coin word and records it. -/
example : ProbComp.eval (identityPKE.simFilterWordHandler (fun _ => 0) (fun _ _ _ => true) 1 []
      [false] (.G, [true]) {}) =
    PMF.pure ([], { gCache := [([true], [])] }) := by
  simp [WordPKE.simFilterWordHandler, identityPKE, Scheme.simFilterHandler,
    Scheme.simFilterDispatch, simHashG, RandomOracle.zoomStateT, memoize, WordPKE.scheme,
    WordPKE.toExplicitCoin, BitString.sampleList, pmf_norm]

/-- A `G` request of the wrong length gets the empty reply and leaves the state unchanged. -/
example : ProbComp.eval (identityPKE.simFilterWordHandler (fun _ => 0) (fun _ _ _ => true) 1 []
      [false] (.G, [true, false]) {}) = PMF.pure ([], {}) := by
  simp [WordPKE.simFilterWordHandler, identityPKE]

/-- Decapsulation of the challenge ciphertext is refused with the empty reply. -/
example : ProbComp.eval (identityPKE.simFilterWordHandler (fun _ => 0) (fun _ _ _ => true) 1 []
      [false] (.decaps, [false]) {}) = PMF.pure ([], {}) := by
  simp [WordPKE.simFilterWordHandler, identityPKE, Scheme.simFilterHandler,
    Scheme.simFilterDispatch, stateT_pure_apply, pmf_norm]

/-- Any other ciphertext within the bound is answered from the ciphertext table `H_q`: with empty
keys the reply is `encOption encBits (some []) = [true]`, and `([true], [])` is recorded. -/
example : ProbComp.eval (identityPKE.simFilterWordHandler (fun _ => 0) (fun _ _ _ => true) 1 []
      [false] (.decaps, [true]) {}) =
    PMF.pure ([true], { hqCache := [([true], [])] }) := by
  simp [WordPKE.simFilterWordHandler, identityPKE, Scheme.simFilterHandler,
    Scheme.simFilterDispatch, filterDecaps, simHashHq, RandomOracle.zoomStateT, memoize,
    WordPKE.scheme, BitString.sampleList, stateT_pure_apply, stateT_bind_apply, pmf_norm]

/-- An adversary that queries `G` on its challenge word and reports whether the reply is empty. -/
def queryChallengeG (_ : ℕ) (challenge : List Bool) : WordOracleComp CCAOp Bool :=
  (fun r : List Bool => r.isEmpty) <$> (List.take 1 <$>
    ProbOracleComp.query (spec := fun _ : CCAOp × List Bool => List Bool) (CCAOp.G, challenge))

/-- The adversary is uniform strict oracle PPT. -/
theorem isOraclePPT_queryChallengeG : IsOraclePPT encBool queryChallengeG :=
  ((IsOraclePPTOn.query_take' CCAOp.G (ComputableInPolyTime.snd encUnary encBits)
    (ComputableInPolyTime.const 1)).map' (by fun_prop)).isOraclePPT

/-- Its IND-CPA reduction against the identity scheme is uniform strict PPT. -/
example : (identityPKE.romCpaReductionWord (fun n => n) queryChallengeG).IsPPT encBits :=
  identityPKE_isEfficient.isPPT_romCpaReductionWord
    (by fun_prop : ComputableInPolyTime (fun n : ℕ => n) encUnary encUnary)
    isOraclePPT_queryChallengeG

/-! ### The word ROM IND-CCA game -/

/-- The game's decapsulation oracle refuses the challenge ciphertext with the empty word. -/
example : ProbComp.eval (identityPKE.ccaWordOracle (fun _ => 0) 1 dk [false] (.decaps, [false])
      {}) = PMF.pure ([], {}) := by
  simp [WordPKE.ccaWordOracle, stateT_pure_apply]

/-- A `G` request of the wrong length gets the empty word and leaves the caches unchanged. -/
example : ProbComp.eval (identityPKE.ccaWordOracle (fun _ => 0) 1 dk [false] (.G, [true, true])
      {}) = PMF.pure ([], {}) := by
  simp [WordPKE.ccaWordOracle, WordPKE.roWordOracle, identityPKE]

/-- An in-domain `G` request is answered with a coin of length `coinLen 1 = 0` and cached. -/
example : ProbComp.eval (identityPKE.ccaWordOracle (fun _ => 0) 1 dk [false] (.G, [true])
      {}) = PMF.pure ([], { gCache := [([true], [])] }) := by
  simp [WordPKE.ccaWordOracle, WordPKE.roWordOracle, identityPKE, roHashG,
    RandomOracle.zoomStateT, memoize, BitString.sampleList, pmf_norm]

end CslibFrontierTests.Crypto.FujisakiOkamotoWord
