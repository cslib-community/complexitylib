/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.TreeSignature
public import CslibFrontier.Crypto.Computational.PseudorandomFunction.Coins
public import CslibFrontier.Languages.Probabilistic.Iteration
public import Mathlib.Data.Nat.Pairing
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Eq
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Search
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Probabilistic.Oracle.Composition
import CslibFrontier.Computability.Probabilistic.Oracle.Substitution
import CslibFrontier.Computability.Probabilistic.Sampling
import CslibFrontier.Crypto.Game.Order
import CslibFrontier.Crypto.Negligible.Basic
import CslibFrontier.Languages.Probabilistic.Norm
import CslibFrontier.Languages.Probabilistic.Oracle.Simulation
import CslibFrontier.Languages.Probabilistic.Oracle.Support
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Tactic.SuppCases

/-!
# Tree signatures: from pseudorandom to random coins

The first step of the security proof of stateless tree signatures ([BonehShoup2023],
Section 14.6.3, proof of Theorem 14.6, "we first replace the PRF `F` with a random function").
The tree scheme over an indexed scheme `S` at parameter `n` draws its node coins from a
pseudorandom function `F` keyed at `N n` bits (`prfCoins F`). The EUF-CMA game against it
(`treeGame`, which is `eufCmaGame` of `TreeSignature.scheme` by definition) is compared with the
same game where the coins come from a uniform random function on `N n` bits (`treeIdealGame`).

The coin adversary `treeCoinAdversary` runs the forger inside `coinRealGame` and `coinIdealGame`:
it derives the root key and every node key and signature by
coin requests, so under the real coin oracle it plays `treeGame` and under the ideal one
`treeIdealGame`, exactly (`eval_coinRealGame_treeCoinAdversary`,
`eval_coinIdealGame_treeCoinAdversary`). Its parameter is the PRF's, `N n`, so it recovers `n`
with an inverse `inv` of `N` and plays nothing at parameters outside the range of `N`. Pairing `n`
with any polynomial-time budget (`coinParam`) supplies an injective schedule `N` strictly above the
budget together with a polynomial-time bounded-search left inverse (`coinParamInv`).

## Main definitions

* `Cslib.Crypto.TreeSignature.treeGame`, `Cslib.Crypto.TreeSignature.treeGameWith`,
  `Cslib.Crypto.TreeSignature.tableCoins`, `Cslib.Crypto.TreeSignature.treeIdealGame`: the forging
  games with pseudorandom and random coins.
* `Cslib.Crypto.TreeSignature.coinRequest`, `Cslib.Crypto.TreeSignature.nodeKeyO`,
  `Cslib.Crypto.TreeSignature.signAtO`, `Cslib.Crypto.TreeSignature.certifyO`,
  `Cslib.Crypto.TreeSignature.signO`, `Cslib.Crypto.TreeSignature.simulateTreeGame`,
  `Cslib.Crypto.TreeSignature.treeCoinAdversary`: the tree algorithms with coins from an oracle,
  and the coin adversary.
* `Cslib.Crypto.TreeSignature.coinParam`, `Cslib.Crypto.TreeSignature.coinParamInv`: injective
  polynomial-time PRF parameter schedule strictly above a given budget, and its bounded-search
  left inverse.

## Main results

* `Cslib.Crypto.TreeSignature.eufCmaGame_scheme`: the scheme's game is `treeGame`.
* `Cslib.Crypto.TreeSignature.evalDet_simulateTreeGame`: with deterministic coins (`evalDet`),
  the simulated game is the tree game under any secret (`treeGameWith`), which depends on the
  coins at that secret only (`treeGameWith_congr`).
* `Cslib.Crypto.TreeSignature.eval_coinRealGame_treeCoinAdversary`,
  `Cslib.Crypto.TreeSignature.eval_coinIdealGame_treeCoinAdversary`: the exact simulation.
* `Cslib.Crypto.TreeSignature.succProbability_treeGame_le`,
  `Cslib.Crypto.TreeSignature.succProbability_treeGame_le_prf`: the hybrid bound by the coin-game
  and PRF advantages at `N n`.
* `Cslib.Crypto.TreeSignature.isOraclePPT_treeCoinAdversary`: the coin adversary is strict oracle
  PPT, built from `isOraclePPTOn_certifyO`, `isOraclePPTOn_signO`, `isOraclePPTOn_simulateTreeGame`,
  and the output bounds `keyBound` and `sigBound`.
* `Cslib.Crypto.TreeSignature.exists_negligible_treeGame_le`,
  `Cslib.Crypto.TreeSignature.exists_negligible_treeGame_coinParam_le`: for a pseudorandom function,
  the forging probability with pseudorandom coins exceeds that with random coins by a negligible
  function.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023],
  Section 14.6.3.
-/

public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM
open scoped NNReal

namespace TreeSignature

variable (S : IndexedSignatureScheme) (T : S.Seeded) (depth keyLen : ℕ → ℕ)

/-! ### The forging games -/

/-- The EUF-CMA game of the tree algorithms with a coin function: `SignatureScheme.eufCmaGame`
of `scheme`, stated without certificates so that random coins may be substituted. -/
@[expose] noncomputable def treeGame (coins : List Bool → List Bool → ℕ → List Bool)
    (adversary : Forger) (n : ℕ) : ProbComp Bool := do
  let keys ← keyGen S T coins keyLen n
  let out ← (OracleComp.interpret
    (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifFin k))
      (fun request queried => do
        let sig ← sign S T coins depth keys.2 request.2
        return (sig, request.2 :: queried))) (adversary n keys.1)).run []
  let msig := out.1
  return (msig.1.length == n) && !out.2.contains msig.1 &&
    verify S depth keys.1 msig.1 msig.2

/-- The tree game with a fixed secret `k`. -/
@[expose] noncomputable def treeGameWith (coins : List Bool → List Bool → ℕ → List Bool)
    (k : List Bool) (adversary : Forger) (n : ℕ) : ProbComp Bool := do
  let pk := encPair encUnary encBits (n, (nodeKey S T coins n k []).1)
  let out ← (OracleComp.interpret
    (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifFin k))
      (fun request queried => do
        let sig ← sign S T coins depth (encPair encUnary encBits (n, k)) request.2
        return (sig, request.2 :: queried))) (adversary n pk)).run []
  let msig := out.1
  return (msig.1.length == n) && !out.2.contains msig.1 && verify S depth pk msig.1 msig.2

/-- The tree game samples the secret and plays `treeGameWith`. -/
theorem eval_treeGame (coins : List Bool → List Bool → ℕ → List Bool) (adversary : Forger)
    (n : ℕ) :
    ProbComp.eval (treeGame S T depth keyLen coins adversary n) =
      (BitString.uniformList (keyLen n)).bind fun k =>
        ProbComp.eval (treeGameWith S T depth coins k adversary n) := by
  simp only [pmf_norm, treeGame, treeGameWith, keyGen, BitString.eval_sampleList]

/-- The scheme's EUF-CMA game is `treeGame`. -/
theorem eufCmaGame_scheme {coins : List Bool → List Bool → ℕ → List Bool}
    (hcoins : ComputableInPolyTime
      (fun ((k, input, length) : List Bool × List Bool × ℕ) => coins k input length)
      (encPair encBits (encPair encBits encUnary)) encBits)
    (hkeyLen : ComputableInPolyTime keyLen encUnary encUnary)
    (hdepth : ComputableInPolyTime depth encUnary encUnary)
    (hcap : ∀ n, 2 ≤ S.capacity n) (hdepth_pos : ∀ n, 1 ≤ depth n) (adversary : Forger) (n : ℕ) :
    (scheme S T coins keyLen depth hcoins hkeyLen hdepth hcap hdepth_pos).eufCmaGame adversary n =
      treeGame S T depth keyLen coins adversary n := rfl

/-- Coins read from a random function on `N` bits at the padded request, ignoring the key. -/
@[expose] def tableCoins (N : ℕ) (table : BitString N → BitString N) (_k x : List Bool) (L : ℕ) :
    List Bool :=
  (randomFunctionOracle N table (padRequest N x)).take L

variable (N : ℕ → ℕ)

/-- The tree game with coins from a uniform random function on `N n` bits. -/
@[expose] noncomputable def treeIdealGame (adversary : Forger) (n : ℕ) : ProbComp Bool := do
  let table ← ProbComp.uniform (BitString (N n) → BitString (N n))
  treeGameWith S T depth (tableCoins (N n) table) [] adversary n

/-! ### The tree algorithms with coins from an oracle -/

/-- Request `L` coins for `x` from the coin oracle, keeping at most `L` bits. -/
@[expose] def coinRequest (x : List Bool) (L : ℕ) : WordOracleComp Unit (List Bool) :=
  List.take L <$> ProbOracleComp.query ((), encPair encBits encUnary (x, L))

/-- The key pair of node `path`, from requested coins. -/
@[expose] def nodeKeyO (n : ℕ) (path : List Bool) : WordOracleComp Unit (List Bool × List Bool) :=
  T.keyGenWith n <$> coinRequest (keyInput path) (T.keyGenBudget n)

/-- The signature of `msg` at index `u` by node `path` holding `sk`, from requested coins. -/
@[expose] def signAtO (path sk : List Bool) (u : ℕ) (msg : List Bool) :
    WordOracleComp Unit (List Bool) :=
  T.signWith sk u msg <$> coinRequest (signInput path u) (T.signBudget sk u msg)

/-- One step of the chain along `leaf`: the next bit is the one after the current path. -/
@[expose] def certifyStepO (n : ℕ) (leaf : List Bool) (state : CertState) :
    WordOracleComp Unit CertState := do
  let (node, (_, sk), certs) := state
  let bit := leaf.getD node.length false
  let child ← nodeKeyO S T n (node ++ [bit])
  let σ ← signAtO S T node sk bit.toNat child.1
  return (node ++ [bit], child, certs ++ [(child.1, σ)])

/-- Certify the path to the parent of `leaf`, a leaf of depth `depth n`. -/
@[expose] def certifyO (n : ℕ) (leaf : List Bool) : WordOracleComp Unit CertState := do
  let root ← nodeKeyO S T n []
  OracleComp.iterate (depth n - 1) (certifyStepO S T n leaf) ([], root, [])

/-- Sign `msg`: when `msg` has length `n`, sample a uniform leaf, certify the chain to its parent,
and sign `msg` there; otherwise return `[]`. -/
@[expose] noncomputable def signO (n : ℕ) (msg : List Bool) : WordOracleComp Unit (List Bool) :=
  if msg.length = n then do
    let leaf ← ProbOracleComp.sample (BitString.sampleList (depth n))
    let (node, (_, sk), certs) ← certifyO S T depth n leaf
    let σ ← signAtO S T node sk (leaf.getLastD false).toNat msg
    return encodeSignature leaf certs σ
  else
    pure []

/-- The signing handler of the simulated game: sign through the coin oracle and log the
message. -/
@[expose] noncomputable def signHandler (n : ℕ) (request : Unit × List Bool) :
    StateT (List (List Bool)) (WordOracleComp Unit) (List Bool) := fun queried => do
  let sig ← signO S T depth n request.2
  return (sig, request.2 :: queried)

/-- The tree game at parameter `n`, played against the coin oracle. -/
@[expose] noncomputable def simulateTreeGame (adversary : Forger) (n : ℕ) :
    WordOracleComp Unit Bool := do
  let root ← nodeKeyO S T n []
  let pk := encPair encUnary encBits (n, root.1)
  let out ← (OracleComp.interpret
    (OracleComp.sumHandler (fun k => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin k)))
      (signHandler S T depth n)) (adversary n pk)).run []
  let msig := out.1
  return (msig.1.length == n) && !out.2.contains msig.1 && verify S depth pk msig.1 msig.2

/-- The coin adversary: at the PRF's parameter `M`, recover `n` with `inv` and simulate the tree
game there; outside the range of `N`, output `false`. -/
noncomputable def treeCoinAdversary (inv : ℕ → ℕ) (adversary : Forger) : OracleDistinguisher :=
  fun M _ => if N (inv M) = M then simulateTreeGame S T depth adversary (inv M) else pure false

/-! ### Exact simulation with deterministic coins -/

section Deterministic

variable {S T depth}

/-- The coin function read off a deterministic coin oracle on request words. -/
@[expose] def coinsOf (c : List Bool → List Bool) (_k x : List Bool) (L : ℕ) : List Bool :=
  c (encPair encBits encUnary (x, L))

/-- The law of an oracle program whose coin requests are answered by the deterministic function
`c` on request words, with fresh private coins. -/
noncomputable def evalDet (c : List Bool → List Bool) {α : Type} (program : WordOracleComp Unit α) :
    PMF α :=
  OracleComp.evalWith (OracleComp.sumHandler ProbComp.unifOracle
    (fun r : Unit × List Bool => PMF.pure (c r.2))) program

variable (c : List Bool → List Bool)

@[simp] theorem evalDet_pure {α : Type} (a : α) :
    evalDet c (pure a : WordOracleComp Unit α) = PMF.pure a := by rfl

@[simp] theorem evalDet_bind {α β : Type} (program : WordOracleComp Unit α)
    (next : α → WordOracleComp Unit β) :
    evalDet c (program >>= next) = (evalDet c program).bind fun a => evalDet c (next a) :=
  OracleComp.evalWith_bind _ _ _

@[simp] theorem evalDet_map {α β : Type} (f : α → β) (program : WordOracleComp Unit α) :
    evalDet c (f <$> program) = (evalDet c program).map f :=
  OracleComp.evalWith_map _ _ _

@[simp] theorem evalDet_query (request : Unit × List Bool) :
    evalDet c (ProbOracleComp.query request) = PMF.pure (c request.2) :=
  OracleComp.evalWith_query _ _

@[simp] theorem evalDet_sample {α : Type} (program : ProbComp α) :
    evalDet c (ProbOracleComp.sample program) = ProbComp.eval program := by
  simp only [evalDet, OracleComp.evalWith, ProbOracleComp.interpret_sample]
  rfl

variable {c} (hc : ∀ x L, (c (encPair encBits encUnary (x, L))).length ≤ L)

include hc in
theorem evalDet_coinRequest (x : List Bool) (L : ℕ) :
    evalDet c (coinRequest x L) = PMF.pure (coinsOf c [] x L) := by
  simp only [coinRequest, evalDet_map, evalDet_query, PMF.pure_map, coinsOf,
    List.take_of_length_le (hc x L)]

include hc in
theorem evalDet_nodeKeyO (n : ℕ) (k path : List Bool) :
    evalDet c (nodeKeyO S T n path) = PMF.pure (nodeKey S T (coinsOf c) n k path) := by
  simp only [nodeKeyO, evalDet_map, evalDet_coinRequest hc, PMF.pure_map, nodeKey, coinsOf]

include hc in
theorem evalDet_signAtO (k path sk : List Bool) (u : ℕ) (msg : List Bool) :
    evalDet c (signAtO S T path sk u msg) = PMF.pure (signAt S T (coinsOf c) k path sk u msg) := by
  simp only [signAtO, evalDet_map, evalDet_coinRequest hc, PMF.pure_map, signAt, coinsOf]

include hc in
private theorem evalDet_certifyStepO (n : ℕ) (k leaf : List Bool) (state : CertState) :
    evalDet c (certifyStepO S T n leaf state) =
      PMF.pure (certifyStep S T (coinsOf c) n k state (leaf.getD state.1.length false)) := by
  simp only [certifyStepO, evalDet_bind, evalDet_pure, evalDet_nodeKeyO hc n k,
    evalDet_signAtO hc k, PMF.pure_bind, certifyStep]

/-- A loop of deterministic steps is the iterate of the step. -/
private theorem evalDet_iterate {σ : Type} (m : ℕ) (step : σ → WordOracleComp Unit σ) (f : σ → σ)
    (hstep : ∀ s, evalDet c (step s) = PMF.pure (f s)) (init : σ) :
    evalDet c (OracleComp.iterate m step init) = PMF.pure (f^[m] init) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [OracleComp.iterate_succ, evalDet_bind, ih, PMF.pure_bind, hstep,
      Function.iterate_succ_apply']

/-- The chain's path is the certified prefix. -/
private theorem fst_certify (coins : List Bool → List Bool → ℕ → List Bool) (n : ℕ)
    (k bits : List Bool) :
    (certify S T coins n k bits).1 = bits := by
  induction bits using List.reverseRecOn with
  | nil => rfl
  | append_singleton bits a ih => rw [certify_append]; simp only [certifyStep, ih]

/-- Reading the next bit by the current depth, the chain along the first `m` bits of a leaf is
the iterate of the step, for `m` at most the leaf's length. -/
private theorem certify_take_eq_iterate (coins : List Bool → List Bool → ℕ → List Bool) (n : ℕ)
    (k leaf : List Bool) {m : ℕ} (hm : m ≤ leaf.length) :
    certify S T coins n k (leaf.take m) =
      (fun s : CertState => certifyStep S T coins n k s (leaf.getD s.1.length false))^[m]
        ([], nodeKey S T coins n k [], []) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply', ← ih (by omega), List.take_succ_eq_append_getElem (by omega),
      certify_append, fst_certify, List.length_take, Nat.min_eq_left (by omega),
      List.getD_eq_getElem _ _ (by omega)]

include hc in
private theorem evalDet_certifyO (n : ℕ) (k leaf : List Bool) (hleaf : depth n - 1 ≤ leaf.length) :
    evalDet c (certifyO S T depth n leaf) =
      PMF.pure (certify S T (coinsOf c) n k (leaf.take (depth n - 1))) := by
  rw [certifyO, evalDet_bind, evalDet_nodeKeyO hc n k, PMF.pure_bind,
    evalDet_iterate _ _ _ (evalDet_certifyStepO hc n k leaf),
    certify_take_eq_iterate _ n k leaf hleaf]

include hc in
/-- With deterministic coins, the oracle signer is the signer of the tree scheme under any secret
key word `(n, k)`: the coins do not depend on `k`. -/
theorem evalDet_signO (n : ℕ) (k msg : List Bool) :
    evalDet c (signO S T depth n msg) =
      ProbComp.eval (sign S T (coinsOf c) depth (encPair encUnary encBits (n, k)) msg) := by
  by_cases hmsg : msg.length = n
  · simp only [signO, sign, keyDecoder.decode_enc, hmsg, ↓reduceIte, evalDet_bind, evalDet_pure,
      evalDet_sample, ProbComp.eval_bind, ProbComp.eval_pure, BitString.eval_sampleList]
    refine PMF.bind_congr_on_support _ _ _ fun leaf hleaf => ?_
    have hlen := BitString.length_of_mem_support_uniformList hleaf
    rw [evalDet_certifyO hc n k leaf (by omega), PMF.pure_bind, evalDet_signAtO hc k, PMF.pure_bind,
      signWithLeaf, List.dropLast_eq_take, hlen]
  · simp only [signO, sign, keyDecoder.decode_enc, hmsg, ↓reduceIte, evalDet_pure,
      ProbComp.eval_pure]

include hc in
/-- With deterministic coins, the simulated game is the tree game under any secret `k`. -/
theorem evalDet_simulateTreeGame (adversary : Forger) (n : ℕ) (k : List Bool) :
    evalDet c (simulateTreeGame S T depth adversary n) =
      ProbComp.eval (treeGameWith S T depth (coinsOf c) k adversary n) := by
  simp only [pmf_norm, simulateTreeGame, treeGameWith, evalDet_bind, evalDet_pure,
    evalDet_nodeKeyO hc n k, ProbOracleComp.eval_run_interpret]
  refine congrArg (fun p => PMF.bind p _) ?_
  rw [evalDet, OracleComp.map_run_interpret (OracleComp.isMonadHom_evalWith
    (OracleComp.sumHandler ProbComp.unifOracle (fun r : Unit × List Bool => PMF.pure (c r.2))))]
  refine congrArg (fun h => (OracleComp.interpret (m := StateT (List (List Bool)) PMF) h
    (adversary n _)).run []) ?_
  funext q state
  cases q with
  | inl m => rfl
  | inr request =>
    change OracleComp.evalWith _ ((signHandler S T depth n request).run state) = _
    simp only [signHandler, StateT.run, OracleComp.evalWith_bind, OracleComp.evalWith_pure]
    rw [← evalDet, evalDet_signO hc n k]

end Deterministic

/-! ### The tree game depends on the coins at the secret only -/

section Congr

variable {S T depth}
variable {coins coins' : List Bool → List Bool → ℕ → List Bool} {k k' : List Bool}
  (h : ∀ x L, coins k x L = coins' k' x L)

include h in
theorem nodeKey_congr (n : ℕ) (path : List Bool) :
    nodeKey S T coins n k path = nodeKey S T coins' n k' path := by
  simp only [nodeKey, h]

include h in
theorem signAt_congr (path sk : List Bool) (u : ℕ) (msg : List Bool) :
    signAt S T coins k path sk u msg = signAt S T coins' k' path sk u msg := by
  simp only [signAt, h]

include h in
theorem certify_congr (n : ℕ) (bits : List Bool) :
    certify S T coins n k bits = certify S T coins' n k' bits := by
  have hstep : certifyStep S T coins n k = certifyStep S T coins' n k' := by
    funext state a
    simp only [certifyStep, nodeKey_congr h, signAt_congr h]
  simp only [certify, nodeKey_congr h, hstep]

include h in
theorem signWithLeaf_congr (n : ℕ) (leaf msg : List Bool) :
    signWithLeaf S T coins n k leaf msg = signWithLeaf S T coins' n k' leaf msg := by
  simp only [signWithLeaf, certify_congr h, signAt_congr h]

include h in
theorem sign_congr (n : ℕ) (msg : List Bool) :
    sign S T coins depth (encPair encUnary encBits (n, k)) msg =
      sign S T coins' depth (encPair encUnary encBits (n, k')) msg := by
  simp only [sign, keyDecoder.decode_enc, signWithLeaf_congr h]

include h in
/-- The tree game under a secret depends on the coins at that secret only. -/
theorem treeGameWith_congr (adversary : Forger) (n : ℕ) :
    treeGameWith S T depth coins k adversary n = treeGameWith S T depth coins' k' adversary n := by
  simp only [treeGameWith, nodeKey_congr h, sign_congr h]

omit h in
/-- Since `tableCoins` ignores the secret key, `treeGame` with `tableCoins` has the same law as
`treeGameWith` at `[]` for any key-length schedule. -/
theorem eval_treeGame_tableCoins (keyLen : ℕ → ℕ) (M : ℕ) (table : BitString M → BitString M)
    (adversary : Forger) (n : ℕ) :
    ProbComp.eval (treeGame S T depth keyLen (tableCoins M table) adversary n) =
      ProbComp.eval (treeGameWith S T depth (tableCoins M table) [] adversary n) := by
  rw [eval_treeGame]
  refine (congrArg (PMF.bind _) (funext fun k => congrArg ProbComp.eval
    (treeGameWith_congr (coins := tableCoins M table) (coins' := tableCoins M table)
      (k := k) (k' := []) (fun _ _ => rfl) adversary n))).trans (PMF.bind_const _ _)

end Congr

/-! ### The coin games of the coin adversary -/

section Games

variable {S T depth N}
variable (family : List Bool → List Bool → List Bool) {inv : ℕ → ℕ} (hinv : ∀ n, inv (N n) = n)

include hinv in
/-- The coin adversary at `N n` plays the simulated game at `n`. -/
theorem treeCoinAdversary_apply (adversary : Forger) (n : ℕ) (aux : List Bool) :
    treeCoinAdversary S T depth N inv adversary (N n) aux =
      simulateTreeGame S T depth adversary n := by
  simp only [treeCoinAdversary, hinv n, ite_true]

/-- Evaluating against a stateless deterministic coin oracle is `evalDet`. -/
theorem eval_interpret_eq_evalDet (c : List Bool → List Bool) {α : Type}
    (program : WordOracleComp Unit α) :
    ProbComp.eval (OracleComp.interpret
      (OracleComp.sumHandler ProbComp.unifFin (fun request : Unit × List Bool =>
        pure (c request.2))) program) = evalDet c program := by
  rw [ProbOracleComp.eval_interpret]
  rfl

include hinv in
/-- **Real coins**: the coin adversary in the real coin game at `N n` plays the tree game with
coins `prfCoins family`. -/
theorem eval_coinRealGame_treeCoinAdversary (adversary : Forger) (n : ℕ) :
    ProbComp.eval (coinRealGame family (treeCoinAdversary S T depth N inv adversary) (N n)) =
      ProbComp.eval (treeGame S T depth N (prfCoins family) adversary n) := by
  simp only [coinRealGame, ProbComp.eval_bind, BitString.eval_sampleList,
    treeCoinAdversary_apply hinv adversary, eval_interpret_eq_evalDet, eval_treeGame]
  refine PMF.bind_congr_on_support _ _ _ fun key _ => ?_
  have hc : ∀ x L, (coinOracle family key (encPair encBits encUnary (x, L))).length ≤ L := by
    intro x L
    simp only [coinOracle, coinRequestDecoder.decode_enc, prfCoins]
    exact List.length_take_le _ _
  rw [evalDet_simulateTreeGame hc adversary n key]
  refine congrArg ProbComp.eval (treeGameWith_congr (fun x L => ?_) adversary n)
  simp only [coinsOf, coinOracle, coinRequestDecoder.decode_enc]

include hinv in
/-- **Random coins**: the coin adversary in the ideal coin game at `N n` plays the tree game with
coins from a uniform random function on `N n` bits. -/
theorem eval_coinIdealGame_treeCoinAdversary (adversary : Forger) (n : ℕ) :
    ProbComp.eval (coinIdealGame (treeCoinAdversary S T depth N inv adversary) (N n)) =
      ProbComp.eval (treeIdealGame S T depth N adversary n) := by
  simp only [coinIdealGame, treeIdealGame, ProbComp.eval_bind,
    treeCoinAdversary_apply hinv adversary, eval_interpret_eq_evalDet]
  refine PMF.bind_congr_on_support _ _ _ fun table _ => ?_
  have hc : ∀ x L, (randomCoinOracle (N n) table (encPair encBits encUnary (x, L))).length ≤ L := by
    intro x L
    simp only [randomCoinOracle, coinRequestDecoder.decode_enc]
    exact List.length_take_le _ _
  rw [evalDet_simulateTreeGame hc adversary n []]
  have hcoins : coinsOf (randomCoinOracle (N n) table) = tableCoins (N n) table := by
    funext k x L
    simp only [coinsOf, randomCoinOracle, coinRequestDecoder.decode_enc, tableCoins]
  rw [hcoins]

end Games

/-! ### The hybrid bound -/

section Bound

variable {S T depth N}

variable (family : List Bool → List Bool → List Bool) {inv : ℕ → ℕ} (hinv : ∀ n, inv (N n) = n)

include hinv in
/-- **From pseudorandom to random coins**: the forging probability against the tree scheme with
coins from `family` is at most the forging probability with coins from a random function, plus the
coin-game advantage of `treeCoinAdversary` at the PRF's parameter `N n`. -/
theorem succProbability_treeGame_le (adversary : Forger) (n : ℕ) :
    Game.succProbability (ProbComp.eval (treeGame S T depth N (prfCoins family) adversary n)) ≤
      Game.succProbability (ProbComp.eval (treeIdealGame S T depth N adversary n)) +
        Game.advantage
          (ProbComp.eval (coinRealGame family (treeCoinAdversary S T depth N inv adversary) (N n)))
          (ProbComp.eval (coinIdealGame (treeCoinAdversary S T depth N inv adversary) (N n))) := by
  rw [eval_coinRealGame_treeCoinAdversary family hinv, eval_coinIdealGame_treeCoinAdversary hinv]
  exact Game.succProbability_le_add_of_advantage_le le_rfl

include hinv in
/-- **From pseudorandom to random coins, in PRF advantage**: the hybrid loss equals the PRF
distinguishing advantage of `coinDistinguisher (treeCoinAdversary …)` at `N n`. -/
theorem succProbability_treeGame_le_prf (adversary : Forger) (n : ℕ) :
    Game.succProbability (ProbComp.eval (treeGame S T depth N (prfCoins family) adversary n)) ≤
      Game.succProbability (ProbComp.eval (treeIdealGame S T depth N adversary n)) +
        Game.advantage
          (ProbComp.eval (prfRealGame family
            (coinDistinguisher (treeCoinAdversary S T depth N inv adversary)) (N n)))
          (ProbComp.eval (prfIdealGame
            (coinDistinguisher (treeCoinAdversary S T depth N inv adversary)) (N n))) := by
  rw [← eval_coinRealGame, ← eval_coinIdealGame]
  exact succProbability_treeGame_le family hinv adversary n

open Filter in
omit hinv in
/-- The coin-game advantage of the coin adversary, read at `N n`, is negligible in `n` for a
pseudorandom function, an oracle-PPT coin adversary and `n ≤ N n`. -/
theorem negligible_advantage_treeCoinAdversary (hF : PseudorandomFunction family)
    (hN : ∀ n, n ≤ N n) {adversary : Forger}
    (hB : IsOraclePPT encBool (treeCoinAdversary S T depth N inv adversary)) :
    Negligible (fun n => Game.advantage
      (ProbComp.eval (coinRealGame family (treeCoinAdversary S T depth N inv adversary) (N n)))
      (ProbComp.eval (coinIdealGame (treeCoinAdversary S T depth N inv adversary) (N n)))) := by
  refine negligible_of_le
    ((hF.coinIndistinguishable _ hB).comp_of_polynomial_bound
      (tendsto_atTop_mono hN tendsto_id) (bound := id)
      PolynomiallyBounded.id (Eventually.of_forall hN)) fun _ => ?_
  dsimp only [Function.comp_apply]
  exact le_rfl

end Bound

/-! ### Efficiency of the coin adversary -/

section Efficiency

variable {S T depth N}

/-- A coin request with efficiently computed request and count is strict oracle PPT. -/
theorem isOraclePPTOn_coinRequest {γ : Type} {enc : γ ↪ List Bool} {x : γ → List Bool}
    {L : γ → ℕ} (hx : ComputableInPolyTime x enc encBits)
    (hL : ComputableInPolyTime L enc encUnary) :
    IsOraclePPTOn enc encBits (fun a => coinRequest (x a) (L a)) :=
  IsOraclePPTOn.query_take' () (hx.prod hL).encoding_comp hL

/-- Deriving a node key is strict oracle PPT. -/
theorem isOraclePPTOn_nodeKeyO {γ : Type} {enc : γ ↪ List Bool} {n : γ → ℕ}
    {path : γ → List Bool} (hn : ComputableInPolyTime n enc encUnary)
    (hpath : ComputableInPolyTime path enc encBits) :
    IsOraclePPTOn enc (encPair encBits encBits) (fun a => nodeKeyO S T (n a) (path a)) :=
  (isOraclePPTOn_coinRequest (((ComputableInPolyTime.const false).prod hpath).encoding_comp)
    (T.keyGenBudget_polyTime.comp' hn)).map_with'
    (T.keyGenWith_polyTime.comp' ((hn.comp' (.fst _ _)).prod (.snd _ _)))

/-- Deriving a node signature is strict oracle PPT. -/
theorem isOraclePPTOn_signAtO {γ : Type} {enc : γ ↪ List Bool} {path sk msg : γ → List Bool}
    {u : γ → ℕ} (hpath : ComputableInPolyTime path enc encBits)
    (hsk : ComputableInPolyTime sk enc encBits) (hu : ComputableInPolyTime u enc encUnary)
    (hmsg : ComputableInPolyTime msg enc encBits) :
    IsOraclePPTOn enc encBits (fun a => signAtO S T (path a) (sk a) (u a) (msg a)) :=
  (isOraclePPTOn_coinRequest
    (((ComputableInPolyTime.const true).prod (hpath.prod hu)).encoding_comp)
    (T.signBudget_polyTime.comp' (hsk.prod (hu.prod hmsg)))).map_with'
    (T.signWith_polyTime.comp' (((hsk.prod (hu.prod hmsg)).comp' (.fst _ _)).prod (.snd _ _)))

/-- A chain state, written out so that the certificate automation sees the product. -/
local notation "CertTriple" => (List Bool × (List Bool × List Bool) × List (List Bool × List Bool))

/-- One chain step is strict oracle PPT in the parameter, the leaf and the state. -/
private theorem isOraclePPTOn_certifyStepO :
    IsOraclePPTOn (encPair (encPair encUnary encBits) encCertState) encCertState
      (fun (((n, leaf), state) : (ℕ × List Bool) × CertTriple) =>
        certifyStepO S T n leaf state) := by
  let E0 := encPair (encPair encUnary encBits) encCertState
  let E1 := encPair E0 (encPair encBits encBits)
  have hp0 := ComputableInPolyTime.id' (encIn := E0)
  have hp1 := ComputableInPolyTime.id' (encIn := E1)
  have hp2 := ComputableInPolyTime.id' (encIn := encPair E1 encBits)
  have hnode0 := hp0.snd'.fst'
  have hbit0 := hp0.fst'.snd'.bitsGetDWithInput hnode0.length_bits_comp false
  have hpath0 := hnode0.bitsAppend (hbit0.trans (.of_finite fun a : Bool => [a]))
  have hsign1 := isOraclePPTOn_signAtO (S := S) (T := T)
    (hnode0.comp' hp1.fst') hp1.fst'.snd'.snd'.fst'.snd'
    ((hbit0.comp' hp1.fst').trans (.of_finite Bool.toNat)) hp1.snd'.fst'
  have hret2 := (hpath0.comp' hp2.fst'.fst').prod (hp2.fst'.snd'.prod
    (hp2.fst'.fst'.snd'.snd'.snd'.listAppend'
      (.cons' (hp2.fst'.snd'.fst'.prod hp2.snd') (.const []))))
  exact (isOraclePPTOn_nodeKeyO hp0.fst'.fst' hpath0).bind_with
    (hsign1.bind_with hret2.isOraclePPTOn)

/-! #### Polynomial bounds on derived keys and signatures -/

section Bounds

-- Constants of the polynomial bounds on the seeded algorithms: output lengths of `keyGenWith`
-- and `signWith`, and the budgets.
variable {ck dk cb db cs ds cB dB : ℕ}
  (hkg : ∀ n coins, (encPair encBits encBits (T.keyGenWith n coins)).length ≤
    ck * ((encPair encUnary encBits (n, coins)).length + 1) ^ dk)
  (hkb : ∀ n, T.keyGenBudget n ≤ cb * (n + 1) ^ db)
  (hsg : ∀ sk u msg coins, (T.signWith sk u msg coins).length ≤
    cs * ((encPair (encPair encBits (encPair encUnary encBits)) encBits
      ((sk, u, msg), coins)).length + 1) ^ ds)
  (hsb : ∀ sk u msg, T.signBudget sk u msg ≤
    cB * ((encPair encBits (encPair encUnary encBits) (sk, u, msg)).length + 1) ^ dB)

/-- A bound on both components of a derived node key at parameter `n`. -/
@[expose] def keyBound (ck dk cb db n : ℕ) : ℕ := ck * (2 * n + 2 + cb * (n + 1) ^ db) ^ dk

/-- A bound on a derived signature by a node whose secret key has length at most `K`, at an index
at most `1`, on a message of length at most `L`. -/
@[expose] def sigBound (cs ds cB dB K L : ℕ) : ℕ :=
  cs * (2 * (2 * K + L + 4) + cB * (2 * K + L + 5) ^ dB + 2) ^ ds

theorem computableInPolyTime_keyBound (ck dk cb db : ℕ) :
    ComputableInPolyTime (keyBound ck dk cb db) encUnary encUnary := by
  unfold keyBound
  fun_prop

theorem computableInPolyTime_sigBound (cs ds cB dB : ℕ) :
    ComputableInPolyTime (fun p : ℕ × ℕ => sigBound cs ds cB dB p.1 p.2)
      (encPair encUnary encUnary) encUnary := by
  unfold sigBound
  fun_prop

private theorem sigBound_funProp {α : Type} {enc : α ↪ List Bool} {K L : α → ℕ}
    (cs ds cB dB : ℕ) (hK : ComputableInPolyTime K enc encUnary)
    (hL : ComputableInPolyTime L enc encUnary) :
    ComputableInPolyTime (fun a => sigBound cs ds cB dB (K a) (L a)) enc encUnary :=
  ((computableInPolyTime_sigBound cs ds cB dB).comp' (hK.prod hL)).of_enc_eq fun _ => rfl

/-- A reply to a coin request has at most the requested length. -/
theorem length_le_of_mem_support_coinRequest {x : List Bool} {L : ℕ} {coins : List Bool}
    (h : coins ∈ OracleComp.support (coinRequest x L)) : coins.length ≤ L := by
  obtain ⟨raw, -, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp h
  exact List.length_take_le _ _

include hkg hkb in
/-- Both components of a derived node key are bounded by `keyBound`. -/
theorem length_le_of_mem_support_nodeKeyO {n : ℕ} {path : List Bool} {key : List Bool × List Bool}
    (h : key ∈ OracleComp.support (nodeKeyO S T n path)) :
    let (pk, sk) := key
    pk.length ≤ keyBound ck dk cb db n ∧ sk.length ≤ keyBound ck dk cb db n := by
  obtain ⟨coins, hcoins, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp h
  have hlen := (length_le_of_mem_support_coinRequest hcoins).trans (hkb n)
  have hbound := (hkg n coins).trans (Nat.mul_le_mul_left ck (Nat.pow_le_pow_left
    (show (encPair encUnary encBits (n, coins)).length + 1 ≤ 2 * n + 2 + cb * (n + 1) ^ db by
      simp only [length_encPair, encUnary_apply, List.length_replicate, encBits_apply]; omega) dk))
  exact ⟨(length_le_encPair_left encBits encBits _).trans hbound,
    (length_le_encPair_right encBits encBits _).trans hbound⟩

include hsg hsb in
/-- A derived signature is bounded by `sigBound`. -/
theorem length_le_of_mem_support_signAtO {path sk msg σ : List Bool} {u K L : ℕ}
    (hsk : sk.length ≤ K) (hu : u ≤ 1) (hmsg : msg.length ≤ L)
    (h : σ ∈ OracleComp.support (signAtO S T path sk u msg)) :
    σ.length ≤ sigBound cs ds cB dB K L := by
  obtain ⟨coins, hcoins, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp h
  have hlen := (length_le_of_mem_support_coinRequest hcoins).trans (hsb sk u msg)
  simp only [length_encPair, encUnary_apply, List.length_replicate, encBits_apply] at hlen
  refine (hsg sk u msg coins).trans (Nat.mul_le_mul_left cs (Nat.pow_le_pow_left ?_ ds))
  simp only [length_encPair, encUnary_apply, List.length_replicate, encBits_apply]
  have hpow : cB * (2 * sk.length + 1 + (2 * u + 1 + msg.length) + 1) ^ dB ≤
      cB * (2 * K + L + 5) ^ dB :=
    Nat.mul_le_mul_left cB (Nat.pow_le_pow_left (by omega) dB)
  omega

variable (hdepth : ComputableInPolyTime depth encUnary encUnary)

/-- The key bound of a loop input `((n, leaf), root)`: `keyBound n`, covering also the root. -/
private def loopKeyBound (ck dk cb db : ℕ) (a : (ℕ × List Bool) × (List Bool × List Bool)) : ℕ :=
  keyBound ck dk cb db a.1.1 + a.2.1.length + a.2.2.length

/-- The invariant of the chain loop after `i` steps: the path has `i` bits, the current key and
every certified key are bounded by the loop's key bound, and every certified signature by the
corresponding `sigBound`. -/
private def chainInvariant (ck dk cb db cs ds cB dB : ℕ)
    (a : (ℕ × List Bool) × (List Bool × List Bool)) (i : ℕ) (state : CertState) : Prop :=
  state.1.length = i ∧ state.2.1.1.length ≤ loopKeyBound ck dk cb db a ∧
    state.2.1.2.length ≤ loopKeyBound ck dk cb db a ∧ state.2.2.length = i ∧
    ∀ e ∈ state.2.2, e.1.length ≤ loopKeyBound ck dk cb db a ∧
      e.2.length ≤ sigBound cs ds cB dB (loopKeyBound ck dk cb db a) (loopKeyBound ck dk cb db a)

include hkg hkb hsg hsb in
/-- One chain step preserves the invariant, whatever the oracle answers. -/
private theorem chainInvariant_step (a : (ℕ × List Bool) × (List Bool × List Bool)) (i : ℕ)
    (state : CertState) (hinv : chainInvariant ck dk cb db cs ds cB dB a i state)
    (next : CertState) (hnext : next ∈ OracleComp.support (certifyStepO S T a.1.1 a.1.2 state)) :
    chainInvariant ck dk cb db cs ds cB dB a (i + 1) next := by
  obtain ⟨hpath, hpk, hsk, hlen, hcerts⟩ := hinv
  supp_cases hnext [certifyStepO] with ⟨child, hchild, σ, hσ, rfl⟩
  have hchild' := length_le_of_mem_support_nodeKeyO hkg hkb hchild
  have hK : keyBound ck dk cb db a.1.1 ≤ loopKeyBound ck dk cb db a := by
    simp only [loopKeyBound]; omega
  have hσ' := length_le_of_mem_support_signAtO hsg hsb hsk
    (show (a.1.2.getD state.1.length false).toNat ≤ 1 from Bool.toNat_le _)
    (hchild'.1.trans hK) hσ
  refine ⟨by simp only [List.length_append, List.length_singleton, hpath],
    hchild'.1.trans hK, hchild'.2.trans hK,
    by simp only [List.length_append, List.length_singleton, hlen], ?_⟩
  intro e he
  simp only [List.mem_append, List.mem_singleton] at he
  rcases he with he | rfl
  · exact hcerts e he
  · exact ⟨hchild'.1.trans hK, hσ'⟩

include hkg hkb hsg hsb hdepth in
/-- The chain loop is strict oracle PPT in `((n, leaf), root)`, and every possible final state
satisfies the invariant at `depth n - 1`. -/
private theorem isOraclePPTOn_chain :
    IsOraclePPTOn (encPair (encPair encUnary encBits) (encPair encBits encBits)) encCertState
      (fun a : (ℕ × List Bool) × (List Bool × List Bool) =>
        OracleComp.iterate (depth a.1.1 - 1) (certifyStepO S T a.1.1 a.1.2) ([], a.2, [])) ∧
    ∀ a : (ℕ × List Bool) × (List Bool × List Bool), ∀ state ∈ OracleComp.support
      (OracleComp.iterate (depth a.1.1 - 1) (certifyStepO S T a.1.1 a.1.2) ([], a.2, [])),
      chainInvariant ck dk cb db cs ds cB dB a (depth a.1.1 - 1) state := by
  let encIn := encPair (encPair encUnary encBits) (encPair encBits encBits)
  let K := loopKeyBound ck dk cb db
  let B (a : (ℕ × List Bool) × (List Bool × List Bool)) := sigBound cs ds cB dB (K a) (K a)
  have ha := ComputableInPolyTime.id' (encIn := encIn)
  have hp := ComputableInPolyTime.id' (encIn := encPair encIn encCertState)
  have hd := hdepth.comp' ha.fst'.fst'
  have hK : ComputableInPolyTime K encIn encUnary :=
    ((((computableInPolyTime_keyBound ck dk cb db).comp' ha.fst'.fst').unary_add'
      ha.snd'.fst'.length_bits_comp).unary_add' ha.snd'.snd'.length_bits_comp).of_enc_eq
      fun _ => rfl
  have hB : ComputableInPolyTime B encIn encUnary :=
    sigBound_funProp cs ds cB dB hK hK
  let c2 := ComputableInPolyTime.const (encIn := encIn) (encOut := encUnary) 2
  let c1 := ComputableInPolyTime.const (encIn := encIn) (encOut := encUnary) 1
  have h2K1 := (c2.unary_mul' hK).unary_add' c1
  have hsize : ComputableInPolyTime
      (fun a => 2 * depth a.1.1 + 1 + (2 * (2 * K a + 1 + K a) + 1 +
        depth a.1.1 * (2 * (2 * K a + 1 + B a) + 1))) encIn encUnary :=
    (((c2.unary_mul' hd).unary_add' c1).unary_add'
      (((c2.unary_mul' (h2K1.unary_add' hK)).unary_add' c1).unary_add'
        (hd.unary_mul' ((c2.unary_mul' (h2K1.unary_add' hB)).unary_add' c1)))).of_enc_eq
      fun _ => rfl
  refine IsOraclePPTOn.iterateWith_spec'
    ((hd.unary_sub' c1).of_enc_eq fun _ => rfl)
    (((ComputableInPolyTime.const []).prod (ha.snd'.prod (.const []))).of_enc_eq fun _ => rfl)
    (Eq.mp (congrArg (IsOraclePPTOn (encPair encIn encCertState) encCertState)
      (funext fun ⟨⟨⟨_, _⟩, _⟩, _⟩ => rfl))
      (isOraclePPTOn_certifyStepO.preprocess' (hp.fst'.fst'.prod hp.snd')))
    (chainInvariant ck dk cb db cs ds cB dB)
    (fun a => ⟨rfl, by change a.2.1.length ≤ _; unfold loopKeyBound; omega,
      by change a.2.2.length ≤ _; unfold loopKeyBound; omega, rfl, by rintro _ ⟨⟩⟩)
    (fun a i state _ => chainInvariant_step hkg hkb hsg hsb a i state)
    hsize.polyBounded ?_
  rintro a i ⟨path, key, certs⟩ hi ⟨hpath, hpk, hsk, hlen, hcerts⟩
  have hlist := length_encList_le (encPair encBits encBits) certs
    (b := 2 * K a + 1 + B a) fun e he => by
    obtain ⟨h1, h2⟩ := hcerts e he; simp only [length_encPair, encBits_apply, K, B]; omega
  have hmul := Nat.mul_le_mul_right (2 * (2 * K a + 1 + B a) + 1) (hi.trans (Nat.sub_le _ _))
  dsimp only at hpath hlen
  simp only [length_encPair, encBits_apply, hpath, hlen, K, B] at hpk hsk hlist hmul ⊢
  omega

omit hkg hkb hsg hsb hdepth in
/-- `sigBound` is monotone in both bounds. -/
theorem sigBound_mono {K K' L L' : ℕ} (hK : K ≤ K') (hL : L ≤ L') :
    sigBound cs ds cB dB K L ≤ sigBound cs ds cB dB K' L' := by
  unfold sigBound
  have h1 : cB * (2 * K + L + 5) ^ dB ≤ cB * (2 * K' + L' + 5) ^ dB :=
    Nat.mul_le_mul_left cB (Nat.pow_le_pow_left (by omega) dB)
  exact Nat.mul_le_mul_left cs (Nat.pow_le_pow_left (by omega) ds)

include hkg hkb hsg hsb hdepth in
private theorem isOraclePPTOn_certifyO_aux :
    IsOraclePPTOn (encPair encUnary encBits) encCertState
      (fun p : ℕ × List Bool => certifyO S T depth p.1 p.2) ∧
    ∀ p : ℕ × List Bool, ∀ c ∈ OracleComp.support (certifyO S T depth p.1 p.2),
      c.1.length = depth p.1 - 1 ∧ c.2.1.2.length ≤ 3 * keyBound ck dk cb db p.1 ∧
      c.2.2.length = depth p.1 - 1 ∧
      ∀ e ∈ c.2.2, e.1.length ≤ 3 * keyBound ck dk cb db p.1 ∧
        e.2.length ≤ sigBound cs ds cB dB (3 * keyBound ck dk cb db p.1)
          (3 * keyBound ck dk cb db p.1) := by
  obtain ⟨hchain, hchainInv⟩ := isOraclePPTOn_chain hkg hkb hsg hsb hdepth
  refine ⟨(isOraclePPTOn_nodeKeyO (ComputableInPolyTime.fst _ _) (.const [])).bind_with hchain, ?_⟩
  intro p c hc
  simp only [certifyO, OracleComp.support, OracleComp.mem_supportWith_bind_iff] at hc
  obtain ⟨root, hroot, hc⟩ := hc
  have hrootLen := length_le_of_mem_support_nodeKeyO hkg hkb hroot
  obtain ⟨hpath, -, hsk, hlen, hcerts⟩ := hchainInv (p, root) c hc
  have hK : loopKeyBound ck dk cb db (p, root) ≤ 3 * keyBound ck dk cb db p.1 := by
    change keyBound ck dk cb db p.1 + root.1.length + root.2.length ≤ _; omega
  exact ⟨hpath, hsk.trans hK, hlen, fun e he =>
    ⟨(hcerts e he).1.trans hK, (hcerts e he).2.trans (sigBound_mono hK hK)⟩⟩

/-- A bound on the length of a signature word produced by `signO` at parameter `n` on an `L`-bit
message. -/
private def sigWordBound (ck dk cb db cs ds cB dB : ℕ) (depth : ℕ → ℕ) (n L : ℕ) : ℕ :=
  2 * depth n + 1 + (2 * (depth n * (2 * (2 * (3 * keyBound ck dk cb db n) + 1 +
    sigBound cs ds cB dB (3 * keyBound ck dk cb db n) (3 * keyBound ck dk cb db n)) + 1)) + 1 +
    sigBound cs ds cB dB (3 * keyBound ck dk cb db n) L)

include hdepth in
private theorem computableInPolyTime_sigWordBound (ck dk cb db cs ds cB dB : ℕ) :
    ComputableInPolyTime (fun p : ℕ × ℕ => sigWordBound ck dk cb db cs ds cB dB depth p.1 p.2)
      (encPair encUnary encUnary) encUnary := by
  let E := encPair encUnary encUnary
  have hp := ComputableInPolyTime.id' (encIn := E)
  have hd := hdepth.comp' hp.fst'
  have h3K := (ComputableInPolyTime.const 3).unary_mul'
    ((computableInPolyTime_keyBound ck dk cb db).comp' hp.fst')
  have hB1 := sigBound_funProp cs ds cB dB h3K h3K
  have hB2 := sigBound_funProp cs ds cB dB h3K hp.snd'
  let c2 := ComputableInPolyTime.const (encIn := E) (encOut := encUnary) 2
  let c1 := ComputableInPolyTime.const (encIn := E) (encOut := encUnary) 1
  exact (((c2.unary_mul' hd).unary_add' c1).unary_add'
    (((c2.unary_mul' (hd.unary_mul'
      ((c2.unary_mul' (((c2.unary_mul' h3K).unary_add' c1).unary_add' hB1)).unary_add'
        c1))).unary_add' c1).unary_add' hB2)).of_enc_eq fun _ => rfl

include hkg hkb hsg hsb hdepth in
private theorem isOraclePPTOn_signO_aux :
    IsOraclePPTOn (encPair encUnary encBits) encBits
      (fun p : ℕ × List Bool => signO S T depth p.1 p.2) ∧
    ∀ p : ℕ × List Bool, ∀ sig ∈ OracleComp.support (signO S T depth p.1 p.2),
      sig.length ≤ sigWordBound ck dk cb db cs ds cB dB depth p.1 p.2.length := by
  obtain ⟨hcert, hcertBound⟩ := isOraclePPTOn_certifyO_aux hkg hkb hsg hsb hdepth
  refine ⟨?_, ?_⟩
  · let E0 := encPair encUnary encBits
    let E1 := encPair E0 encBits
    let E2 := encPair E1 encCertState
    have hp0 := ComputableInPolyTime.id' (encIn := E0)
    have hp1 := ComputableInPolyTime.id' (encIn := E1)
    have hp2 := ComputableInPolyTime.id' (encIn := E2)
    have hp3 := ComputableInPolyTime.id' (encIn := encPair E2 encBits)
    have hleaf := (ComputableInPolyTime.sampleList (hdepth.comp' hp0.fst')).isOraclePPTOn
      (Operation := Unit)
    have hcert1 := hcert.preprocess' (hp1.fst'.fst'.prod hp1.snd')
    have hlast2 : ComputableInPolyTime
        (fun q : ((ℕ × List Bool) × List Bool) × CertState => (q.1.2.getLastD false).toNat)
        E2 encUnary :=
      ((hp2.fst'.snd'.bitsGetDWithInput
        (hp2.fst'.snd'.length_bits_comp.unary_sub' (.const 1)) false).trans
        (.of_finite (encOut := encUnary) Bool.toNat)).of_enc_eq fun q => by
          simp only [List.getLastD_eq_getLast?, List.getLast?_eq_getElem?,
            ← List.getD_eq_getElem?_getD]
    have hsign2 := isOraclePPTOn_signAtO (S := S) (T := T) hp2.snd'.fst'
      hp2.snd'.snd'.fst'.snd' hlast2 hp2.fst'.fst'.snd'
    have hret3 := (hp3.fst'.fst'.snd'.prod (hp3.fst'.snd'.snd'.snd'.prod hp3.snd')).encoding_comp
    unfold signO
    exact IsOraclePPTOn.ite' (condition := fun p : ℕ × List Bool => p.2.length = p.1)
      ((hp0.snd'.length_bits_comp.decide_eq' hp0.fst').of_enc_eq fun _ => rfl)
      (hleaf.bind_with (hcert1.bind_with (hsign2.bind_with hret3.isOraclePPTOn)))
      (ComputableInPolyTime.isOraclePPTOn (ComputableInPolyTime.const []))
  · intro p sig hsig
    unfold signO at hsig
    split_ifs at hsig with hmsg
    · supp_cases hsig with ⟨leaf, hleaf, ⟨node, ⟨pk, sk⟩, certs⟩, hc, σ, hσ, rfl⟩
      change leaf ∈ (ProbOracleComp.sample (BitString.sampleList (depth p.1))).support at hleaf
      rw [ProbOracleComp.support_sample, BitString.eval_sampleList] at hleaf
      have hleafLen := BitString.length_of_mem_support_uniformList hleaf
      obtain ⟨-, hsk, hlen, hcerts⟩ := hcertBound (p.1, leaf) (node, (pk, sk), certs) hc
      have hσ' := length_le_of_mem_support_signAtO hsg hsb hsk (Bool.toNat_le _) le_rfl hσ
      dsimp only at hsk hlen hcerts hσ'
      let K3 := 3 * keyBound ck dk cb db p.1
      have hlist := length_encList_le (encPair encBits encBits) certs
        (b := 2 * K3 + 1 + sigBound cs ds cB dB K3 K3) fun e he => by
        obtain ⟨h1, h2⟩ := hcerts e he; simp only [length_encPair, encBits_apply, K3]; omega
      have hmul := Nat.mul_le_mul_right (2 * (2 * K3 + 1 + sigBound cs ds cB dB K3 K3) + 1)
        (Nat.sub_le (depth p.1) 1)
      simp only [encodeSignature, length_encPair, encBits_apply, sigWordBound, hleafLen, hlen, K3]
        at hsk hlist hmul ⊢
      omega
    · rw [OracleComp.eq_of_mem_supportWith_pure hsig]
      exact Nat.zero_le _

include hkg hkb hsg hsb hdepth in
private theorem isOraclePPTOn_simulateTreeGame_aux {adversary : Forger}
    (hA : IsOraclePPT (encPair encBits encBits) adversary) :
    IsOraclePPTOn encUnary encBool (fun n => simulateTreeGame S T depth adversary n) := by
  obtain ⟨hsign, hsignBound⟩ := isOraclePPTOn_signO_aux hkg hkb hsg hsb hdepth
  let encCaller := encPair encUnary (encPair encBits encBits)
  let encHandlerIn :=
    encPair encCaller (encPair (encPair (encFinEnum Unit) encBits) (encList encBits))
  have hp := ComputableInPolyTime.id' (encIn := encHandlerIn)
  have hq := ComputableInPolyTime.id' (encIn := encPair encHandlerIn encBits)
  have hhandler : IsOraclePPTOn encHandlerIn (encPair encBits (encList encBits))
      (fun pair : (ℕ × (List Bool × List Bool)) × ((Unit × List Bool) × List (List Bool)) =>
        signHandler S T depth pair.1.1 pair.2.1 pair.2.2) :=
    (hsign.preprocess' ((hp.fst'.fst'.prod hp.snd'.fst'.snd').of_enc_eq fun _ => rfl)).bind_with
      ((hq.snd'.prod (.cons' hq.fst'.snd'.fst'.snd' hq.fst'.snd'.snd')).of_enc_eq
        fun _ => rfl).isOraclePPTOn
  have hbound := computableInPolyTime_sigWordBound (depth := depth) hdepth ck dk cb db cs ds cB dB
  have hr := ComputableInPolyTime.id' (encIn := encPair encCaller encBits)
  have hlen := hr.snd'.length_bits_comp
  have hresources : ComputableInPolyTime
      (fun pair : (ℕ × (List Bool × List Bool)) × List Bool =>
        sigWordBound ck dk cb db cs ds cB dB depth pair.1.1 pair.2.length + 2 * pair.2.length + 2)
      (encPair encCaller encBits) encUnary :=
    ((((hbound.comp' (hr.fst'.fst'.prod hlen)).unary_add'
      ((ComputableInPolyTime.const 2).unary_mul' hlen)).unary_add' (.const 2))).of_enc_eq
      fun _ => rfl
  have hc := ComputableInPolyTime.id' (encIn := encCaller)
  have hrun := hA.run_interpret_preprocess_open' (External := Unit)
    (handler := fun c : ℕ × (List Bool × List Bool) => signHandler S T depth c.1)
    (prepare := fun c : ℕ × (List Bool × List Bool) =>
      (c.1, encPair encUnary encBits (c.1, c.2.1)))
    (initial := fun _ => ([] : List (List Bool)))
    (resources := fun c w =>
      sigWordBound ck dk cb db cs ds cB dB depth c.1 w.length + 2 * w.length + 2)
    ((hc.fst'.prod (hc.fst'.prod hc.snd'.fst').encoding_comp).of_enc_eq fun _ => rfl)
    hhandler (ComputableInPolyTime.const [])
    (fun _ _ => True) (fun _ => trivial) hresources fun c request queried _ result hresult => by
      supp_cases hresult [signHandler] with ⟨sig, hsig, rfl⟩
      have hsigLen := hsignBound (c.1, request.2) sig hsig
      dsimp only at hsigLen
      refine ⟨trivial, by change sig.length ≤ _; omega, ?_⟩
      change (encList encBits (request.2 :: queried)).length ≤ _
      simp only [encList_cons, List.length_append, length_frame, encBits_apply]; omega
  have hg := ComputableInPolyTime.id'
    (encIn := encPair encCaller (encPair (encPair encBits encBits) (encList encBits)))
  have hpk := (hg.fst'.fst'.prod hg.fst'.snd'.fst').encoding_comp
  have hmsg := hg.snd'.fst'.fst'
  have hv := (computableInPolyTime_verify (S := S) (depth := depth) hdepth).comp'
    (hpk.prod (hmsg.prod hg.snd'.fst'.snd'))
  have hchk := (hmsg.length_bits_comp.unary_beq' hg.fst'.fst').bool_and'
    (ComputableInPolyTime.bool_not.comp'
      (ComputableInPolyTime.anyWithInput (test := fun q b => b == q.2.1.1) hg.snd'.snd'
        (((ComputableInPolyTime.snd _ encBits).beq (hmsg.comp' (.fst _ encBits))).of_enc_eq
          fun _ => rfl)))
  have hpost := (hchk.bool_and' hv).of_enc_eq
    (g := fun q : (ℕ × (List Bool × List Bool)) × ((List Bool × List Bool) × List (List Bool)) =>
      (q.2.1.1.length == q.1.1) && !q.2.2.contains q.2.1.1 &&
        verify S depth (encPair encUnary encBits (q.1.1, q.1.2.1)) q.2.1.1 q.2.1.2)
    fun q => by
      have hc : q.2.2.contains q.2.1.1 = q.2.2.any (fun b => b == q.2.1.1) :=
        Bool.eq_iff_iff.mpr (by
          simp only [List.contains_iff_mem, List.any_eq_true, beq_iff_eq, exists_eq_right])
      exact congrArg encBool (by dsimp only; rw [hc])
  exact (isOraclePPTOn_nodeKeyO ComputableInPolyTime.id' (.const [])).bind_with
    (hrun.bind_with hpost.isOraclePPTOn)

end Bounds

private theorem exists_seeded_bounds :
    ∃ ck dk cb db cs ds cB dB : ℕ,
      (∀ n coins, (encPair encBits encBits (T.keyGenWith n coins)).length ≤
        ck * ((encPair encUnary encBits (n, coins)).length + 1) ^ dk) ∧
      (∀ n, T.keyGenBudget n ≤ cb * (n + 1) ^ db) ∧
      (∀ sk u msg coins, (T.signWith sk u msg coins).length ≤
        cs * ((encPair (encPair encBits (encPair encUnary encBits)) encBits
          ((sk, u, msg), coins)).length + 1) ^ ds) ∧
      (∀ sk u msg, T.signBudget sk u msg ≤
        cB * ((encPair encBits (encPair encUnary encBits) (sk, u, msg)).length + 1) ^ dB) := by
  obtain ⟨ck, dk, hkg⟩ := T.keyGenWith_polyTime.polyBounded_length.exists_le
  obtain ⟨cb, db, hkb⟩ := T.keyGenBudget_polyTime.polyBounded_length.exists_le
  obtain ⟨cs, ds, hsg⟩ := T.signWith_polyTime.polyBounded_length.exists_le
  obtain ⟨cB, dB, hsb⟩ := T.signBudget_polyTime.polyBounded_length.exists_le
  simp only [encUnary_apply, List.length_replicate] at hkb hsb
  exact ⟨ck, dk, cb, db, cs, ds, cB, dB, fun n coins => hkg (n, coins), hkb,
    fun sk u msg coins => hsg ((sk, u, msg), coins), fun sk u msg => hsb (sk, u, msg)⟩

/-- Certifying the chain to a leaf's parent is uniformly strict oracle PPT in `(n, leaf)`. -/
theorem isOraclePPTOn_certifyO (hdepth : ComputableInPolyTime depth encUnary encUnary) :
    IsOraclePPTOn (encPair encUnary encBits) encCertState
      (fun p : ℕ × List Bool => certifyO S T depth p.1 p.2) := by
  obtain ⟨_, _, _, _, _, _, _, _, hkg, hkb, hsg, hsb⟩ := exists_seeded_bounds (T := T)
  exact (isOraclePPTOn_certifyO_aux hkg hkb hsg hsb hdepth).1

/-- The oracle signer is uniformly strict oracle PPT in `(n, msg)`. -/
theorem isOraclePPTOn_signO (hdepth : ComputableInPolyTime depth encUnary encUnary) :
    IsOraclePPTOn (encPair encUnary encBits) encBits
      (fun p : ℕ × List Bool => signO S T depth p.1 p.2) := by
  obtain ⟨_, _, _, _, _, _, _, _, hkg, hkb, hsg, hsb⟩ := exists_seeded_bounds (T := T)
  exact (isOraclePPTOn_signO_aux hkg hkb hsg hsb hdepth).1

/-- The simulated tree game is uniformly strict oracle PPT in the unary parameter for every
oracle-PPT forger. -/
theorem isOraclePPTOn_simulateTreeGame (hdepth : ComputableInPolyTime depth encUnary encUnary)
    {adversary : Forger} (hA : IsOraclePPT (encPair encBits encBits) adversary) :
    IsOraclePPTOn encUnary encBool (fun n => simulateTreeGame S T depth adversary n) := by
  obtain ⟨_, _, _, _, _, _, _, _, hkg, hkb, hsg, hsb⟩ := exists_seeded_bounds (T := T)
  exact isOraclePPTOn_simulateTreeGame_aux hkg hkb hsg hsb hdepth hA

/-- The coin adversary is uniformly strict oracle PPT: the seeded algorithms' certificates supply
the polynomial bounds. -/
theorem isOraclePPT_treeCoinAdversary (hdepth : ComputableInPolyTime depth encUnary encUnary)
    (hN : ComputableInPolyTime N encUnary encUnary) {inv : ℕ → ℕ}
    (hinvPoly : ComputableInPolyTime inv encUnary encUnary) {adversary : Forger}
    (hA : IsOraclePPT (encPair encBits encBits) adversary) :
    IsOraclePPT encBool (treeCoinAdversary S T depth N inv adversary) := by
  have hsim := isOraclePPTOn_simulateTreeGame (S := S) (T := T) hdepth hA
  have hin := ComputableInPolyTime.id' (encIn := encPair encUnary encBits)
  have hinv1 := (hinvPoly.comp' hin.fst').of_enc_eq fun _ => rfl
  refine IsOraclePPTOn.isOraclePPT ?_
  unfold treeCoinAdversary
  exact IsOraclePPTOn.ite' (condition := fun input : ℕ × List Bool => N (inv input.1) = input.1)
    (((hN.comp' hinv1).decide_eq' hin.fst').of_enc_eq fun _ => rfl)
    (hsim.preprocess' hinv1)
    (ComputableInPolyTime.isOraclePPTOn (ComputableInPolyTime.const false))

end Efficiency

/-! ### Injective parameter schedule above any coin budget -/

/-- Pair `n` with `budget n + 1` to obtain an injective PRF parameter schedule satisfying
`n ≤ coinParam budget n` and `budget n < coinParam budget n`, without assuming `budget` is
monotone. -/
@[expose] def coinParam (budget : ℕ → ℕ) (n : ℕ) : ℕ :=
  Nat.pair n (budget n + 1)

/-- Bounded-search left inverse of `coinParam budget`. -/
@[expose] def coinParamInv (budget : ℕ → ℕ) (M : ℕ) : ℕ :=
  Nat.findGreatest (fun k => coinParam budget k = M) M

theorem le_coinParam (budget : ℕ → ℕ) (n : ℕ) : n ≤ coinParam budget n :=
  Nat.left_le_pair n (budget n + 1)

theorem lt_coinParam (budget : ℕ → ℕ) (n : ℕ) : budget n < coinParam budget n :=
  Nat.lt_of_lt_of_le (Nat.lt_succ_self (budget n)) (Nat.right_le_pair n (budget n + 1))

theorem coinParam_injective (budget : ℕ → ℕ) : Function.Injective (coinParam budget) := by
  intro n m h
  have hpair := congrArg (Prod.fst ∘ Nat.unpair) h
  simpa only [Function.comp_apply, coinParam, Nat.unpair_pair] using hpair

@[simp]
theorem coinParamInv_coinParam (budget : ℕ → ℕ) (n : ℕ) :
    coinParamInv budget (coinParam budget n) = n := by
  apply le_antisymm
  · by_contra! hlt
    have hspec : coinParam budget (coinParamInv budget (coinParam budget n)) =
        coinParam budget n :=
      Nat.findGreatest_spec (P := fun k => coinParam budget k = coinParam budget n)
        (le_coinParam budget n) rfl
    exact hlt.ne' (coinParam_injective budget hspec)
  · exact Nat.le_findGreatest (le_coinParam budget n) rfl

theorem computableInPolyTime_coinParam {budget : ℕ → ℕ}
    (hbudget : ComputableInPolyTime budget encUnary encUnary) :
    ComputableInPolyTime (coinParam budget) encUnary encUnary :=
  ComputableTidilyInPolyTime.unary_pair.computableInPolyTime.comp
    (ComputableInPolyTime.id'.prod (hbudget.unary_add' (.const 1)))

theorem computableInPolyTime_coinParamInv {budget : ℕ → ℕ}
    (hbudget : ComputableInPolyTime budget encUnary encUnary) :
    ComputableInPolyTime (coinParamInv budget) encUnary encUnary := by
  have hparam := computableInPolyTime_coinParam hbudget
  unfold coinParamInv
  exact ComputableInPolyTime.findGreatest ComputableInPolyTime.id'
    ((hparam.comp (.snd' .id')).decide_eq' (.fst' .id'))

/-! ### The hybrid, with a negligible error -/

/-- **Pseudorandom coins may be replaced by random coins**: for a pseudorandom function, an
oracle-PPT forger, polynomial-time `depth`, `N` with `n ≤ N n` and a polynomial-time left
inverse `inv` of `N`, the forging probability against the tree scheme with coins `prfCoins family`
exceeds the forging probability with random coins by a negligible function. -/
theorem exists_negligible_treeGame_le {family : List Bool → List Bool → List Bool}
    (hF : PseudorandomFunction family) (hdepth : ComputableInPolyTime depth encUnary encUnary)
    (hN : ComputableInPolyTime N encUnary encUnary) (hNge : ∀ n, n ≤ N n) {inv : ℕ → ℕ}
    (hinvPoly : ComputableInPolyTime inv encUnary encUnary) (hinv : ∀ n, inv (N n) = n)
    {adversary : Forger} (hA : IsOraclePPT (encPair encBits encBits) adversary) :
    ∃ ε : ℕ → ℝ≥0, Negligible ε ∧ ∀ n,
      Game.succProbability (ProbComp.eval (treeGame S T depth N (prfCoins family) adversary n)) ≤
        Game.succProbability (ProbComp.eval (treeIdealGame S T depth N adversary n)) + ε n :=
  ⟨_, negligible_advantage_treeCoinAdversary family hF hNge
    (isOraclePPT_treeCoinAdversary hdepth hN hinvPoly hA),
    fun n => succProbability_treeGame_le family hinv adversary n⟩

/-- **Pseudorandom coins at `coinParam budget`**: for any polynomial-time unary `budget`,
instantiating the PRF parameter at `coinParam budget` replaces `prfCoins family` with random
function coins up to a negligible error, with no separate left-inverse hypothesis. -/
theorem exists_negligible_treeGame_coinParam_le {family : List Bool → List Bool → List Bool}
    (hF : PseudorandomFunction family) (hdepth : ComputableInPolyTime depth encUnary encUnary)
    {budget : ℕ → ℕ} (hbudget : ComputableInPolyTime budget encUnary encUnary)
    {adversary : Forger} (hA : IsOraclePPT (encPair encBits encBits) adversary) :
    ∃ ε : ℕ → ℝ≥0, Negligible ε ∧ ∀ n,
      Game.succProbability (ProbComp.eval
        (treeGame S T depth (coinParam budget) (prfCoins family) adversary n)) ≤
        Game.succProbability (ProbComp.eval
          (treeIdealGame S T depth (coinParam budget) adversary n)) + ε n :=
  exists_negligible_treeGame_le S T depth (coinParam budget) hF hdepth
    (computableInPolyTime_coinParam hbudget) (le_coinParam budget)
    (computableInPolyTime_coinParamInv hbudget) (coinParamInv_coinParam budget) hA

end TreeSignature

end Cslib.Crypto
