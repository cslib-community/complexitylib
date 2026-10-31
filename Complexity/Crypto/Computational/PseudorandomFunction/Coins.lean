/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.PseudorandomFunction
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Decoder
import Complexity.Computability.Probabilistic.Oracle.Composition
import Complexity.Computability.Probabilistic.Oracle.Substitution
import Complexity.Languages.Probabilistic.Oracle.Simulation
import Complexity.Languages.Probabilistic.Oracle.Support
import Complexity.Probability.PMF.Bind
import Complexity.Tactic.PolyTime
import Complexity.Tactic.PPT

/-!
# Pseudorandom coins from a pseudorandom function

A pseudorandom function with `N`-bit keys, inputs and outputs supplies up to `N` pseudorandom
coins for every short request word: pad the request prefix-freely to `N` bits (`padRequest`),
evaluate, and keep the requested number of bits (`prfCoins`). Distinct requests of length below
`N` pad to distinct inputs, so in the ideal world they receive independent uniform coins, and a
repeated request receives the same coins. This is the coin source of stateless tree signatures
([BonehShoup2023], Section 14.6.2, "Generating internal keys using a PRF"), where `N` is a
polynomial in the signature scheme's parameter chosen above every coin budget.

The coin games `coinRealGame` and `coinIdealGame` let an adversary request `(x, L)` and answer with
`prfCoins family k x L` under a uniform key, or with the first `L` bits of a uniform random
function at `padRequest N x`. The reduction `coinDistinguisher` forwards each request padded and
truncates the reply, so both games are exactly the PRF games of the forwarded adversary
(`eval_coinRealGame`, `eval_coinIdealGame`), and a pseudorandom function makes the coin games
indistinguishable (`PseudorandomFunction.coinIndistinguishable`).

## Main definitions

* `Cslib.Crypto.padRequest`, `Cslib.Crypto.prfCoins`: the padding and the coins.
* `Cslib.Crypto.coinRequestDecoder`, `Cslib.Crypto.coinRealGame`, `Cslib.Crypto.coinIdealGame`:
  the coin games.
* `Cslib.Crypto.coinDistinguisher`: the reduction to the PRF games.

## Main results

* `Cslib.Crypto.length_padRequest`, `Cslib.Crypto.padRequest_injective`,
  `Cslib.Crypto.length_prfCoins`, `Cslib.Crypto.computableInPolyTime_prfCoins`: the coins have
  the requested length, come from distinct inputs for distinct short requests, and are computable
  in polynomial time.
* `Cslib.Crypto.eval_coinRealGame`, `Cslib.Crypto.eval_coinIdealGame`,
  `Cslib.Crypto.isOraclePPT_coinDistinguisher`: the exact reduction and its efficiency.
* `Cslib.Crypto.PseudorandomFunction.coinIndistinguishable`: the coin games are
  indistinguishable for every oracle-PPT adversary.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023],
  Section 14.6.2.
-/

@[expose] public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM
open scoped NNReal

/-! ### Padding and coins -/

/-- Pad a request to exactly `w` bits: the request, a `true`, then `false`s, cut at `w` bits.
Requests shorter than `w` pad injectively. -/
def padRequest (w : ℕ) (x : List Bool) : List Bool := (x ++ true :: List.replicate w false).take w

@[simp]
theorem length_padRequest (w : ℕ) (x : List Bool) : (padRequest w x).length = w := by
  simp only [padRequest, List.length_take, List.length_append, List.length_cons,
    List.length_replicate]
  omega

/-- A request shorter than the width pads to the request, a `true` and `false`s. -/
theorem padRequest_of_lt {w : ℕ} {x : List Bool} (hx : x.length < w) :
    padRequest w x = x ++ true :: List.replicate (w - x.length - 1) false := by
  simp only [padRequest]
  rw [List.take_append, List.take_of_length_le hx.le,
    show w - x.length = (w - x.length - 1) + 1 by omega, List.take_succ_cons, List.take_replicate]
  congr 3
  omega

/-- Strip the padding: drop the trailing `false`s and the `true` before them. -/
def unpadRequest (p : List Bool) : List Bool := (p.reverse.dropWhile (· == false)).tail.reverse

theorem unpadRequest_padRequest {w : ℕ} {x : List Bool} (hx : x.length < w) :
    unpadRequest (padRequest w x) = x := by
  rw [padRequest_of_lt hx]
  simp [unpadRequest]

/-- Distinct requests shorter than the width pad to distinct words. -/
theorem padRequest_injective {w : ℕ} {x y : List Bool} (hx : x.length < w) (hy : y.length < w)
    (h : padRequest w x = padRequest w y) : x = y := by
  rw [← unpadRequest_padRequest hx, h, unpadRequest_padRequest hy]

/-- `L` coins for the request `x` from the key `k`: the family at the request padded to the key's
length, cut to `L` bits. -/
def prfCoins (family : List Bool → List Bool → List Bool) (k x : List Bool) (L : ℕ) :
    List Bool :=
  (family k (padRequest k.length x)).take L

/-- The coins have the requested length when it is at most the key length. -/
theorem length_prfCoins {family : List Bool → List Bool → List Bool}
    (hlen : ∀ key query, query.length = key.length → (family key query).length = key.length)
    (k x : List Bool) {L : ℕ} (hL : L ≤ k.length) : (prfCoins family k x L).length = L := by
  simp only [prfCoins, List.length_take, hlen k _ (length_padRequest _ _)]
  omega

/-- The coins are computable in polynomial time from the key, the request and the unary count. -/
theorem computableInPolyTime_prfCoins {family : List Bool → List Bool → List Bool}
    (hF : ComputableInPolyTime (fun p : List Bool × List Bool => family p.1 p.2)
      (encPair encBits encBits) encBits) :
    ComputableInPolyTime (fun p : List Bool × List Bool × ℕ => prfCoins family p.1 p.2.1 p.2.2)
      (encPair encBits (encPair encBits encUnary)) encBits := by
  unfold prfCoins padRequest
  polytime

/-! ### The coin games -/

/-- A coin request word `encPair encBits encUnary (x, L)`: the request `x` and the number `L` of
coins; `requestDecoder`-style, every word decodes to some pair. -/
def coinRequestDecoder : Decoder (encPair encBits encUnary) := Decoder.bits.pair Decoder.unary

variable (family : List Bool → List Bool → List Bool)

/-- The real coin oracle: `prfCoins` under the key, on the decoded request. -/
def coinOracle (k request : List Bool) : List Bool :=
  prfCoins family k (coinRequestDecoder.decode request).1 (coinRequestDecoder.decode request).2

/-- The ideal coin oracle: the random function at the padded request, cut to the count. -/
def randomCoinOracle (N : ℕ) (table : BitString N → BitString N) (request : List Bool) :
    List Bool :=
  (randomFunctionOracle N table (padRequest N (coinRequestDecoder.decode request).1)).take
    (coinRequestDecoder.decode request).2

/-- The real coin game: a uniform `N`-bit key answers every request with `prfCoins`. -/
noncomputable def coinRealGame (adversary : OracleDistinguisher) (N : ℕ) : ProbComp Bool := do
  let key ← BitString.sampleList N
  OracleComp.interpret
    (ProbOracleComp.handler ProbComp.unifFin (fun request =>
      pure (coinOracle family key request.2))) (adversary N [])

/-- The ideal coin game: a uniform random function on `N` bits answers every request at its
padding, cut to the requested count. -/
noncomputable def coinIdealGame (adversary : OracleDistinguisher) (N : ℕ) : ProbComp Bool := do
  let table ← ProbComp.uniform (BitString N → BitString N)
  OracleComp.interpret
    (ProbOracleComp.handler ProbComp.unifFin (fun request =>
      pure (randomCoinOracle N table request.2))) (adversary N [])

/-! ### The reduction to the PRF games -/

/-- Forward a coin request to the function oracle at its padding, keeping the requested bits. -/
def coinQuery (N : ℕ) (request : Unit × List Bool) : WordOracleComp Unit (List Bool) :=
  List.take (coinRequestDecoder.decode request.2).2 <$>
    ProbOracleComp.query ((), padRequest N (coinRequestDecoder.decode request.2).1)

/-- The PRF distinguisher built from a coin adversary: run it, answering through `coinQuery`. -/
def coinDistinguisher (adversary : OracleDistinguisher) : OracleDistinguisher := fun N aux =>
  OracleComp.interpret
    (ProbOracleComp.handler (fun k => ProbOracleComp.sample (ProbComp.unifFin k)) (coinQuery N))
    (adversary N aux)

/-- Interpreting the forwarded program against a stateless word oracle is interpreting the
original program against that oracle composed with `coinQuery`. -/
private theorem interpret_coinDistinguisher (oracle : Unit × List Bool → ProbComp (List Bool))
    (adversary : OracleDistinguisher) (N : ℕ) (aux : List Bool) :
    OracleComp.interpret (ProbOracleComp.handler ProbComp.unifFin oracle)
      (coinDistinguisher adversary N aux) =
    OracleComp.interpret (ProbOracleComp.handler ProbComp.unifFin (fun request =>
      List.take (coinRequestDecoder.decode request.2).2 <$>
        oracle ((), padRequest N (coinRequestDecoder.decode request.2).1))) (adversary N aux) := by
  simp only [coinDistinguisher, OracleComp.interpret_interpret, ProbOracleComp.interpret_handler,
    ProbOracleComp.interpret_sample, coinQuery, OracleComp.interpret_map,
    ProbOracleComp.interpret_query]
  congr 1

/-- The real coin game is the real PRF game of the forwarded adversary. -/
theorem eval_coinRealGame (adversary : OracleDistinguisher) (N : ℕ) :
    ProbComp.eval (coinRealGame family adversary N) =
      ProbComp.eval (prfRealGame family (coinDistinguisher adversary) N) := by
  simp only [coinRealGame, prfRealGame, ProbComp.eval_bind, BitString.eval_sampleList]
  refine PMF.bind_congr_on_support _ _ _ fun key hkey => ?_
  have hlen := BitString.length_of_mem_support_uniformList hkey
  rw [interpret_coinDistinguisher]
  refine congrArg (fun h => ProbComp.eval (OracleComp.interpret
    (ProbOracleComp.handler ProbComp.unifFin h) (adversary N []))) (funext fun request => ?_)
  simp only [map_pure, coinOracle, prfCoins, prfOracle, length_padRequest, hlen, ite_true]

/-- The ideal coin game is the ideal PRF game of the forwarded adversary. -/
theorem eval_coinIdealGame (adversary : OracleDistinguisher) (N : ℕ) :
    ProbComp.eval (coinIdealGame adversary N) =
      ProbComp.eval (prfIdealGame (coinDistinguisher adversary) N) := by
  simp only [coinIdealGame, prfIdealGame, ProbComp.eval_bind]
  refine PMF.bind_congr_on_support _ _ _ fun table _ => ?_
  rw [interpret_coinDistinguisher]
  refine congrArg (fun h => ProbComp.eval (OracleComp.interpret
    (ProbOracleComp.handler ProbComp.unifFin h) (adversary N []))) (funext fun request => ?_)
  simp only [map_pure, randomCoinOracle]

/-- `coinQuery` as a handler with trivial state, for the open substitution rule. -/
private def coinHandler (N : ℕ) (request : Unit × List Bool) :
    StateT Unit (WordOracleComp Unit) (List Bool) := fun u =>
  (fun reply => (reply, u)) <$> coinQuery N request

/-- The forwarded adversary is uniformly strict oracle PPT whenever the coin adversary is. -/
theorem isOraclePPT_coinDistinguisher {adversary : OracleDistinguisher}
    (hadversary : IsOraclePPT encBool adversary) :
    IsOraclePPT encBool (coinDistinguisher adversary) := by
  have hdecode := coinRequestDecoder.computableInPolyTime
  have hhandler : IsOraclePPTOn
      (encPair (encPair encUnary encBits)
        (encPair (encPair (encFinEnum Unit) encBits) (encFinEnum Unit)))
      (encPair encBits (encFinEnum Unit))
      (fun pair : (ℕ × List Bool) × ((Unit × List Bool) × Unit) =>
        coinHandler pair.1.1 pair.2.1 pair.2.2) := by
    have heq : (fun pair : (ℕ × List Bool) × ((Unit × List Bool) × Unit) =>
        coinHandler pair.1.1 pair.2.1 pair.2.2) = fun pair =>
          (fun reply => (reply, ())) <$>
            (List.take (coinRequestDecoder.decode pair.2.1.2).2 <$>
              ProbOracleComp.query (spec := fun _ : Unit × List Bool => List Bool)
                ((), padRequest pair.1.1 (coinRequestDecoder.decode pair.2.1.2).1)) := by
      funext pair
      obtain ⟨_, _, ⟨⟩⟩ := pair
      rfl
    rw [heq]
    refine (IsOraclePPTOn.query_take' () ?_ ?_).map' ?_
    · unfold padRequest
      polytime
    · polytime
    · polytime
  have hrun := hadversary.run_interpret_preprocess_open' (External := Unit)
    (handler := fun c => coinHandler c.1)
    (prepare := fun c : ℕ × List Bool => c) (initial := fun _ => ())
    (resources := fun _ w => w.length)
    ComputableInPolyTime.id' hhandler (ComputableInPolyTime.const ()) (fun _ _ => True)
    (fun _ => trivial) (by polytime) ?_
  · refine (hrun.map' (ComputableInPolyTime.fst encBool (encFinEnum Unit))).congr
      fun c External oracle e => ?_
    have hlift : ProbOracleComp.handler
        (fun n => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin n)))
        (fun q => coinHandler c.1 q) =
      fun q => StateT.lift (σ := Unit) (ProbOracleComp.handler
        (fun n => ProbOracleComp.sample (ProbComp.unifFin n)) (coinQuery c.1) q) := by
      funext q
      cases q with
      | inl n => rfl
      | inr q =>
        funext u
        exact map_eq_pure_bind _ _
    have h : Prod.fst <$> (OracleComp.interpret
        (ProbOracleComp.handler
          (fun n => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin n)))
          (fun q => coinHandler c.1 q)) (adversary c.1 c.2)).run () =
        coinDistinguisher adversary c.1 c.2 := by
      rw [hlift, OracleComp.run_interpret_lift, Functor.map_map]
      exact id_map _
    rw [h]
  · intro c request u _ result hresult
    obtain ⟨reply, hreply, rfl⟩ := ProbOracleComp.mem_support_map hresult
    obtain ⟨raw, -, rfl⟩ := ProbOracleComp.mem_support_map hreply
    refine ⟨trivial, (List.length_take_le _ _).trans ?_, le_add_right le_rfl⟩
    exact length_dropFrame_le request.2

/-- **A pseudorandom function gives pseudorandom coins**: the real and ideal coin games are
indistinguishable for every oracle-PPT adversary, with the same advantage as the forwarded
adversary's in the PRF games. -/
theorem PseudorandomFunction.coinIndistinguishable {family : List Bool → List Bool → List Bool}
    (hF : PseudorandomFunction family) :
    Game.Indistinguishable (fun adversary N => ProbComp.eval (coinRealGame family adversary N))
      (fun adversary N => ProbComp.eval (coinIdealGame adversary N)) (IsOraclePPT encBool) := by
  intro adversary hadversary
  simpa only [eval_coinRealGame, eval_coinIdealGame] using
    hF.secure (coinDistinguisher adversary) (isOraclePPT_coinDistinguisher hadversary)

end Cslib.Crypto
