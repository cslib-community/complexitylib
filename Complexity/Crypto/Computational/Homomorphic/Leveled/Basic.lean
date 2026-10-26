/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.Layered.Compile
public import Complexity.Computability.Circuit.Boolean.Layered.Padding
public import Complexity.Crypto.Computational.Homomorphic.KeyChain
public import Complexity.Crypto.Computational.Homomorphic.Layered
public import Complexity.Crypto.Computational.Homomorphic.Leveled.Encoding

/-!
# A depth-budgeted homomorphic scheme

For a depth budget `B`, generate `2 * B + 1` independent base keys and encrypt each secret
under the next public key. Evaluation compiles the circuit and pads its schedule with identity
refresh layers to exactly `2 * B` transitions. All permitted circuits therefore end at the same
final key, including circuits with no gates. Output selection requires no further transition.

The public artifact contains only public keys and encrypted links. The private artifact contains
the two endpoint secrets. A leading ciphertext bit selects the initial secret for fresh
encryptions and the final secret for evaluated ciphertexts. This adapts Gentry's leveled
construction to `Scheme.Correct`, which requires the same decryption algorithm for both forms.
The tag does not claim to hide whether a ciphertext is fresh or evaluated. There is no encrypted
link from the final key back to the initial key.

All algorithms are total. Decryption executes the supplied decryption circuit on a padded or
truncated input, rather than relying on unspecified behavior of the base decryption algorithm
on malformed words. Correctness, native efficiency and security are separate obligations.

The scheme evaluator `(scheme D budget).evaluate` remains single-hop: it starts at the initial
public key and pads to `2 * budget n` transitions. Multi-hop evaluation goes through
`evaluateHop`, which starts at an explicit depth offset `offset` along the public key chain and
evaluates a circuit of depth at most `step`, with the caller tracking the offsets. Only a hop
ending at `offset + step = budget n` produces a ciphertext that `(scheme D budget).decrypt` can
decrypt, because the private artifact retains only the two endpoint secrets (`0` and
`2 * budget n`). A hop ending before `budget n` (including a depth-zero wiring hop at an
intermediate offset) produces a `true`-tagged ciphertext under key `2 * (offset + step)` that
`(scheme D budget).decrypt` cannot decrypt.

This level-indexed hop API is an original adaptation, closest to Gentry's sub-scheme `E^(δ)`
([Gentry2009], Section 2, p. 171). GHV is cited for the multi-hop notion (paraphrase: evaluation
can be applied to its own outputs) [GentryHaleviVaikuntanathan2010]; that notion is not claimed
for the fixed-start scheme evaluator `(scheme D budget).evaluate` itself.

## Main definitions

* `Cslib.Crypto.Homomorphic.Leveled.keyPair`: serialize the public and private artifacts.
* `Cslib.Crypto.Homomorphic.Leveled.evaluateCircuit`: pad and evaluate a raw circuit schedule.
* `Cslib.Crypto.Homomorphic.Leveled.evaluateHop`: evaluate one depth-bounded hop starting at an
  offset along the public key chain.
* `Cslib.Crypto.Homomorphic.Leveled.scheme`: the actual depth-budgeted encryption scheme.

## References

* [C. Gentry, *Fully homomorphic encryption using ideal lattices*, Section 2,
  pp. 171--172][Gentry2009]
* [C. Gentry, S. Halevi, and V. Vaikuntanathan, *$i$-Hop Homomorphic Encryption and
  Rerandomizable Yao Circuits*][GentryHaleviVaikuntanathan2010]
-/

@[expose] public section

namespace Cslib.Crypto.Homomorphic.Leveled

open Circuits Circuits.Boolean

/-- Public keys and encrypted links are public; only the endpoint secrets are retained privately.
The intermediate secrets used to construct the links are omitted from both artifacts. -/
def keyPair (depth : ℕ) (keys : List (List Bool × List Bool))
    (links : List (List (List Bool))) : List Bool × List Bool :=
  (encPublicKey (keys.map Prod.fst, links),
    encSecretKey ((keys.getD 0 ([], [])).2, (keys.getD depth ([], [])).2))

/-- Sample the actual acyclic chain and serialize its public and private projections. -/
def keyGen (E : Scheme) (n budget : ℕ) : ProbComp (List Bool × List Bool) :=
  (fun chain => keyPair (2 * budget) chain.1 chain.2) <$>
    E.generateKeyChain n (2 * budget)

/-- A fresh ciphertext contains a false tag and an encryption under the initial public key. -/
def encrypt (E : Scheme) (n : ℕ) (pk : List Bool) (bit : Bool) : ProbComp (List Bool) :=
  List.cons false <$> E.encrypt n ((publicKeyDecoder.decode pk).1.getD 0 []) bit

variable {E : Scheme} {secretWidth ciphertextWidth : ℕ → ℕ}
  (D : DecryptionCircuits E secretWidth ciphertextWidth)

/-- Execute the certified decryption circuit with the endpoint selected by the tag. This
algorithm is independent of the depth budget, including on malformed keys and ciphertexts. -/
def decrypt (n : ℕ) (sk ciphertext : List Bool) : Bool :=
  let endpoints := secretKeyDecoder.decode sk
  let secret := if ciphertext.headD false then endpoints.2 else endpoints.1
  (D.circuit n).eval interpretation
    (BitString.ofList (secretWidth n + ciphertextWidth n) (secret ++ ciphertext.tail)) 0

/-- Compile, pad with identity refreshes, evaluate, and select the original ordered outputs.
`publicKeys` starts with the first target key, omitting the initial input-encryption key.
For an over-budget raw code, `padTo` retains the full compiled schedule; no correctness claim
is made for such inputs. -/
def evaluateCircuit (n budget : ℕ) (publicKeys : List (List Bool))
    (links : List (List (List Bool))) (inputs : List (List Bool))
    (inputCount : ℕ) (code : List (Op × List ℕ) × List ℕ) : ProbComp (List (List Bool)) :=
  let compiled := Layered.compile inputCount code
  let layers := Layered.padTo inputCount (2 * budget) compiled.1
  (fun row => compiled.2.map (row.getD · [])) <$>
    Scheme.evaluateLayers D n publicKeys links inputs layers

/-- Original level-indexed adaptation: strip tags and evaluate a step-bounded circuit starting
at depth offset `offset` along the
public key chain (`2 * offset` layer transitions into the public artifact), and tag the result
with `true`. The scheme evaluator `(scheme D budget).evaluate` remains single-hop; multi-hop
evaluation goes through `evaluateHop`, and the caller tracks the offsets. Only a hop that ends at
`budget n` (`offset + step = budget n`) yields a ciphertext that `(scheme D budget).decrypt` can
decrypt, because the private artifact holds only the two endpoint secrets (`0` and `2 * budget n`).
A hop ending before `budget n` (including a depth-zero wiring hop at an intermediate offset)
produces a `true`-tagged ciphertext under an intermediate key that `(scheme D budget).decrypt`
cannot decrypt. -/
def evaluateHop (n offset step : ℕ) (pk : List Bool) (c : Σ m, Circuit signature m 1)
    (inputs : List (List Bool)) : ProbComp (List Bool) :=
  let artifact := publicKeyDecoder.decode pk
  (fun row => true :: row.headD []) <$>
    evaluateCircuit D n step (artifact.1.tail.drop (2 * offset)) (artifact.2.drop (2 * offset))
      (inputs.map List.tail) c.1 c.2.code

/-- Strip fresh tags, evaluate the padded circuit under the public chain, and tag the result
for the final endpoint secret. The correctness contract takes fresh encryptions as inputs. -/
def evaluate (n budget : ℕ) (pk : List Bool) (c : Σ m, Circuit signature m 1)
    (inputs : List (List Bool)) : ProbComp (List Bool) :=
  let artifact := publicKeyDecoder.decode pk
  (fun row => true :: row.headD []) <$>
    evaluateCircuit D n budget artifact.1.tail artifact.2 (inputs.map List.tail) c.1 c.2.code

/-- At zero offset, hop evaluation coincides with the single-hop evaluator. -/
@[simp]
theorem evaluateHop_zero (n budget : ℕ) (pk : List Bool) (c : Σ m, Circuit signature m 1)
    (inputs : List (List Bool)) :
    evaluateHop D n 0 budget pk c inputs = evaluate D n budget pk c inputs :=
  rfl

/-- The depth-budgeted scheme. Efficiency of the budget family is a separate hypothesis for
the uniform runtime certificates. No correctness or runtime conclusion is bundled as input. -/
def scheme (budget : ℕ → ℕ) : Scheme where
  keyGen n := keyGen E n (budget n)
  encrypt := encrypt E
  decrypt := decrypt D
  evaluate n := evaluate D n (budget n)
  permitted n c := c.2.depth ≤ budget n

end Cslib.Crypto.Homomorphic.Leveled
