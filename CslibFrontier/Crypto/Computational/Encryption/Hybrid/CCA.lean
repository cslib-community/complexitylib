/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.Encryption.Hybrid
public import CslibFrontier.Crypto.Computational.Encryption.CCA
public import CslibFrontier.Crypto.Computational.PseudorandomFunction
import CslibFrontier.Languages.Probabilistic.Norm

/-!
# Adaptive decapsulation experiments

The KEM experiments of [BonehShoup2023], Exercise 12.5, reuse the real and ideal sampling
continuations of `Hybrid`. After receiving `(pk, (shownKey, ct))`, the adversary may make adaptive
decapsulation queries. The existing `cca2Phase2Oracle` rejects the exact challenge word in both
worlds and encodes every other `Option` reply, distinguishing rejection from an empty key.
There is no prechallenge decapsulation phase or additional challenge encapsulation.

Security is expressed with the existing `Game.Indistinguishable` and `IsOraclePPT` predicates;
these experiments introduce no new adversary or security structure. They specialize to the
existing CPA games for adversaries that only sample closed programs.

## Main definitions

* `Cslib.Crypto.Encryption.kemCCAContinuation`: interpret the postchallenge adversary.
* `Cslib.Crypto.Encryption.kemCCARealGame`: the encapsulated key is shown.
* `Cslib.Crypto.Encryption.kemCCAIdealGame`: an independent uniform key is shown.

## Main results

* `Cslib.Crypto.Encryption.eval_kemCCARealGame_sample`: recover the real CPA game.
* `Cslib.Crypto.Encryption.eval_kemCCAIdealGame_sample`: recover the ideal CPA game.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Exercise 12.5, pp. 513–514.
-/

@[expose] public section

namespace Cslib.Crypto.Encryption

open Probability Turing.MultiTapeTM

/-- Interpret a KEM distinguisher using the existing challenge-rejecting decryption oracle.
Only the encoded public key, shown key and challenge ciphertext are passed to the adversary;
`sk` remains internal to the challenger. -/
def kemCCAContinuation (decaps : ℕ → List Bool → List Bool → Option (List Bool))
    (distinguisher : OracleDistinguisher) (n : ℕ) (sk pk k ct : List Bool) : ProbComp Bool := do
  let result ← (OracleComp.interpret
    (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m))
      (cca2Phase2Oracle encBits decaps n sk ct))
    (distinguisher n (encPair encBits (encPair encBits encBits) (pk, (k, ct))))).run ()
  return result.1

/-- Real KEM experiment with adaptive postchallenge decapsulation queries. -/
def kemCCARealGame (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encaps : ℕ → List Bool → ProbComp (List Bool × List Bool))
    (decaps : ℕ → List Bool → List Bool → Option (List Bool))
    (distinguisher : OracleDistinguisher) (n : ℕ) : ProbComp Bool :=
  kemRealGameWith keyGen encaps (kemCCAContinuation decaps distinguisher) n

/-- Ideal KEM experiment: replace only the shown key; the decapsulation oracle uses the same
secret key and excludes the same challenge ciphertext as the real experiment. -/
noncomputable def kemCCAIdealGame (keyLen : ℕ → ℕ)
    (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encaps : ℕ → List Bool → ProbComp (List Bool × List Bool))
    (decaps : ℕ → List Bool → List Bool → Option (List Bool))
    (distinguisher : OracleDistinguisher) (n : ℕ) : ProbComp Bool :=
  kemIdealGameWith keyLen keyGen encaps (kemCCAContinuation decaps distinguisher) n

/-- A closed distinguisher ignores the decapsulation oracle, recovering the real CPA game. -/
theorem eval_kemCCARealGame_sample (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encaps : ℕ → List Bool → ProbComp (List Bool × List Bool))
    (decaps : ℕ → List Bool → List Bool → Option (List Bool))
    (distinguisher : Distinguisher) (n : ℕ) :
    ProbComp.eval (kemCCARealGame keyGen encaps decaps
      (fun n input => ProbOracleComp.sample (distinguisher n input)) n) =
      ProbComp.eval (kemRealGame keyGen encaps distinguisher n) := by
  simp only [pmf_norm, kemCCARealGame, kemRealGame, kemRealGameWith, kemCCAContinuation,
    ProbOracleComp.eval_run_interpret, ProbOracleComp.run_interpret_sample]

/-- A closed distinguisher ignores the decapsulation oracle, recovering the ideal CPA game. -/
theorem eval_kemCCAIdealGame_sample (keyLen : ℕ → ℕ)
    (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encaps : ℕ → List Bool → ProbComp (List Bool × List Bool))
    (decaps : ℕ → List Bool → List Bool → Option (List Bool))
    (distinguisher : Distinguisher) (n : ℕ) :
    ProbComp.eval (kemCCAIdealGame keyLen keyGen encaps decaps
      (fun n input => ProbOracleComp.sample (distinguisher n input)) n) =
      ProbComp.eval (kemIdealGame keyLen keyGen encaps distinguisher n) := by
  simp only [pmf_norm, kemCCAIdealGame, kemIdealGame, kemIdealGameWith, kemRealGameWith,
    kemCCAContinuation, ProbOracleComp.eval_run_interpret, ProbOracleComp.run_interpret_sample]

end Cslib.Crypto.Encryption
