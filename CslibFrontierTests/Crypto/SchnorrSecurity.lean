/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Crypto.Computational.SchnorrSignature.Security
import CslibFrontier.Crypto.Computational.DiscreteLog.SchnorrGroup
import CslibFrontier.Crypto.Negligible.Dyadic
import Mathlib.Tactic.NormNum.Prime

/-!
# Schnorr security clients

An ordinary `module` client of Schnorr EUF-CMA security under discrete log.

Check the extraction step of the two-pass forking adversary in the order-11 subgroup modulo `23`:
it extracts only when the first pass names a query, the second pass names the same query, and the
two answers there differ; and then it outputs `(c - c')⁻¹ (z - z')` modulo the group order.

Then apply `negligible_worldGame_schnorrEncodedROMScheme` to an actual adaptive native forger over
Schnorr groups, with challenge width `n`. The forger's `IsOraclePPT` certificate, the width's
runtime and the negligibility of `2⁻ⁿ` are discharged here. The group family and its bound
`2 ^ n ≤ q` remain hypotheses, as does the discrete-logarithm assumption: no deterministic
polynomial-time family of Schnorr groups with superpolynomial order is constructed in the library.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.Crypto.SchnorrSecurity

open Cslib Cslib.Probability Cslib.Crypto Cslib.Crypto.PrimeOrderGroupFamily
open Cslib.Crypto.Protocols.ROMSignature Turing.MultiTapeTM

private def d23 : schnorrGroups.Desc :=
  ⟨(23, 11, 2), ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩⟩

private def answers : List (List Bool) := [[true], [false]]

private def answers' : List (List Bool) := [[false], [false]]

-- Distinct answers at query `0`, challenges `1` and `0`, responses `3` and `1`:
-- the witness is `(1 - 0)⁻¹ (3 - 1) = 2` modulo `11`.
example : schnorrGroups.schnorrForkOutput d23 answers answers' (1, [true], [true, true])
    (1, [false], [true]) = [false, true] := by
  decide

-- No named query: nothing is extracted.
example : schnorrGroups.schnorrForkOutput d23 answers answers' (0, [true], [true, true])
    (1, [false], [true]) = [] := by
  decide

-- The second pass names another query: nothing is extracted.
example : schnorrGroups.schnorrForkOutput d23 answers answers' (1, [true], [true, true])
    (2, [false], [true]) = [] := by
  decide

-- Equal answers at the named query: nothing is extracted.
example : schnorrGroups.schnorrForkOutput d23 answers answers' (2, [true], [true, true])
    (2, [false], [true]) = [] := by
  decide

/-- An adaptive native forger. It makes two signing requests on the empty message, hashes the
first bit of the first signature, and outputs the first three digest bits as its message with
that bit as its signature. -/
private def nativeForger (_ : ℕ) (_ : List Bool) :
    WordOracleComp Bool (List Bool × List Bool) := do
  let sig ← List.take 1 <$> ProbOracleComp.query (false, [])
  let _ ← List.take 1 <$> ProbOracleComp.query (false, [])
  let digest ← List.take 3 <$> ProbOracleComp.query (true, sig)
  return (digest, sig)

private theorem nativeForger_ppt : IsOraclePPT (encPair encBits encBits) nativeForger := by
  unfold IsOraclePPT nativeForger
  apply IsOraclePPTOn.bind_with (middle := encBits)
  · fun_prop
  apply IsOraclePPTOn.bind_with (middle := encBits)
  · fun_prop
  apply IsOraclePPTOn.bind_with (middle := encBits)
  · fun_prop
  fun_prop

-- Over any polynomial-time family of Schnorr groups of order at least `2 ^ n` on which discrete
-- logarithms are hard, this forger wins the native EUF-CMA game with `n`-bit challenges, actual
-- keys and actual nonces with negligible probability.
example (description : ℕ → schnorrGroups.Desc)
    (hdescription : ComputableInPolyTime description encUnary schnorrGroups.encDesc)
    (hwq : ∀ n, 2 ^ n ≤ schnorrGroups.order (description n))
    (hDL : schnorrGroups.DiscreteLog fun n => PMF.pure (description n)) :
    Negligible fun n => Game.succProbability
      (worldGame (schnorrGroups.schnorrEncodedROMScheme (description n) n
          (ProbComp.eval (schnorrGroups.schnorrSigKeyGen n (description n)))
          ((ProbComp.eval (schnorrGroups.sampleExp n (description n))).map Nat.cast))
        (fun pk => routeWordProgram (⟨List.ofFn, List.ofFn_injective⟩ : BitString n ↪ List Bool)
          (nativeForger n pk))
        (fun verified ⟨msg, _⟩ pairs => verified && !(pairs.map Prod.fst).contains msg)) :=
  schnorrGroups.negligible_worldGame_schnorrEncodedROMScheme description hdescription
    (width := fun n => n) (by fun_prop) hwq negligible_one_div_two_pow hDL nativeForger_ppt

end CslibFrontierTests.Crypto.SchnorrSecurity
