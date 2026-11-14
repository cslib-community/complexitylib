/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Crypto.Computational.SchnorrSignature.Security
import CslibFrontier.Crypto.Computational.DiscreteLog.SchnorrGroup
import CslibFrontier.Crypto.Negligible.Dyadic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat.WordsRoundTrip
import CslibFrontier.Foundations.Data.Nat.PolynomialBound.Closure
import Mathlib.NumberTheory.Bertrand
import Mathlib.Tactic.NormNum.Prime

/-!
# Schnorr security clients

An ordinary `module` client of Schnorr EUF-CMA security under discrete log.

Check the extraction step of the two-pass forking adversary in the order-11 subgroup modulo `23`:
it extracts only when the first pass names a query, the second pass names the same query, and the
two answers there differ; and then it outputs `(c - c')⁻¹ (z - z')` modulo the group order.

Then check that `ROMSignature.wordEufCmaGame` and `schnorrNativeROMScheme` only name the existing
shared-oracle game of the native scheme, and apply `DiscreteLog.eufCma_schnorrNativeROMScheme` with
challenge width `n`, and through it to an actual adaptive native forger. The width's runtime, the
negligibility of `2⁻ⁿ` and the forger's `IsOraclePPT` certificate are discharged here.

* Over Schnorr groups, the group family, its polynomial description length and its bound
  `2 ^ n ≤ q` remain hypotheses, as does the discrete-logarithm assumption: the library constructs
  no family of Schnorr groups of order at least `2 ^ n` with polynomial-size parameters.
* Over the additive groups `ZMod p` of primes `2 ^ n < p ≤ 2 ^ (n + 1)` given by Bertrand's
  postulate, every parameter condition is discharged unconditionally, so the discrete-logarithm
  assumption is the only premise left. No algorithm chooses the primes. Discrete logarithms are
  easy in these groups, since `α • 1` is encoded by the residue of `α`, so the assumption fails
  for them. The example shows only that the parameter conditions hold together without any
  conjecture on primes.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.Crypto.SchnorrSecurity

open Cslib Cslib.Probability Cslib.Crypto Cslib.Crypto.PrimeOrderGroupFamily Cslib.Crypto.Protocols
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

-- The names only abbreviate the existing game: the forger's game against the native scheme is,
-- by definition, the shared-oracle game of the encoded scheme with the actual key generator and
-- nonce sampler, the forger routed into it, and final-message freshness.
example (d : schnorrGroups.Desc) (n m : ℕ)
    (forger : List Bool → WordOracleComp Bool (List Bool × List Bool)) :
    wordEufCmaGame (encBitString m) (schnorrGroups.schnorrNativeROMScheme n d m) forger =
      worldGame (schnorrGroups.schnorrEncodedROMScheme d m
          (ProbComp.eval (schnorrGroups.schnorrSigKeyGen n d))
          ((ProbComp.eval (schnorrGroups.sampleExp n d)).map Nat.cast))
        (fun pk => routeWordProgram (⟨List.ofFn, List.ofFn_injective⟩ : BitString m ↪ List Bool)
          (forger pk))
        (fun verified ⟨msg, _⟩ pairs => verified && !(pairs.map Prod.fst).contains msg) :=
  rfl

/-- Over any family of Schnorr groups with polynomial-length parameters and order at least `2 ^ n`
on which discrete logarithms are hard, the native scheme with `n`-bit challenges is EUF-CMA secure
in the random-oracle model. -/
private theorem eufCma_schnorrGroups (description : ℕ → schnorrGroups.Desc)
    (hdescription : PolynomiallyBounded fun n => (schnorrGroups.encDesc (description n)).length)
    (hwq : ∀ n, 2 ^ n ≤ schnorrGroups.order (description n))
    (hDL : schnorrGroups.DiscreteLog fun n => PMF.pure (description n)) :
    ROMSignature.EUFCMA (fun n => encBitString n)
      (fun n => schnorrGroups.schnorrNativeROMScheme n (description n) n) :=
  hDL.eufCma_schnorrNativeROMScheme hdescription (width := fun n => n) (by fun_prop) hwq
    negligible_one_div_two_pow

-- In particular, the adaptive forger above wins with negligible probability.
example (description : ℕ → schnorrGroups.Desc)
    (hdescription : PolynomiallyBounded fun n => (schnorrGroups.encDesc (description n)).length)
    (hwq : ∀ n, 2 ^ n ≤ schnorrGroups.order (description n))
    (hDL : schnorrGroups.DiscreteLog fun n => PMF.pure (description n)) :
    Negligible fun n => Game.succProbability (wordEufCmaGame (encBitString n)
      (schnorrGroups.schnorrNativeROMScheme n (description n) n) (nativeForger n)) :=
  (eufCma_schnorrGroups description hdescription hwq hDL).negligible nativeForger nativeForger_ppt

/-! ### Unconditional parameters: additive groups of Bertrand primes -/

/-- Primes, as public group parameters. -/
private abbrev PrimeDesc : Type := {p : ℕ // p.Prime}

/-- A prime is encoded by its binary digits. -/
private def encPrime : PrimeDesc ↪ List Bool :=
  (Function.Embedding.subtype _).trans encNat

private theorem computableInPolyTime_val :
    ComputableInPolyTime (Subtype.val : PrimeDesc → ℕ) encPrime encNat :=
  ComputableInPolyTime.of_eq fun _ => rfl

/-- Addition modulo `p` of binary residues. -/
private def primeAdd : PrimeDesc × List Bool × List Bool → List Bool
  | (p, x, y) => ((ofBits x + ofBits y) % p.1).bits

/-- Multiplication modulo `p` of a binary residue by a natural number. -/
private def primeSMul : PrimeDesc × ℕ × List Bool → List Bool
  | (p, a, x) => (a * ofBits x % p.1).bits

/-- The additive groups `ZMod p` of prime order `p`, with generator `1` and residues encoded in
binary. -/
private def primeFields : PrimeOrderGroupFamily where
  Desc := PrimeDesc
  encDesc := encPrime
  order p := p.1
  prime_order p := p.2
  Carrier p := ZMod p.1
  generator _ := 1
  card_carrier p := Nat.card_zmod p.1
  generator_ne_zero p := by
    have := Fact.mk p.2
    exact one_ne_zero
  encode _ x := x.val.bits
  encode_injective p x y h := by
    have : NeZero p.1 := ⟨p.2.ne_zero⟩
    exact ZMod.val_injective _ (encNat.injective h)
  add := primeAdd
  add_encode p x y := by
    have : NeZero p.1 := ⟨p.2.ne_zero⟩
    simp only [primeAdd, ofBits_bits, ZMod.val_add]
  smul := primeSMul
  smul_encode p a x := by
    have : NeZero p.1 := ⟨p.2.ne_zero⟩
    simp only [primeSMul, ofBits_bits, smul_eq_mul, ZMod.val_mul, ZMod.val_natCast,
      Nat.mod_mul_mod]
  computableInPolyTime_order := computableInPolyTime_val
  computableInPolyTime_generator := by
    have := computableInPolyTime_val
    simp only [ZMod.val_one_eq_one_mod]
    fun_prop
  computableInPolyTime_add := by
    have := computableInPolyTime_val
    unfold primeAdd
    fun_prop
  computableInPolyTime_smul := by
    have := computableInPolyTime_val
    unfold primeSMul
    fun_prop

private theorem exists_bertrandPrime (n : ℕ) : ∃ p, p.Prime ∧ 2 ^ n < p ∧ p ≤ 2 * 2 ^ n :=
  Nat.exists_prime_lt_and_le_two_mul (2 ^ n) (pow_ne_zero n two_ne_zero)

/-- A prime `2 ^ n < p ≤ 2 ^ (n + 1)` by Bertrand's postulate, chosen without any algorithm. -/
private noncomputable def bertrandPrime (n : ℕ) : primeFields.Desc :=
  ⟨(exists_bertrandPrime n).choose, (exists_bertrandPrime n).choose_spec.1⟩

private theorem two_pow_le_order_bertrandPrime (n : ℕ) :
    2 ^ n ≤ primeFields.order (bertrandPrime n) :=
  (exists_bertrandPrime n).choose_spec.2.1.le

/-- The prime has at most `n + 2` binary digits. -/
private theorem polynomiallyBounded_bertrandPrime :
    PolynomiallyBounded fun n => (primeFields.encDesc (bertrandPrime n)).length := by
  refine PolynomiallyBounded.of_forall_le 2 1 fun n => ?_
  change (exists_bertrandPrime n).choose.bits.length ≤ _
  have hle := (exists_bertrandPrime n).choose_spec.2.2
  have hsize : (exists_bertrandPrime n).choose.size ≤ n + 2 := by
    apply Nat.size_le.mpr
    have hpos := Nat.two_pow_pos n
    rw [pow_succ, pow_succ]
    omega
  rw [Nat.size_eq_bits_len, pow_one]
  omega

-- With every parameter condition discharged, the headline needs only the discrete-logarithm
-- assumption for the Bertrand primes. It fails for these groups (see the module docstring).
example (hDL : primeFields.DiscreteLog fun n => PMF.pure (bertrandPrime n)) :
    ROMSignature.EUFCMA (fun n => encBitString n)
      (fun n => primeFields.schnorrNativeROMScheme n (bertrandPrime n) n) :=
  hDL.eufCma_schnorrNativeROMScheme polynomiallyBounded_bertrandPrime (width := fun n => n)
    (by fun_prop) two_pow_le_order_bertrandPrime negligible_one_div_two_pow

end CslibFrontierTests.Crypto.SchnorrSecurity
