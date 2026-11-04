/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.TreeEval.Ary.PackingParameters
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.InSpace.NatSize
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.InSpace.NatPrime
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.InSpace.NatPow
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.Constructible

/-!
# Uniform native initialization of packed field parameters

Both fan-in and value width are runtime binary naturals. Initialization computes their chunk
width, ceiling chunk count, alphabet size and the exact least sufficient prime used by the
packed algebra. Primality uses a divisor-counter loop; the bounded first-prime search stores
only its two binary counters. No table of candidates or divisors is constructed.

The space certificate is linear in the binary encoding of `(d,b)`, including output storage.
Running time is deliberately unrestricted. This initializes the parameters; it does not claim
the remaining implicit evaluator or its transition certificates.
-/

public section

namespace Cslib.TreeEval.Ary.Packed

open Turing MultiTapeTM ComputableInSpace

/-- Runtime chunk width is computed by measuring the binary product, not by a finite lookup. -/
theorem chunkWidth_inSpace :
    ComputableInSpace (fun q : ℕ × ℕ => chunkWidth q.1 q.2)
      (encPair encNat encNat) encNat (fun q => (encPair encNat encNat q).length) :=
  (budget_comp_linear natSize
    (budget_natMul (fst encNat encNat) (snd encNat encNat))).of_enc_eq fun _ => rfl

/-- Ceiling division uses binary addition, predecessor and division at runtime. -/
theorem chunkCount_inSpace :
    ComputableInSpace (fun q : ℕ × ℕ => chunkCount q.1 q.2)
      (encPair encNat encNat) encNat (fun q => (encPair encNat encNat q).length) := by
  have hb := snd encNat encNat
  exact (budget_natDiv (budget_natPred (budget_natAdd hb chunkWidth_inSpace))
    chunkWidth_inSpace).of_enc_eq fun q => by
      rw [chunkCount, Nat.ceilDiv_eq_add_pred_div]

/-- The chunk alphabet size has only `chunkWidth + 1` binary digits. -/
theorem alphabetSize_inSpace :
    ComputableInSpace (fun q : ℕ × ℕ => 2 ^ chunkWidth q.1 q.2)
      (encPair encNat encNat) encNat (fun q => (encPair encNat encNat q).length) := by
  refine budget_natPow_variable (budget_const (encB := encNat) 2 (.refl _))
    chunkWidth_inSpace ?_
  refine .of_le_linear 8 8 fun q => ?_
  have hm := Nat.size_mul_le q.1 q.2
  have hlen := length_encNat_le_self (chunkWidth q.1 q.2)
  have htwo : (encNat 2).length = 2 := rfl
  simp only [length_encPair, length_encNat_eq_size, chunkWidth, htwo] at *
  omega

/-- The corrected strict degree threshold is computed from the runtime packed parameters. -/
theorem gateDegree_inSpace :
    ComputableInSpace (fun q : ℕ × ℕ => gateDegree q.1 q.2)
      (encPair encNat encNat) encNat (fun q => (encPair encNat encNat q).length) :=
  (budget_natMul (budget_natMul (fst encNat encNat) chunkCount_inSpace)
    (budget_natPred alphabetSize_inSpace)).of_enc_eq fun _ => rfl

/-- A concrete bounded search computes the same least prime as the algebraic construction. -/
theorem fieldModulus_eq_boundedFirstPrime (d b : ℕ) :
    fieldModulus d b = PrimeSearch.boundedFirstPrime (gateDegree d b + 2)
      (2 * (gateDegree d b + 1)) := by
  symm
  apply PrimeSearch.boundedFirstPrime_eq_find
    (gateDegree d b + 2) (2 * (gateDegree d b + 1))
    (Nat.exists_infinite_primes (gateDegree d b + 2))
  exact fieldModulus_le d b

/-- Native initialization finds the exact selected prime in binary-input-linear space.
The hidden constant is uniform in both runtime parameters. -/
theorem fieldModulus_inSpace :
    ComputableInSpace (fun q : ℕ × ℕ => fieldModulus q.1 q.2)
      (encPair encNat encNat) encNat (fun q => (encPair encNat encNat q).length) := by
  have hsucc := budget_natSucc gateDegree_inSpace
  have hlo := budget_natSucc hsucc
  have hbound := budget_natAdd hsucc hsucc
  refine (budget_comp_linear PrimeSearch.boundedFirstPrime_inSpace
    (budget_prod hlo hbound)).of_enc_eq ?_
  intro q
  have hboundeq : 2 * (gateDegree q.1 q.2 + 1) =
      (gateDegree q.1 q.2 + 1) + (gateDegree q.1 q.2 + 1) := by omega
  rw [fieldModulus_eq_boundedFirstPrime, hboundeq]

/-- Width, chunk count, alphabet size and modulus, all initialized from runtime parameters. -/
@[expose] def parameters (d b : ℕ) : ℕ × ℕ × ℕ × ℕ :=
  (chunkWidth d b, chunkCount d b, 2 ^ chunkWidth d b, fieldModulus d b)

/-- Framed binary encoding of width, chunk count, alphabet size and modulus. -/
abbrev encParameters : ℕ × ℕ × ℕ × ℕ ↪ List Bool :=
  encPair encNat (encPair encNat (encPair encNat encNat))

/-- All four parameters can be initialized uniformly with their encoded output charged. -/
theorem parameters_inSpace :
    ComputableInSpace (fun q : ℕ × ℕ => parameters q.1 q.2)
      (encPair encNat encNat) encParameters (fun q => (encPair encNat encNat q).length) :=
  budget_prod chunkWidth_inSpace
    (budget_prod chunkCount_inSpace (budget_prod alphabetSize_inSpace fieldModulus_inSpace))

end Cslib.TreeEval.Ary.Packed
