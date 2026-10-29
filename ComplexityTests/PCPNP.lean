/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Classes.PCP.NP
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Tactic.PolyTime

/-! Sparse proof tables, duplicate addresses, malformed witnesses, and exact NP containment. -/

namespace ComplexityTests.PCPNP

open Cslib Cslib.Complexity Turing.MultiTapeTM

private def requireBit : PCPVerifier (Bool × ℕ) where
  coins := fun _ => 1
  queries := fun p => [p.1.2, p.1.2]
  verdict := fun p => p.1.1.1 && p.2.getD 0 false && p.2.getD 1 false

private theorem requireBit_polyTime : requireBit.PolyTime (encPair encBool encNat) := by
  refine ⟨?_, ?_, ?_⟩ <;> unfold requireBit <;> fun_prop

private theorem requireBit_coins (a : Bool × ℕ) :
    requireBit.coins a ≤ 1 * (Nat.log 2 (encPair encBool encNat a).length + 1) := by
  simp only [requireBit, one_mul]
  lia

-- Large binary addresses produce four table entries, never an address-sized certificate.
example : requireBit.queryTable (true, 2 ^ 100) = [2 ^ 100, 2 ^ 100, 2 ^ 100, 2 ^ 100] := by
  decide

example : requireBit.tableVerifier ((true, 2 ^ 100), [true]) = true := by decide

-- Every duplicate consults the first occurrence; later contradictory bits are ignored.
example : requireBit.tableVerifier ((true, 2 ^ 100), [true, false, false, false]) = true := by
  decide

example : requireBit.tableVerifier ((true, 2 ^ 100), [false, true, true, true]) = false := by
  decide

example : requireBit.tableVerifier ((true, 2 ^ 100), []) = false := by decide

example : requireBit.tableVerifier ((false, 2 ^ 100), [true, true, true, true]) = false := by
  decide

-- An honest queried-bit table can be padded to an exact certificate length.
example :
    let table := PCPVerifier.answers [false, true] (requireBit.queryTable (true, 1)) ++
      List.replicate 7 false
    table.length = 11 ∧ requireBit.tableVerifier ((true, 1), table) = true := by
  decide

example : ComputableInPolyTime requireBit.tableVerifier
    (encPair (encPair encBool encNat) encBits) encBool :=
  PCPVerifier.isPolyTime_tableVerifier requireBit_polyTime requireBit_coins

example : ComputableInPolyTime (fun p : (Bool × ℕ) × List Bool =>
      let input := p.1
      requireBit.tableVerifier (input, p.2))
    (encPair (encPair encBool encNat) encBits) encBool := by
  have h := PCPVerifier.isPolyTime_tableVerifier requireBit_polyTime requireBit_coins
  polytime

-- The table is the restriction of an actual finite PCP proof even for enormous addresses.
example : ∃ proof, ∀ word, word.length = 1 → requireBit.accepts (true, 2 ^ 100) proof word = true :=
  PCPVerifier.tableVerifier_sound (V := requireBit) _ [true] (by decide)

private theorem requireBit_isPCPVerifier :
    IsPCPVerifier (encPair encBool encNat) (fun n => Nat.log 2 n + 1) (fun _ => 2)
      requireBit {a | a.1 = true} := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [one_mul] using requireBit_coins
  · intro a word _
    simp [requireBit]
  · rintro ⟨bit, address⟩ hbit
    refine ⟨List.replicate (address + 1) true, fun word _ => ?_⟩
    simp only [Set.mem_ofPred_eq] at hbit
    simp [PCPVerifier.accepts, PCPVerifier.answers, requireBit, hbit]
  · rintro ⟨bit, address⟩ hbit proof
    have hb : bit = false := Bool.eq_false_iff.mpr hbit
    subst bit
    change 2 * (Finset.univ.filter fun _ : Fin 1 → Bool => false = true).card ≤ 2 ^ 1
    decide

-- Both accepted and rejected instances occur, so the verifier hypotheses are nonvacuous.
example : {a : Bool × ℕ | a.1 = true} ∈ NP (encPair encBool encNat) := by
  apply PCP_log_subset_NP (fun _ => 1)
  refine ⟨requireBit, 1, 2, requireBit_polyTime, ?_⟩
  simpa only [one_mul, mul_one] using requireBit_isPCPVerifier

private def conflictingCoins : PCPVerifier ℕ where
  coins := fun _ => 1
  queries := fun p => [p.1]
  verdict := fun p => p.2.getD 0 false == p.1.2.getD 0 false

-- Across different random words a shared address cannot receive two answers.
example : conflictingCoins.tableVerifier (2 ^ 100, [false, true]) = false := by decide

example : conflictingCoins.tableVerifier (2 ^ 100, [true, false]) = false := by decide

private def noQueries : PCPVerifier Unit where
  coins := fun _ => 0
  queries := fun _ => []
  verdict := fun _ => true

example : noQueries.queryTable () = [] := by decide

example : noQueries.tableVerifier ((), []) = true := by decide

example (enc : Unit ↪ List Bool) : ComputableInPolyTime noQueries.tableVerifier
    (encPair enc encBits) encBool := by
  apply PCPVerifier.isPolyTime_tableVerifier (c := 0)
  · refine ⟨?_, ?_, ?_⟩ <;> unfold noQueries <;> fun_prop
  · simp [noQueries]

example : ∃ proof, ∀ word, word.length = 0 → noQueries.accepts () proof word = true :=
  PCPVerifier.tableVerifier_sound (V := noQueries) () [] (by decide)

-- The bounded decoder saturates on arbitrary noncanonical binary words as well.
example : BitString.boundedBinaryValue 0 [true, false, true] = 0 := by decide

example : BitString.boundedBinaryValue 5 [false, false, true, true, false] = 5 := by decide

example : BitString.binaryValue (13 : ℕ).bits.reverse = 13 :=
  BitString.binaryValue_reverse_bits 13

example : ComputableInPolyTime (fun n : ℕ => n + 1) encUnary encUnary := by
  refine .of_tidy ?_
  apply ComputableTidilyInPolyTime.binary_to_unary_bounded (bound := fun n => n + 2)
  · exact ComputableTidilyInPolyTime.unary_to_binary.comp (by fun_prop)
  · fun_prop
  · intro n
    lia

-- Arbitrary binary-to-unary expansion is deliberately unavailable.
example : True := by
  fail_if_success
    have : ComputableInPolyTime (fun n : ℕ => n) encNat encUnary := by fun_prop
  trivial

-- A randomness bound alone does not provide the verifier's computation certificates.
example {α : Type} (enc : α ↪ List Bool) (V : PCPVerifier α) (c : ℕ)
    (_hcoins : ∀ a, V.coins a ≤ c * (Nat.log 2 (enc a).length + 1)) : True := by
  fail_if_success
    have : ComputableInPolyTime V.tableVerifier (encPair enc encBits) encBool := by fun_prop
  trivial

end ComplexityTests.PCPNP
