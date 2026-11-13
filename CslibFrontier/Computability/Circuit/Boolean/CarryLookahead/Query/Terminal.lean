/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.CarryLookahead.Query.Routing
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic

/-!
# Terminal requests for the finishing adder

A terminal word starts with a query flag, an operand selector, and either the claimed bit or an
immediate answer. Its tail is a binary component index. The padded incoming carry is zero, so
only input indices strictly below twice the width request an actual operand bit. The request
construction is polynomial in the short routing metadata and never reads the operands.
-/

public section

namespace Cslib.Circuits.Boolean.CarryLookahead.Query.Terminal

open Routing Turing.MultiTapeTM ComputableInPolyTime

/-- Whether the terminal refers to a bit in one of the two operands. -/
@[expose] def queries (p : Position) : Bool :=
  decide (p.address.tag = 0 ∧ p.address.index < 2 * p.width)

/-- Select the right operand for an input in the second half of the input array. -/
@[expose] def carry (p : Position) : Bool := decide (p.width ≤ p.address.index)

/-- The binary bit index within the selected operand. -/
@[expose] def index (p : Position) : ℕ :=
  if carry p then p.address.index - p.width else p.address.index

/-- Immediate answer at a constant terminal. Input padding and invalid inputs read zero. -/
@[expose] def answer (p : Position) : Bool :=
  match operation p with
  | .const b => b == p.claim
  | _ => false

/-- The third request bit carries a claim for a query, or the answer for an immediate leaf. -/
@[expose] def claimOrAnswer (p : Position) : Bool :=
  if queries p then p.claim else answer p

/-- Request flag, operand selector, claim or answer, and binary component index. -/
@[expose] def word (p : Position) : List Bool :=
  [queries p, carry p, claimOrAnswer p] ++ encNat (index p)

/-- An operand request always names a valid bit of the selected operand. -/
theorem index_lt {p : Position} (hq : queries p = true) : index p < p.width := by
  simp only [queries, decide_eq_true_eq] at hq
  unfold index carry
  split_ifs <;> simp_all
  omega

/-- Request classification is native polynomial time in the metadata. -/
theorem queries_polyTime : ComputableInPolyTime queries encPosition encBool := by
  unfold queries
  fun_prop

/-- Operand selection is native polynomial time in the metadata. -/
theorem carry_polyTime : ComputableInPolyTime carry encPosition encBool := by
  unfold carry
  fun_prop

/-- Computing the component index is native polynomial time in the metadata. -/
theorem index_polyTime : ComputableInPolyTime index encPosition encNat := by
  have := carry_polyTime
  unfold index
  fun_prop

/-- Constant comparison does not depend on any operand word. -/
theorem answer_polyTime : ComputableInPolyTime answer encPosition encBool := by
  have h := of_finite (encIn := encPair encOp encBool) (encOut := encBool)
    (fun q : Op × Bool => match q.1 with | .const b => b == q.2 | _ => false)
  exact h.comp (operation_polyTime.pair (by fun_prop))

/-- The complete terminal request is computed from the short metadata by a native machine. -/
theorem word_polyTime : ComputableInPolyTime word encPosition encBits := by
  have hq := queries_polyTime
  have hc := carry_polyTime
  have ha := answer_polyTime
  have hb : ComputableInPolyTime (fun n : ℕ => encNat n) encNat encBits := .of_eq fun _ => rfl
  have hi : ComputableInPolyTime (fun p => encNat (index p)) encPosition encBits :=
    hb.comp index_polyTime
  unfold word claimOrAnswer
  fun_prop

/-- Requests to the left operand retain the original bit index and claimed value. -/
theorem word_input_left (w rounds : ℕ) (i : Fin w) (claim : Bool) :
    word (ofClaim w rounds ⟨.input i.val, claim⟩) =
      [true, false, claim] ++ encNat i.val := by
  have hi : i.val < 2 * w := by omega
  simp [word, queries, carry, index, claimOrAnswer, ofClaim, Address.toData, hi,
    Nat.not_le.mpr i.isLt]

/-- Requests to the right operand subtract the left operand's width from the address. -/
theorem word_input_right (w rounds : ℕ) (i : Fin w) (claim : Bool) :
    word (ofClaim w rounds ⟨.input (w + i.val), claim⟩) =
      [true, true, claim] ++ encNat i.val := by
  have hi : w + i.val < 2 * w := by omega
  simp [word, queries, carry, index, claimOrAnswer, ofClaim, Address.toData, hi]

/-- The padded incoming carry has an immediate zero answer and never queries an operand. -/
theorem word_input_padding (w rounds : ℕ) (claim : Bool) :
    word (ofClaim w rounds ⟨.input (w + w), claim⟩) =
      [false, true, !claim] ++ encNat w := by
  cases claim <;>
    simp [word, queries, carry, index, claimOrAnswer, answer, operation, ofClaim,
      Address.toData, opData, Nat.two_mul]

/-- Interpret a terminal request by querying the actual selected operand, or using its answer. -/
@[expose] def response {w : ℕ} (left right : BitString w) (p : Position)
    (hw : p.width = w) : Bool :=
  if hq : queries p = true then
    (if carry p then right ⟨index p, hw ▸ index_lt hq⟩
      else left ⟨index p, hw ▸ index_lt hq⟩) == p.claim
  else answer p

private theorem readInput_operands (w : ℕ) (left right : BitString w) (i : ℕ) :
    readInput w (Fin.append (Fin.append left right) ![false]) i =
      if hi : i < w then left ⟨i, hi⟩
      else if hi : i < w + w then right ⟨i - w, by omega⟩ else false := by
  by_cases h₀ : i < w
  · simp [readInput, Fin.append, Fin.addCases, h₀, show i < w + w by omega,
      show i < w + w + 1 by omega]
  · by_cases h₁ : i < w + w
    · simp [readInput, Fin.append, Fin.addCases, h₀, h₁, show i < w + w + 1 by omega]
    · by_cases h₂ : i < w + w + 1
      · have hi : i = w + w := by omega
        subst i
        simp [readInput, Fin.append, Fin.addCases, h₀]
      · simp [readInput, h₀, h₁, h₂]

/-- At a routed terminal, the response agrees with the actual finishing-adder wire value. -/
theorem response_eq_true_iff (w rounds : ℕ) (left right : BitString w)
    (c : LocalValueGame.Claim Address) (hp : player (ofClaim w rounds c) = none) :
    response left right (ofClaim w rounds c) rfl = true ↔
      value w rounds (Fin.append (Fin.append left right) ![false]) c.wire = c.value := by
  rw [value_eq_eval]
  rcases c with ⟨a, v⟩
  cases a with
  | input i =>
    simp only [LocalValueGame.Decoder.eval, decoder, readInput_operands]
    by_cases h₀ : i < w
    · have h₁ : i < 2 * w := by omega
      simp [response, queries, carry, index, ofClaim, Address.toData, h₀, h₁,
        Nat.not_le.mpr h₀]
    · by_cases h₁ : i < 2 * w
      · simp [response, queries, carry, index, ofClaim, Address.toData, h₀, h₁,
          show w ≤ i by omega, show i < w + w by omega]
      · simp [response, queries, answer, operation, ofClaim, Address.toData, opData, h₀, h₁,
          show ¬i < w + w by omega]
  | generate r i | propagate r i =>
    by_cases hi : i ≤ w <;> by_cases hr : r = 0 <;> by_cases hj : i < w <;>
      simp [player, response, queries, ofClaim, Address.toData, answer, operation, opData,
        LocalValueGame.Decoder.eval, decoder, hi, hr, hj] at hp ⊢
  | generateAnd r i | xorOr i | xorAnd i | xorNot i | xor i
  | sumOr i | sumAnd i | sumNot i | sum i =>
    simp [player, operation_ofClaim, decoder] at hp

end Cslib.Circuits.Boolean.CarryLookahead.Query.Terminal
