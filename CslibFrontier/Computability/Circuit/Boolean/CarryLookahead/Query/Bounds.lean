/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.CarryLookahead.Query.PolyTime

/-!
# Bounds for carry-lookahead query addresses

The invariant includes the padded input and sentinel carry cells. It is preserved by every
decoded child, even an unused child of a constant gate. Thus a complete routing history stores
only a binary index and a unary round bounded by the initial parameters.
-/

public section

namespace Cslib.Circuits.Boolean.CarryLookahead.Query

/-- The address lies within the input, carry, or finishing layers of a width-`w` query. -/
@[expose] def WellFormed (w rounds : ℕ) : Address → Prop
  | .input i => i ≤ 2 * w
  | .generate r i | .propagate r i | .generateAnd r i => r ≤ rounds ∧ i ≤ w + 1
  | .xorOr i | .xorAnd i | .xorNot i | .xor i
  | .sumOr i | .sumAnd i | .sumNot i | .sum i => i < w

/-- Every child remains bounded, including unused children of terminal gates. -/
theorem WellFormed.child {w rounds : ℕ} {a : Address} (ha : WellFormed w rounds a)
    (u : BitString (w + w + 1)) (b : Bool) :
    WellFormed w rounds ((decoder w rounds u).child a b) := by
  have hn {i d : ℕ} (hi : i ≤ w + 1) : neighbourIndex (w + 1) d i ≤ w + 1 := by
    unfold neighbourIndex
    split_ifs <;> omega
  cases a with
  | input i => exact ha
  | generate r i =>
    cases r <;> cases b <;>
      simp only [decoder, Bool.false_eq_true, ↓reduceIte, WellFormed] at ha ⊢ <;>
      (try split_ifs) <;> omega
  | propagate r i | generateAnd r i =>
    cases r <;> cases b <;>
      simp only [decoder, Bool.false_eq_true, ↓reduceIte, WellFormed] at ha ⊢
    all_goals first | omega | exact ⟨by omega, hn ha.2⟩
  | xorOr i | xorAnd i | xorNot i | xor i | sumOr i | sumAnd i | sumNot i | sum i =>
    cases b <;> simp only [decoder, Bool.false_eq_true, ↓reduceIte, WellFormed] at ha ⊢ <;>
      omega

/-- An arbitrary sequence of local choices preserves the address bound. -/
theorem WellFormed.foldl {w rounds : ℕ} {a : Address} (ha : WellFormed w rounds a)
    (u : BitString (w + w + 1)) (path : List Bool) :
    WellFormed w rounds (path.foldl (decoder w rounds u).child a) := by
  induction path generalizing a with
  | nil => exact ha
  | cons b path ih => exact ih (ha.child u b)

/-- The stored round and index are bounded uniformly across all address constructors. -/
theorem WellFormed.fields {w rounds : ℕ} {a : Address} (ha : WellFormed w rounds a) :
    a.toData.round ≤ rounds ∧ a.toData.index ≤ 2 * w + 1 := by
  cases a <;> simp only [WellFormed, Address.toData] at ha ⊢ <;> omega

/-- Bounded query addresses use logarithmic width and unary-round space. -/
theorem WellFormed.length_encAddress {w rounds : ℕ} {a : Address}
    (ha : WellFormed w rounds a) :
    (encAddress a).length ≤ 2 * rounds + w.size + 11 := by
  have hr := ha.fields.1
  have hi : a.toData.index.size ≤ w.size + 1 := by
    apply (Nat.size_le_size ha.fields.2).trans
    have hbit : Nat.bit true w ≠ 0 := by simp [Nat.bit_val]
    simpa [Nat.bit_val] using (Nat.size_bit hbit).le
  exact (length_encAddress_le a).trans (by omega)

end Cslib.Circuits.Boolean.CarryLookahead.Query
