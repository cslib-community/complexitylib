/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.CarryLookahead.Local
public import CslibFrontier.Computability.Circuit.Boolean.LocalValueGame

/-!
# Cross-layer value queries for carry-lookahead addition

Addresses name input bits, a cell of a doubling round, or one of the fixed finishing gates.
The local decoder follows at most two predecessor addresses without constructing any row.
Its semantics agrees with the existing carry-lookahead adder, including the incoming and outgoing
carry. A rank charges at most two gates per doubling round and six finishing gates.

Input access is explicit through `readInput`. The semantic decoder is not a free-oracle
machine certificate: a native implementation must charge reading the runtime input and encoding
and updating the address. In particular this file alone does not give sublinear-time input access.
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.CarryLookahead.Query

open LocalValueGame

/-- An address in the shared carry-prefix graph and its fixed finishing XOR gates. -/
inductive Address where
  | input (index : ℕ)
  | generate (round cell : ℕ)
  | propagate (round cell : ℕ)
  | generateAnd (round cell : ℕ)
  | xorOr (bit : ℕ)
  | xorAnd (bit : ℕ)
  | xorNot (bit : ℕ)
  | xor (bit : ℕ)
  | sumOr (bit : ℕ)
  | sumAnd (bit : ℕ)
  | sumNot (bit : ℕ)
  | sum (bit : ℕ)
  deriving DecidableEq

/-- Total sequential-input lookup used in the semantics; invalid references read false. -/
def readInput (w : ℕ) (u : BitString (w + w + 1)) (i : ℕ) : Bool :=
  if h : i < w + w + 1 then u ⟨i, h⟩ else false

/-- The operation at one address, with `rounds` used only by the finishing gates' routing. -/
def decoder (w rounds : ℕ) (u : BitString (w + w + 1)) : Decoder Address where
  op
    | .input i => .const (readInput w u i)
    | .generate _ i => if i < w + 1 then .or else .const false
    | .propagate r i => if i < w + 1 then
        if r = 0 then (if i < w then .or else .const false) else .and
        else .const true
    | .generateAnd _ _ => .and
    | .xorOr _ | .sumOr _ => .or
    | .xorAnd _ | .sumAnd _ | .xor _ | .sum _ => .and
    | .xorNot _ | .sumNot _ => .not
  child a b := match a with
    | .input i => .input i
    | .generate 0 i => if i < w then
        if b then .generateAnd 0 i else .generateAnd 0 i
        else .input (w + w)
    | .generate (r + 1) i => if b then .generateAnd (r + 1) i else .generate r i
    | .propagate 0 i => .input (if b then w + (w - 1 - i) else w - 1 - i)
    | .propagate (r + 1) i => .propagate r (if b then neighbourIndex (w + 1) (2 ^ r) i else i)
    | .generateAnd 0 i => .input (if b then w + (w - 1 - i) else w - 1 - i)
    | .generateAnd (r + 1) i => if b then .generate r (neighbourIndex (w + 1) (2 ^ r) i)
        else .propagate r i
    | .xorOr i | .xorAnd i => .input (if b then w + i else i)
    | .xorNot i => .xorAnd i
    | .xor i => if b then .xorNot i else .xorOr i
    | .sumOr i | .sumAnd i => if b then .generate rounds (w - i) else .xor i
    | .sumNot i => .sumAnd i
    | .sum i => if b then .sumNot i else .sumOr i

/-- A proof-only rank: two steps per carry round, and fixed finishing overhead. -/
def rank (rounds : ℕ) : Address → ℕ
  | .input _ => 0
  | .generate r _ => 2 * r + 2
  | .propagate r _ => 2 * r + 1
  | .generateAnd r _ => 2 * r + 1
  | .xorOr _ | .xorAnd _ => 1
  | .xorNot _ => 2
  | .xor _ => 3
  | .sumOr _ | .sumAnd _ => 2 * rounds + 4
  | .sumNot _ => 2 * rounds + 5
  | .sum _ => 2 * rounds + 6

/-- Every used local edge decreases rank, including both universal choices. -/
theorem descends (w rounds : ℕ) (u : BitString (w + w + 1)) :
    (decoder w rounds u).Descends (rank rounds) := by
  intro a b
  cases a with
  | input i => trivial
  | generate r i =>
    cases r <;> cases b <;> simp only [decoder] <;>
      split_ifs <;> simp_all [rank]
  | propagate r i =>
    cases r <;> cases b <;> simp only [decoder] <;>
      split_ifs <;> simp_all [rank]
  | generateAnd r i =>
    cases r <;> cases b <;> simp [decoder, rank]
    omega
  | xorOr i | xorAnd i | xorNot i | xor i | sumOr i | sumAnd i | sumNot i | sum i =>
    cases b <;> simp [decoder, rank]

/-- The mathematical row after the specified number of doubling rounds. This is proof data,
not a row constructed by the decoder. -/
def row (w : ℕ) (u : BitString (w + w + 1)) (r : ℕ) : BitString ((w + 1) + (w + 1)) :=
  (scan (w + 1) r).eval interpretation ((initial w).eval interpretation u)

/-- The semantic value at each locally addressed gate. -/
def value (w rounds : ℕ) (u : BitString (w + w + 1)) : Address → Bool
  | .input i => readInput w u i
  | .generate r i => (readRow (row w u r) i).1
  | .propagate r i => (readRow (row w u r) i).2
  | .generateAnd 0 i => readInput w u (w - 1 - i) && readInput w u (w + (w - 1 - i))
  | .generateAnd (r + 1) i => (readRow (row w u r) i).2 &&
      (readRow (row w u r) (neighbourIndex (w + 1) (2 ^ r) i)).1
  | .xorOr i => readInput w u i || readInput w u (w + i)
  | .xorAnd i => readInput w u i && readInput w u (w + i)
  | .xorNot i => !(readInput w u i && readInput w u (w + i))
  | .xor i => xor (readInput w u i) (readInput w u (w + i))
  | .sumOr i => xor (readInput w u i) (readInput w u (w + i)) ||
      (readRow (row w u rounds) (w - i)).1
  | .sumAnd i => xor (readInput w u i) (readInput w u (w + i)) &&
      (readRow (row w u rounds) (w - i)).1
  | .sumNot i => !(xor (readInput w u i) (readInput w u (w + i)) &&
      (readRow (row w u rounds) (w - i)).1)
  | .sum i => xor (xor (readInput w u i) (readInput w u (w + i)))
      (readRow (row w u rounds) (w - i)).1

private theorem xor_eq (a b : Bool) : xor a b = ((a || b) && !(a && b)) := by
  cases a <;> cases b <;> rfl

private theorem row_succ (w : ℕ) (u : BitString (w + w + 1)) (r i : ℕ)
    (hi : i < w + 1) :
    readRow (row w u (r + 1)) i =
      combine (readRow (row w u r) i)
        (readRow (row w u r) (neighbourIndex (w + 1) (2 ^ r) i)) := by
  rw [row, scan, Circuit.eval_comp, readRow_step, ite_eq_left hi]
  change combine (readRow (row w u r) i) (readRow (row w u r) (i + 2 ^ r)) = _
  by_cases hn : i + 2 ^ r < w + 1
  · simp [neighbourIndex, hn]
  · simp [neighbourIndex, hn, readRow]

/-- The supplied semantic value satisfies every decoded local equation. -/
theorem value_eq_eval (w rounds : ℕ) (u : BitString (w + w + 1)) (a : Address) :
    value w rounds u a = (decoder w rounds u).eval (value w rounds u) a := by
  cases a with
  | input i => rfl
  | generate r i =>
    by_cases hi : i < w + 1
    · cases r with
      | zero =>
        have h := readRow_initial u ⟨i, hi⟩
        
        by_cases hw : i < w
        · simp [value, Decoder.eval, decoder, hw, h, readInput, leftInput, rightInput, Nat.add_comm,
          row, scan,
          Circuit.eval_wiring, show i ≤ w by omega, show w - 1 - i < w + w + 1 by omega,
          show w + (w - 1 - i) < w + w + 1 by omega]
        · simp [value, Decoder.eval, decoder, hw, h, readInput, Fin.last, row, scan,
          Circuit.eval_wiring, show i ≤ w by omega]
      | succ r =>
        rw [value, row_succ w u r i hi]
        simp [Decoder.eval, decoder, value, combine, show i ≤ w by omega]
    · simp [value, readRow, hi, Decoder.eval, decoder, show ¬i ≤ w by omega]
  | propagate r i =>
    by_cases hi : i < w + 1
    · cases r with
      | zero =>
        have h := readRow_initial u ⟨i, hi⟩
        
        by_cases hw : i < w
        · simp [value, Decoder.eval, decoder, hw, h, readInput, leftInput, rightInput, Nat.add_comm,
          row, scan,
          Circuit.eval_wiring, show i ≤ w by omega, show w - 1 - i < w + w + 1 by omega,
          show w + (w - 1 - i) < w + w + 1 by omega]
        · simp [value, Decoder.eval, decoder, hw, h, row, scan,
          Circuit.eval_wiring, show i ≤ w by omega]
      | succ r =>
        rw [value, row_succ w u r i hi]
        simp [Decoder.eval, decoder, value, combine, show i ≤ w by omega]
    · simp [value, readRow, hi, Decoder.eval, decoder, show ¬i ≤ w by omega]
  | generateAnd r i => cases r <;> rfl
  | xorOr i | xorAnd i | xorNot i | sumOr i | sumAnd i | sumNot i => rfl
  | xor i | sum i => exact xor_eq _ _

/-- At the prescribed logarithmic number of rounds, an addressed sum bit is exactly the
corresponding output of the existing adder. -/
theorem value_sum_eq (w : ℕ) (u : BitString (w + w + 1)) (i : Fin w) :
    value w (Nat.clog 2 (w + 1)) u (.sum i) =
      (carryLookahead w).eval interpretation u i.castSucc := by
  simp only [value, carryLookahead, Circuit.eval_comp, finish, Circuit.eval_append,
    show i.castSucc = Fin.castAdd 1 i from rfl, Fin.append_left, Circuit.eval_pi,
    Formula.eval_toCircuit, sumFormula, Formula.eval_xor, Formula.eval_input,
    Circuit.eval_wiring, Function.comp_apply, Fin.append_right]
  simp [readInput, readRow, row, carries, Circuit.eval_comp, leftInput, rightInput,
    show w - i.val < w + 1 by omega, show i.val < w + w + 1 by omega,
    show w + i.val < w + w + 1 by omega, Fin.castAdd, Fin.addNat, Fin.castLE, Nat.add_comm]

/-- The generate cell at index zero is the outgoing carry, including width zero. -/
theorem value_carry_eq (w : ℕ) (u : BitString (w + w + 1)) :
    value w (Nat.clog 2 (w + 1)) u (.generate (Nat.clog 2 (w + 1)) 0) =
      (carryLookahead w).eval interpretation u (Fin.last w) := by
  rw [eval_carryLookahead_carry]
  simpa [value, readRow, row, carries, Circuit.eval_comp, Fin.castAdd, Fin.castLE] using
    eval_carries u (Fin.last w)

/-- The complete local value game answers the selected sum bit of the existing adder. -/
theorem wins_sum_iff (w : ℕ) (u : BitString (w + w + 1))
    (enc : Claim Address ↪ List Bool) (i : Fin w) (b : Bool) :
    Turing.MultiTapeATM.WordGame.Wins
      (LocalValueGame.update (decoder w (Nat.clog 2 (w + 1)) u) enc)
      (position (decoder w (Nat.clog 2 (w + 1)) u) enc ⟨.sum i, b⟩) ↔
        (carryLookahead w).eval interpretation u i.castSucc = b := by
  rw [wins_position_iff (descends w (Nat.clog 2 (w + 1)) u)
    (value w (Nat.clog 2 (w + 1)) u) (value_eq_eval w (Nat.clog 2 (w + 1)) u)]
  rw [value_sum_eq]

/-- A requested sum bit is decided by a value game with logarithmically many moves. -/
theorem ends_sum (w : ℕ) (u : BitString (w + w + 1))
    (enc : Claim Address ↪ List Bool) (i : ℕ) (b : Bool) :
    Turing.MultiTapeATM.WordGame.Ends (LocalValueGame.update (decoder w (Nat.clog 2 (w + 1)) u) enc)
      (2 * Nat.clog 2 (w + 1) + 6)
      (position (decoder w (Nat.clog 2 (w + 1)) u) enc ⟨.sum i, b⟩) :=
  by simpa only [rank] using
    ends_position (encC := enc) (descends w (Nat.clog 2 (w + 1)) u)
      (⟨.sum i, b⟩ : Claim Address)

end Cslib.Circuits.Boolean.CarryLookahead.Query
