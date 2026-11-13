/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.RelativeScan

/-!
# Canonical row-major bits for movement schedules

Each row lists the input head first and then the work heads. Each movement occupies its negative
and positive indicator bits. The pair `11` is invalid. Canonical words consist of complete rows
of valid aligned pairs; these definitions specify an input representation, not a free native
validator or a conversion from a packed binary natural.
-/

public section

namespace Turing.MultiTapeTM.ScheduleBits

/-- Column zero is the input head; column `h.succ` is work head `h`. -/
@[expose] def head {k : ℕ} : Fin (k + 1) → Option (Fin k) := Fin.cases none some

/-- The first raw column is the input-head movement. -/
@[simp] theorem head_zero {k : ℕ} : head (0 : Fin (k + 1)) = none := rfl

/-- Successor columns are the work-head movements. -/
@[simp] theorem head_succ {k : ℕ} (h : Fin k) : head h.succ = some h := rfl

/-- Decode one aligned movement pair, rejecting `11`. -/
@[expose] def decodePair : Bool → Bool → Option SignType
  | false, false => some 0
  | true, false => some (-1)
  | false, true => some 1
  | true, true => none

/-- Every movement has a canonical pair with the expected decoder result. -/
@[simp] theorem decodePair_encode (s : SignType) :
    decodePair (RelativeScan.negative s) (RelativeScan.positive s) = some s := by
  cases s <;> simp [RelativeScan.negative, RelativeScan.positive, decodePair]

/-- A binary word partitions into valid aligned pairs. Odd-length words have no derivation. -/
inductive ValidPairs : List Bool → Prop
  /-- The empty word contains no invalid pair. -/
  | nil : ValidPairs []
  /-- Prepend one valid pair. -/
  | cons {a b : Bool} {rest : List Bool} :
      decodePair a b ≠ none → ValidPairs rest → ValidPairs (a :: b :: rest)

/-- Appending complete sequences of valid pairs preserves pair alignment. -/
theorem ValidPairs.append {a b : List Bool} (ha : ValidPairs a) (hb : ValidPairs b) :
    ValidPairs (a ++ b) := by
  induction ha with
  | nil => exact hb
  | cons h _ ih => exact .cons h ih

/-- The invalid aligned pair cannot represent a movement. -/
theorem not_validPairs_true_true (rest : List Bool) : ¬ ValidPairs (true :: true :: rest) := by
  intro h
  cases h with
  | cons hn _ => exact hn rfl

/-- Movement encoding always produces complete canonical pairs. -/
theorem validPairs_encode (ss : List SignType) : ValidPairs (RelativeScan.encode ss) := by
  induction ss with
  | nil => exact .nil
  | cons s ss ih => exact .cons (by simp) ih

/-- One row, in input-first head order and two-bit movement encoding. -/
@[expose] def row {k : ℕ} (r : Option (Fin k) → SignType) : List Bool :=
  RelativeScan.encode (List.ofFn fun c => r (head c))

/-- Consecutive rows with no padding or delimiters. -/
@[expose] def rows {k : ℕ} : List (Option (Fin k) → SignType) → List Bool
  | [] => []
  | r :: rs => row r ++ rows rs

/-- The selected column, retaining its two-bit movement pairs in row order. -/
@[expose] def column {k : ℕ} (c : Fin (k + 1)) (rs : List (Option (Fin k) → SignType)) :
    List Bool :=
  RelativeScan.encode (rs.map fun r => r (head c))

/-- Every raw row has two cells for each input or work head. -/
@[simp] theorem length_row {k : ℕ} (r : Option (Fin k) → SignType) :
    (row r).length = 2 * (k + 1) := by simp [row]

/-- The raw schedule length is the fixed row width times the number of rows. -/
@[simp] theorem length_rows {k : ℕ} (rs : List (Option (Fin k) → SignType)) :
    (rows rs).length = 2 * (k + 1) * rs.length := by
  induction rs with
  | nil => simp [rows]
  | cons r rs ih => simp [rows, ih, Nat.mul_add, Nat.add_comm]

/-- A selected column has exactly two cells per schedule row. -/
@[simp] theorem length_column {k : ℕ} (c : Fin (k + 1))
    (rs : List (Option (Fin k) → SignType)) : (column c rs).length = 2 * rs.length := by
  simp [column]

/-- Raw canonical schedules contain complete rows and reject every invalid aligned pair. -/
@[expose] def Canonical (k : ℕ) (word : List Bool) : Prop :=
  word.length % (2 * (k + 1)) = 0 ∧ ValidPairs word

/-- Encoded rows satisfy the explicit canonical-input condition. -/
theorem canonical_rows {k : ℕ} (rs : List (Option (Fin k) → SignType)) :
    Canonical k (rows rs) := by
  constructor
  · simp
  · induction rs with
    | nil => exact .nil
    | cons r rs ih => exact (validPairs_encode _).append ih

/-- An invalid first pair is rejected even if the remaining word has whole-row length. -/
theorem not_canonical_true_true (k : ℕ) (rest : List Bool) :
    ¬ Canonical k (true :: true :: rest) := fun h => not_validPairs_true_true rest h.2

/-- A row splits around the selected movement into fixed-width prefix and suffix fields. -/
theorem exists_row_split {k : ℕ} (r : Option (Fin k) → SignType) (c : Fin (k + 1)) :
    ∃ pre post : List Bool,
      pre.length = 2 * c.val ∧ post.length = 2 * (k - c.val) ∧
      row r = pre ++ [RelativeScan.negative (r (head c)), RelativeScan.positive (r (head c))] ++
        post := by
  let signs := List.ofFn fun j => r (head j)
  refine ⟨RelativeScan.encode (signs.take c.val),
    RelativeScan.encode (signs.drop (c.val + 1)), ?_, ?_, ?_⟩
  · simp only [RelativeScan.length_encode, List.length_take, List.length_ofFn, signs]
    rw [Nat.min_eq_left (by omega)]
  · simp only [RelativeScan.length_encode, List.length_drop, List.length_ofFn, signs]
    omega
  · have hi : c.val < signs.length := by simp only [signs, List.length_ofFn]; omega
    have hs := List.take_append_drop c.val signs
    rw [List.drop_eq_getElem_cons hi] at hs
    have he : signs[c.val] = r (head c) := by
      exact List.getElem_ofFn ..
    rw [he] at hs
    calc
      row r = RelativeScan.encode (signs.take c.val ++ r (head c) ::
          signs.drop (c.val + 1)) := congrArg RelativeScan.encode hs.symm
      _ = _ := by simp [RelativeScan.encode, List.append_assoc]

end Turing.MultiTapeTM.ScheduleBits
