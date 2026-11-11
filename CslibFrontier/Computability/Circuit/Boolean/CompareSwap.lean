/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.Formula
public import CslibFrontier.Computability.Circuit.Evaluation
public import Mathlib.Order.PiLex
import Mathlib.Order.Fin.Tuple
import Mathlib.Tactic.Ring

/-!
# Boolean comparison and compare-exchange circuits

The comparator reads key coordinates in selector order, with coordinate zero most
significant. Its formula has `6 * k + 1` gates for `k` selected input bits. Compare-exchange
computes the comparison once, retains it and its negation, and selects whole records using
three gates per output bit. Ties preserve the input order, including payload bits outside the key.

For two nonempty records of width `r`, the circuit uses exactly `6 * k + 6 * r + 2` gates,
including constants and negations. Empty records use no gates. Key positions may be arbitrary;
the usual prefix key is `Fin.castLE h` for `h : k ≤ r`.

## Main definitions

* `Cslib.Circuits.Formula.lexLt`: compare two selected input sequences lexicographically.
* `Cslib.Circuits.Boolean.compareSwapCircuit`: order two records by selected key coordinates.
* `Cslib.Circuits.Boolean.compareSwapCircuit.record`: expose a shared swap flag and its complement.
* `Cslib.Circuits.Boolean.compareSwapCircuit.switch`: exchange payloads using saved controls.

## Main results

* `Cslib.Circuits.Formula.eval_lexLt_iff`: agreement with Mathlib's lexicographic order.
* `Cslib.Circuits.Boolean.eval_compareSwapCircuit`: swap whole records exactly when out of order.
* `Cslib.Circuits.Boolean.size_compareSwapCircuit`: exact total gate count.
* `Cslib.Circuits.Boolean.compareSwapCircuit_keys_ordered`: the output keys are in ascending order.
* `Cslib.Circuits.Boolean.compareSwapCircuit.cost_record_eq_exchange`: exposing controls adds
  no gates to `exchange`, which computes its flag even at zero payload width.

## References

* Adapts the comparator endpoint of MassProduction/Sorting.lean in
  [S. Schlesinger, *Boolean circuit mass production formalization*][Schlesinger2026MassProduction],
  using a linear-size comparison and sharing its result between outputs.
-/

@[expose] public section

namespace Cslib.Circuits

namespace Formula

open Boolean

/-- Compare two selected input sequences, with coordinate zero most significant. -/
def lexLt {n : ℕ} : {k : ℕ} → (Fin k → Fin n) → (Fin k → Fin n) → Formula signature n
  | 0, _, _ => const false
  | _ + 1, left, right =>
    let a := input (left 0)
    let b := input (right 0)
    (a.not.and b).or ((a.not.or b).and (lexLt (left ∘ Fin.succ) (right ∘ Fin.succ)))

/-- Lexicographic comparison of selected input leaves uses six gates per coordinate and one
constant gate. Repeated or overlapping selections are allowed. -/
@[simp] theorem size_lexLt {n k : ℕ} (left right : Fin k → Fin n) :
    (lexLt left right).size = 6 * k + 1 := by
  induction k with
  | zero => simp [lexLt]
  | succ k ih =>
    simp only [lexLt, size_or, size_and, size_not, size_input, ih]
    lia

/-- The comparison formula agrees with the lexicographic order, including empty keys. -/
@[simp] theorem eval_lexLt_iff {n k : ℕ} (left right : Fin k → Fin n) (x : BitString n) :
    (lexLt left right).eval interpretation x = true ↔ toLex (x ∘ left) < toLex (x ∘ right) := by
  induction k with
  | zero =>
    have h : ¬ toLex (x ∘ left) < toLex (x ∘ right) := fun ⟨i, _⟩ => i.elim0
    simp [lexLt, h]
  | succ k ih =>
    have hlex (a b : BitString (k + 1)) : toLex a < toLex b ↔
        a 0 < b 0 ∨ a 0 = b 0 ∧ toLex (a ∘ Fin.succ) < toLex (b ∘ Fin.succ) := by
      change Pi.Lex (· < ·) (· < ·) a b ↔
        a 0 < b 0 ∨ a 0 = b 0 ∧ Pi.Lex (· < ·) (· < ·) (Fin.tail a) (Fin.tail b)
      simpa only [Fin.cons_self_tail] using
        (Fin.pi_lex_lt_cons_cons (x₀ := a 0) (y₀ := b 0) (x := Fin.tail a) (y := Fin.tail b)
          (fun {_} => (· < ·)))
    rw [hlex]
    simp only [lexLt, eval_or, eval_and, eval_not, eval_input, Bool.or_eq_true,
      Bool.and_eq_true, ih, Function.comp_apply]
    cases x (left 0) <;> cases x (right 0) <;> simp [Function.comp_def]

end Formula

namespace Boolean

/-- Compare two records by `key`, preserving their order when the keys agree. The comparison
and its negation are shared across all output bits. Empty records use the identity wiring. -/
def compareSwapCircuit {k r : ℕ} (key : Fin k → Fin r) :
    Circuit signature (r + r) (r + r) :=
  if r = 0 then Circuit.id signature (r + r) else
    exchange (Formula.lexLt (Fin.natAdd r ∘ key) (Fin.castAdd r ∘ key)).toCircuit
where
  /-- Retain a flag and compute its negation once. -/
  flagPair : Circuit signature 1 2 :=
    (Circuit.id signature 1).append ((Formula.input (0 : Fin 1)).not.toCircuit)
  /-- Select one of two data wires using a stored flag and its stored negation. -/
  selectBit {n : ℕ} (left right : Fin n) : Formula signature (2 + n) :=
    ((Formula.input (Fin.castAdd n (0 : Fin 2))).and (Formula.input (Fin.natAdd 2 right))).or
      ((Formula.input (Fin.castAdd n (1 : Fin 2))).and (Formula.input (Fin.natAdd 2 left)))
  /-- Swap the two blocks of record wires. -/
  swapInput (r : ℕ) : Fin (r + r) → Fin (r + r) :=
    Fin.addCases (Fin.natAdd r) (Fin.castAdd r)
  /-- Switch two payload blocks using a supplied flag and its supplied complement. -/
  switch (r : ℕ) : Circuit signature (2 + (r + r)) (r + r) :=
    Circuit.pi fun j => (selectBit j (swapInput r j)).toCircuit
  /-- Expose the shared flag and its complement before the exchanged records. -/
  record {r : ℕ} (flag : Circuit signature (r + r) 1) :
      Circuit signature (r + r) (2 + (r + r)) :=
    ((Circuit.wiring signature (Fin.castAdd (r + r))).append (switch r)).comp
      ((flagPair.comp flag).append (Circuit.id signature (r + r)))
  /-- Share a swap flag across every bit of the two records. -/
  exchange {r : ℕ} (flag : Circuit signature (r + r) 1) :
      Circuit signature (r + r) (r + r) :=
    (switch r).comp
      ((flagPair.comp flag).append (Circuit.id signature (r + r)))

open compareSwapCircuit

private theorem eval_flagPair (x : BitString 1) :
    flagPair.eval interpretation x = ![x 0, !x 0] := by
  funext j
  exact Fin.cases rfl (Fin.cases rfl (fun i => i.elim0)) j

private theorem eval_selectBit {n : ℕ} (left right : Fin n) (b : Bool) (x : BitString n) :
    (selectBit left right).eval interpretation (Fin.append ![b, !b] x) =
      if b then x right else x left := by
  cases b <;> simp [selectBit]

/-- The control bits are supplied together: invalid pairs are not asserted to be swaps. -/
theorem compareSwapCircuit.eval_switch (r : ℕ) (b : Bool) (x y : BitString r) :
    (switch r).eval interpretation (Fin.append ![b, !b] (Fin.append x y)) =
      if b then Fin.append y x else Fin.append x y := by
  funext j
  cases b <;> cases j using Fin.addCases <;>
    simp [switch, selectBit, swapInput, -Fin.natAdd_eq_addNat]

/-- Recording returns both existing control wires without duplicating their computation. -/
theorem compareSwapCircuit.eval_record {r : ℕ} (flag : Circuit signature (r + r) 1)
    (x y : BitString r) :
    (record flag).eval interpretation (Fin.append x y) =
      let b := flag.eval interpretation (Fin.append x y) 0
      Fin.append ![b, !b] (if b then Fin.append y x else Fin.append x y) := by
  simp only [record, Circuit.eval_comp, Circuit.eval_append, Circuit.id,
    Circuit.eval_wiring, Function.comp_id, eval_flagPair]
  rw [eval_switch]
  congr 1 with j : 1
  simp

/-- Applying the same saved controls twice restores arbitrary payloads. -/
theorem compareSwapCircuit.switch_involutive (r : ℕ) (b : Bool) (x y : BitString r) :
    (switch r).eval interpretation
      (Fin.append ![b, !b] ((switch r).eval interpretation (Fin.append ![b, !b]
        (Fin.append x y)))) = Fin.append x y := by
  rw [eval_switch]
  cases b with
  | false => simpa using eval_switch r false x y
  | true => simpa using eval_switch r true y x

/-- Switching charges two ANDs and one OR for each output bit. -/
theorem compareSwapCircuit.cost_switch (r : ℕ) (cost : signature.Op → ℕ) :
    (switch r).program.cost cost = 2 * r * (2 * cost .and + cost .or) := by
  simp only [switch, Circuit.cost_program_pi, Formula.cost_toCircuit, selectBit,
    Formula.and, Formula.or, Formula.cost_gate, Formula.cost_input,
    Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  ring

/-- The comparator and one shared negation are charged in addition to switching. -/
theorem compareSwapCircuit.cost_record {r : ℕ} (flag : Circuit signature (r + r) 1)
    (cost : signature.Op → ℕ) :
    (record flag).program.cost cost =
      flag.program.cost cost + cost .not + 2 * r * (2 * cost .and + cost .or) := by
  simp only [record, Circuit.cost_program_comp, Circuit.cost_program_append,
    Circuit.cost_program_wiring, cost_switch, flagPair, Circuit.id, Formula.cost_toCircuit,
    Formula.not, Formula.cost_gate, Formula.cost_input, Fin.sum_univ_one, Matrix.cons_val_zero]
  ring

/-- Exposing the controls adds no gates to `exchange`. Unlike `compareSwapCircuit`, `exchange`
and `record` compute the flag even when the payload width is zero. -/
theorem compareSwapCircuit.cost_record_eq_exchange {r : ℕ}
    (flag : Circuit signature (r + r) 1) (cost : signature.Op → ℕ) :
    (record flag).program.cost cost = (exchange flag).program.cost cost := by
  simp only [record, exchange, Circuit.cost_program_comp, Circuit.cost_program_append,
    Circuit.cost_program_wiring, Nat.zero_add]

private theorem eval_exchange {r : ℕ} (flag : Circuit signature (r + r) 1)
    (x y : BitString r) : (exchange flag).eval interpretation (Fin.append x y) =
      if flag.eval interpretation (Fin.append x y) 0 then Fin.append y x else Fin.append x y := by
  funext j
  simp only [exchange, switch, Circuit.eval_comp, Circuit.eval_pi, Formula.eval_toCircuit,
    Circuit.eval_append, eval_flagPair, Circuit.id, Circuit.eval_wiring, Function.comp_id,
    eval_selectBit]
  cases flag.eval interpretation (Fin.append x y) 0 <;>
    cases j using Fin.addCases <;> simp [swapInput, -Fin.natAdd_eq_addNat]

private theorem size_exchange {r : ℕ} (flag : Circuit signature (r + r) 1) :
    (exchange flag).size = flag.size + 6 * r + 1 := by
  simp only [exchange, switch, Circuit.size_comp, Circuit.size_append, flagPair, Circuit.id,
    Circuit.size_wiring, Formula.size_toCircuit, Formula.size_not, Formula.size_input,
    selectBit, Formula.size_or, Formula.size_and, Circuit.size_pi, Finset.sum_const,
    Finset.card_fin, smul_eq_mul]
  lia

open Classical in
/-- Compare-exchange swaps whole records precisely when the right key precedes the left key. -/
theorem eval_compareSwapCircuit {k r : ℕ} (key : Fin k → Fin r) (x y : BitString r) :
    (compareSwapCircuit key).eval interpretation (Fin.append x y) =
      if toLex (y ∘ key) < toLex (x ∘ key) then Fin.append y x else Fin.append x y := by
  by_cases h : r = 0
  · subst r
    funext j
    exact j.elim0
  · simp only [compareSwapCircuit, h, ↓reduceIte]
    simpa only [Formula.eval_toCircuit, Formula.eval_lexLt_iff, Function.comp_def,
      Fin.append_right, Fin.append_left] using
      eval_exchange (Formula.lexLt (Fin.natAdd r ∘ key) (Fin.castAdd r ∘ key)).toCircuit x y

/-- Exact gate count, including the constant and the shared negation. -/
@[simp] theorem size_compareSwapCircuit {k r : ℕ} (key : Fin k → Fin r) :
    (compareSwapCircuit key).size = if r = 0 then 0 else 6 * k + 6 * r + 2 := by
  by_cases h : r = 0 <;>
    simp only [compareSwapCircuit, h, ↓reduceIte, Circuit.id, Circuit.size_wiring,
      size_exchange, Formula.size_toCircuit, Formula.size_lexLt]
  lia

/-- The selected keys of the two output records are in ascending order. -/
theorem compareSwapCircuit_keys_ordered {k r : ℕ} (key : Fin k → Fin r) (x y : BitString r) :
    let output := (compareSwapCircuit key).eval interpretation (Fin.append x y)
    toLex (fun i => output (Fin.castAdd r (key i))) ≤
      toLex (fun i => output (Fin.natAdd r (key i))) := by
  classical
  dsimp only
  rw [eval_compareSwapCircuit]
  split_ifs with h
  · simpa only [Fin.append_left, Fin.append_right, Function.comp_def] using h.le
  · simpa only [Fin.append_left, Fin.append_right, Function.comp_def] using le_of_not_gt h

/-- Equal keys preserve the entire pair, including payload coordinates outside the key. -/
theorem eval_compareSwapCircuit_of_key_eq {k r : ℕ} (key : Fin k → Fin r)
    (x y : BitString r) (h : x ∘ key = y ∘ key) :
    (compareSwapCircuit key).eval interpretation (Fin.append x y) = Fin.append x y := by
  classical
  rw [eval_compareSwapCircuit, h]
  exact ite_eq_right (lt_irrefl (toLex (y ∘ key)))

end Boolean

end Cslib.Circuits
