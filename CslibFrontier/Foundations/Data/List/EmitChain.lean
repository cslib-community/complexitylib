/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Data.List.GetD
import Mathlib.Data.List.Range

/-!
# Indexed expansion of block-emitting list recursions

A recursion consumes a prefix, emitting a block at each step and replacing its carry by a
value determined by the step index. The final suffix is passed to a terminal operation.
The expansion retains the order and multiplicity of every emitted block.

## Main results

* `List.eq_flatMap_range_of_emit`: expand such a recursion into an indexed `flatMap`.
-/

public section

namespace List

/-- Expand a block-emitting recursion that leaves `reserve` entries for its terminal operation.
The new carry depends only on the absolute index; it need not equal the emitted value. -/
theorem eq_flatMap_range_of_emit {α β : Type*}
    (f : ℕ → α → List α → List β) (next : ℕ → α)
    (emit : ℕ → α → α → List β) (finish : α → List α → List β) (reserve : ℕ)
    (hshort : ∀ j carry rest, rest.length ≤ reserve → f j carry rest = finish carry rest)
    (hstep : ∀ j carry b rest, reserve < (b :: rest).length →
      f j carry (b :: rest) = emit j carry b ++ f (j + 1) (next j) rest)
    (j : ℕ) (carry : α) (rest : List α) :
    f j carry rest =
      (range (rest.length - reserve)).flatMap (fun i =>
        emit (j + i) (if i = 0 then carry else next (j + (i - 1))) (rest.getD i carry)) ++
      finish (if rest.length - reserve = 0 then carry
        else next (j + (rest.length - reserve - 1))) (rest.drop (rest.length - reserve)) := by
  induction rest generalizing j carry with
  | nil => simp [hshort j carry [] (by simp)]
  | cons b rest ih =>
    by_cases hs : (b :: rest).length ≤ reserve
    · have hz : rest.length + 1 - reserve = 0 := by
        simp only [length_cons] at hs
        omega
      simp [hshort j carry (b :: rest) hs, hz]
    · have hn : (b :: rest).length - reserve = (rest.length - reserve) + 1 := by
        simp only [length_cons] at hs ⊢
        omega
      rw [hstep j carry b rest (by omega), ih]
      simp only [hn, range_succ_eq_map, flatMap_cons, flatMap_map, ite_true,
        getD_cons_zero, Nat.add_zero, drop_succ_cons, Nat.succ_ne_zero, ite_false,
        Nat.add_one_sub_one, append_assoc]
      congr 1
      have hcarry (i : ℕ) :
          (if i = 0 then next j else next (j + 1 + (i - 1))) = next (j + i) := by
        cases i <;> simp [Nat.add_comm, Nat.add_left_comm]
      apply congrArg₂ List.append
      · apply flatMap_congr
        intro i hi
        have hi' : i < rest.length := by
          simp only [mem_range] at hi
          omega
        rw [hcarry i, getD_cons_succ, getD_eq_getElem _ _ hi', getD_eq_getElem _ _ hi']
        congr 1
        omega
      · rw [hcarry]

end List
