/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (list import regression tests)

import Complexity.Foundations.Data.List.Basic

/-! # The combined list import

Every original theorem remains usable from the old `Basic` import alone. The anonymous clients
check elaborated references, so dropping a topic from the re-export fails without another topic
import masking it. Actual library consumers use the narrow topic modules.
-/

example :
    (([1] ++ 2 :: [3]).zip ([1] ++ 2 :: [3]).tail =
        ([1] ++ [2]).zip ([1] ++ [2]).tail ++ (2 :: [3]).zip [3] ∧
      decide (2 ∈ [1, 2, 3]) = ([1, 2, 3].any fun u => decide (u = 2)) ∧
      ([10, 20, 30].set 1 99).getD 1 0 = 99 ∧
      ([10, 20, 30].set 1 99).getD 2 0 = ([10, 20, 30] : List ℕ).getD 2 0 ∧
      [10, 20].getD ([10, 20].idxOf 20) 0 = 20 ∧
      ((List.range 3).map (· + 1)).getD 1 0 = 2 ∧
      (List.range 3).map (fun i : ℕ => i + 1) = List.ofFn (fun i : Fin 3 => i.val + 1) ∧
      ([true, false, true].countP (fun b => ¬ (b = true) ∧ (b = true)) +
        [true, false, true].countP (fun b => (b = true) ∧ (b = true)) =
        [true, false, true].countP (fun b => b = true))) :=
  ⟨List.zip_tail_append_cons [1] 2 [3],
    List.decide_mem_eq_any 2 [1, 2, 3],
    List.getD_set_self (by decide),
    List.getD_set_ne (by decide),
    List.getD_idxOf (by decide) 0,
    List.getD_map_range (· + 1) 0 (by decide),
    List.map_range_eq_ofFn 3 (fun i : ℕ => i + 1),
    List.countP_and_not_add_countP_and (· = true) (· = true) [true, false, true]⟩

example :
    (∀ x ∈ ([1, 2].set 0 3), x ≤ 3) ∧
    [1, 2].getD 1 0 ≤ 2 ∧
    ([1, 2].getD 1 0 ∈ [1, 2] ∨ [1, 2].getD 1 0 = 0) :=
  ⟨List.forall_mem_set_of_forall_mem (by decide) (by decide),
   List.getD_le_of_forall_le (by decide) 1,
   List.getD_mem_or [1, 2] 1 0⟩

-- Recover an unknown unary block and suffix from a concrete encoded word.
example (n : ℕ) (l : List Bool)
    (h : List.replicate n (!true) ++ true :: l = [false, false, true, false]) :
    n = 2 ∧ l = [false] :=
  List.replicate_not_append_cons_inj (m' := 2) h

example (n : ℕ) (l : List Bool)
    (h : List.replicate n true ++ false :: l = [true, true, false, true]) :
    n = 2 ∧ l = [true] :=
  List.replicate_true_append_false_inj (m' := 2) h

example :
    (([1, 2].take 1).foldl (· + ·) 0 ≤ 10 ∧
      ([1, 2].foldr (fun candidate rest => if 1 = candidate then 5 else rest) 0 = 5) ∧
      ([1, 2].flatMap fun x => [x, x]).length ≤ [1, 2].length * 2) :=
  ⟨List.foldl_take_invariant [1, 2] (· + ·) 0 (fun i s => s ≤ i * 10) (by decide)
      (fun i hi s hs => by
        have : [1, 2][i] ≤ 10 := by clear s hs; revert i hi; decide
        omega) 1 (by decide),
   List.foldr_ite_eq_of_mem [1, 2] 1 (fun _ => 5) 0 (by decide),
   List.length_flatMap_le (f := fun x => [x, x]) (fun _ _ => le_rfl)⟩
