/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

import CslibFrontier.Cryptanalysis.AddXNORClasses
import CslibFrontier.Cryptanalysis.AddXNORFlipWeight

/-!
# Reachable-state, class-counter and flip-weight clients

The small exhaustive client quantifies over every width-one input with two
operators. A symbolic client checks width two with three operators. Other cases
check modular wrap, XNOR, unreachable targets, empty
chains, zero width, duplicate witnesses, projection and concentrated balance.
Resource statements expose their actual operation units; they are not native
machine-runtime claims.
-/

public section

open Cslib.Cryptanalysis.AddXNOR
open scoped BigOperators

example : (WordTable.decide 3 [[true, false, false]] [true, true, true]
    [false, false, false]).ret = true := by decide

example : (WordTable.decide 3 [[false, false, false]] [false, false, false]
    [true, true, true]).ret = true := by decide

example : (WordTable.decide 3 [[false, false, false]] [false, false, false]
    [true, false, false]).ret = false := by decide

example : (WordTable.decide 0 [[], [], []] [] []).ret = true := by decide
example : (WordTable.decide 2 [] [true, false] [true, false]).ret = true := by decide
example : (WordTable.decide 2 [] [true, false] [false, true]).ret = false := by decide

/-- A complete width-two client retains unrestricted operator choices. -/
example (as : Fin 3 → BitVec 2) (s t : BitVec 2) :
    (WordTable.decide 2 ((List.ofFn as).map stateKey) (stateKey s) (stateKey t)).ret = true ↔
      Solvable (List.ofFn as) s t :=
  WordTable.decide_correct (List.ofFn as) s t

/-- Kernel enumeration of every one-bit instance with two free operators. -/
example : ∀ (as : Fin 2 → BitVec 1) (s t : BitVec 1),
    (WordTable.decide 1 ((List.ofFn as).map stateKey) (stateKey s) (stateKey t)).ret = true ↔
      ∃ bs : Fin 2 → Bool, eval (steps bs as) s = t := by decide

example {m : ℕ} (as : List (BitVec m)) (s t : BitVec m) :
    (WordTable.decide m (as.map stateKey) (stateKey s) (stateKey t)).time ≤
      (m + 1) * (m + 4) + as.length * (29 * 2 ^ m + 3 * m + 3) + 3 * m + 2 := by
  simpa using WordTable.decide_time_le m (as.map stateKey) (stateKey s) (stateKey t)
    (by intro a ha; obtain ⟨w, _, rfl⟩ := List.mem_map.1 ha; simp [stateKey])

example {m : ℕ} (as : List (List Bool)) (s t : List Bool)
    (hwidth : ∀ a ∈ as, a.length ≤ m) :
    (WordTable.decide m as s t).time ≤ 40 * (as.length + 1) * (m + 1) * 2 ^ m :=
  WordTable.decide_linear_table_work m as s t hwidth

/-- Both branches of a zero-width chain coincide, but all eight witnesses count. -/
example : (WordTable.classCounters [0#0, 0#0, 0#0] 0#0).read 0#0 = 8 := by decide

/-- At width one, the zero-operand chain splits exactly into its two parity classes. -/
example : (WordTable.classCounters [0#1, 0#1, 0#1] 0#1).read 0#1 = 4 ∧
    (WordTable.classCounters [0#1, 0#1, 0#1] 0#1).read 1#1 = 4 := by decide

example : (WordTable.backwardCounters [1#3, 2#3] 0#3).read 5#3 = 1 := by decide
example : (WordTable.backwardCounters [0#0, 0#0, 0#0] 0#0).read 0#0 = 8 := by decide

example {m q : ℕ} (as : Fin q → BitVec m) (s t : BitVec m) :
    (WordTable.classCounters (List.ofFn as) s).read t = solutionCount as s t :=
  WordTable.classCounters_read as s t

example {m p q : ℕ} (hp : p ≤ m) (as : Fin q → BitVec m) (s : BitVec m) (g : BitVec p) :
    (WordTable.classCounters (List.ofFn fun i => (as i).setWidth p)
      (s.setWidth p)).read g = forwardClassCount p as s g :=
  WordTable.projected_classCounters hp as s g

example {m p l r : ℕ} (hp : p ≤ m) (left : Fin l → BitVec m)
    (right : Fin r → BitVec m) (s t : BitVec m) :
    (WordTable.maxMin
      (WordTable.classCounters (List.ofFn fun i => (left i).setWidth p) (s.setWidth p))
      (WordTable.backwardCounters (List.ofFn fun i => (right i).setWidth p)
        (t.setWidth p))).ret = classBalance p left right s t :=
  WordTable.computed_balance hp left right s t

/-- Zero low operands concentrate classes. Balance is not assumed small. -/
example : classBalance 2 (fun _ : Fin 4 => 0#3) (fun _ : Fin 4 => 0#3) 0#3 0#3 = 8 := by
  decide

example : forwardClassCount 0 (fun _ : Fin 3 => 5#4) 2#4 0#0 = 8 := by decide
example : backwardClassCount 0 (fun _ : Fin 3 => 5#4) 2#4 0#0 = 8 := by decide

example (g : BitVec 2) :
    (𝔼 s : BitVec 4, (forwardClassCount 2 (fun _ : Fin 4 => 3#4) s g : ℚ)) = 4 := by
  convert mean_forwardClassCount 2 2 4 (fun _ => 3#4) g using 1; norm_num

example (g : BitVec 2) :
    (𝔼 a : BitVec 4,
      (backwardClassCount 2 (Fin.cons a (fun _ : Fin 3 => 3#4)) 0#4 g : ℚ)) = 4 := by
  convert mean_backwardClassCount 2 2 3 (fun _ => 3#4) 0#4 g using 1; norm_num

/-- An empty suffix has no random operand, so the uniform-class conclusion fails. -/
example : backwardClassCount 1 (Fin.elim0 : Fin 0 → BitVec 2) 0#2 0#1 = 1 ∧
    backwardClassCount 1 (Fin.elim0 : Fin 0 → BitVec 2) 0#2 1#1 = 0 := by decide

example : (𝔼 t : BitVec 0, 𝔼 a : BitVec 0,
    (Cslib.BitString.weight (fun i : Fin 0 =>
      (step false t a ^^^ step true t a).getLsbD i) : ℚ)) = 0 := by
  simpa using expected_operator_flip_weight 0

example : (𝔼 t : BitVec 1, 𝔼 a : BitVec 1,
    (Cslib.BitString.weight (fun i : Fin 1 =>
      (step false t a ^^^ step true t a).getLsbD i) : ℚ)) = 1 := by
  convert expected_operator_flip_weight 1 using 1; norm_num

example : (𝔼 t : BitVec 5, 𝔼 a : BitVec 5,
    (Cslib.BitString.weight (fun i : Fin 5 =>
      (step false t a ^^^ step true t a).getLsbD i) : ℚ)) = 111 / 32 := by
  convert expected_operator_flip_weight 5 using 1; norm_num
