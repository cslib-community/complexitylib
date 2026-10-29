/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Product

-- Actual native interpreter regressions supplement the general execution proofs.
set_option linter.hashCommand false

namespace ComplexityTests.SchonhageProduct

open Cslib.WordRAM Cslib.WordRAM.Signed
open Cslib.Algorithms.MatrixMultiplication.Schonhage
open Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.QueriedProduct

private def observe {m N : ℕ} (bits : Bool) (L : ℕ)
    (X : Matrix (Fin N) (Fin (D m)) ℤ) (Y : Matrix (Fin (D m)) (Fin N) ℤ)
    (qs : List (Fin N × Fin N)) : Option (List ℤ × Bool) :=
  let data := (State.init (input bits L X Y qs) : State 160).data
  let sentinel := memoryEnd L m N qs.length + 17
  let start := data.write sentinel 91
  ((program bits).eval 32 4096 start).map fun (y, _) =>
    ((List.range qs.length).map (fun i => decode (y.mem (y.regs output + i))),
      decide ((∀ a < inputEnd m N qs.length, y.mem a = data.mem a) ∧ y.mem sentinel = 91))

-- The actual complete pipeline handles an empty original input without a tile division.
#guard observe false 0 (m := 0) (N := 0) (fun _ _ => 0) (fun _ _ => 0) [] ==
  some ([], true)

-- Signed operands and repeated requests survive both producer calls and reconstruction.
#guard observe false 0 (m := 0) (N := 1) (fun _ _ => -3) (fun _ _ => 2)
    [(0, 0), (0, 0), (0, 0)] == some ([-6, -6, -6], true)

-- Raw unsigned entries are doubled by real code before signed encoding, not in the input.
#guard observe true 0 (m := 0) (N := 1) (fun _ _ => 1) (fun _ _ => 1)
    [(0, 0), (0, 0)] == some ([1, 1], true)

-- Distinct tile pointers and returned epochs are reused across all four padded band pairs.
#guard observe false 1 (m := 0) (N := 4)
    (fun i _ => (i.val : ℤ) - 2) (fun _ j => (j.val : ℤ) - 1)
    [(3, 0), (0, 3), (3, 3), (1, 0), (3, 0)] == some ([-1, -4, 2, 1, -1], true)

-- A nonempty inner coordinate makes the pruned kernel visit all ten signed tensor terms.
#guard observe false 1 (m := 1) (N := 2)
    (fun i k => (i.val : ℤ) + k.val - 1) (fun k j => (k.val : ℤ) + j.val - 2)
    [(1, 0), (0, 1), (1, 1), (1, 0)] == some ([2, 6, 8, 2], true)

-- Empty matrices also admit positive tensor depth without any tile division.
#guard observe false 1 (m := 1) (N := 0) (fun _ _ => 0) (fun _ _ => 0) [] ==
  some ([], true)

private def signedX : Matrix (Fin 1) (Fin (D 0)) ℤ := fun _ _ => -3
private def signedY : Matrix (Fin (D 0)) (Fin 1) ℤ := fun _ _ => 2
private def repeated : List (Fin 1 × Fin 1) := [(0, 0), (0, 0), (0, 0)]

-- Kernel-checked execution clients use the same final memory for prefix Runs, halt and values.
example :
    InputFits (admissionWidth 0 0 1 3 3) (input false 0 signedX signedY repeated) ∧
    ∃ y n, n ≤ timeBound (by decide : 0 ≤ 0) repeated ∧
      Runs (admissionWidth 0 0 1 3 3) ((program false).program output)
        (State.init (input false 0 signedX signedY repeated)) ⟨(program false).size, y⟩ n ∧
      Executes (admissionWidth 0 0 1 3 3) ((program false).program output)
        (State.init (input false 0 signedX signedY repeated)) (outputBase 0 0 1 3) (n + 1) ∧
      (∀ i : Fin 3, y.mem (outputBase 0 0 1 3 + i.val) = encode (-6)) := by
  obtain ⟨hi, y, n, hn, hr, he, _, hv, _⟩ := runs_wide (A := 3) (by decide : 0 ≤ 0)
    false signedX signedY repeated (by intro i k; norm_num [signedX])
    (by intro k j; norm_num [signedY]) (by simp) le_rfl
  refine ⟨hi, y, n, hn, hr, he, ?_⟩
  intro i
  have h := hv i
  fin_cases i <;> norm_num [signedX, signedY, repeated, Matrix.mul_apply, D,
    Fin.sum_univ_succ] at h ⊢ <;> exact h

private def thinN (m : ℕ) : ℕ := D m ^ 18
private def thinIndex (m : ℕ) : Fin (thinN m) :=
  ⟨0, Nat.pow_pos (Nat.pow_pos (by decide))⟩
private def thinQuery (m : ℕ) : List (Fin (thinN m) × Fin (thinN m)) :=
  [(thinIndex m, thinIndex m)]

-- A nonempty, fully admitted thin family exists at every inner depth. The input contains
-- literal matrix words and a raw coordinate; the symbolic client does not execute a huge VM run.
example (m : ℕ) :
    InputFits (128 * Nat.clog 2 (thinN m + 3))
      (input (m := m) true (19 * m) (fun _ _ => (0 : ℤ)) (fun _ _ => (0 : ℤ)) (thinQuery m)) ∧
    ∃ y n,
      Runs (128 * Nat.clog 2 (thinN m + 3)) ((program true).program output)
        (State.init (input (m := m) true (19 * m) (fun _ _ => (0 : ℤ)) (fun _ _ => (0 : ℤ))
          (thinQuery m))) ⟨(program true).size, y⟩ n ∧
      Executes (128 * Nat.clog 2 (thinN m + 3)) ((program true).program output)
        (State.init (input (m := m) true (19 * m) (fun _ _ => (0 : ℤ)) (fun _ _ => (0 : ℤ))
          (thinQuery m))) (outputBase (19 * m) m (thinN m) 1) (n + 1) ∧
      ((n + 1 : ℕ) : ℝ) ≤ 4325376 * ((19 * m + 1 : ℕ) : ℝ) * (thinN m : ℝ) ^ 2 /
        (D m : ℝ) ^ (1 / 18 : ℝ) ∧ y.mem (outputBase (19 * m) m (thinN m) 1) = 0 := by
  have hQ : (thinQuery m).length * 2 ^ m ≤ thinN m ^ 2 := by
    calc (thinQuery m).length * 2 ^ m = 2 ^ m := by simp [thinQuery]
      _ ≤ D m := Nat.pow_le_pow_left (by decide : 2 ≤ 4) m
      _ ≤ (D m) ^ 36 := Nat.le_self_pow (by decide : 36 ≠ 0) _
      _ = thinN m ^ 2 := by norm_num [thinN, ← pow_mul]
  obtain ⟨hi, y, n, hr, he, hn, _, hv, _⟩ := runs_thin
    (W := 128 * Nat.clog 2 (thinN m + 3)) (m := m) (A := 0) true
    (fun _ _ => (0 : ℤ)) (fun _ _ => (0 : ℤ)) (thinQuery m) le_rfl hQ
    (by simp) (by simp) (by simp) (by simp [thinQuery, Nat.add_assoc])
  refine ⟨hi, y, n, hr, he, hn, ?_⟩
  have h := hv ⟨0, by simp [thinQuery]⟩
  change y.mem (outputBase (19 * m) m (thinN m) 1) = encode
    (((0 : Matrix (Fin (thinN m)) (Fin (D m)) ℤ) *
      (0 : Matrix (Fin (D m)) (Fin (thinN m)) ℤ)) (thinIndex m) (thinIndex m)) at h
  simpa only [Matrix.zero_mul, Matrix.zero_apply, encode, Int.natAbs_zero,
    Int.lt_irrefl, ↓reduceIte, Nat.mul_zero, Nat.zero_add] using h

-- The sufficient numerical budget has a strict boundary; this is not a necessary runtime width.
example : ¬Fits 29 (wordBudget 0 0 1 3) ∧ Fits 30 (wordBudget 0 0 1 3) := by
  decide +kernel

-- Repeated requests satisfy the distinct-set condition without satisfying occurrence sparsity.
example : repeated.toFinset.card * 2 ^ 0 ≤ 1 ^ 2 ∧ ¬repeated.length * 2 ^ 0 ≤ 1 ^ 2 := by
  decide +kernel

-- Negative integers require signed mode: raw input deliberately represents nonnegative values.
#guard observe false 0 (m := 0) (N := 1) (fun _ _ => -1) (fun _ _ => 2)
    [(0, 0)] == some ([-2], true)
#guard observe true 0 (m := 0) (N := 1) (fun _ _ => -1) (fun _ _ => 2)
    [(0, 0)] == some ([0], true)

private def framedSigned : Data 160 :=
  ((State.init (input false 0 signedX signedY repeated) : State 160).data.write 0 77).write
    (memoryEnd 0 0 1 3) 91

-- A real call accepts an unrelated length/header word and preserves a sentinel exactly at
-- the allocation boundary, while computing the signed products and restoring the whole input.
example : ∃ y : Data 160, ∃ n, n ≤ timeBound (by decide : 0 ≤ 0) repeated ∧
    Runs 34 ((program false).program output) ⟨0, framedSigned⟩
      ⟨(program false).size, y⟩ n ∧
    Executes 34 ((program false).program output) ⟨0, framedSigned⟩
      (outputBase 0 0 1 3) (n + 1) ∧
    y.mem 0 = 77 ∧ y.mem (memoryEnd 0 0 1 3) = 91 ∧
    y.mem (outputBase 0 0 1 3) = encode (-6) := by
  obtain ⟨y, ⟨n, hn, he⟩, hp, hv, hf⟩ := exec (w := 32) (A := 3) (by decide)
    (by decide : 0 ≤ 0) false signedX signedY repeated framedSigned
    (by
      intro a ha hb
      have : a < 13 := by norm_num [inputEnd, repeated, D] at hb ⊢; exact hb
      interval_cases a <;> decide +kernel)
    (by intro i k; norm_num [signedX]) (by intro k j; norm_num [signedY])
    (by simp) (by decide +kernel) (by decide +kernel)
  change Parameters 0 0 1 3 y at hp
  change ∀ a, ¬(inputEnd 0 1 3 ≤ a ∧ a < memoryEnd 0 0 1 3) →
    y.mem a = framedSigned.mem a at hf
  refine ⟨y, n, hn, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [Nat.zero_add] using he.runs (pc := 0)
      (p := (program false).program output) (Program.Contains.self _).append_left
  · simpa only [hp.output] using he.executes output
  · rw [hf 0 (by decide +kernel)]
    decide +kernel
  · rw [hf (memoryEnd 0 0 1 3) (by omega)]
    rfl
  · have h := hv ⟨0, by decide⟩
    norm_num [signedX, signedY, repeated, Matrix.mul_apply, D, Fin.sum_univ_succ] at h ⊢
    exact h

end ComplexityTests.SchonhageProduct
