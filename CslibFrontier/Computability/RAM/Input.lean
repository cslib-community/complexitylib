/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.RAM.Cost
import Mathlib.Data.List.GetD

/-!
# Preparing length-prefixed RAM inputs

The external convention `Cslib.RAM.Input.encode 5 input` reserves five zero scratch registers,
then stores a length header and the input words. Installing this convention is uncharged, as in
the underlying RAM; it is not a certified encoding reduction. The program below charges every
instruction used to relocate the header and words to a fixed address `R ≥ 5` and clear the prefix.
It copies backwards so that overlapping source and destination intervals are safe.

This uses the existing natural-number adaptation of Cook and Reckhow's RAM and its logarithmic
cost measure, not their charged finite-alphabet input/output convention.

## Main definitions

* `Cslib.RAM.Input.encode`: zero prefix, length header, and input words.
* `Cslib.RAM.Input.prepare`: backward relocation followed by prefix clearing.
* `Cslib.RAM.Input.prepareSteps`: the exact number of executed instructions.

## Main results

* `Cslib.RAM.Input.run_prepare_append`: preparation works before arbitrary appended code.
* `Cslib.RAM.Input.time_prepare_append_le`: the charged logarithmic cost of preparation.

## References

* [S. A. Cook and R. A. Reckhow, *Time bounded random access machines*][CookReckhow1973]
-/

@[expose] public section

namespace Cslib.RAM.Input

/-- A zero prefix followed by the input length and input words. Installing this external input
convention incurs no instruction cost. -/
def encode (R : ℕ) (input : List ℕ) : List ℕ :=
  List.replicate R 0 ++ input.length :: input

/-- Relocate the length header and input from address `5` to `R`, then clear registers below `R`.
Registers `0` through `4` hold one, the remaining word count, source and destination pointers,
and the current word. The six-instruction loop copies backwards; the final straight-line block
clears the prefix, including all scratch registers. The correctness theorem requires `5 ≤ R`. -/
def prepare (R : ℕ) : Program :=
  [.const 0 1, .const 2 5, .add 1 5 0, .add 2 2 5, .const 3 R, .add 3 3 5,
   .load 4 2, .store 3 4, .sub 1 1 0, .sub 2 2 0, .sub 3 3 0, .jpos 1 6] ++
    (List.range R).map (fun i => .const i 0)

/-- The number of preparation instructions executed on `input`. -/
def prepareSteps (R : ℕ) (input : List ℕ) : ℕ := 6 + 6 * (input.length + 1) + R

@[simp]
theorem length_prepare (R : ℕ) : (prepare R).length = 12 + R := by
  simp only [prepare, List.length_append, List.length_cons, List.length_nil,
    List.length_map, List.length_range]

-- Above `R + m` the suffix is already relocated; below it the source block is unchanged.
-- The five scratch registers lie below both blocks.
private def copyRegs (R : ℕ) (values : List ℕ) (m v : ℕ) : URM.Regs
  | 0 => 1
  | 1 => m
  | 2 => 4 + m
  | 3 => R - 1 + m
  | 4 => v
  | i + 5 => if R + m ≤ i + 5 then values.getD (i + 5 - R) 0 else values.getD i 0

private def copyState (R : ℕ) (values : List ℕ) (m v : ℕ) : State :=
  ⟨if m = 0 then 12 else 6, copyRegs R values m v⟩

private theorem copyRegs_read_ge {R m v i : ℕ} (values : List ℕ) (hi : 5 ≤ i) :
    (copyRegs R values m v).read i =
      if R + m ≤ i then values.getD (i - R) 0 else values.getD (i - 5) 0 := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hi
  simp [URM.Regs.read, copyRegs, Nat.add_comm]

private theorem copyRegs_read_source {R m v : ℕ} (values : List ℕ) (hR : 5 ≤ R) :
    (copyRegs R values (m + 1) v).read (5 + m) = values.getD m 0 := by
  rw [copyRegs_read_ge values (by lia)]
  simp [show ¬R + (m + 1) ≤ 5 + m by lia, show 5 + m - 5 = m by lia]

private theorem run_copy_round {R : ℕ} (hR : 5 ≤ R) (tail : Program)
    (values : List ℕ) (m v : ℕ) :
    run (prepare R ++ tail) 6 (copyState R values (m + 1) v) =
      copyState R values m (values.getD m 0) := by
  have hsrc := copyRegs_read_source (m := m) (v := v) values hR
  have hdst : R - 1 + (m + 1) = R + m := by lia
  have hd : 5 ≤ R + m := by lia
  have r0 : (copyRegs R values (m + 1) v).read 0 = 1 := rfl
  have r1 : (copyRegs R values (m + 1) v).read 1 = m + 1 := rfl
  have r2 : (copyRegs R values (m + 1) v).read 2 = 5 + m := by
    change 4 + (m + 1) = 5 + m
    lia
  have r3 : (copyRegs R values (m + 1) v).read 3 = R + m := hdst
  norm_num [run, Function.iterate_succ_apply, step, prepare, Instr.exec, copyState,
    r0, r1, r2, r3, hsrc, URM.Regs.write_read_of_ne, show R + m ≠ 0 by lia,
    show R + m ≠ 1 by lia, show R + m ≠ 2 by lia, show R + m ≠ 3 by lia,
    show R + m ≠ 4 by lia, show 0 ≠ R + m by lia, show 1 ≠ R + m by lia,
    show 2 ≠ R + m by lia, show 3 ≠ R + m by lia]
  constructor
  · split <;> split <;> lia
  · funext i
    rcases i with _ | _ | _ | _ | _ | i
    all_goals simp only [URM.Regs.write, Function.update_apply]
    all_goals simp only [copyRegs]
    all_goals split_ifs <;> grind

private theorem run_copy_loop {R : ℕ} (hR : 5 ≤ R) (tail : Program)
    (values : List ℕ) (m v : ℕ) :
    ∃ v', run (prepare R ++ tail) (6 * m) (copyState R values m v) =
      copyState R values 0 v' := by
  induction m generalizing v with
  | zero => exact ⟨v, rfl⟩
  | succ m ih =>
    obtain ⟨v', hv'⟩ := ih (values.getD m 0)
    refine ⟨v', ?_⟩
    rw [show 6 * (m + 1) = 6 + 6 * m by lia, run_add, run_copy_round hR, hv']

private theorem read_padded (R : ℕ) (values : List ℕ) (i : ℕ) :
    (URM.Regs.ofInputs (List.replicate R 0 ++ values)).read i =
      if i < R then 0 else values.getD (i - R) 0 := by
  change (List.replicate R 0 ++ values).getD i 0 = _
  by_cases hi : i < R
  · rw [List.getD_append _ _ _ _ (by simpa using hi), List.getD_replicate 0 hi]
    simp [hi]
  · rw [List.getD_append_right _ _ _ _ (by simp only [List.length_replicate]; lia)]
    simp [hi]

private theorem run_setup {R : ℕ} (hR : 5 ≤ R) (tail : Program) (input : List ℕ) :
    run (prepare R ++ tail) 6 (State.init (encode 5 input)) =
      copyState R (input.length :: input) (input.length + 1) 0 := by
  norm_num [run, Function.iterate_succ_apply, step, prepare, Instr.exec, State.init,
    encode, List.replicate_succ, copyState, URM.Regs.read, URM.Regs.ofInputs,
    URM.Regs.write, Function.update_apply]
  funext i
  rcases i with _ | _ | _ | _ | _ | i
  all_goals norm_num [copyRegs, Function.update_apply, URM.Regs.ofInputs]
  · lia
  · lia
  · intro hi
    rw [List.getElem?_eq_none (by simp only [List.length_cons]; lia),
      List.getElem?_eq_none (by simp only [List.length_cons]; lia)]

private theorem getElem_clear {R i : ℕ} (tail : Program) (hi : i < R) :
    (prepare R ++ tail)[12 + i]? = some (.const i 0) := by
  rw [Nat.add_comm 12 i]
  simp [prepare, List.getElem?_append, hi]

private theorem run_clear {R k : ℕ} (tail : Program) (hk : k ≤ R) (regs : URM.Regs) :
    run (prepare R ++ tail) k ⟨12, regs⟩ =
      ⟨12 + k, fun i => if i < k then 0 else regs.read i⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [run_succ', ih (by lia), step_of_getElem? (getElem_clear tail (by lia))]
    ext1
    · rfl
    · funext i
      simp only [Instr.exec, URM.Regs.write, Function.update_apply, URM.Regs.read]
      split_ifs <;> first | rfl | lia

private theorem time_clear {R k : ℕ} (tail : Program) (hk : k ≤ R) (regs : URM.Regs) :
    time logCost (prepare R ++ tail) k ⟨12, regs⟩ = k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [time_succ', ih (by lia), run_clear tail (by lia),
      stepCost_of_getElem? (getElem_clear tail (by lia))]
    rfl

/-- Before arbitrary appended code, preparation reaches its exact entry point with the relocated
length header and words and a zero prefix. This includes overlapping ranges and empty input. -/
theorem run_prepare_append {R : ℕ} (hR : 5 ≤ R) (tail : Program) (input : List ℕ) :
    run (prepare R ++ tail) (prepareSteps R input) (State.init (encode 5 input)) =
      ⟨(prepare R).length, URM.Regs.ofInputs (encode R input)⟩ := by
  obtain ⟨v, hv⟩ := run_copy_loop hR tail (input.length :: input) (input.length + 1) 0
  rw [prepareSteps, run_add, run_add, run_setup hR, hv]
  change run (prepare R ++ tail) R ⟨12, copyRegs R (input.length :: input) 0 v⟩ = _
  rw [run_clear tail le_rfl, length_prepare]
  ext1
  · rfl
  · funext i
    change (if i < R then 0 else (copyRegs R (input.length :: input) 0 v).read i) =
      (URM.Regs.ofInputs (List.replicate R 0 ++ input.length :: input)).read i
    rw [read_padded]
    by_cases hi : i < R
    · simp [hi]
    · rw [ite_eq_right hi, ite_eq_right hi, copyRegs_read_ge _ (by lia)]
      simp [show R ≤ i by lia]

private theorem time_copy_round_le {R B : ℕ} (hR : 5 ≤ R) (tail : Program)
    (values : List ℕ) (m v : ℕ) (hB : 1 ≤ B)
    (hs : bitLength (5 + m) ≤ B) (hd : bitLength (R + m) ≤ B)
    (hm : bitLength (m + 1) ≤ B) (hm' : bitLength m ≤ B)
    (hv : bitLength (values.getD m 0) ≤ B) :
    time logCost (prepare R ++ tail) 6 (copyState R values (m + 1) v) ≤ 12 * B := by
  have hsrc := copyRegs_read_source (m := m) (v := v) values hR
  have r0 : (copyRegs R values (m + 1) v).read 0 = 1 := rfl
  have r1 : (copyRegs R values (m + 1) v).read 1 = m + 1 := rfl
  have r2 : (copyRegs R values (m + 1) v).read 2 = 5 + m := by
    change 4 + (m + 1) = 5 + m
    lia
  have r3 : (copyRegs R values (m + 1) v).read 3 = R + m := by
    change R - 1 + (m + 1) = R + m
    lia
  norm_num [time_succ, stepCost, run, Function.iterate_succ_apply, step, prepare,
    Instr.exec, copyState, logCost, r0, r1, r2, r3, hsrc, URM.Regs.write_read_of_ne,
    show 0 ≠ R + m by lia, show 1 ≠ R + m by lia,
    show 2 ≠ R + m by lia, show 3 ≠ R + m by lia]
  have h1 : bitLength 1 = 1 := rfl
  simp only [List.getD_eq_getElem?_getD] at hv
  lia

private theorem time_copy_loop_le {R n m b : ℕ} (hR : 5 ≤ R) (tail : Program)
    (values : List ℕ) (v : ℕ) (hm : m ≤ n + 1) (hn : bitLength n ≤ b)
    (hvalues : ∀ i, bitLength (values.getD i 0) ≤ b) :
    time logCost (prepare R ++ tail) (6 * m) (copyState R values m v) ≤
      12 * m * (bitLength (R + 5) + b + 1) := by
  induction m generalizing v with
  | zero => simp
  | succ m ih =>
    have hmn : m ≤ n := by lia
    have hmb : bitLength m ≤ b := (bitLength_mono hmn).trans hn
    have h5 : bitLength 5 ≤ bitLength (R + 5) := bitLength_mono (by lia)
    have hR' : bitLength R ≤ bitLength (R + 5) := bitLength_mono (by lia)
    have h1 : bitLength 1 = 1 := rfl
    have ht := time_copy_round_le (B := bitLength (R + 5) + b + 1) hR tail values m v
      (by lia)
      ((bitLength_add_le 5 m).trans (by lia))
      ((bitLength_add_le R m).trans (by lia))
      ((bitLength_add_le m 1).trans (by lia))
      (by lia) ((hvalues m).trans (by lia))
    have hi := ih (values.getD m 0) (by lia)
    rw [show 6 * (m + 1) = 6 + 6 * m by lia, time_add, run_copy_round hR]
    exact (add_le_add ht hi).trans_eq (by ring)

private theorem time_setup_le {R b : ℕ} (tail : Program) (input : List ℕ)
    (hn : bitLength input.length ≤ b) :
    time logCost (prepare R ++ tail) 6 (State.init (encode 5 input)) ≤
      12 * (bitLength (R + 5) + b + 1) := by
  have h5 : bitLength 5 ≤ bitLength (R + 5) := bitLength_mono (by lia)
  have hR : bitLength R ≤ bitLength (R + 5) := bitLength_mono (by lia)
  have h1 : bitLength 1 = 1 := rfl
  norm_num [time_succ, stepCost, run, Function.iterate_succ_apply, step, prepare,
    Instr.exec, State.init, encode, List.replicate_succ, logCost,
    URM.Regs.read, URM.Regs.ofInputs, URM.Regs.write, Function.update_apply]
  lia

/-- Preparation costs at most a constant depending only on `R` times the number of input words
(including the header) times their bit-length bound. The length bound already implies `1 ≤ b`.
Every relocation and clearing instruction is charged; external input installation remains free. -/
theorem time_prepare_append_le {R b : ℕ} (hR : 5 ≤ R) (tail : Program) (input : List ℕ)
    (hlen : bitLength input.length ≤ b) (hinput : ∀ v ∈ input, bitLength v ≤ b) :
    time logCost (prepare R ++ tail) (prepareSteps R input) (State.init (encode 5 input)) ≤
      (24 + R) * (bitLength (R + 5) + 2) * (input.length + 1) * b := by
  have hb : 1 ≤ b := (one_le_bitLength input.length).trans hlen
  have hvalues (i : ℕ) : bitLength ((input.length :: input).getD i 0) ≤ b := by
    by_cases hi : i < (input.length :: input).length
    · rw [List.getD_eq_getElem _ 0 hi]
      rcases List.mem_cons.mp (List.getElem_mem hi) with h | h
      · rw [h]
        exact hlen
      · exact hinput _ h
    · rw [List.getD_eq_default _ 0 (by lia)]
      exact hb
  obtain ⟨v, hv⟩ := run_copy_loop hR tail (input.length :: input) (input.length + 1) 0
  have hsetup := time_setup_le (R := R) tail input hlen
  have hcopy := time_copy_loop_le hR tail (input.length :: input) 0 le_rfl hlen hvalues
  rw [prepareSteps, time_add, time_add, run_add, run_setup hR, hv]
  change _ + _ + time logCost (prepare R ++ tail) R
    ⟨12, copyRegs R (input.length :: input) 0 v⟩ ≤ _
  rw [time_clear tail le_rfl]
  have hbound : bitLength (R + 5) + b + 1 ≤ (bitLength (R + 5) + 2) * b := by
    nlinarith
  have hcost := add_le_add (add_le_add hsetup hcopy) (Nat.le_refl R)
  refine hcost.trans ?_
  calc
    _ ≤ (24 + R) * (input.length + 1) * (bitLength (R + 5) + b + 1) := by
      have hfirst : 12 * (bitLength (R + 5) + b + 1) ≤
          12 * (input.length + 1) * (bitLength (R + 5) + b + 1) := by
        gcongr
        lia
      have hclear : R ≤ R * ((input.length + 1) * (bitLength (R + 5) + b + 1)) := by
        exact Nat.le_mul_of_pos_right _ (by positivity)
      nlinarith only [hfirst, hclear]
    _ ≤ (24 + R) * (input.length + 1) * ((bitLength (R + 5) + 2) * b) := by gcongr
    _ = _ := by ring

end Cslib.RAM.Input

end
