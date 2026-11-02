/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.CountPrime.Exec
import Mathlib.Data.List.GetD

/-!
# Initialized native modular counting

The ordinary input is raw `(n,p)` followed by three canonical signed, row-major matrices.
The real nine-instruction header computes every original pointer and workspace start. The
complete counter then constructs and counts its actual cyclic product. No table, padding
parameter or intermediate fit certificate occurs in the input.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.CountPrime

open Cslib.WordRAM Cslib.WordRAM.Signed

/-- Raw `(n,p)` followed by canonical signed AB, BC and AC payloads in row-major order. -/
@[expose] def inputWords (n p : ℕ) (values : List ℤ) : List ℕ :=
  [n, p] ++ values.map encode

/-- The exact original payload word, including the common zero default beyond the input. -/
theorem input_word (n p : ℕ) (values : List ℤ) (q : ℕ) :
    (Data.init (inputWords n p values) : Data 128).mem (3 + q) = encode (values.getD q 0) := by
  rw [show 3 + q = (2 + q) + 1 by omega, Data.init_mem_succ]
  rw [inputWords, List.getD_append_right _ _ _ _ (by simp)]
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.add_sub_cancel_left]
  exact List.getD_map values 0 encode

/-- The actual header reads only the two original scalar words and computes all array bases. -/
theorem exec_header {W n p : ℕ} (x : Data 128) (hn : x.mem 1 = n) (hp : x.mem 2 = p)
    (hw : Fits W (3 + 3 * (n * n) + 8)) :
    ∃ y, ExecWithin W input x y 9 ∧ y.mem = x.mem ∧
      y.regs Reg.side = n ∧ y.regs Reg.modulus = p ∧
      y.regs Reg.inputAB = 3 ∧ y.regs Reg.inputBC = 3 + n * n ∧
      y.regs Reg.inputAC = 3 + 2 * (n * n) ∧ y.regs Reg.scratch = 3 + 3 * (n * n) := by
  let z := (((((((((x.set Reg.address 1).set Reg.side n).set Reg.address 2).set
    Reg.modulus p).set Reg.cells (n * n)).set Reg.inputAB 3).set
    Reg.inputBC (3 + n * n)).set Reg.inputAC (3 + n * n + n * n)).set
    Reg.scratch (3 + n * n + n * n + n * n))
  have run : ExecWithin W input x z 9 := by
    ram_eval [input, z, hn, hp, hw.of_le (by omega : 1 ≤ _),
      hw.of_le (by omega : 2 ≤ _), hw.of_le (by omega : 3 ≤ _),
      hw.of_le (by omega : n * n ≤ _), hw.of_le (by omega : 3 + n * n ≤ _),
      hw.of_le (by omega : 3 + n * n + n * n ≤ _),
      hw.of_le (by omega : 3 + n * n + n * n + n * n ≤ _),
      Reg.address, Reg.side, Reg.modulus, Reg.cells, Reg.inputAB, Reg.inputBC,
      Reg.inputAC, Reg.scratch]
  refine ⟨z, run, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp +decide [z, Reg.address, Reg.side, Reg.modulus, Reg.cells,
    Reg.inputAB, Reg.inputBC, Reg.inputAC, Reg.scratch, Nat.succ_mul, Nat.add_assoc]

/-- Initialized actual structured execution with original-parameter numerical admission.
Setup, all real computation and the input header are charged; the final halt is excluded. -/
theorem exec_input_at {w n p A : ℕ} (values : List ℤ)
    (hlen : values.length = 3 * (n * n)) (hp : 0 < p)
    (hv : ∀ z ∈ values, z.natAbs ≤ A)
    (hmag : GenericRAM.Signed.Fits w (magnitudeBudget p (Nat.clog 2 n) A : ℤ))
    (hw : Fits (w + 2) (addressBudget n p (Nat.clog 2 n) (3 + 3 * (n * n))
      3 (3 + n * n) (3 + 2 * (n * n)))) :
    InputFits (w + 2) (inputWords n p values) ∧
    ∃ y, ExecWithin (w + 2) entryProgram (.init (inputWords n p values)) y (cost n p + 9) ∧
      y.regs Reg.result = Cslib.Algorithms.ExactTriangle.countZeroMod
        (fun α β : Fin n => values.getD (α.val * n + β.val) 0)
        (fun α β : Fin n => values.getD (n * n + α.val * n + β.val) 0)
        (fun α β : Fin n => values.getD (2 * (n * n) + α.val * n + β.val) 0) p ∧
      y.Bounded (w + 2) ∧
      ∀ d, d < 3 + 3 * (n * n) ∨ memoryEnd n p (Nat.clog 2 n) (3 + 3 * (n * n)) ≤ d →
        y.mem d = (Data.init (inputWords n p values) : Data 128).mem d := by
  let k := Nat.clog 2 n
  have h4 : 0 < 4 ^ k := by positivity
  have h2 : 0 < 2 ^ k := by positivity
  have harea : 0 < 4 ^ k * p := Nat.mul_pos h4 hp
  have hA : A ≤ magnitudeBudget p k A := by unfold magnitudeBudget; omega
  have original (q : ℕ) (hq : q < 3 * (n * n)) : (values.getD q 0).natAbs ≤ A := by
    have hq' : q < values.length := by omega
    have hm : values.getD q 0 ∈ values := by
      rw [List.getD_eq_getElem _ _ hq']
      exact List.getElem_mem hq'
    exact hv _ hm
  have hi : InputFits (w + 2) (inputWords n p values) := by
    refine ⟨?_, ?_⟩
    · simpa only [inputWords, List.length_append, List.length_cons, List.length_nil,
        List.length_map, hlen, Nat.reduceAdd] using
        hw.of_le (by unfold addressBudget; dsimp only [k] at *; omega :
          2 + 3 * (n * n) ≤ _)
    · intro v hm
      rcases List.mem_append.mp hm with hm | hm
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
        rcases hm with rfl | rfl
        · exact hw.of_le (by unfold addressBudget; dsimp only [k] at *; omega)
        · exact hw.of_le (by unfold addressBudget; dsimp only [k] at *; omega)
      · obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hm
        exact (encode_fits (hmag.of_natAbs_le ((hv z hz).trans hA))).mono (by omega)
  obtain ⟨x0, headerRun, memory, hn, hpReg, hAB, hBC, hAC, hs⟩ := exec_header (n := n) (p := p)
    (.init (inputWords n p values)) (by rfl) (by rfl)
    (hw.of_le (by unfold addressBudget; dsimp only [k] at *; omega))
  obtain ⟨y, counterRun, _, result, frame⟩ := exec x0
    (fun i => values.getD i 0) (fun i => values.getD (n * n + i) 0)
    (fun i => values.getD (2 * (n * n) + i) 0)
    hp hn hpReg hAB hBC hAC hs (by omega) (by omega) (by omega)
    (fun i hi => original i (by omega)) (fun i hi => original (n * n + i) (by omega))
    (fun i hi => original (2 * (n * n) + i) (by omega))
    (by intro i hi; rw [memory]; exact input_word n p values i)
    (by
      intro i hi
      rw [memory]
      simpa only [Nat.add_assoc] using input_word n p values (n * n + i))
    (by
      intro i hi
      rw [memory]
      simpa only [Nat.add_assoc] using input_word n p values (2 * (n * n) + i)) hmag hw
  have full : ExecWithin (w + 2) entryProgram (.init (inputWords n p values)) y
      (cost n p + 9) := (headerRun.seq counterRun).mono (by omega)
  refine ⟨hi, y, full, ?_, full.bounded (.init hi), ?_⟩
  · simpa only [Nat.add_assoc] using result
  · intro d hd
    exact (frame d hd).trans (congrFun memory d)

end Cslib.Algorithms.WordRAM.ExactTriangle.CountPrime
