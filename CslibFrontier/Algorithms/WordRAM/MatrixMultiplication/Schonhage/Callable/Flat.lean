/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Callable.Input

/-!
# Initialized flat callable products

The same final native data witnesses the charged prefix run, exact physical product words,
restored local original input, protected caller memory and the final halt. The program and its
163 registers are fixed independently of dimensions, runtime base and physical word width.
-/

public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.CallableProduct

open Cslib.WordRAM
open Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- Prepend the two-instruction runtime-base loader to a callable kernel execution and package
the initialized `Runs`, `Executes` and `Data.Bounded` witnesses at the same final state `y`. -/
theorem entry_runs {W b out T : ℕ} {body : Code .standard 163} {inp : List ℕ} {y : Data 163}
    (hi : InputFits W inp) (h1 : Fits W 1)
    (hread : (State.init inp : State 163).data.mem 1 = b)
    (hy : ExecWithin W body
      (((State.init inp : State 163).data.set Reg.address 1).set Reg.base b) y T)
    (hyr : y.regs Reg.result = out) :
    let c : Code .standard 163 :=
      .seq (ram[ Reg.address ← #1; Reg.base ← *Reg.address ]) body
    ∃ n, n ≤ T + 2 ∧
      Runs W (c.program Reg.result) (State.init inp) ⟨c.size, y⟩ n ∧
      Executes W (c.program Reg.result) (State.init inp) out (n + 1) ∧
      y.Bounded W := by
  intro c
  let x := (State.init inp : State 163).data
  let s := (x.set Reg.address 1).set Reg.base b
  have hread' : x.mem 1 = b := hread
  have hs : ExecWithin (B := .standard) W
      (ram[ Reg.address ← #1; Reg.base ← *Reg.address ]) x s 2 := by
    ram_eval [s, h1, hread', Reg.address, Reg.base, Fin.mk.injEq]
  have he : ExecWithin W c x y (2 + T) := hs.seq hy
  have ybound : y.Bounded W := he.bounded (by simpa only [x, State.init] using Data.Bounded.init hi)
  obtain ⟨n, hn, he⟩ := he
  refine ⟨n, by omega, ?_, ?_, ybound⟩
  · simpa only [Nat.zero_add, x, State.init] using he.runs (pc := 0)
      (p := c.program Reg.result) (Program.Contains.self _).append_left
  · simpa only [hyr, x, State.init] using he.executes Reg.result

/-- Actual initialized execution with no computed-layout, bounded-scratch or execution premise.
Every original duplicate request has its own exact physical answer cell. The `n+1` charge
includes the halt reached by the same final data `y` in the prefix `Runs`. -/
theorem runs {W m N : ℕ} (caller : List ℕ)
    (X : Matrix (Fin N) (Fin (D m)) ℤ) (Y : Matrix (Fin (D m)) (Fin N) ℤ)
    (qs : List (Fin N × Fin N)) (hN : D m ^ 18 ≤ N)
    (hX : ∀ i k, 0 ≤ X i k ∧ X i k ≤ 1) (hY : ∀ k j, 0 ≤ Y k j ∧ Y k j ≤ 1)
    (hcaller : ∀ v ∈ caller, Fits W v)
    (hfit : Fits W (inputBase caller + 4 * windowSize N qs.length + 1024)) :
    InputFits W (input caller X Y qs) ∧
    ∃ y n, n ≤ timeBound (m := m) qs + 2 ∧
      Runs W (entryProgram.program Reg.result) (State.init (input caller X Y qs))
        ⟨entryProgram.size, y⟩ n ∧
      Executes W (entryProgram.program Reg.result) (State.init (input caller X Y qs))
        (inputBase caller + QueriedProduct.outputBase (19 * m) m N qs.length) (n + 1) ∧
      y.Bounded W ∧
      (∀ i : Fin qs.length,
        y.mem (inputBase caller + (QueriedProduct.outputBase (19 * m) m N qs.length + i.val)) =
          Signed.encode ((X * Y) (qs.get i).1 (qs.get i).2)) ∧
      (∀ a, a < QueriedProduct.inputEnd m N qs.length →
        y.mem (inputBase caller + a) =
          (State.init (input caller X Y qs) : State 163).data.mem (inputBase caller + a)) ∧
      (∀ a, a < inputBase caller ∨ inputBase caller + windowSize N qs.length ≤ a →
        y.mem a = (State.init (input caller X Y qs) : State 163).data.mem a) := by
  have hi := input_fits caller X Y qs hN hX hY hcaller hfit
  obtain ⟨y, hy, yr, _, _, yv, yi, yf⟩ := exec X Y qs
    (((State.init (input caller X Y qs) : State 163).data.set Reg.address 1).set Reg.base
      (inputBase caller))
    (by simp) (fun a _ => input_word caller X Y qs a) hX hY hN hfit
  obtain ⟨n, hn, hruns, hexec, ybound⟩ := entry_runs hi (hfit.of_le (by omega))
    (by simp [input, State.init, Data.init]) hy yr
  exact ⟨hi, y, n, hn, hruns, hexec, ybound, yv, yi, yf⟩

-- This finite syntactic check visits the fixed 160-register normalization sequence.
set_option maxRecDepth 4096 in
/-- The setup normalization sequence fits within `1024` flat instructions. -/
theorem setup_size : setup.size ≤ 1024 := by decide +kernel

-- This finite syntactic check visits the fixed normalization and reused arithmetic routines.
set_option maxRecDepth 4096 in
/-- The setup normalization sequence never inspects the physical word width. -/
theorem setup_not_readsWidth : ¬setup.ReadsWidth := by decide +kernel

/-- The complete standalone caller has a fixed finite flat program, including halt. -/
theorem program_length_le : (entryProgram.program Reg.result).length ≤ 131072 := by
  have hp := QueriedProduct.program_length_le true
  simp only [Code.program, List.length_append, Code.length_assemble,
    List.length_singleton] at hp ⊢
  have hc := MemoryWindow.size_compile (QueriedProduct.program true)
  have hs := setup_size
  have hi : restoreInput.size = 13 := by decide +kernel
  have ho : returnOutput.size = 13 := by decide +kernel
  simp only [entryProgram, program, Code.size] at *
  omega

/-- The width-independent code computes its own virtual modulus without reading physical width. -/
theorem not_readsWidth : ¬entryProgram.ReadsWidth := by
  have hr : ¬restoreInput.ReadsWidth := by decide +kernel
  have ho : ¬returnOutput.ReadsWidth := by decide +kernel
  simp only [entryProgram, program, Code.ReadsWidth, Op.ReadsWidth,
    MemoryWindow.readsWidth_compile, QueriedProduct.not_readsWidth, setup_not_readsWidth,
    hr, ho, not_false_eq_true, or_self]

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.CallableProduct
