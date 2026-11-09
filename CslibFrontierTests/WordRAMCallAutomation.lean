/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

import CslibFrontier.Computability.WordRAM.SymbolicExec.Call
import CslibFrontier.Computability.WordRAM.Notation

/-!
# Contract calls inside symbolic execution

An actual read-only routine is called in a proper register bank from an arbitrary dirty caller.
The continuation writes the returned word to memory and preserves the outside register frame.
The call charges its own instructions; neither a wrong routine nor a smaller total is accepted.
-/

namespace CslibFrontierTests.WordRAMCallAutomation

open Cslib.WordRAM

private abbrev a : Fin 2 := 0
private abbrev b : Fin 2 := 1
private abbrev out : Fin 4 := 0
private abbrev result : Fin 4 := 2
private abbrev dest : Fin 4 := 3

private def readThird : Code .standard 2 := ram[ a ← #3; b ← *a ]

private theorem readThird_spec {w : ℕ} (x : Data 2) (h3 : Fits w 3)
    :
    ∃ y, ExecWithin w readThird x y 2 ∧ y.mem = x.mem ∧ y.regs 1 = x.mem 3 := by
  unfold readThird
  wram_exec [h3]
  wram_simp

private def bank (i : Fin 2) : Fin 4 := ⟨i.val + 1, by omega⟩

private theorem bank_injective : bank.Injective := by
  intro i j h
  apply Fin.ext
  have := congrArg Fin.val h
  dsimp only [bank] at this
  omega

private def caller : Code .standard 4 :=
  .seq (ram[ dest ← #9 ]) (.seq (readThird.rename bank) (ram[ out ← result; *dest ← out ]))

/-- All five actual instructions are charged; arbitrary unused registers/memory need not fit. -/
example {w : ℕ} (x : Data 4) (h9 : Fits w 9) :
    ∃ y, ExecWithin w caller x y 5 ∧ y.mem 9 = x.mem 3 ∧
      y.regs 3 = 9 ∧ ∀ a, a ≠ 9 → y.mem a = x.mem a := by
  unfold caller
  wram_exec [h9]
  wram_call (readThird_spec _ (h9.of_le (by omega))) renamed bank_injective with
    y ⟨⟨hm, hv⟩, hf⟩
  have h3 : y.regs 3 = 9 := hf 3 (by
    intro j hj
    have := congrArg Fin.val hj
    dsimp only [bank] at this
    omega)
  change y.regs result = x.mem 3 at hv
  wram_exec [hv, h3]
  wram_simp [hm, h3]
  intro a ha
  wram_simp [ha, hm]

/-- Existing time-indexed specifications retain their returned charge in the continuation. -/
example {w k : ℕ} {c : Code .standard 4} {x : Data 4}
    (h : WP w c x (fun y t => t ≤ k ∧ y.mem = x.mem)) :
    WP w (.seq c (.op (.copy 0 0))) x (fun y t => t ≤ k + 1 ∧ y.mem = x.mem) := by
  apply WP.seq
  wram_call h with y t ⟨ht, hm⟩
  wram_exec
  wram_simp [ht, hm]

/-- A different routine's theorem cannot cross the named call. -/
example {w : ℕ} (x : Data 2)
    (_h : ∃ y, ExecWithin w (.op (.copy 0 0) : Code .standard 2) x y 1 ∧ True)
    (h3 : Fits w 3) :
    WP w readThird x (fun y t => t = 2 ∧ y.regs 1 = x.mem 3) := by
  fail_if_success wram_call _h with y _
  wram_call (readThird_spec x h3) with y ⟨_, hy⟩
  exact ⟨trivial, hy⟩

/-- The callee's two-instruction allowance cannot be discarded by its continuation. -/
example {w : ℕ} (x : Data 2) (h3 : Fits w 3) :
    WP w readThird x (fun _ t => t ≤ 2) := by
  fail_if_success
    have : WP w readThird x (fun _ t => t ≤ 1) := by
      wram_call (readThird_spec x h3) with y _
      decide
  wram_call (readThird_spec x h3) with y _
  trivial

/-- A real instruction cannot be assigned zero allowance, even with valid word fits. -/
example (x : Data 4) :
    ∃ y, ExecWithin (B := .standard) 8 (ram[ out ← #3 ]) x y 1 ∧ y.regs 0 = 3 := by
  fail_if_success
    have : ∃ y, ExecWithin (B := .standard) 8 (ram[ out ← #3 ]) x y 0 ∧ y.regs 0 = 3 := by
      wram_exec
      wram_simp
  wram_exec
  wram_simp

/-- Polynomial envelopes and calling conventions do not supply missing exact word fits. -/
example : ¬ Fits 2 4 := by decide

end CslibFrontierTests.WordRAMCallAutomation
