/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

import CslibFrontier.Computability.WordRAM.SymbolicExec.CanonicalCall
import CslibFrontier.Computability.WordRAM.Notation
import CslibFrontier.Computability.WordRAM.Subroutine

/-!
# Canonical register-bank continuations

A permuted finite bank writes memory before returning. The caller continues with that actual
memory, using its preserved destination register. Unused caller words may be arbitrarily dirty.
-/

namespace CslibFrontierTests.WordRAMCanonicalCall

open Cslib.WordRAM

private abbrev a : Fin 2 := 0
private abbrev b : Fin 2 := 1
private abbrev dest : Fin 4 := 3
private abbrev out : Fin 4 := 0

private def bank : Fin 2 → Fin 4 := ![2, 0]
private def writeSeven : Code .standard 2 := ram[ a ← #3; b ← #7; *a ← b ]

private theorem writeSeven_spec {w : ℕ} (x : Data 2) (h7 : Fits w 7) :
    ∃ y, ExecWithin w writeSeven x y 3 ∧
      y.mem = Function.update x.mem 3 7 ∧ y.regs 1 = 7 ∧ y.regs 0 = 3 := by
  unfold writeSeven
  wram_exec [h7, h7.of_le (show 3 ≤ 7 by decide)]
  wram_simp [Data.write_mem]

private def caller : Code .standard 4 :=
  .seq (ram[ dest ← #9 ]) (.seq (writeSeven.rename bank) (ram[ *dest ← out ]))

/-- Both stores are visible; outside registers survive without a global bounded-state premise. -/
example {w : ℕ} (x : Data 4) (h9 : Fits w 9) :
    ∃ y, ExecWithin w caller x y 5 ∧ y.mem 3 = 7 ∧ y.mem 9 = 7 ∧
      y.regs 1 = x.regs 1 ∧ y.regs 3 = 9 ∧ y.regs 2 = 3 ∧
      ∀ a, a ≠ 3 → a ≠ 9 → y.mem a = x.mem a := by
  unfold caller
  wram_exec [h9]
  wram_call (writeSeven_spec _ (h9.of_le (by omega))) canonical
    (by decide : bank.Injective) with y ⟨hm, hv, ha⟩
  wram_exec [hv]
  wram_simp [hm, hv, ha, Function.update_apply]
  intro a ha hb
  wram_simp [ha, hb, hm, Function.update_apply]

/-- Canonical calls retain the routine's full allowance. -/
example (x : Data 4) :
    WP 8 (writeSeven.rename bank) x (fun y t => t ≤ 3 ∧ y.mem 3 = 7) := by
  fail_if_success
    have : WP 8 (writeSeven.rename bank) x (fun _ t => t ≤ 2) := by
      wram_call (writeSeven_spec _ (by decide)) canonical
        (by decide : bank.Injective) with y _
      decide
  wram_call (writeSeven_spec _ (by decide)) canonical
    (by decide : bank.Injective) with y ⟨hm, _, _⟩
  wram_simp [hm, Function.update_apply]

/-- An inside-bank register uses the actual returned value, even when it was an input. -/
example (x : Data 4) (y : Data 2) (h : y.regs 0 = 23) :
    (y.extend bank x).regs 2 = 23 := by
  wram_simp [h]

/-- The empty bank preserves every register and still takes the returned memory. -/
example (x : Data 4) (y : Data 0) (i : Fin 4) :
    (y.extend Fin.elim0 x).regs i = x.regs i ∧ (y.extend Fin.elim0 x).mem = y.mem := by
  exact ⟨Data.extend_regs_of_forall_ne _ _ _ (fun j => j.elim0), rfl⟩

/-- Symbolic banks can use the explicit equations without finite-bank evaluation. -/
example {r s : ℕ} (f : Fin r → Fin s) (hf : f.Injective)
    (x : Data s) (y : Data r) (i : Fin r) :
    ((y.set i 23).extend f (x.set (f i) 99)).regs (f i) = 23 := by
  rw [Data.extend_regs_of_eq hf _ _ i (f i) rfl]
  exact Data.set_regs_self y i 23

/-- Colliding bank entries cannot satisfy the canonical call rule's injection premise. -/
example : ¬ Function.Injective (fun _ : Fin 2 => (0 : Fin 4)) := by decide

/-- A register frame alone supplies no memory frame. -/
example : ∃ x : Data 4, ∃ y : Data 2,
    (y.extend bank x).regs 1 = x.regs 1 ∧ (y.extend bank x).mem 8 ≠ x.mem 8 := by
  refine ⟨⟨fun _ => 1000, fun _ => 17⟩, ⟨fun _ => 3, fun _ => 29⟩, ?_, by decide⟩
  wram_simp

end CslibFrontierTests.WordRAMCanonicalCall
