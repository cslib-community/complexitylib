/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ThreeSum.ChanHe.TraversalPending
public import Complexity.Algorithms.WordRAM.ThreeSum.ChanHe.TraversalTime

/-!
# Native dispatch after popping a Chan–He entry

The zero-fuel and empty-array cases execute their actual branch paths. Live calls execute the
complete visit followed by all three native child pushes. No guard is evaluated by a host
program, and skipped entries retain the same charged pop as live entries.

## Main results

* `body_skip`: actual pop and dispatch for every skipped entry.
* `body_live`: the four actual negative branches connect a pop to the complete live suffix.

These control-flow composition proofs are original.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Traversal

open Cslib.WordRAM

private theorem copy_self {w : ℕ} (x : Data 128) :
    Exec (B := .standard) w (.op (.copy (slot 0) (slot 0))) x x 1 := by
  convert (Exec.copy (B := Basis.standard) (w := w) (x := x)
    (d := slot 0) (s := slot 0)) using 1
  ext i <;> simp [Data.set]

/-- Every skipped entry executes the actual seven pops and the appropriate guard path.
The resulting data is exactly the pop result; the self-copy does not change it. -/
theorem body_skip {w : ℕ} {x y : Data 128} {e : Entry}
    (hp : Exec w popFrame x y 99) (hl : e.Loaded y) (hz : y.regs zero = 0)
    (hskip : e.fuel = 0 ∨ (e.data 0).length = 0 ∨
      (e.data 1).length = 0 ∨ (e.data 2).length = 0) :
    ExecWithin w body x y 107 := by
  have hf : y.regs (slot 0) = e.fuel := hl.1
  have hn₀ : y.regs (slot 2) = (e.data 0).length := hl.2.2 0
  have hn₁ : y.regs (slot 4) = (e.data 1).length := hl.2.2 1
  have hn₂ : y.regs (slot 6) = (e.data 2).length := hl.2.2 2
  by_cases h₀ : e.fuel = 0
  · exact (hp.seq (Exec.branch_pos
      (by change y.regs (slot 0) = y.regs zero; omega) (copy_self y))).within.mono (by omega)
  · by_cases h₁ : (e.data 0).length = 0
    · exact (hp.seq (Exec.branch_neg
        (by change ¬y.regs (slot 0) = y.regs zero; omega)
        (Exec.branch_pos (by change y.regs (slot 2) = y.regs zero; omega)
          (copy_self y)))).within.mono (by omega)
    · by_cases h₂ : (e.data 1).length = 0
      · exact (hp.seq (Exec.branch_neg
          (by change ¬y.regs (slot 0) = y.regs zero; omega)
          (Exec.branch_neg (by change ¬y.regs (slot 2) = y.regs zero; omega)
            (Exec.branch_pos (by change y.regs (slot 4) = y.regs zero; omega)
              (copy_self y))))).within.mono (by omega)
      · have h₃ : (e.data 2).length = 0 := by omega
        exact (hp.seq (Exec.branch_neg
          (by change ¬y.regs (slot 0) = y.regs zero; omega)
          (Exec.branch_neg (by change ¬y.regs (slot 2) = y.regs zero; omega)
            (Exec.branch_neg (by change ¬y.regs (slot 4) = y.regs zero; omega)
              (Exec.branch_pos (by change y.regs (slot 6) = y.regs zero; omega)
                (copy_self y)))))).within.mono (by omega)

/-- A live entry takes all four native negative branches before executing the supplied actual
visit and three-push executions. The bound charges the seven pops and eight branch/jump steps. -/
theorem body_live {w T : ℕ} {x a b y : Data 128} {e : Entry}
    (hp : Exec w popFrame x a 99) (hl : e.Loaded a) (hz : a.regs zero = 0)
    (hf : e.fuel ≠ 0) (hn : ∀ j, (e.data j).length ≠ 0)
    (hv : ExecWithin w visit a b T) (hc : Exec w pushChildren b y 207) :
    ExecWithin w body x y (T + 314) := by
  obtain ⟨t, ht, he⟩ := hv
  have hg₀ : ¬(Cond.eq (slot 0) zero).Holds a := by
    change a.regs (slot 0) ≠ a.regs zero
    rw [hl.1, hz]
    exact hf
  have hg (j : Fin 3) : ¬(Cond.eq (arrayLength j) zero).Holds a := by
    change a.regs (arrayLength j) ≠ a.regs zero
    rw [hl.2.2 j, hz]
    exact hn j
  have he' : Exec w body x y (99 + (t + 207 + 2 + 2 + 2 + 2)) :=
    hp.seq (Exec.branch_neg hg₀ (Exec.branch_neg (hg 0) (Exec.branch_neg (hg 1)
      (Exec.branch_neg (hg 2) (he.seq hc)))))
  exact he'.within.mono (by omega)

end Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Traversal
