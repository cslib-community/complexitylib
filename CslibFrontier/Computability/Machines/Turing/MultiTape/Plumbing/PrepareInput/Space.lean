/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.PrepareInput
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Machine.Space

/-!
# Workspace of the buffered-input handoff

## Main results

* `Turing.MultiTapeTM.workTapePos_runFrom_prepareInput_mem_window`: the existing marker and
  rewind routines preserve a window containing the buffer, its left boundary and all prior heads.
-/

public section

namespace Turing.MultiTapeTM

variable {k : ℕ} {Symbol State : Type} {input : List Symbol}

/-- Preparing an actual buffered word preserves a head window on every execution prefix.
The bound charges the buffer length independently of the number of execution steps. -/
theorem workTapePos_runFrom_prepareInput_mem_window (mark : Symbol)
    (cfg : Cfg (k + 2) Symbol State input) (word : List Symbol) (bound : ℕ)
    (hword : cfg.workTapes (Fin.natAdd k 0) = tapeOfList word)
    (hhead : cfg.workTapePos (Fin.natAdd k 0) = word.length)
    (hflag : cfg.workTapePos (Fin.natAdd k 1) = 0)
    (hbound : word.length ≤ bound) (hone : 1 ≤ bound)
    (hheads : ∀ i, cfg.workTapePos i ∈ window bound) (steps : ℕ) (i : Fin (k + 2)) :
    ((prepareInput k mark).runFrom
      (cfg.withState (some (prepareInput k mark).q₀)) steps).workTapePos i ∈ window bound := by
  let marker := (markWork Symbol (some mark)).extendTapes (tapeEmb (Fin.natAdd k (1 : Fin 2)))
  let rewind := (rewindWork Symbol).extendTapes (tapeEmb (Fin.natAdd k (0 : Fin 2)))
  let mid : Cfg (k + 2) Symbol MarkWorkState input :=
    { cfg.withState none with
      workTapes := Function.update cfg.workTapes (Fin.natAdd k 1)
        (Function.update (cfg.workTapes (Fin.natAdd k 1)) (-1) (some mark)) }
  have hmark : marker.runFrom (cfg.withState (some marker.q₀)) 2 = mid := by
    simp only [marker, runFrom_tapeEmb, oneTapeCfg, Cfg.withState, extendTapes_q₀,
      runFrom_markWork, embed_tapeEmb]
    simp [mid, Cfg.withState, hflag]
  have hP₀ (m : ℕ) (hm : m < 2) :
      ∀ j, (marker.runFrom (cfg.withState (some marker.q₀)) m).workTapePos j ∈ window bound := by
    intro j
    rcases (show m = 0 ∨ m = 1 by omega) with rfl | rfl
    · exact hheads j
    · simp only [marker, runFrom_tapeEmb, oneTapeCfg, Cfg.withState, extendTapes_q₀,
        embed_tapeEmb]
      by_cases hj : j = Fin.natAdd k (1 : Fin 2)
      · subst j
        simp only [Function.update_self]
        let c : Cfg 1 Symbol MarkWorkState input :=
          ⟨some (markWork Symbol (some mark)).q₀, cfg.inputPos,
            fun _ => cfg.workTapes (Fin.natAdd k 1), fun _ => 0, cfg.output⟩
        have hstep := MultiTapeNTM.Step.workTapePos_le
          ((step_iff (tm := markWork Symbol (some mark)) (c := c)).mpr rfl) (0 : Fin 1)
        have habs := abs_le.mp hstep
        rw [window, Finset.mem_Icc]
        simpa only [runFrom, Function.iterate_one, hflag] using
          (show -(bound : ℤ) ≤ ((markWork Symbol (some mark)).step c).workTapePos 0 ∧
            ((markWork Symbol (some mark)).step c).workTapePos 0 ≤ bound by
              dsimp only [c] at habs ⊢
              constructor <;> omega)
      · simpa only [Function.update_of_ne hj, mid, Cfg.withState] using hheads j
  have hP₁ (n : ℕ) :
      ∀ j, (rewind.runFrom (mid.withState (some rewind.q₀)) n).workTapePos j ∈ window bound := by
    intro j
    simp only [rewind, runFrom_tapeEmb, oneTapeCfg, Cfg.withState, extendTapes_q₀,
      embed_tapeEmb]
    by_cases hj : j = Fin.natAdd k (0 : Fin 2)
    · subst j
      simp only [Function.update_self]
      have hmid : mid.workTapes (Fin.natAdd k 0) = tapeOfList word := by
        simpa [mid] using hword
      have hrew := workTapePos_runFrom_rewindWork (Symbol := Symbol) none
        mid.inputPos (mid.workTapes (Fin.natAdd k 0)) mid.output hmid
        (p := word.length) le_rfl n
      have hmidhead : mid.workTapePos (Fin.natAdd k 0) = word.length := hhead
      rw [hmidhead]
      rw [window, Finset.mem_Icc]
      simp only [Set.mem_Icc] at hrew
      constructor <;> omega
    · simpa only [Function.update_of_ne hj, mid, Cfg.withState] using hheads j
  have h := withState_runFrom_seq (tm₀ := marker) (tm₁ := rewind)
    (P := fun c => ∀ j, c.workTapePos j ∈ window bound) hmark rfl hP₀ hP₁ steps
  exact h i

end Turing.MultiTapeTM
