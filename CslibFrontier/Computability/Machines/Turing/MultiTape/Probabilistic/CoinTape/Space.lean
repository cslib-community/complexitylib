/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Machine.Nondeterministic
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Machine.Space

/-!
# Workspace windows for fixed coin tapes

## Main results

* `Turing.MultiTapePTM.workTapePos_runClosedCoins_mem_window`: an all-prefix space bound
  bounds every head reached by a fixed coin tape, including tapes longer than the halting time.
-/

public section

namespace Turing.MultiTapePTM

open MultiTapeMachine

/-- An all-prefix workspace bound contains every head reached using any fixed coin tape. -/
theorem workTapePos_runClosedCoins_mem_window {k : ℕ} {Symbol State : Type}
    {input : List Symbol} (machine : MultiTapePTM k Symbol State) {space : ℕ}
    (hs : machine.toNTM.RunsInSpace input space) (coins : List Bool) (i : Fin k) :
    (machine.runClosedConfigFromCoins coins (machine.initialConfig input)).tapes.workTapePos i ∈
      window space := by
  obtain ⟨p, hhead, -, hlast⟩ :=
    (machine.exists_runPath_toNTM_iff (c := machine.toNTM.initCfg input)).mpr ⟨coins, rfl, rfl⟩
  have hwin := MultiTapeNTM.RunPath.inWindow_of_space_le (p := p) (s := space)
    (fun i => by rw [hhead]; rfl) (hs ⟨p, hhead⟩)
  rw [tapes_runClosedConfigFromCoins, ← initCfg_toNTM, ← hlast]
  exact hwin _ p.last_mem i

end Turing.MultiTapePTM
