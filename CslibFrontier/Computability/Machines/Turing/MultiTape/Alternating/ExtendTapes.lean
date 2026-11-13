/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.GuessVerify
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.ExtendTapesView

/-!
# Reserving work tapes for alternating machines

The deterministic tape compiler reindexes each of the two native transitions. Every branch keeps
its player, clock, and output; all additional tapes and their head positions remain untouched.
This lets an alternating continuation run beside metadata belonging to an enclosing controller.
-/

public section

namespace Turing.MultiTapeATM

variable {k K : ℕ} {S : Type} {input : List Bool}

/-- Run on the selected tapes using the existing deterministic tape compiler for both moves. -/
@[expose] noncomputable def extendTapes (atm : MultiTapeATM k Bool S) (e : Fin k ↪ Fin K) :
    MultiTapeATM K Bool S :=
  ofTMs (fun b => (atm.toPTM.withCoin b).toTM.extendTapes e) atm.universal

/-- Each native move commutes with embedding the actual storage, including arbitrary extra tapes. -/
theorem next_embed (atm : MultiTapeATM k Bool S) (e : Fin k ↪ Fin K)
    (c : Cfg k Bool S input) (extra : Fin K → ℤ → Option Bool) (pos : Fin K → ℤ) (b : Bool) :
    (atm.extendTapes e).next b (MultiTapeTM.embed e c extra pos) =
      MultiTapeTM.embed e (atm.next b c) extra pos := by
  rw [extendTapes, next_ofTMs]
  exact MultiTapeTM.step_iff.mp
    ((MultiTapeTM.embedHom (atm.toPTM.withCoin b).toTM e extra pos).map_rel
      (MultiTapeTM.step_iff.mpr rfl))

/-- Extra tapes preserve bounded acceptance at exactly the same clock. -/
theorem acceptsWithin_embed_iff (atm : MultiTapeATM k Bool S) (e : Fin k ↪ Fin K)
    (n : ℕ) (c : Cfg k Bool S input) (extra : Fin K → ℤ → Option Bool) (pos : Fin K → ℤ) :
    (atm.extendTapes e).AcceptsWithin n (MultiTapeTM.embed e c extra pos) ↔
      atm.AcceptsWithin n c := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    cases hs : c.state with
    | none => simp [AcceptsWithin, MultiTapeTM.embed, hs]
    | some q =>
      have hstate : (MultiTapeTM.embed e c extra pos).state = some q := hs
      simp only [AcceptsWithin, hstate, hs]
      change (if atm.universal q then ∀ b, _ else ∃ b, _) ↔ _
      simp only [next_embed, ih]

/-- Extra tapes preserve all-branch halting, including unsuccessful existential guesses. -/
theorem haltsWithin_embed_iff (atm : MultiTapeATM k Bool S) (e : Fin k ↪ Fin K)
    (n : ℕ) (c : Cfg k Bool S input) (extra : Fin K → ℤ → Option Bool) (pos : Fin K → ℤ) :
    (atm.extendTapes e).HaltsWithin n (MultiTapeTM.embed e c extra pos) ↔ atm.HaltsWithin n c := by
  induction n generalizing c with
  | zero => simp [haltsWithin_zero, MultiTapeTM.embed]
  | succ n ih => simp only [haltsWithin_succ, next_embed, ih]

/-- Read bounded acceptance through the selected tapes of an arbitrary ambient configuration. -/
theorem acceptsWithin_extendTapes_iff (atm : MultiTapeATM k Bool S) (e : Fin k ↪ Fin K)
    (n : ℕ) (c : Cfg K Bool S input) :
    (atm.extendTapes e).AcceptsWithin n c ↔ atm.AcceptsWithin n (MultiTapeTM.viewCfg e c) := by
  have h := acceptsWithin_embed_iff atm e n (MultiTapeTM.viewCfg e c) c.workTapes c.workTapePos
  rwa [MultiTapeTM.embed_viewCfg] at h

/-- Read all-branch halting through the selected tapes of an arbitrary ambient configuration. -/
theorem haltsWithin_extendTapes_iff (atm : MultiTapeATM k Bool S) (e : Fin k ↪ Fin K)
    (n : ℕ) (c : Cfg K Bool S input) :
    (atm.extendTapes e).HaltsWithin n c ↔ atm.HaltsWithin n (MultiTapeTM.viewCfg e c) := by
  have h := haltsWithin_embed_iff atm e n (MultiTapeTM.viewCfg e c) c.workTapes c.workTapePos
  rwa [MultiTapeTM.embed_viewCfg] at h

end Turing.MultiTapeATM
