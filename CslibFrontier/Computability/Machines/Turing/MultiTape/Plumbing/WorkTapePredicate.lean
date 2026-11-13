/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.InputFromTape
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.FromLeftBlank
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.Deterministic
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Native Boolean predicates on serialized work-tape queries

The query is already serialized at cell zero of a designated work tape. A native predicate whose
run restores blank scratch and all heads runs through `inputFromWord`, with a private marker tape.
Two real transitions position and restore the host input head. The six added transitions include
both marker writes, marker cleanup, and both host-head movements. Serialization is a separate
charged prerequisite.
-/

public section

namespace Turing.MultiTapeTM.WorkTapePredicate

variable {k : ℕ} {S : Type}

/-- Run the predicate on a work-tape word, beginning and ending at the host input's left blank. -/
noncomputable def machine (tm : MultiTapeTM k Bool S) :=
  (tm.inputFromWord true).fromLeftBlank

/-- Serialized input on tape `Fin.natAdd k 0`, all work heads at zero, all other tapes blank,
and the host input head at its left blank. The output argument is an existing prefix. -/
@[expose] def config (outer word : List Bool) (out : List Bool := []) :
    Cfg (k + 2) Bool Unit outer :=
  { tapesCfg outer (Function.update (fun _ => []) (Fin.natAdd k 0) word) 0 0 out with
    inputPos := 0 }

/-- The runner preserves the serialized query, clears its private scratch and marker, restores
all heads, and appends precisely the predicate's output. Its overhead is six native transitions. -/
theorem runsBetween {tm : MultiTapeTM k Bool S} {word result : List Bool} {t s : ℕ}
    (h : RunsBetween tm (tapesCfg word (fun _ => []) 0 0 [])
      (tapesCfg word (fun _ => []) 0 0 result) t s) (outer out : List Bool) :
    RunsBetween (machine tm) (config outer word out) (config outer word (out ++ result))
      (t + 6) (s + 2 * (word.length + 2) + 6 * k + 16) := by
  let ws : Fin (k + 2) → List Bool := Function.update (fun _ => []) (Fin.natAdd k 0) word
  have hc := transformsTapes_inputFromWord_of_runFrom (M := tm) (w := word) (e := result)
    (ws₀ := fun _ => []) (ws₁ := fun _ => []) (t := t) (s := s) true
    (by simpa only [tapesCfg_zero_withState] using h.1)
    (by simpa only [tapesCfg_zero_withState] using h.2)
  obtain ⟨ws', emitted, ⟨hw, he⟩, hr⟩ :=
    RunsBetween.of_transformsTapes (input := outer) hc (ws := ws)
      (by rw [append_nil_eq_update]) 0 out
  have hw' : ws' = ws := by simpa only [append_nil_eq_update] using hw
  rw [hw', he] at hr
  convert hr.fromLeftBlank rfl rfl using 1 <;> (first | rfl | omega)

/-- Duplicating the runner's transitions produces a native alternating leaf with no additional
clock overhead. A singleton Boolean output accepts exactly when that Boolean is true. -/
theorem acceptsWithin {tm : MultiTapeTM k Bool S} {word : List Bool} {answer : Bool} {t s : ℕ}
    (h : RunsBetween tm (tapesCfg word (fun _ => []) 0 0 [])
      (tapesCfg word (fun _ => []) 0 0 [answer]) t s) (outer : List Bool) :
    (MultiTapeATM.ofTMs (fun _ => machine tm) (fun _ => false)).AcceptsWithin (t + 6)
      ((config outer word).withState (some (machine tm).q₀)) ↔ answer = true := by
  rw [MultiTapeATM.acceptsWithin_ofTMs_const_iff, (runsBetween h outer []).1]
  simp [config, tapesCfg, Cfg.withState]

/-- The same native budget bounds all alternating branches, regardless of the returned bit. -/
theorem haltsWithin {tm : MultiTapeTM k Bool S} {word : List Bool} {answer : Bool} {t s : ℕ}
    (h : RunsBetween tm (tapesCfg word (fun _ => []) 0 0 [])
      (tapesCfg word (fun _ => []) 0 0 [answer]) t s) (outer : List Bool) :
    (MultiTapeATM.ofTMs (fun _ => machine tm) (fun _ => false)).HaltsWithin (t + 6)
      ((config outer word).withState (some (machine tm).q₀)) := by
  rw [MultiTapeATM.haltsWithin_ofTMs_const_iff, (runsBetween h outer []).1]
  rfl

/-- Every native polynomial-time Boolean predicate has one finite work-tape runner. Its clock
is bounded by a polynomial in the serialized input length; constructing that serialization is
not part of this theorem. The same runner works with any unrelated host input. -/
theorem exists_of_polyTime {α : Type} {enc : α ↪ List Bool} {f : α → Bool}
    (hf : ComputableInPolyTime f enc encBool) :
    ∃ (k : ℕ) (S : Type) (_ : Finite S) (runner : MultiTapeTM (k + 2) Bool S)
      (c d : ℕ), ∀ (a : α) (outer : List Bool),
        runner.runFrom ((config outer (enc a)).withState (some runner.q₀))
          (c * ((enc a).length + 1) ^ d) =
          (config outer (enc a) [f a]).withState none := by
  obtain ⟨t, s, ht, _, k, S, hS, tm, htm⟩ := hf.tidy
  obtain ⟨c, d, hbound⟩ := (ht.add (PolyBounded.const 6)).exists_le
  refine ⟨k, _, inferInstance, machine tm, c, d, ?_⟩
  intro a outer
  have hrun : RunsBetween tm (tapesCfg (enc a) (fun _ => []) 0 0 [])
      (tapesCfg (enc a) (fun _ => []) 0 0 (encBool (f a))) (t a) (s a) := by
    simpa only [RunsBetween, tapesCfg_zero_withState] using computesTidily_iff_runFrom.mp (htm a)
  have hr := (runsBetween hrun outer []).1
  rw [runFrom_eq_of_halt _ _ (hbound a) (by rw [hr]; rfl), hr]
  simp only [encBool_apply, List.nil_append]

/-- The extracted work-tape predicate is also one finite native alternating leaf, with a
polynomial all-branch bound and exact singleton-output acceptance. -/
theorem exists_alternating_of_polyTime {α : Type} {enc : α ↪ List Bool} {f : α → Bool}
    (hf : ComputableInPolyTime f enc encBool) :
    ∃ (k : ℕ) (S : Type) (_ : Finite S) (runner : MultiTapeATM (k + 2) Bool S)
      (c d : ℕ), ∀ (a : α) (outer : List Bool),
        (runner.AcceptsWithin (c * ((enc a).length + 1) ^ d)
          ((config outer (enc a)).withState (some runner.toPTM.toNTM.q₀)) ↔ f a = true) ∧
        runner.HaltsWithin (c * ((enc a).length + 1) ^ d)
          ((config outer (enc a)).withState (some runner.toPTM.toNTM.q₀)) := by
  obtain ⟨k, S, hS, tm, c, d, htm⟩ := exists_of_polyTime hf
  refine ⟨k, S, hS, MultiTapeATM.ofTMs (fun _ => tm) (fun _ => false), c, d, ?_⟩
  intro a outer
  constructor
  · rw [MultiTapeATM.acceptsWithin_ofTMs_const_iff]
    change (tm.runFrom ((config outer (enc a)).withState (some tm.q₀)) _).state = none ∧
      (tm.runFrom ((config outer (enc a)).withState (some tm.q₀)) _).output = [true] ↔ _
    rw [htm]
    simp [config, tapesCfg, Cfg.withState]
  · rw [MultiTapeATM.haltsWithin_ofTMs_const_iff]
    change (tm.runFrom ((config outer (enc a)).withState (some tm.q₀)) _).state = none
    rw [htm]
    rfl

end Turing.MultiTapeTM.WorkTapePredicate
