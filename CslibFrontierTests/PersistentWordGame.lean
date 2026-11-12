/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.WordGame
import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.AppendAtCursor

/-!
# Persistent work storage in an alternating loop

A universal move erases the move marker in two native steps and reaches acceptance. An arbitrary
payload on the second tape remains untouched with its cursor at its right end; the input cursor
is zero rather than the normalized start. The branch clock is seven independently of payload
length. A separate append check advances the persistent payload cursor in one step.
-/

namespace CslibFrontierTests.PersistentWordGame

open Turing Turing.MultiTapeTM Turing.MultiTapeATM Turing.MultiTapeATM.WordGame

private def round : MultiTapeTM 2 Bool Bool :=
  .ofTr false fun q _ _ =>
    if q then ⟨0, fun i => if i = 0 then (some none, -1) else (none, 0), none, none⟩
    else ⟨0, fun i => if i = 0 then (none, 1) else (none, 0), none, some true⟩

private def store (payload : List Bool) : Cfg 2 Bool Unit [] :=
  ⟨none, 0, fun i => if i = 1 then tapeOfList payload else fun _ => none,
    fun i => if i = 1 then (payload.length : ℤ) else 0, []⟩

private def header (done : Bool) : List Bool := if done then [true] else [true, false]

private theorem round_run (payload : List Bool) (b : Bool) :
    round.runFrom
      ((cfg (S₁ := Bool) (S₂ := Bool) 0 none [true, b] 0 [] (store payload)).withState
        (some round.q₀)) 2 =
      (cfg (S₁ := Bool) (S₂ := Bool) 0 none [true] 0 [] (store payload)).withState none := by
  have herase : Function.update (tapeOfList [true, b]) 1 none = tapeOfList [true] := by
    rw [show tapeOfList [true, b] = Function.update (tapeOfList [true]) 1 (some b) from
      tapeOfList_append_single [true] b, Function.update_idem]
    exact Function.update_eq_self_iff.mpr rfl
  simp [MultiTapeTM.runFrom, Function.iterate_succ_apply', MultiTapeTM.step_of_state,
    MultiTapeTM.tr_ofTr, round, Action.apply, cfg, Cfg.withState, herase, funext_iff]

private theorem rounds (payload : List Bool) :
    StorageRounds round 0 header (fun _ => store payload) (fun _ _ => true) (fun _ => True) := by
  intro a _ u x r he b
  cases a with
  | true => simp [header] at he
  | false =>
    simp only [header, Bool.false_eq_true, ↓reduceIte, List.cons.injEq] at he
    obtain ⟨rfl, rfl, rfl⟩ := he
    exact ⟨trivial, 2, round_run payload b⟩

example (payload : List Bool) :
    ∃ n, (wordGame round round 0).AcceptsWithin n
      (cfg 0 (some .disp0) (header false) 0 [] (store payload)) := by
  apply (accepts_storage_iff (rounds payload) false trivial).mpr
  exact .forallMove false false [] rfl fun _ => .accept true rfl

example (payload : List Bool) :
    (wordGame round round 0).HaltsWithin 7
      (cfg 0 (some .disp0) (header false) 0 [] (store payload)) := by
  apply haltsWithin_storage_of_potential header (fun _ => store payload) (fun _ _ => true)
    (fun _ => True) (fun done => if done then 0 else 5) ?_ false trivial
  intro a _ u x r he b
  cases a with
  | true => simp [header] at he
  | false =>
    simp only [header, Bool.false_eq_true, ↓reduceIte, List.cons.injEq] at he
    obtain ⟨rfl, rfl, rfl⟩ := he
    exact ⟨2, round_run payload b, by decide, trivial⟩

example (payload : List Bool) (b : Bool) :
    (appendAtCursor (1 : Fin 2) b).runFrom ((store payload).withState (some ())) 1 =
      ⟨none, 0, Function.update (store payload).workTapes 1 (tapeOfList (payload ++ [b])),
        Function.update (store payload).workTapePos 1 ((payload.length : ℤ) + 1), []⟩ := by
  exact runFrom_appendAtCursor 1 b 0 _ _ [] payload (by simp [store]) (by simp [store])

end CslibFrontierTests.PersistentWordGame
