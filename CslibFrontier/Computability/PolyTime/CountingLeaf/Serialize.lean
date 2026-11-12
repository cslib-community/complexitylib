/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PolyTime.CountingLeaf.Raw
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.AppendWord
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.FromLeftBlank
import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.RewindWork
import Mathlib.Tactic.FinCases

/-!
# Physical serialization of raw counting-leaf queries

Six source words occupy tapes 0–5; tape 6 is the initially blank destination. Each field is
copied at the current destination cursor, so prefixes are never rescanned. The first five fields
are framed and the final index is raw. Sources are preserved, with heads left at their ends.
-/

public section

namespace Cslib.CountingLeaf.Serialize

open Turing Turing.MultiTapeTM

/-- Physical field words, including the singleton carry selector. -/
@[expose] def fields (q : RawInput) : Fin 6 → List Bool :=
  ![q.context, q.count, q.width, q.path, [q.carry], q.bit]

/-- Serialized prefixes after zero through six field phases. -/
@[expose] def prefixWord (q : RawInput) : Fin 7 → List Bool :=
  ![[], frame q.context, frame q.context ++ frame q.count,
    frame q.context ++ frame q.count ++ frame q.width,
    frame q.context ++ frame q.count ++ frame q.width ++ frame q.path,
    frame q.context ++ frame q.count ++ frame q.width ++ frame q.path ++ frame [q.carry],
    encRawInput q]

@[simp] private theorem prefix_full (q : RawInput) : prefixWord q 6 = encRawInput q := rfl

/-- Select one source and the persistent destination. -/
private def tapes (i : Fin 6) : Fin 2 ↪ Fin 7 where
  toFun := ![i.castSucc, 6]
  inj' := by
    intro a b h
    fin_cases a <;> fin_cases b <;> try rfl
    all_goals have hi := i.isLt; have hv := congrArg Fin.val h; simp at hv; omega

@[simp] private theorem tapes_source (i : Fin 6) : tapes i 0 = i.castSucc := rfl
@[simp] private theorem tapes_dest (i : Fin 6) : tapes i 1 = Fin.last 6 := rfl

@[simp] private theorem lastCases_six {α : Sort*} (last : α) (rest : Fin 6 → α) :
    Fin.lastCases last rest (6 : Fin 7) = last := Fin.lastCases_last

/-- One fixed field phase: framing is omitted only for the final index. -/
private noncomputable def phase (i : Fin 6) :=
  (AppendWord.machine (decide (i.val < 5))).extendTapes (tapes i)

/-- Exact storage between field phases, with destination parked at its right blank. -/
@[expose] def stage (input : List Bool) (q : RawInput) (n : Fin 7) (out : List Bool) :
    Cfg 7 Bool Unit input :=
  tapesCfg input (Fin.lastCases (prefixWord q n) (fields q)) 0
    (Fin.lastCases ((prefixWord q n).length : ℤ)
      (fun i => if i.val < n.val then ((fields q i).length : ℤ) else 0)) out

private theorem prefix_next (q : RawInput) (i : Fin 6) :
    prefixWord q i.succ = prefixWord q i.castSucc ++
      AppendWord.fragment (decide (i.val < 5)) (fields q i) := by
  fin_cases i <;> simp [prefixWord, fields, AppendWord.fragment, List.append_assoc]

private theorem view_stage (input : List Bool) (q : RawInput) (i : Fin 6) (out : List Bool) :
    viewCfg (tapes i) (stage input q i.castSucc out) =
      AppendWord.config input (fields q i) (prefixWord q i.castSucc) 0 out := by
  apply Cfg.ext <;> try rfl
  all_goals funext j; fin_cases j <;> simp [viewCfg, stage, AppendWord.config, tapesCfg]

/-- Each physical phase appends exactly its field and advances only its two selected heads. -/
private theorem runsBetween_phase (input : List Bool) (q : RawInput) (i : Fin 6) (out : List Bool) :
    RunsBetween (phase i) (stage input q i.castSucc out) (stage input q i.succ out)
      (AppendWord.clock (decide (i.val < 5)) (fields q i))
      (2 * (AppendWord.clock (decide (i.val < 5)) (fields q i) + 1) + 5) := by
  have h := AppendWord.runsBetween (decide (i.val < 5)) input (fields q i)
    (prefixWord q i.castSucc) out
  rw [← view_stage] at h
  have he := h.extendTapes (tapes i)
  have heq : embed (tapes i)
      (AppendWord.config input (fields q i)
        (prefixWord q i.castSucc ++ AppendWord.fragment (decide (i.val < 5)) (fields q i))
        (fields q i).length out)
      (stage input q i.castSucc out).workTapes (stage input q i.castSucc out).workTapePos =
        stage input q i.succ out := by
    apply embed_tapesCfg
    · intro j
      fin_cases j <;>
        simp [prefix_next]
    · intro j hj
      cases j using Fin.lastCases with
      | last => exact (hj ⟨1, rfl⟩).elim
      | cast j =>
        have hne : j ≠ i := by
          intro hji
          subst j
          exact hj ⟨0, rfl⟩
        have hv : j.val ≠ i.val := fun h => hne (Fin.ext h)
        simp only [Fin.lastCases_castSucc, Pi.zero_apply, Fin.val_castSucc,
          Fin.val_succ, true_and]
        split_ifs <;> (first | rfl | omega)
  rw [heq] at he
  exact he

/-- Six fixed append phases; the machine is independent of the field lengths. -/
private noncomputable def writeMachine :=
  (phase 0).seq ((phase 1).seq ((phase 2).seq ((phase 3).seq ((phase 4).seq (phase 5)))))

/-- Appending all six fields spends one transition per output cell and one final blank test. -/
private theorem runsBetween_write (input : List Bool) (q : RawInput) (out : List Bool) :
    RunsBetween writeMachine (stage input q 0 out) (stage input q 6 out)
      ((encRawInput q).length + 1) (2 * (encRawInput q).length + 44) := by
  have h := (runsBetween_phase input q 0 out).seq
    ((runsBetween_phase input q 1 out).seq ((runsBetween_phase input q 2 out).seq
      ((runsBetween_phase input q 3 out).seq
        ((runsBetween_phase input q 4 out).seq (runsBetween_phase input q 5 out)))))
  convert h using 1 <;> (first | rfl | (simp [AppendWord.clock, fields]; omega))

/-- Serialized destination at its origin; all six preserved sources have heads at their ends. -/
@[expose] def finished (input : List Bool) (q : RawInput) (out : List Bool) :
    Cfg 7 Bool Unit input :=
  tapesCfg input (Fin.lastCases (encRawInput q) (fields q)) 0
    (Fin.lastCases 0 (fun i => ((fields q i).length : ℤ))) out

private noncomputable def rewind :=
  (rewindWork Bool).extendTapes (tapeEmb (Fin.last 6))

private theorem runsBetween_rewind (input : List Bool) (q : RawInput) (out : List Bool) :
    RunsBetween rewind (stage input q 6 out) (finished input q out)
      ((encRawInput q).length + 2) (7 * ((encRawInput q).length + 3)) := by
  apply RunsBetween.of_runFrom
  simp only [rewind, runFrom_tapeEmb, oneTapeCfg, stage, tapesCfg, Cfg.withState,
    extendTapes_q₀, Pi.zero_apply, sub_zero, Fin.lastCases_last]
  rw [prefix_full, runFrom_rewindWork_none _ _ _ rfl le_rfl, embed_tapeEmb]
  apply Cfg.ext <;> try rfl
  all_goals
    funext j
    cases j using Fin.lastCases with
    | last => simp [finished, tapesCfg]
    | cast j =>
      have hn : j.castSucc ≠ (6 : Fin 7) := Fin.castSucc_ne_last j
      simp [finished, tapesCfg, hn]

private noncomputable def core := writeMachine.seq rewind

private theorem runsBetween_core (input : List Bool) (q : RawInput) (out : List Bool) :
    RunsBetween core (stage input q 0 out) (finished input q out)
      (2 * (encRawInput q).length + 3) (9 * (encRawInput q).length + 65) := by
  convert (runsBetween_write input q out).seq (runsBetween_rewind input q out) using 1 <;>
    (first | rfl | omega)

/-- Complete native serializer, including host-input positioning and destination rewind. -/
noncomputable def machine := core.fromLeftBlank

/-- Six source words at their origins, blank destination, host input parked at its left blank. -/
@[expose] def initial (input : List Bool) (q : RawInput) (out : List Bool := []) :
    Cfg 7 Bool Unit input := { stage input q 0 out with inputPos := 0 }

/-- Ready-to-read encoded query on tape 6; host input restored to its left blank. -/
@[expose] def final (input : List Bool) (q : RawInput) (out : List Bool := []) :
    Cfg 7 Bool Unit input := { finished input q out with inputPos := 0 }

/-- All serialization, framing, cursor movement, and final rewinding are charged. -/
theorem runsBetween (input : List Bool) (q : RawInput) (out : List Bool) :
    RunsBetween machine (initial input q out) (final input q out)
      (2 * (encRawInput q).length + 5) (9 * (encRawInput q).length + 93) := by
  exact (runsBetween_core input q out).fromLeftBlank rfl rfl

end Cslib.CountingLeaf.Serialize
