/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.AppendWord
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.FromLeftBlank
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.ClearWork
import Mathlib.Tactic.FinCases

/-!
# Native updates of a word game's separate control and metadata

The control word is `[player, move]`. A round reads its actual second cell and gathers the query
`[true, move, false] ++ metadata`, the pair encoding of the chosen bit and the metadata. The player
bit is discarded. All tape traversals, rewinds and erasures are executed by finite machines.
-/

public section

namespace Turing.MultiTapeTM.WordGameRound

/-- Scratch tapes followed by control, metadata, query and a boundary marker. -/
@[expose] def tapeWords (k : ℕ) (control metadata query : List Bool) :
    Fin (k + 4) → List Bool :=
  Fin.append (fun _ => []) ![control, metadata, query, []]

/-- Word storage at the ordinary input position, including a temporary query word. -/
@[expose] def queryConfig (k : ℕ) (input control metadata query out : List Bool) :
    Cfg (k + 4) Bool Unit input :=
  tapesCfg input (tapeWords k control metadata query) 0 0 out

/-- Stream-facing storage, parked at the real input's left blank with all work heads at zero. -/
@[expose] def config (k : ℕ) (input control metadata out : List Bool) :
    Cfg (k + 4) Bool Unit input :=
  { queryConfig k input control metadata [] out with inputPos := 0 }

/-- The four named tapes before adding a block of private scratch tapes. -/
@[expose] def phaseCfg (input control metadata query : List Bool) (hm hq : ℤ) (out : List Bool) :
    Cfg 4 Bool Unit input :=
  tapesCfg input ![control, metadata, query, []] 0 ![0, hm, hq, 0] out

/-- Read the chosen bit, writing its framed Boolean encoding to the query tape. -/
private def queryPrefix : MultiTapeTM 4 Bool (Fin 3) :=
  ofTr 0 fun q _ work =>
    if q = 0 then
      ⟨0, ![(none, 1), (none, 0), (some (some true), 1), (none, 0)], none, some 1⟩
    else if q = 1 then
      ⟨0, ![(none, -1), (none, 0), (some (work 0), 1), (none, 0)], none, some 2⟩
    else
      ⟨0, ![(none, 0), (none, 0), (some (some false), 1), (none, 0)], none, none⟩

private theorem runs_prefix (input metadata out : List Bool) (player move : Bool) :
    RunsBetween queryPrefix (phaseCfg input [player, move] metadata [] 0 0 out)
      (phaseCfg input [player, move] metadata [true, move, false] 0 3 out) 3 16 := by
  apply RunsBetween.of_runFrom
  let c₁ := tapesCfg input ![[player, move], metadata, [true], []] 0 ![1, 0, 1, 0] out
  let c₂ := phaseCfg input [player, move] metadata [true, move] 0 2 out
  have h₀ : queryPrefix.step ((phaseCfg input [player, move] metadata [] 0 0 out).withState
      (some 0)) = c₁.withState (some 1) := by
    apply step_tapesCfg (a :=
      ⟨0, ![(none, 1), (none, 0), (some (some true), 1), (none, 0)], none, some 1⟩)
    · simp [queryPrefix]
    · rfl
    · rfl
    · intro i
      fin_cases i <;> try rfl
      simpa using update_shifted_append ([] : List Bool) true 0
    · intro i
      fin_cases i <;> rfl
  have h₁ : queryPrefix.step (c₁.withState (some 1)) = c₂.withState (some 2) := by
    apply step_tapesCfg (a :=
      ⟨0, ![(none, -1), (none, 0), (some (some move), 1), (none, 0)], none, some 2⟩)
    · simp only [queryPrefix, tr_ofTr, Fin.reduceEq, ite_false, ite_true]
      rfl
    · rfl
    · rfl
    · intro i
      fin_cases i <;> try rfl
      simpa using update_shifted_append [true] move 0
    · intro i
      fin_cases i <;> rfl
  have h₂ : queryPrefix.step (c₂.withState (some 2)) =
      (phaseCfg input [player, move] metadata [true, move, false] 0 3 out).withState none := by
    apply step_tapesCfg (a :=
      ⟨0, ![(none, 0), (none, 0), (some (some false), 1), (none, 0)], none, none⟩)
    · simp [queryPrefix]
    · rfl
    · rfl
    · intro i
      fin_cases i <;> try rfl
      simpa using update_shifted_append [true, move] false 0
    · intro i
      fin_cases i <;> rfl
  change queryPrefix.runFrom
    ((phaseCfg input [player, move] metadata [] 0 0 out).withState (some 0))
      (1 + (1 + 1)) = _
  simp only [runFrom_add, runFrom_one, h₀, h₁, h₂]

private def appendEmb : Fin 2 ↪ Fin 4 :=
  ⟨![1, 2], by intro i j h; fin_cases i <;> fin_cases j <;> simp_all⟩

private noncomputable def append := (AppendWord.machine false).extendTapes appendEmb

private theorem runs_append (input control metadata query out : List Bool) :
    RunsBetween append (phaseCfg input control metadata query 0 query.length out)
      (phaseCfg input control metadata (query ++ metadata) metadata.length
        (query ++ metadata).length out)
      (metadata.length + 1) (2 * (metadata.length + 2) + 2) := by
  have hv : viewCfg appendEmb (phaseCfg input control metadata query 0 query.length out) =
      AppendWord.config input metadata query 0 out := by
    apply Cfg.ext <;> try rfl
    all_goals funext i; fin_cases i <;> rfl
  have h₀ := AppendWord.runsBetween false input metadata query out
  rw [← hv] at h₀
  have h := h₀.extendTapes appendEmb
  have he : embed appendEmb
      (AppendWord.config input metadata (query ++ metadata) metadata.length out)
      (phaseCfg input control metadata query 0 query.length out).workTapes
      (phaseCfg input control metadata query 0 query.length out).workTapePos =
      phaseCfg input control metadata (query ++ metadata) metadata.length
        (query ++ metadata).length out := by
    apply embed_tapesCfg
    · intro i
      fin_cases i <;> exact ⟨rfl, rfl, rfl⟩
    · intro i hi
      fin_cases i
      · exact ⟨rfl, rfl, rfl⟩
      · exact (hi ⟨0, rfl⟩).elim
      · exact (hi ⟨1, rfl⟩).elim
      · exact ⟨rfl, rfl, rfl⟩
  simpa only [append, AppendWord.fragment, Bool.false_eq_true, ite_false, AppendWord.clock,
    Nat.one_mul, he] using h

private noncomputable def rewind (i : Fin 4) :=
  (rewindWork Bool).extendTapes (tapeEmb i)

private theorem runs_rewind (input : List Bool) (words : Fin 4 → List Bool)
    (i : Fin 4) (heads : Fin 4 → ℤ) (hi : heads i = (words i).length) (out : List Bool) :
    RunsBetween (rewind i)
      (tapesCfg input words 0 heads out)
      (tapesCfg input words 0 (Function.update heads i 0) out) ((words i).length + 2)
      (4 * ((words i).length + 3)) := by
  apply RunsBetween.of_runFrom
  simp only [rewind, runFrom_tapeEmb, oneTapeCfg, tapesCfg, Cfg.withState,
    extendTapes_q₀, Pi.zero_apply, sub_zero, hi]
  rw [runFrom_rewindWork_none _ _ _ rfl le_rfl, embed_tapeEmb]
  apply Cfg.ext <;> try rfl
  · funext j
    by_cases hj : j = i <;> simp [hj]

private noncomputable def clear (i : Fin 4) :=
  (clearWork Bool).extendTapes (tapeEmb i)

private theorem runs_clear (input : List Bool) (words : Fin 4 → List Bool)
    (i : Fin 4) (out : List Bool) :
    RunsBetween (clear i) (tapesCfg input words 0 0 out)
      (tapesCfg input (Function.update words i []) 0 0 out)
      (3 * ((words i).length + 1)) ((words i).length + 5) := by
  have h := RunsBetween.of_transformsTapes (input := input)
    (transformsTapes_clearWork_tapeEmb i (words i)) (ws := words) rfl 0 out
  obtain ⟨_, _, ⟨rfl, rfl⟩, h⟩ := h
  simpa only [clear, List.append_nil, Nat.add_assoc] using h

/-- Gather the chosen bit and metadata on the query tape, clearing the two source words. -/
noncomputable def gather :=
  queryPrefix.seq (append.seq ((rewind 1).seq ((rewind 2).seq ((clear 0).seq (clear 1)))))

/-- The gather clock charges each copy, rewind and clear pass; the ambient output is preserved. -/
theorem runsBetween_gather (input metadata out : List Bool) (player move : Bool) :
    RunsBetween gather (phaseCfg input [player, move] metadata [] 0 0 out)
      (phaseCfg input [] [] ([true, move, false] ++ metadata) 0 0 out)
      (6 * metadata.length + 23) (11 * metadata.length + 70) := by
  let query := [true, move, false] ++ metadata
  have ha := runs_append input [player, move] metadata [true, move, false] out
  have hr₁ := runs_rewind input ![[player, move], metadata, query, []] 1
    ![0, (metadata.length : ℤ), (query.length : ℤ), 0] rfl out
  have hr₂ := runs_rewind input ![[player, move], metadata, query, []] 2
    ![0, 0, (query.length : ℤ), 0] rfl out
  have hc₀ := runs_clear input ![[player, move], metadata, query, []] 0 out
  have hc₁ := runs_clear input ![[], metadata, query, []] 1 out
  have hu₁ : Function.update ![0, (metadata.length : ℤ), (query.length : ℤ), 0]
      (1 : Fin 4) 0 = ![0, 0, (query.length : ℤ), 0] := by
    ext i; fin_cases i <;> simp
  have hu₂ : Function.update ![0, 0, (query.length : ℤ), 0] (2 : Fin 4) 0 = 0 := by
    ext i; fin_cases i <;> simp
  have hw₀ : Function.update ![[player, move], metadata, query, []] (0 : Fin 4) [] =
      ![[], metadata, query, []] := by
    ext i; fin_cases i <;> simp
  have hw₁ : Function.update ![[], metadata, query, []] (1 : Fin 4) [] =
      ![[], [], query, []] := by
    ext i; fin_cases i <;> simp
  rw [hu₁] at hr₁
  rw [hu₂] at hr₂
  rw [hw₀] at hc₀
  rw [hw₁] at hc₁
  have h := (runs_prefix input metadata out player move).seq
    (ha.seq (hr₁.seq (hr₂.seq (hc₀.seq hc₁))))
  have hz : (![0, 0, 0, 0] : Fin 4 → ℤ) = 0 := by
    ext i; fin_cases i <;> rfl
  convert h using 1 <;> simp [gather, phaseCfg, query, hz] <;> omega

/-- Gather on the four named tapes after a block of untouched scratch tapes. -/
noncomputable def gatherOn (k : ℕ) := gather.extendTapes (Fin.natAddEmb k)

/-- Gathering ignores the private scratch tapes and returns every head to zero. -/
theorem runsBetween_gatherOn (k : ℕ) (input metadata out : List Bool) (player move : Bool) :
    RunsBetween (gatherOn k) (queryConfig k input [player, move] metadata [] out)
      (queryConfig k input [] [] ([true, move, false] ++ metadata) out)
      (6 * metadata.length + 23) (11 * metadata.length + 70 + k) := by
  have hv : viewCfg (Fin.natAddEmb k) (queryConfig k input [player, move] metadata [] out) =
      phaseCfg input [player, move] metadata [] 0 0 out := by
    apply Cfg.ext <;> try rfl
    · funext j z
      simp [viewCfg, queryConfig, phaseCfg, tapeWords, tapesCfg]
    · funext j
      fin_cases j <;> rfl
  have h := runsBetween_gather input metadata out player move
  rw [← hv] at h
  have he : embed (Fin.natAddEmb k)
      (phaseCfg input [] [] ([true, move, false] ++ metadata) 0 0 out)
      (queryConfig k input [player, move] metadata [] out).workTapes
      (queryConfig k input [player, move] metadata [] out).workTapePos =
      queryConfig k input [] [] ([true, move, false] ++ metadata) out := by
    apply embed_tapesCfg
    · intro j
      simp only [Fin.natAddEmb_apply, tapeWords, Fin.append_right, Pi.zero_apply]
      fin_cases j <;> simp
    · intro j hj
      induction j using Fin.addCases with
      | left j => simp [tapeWords]
      | right j => exact (hj ⟨j, rfl⟩).elim
  have h' := h.extendTapes (Fin.natAddEmb k)
  rw [he] at h'
  simpa only [gatherOn, Nat.add_sub_cancel] using h'

end Turing.MultiTapeTM.WordGameRound
