/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/
module

public import CslibFrontier.Crypto.Protocols.PIR.Preprocessing.Basic
public import CslibFrontier.Crypto.Protocols.PIR.Preprocessing.Piano

@[expose] public section

/-! # Tests for Single-Server Preprocessing PIR and the Piano Scheme

Concrete smoke tests exercising:
0. Satisfiability of `Scheme.IsCorrect` and `Scheme.IsPerfectlyPrivateWith` (`downloadScheme`).
1. Single-pass chunk streaming (`streamChunk`, `foldr_streamChunk_univ`) and `HintTable.Valid`
   on a concrete `2 × 2` database (`Chunk = Fin 2`, `Offset = Fin 2`).
2. Single-query and multi-query online execution (`HintTable.onlineStep`,
   `HintTable.runOnlineSteps`) with concrete bit reconstruction and hint refresh.
3. Adaptive multi-query perfect privacy (`isPerfectlyPrivateWith_pianoHybridScheme`,
   `privacyAdvantage_pianoHybridScheme_eq_zero`), non-adaptive multi-query transcript privacy
   (`eval_queryTranscript_pianoHybridScheme`), and compacted punctured query privacy
   (`eval_compactedQuery_uniform`) on concrete finite chunk/offset types.
4. The bridge `HintTable.onlineStep_sets_eq_pianoStepSets` between the full client and the hybrid.
5. Online communication cost (`onlineCommunication_fullQuery_pow`,
   `onlineCommunication_compacted_pow`).
-/

namespace Cslib.Crypto.Protocols.PIR.Preprocessing.Piano.Tests

open Cslib.Crypto.Protocols.PIR.Preprocessing
open Cslib.Crypto.Protocols.PIR.Preprocessing.Piano

/-! ### The generic notions are satisfiable -/

/-- The scheme that downloads the whole database offline and answers every query locally, sending
the server a `Unit` message. It is correct and perfectly private, so neither `Scheme.IsCorrect`
nor `Scheme.IsPerfectlyPrivateWith` is vacuous; it says nothing about Piano. -/
def downloadScheme (ι : Type) : Scheme ι (ι → Bool) Bool Unit Unit where
  preprocess x := pure x
  query h i := pure (h i, ())
  answer _ _ := ()
  reconstruct b _ := b
  refresh h _ _ _ := pure h

example (ι : Type) : (downloadScheme ι).IsCorrect := by
  refine Scheme.isCorrect_of_forall_preprocess fun x is h₀ hmem => ?_
  simp only [downloadScheme, ProbComp.eval_pure, PMF.support_pure,
    Set.mem_singleton_iff] at hmem
  subst hmem
  induction is with
  | nil => exact Scheme.isCorrectFrom_nil _ _ _
  | cons i is ih =>
    refine Scheme.isCorrectFrom_cons fun h' β hmem => ?_
    simp only [Scheme.step, downloadScheme, bind_pure_comp, map_pure, ProbComp.eval_pure,
      PMF.support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    obtain ⟨rfl, rfl⟩ := hmem
    exact ⟨rfl, ih⟩

example (ι : Type) : (downloadScheme ι).IsPerfectlyPrivateWith (pure ()) := by
  intro St adv x k st₀
  simp only [Scheme.realAdaptiveView, downloadScheme, ProbComp.eval_bind, ProbComp.eval_pure,
    PMF.pure_bind]
  induction k generalizing st₀ with
  | zero => simp [Scheme.realAdaptiveFrom, idealAdaptiveView]
  | succ k ih =>
    simp [Scheme.realAdaptiveFrom, idealAdaptiveView, idealAdaptiveStep, Scheme.realAdaptiveStep,
      ih]

/-! ### Concrete 4-bit database (`2` chunks × `2` offsets) -/

/-- Concrete 4-bit database on `Fin 2 × Fin 2`:
`db (0, 0) = true`, `db (0, 1) = false`, `db (1, 0) = true`, `db (1, 1) = true`. -/
def exampleDB : Fin 2 × Fin 2 → Bool
  | (0, 0) => true
  | (0, 1) => false
  | (1, 0) => true
  | (1, 1) => true

/-- Concrete primary hint sets `T₀ = (0, 1)` and `T₁ = (1, 0)` covering all four positions of
`Fin 2 × Fin 2`. -/
def examplePrimarySets : Fin 2 → Fin 2 → Fin 2
  | 0, 0 => 0
  | 0, 1 => 1
  | 1, 0 => 1
  | 1, 1 => 0

/-- Concrete replacement offsets for each chunk. -/
def exampleReplOffsets : Fin 2 → Fin 2 → Fin 2
  | 0, 0 => 1
  | 0, 1 => 0
  | 1, 0 => 0
  | 1, 1 => 1

/-- Concrete backup sets for each chunk. -/
def exampleBackupSets : Fin 2 → Fin 2 → Fin 2 → Fin 2
  | _, k, j => examplePrimarySets k j

/-- Offline preprocessing table for `exampleDB` obtained by streaming chunks `0` and `1`. -/
def exampleTable : HintTable 2 2 (Fin 2) (Fin 2) :=
  streamPreprocess exampleDB examplePrimarySets exampleReplOffsets exampleBackupSets

/-- Single-pass chunk streaming over `[0, 1]` matches `exampleTable`. -/
example :
    (Finset.univ : Finset (Fin 2)).toList.foldr
      (fun j t => streamChunk j (fun δ => exampleDB (j, δ)) t)
      (initHintTable examplePrimarySets exampleReplOffsets exampleBackupSets) =
      exampleTable :=
  foldr_streamChunk_univ exampleDB examplePrimarySets exampleReplOffsets exampleBackupSets

/-- `exampleTable` satisfies `HintTable.Valid exampleDB`. -/
theorem exampleTable_valid : exampleTable.Valid exampleDB :=
  HintTable.valid_streamPreprocess exampleDB examplePrimarySets exampleReplOffsets exampleBackupSets

/-- Concrete verification of `findHint` on `examplePrimarySets`: query `(0, 0)` matches hint `0`
and query `(0, 1)` matches hint `1`. -/
example : findHint examplePrimarySets (0, 0) = some 0 := by decide
example : findHint examplePrimarySets (0, 1) = some 1 := by decide

/-- Concrete single-step online execution on `exampleTable` for query `(0, 0)` reconstructs
`exampleDB (0, 0) = true` and increments chunk `0`'s consumption counter to `1`. -/
example : (exampleTable.onlineStep exampleDB (0, 0)).2 = exampleDB (0, 0) := by decide
example : (exampleTable.onlineStep exampleDB (0, 0)).1.used 0 = 1 := by decide

/-- Concrete two-query sequential online execution on `exampleTable` for `[(0, 0), (0, 1)]`
reconstructs `[true, false] = [exampleDB (0, 0), exampleDB (0, 1)]`. -/
example :
    (exampleTable.runOnlineSteps exampleDB [(0, 0), (0, 1)]).2 =
      [(0, 0), (0, 1)].map exampleDB := by
  decide

/-- Applying `HintTable.onlineStep_correct` to `exampleTable` and query `(1, 0)`. -/
example :
    (exampleTable.onlineStep exampleDB (1, 0)).2 = exampleDB (1, 0) ∧
      (exampleTable.onlineStep exampleDB (1, 0)).1.Valid exampleDB :=
  HintTable.onlineStep_correct (x := (1, 0)) exampleTable_valid ⟨⟨1, rfl⟩, by decide⟩

/-- The full client's server query and refreshed primary table on `exampleTable` for query `(0, 0)`
are the two components of `pianoStepSets`, so the hypotheses of the bridge are satisfiable. -/
example :
    (exampleTable.onlineStep exampleDB (0, 0)).1.primarySets =
        (pianoStepSets (0, 0) (exampleTable.primarySets,
          replaceInChunk (exampleTable.backupSets 0 0) 0 (exampleTable.replOffsets 0 0))).1 ∧
      replaceInChunk (exampleTable.primarySets 0) 0 (exampleTable.replOffsets 0 0) =
        (pianoStepSets (0, 0) (exampleTable.primarySets,
          replaceInChunk (exampleTable.backupSets 0 0) 0 (exampleTable.replOffsets 0 0))).2 :=
  HintTable.onlineStep_sets_eq_pianoStepSets (x := (0, 0)) exampleDB exampleTable
    (by decide) (by decide)

/-! ### Ideal-random-set hybrid privacy and communication tests -/

/-- Adaptive multi-query perfect privacy for `pianoHybridScheme 4 (Fin 3) (Fin 3)` against any
adaptive malicious server. -/
example :
    (pianoHybridScheme 4 (Fin 3) (Fin 3)).IsPerfectlyPrivateWith
      (ProbComp.uniform (Fin 3 → Fin 3)) :=
  isPerfectlyPrivateWith_pianoHybridScheme

/-- Every adaptive server with state `St` and Boolean finalizer `finalize : St → Bool` has zero
distinguishing advantage against `pianoHybridScheme 4 (Fin 3) (Fin 3)` over any number of queries
`k`. -/
example {St : Type} (adv : AdaptiveServer (Fin 3 × Fin 3) (Fin 3 → Fin 3) Bool St)
    (finalize : St → Bool) (db : Fin 3 × Fin 3 → Bool) (k : ℕ) (st₀ : St) :
    (pianoHybridScheme 4 (Fin 3) (Fin 3)).privacyAdvantage
      (ProbComp.uniform (Fin 3 → Fin 3)) adv finalize db k st₀ = 0 :=
  privacyAdvantage_pianoHybridScheme_eq_zero adv finalize db k st₀

/-- Concrete adaptive server with non-Boolean state `ℕ × List (Fin 3 → Fin 3)` (step counter and
recorded query log) and Boolean finalizer inspecting the logged transcript. -/
def transcriptServer : AdaptiveServer (Fin 3 × Fin 3) (Fin 3 → Fin 3) Bool
    (ℕ × List (Fin 3 → Fin 3)) where
  chooseQuery st := pure ((st.1 + 1, st.2), (0, 0))
  onQuery st q := pure ((st.1, q :: st.2), decide (q 0 = 0))

example (db : Fin 3 × Fin 3 → Bool) :
    (pianoHybridScheme 4 (Fin 3) (Fin 3)).privacyAdvantage
      (ProbComp.uniform (Fin 3 → Fin 3)) transcriptServer
      (fun st => decide (st.2.length = 2)) db 2 (0, []) = 0 :=
  privacyAdvantage_pianoHybridScheme_eq_zero transcriptServer
    (fun st => decide (st.2.length = 2)) db 2 (0, [])

/-- Multi-query non-adaptive transcript privacy for `pianoHybridScheme 4 (Fin 2) (Fin 2)` on the
3-query sequence `[(0, 0), (1, 1), (0, 1)]`. -/
example :
    ProbComp.eval
      ((pianoHybridScheme 4 (Fin 2) (Fin 2)).queryTranscript exampleDB [(0, 0), (1, 1), (0, 1)]) =
      ProbComp.eval (simTranscript (ProbComp.uniform (Fin 2 → Fin 2)) 3) :=
  eval_queryTranscript_pianoHybridScheme exampleDB [(0, 0), (1, 1), (0, 1)]

/-- Compacted punctured query privacy (`√n - 1 = 3` offsets for `4` chunks of size `4`). -/
example (x : Fin 4 × Fin 4) :
    ProbComp.eval (do
      let T ← ProbComp.uniform (Fin 8 → Fin 4 → Fin 4)
      let B ← ProbComp.uniform (Fin 4 → Fin 4)
      pure (compactedOffsets (pianoStepSets x (T, B)).2 x.1)) =
      ProbComp.eval (ProbComp.uniform (Fin 3 → Fin 4)) := by
  rw [eval_compactedQuery_uniform (M₁ := 8) x, ProbComp.eval_uniform]

/-- Online communication on `4` chunks of size `4` (`n = 16`, `√n = 4`): the main scheme sends `4`
offsets in `Fin (2 ^ 2)` and receives `1` bit (`9` bits). -/
example : onlineCommunication (Fin 4 → Fin (2 ^ 2)) Bool = 9 :=
  onlineCommunication_fullQuery_pow 4 2

/-- The Appendix A variant on the same database sends `3` offsets (`6` bits) and receives `4` parity
bits (`10` bits). -/
example : onlineCommunication (Fin 3 → Fin (2 ^ 2)) (Fin 4 → Bool) = 10 :=
  onlineCommunication_compacted_pow 3 2

/--
info: 'Cslib.Crypto.Protocols.PIR.Preprocessing.Piano.findHint_eq_some' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms findHint_eq_some

end Cslib.Crypto.Protocols.PIR.Preprocessing.Piano.Tests

end
