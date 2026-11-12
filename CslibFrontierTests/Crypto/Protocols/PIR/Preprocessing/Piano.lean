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
1. Single-pass chunk streaming (`streamChunk`, `foldr_streamChunk_univ`) and `HintTable.Valid`
   on a concrete `2 × 2` database (`Chunk = Fin 2`, `Offset = Fin 2`).
2. Single-query and multi-query online execution (`HintTable.onlineStep`,
   `HintTable.runOnlineSteps`) with concrete bit reconstruction and hint refresh.
3. Adaptive multi-query perfect privacy (`isPerfectlyPrivateWith_pianoScheme`,
   `privacyAdvantage_pianoScheme_eq_zero`), non-adaptive multi-query transcript privacy
   (`eval_queryTranscript_pianoScheme`), and compacted punctured query privacy
   (`eval_compactedQuery_uniform`) on concrete finite chunk/offset types.
4. Sublinear online communication cost (`onlineCommunication_pianoScheme`,
   `onlineCommunication_compacted_pow`).
-/

namespace Cslib.Crypto.Protocols.PIR.Preprocessing.Piano.Tests

open Cslib.Crypto.Protocols.PIR.Preprocessing
open Cslib.Crypto.Protocols.PIR.Preprocessing.Piano

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

/-! ### Ideal-random-set Piano scheme privacy and communication tests -/

/-- Adaptive multi-query perfect privacy for `pianoScheme 4 (Fin 3) (Fin 3)` against any
adaptive malicious server. -/
example :
    (pianoScheme 4 (Fin 3) (Fin 3)).IsPerfectlyPrivateWith
      (ProbComp.uniform (Fin 3 → Fin 3)) :=
  isPerfectlyPrivateWith_pianoScheme

/-- Every Boolean-output adaptive server has zero distinguishing advantage against
`pianoScheme 4 (Fin 3) (Fin 3)` over any number of queries `k`. -/
example (adv : AdaptiveServer (Fin 3 × Fin 3) (Fin 3 → Fin 3) Bool Bool)
    (db : Fin 3 × Fin 3 → Bool) (k : ℕ) :
    (pianoScheme 4 (Fin 3) (Fin 3)).privacyAdvantage
      (ProbComp.uniform (Fin 3 → Fin 3)) adv db k false = 0 :=
  privacyAdvantage_pianoScheme_eq_zero adv db k false

/-- Multi-query non-adaptive transcript privacy for `pianoScheme 4 (Fin 2) (Fin 2)` on the
3-query sequence `[(0, 0), (1, 1), (0, 1)]`. -/
example :
    ProbComp.eval
      ((pianoScheme 4 (Fin 2) (Fin 2)).queryTranscript exampleDB [(0, 0), (1, 1), (0, 1)]) =
      ProbComp.eval (simTranscript (ProbComp.uniform (Fin 2 → Fin 2)) 3) :=
  eval_queryTranscript_pianoScheme exampleDB [(0, 0), (1, 1), (0, 1)]

/-- Compacted punctured query privacy (`√n - 1 = 3` offsets for `4` chunks of size `4`). -/
example (x : Fin 4 × Fin 4) :
    ProbComp.eval (do
      let T ← ProbComp.uniform (Fin 8 → Fin 4 → Fin 4)
      let B ← ProbComp.uniform (Fin 4 → Fin 4)
      pure (compactedOffsets (pianoStepSets x (T, B)).2 x.1)) =
      ProbComp.eval (ProbComp.uniform (Fin 3 → Fin 4)) := by
  rw [eval_compactedQuery_uniform (M₁ := 8) x, ProbComp.eval_uniform]

/-- Online communication cost of `pianoScheme` on `4 × 4` chunks (`n = 16`, `√n = 4`): the
compacted punctured query sends `3` offsets in `Fin (2 ^ 2)` (`6` bits) and receives `1` bit
(`3 * 2 + 1 = 7` bits total). -/
example : onlineCommunication (Fin 3 → Fin (2 ^ 2)) Bool = 3 * 2 + 1 :=
  onlineCommunication_compacted_pow 3 2

/--
info: 'Cslib.Crypto.Protocols.PIR.Preprocessing.Piano.findHint_eq_some' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms findHint_eq_some

end Cslib.Crypto.Protocols.PIR.Preprocessing.Piano.Tests

end
