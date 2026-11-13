/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.ScheduleBits
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Combinators.Transducer
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.KernelOnWords
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Native extraction of a raw movement-schedule column

For fixed machine tape count and selected head, finite control skips the row prefix, copies the
two selected movement bits, and skips the row suffix. The schedule length and contents are not
compiled into the controller. Existing transducer and word adapters supply a concrete native
machine that preserves the full raw source, writes the column, and restores every head.

The raw-word clock is `4*N+M+14`, where `N` and `M` are the source and output cell counts.
Correctness is specified on canonical encoded rows; the extractor does not claim to validate
arbitrary malformed input or convert a packed binary natural into raw rows for free.
-/

public section

namespace Turing.MultiTapeTM.ScheduleColumn

/-- Finite control for one fixed-width pair field. -/
inductive Phase (left right : ℕ)
  /-- Number of prefix cells still to skip. Zero copies the first selected bit. -/
  | before : Fin (left + 1) → Phase left right
  /-- Copy the second selected bit. -/
  | second : Phase left right
  /-- One more than this value is the number of suffix cells still to skip. -/
  | after : Fin right → Phase left right
  deriving Fintype

private def afterState (left right n : ℕ) (hn : n ≤ right) : Phase left right :=
  if hz : n = 0 then .before ⟨left, by omega⟩ else .after ⟨n - 1, by omega⟩

/-- Copy a two-bit field between fixed-width prefix and suffix fields in every row. -/
def reader (left right : ℕ) : Transducer Bool (Phase left right) where
  q₀ := .before ⟨left, by omega⟩
  step q b := match q with
    | .before i => if hz : i.val = 0 then (.second, [b])
      else (.before ⟨i.val - 1, by omega⟩, [])
    | .second => (afterState left right right le_rfl, [b])
    | .after i => (afterState left right i.val (by omega), [])
  final _ := []
  length_step_le q b := by
    cases q with
    | before i => dsimp only; split_ifs <;> simp
    | second => simp
    | after i => simp
  length_final_le _ := by simp

private theorem run_before (left right : ℕ) (pre rest : List Bool) (hp : pre.length ≤ left) :
    (reader left right).run (.before ⟨pre.length, by omega⟩) (pre ++ rest) =
      (reader left right).run (.before 0) rest := by
  induction pre with
  | nil => rfl
  | cons b pre ih =>
    rw [List.cons_append, Transducer.run_cons]
    simp only [reader, List.length_cons, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false,
      dite_false, Nat.add_sub_cancel, List.nil_append]
    exact ih (by simp only [List.length_cons] at hp; omega)

private theorem run_after (left right : ℕ) (post rest : List Bool) (hp : post.length ≤ right) :
    (reader left right).run (afterState left right post.length hp) (post ++ rest) =
      (reader left right).run (reader left right).q₀ rest := by
  induction post with
  | nil => simp [afterState, reader]
  | cons b post ih =>
    have hs : afterState left right (b :: post).length hp =
        .after ⟨post.length, by simp only [List.length_cons] at hp; omega⟩ := by
      simp [afterState]
    rw [hs, List.cons_append, Transducer.run_cons]
    simp only [reader, List.nil_append]
    exact ih (by simp only [List.length_cons] at hp; omega)

private theorem run_field (left right : ℕ) (pre post rest : List Bool) (a b : Bool)
    (hp : pre.length = left) (hs : post.length = right) :
    (reader left right).run (reader left right).q₀ (pre ++ [a, b] ++ post ++ rest) =
      [a, b] ++ (reader left right).run (reader left right).q₀ rest := by
  have hb := run_before left right pre ([a, b] ++ post ++ rest) hp.le
  simp only [hp] at hb
  change (reader left right).run (.before ⟨left, by omega⟩) _ = _
  simp only [List.append_assoc] at hb ⊢
  rw [hb]
  change a :: b :: (reader left right).run (afterState left right right le_rfl)
    (post ++ rest) = a :: b :: (reader left right).run (reader left right).q₀ rest
  have ha := run_after left right post rest hs.le
  simpa only [hs] using congrArg (fun w => a :: b :: w) ha

private theorem run_row {k : ℕ} (c : Fin (k + 1)) (r : Option (Fin k) → SignType)
    (rest : List Bool) :
    (reader (2 * c.val) (2 * (k - c.val))).run (reader (2 * c.val) (2 * (k - c.val))).q₀
        (ScheduleBits.row r ++ rest) =
      [RelativeScan.negative (r (ScheduleBits.head c)),
        RelativeScan.positive (r (ScheduleBits.head c))] ++
        (reader (2 * c.val) (2 * (k - c.val))).run
          (reader (2 * c.val) (2 * (k - c.val))).q₀ rest := by
  obtain ⟨pre, post, hp, hs, hr⟩ := ScheduleBits.exists_row_split r c
  rw [hr]
  exact run_field _ _ pre post rest _ _ hp hs

private theorem run_rows {k : ℕ} (c : Fin (k + 1))
    (rs : List (Option (Fin k) → SignType)) :
    (reader (2 * c.val) (2 * (k - c.val))).run (reader (2 * c.val) (2 * (k - c.val))).q₀
      (ScheduleBits.rows rs) = ScheduleBits.column c rs := by
  induction rs with
  | nil => simp [ScheduleBits.rows, ScheduleBits.column, reader, RelativeScan.encode]
  | cons r rs ih =>
    rw [ScheduleBits.rows, run_row, ih]
    simp [ScheduleBits.column, RelativeScan.encode]

/-- Extract one fixed head column. Tape 1 is the source, tape 0 receives the column, and tape 2
is temporary adapter storage. No state depends on the runtime number or contents of rows. -/
@[expose] noncomputable def machine {k : ℕ} (c : Fin (k + 1)) :=
  (((reader (2 * c.val) (2 * (k - c.val))).toTM).seq (rewindInput Bool)).onWords true

/-- Native extraction preserves the entire raw schedule and the prior output. All three work
heads return to zero; the adapter tape is blank. The input head starts and ends at position one.
The source is the canonical encoding of rows, whose validity is `ScheduleBits.canonical_rows`. -/
theorem runsBetween_raw {k : ℕ} (c : Fin (k + 1)) (input out : List Bool)
    (rs : List (Option (Fin k) → SignType)) :
    RunsBetween (machine c) (tapesCfg input ![[], ScheduleBits.rows rs, []] 0 0 out)
      (tapesCfg input ![ScheduleBits.column c rs, ScheduleBits.rows rs, []] 0 0 out)
      (4 * (ScheduleBits.rows rs).length + (ScheduleBits.column c rs).length + 14)
      (2 * (ScheduleBits.rows rs).length + 2 * (ScheduleBits.column c rs).length + 18) := by
  have ht := ((reader (2 * c.val) (2 * (k - c.val))).computesTidily
    (ScheduleBits.rows rs)).onWords true
  rw [run_rows] at ht
  obtain ⟨words', emitted, ⟨hw, he⟩, hr⟩ := RunsBetween.of_transformsTapes
    (input := input) ht (ws := ![[], ScheduleBits.rows rs, []]) (by
      funext i
      fin_cases i <;> simp) 0 out
  rw [hw, he, List.append_nil] at hr
  have hu : Function.update (![[], ScheduleBits.rows rs, []])
      ((Fin.last 0).castAdd 2) (ScheduleBits.column c rs) =
      ![ScheduleBits.column c rs, ScheduleBits.rows rs, []] := by
    funext i
    fin_cases i <;> simp
  rw [hu] at hr
  convert hr using 1 <;> first | rfl | omega

/-- Fixed row width yields a linear clock in the number of schedule rows. The machine itself
has no runtime row count in its finite control. -/
theorem runsBetween {k : ℕ} (c : Fin (k + 1)) (input out : List Bool)
    (rs : List (Option (Fin k) → SignType)) :
    RunsBetween (machine c) (tapesCfg input ![[], ScheduleBits.rows rs, []] 0 0 out)
      (tapesCfg input ![ScheduleBits.column c rs, ScheduleBits.rows rs, []] 0 0 out)
      ((8 * k + 10) * rs.length + 14) ((4 * k + 8) * rs.length + 18) := by
  have h := runsBetween_raw c input out rs
  simp only [ScheduleBits.length_rows, ScheduleBits.length_column] at h
  convert h using 1 <;> ring

end Turing.MultiTapeTM.ScheduleColumn
