/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.PositionPairsCore
import Mathlib.Tactic.FinCases

/-!
# Pair positioning bounded by the source word

One fixed finite machine reads a binary interval index from tape 1 and advances along pairs on
source tape 0, stopping at the end of the source even when the requested index is much larger.
The source is preserved, both auxiliary tapes are erased and their heads are restored to zero.
One output bit reports whether the requested pair exists. Thus the resource bound is linear in
the source length plus the binary index width, independently of the value of a rejected index.

`runsBetween` charges a tighter bound in terms of the number of pairs actually traversed;
`runsBetween_bits` specializes it to canonical binary indices.
-/

public section

namespace Turing.MultiTapeTM.BoundedPositionPairs

open Cslib.BitString

private def report : MultiTapeTM 3 Bool Unit :=
  .ofTr () fun _ _ work =>
    ⟨0, fun _ => (none, 0), some (work 0).isSome, none⟩

/-- Test the source before each pair advance, clear the counter and flag, then report whether
the final source cell is nonblank. The input index never enters the finite control. -/
noncomputable def machine := (PositionPairs.guarded Option.isSome).seq report

private theorem source_isSome (source : List Bool) (q i : ℕ) (hs : source.length = 2 * q) :
    (tapeOfList source (2 * (i : ℤ))).isSome = decide (i < q) := by
  apply Bool.eq_iff_iff.mpr
  simp only [Option.isSome_iff_ne_none, ne_eq, tapeOfList_eq_none_iff, decide_eq_true_eq]
  omega

private theorem runsBetween_report (input source out : List Bool) (q i : ℕ)
    (hs : source.length = 2 * q) :
    RunsBetween report (PositionPairs.config input source [] [] (2 * (i : ℤ)) out)
      (PositionPairs.config input source [] [] (2 * (i : ℤ)) (out ++ [decide (i < q)]))
      1 6 := by
  apply RunsBetween.of_runFrom
  rw [runFrom_one, step_of_state rfl]
  have hcell := source_isSome source q i hs
  refine Cfg.ext ?_ ?_ ?_ ?_ ?_ <;>
    simp [report, PositionPairs.config, tapesCfg, Action.apply, Cfg.withState,
      Cfg.workTapeSymbols, hcell]

/-- Stop at the earlier of the requested interval and EOF, preserving the source and clearing
both auxiliary tapes. The output distinguishes an existing pair from an out-of-range index,
including the empty-source case. Only traversed pairs and the original index width are charged. -/
theorem runsBetween (input source w out : List Bool) (q : ℕ) (hs : source.length = 2 * q) :
    RunsBetween machine (PositionPairs.config input source w [] 0 out)
      (PositionPairs.config input source [] [] (2 * (min (lsbValue w) q : ℕ) : ℤ)
        (out ++ [decide (lsbValue w < q)]))
      (11 * min (lsbValue w) q + 5 * w.length + 14)
      (3 * (11 * min (lsbValue w) q + 5 * w.length + 15)) := by
  have hpos := PositionPairs.runsBetween_guarded Option.isSome input source w out
    (min (lsbValue w) q) (Nat.min_le_left _ _) (fun i hi => by
      rw [source_isSome source q i hs]
      simp only [decide_eq_true_eq]
      omega) (by
      by_cases hi : lsbValue w ≤ q
      · exact Or.inl (Nat.min_eq_left hi)
      · right
        rw [source_isSome source q (min (lsbValue w) q) hs, Nat.min_eq_right (by omega)]
        simp)
  have hr := runsBetween_report input source out q (min (lsbValue w) q) hs
  have hlt : min (lsbValue w) q < q ↔ lsbValue w < q := by omega
  simp only [hlt] at hr
  have hall := hpos.seq hr
  have hraw := RunsBetween.of_runFrom hall.1
  exact hraw

/-- Canonical binary indices use the same finite machine, with EOF bounding traversal even for
arbitrarily large rejected indices. -/
theorem runsBetween_bits (input source out : List Bool) (q p : ℕ)
    (hs : source.length = 2 * q) :
    RunsBetween machine (PositionPairs.config input source p.bits [] 0 out)
      (PositionPairs.config input source [] [] (2 * (min p q : ℕ) : ℤ)
        (out ++ [decide (p < q)]))
      (11 * min p q + 5 * p.bits.length + 14)
      (3 * (11 * min p q + 5 * p.bits.length + 15)) := by
  simpa only [lsbValue_bits] using runsBetween input source p.bits out q hs

/-- A bound independent of the numeric value of the index: only the source and index lengths
matter. This is the bound needed before dispatching an endpoint query on an untrusted index. -/
theorem runsBetween_length (input source w out : List Bool) (q : ℕ)
    (hs : source.length = 2 * q) :
    RunsBetween machine (PositionPairs.config input source w [] 0 out)
      (PositionPairs.config input source [] [] (2 * (min (lsbValue w) q : ℕ) : ℤ)
        (out ++ [decide (lsbValue w < q)]))
      (11 * q + 5 * w.length + 14) (3 * (11 * q + 5 * w.length + 15)) :=
  (runsBetween input source w out q hs).mono
    (by omega) (Nat.mul_le_mul_left 3 (by omega))

end Turing.MultiTapeTM.BoundedPositionPairs
