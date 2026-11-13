/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.BinaryIncrement
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.RunsBetween
public import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-!
# Recovering a pair cursor as a growing binary counter

The source head begins at position `2*q` in a dense source word. A read-only leftward pass counts
one increment per pair on a blank second tape. The left blank terminates the pass: no sentinel is
inserted into the source. Both heads end at zero, the complete source word is preserved, and the
counter is the canonical binary word `q.bits`. Amortized native increments and loop dispatch cost
at most `8*q+3` transitions altogether.
-/

public section

namespace Turing.MultiTapeTM.CursorCount

/-- One movement of the source head, preserving both tapes. -/
@[expose] def sourceMove (move : SignType) : MultiTapeTM 2 Bool Unit :=
  ofTr () fun _ _ _ => ⟨0, ![(none, move), (none, 0)], none, none⟩

/-- Native binary increment on the counter tape, leaving the source head in place. -/
@[expose] noncomputable def increment :=
  BinaryIncrement.machine.extendTapes (Fin.natAddEmb 1 : Fin 1 ↪ Fin 2)

/-- Consume a pair leftwards and increment once. -/
@[expose] noncomputable def round :=
  (sourceMove (-1)).seq (increment.seq (sourceMove (-1)))

/-- Count pairs back to the source's left blank, then restore the source head to zero. -/
@[expose] noncomputable def machine :=
  (sourceMove (-1)).seq
    ((whileCond (fun _ work => (work 0).isSome) round).seq (sourceMove 1))

/-- A full source word, its cursor, and a counter whose head is at zero. -/
@[expose] def config (input source counter : List Bool) (cursor : ℤ) (out : List Bool) :
    Cfg 2 Bool Unit input :=
  tapesCfg input ![source, counter] 0 ![cursor, 0] out

private theorem runsBetween_sourceMove (input source counter out : List Bool) (cursor : ℤ)
    (move : SignType) :
    RunsBetween (sourceMove move) (config input source counter cursor out)
      (config input source counter (cursor + (move : ℤ)) out) 1 4 := by
  apply RunsBetween.of_runFrom
  rw [runFrom_one]
  apply step_tapesCfg (a := ⟨0, ![(none, move), (none, 0)], none, none⟩)
  · simp [sourceMove]
  · rfl
  · rfl
  · intro i
    fin_cases i <;> rfl
  · intro i
    fin_cases i <;> simp

private theorem runFrom_increment (input source out : List Bool) (cursor : ℤ) (n : ℕ) :
    increment.runFrom ((config input source n.bits cursor out).withState
      (some increment.q₀)) (2 * BinaryIncrement.initialOnes n.bits + 3) =
      (config input source (n + 1).bits cursor out).withState none := by
  rw [increment, runFrom_extendTapes]
  have hv : viewCfg (Fin.natAddEmb 1 : Fin 1 ↪ Fin 2)
      ((config input source n.bits cursor out).withState
        (some (BinaryIncrement.machine.extendTapes (Fin.natAddEmb 1 : Fin 1 ↪ Fin 2)).q₀)) =
      ⟨some BinaryIncrement.machine.q₀, 1, fun _ => tapeOfList n.bits, fun _ => 0, out⟩ := by
    refine Cfg.ext rfl rfl ?_ ?_ rfl
    · funext i z
      fin_cases i
      change tapeOfList n.bits (z - 0) = tapeOfList n.bits z
      rw [sub_zero]
    · funext i
      fin_cases i
      rfl
  rw [hv, BinaryIncrement.runFrom_bits, embed_natAdd]
  refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext i <;> fin_cases i <;>
    simp [config, tapesCfg, Cfg.withState, Fin.append, Fin.addCases]

private theorem runsBetween_round (input source out : List Bool) (cursor : ℤ) (n : ℕ) :
    RunsBetween round (config input source n.bits cursor out)
      (config input source (n + 1).bits (cursor - 2) out)
      (2 * BinaryIncrement.initialOnes n.bits + 5)
      (4 * BinaryIncrement.initialOnes n.bits + 16) := by
  have hs := (runsBetween_sourceMove input source n.bits out cursor (-1)).seq
    ((RunsBetween.of_runFrom (runFrom_increment input source out (cursor - 1) n)).seq
      (runsBetween_sourceMove input source (n + 1).bits out (cursor - 1) (-1)))
  simp only [SignType.coe_neg_one] at hs
  have hp : cursor - 1 + -1 = cursor - 2 := by omega
  have ht : 1 + (2 * BinaryIncrement.initialOnes n.bits + 3 + 1) =
      2 * BinaryIncrement.initialOnes n.bits + 5 := by omega
  have hs' : 4 + (2 * (2 * BinaryIncrement.initialOnes n.bits + 3 + 1) + 4) =
      4 * BinaryIncrement.initialOnes n.bits + 16 := by omega
  simpa only [round, hp, ht, hs'] using hs

private theorem sum_increment_clocks (q : ℕ) :
    (Finset.range q).sum (fun i => 2 * BinaryIncrement.initialOnes i.bits + 3) +
      2 * q.bits.count true = 5 * q := by
  induction q with
  | zero => simp
  | succ q ih =>
    have hp := BinaryIncrement.initialOnes_add_count_incr q.bits
    rw [← NatSucc.bits_succ] at hp
    rw [Finset.sum_range_succ]
    omega

/-- Recover the cursor from blank counter storage, preserving all source cells and output.
The source need only contain the prefix traversed by the cursor. -/
theorem runsBetween (input source out : List Bool) (q : ℕ) (hsource : 2 * q ≤ source.length) :
    RunsBetween machine (config input source [] (2 * q) out)
      (config input source q.bits 0 out) (8 * q + 3) (16 * q + 8) := by
  let cfg (i : ℕ) := config input source i.bits (2 * (q - i : ℕ) - 1) out
  have hr := runsBetween_whileCond (c := fun _ work => (work 0).isSome) (tm := round)
    cfg q (fun i => 2 * BinaryIncrement.initialOnes i.bits + 5)
    (fun i => 4 * BinaryIncrement.initialOnes i.bits + 16) (fun i hi => by
      constructor
      · simp only [cfg, config, tapesCfg, Cfg.workTapeSymbols, Matrix.cons_val_zero,
          Pi.zero_apply, sub_zero, Option.isSome_iff_ne_none, ne_eq, tapeOfList_eq_none_iff]
        omega
      · have he : (2 : ℤ) * (q - i : ℕ) - 1 - 2 = 2 * (q - (i + 1) : ℕ) - 1 := by omega
        simpa only [cfg, he] using
          runsBetween_round input source out (2 * (q - i : ℕ) - 1) i)
    (by
      simp only [cfg, config, tapesCfg, Cfg.workTapeSymbols, Matrix.cons_val_zero,
        Pi.zero_apply, sub_zero, Nat.sub_self, Nat.cast_zero, mul_zero, zero_sub]
      rfl)
  simp only [cfg, Nat.sub_zero, Nat.sub_self, Nat.zero_bits, Nat.cast_zero, mul_zero,
    zero_sub] at hr
  have hstart := runsBetween_sourceMove input source [] out (2 * q) (-1)
  have hfinish := runsBetween_sourceMove input source q.bits out (-1) 1
  have h := hstart.seq (hr.seq hfinish)
  have hc := sum_increment_clocks q
  have ht : 1 + ((∑ i ∈ Finset.range q,
      (2 * BinaryIncrement.initialOnes i.bits + 5 + 1)) + 1 + 1) ≤ 8 * q + 3 := by
    simp only [show ∀ i : ℕ, 2 * BinaryIncrement.initialOnes i.bits + 5 + 1 =
      (2 * BinaryIncrement.initialOnes i.bits + 3) + 3 by intro i; omega,
      Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul] at hc ⊢
    omega
  have hh : RunsBetween _ _ _ (8 * q + 3) (16 * q + 8) :=
    (RunsBetween.of_runFrom h.1).mono ht (by omega)
  simpa [machine, cfg, config] using hh

end Turing.MultiTapeTM.CursorCount
