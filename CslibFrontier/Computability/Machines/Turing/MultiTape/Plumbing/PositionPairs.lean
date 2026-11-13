/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.BinaryDecrementFlag
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.RunsBetween
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.ClearWork
import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.WordMoves
import Mathlib.Data.Fin.Embedding
import Mathlib.Tactic.FinCases

/-!
# Positioning a pair cursor from a binary counter

One fixed finite machine decrements a runtime binary word until underflow and moves the source
head twice after each successful decrement. It preserves every source cell and the old output.
A single reusable flag cell receives the decrement's underflow bit; the flag and counter tapes
are cleared before returning, with both auxiliary heads restored to zero.

The amortized decrement bound charges only the borrow prefixes, not the full counter width on
every round. All loop tests, flag rewinds, source moves and final cleanup are included in the
linear bound. The source need not be copied or inspected while positioning its head.
-/

public section

namespace Turing.MultiTapeTM.PositionPairs

open Cslib.BitString

/-- Source, binary counter and reusable one-cell flag; only the source head may be displaced. -/
@[expose] def config (input source counter flag : List Bool) (cursor : ℤ) (out : List Bool) :
    Cfg 3 Bool Unit input :=
  tapesCfg input ![source, counter, flag] 0 ![cursor, 0, 0] out

private def rewindFlag : MultiTapeTM 3 Bool Unit :=
  .ofTr () fun _ _ _ => ⟨0, ![(none, 0), (none, 0), (none, -1)], none, none⟩

private noncomputable def decrementReady :=
  (binaryDecrement.outputToTape.extendTapes (Fin.natAddEmb 1 : Fin 2 ↪ Fin 3)).seq rewindFlag

private def advance : MultiTapeTM 3 Bool Bool :=
  .ofTr false fun phase _ _ =>
    ⟨0, ![(none, 1), (none, 0), (if phase then none else some none, 0)], none,
      if phase then none else some true⟩

private noncomputable def round := advance.seq decrementReady

private def eraseFlag : MultiTapeTM 3 Bool Unit :=
  .ofTr () fun _ _ _ => ⟨0, ![(none, 0), (none, 0), (some none, 0)], none, none⟩

private noncomputable def finish :=
  eraseFlag.seq ((clearWork Bool).extendTapes (tapeEmb (1 : Fin 3)))

/-- Decrement, test the retained flag, and advance twice on each successful round, then clean
both auxiliary tapes. Its finite control does not depend on the counter value or width. -/
noncomputable def machine :=
  decrementReady.seq ((whileCond (fun _ work => work 2 == some false) round).seq finish)

private theorem runFrom_decrement (input source w out : List Bool) (cursor : ℤ) :
    (binaryDecrement.outputToTape.extendTapes (Fin.natAddEmb 1 : Fin 2 ↪ Fin 3)).runFrom
      ((config input source w [] cursor out).withState (some binaryDecrement.q₀))
      (2 * BinaryDecrement.zeros w + 3) =
      (tapesCfg input ![source, decrement w, [decide (lsbValue w = 0)]]
        0 ![cursor, 0, 1] out).withState none := by
  have hpair {α : Type} (a b : α) :
      (Fin.lastCases b (fun _ : Fin 1 => a) : Fin 2 → α) = ![a, b] := by
    funext i
    induction i using Fin.lastCases with
    | last => rw [Fin.lastCases_last]; rfl
    | cast i => rw [Fin.lastCases_castSucc]; fin_cases i; rfl
  have h := runFrom_binaryDecrement_outputToTape (input := input) 1 w
  simp only [hpair] at h
  have hp := runFrom_map (binaryDecrement.outputToTape.prependOutputHom out)
    (⟨some binaryDecrement.q₀, 1, ![tapeOfList w, tapeOfList []], fun _ => 0, []⟩ :
      Cfg 2 Bool _ input) (2 * BinaryDecrement.zeros w + 3)
  rw [h] at hp
  simp only [MultiTapeNTM.prependOutputHom_apply] at hp
  have he0 : (Fin.natAddEmb 1 : Fin 2 ↪ Fin 3) 0 = 1 := rfl
  have he1 : (Fin.natAddEmb 1 : Fin 2 ↪ Fin 3) 1 = 2 := rfl
  rw [runFrom_extendTapes]
  have hv : viewCfg (Fin.natAddEmb 1 : Fin 2 ↪ Fin 3)
      ((config input source w [] cursor out).withState (some binaryDecrement.q₀)) =
      (⟨some binaryDecrement.q₀, 1, ![tapeOfList w, tapeOfList []], fun _ => 0, []⟩ :
        Cfg 2 Bool _ input).prependOutput out := by
    refine Cfg.ext rfl rfl ?_ ?_ (by simp [viewCfg, config, tapesCfg]) <;>
      funext i <;> fin_cases i <;>
      simp [viewCfg, config, tapesCfg, Cfg.withState, Cfg.prependOutput, he0, he1]
  rw [hv, hp, embed_natAdd]
  refine Cfg.ext rfl rfl ?_ ?_ (by simp [Cfg.prependOutput, tapesCfg]) <;>
    funext i <;> fin_cases i <;>
    simp [config, tapesCfg, Cfg.withState, Cfg.prependOutput, Fin.append, Fin.addCases]

private theorem runsBetween_decrementReady (input source w out : List Bool) (cursor : ℤ) :
    RunsBetween decrementReady (config input source w [] cursor out)
      (config input source (decrement w) [decide (lsbValue w = 0)] cursor out)
      (2 * BinaryDecrement.zeros w + 4) (3 * (2 * BinaryDecrement.zeros w + 5)) := by
  have hr : RunsBetween rewindFlag
      (tapesCfg input ![source, decrement w, [decide (lsbValue w = 0)]]
        0 ![cursor, 0, 1] out)
      (config input source (decrement w) [decide (lsbValue w = 0)] cursor out) 1 6 := by
    apply RunsBetween.of_runFrom
    rw [runFrom_one]
    apply step_tapesCfg (a := ⟨0, ![(none, 0), (none, 0), (none, -1)], none, none⟩)
    · simp [rewindFlag]
    · rfl
    · rfl
    · intro i; fin_cases i <;> rfl
    · intro i; fin_cases i <;> simp
  have hd := (RunsBetween.of_runFrom (runFrom_decrement input source w out cursor)).seq hr
  apply RunsBetween.of_runFrom
  simpa only [decrementReady, Nat.add_assoc] using hd.1

private theorem runsBetween_advance (input source w out : List Bool) (cursor : ℤ) (b : Bool) :
    RunsBetween advance (config input source w [b] cursor out)
      (config input source w [] (cursor + 2) out) 2 9 := by
  let mid := config input source w [] (cursor + 1) out
  have h₀ : advance.step ((config input source w [b] cursor out).withState (some false)) =
      mid.withState (some true) := by
    apply step_tapesCfg
      (a := ⟨0, ![(none, 1), (none, 0), (some none, 0)], none, some true⟩)
    · simp [advance]
    · rfl
    · rfl
    · intro i
      fin_cases i <;> try rfl
      simpa using update_shifted_cons_none b ([] : List Bool) (0 : ℤ)
    · intro i; fin_cases i <;> simp
  have h₁ : advance.step (mid.withState (some true)) =
      (config input source w [] (cursor + 2) out).withState none := by
    apply step_tapesCfg (a := ⟨0, ![(none, 1), (none, 0), (none, 0)], none, none⟩)
    · simp [advance]
    · rfl
    · rfl
    · intro i; fin_cases i <;> rfl
    · intro i; fin_cases i <;> simp; omega
  apply RunsBetween.of_runFrom
  change advance.runFrom ((config input source w [b] cursor out).withState (some false))
    (1 + 1) = _
  simp only [runFrom_add, runFrom_one, h₀, h₁]

private theorem runsBetween_round (input source w out : List Bool) (cursor : ℤ) (b : Bool) :
    RunsBetween round (config input source w [b] cursor out)
      (config input source (decrement w) [decide (lsbValue w = 0)] (cursor + 2) out)
      (2 * BinaryDecrement.zeros w + 6) (3 * (2 * BinaryDecrement.zeros w + 7)) := by
  apply RunsBetween.of_runFrom
  have h := (runsBetween_advance input source w out cursor b).seq
    (runsBetween_decrementReady input source w out (cursor + 2))
  simpa only [round, show 2 + (2 * BinaryDecrement.zeros w + 4) =
    2 * BinaryDecrement.zeros w + 6 by omega] using h.1

private theorem runsBetween_finish (input source w out : List Bool) (cursor : ℤ) (b : Bool) :
    RunsBetween finish (config input source w [b] cursor out)
      (config input source [] [] cursor out) (3 * w.length + 4) (3 * (3 * w.length + 5)) := by
  have hf : RunsBetween eraseFlag (config input source w [b] cursor out)
      (config input source w [] cursor out) 1 6 := by
    apply RunsBetween.of_runFrom
    rw [runFrom_one]
    apply step_tapesCfg (a := ⟨0, ![(none, 0), (none, 0), (some none, 0)], none, none⟩)
    · simp [eraseFlag]
    · rfl
    · rfl
    · intro i
      fin_cases i <;> try rfl
      simpa using update_shifted_cons_none b ([] : List Bool) (0 : ℤ)
    · intro i; fin_cases i <;> simp
  obtain ⟨_, _, ⟨rfl, rfl⟩, hc⟩ := RunsBetween.of_transformsTapes (input := input)
    (transformsTapes_clearWork (Symbol := Bool) w) (ws := fun _ => w) rfl 0 out
  simp only [List.append_nil] at hc
  have hv : viewCfg (tapeEmb (1 : Fin 3)) (config input source w [] cursor out) =
      tapesCfg input (fun _ : Fin 1 => w) 0 0 out := by
    refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext i <;> fin_cases i <;> rfl
  rw [← hv] at hc
  have he := hc.extendTapes (tapeEmb (1 : Fin 3))
  have hfinal : embed (tapeEmb (1 : Fin 3)) (tapesCfg input (fun _ : Fin 1 => []) 0 0 out)
      (config input source w [] cursor out).workTapes
      (config input source w [] cursor out).workTapePos = config input source [] [] cursor out := by
    rw [embed_tapeEmb]
    refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext i <;> fin_cases i <;>
      simp [config, tapesCfg]
  rw [hfinal] at he
  apply RunsBetween.of_runFrom
  have h := hf.seq he
  simpa only [finish, show 1 + 3 * (w.length + 1) = 3 * w.length + 4 by omega] using h.1

private theorem totalClock_eq_sum (n : ℕ) (w : List Bool) :
    BinaryDecrement.totalClock n w =
      ∑ i ∈ Finset.range n, (2 * BinaryDecrement.zeros (decrement^[i] w) + 3) := by
  induction n generalizing w with
  | zero => simp [BinaryDecrement.totalClock]
  | succ n ih =>
    rw [BinaryDecrement.totalClock, Finset.sum_range_succ', ih]
    simp only [Function.iterate_zero_apply, Function.iterate_succ_apply]
    omega

/-- Position the source head at twice the counter value, clearing both auxiliary tapes.
The bound includes the final underflow, reusable-flag housekeeping and complete counter erasure.
Source length is unrestricted: this primitive moves the cursor without reading source cells. -/
theorem runsBetween (input source w out : List Bool) :
    RunsBetween machine (config input source w [] 0 out)
      (config input source [] [] (2 * (lsbValue w : ℤ)) out)
      (11 * lsbValue w + 5 * w.length + 13)
      (3 * (11 * lsbValue w + 5 * w.length + 14)) := by
  let cfg (i : ℕ) := config input source (decrement^[i + 1] w)
    [decide (lsbValue (decrement^[i] w) = 0)] (2 * (i : ℤ)) out
  let time (i : ℕ) := 2 * BinaryDecrement.zeros (decrement^[i + 1] w) + 6
  have hloop := runsBetween_whileCond (c := fun _ work => work 2 == some false) (tm := round)
    cfg (lsbValue w) time (fun i => 3 * (time i + 1)) (fun i hi => by
      have hv := lsbValue_iterate_decrement i w hi.le
      constructor
      · simp [cfg, config, Cfg.workTapeSymbols, tapeOfList, hv,
          Nat.ne_of_gt (by omega : 0 < lsbValue w - i)]
      · have hr := runsBetween_round input source (decrement^[i + 1] w) out (2 * (i : ℤ))
          (decide (lsbValue (decrement^[i] w) = 0))
        simpa [cfg, time, Function.iterate_succ_apply', Nat.cast_add, Nat.cast_one,
          mul_add] using hr)
    (by
      have hv := lsbValue_iterate_decrement (lsbValue w) w le_rfl
      simp [cfg, config, Cfg.workTapeSymbols, tapeOfList, hv])
  have hfirst := runsBetween_decrementReady input source w out 0
  have hfinish := runsBetween_finish input source (decrement^[lsbValue w + 1] w) out
    (2 * (lsbValue w : ℤ)) (decide (lsbValue (decrement^[lsbValue w] w) = 0))
  have hzero : cfg 0 = config input source (decrement w) [decide (lsbValue w = 0)] 0 out := by
    simp only [cfg, Nat.zero_add, Function.iterate_one, Function.iterate_zero_apply,
      Nat.cast_zero, mul_zero]
    rfl
  rw [hzero] at hloop
  have hall := hfirst.seq (hloop.seq hfinish)
  have hlength : (decrement^[lsbValue w + 1] w).length = w.length := by
    induction (lsbValue w + 1) with
    | zero => rfl
    | succ n ih => simpa only [Function.iterate_succ_apply', length_decrement] using ih
  have hsum : 2 * BinaryDecrement.zeros w + 3 +
      ∑ i ∈ Finset.range (lsbValue w), (2 * BinaryDecrement.zeros (decrement^[i + 1] w) + 3) =
      BinaryDecrement.totalClock (lsbValue w + 1) w := by
    rw [totalClock_eq_sum, Finset.sum_range_succ']
    simp [Nat.add_comm]
  have hclock := BinaryDecrement.totalClock_le (lsbValue w + 1) w
  have htime : 2 * BinaryDecrement.zeros w + 4 +
      ((∑ i ∈ Finset.range (lsbValue w), (time i + 1)) + 1 +
        (3 * (decrement^[lsbValue w + 1] w).length + 4)) ≤
      11 * lsbValue w + 5 * w.length + 13 := by
    simp only [time, show ∀ i : ℕ,
      2 * BinaryDecrement.zeros (decrement^[i + 1] w) + 6 + 1 =
        (2 * BinaryDecrement.zeros (decrement^[i + 1] w) + 3) + 4 by intro i; omega,
      Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul, hlength]
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul] at hsum
    omega
  have hraw := RunsBetween.of_runFrom hall.1
  have hbound := hraw.mono htime (Nat.mul_le_mul_left 3 (Nat.add_le_add_right htime 1))
  simpa only [machine, Nat.add_assoc] using hbound

/-- Canonical binary input positions the source at pair `p`, using one uniform finite machine. -/
theorem runsBetween_bits (input source out : List Bool) (p : ℕ) :
    RunsBetween machine (config input source p.bits [] 0 out)
      (config input source [] [] (2 * (p : ℤ)) out)
      (11 * p + 5 * p.bits.length + 13) (3 * (11 * p + 5 * p.bits.length + 14)) := by
  simpa only [lsbValue_bits] using runsBetween input source p.bits out

end Turing.MultiTapeTM.PositionPairs
