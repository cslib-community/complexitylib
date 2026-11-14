/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.RelativeScan
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.CursorCount
import Mathlib.Tactic.FinCases

/-!
# Native relative scanning with a binary consumed offset

A three-tape machine initializes and performs the distance scan, then converts the source cursor
into a growing binary counter. Tape 0 preserves the two-bit movement stream, tape 1 holds the
three distance markers, and tape 2 returns the canonical consumed offset. Initialization, scanning,
and counter construction together cost at most `10*consumed+9` native transitions. Starting at
pair cursor `p` in the full source returns the absolute index `p+consumed`, with the extra
`8*p` transitions charged for counting and rewinding the preserved prefix.
-/

public section

namespace Turing.MultiTapeTM.RelativeScanIndex

/-- Tape 1 is reserved for the scanner's signed-distance markers. -/
@[expose] def counterTapes : Fin 2 ↪ Fin 3 := Fin.succAboveEmb 1

/-- Initialize the relative scan, then recover its pair cursor as a binary natural. -/
@[expose] noncomputable def machine (start : Fin 5) :=
  ((RelativeScan.initialized start).extendTapes Fin.castSuccEmb).seq
    (CursorCount.machine.extendTapes counterTapes)

/-- All heads start at zero, with only the source tape occupied. -/
@[expose] def initialConfig (input source out : List Bool) : Cfg 3 Bool Unit input :=
  tapesCfg input ![source, [], []] 0 0 out

/-- The source head is already at pair cursor `p`; marker and counter tapes start blank.
Establishing this input cursor is a separate operation. -/
@[expose] def positionedConfig (input source : List Bool) (p : ℕ) (out : List Bool) :
    Cfg 3 Bool Unit input :=
  tapesCfg input ![source, [], []] 0 ![2 * p, 0, 0] out

/-- The full source is preserved, its head is restored, and the offset is stored in canonical
binary. The signed-distance head and the previously appended result flag are also retained. -/
@[expose] def finalConfig (input source out : List Bool) (r : RelativeScan.Result) :
    Cfg 3 Bool Unit input :=
  tapesCfg input ![source, [true, true, true], r.consumed.bits] 0 ![0, r.distance + 1, 0]
    (out ++ [r.found])

private theorem counter_view (input source marker counter out : List Bool) (cursor head : ℤ) :
    viewCfg counterTapes (tapesCfg input ![source, marker, counter] 0 ![cursor, head, 0] out) =
      CursorCount.config input source counter cursor out := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext i <;> fin_cases i <;> rfl

private theorem counter_embed (input source marker counter counter' out : List Bool)
    (cursor head : ℤ) :
    embed counterTapes (CursorCount.config input source counter' 0 out)
      (tapesCfg input ![source, marker, counter] 0 ![cursor, head, 0] out).workTapes
      (tapesCfg input ![source, marker, counter] 0 ![cursor, head, 0] out).workTapePos =
      tapesCfg input ![source, marker, counter'] 0 ![0, head, 0] out := by
  have h0 : partialInv counterTapes 0 = some 0 := partialInv_embed counterTapes 0
  have h2 : partialInv counterTapes 2 = some 1 := partialInv_embed counterTapes 1
  have h1 : partialInv counterTapes 1 = none := by
    apply partialInv_eq_none
    rintro ⟨i, hi⟩
    exact Fin.succAbove_ne (1 : Fin 3) i hi
  refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext i <;> fin_cases i <;>
    simp [embed, h0, h1, h2, CursorCount.config, tapesCfg]

/-- A positioned scan returns an absolute index by counting the full source prefix. There is
no prefix copy or binary addition subroutine: the physical source cursor is rewound and counted.
The match flag remains false on exhaustion, even when the last movement enters the window. -/
theorem runsBetween_fromPrefix (input out : List Bool) (pre ss : List SignType) (start : Fin 5) :
    RunsBetween (machine start)
      (positionedConfig input (RelativeScan.encode pre ++ RelativeScan.encode ss) pre.length out)
      (finalConfig input (RelativeScan.encode pre ++ RelativeScan.encode ss) out
        { RelativeScan.evaluate ss (RelativeScan.initialDistance start) with
          consumed := pre.length +
            (RelativeScan.evaluate ss (RelativeScan.initialDistance start)).consumed })
      (8 * pre.length + 10 * (RelativeScan.evaluate ss
        (RelativeScan.initialDistance start)).consumed + 9)
      (16 * pre.length + 20 * (RelativeScan.evaluate ss
        (RelativeScan.initialDistance start)).consumed + 26) := by
  let source := RelativeScan.encode pre ++ RelativeScan.encode ss
  let r := RelativeScan.evaluate ss (RelativeScan.initialDistance start)
  let mid := tapesCfg input ![source, [true, true, true], []] 0
    ![2 * (pre.length + r.consumed), r.distance + 1, 0] (out ++ [r.found])
  have hv : viewCfg (Fin.castSuccEmb : Fin 2 ↪ Fin 3)
      (positionedConfig input source pre.length out) =
      tapesCfg input ![source, []] 0 ![2 * pre.length, 0] out := by
    refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext i <;> fin_cases i <;> rfl
  have hs := RelativeScan.runsBetween_initialized input source (RelativeScan.encode pre)
    ss rfl out start
  simp only [RelativeScan.length_encode, Nat.cast_mul, Nat.cast_ofNat] at hs
  rw [← hv] at hs
  have he := hs.extendTapes (Fin.castSuccEmb : Fin 2 ↪ Fin 3)
  have hcursor : (2 : ℤ) * pre.length + 2 * r.consumed =
      2 * (pre.length + r.consumed) := by omega
  have hm : embed (Fin.castSuccEmb : Fin 2 ↪ Fin 3)
      (RelativeScan.config input source (2 * (pre.length + r.consumed)) r.distance
        (out ++ [r.found]))
      (positionedConfig input source pre.length out).workTapes
      (positionedConfig input source pre.length out).workTapePos = mid := by
    rw [embed_castSucc]
    refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext i <;>
      induction i using Fin.lastCases with
      | last => simp only [Fin.lastCases_last]; rfl
      | cast i => simp only [Fin.lastCases_castSucc]; fin_cases i <;> rfl
  change RunsBetween _ _
    (embed _ (RelativeScan.config input source (2 * pre.length + 2 * r.consumed)
      r.distance (out ++ [r.found])) _ _)
    (2 * r.consumed + 6) (4 * r.consumed + 16 + (3 - 2)) at he
  rw [hcursor, hm] at he
  have hc := CursorCount.runsBetween input source (out ++ [r.found])
    (pre.length + r.consumed) (by
      have hp : r.consumed ≤ ss.length :=
        RelativeScan.consumed_le ss (RelativeScan.initialDistance start)
      simp only [source, List.length_append, RelativeScan.length_encode]
      omega)
  simp only [Nat.cast_add] at hc
  rw [← counter_view input source [true, true, true] [] (out ++ [r.found])
    (2 * (pre.length + r.consumed)) (r.distance + 1)] at hc
  have hc' := hc.extendTapes counterTapes
  rw [counter_embed] at hc'
  have h := he.seq hc'
  change RunsBetween _ _ _ (8 * pre.length + 10 * r.consumed + 9)
    (16 * pre.length + 20 * r.consumed + 26)
  convert h using 1 <;> first | rfl | omega

/-- The complete native pipeline returns the consumed offset in binary and the match flag on
output. The bound includes blank-marker initialization and restores the source and counter heads. -/
theorem runsBetween (input out : List Bool) (ss : List SignType) (start : Fin 5) :
    RunsBetween (machine start) (initialConfig input (RelativeScan.encode ss) out)
      (finalConfig input (RelativeScan.encode ss) out
        (RelativeScan.evaluate ss (RelativeScan.initialDistance start)))
      (10 * (RelativeScan.evaluate ss (RelativeScan.initialDistance start)).consumed + 9)
      (20 * (RelativeScan.evaluate ss (RelativeScan.initialDistance start)).consumed + 26) := by
  have h := runsBetween_fromPrefix input out [] ss start
  simp only [RelativeScan.encode, List.nil_append, List.length_nil,
    Nat.mul_zero, zero_add] at h
  convert h using 1
  refine Cfg.ext rfl rfl rfl ?_ rfl
  funext i
  fin_cases i <;> rfl

/-- Shifting the consumed count gives an absolute result exactly when a match was found. -/
theorem index_add_consumed (p : ℕ) (r : RelativeScan.Result) :
    ({ r with consumed := p + r.consumed } : RelativeScan.Result).index =
      r.index.map (p + ·) := by
  cases hr : r.found <;> simp [RelativeScan.Result.index, hr]

end Turing.MultiTapeTM.RelativeScanIndex
