/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat.Containers
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.StreamingFlatMap
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List

/-!
# Streaming binary counter additions

The input contains framed pairs of binary counters, not unit-cost natural numbers.
One fixed multitape machine adds each pair and emits the framed binary result.
Its polynomial factor depends on the maximum pair wire, rather than the entire
counter table. Input/output materialization and callback temporaries are charged.
Preparing interleaved pairs from two separate tapes is not part of this interface.

## Main results

* `run_computable`: bit time and peak workspace linear in the number of pairs,
  up to a fixed polynomial in the maximum physical pair width.
-/

public section
namespace Turing.MultiTapeTM.BinaryPairSums

/-- Preserve the position of every counter, including zero counters and repeated values. -/
def run (rows : List (ℕ × ℕ)) : List ℕ := rows.map (fun row => row.1 + row.2)

/-- Maximum framed-first/unframed-second binary pair width, plus one for empty input. -/
def width (rows : List (ℕ × ℕ)) : ℕ :=
  streamRecordLength (encPair encNat encNat) rows + 1

private theorem emit_polyTime : ComputableInPolyTime
    (fun q : Unit × (ℕ × ℕ) => [q.2.1 + q.2.2])
    (encPair encUnit (encPair encNat encNat)) (encList encNat) := by
  have add := ComputableTidilyInPolyTime.binary_add.comp
    (ComputableTidilyInPolyTime.snd encUnit (encPair encNat encNat))
  have single : ComputableTidilyInPolyTime (fun n : ℕ => [n]) encNat (encList encNat) :=
    .of_linear (.of_frame (fun _ => by simp))
  exact .of_tidy (single.comp add)

/-- Uniform execution of all binary additions, with all prefix workspace charged by the
streaming certificate. The bound includes materialized input/output, rather than treating
counter-table access or arithmetic as unit cost. -/
theorem run_computable : ∃ P : ℕ → ℕ, Cslib.PolynomiallyBounded P ∧ Monotone P ∧
    ComputableInO run encNatPairList (encList encNat)
      (fun rows => (encNatPairList rows).length + (rows.length + 1) * P (width rows))
      (fun rows => (encNatPairList rows).length + (rows.length + 1) * P (width rows)) := by
  obtain ⟨P, hP, hm, h⟩ := ComputableInO.flatMap_stream emit_polyTime
  have prepare := (ComputableInO.const (encIn := encNatPairList) (encMid := encUnit) ()).prod
    (ComputableInO.of_eq (encIn := encNatPairList) (encMid := encNatPairList) fun _ => rfl)
  have hc := (h.comp prepare).of_enc_eq (g := run) (encC := encList encNat)
    (fun rows => by simp [run, List.map_eq_flatMap])
  let Q := fun B => P B + 10 * B + 10
  have hQ : Cslib.PolynomiallyBounded Q := by dsimp only [Q]; fun_prop
  have mQ : Monotone Q := by
    intro a b hab
    have := hm hab
    dsimp only [Q]
    omega
  refine ⟨Q, hQ, mQ, hc.mono 10 (fun rows => ?_) (fun rows => ?_)⟩ <;>
    simp only [length_encPair, encUnit_apply, List.length_nil,
      streamFilterWidth, Nat.zero_add] <;>
    dsimp only [Q, width] <;> nlinarith

end Turing.MultiTapeTM.BinaryPairSums
