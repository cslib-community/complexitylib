/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Circuit.Boolean.Tournament

/-!
# Comparison and tournament clients

Concrete clients check least-significant-bit-first comparison, payload preservation on ties,
zero widths, singleton tournaments, and a three-record tournament. The generic balanced fold
also has an explicit empty-list client.
-/

namespace ComplexityTests.ComparisonCircuits

open Cslib Cslib.Circuits Cslib.Circuits.Boolean Cslib.BitString

-- Binary 01 is one and binary 10 is two when the first coordinate is least significant.
example : (leCircuit 2).eval interpretation
    (Fin.append ![true, false] ![false, true]) 0 = true := by
  decide

example : (leCircuit 2).eval interpretation
    (Fin.append ![false, true] ![true, false]) 0 = false := by
  decide

example : (leCircuit 0).eval interpretation Fin.elim0 0 = true := rfl

example : (muxCircuit 0).size = 1 ∧ (muxCircuit 0).depth = 0 := by
  decide

example : (minCircuit 0).eval interpretation Fin.elim0 = Fin.elim0 := by
  funext i
  exact i.elim0

-- Equal one-bit keys retain the first record's distinct payload.
example : (keyedMinCircuit 1 1).eval interpretation
    (Fin.append ![false, true] ![false, false]) = ![false, true] := by
  decide

-- A zero-width key ties every pair, so selection retains the first payload.
example : (keyedMinCircuit 0 2).eval interpretation
    (Fin.append ![true, false] ![false, true]) = ![true, false] := by
  decide

private def records : Fin 3 → BitString 2 :=
  ![![true, false], ![false, true], ![false, false]]

example : (packedTournamentCircuit 1 1 2).eval interpretation (packRecords records) =
    ![false, true] := by
  simp only [packedTournamentCircuit, tournamentCircuit, Circuit.eval_balanced,
    List.ofFn_succ, List.ofFn_zero, List.balancedFold, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceDiv, List.take_succ_cons, List.take_zero, List.drop_succ_cons,
    List.drop_zero]
  decide

example : (packedTournamentCircuit 1 1 2).size = 26 ∧
    (packedTournamentCircuit 1 1 2).depth ≤ 16 ∧
    (packedTournamentCircuit 1 1 2).depth < (packedTournamentCircuit 1 1 2).size := by
  have hsize : (packedTournamentCircuit 1 1 2).size = 26 := by simp
  have hdepth : (packedTournamentCircuit 1 1 2).depth ≤ 16 :=
    depth_packedTournamentCircuit_le 1 1 2
  exact ⟨hsize, hdepth, by omega⟩

example (r : BitString 3) :
    (packedTournamentCircuit 1 2 0).eval interpretation (packRecords (fun _ => r)) = r := by
  simp [packedTournamentCircuit, tournamentCircuit, Circuit.balanced, List.ofFn_succ,
    Circuit.eval_wiring, packRecords_comp (r := 1 + 2)]

example : (packedTournamentCircuit 1 2 0).size = 0 ∧
    (packedTournamentCircuit 1 2 0).depth = 0 := by
  constructor
  · simp
  · exact Nat.eq_zero_of_le_zero (depth_packedTournamentCircuit_le 1 2 0)

example : (packedTournamentCircuit 0 0 2).eval interpretation Fin.elim0 = Fin.elim0 := by
  funext i
  exact i.elim0

example : Circuit.balanced (keyedMinCircuit 1 1) (Circuit.id signature 2) [] =
    Circuit.id signature 2 := by simp [Circuit.balanced]

end ComplexityTests.ComparisonCircuits
