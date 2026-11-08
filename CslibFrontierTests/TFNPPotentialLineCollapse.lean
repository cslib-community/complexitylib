/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Complexity.Classes.TFNP.Subclasses.PotentialLineCollapse

/-! Concrete clients for `EOPL = SOPL ∩ PPAD`: the combined end-of-potential-line instance built
from two single-edge families, its edges, its ends and their decoding, and a relation placed in
`EOPL` through `SOPL_inter_PPAD_subset_EOPL`. -/

namespace CslibFrontierTests.TFNPPotentialLineCollapse

open Cslib Cslib.BitString Cslib.Complexity Turing.MultiTapeTM

/-! ### Two single-edge families on `{0, 1}`

Both the sink-of-potential-line family `(n1, P1, S1, V1)` and the end-of-line family
`(n1, P1, S1)` are the single edge `0 → 1`, with potential `V1 u = binaryValue u < 2`. Its unique
sink, and its unique end-of-line solution, is `1`. -/

private def n1 : Unit → ℕ := fun _ => 1
private def S1 : Unit × List Bool → List Bool := fun _ => [true]
private def P1 : Unit × List Bool → List Bool := fun _ => [false]
private def V1 : Unit × List Bool → ℕ := fun p => binaryValue p.2
private def B2 : Unit → ℕ := fun _ => 2

private abbrev succ := soplPpadSucc n1 P1 S1 V1 n1 P1 S1
private abbrev pred := soplPpadPred n1 P1 S1 V1 n1 P1 S1
private abbrev pot := soplPpadPotential V1 n1 B2

/-- The combined instance on `b :: (y ++ x) ∈ {0, 1} ^ 3`. The new source `000` is the pigeon at
`y = 0`; it follows the end-of-line edge `0 → 1` to the hole `110`, the forward copy of the
distinguished source, and then the forward copy of `0 → 1` to `111`. The reversed copy of
`0 → 1` at `y = 1` is `011 → 010`. Potentials increase along both lines. -/
example : succ ((), [false, false, false]) = [true, true, false] ∧
    succ ((), [true, true, false]) = [true, true, true] ∧
    succ ((), [true, true, true]) = [true, true, true] ∧
    pred ((), [true, true, true]) = [true, true, false] ∧
    pred ((), [true, true, false]) = [false, false, false] ∧
    succ ((), [false, true, true]) = [false, true, false] ∧
    pred ((), [false, true, false]) = [false, true, true] ∧
    pot ((), [false, false, false]) < pot ((), [true, true, false]) ∧
    pot ((), [true, true, false]) < pot ((), [true, true, true]) ∧
    pot ((), [false, true, true]) < pot ((), [false, true, false]) := by
  decide

/-- The ends of the combined instance are exactly `111`, `011` and `010`: the sink of the forward
line, and the source and sink of the reversed line. The new source `000`, the inner vertex `110`
and the isolated junk vertices `001`, `100`, `101` are not ends. -/
example :
    let E := endOfPotentialLineRel (fun a => n1 a + n1 a + 1) pred succ pot ()
    E [true, true, true] ∧ E [false, true, true] ∧ E [false, true, false] ∧
      ¬E [false, false, false] ∧ ¬E [true, true, false] ∧ ¬E [false, false, true] ∧
      ¬E [true, false, false] ∧ ¬E [true, false, true] := by
  unfold endOfPotentialLineRel
  decide

/-- Decoding: the ends `111` and `011` have `x = 1`, a sink of the potential line, and the end
`010` has `y = 1`, an end-of-line solution; `x = 0` is not a sink. -/
example : sinkOfPotentialLineRel n1 P1 S1 V1 () [true] ∧
    endOfLineRel n1 P1 S1 () [true] ∧ ¬sinkOfPotentialLineRel n1 P1 S1 V1 () [false] := by
  unfold sinkOfPotentialLineRel endOfLineRel
  decide

private theorem hlenU (S : Unit × List Bool → List Bool) (hS : ∀ p, (S p).length = 1)
    (u : List Bool) (_ : u.length = n1 ()) : (S ((), u)).length = n1 () := hS ((), u)

private theorem hB2 (u : List Bool) (hu : u.length = n1 ()) : V1 ((), u) < B2 () := by
  obtain ⟨c, rfl⟩ := List.length_eq_one_iff.mp hu
  cases c <;> decide

/-- `soplPpad_end` applies to the combined instance, with every hypothesis discharged. -/
example (b : Bool) (y x : List Bool) (hy : y.length = 1) (hx : x.length = 1)
    (h : endOfPotentialLineRel (fun a => n1 a + n1 a + 1) pred succ pot () (b :: (y ++ x))) :
    sinkOfPotentialLineRel n1 P1 S1 V1 () x ∨ endOfLineRel n1 P1 S1 () y :=
  soplPpad_end (hlenU S1 fun _ => rfl) (hlenU P1 fun _ => rfl) (hlenU S1 fun _ => rfl) hB2 hy hx h

/-! ### A relation in `SOPL ∩ PPAD`, hence in `EOPL`

The sink-of-potential-line relation of the uniform single-edge family over `List Bool` is in
`SOPL` by definition and coincides with the end-of-line relation of the same family, so it is in
`PPAD`; the collapse places it in `EOPL`. -/

private def m1 : List Bool → ℕ := fun _ => 1
private def T1 : List Bool × List Bool → List Bool := fun _ => [true]
private def Q1 : List Bool × List Bool → List Bool := fun _ => [false]
private def W1 : List Bool × List Bool → ℕ := fun p => binaryValue p.2

private theorem hm1 : ComputableInPolyTime m1 encBits encUnary := ComputableInPolyTime.const 1
private theorem hT1 : ComputableInPolyTime T1 (encPair encBits encBits) encBits :=
  ComputableInPolyTime.const [true]
private theorem hQ1 : ComputableInPolyTime Q1 (encPair encBits encBits) encBits :=
  ComputableInPolyTime.const [false]
private theorem hW1 : ComputableInPolyTime W1 (encPair encBits encBits) encNat :=
  computableInPolyTime_binaryValue_comp (ComputableInPolyTime.snd encBits encBits)
private theorem hlen1 (S : List Bool × List Bool → List Bool) (hS : ∀ p, (S p).length = 1)
    (a u : List Bool) (_ : u.length = m1 a) : (S (a, u)).length = m1 a := hS (a, u)

private theorem sink_eq_endOfLine :
    sinkOfPotentialLineRel m1 Q1 T1 W1 = endOfLineRel m1 Q1 T1 := by
  funext a u
  change sinkOfPotentialLineRel m1 Q1 T1 W1 [] u = endOfLineRel m1 Q1 T1 [] u
  clear a
  unfold sinkOfPotentialLineRel endOfLineRel hasPotentialOut hasPotentialIn hasOut hasIn
  simp only [m1, Q1, T1, W1]
  apply propext
  rcases u with _ | ⟨c, _ | ⟨d, u⟩⟩
  · simp
  · cases c <;> decide
  · simp

private theorem sopl1 : sinkOfPotentialLineRel m1 Q1 T1 W1 ∈ SOPL encBits :=
  sinkOfPotentialLineRel_mem_SOPL hm1 hQ1 hT1 hW1 (hlen1 Q1 fun _ => rfl) (hlen1 T1 fun _ => rfl)

private theorem ppad1 : sinkOfPotentialLineRel m1 Q1 T1 W1 ∈ PPAD encBits := by
  rw [sink_eq_endOfLine]
  exact endOfLineRel_mem_PPAD hm1 hQ1 hT1 (hlen1 Q1 fun _ => rfl) (hlen1 T1 fun _ => rfl)

example : sinkOfPotentialLineRel m1 Q1 T1 W1 ∈ EOPL encBits :=
  SOPL_inter_PPAD_subset_EOPL ⟨sopl1, ppad1⟩

end CslibFrontierTests.TFNPPotentialLineCollapse
