/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Complexity.Classes.TFNP.Subclasses.SOPLCollapse

/-! Concrete clients for `SOPL = PLS ∩ PPADS` and `EOPL = PLS ∩ PPAD`: the combined
sink-of-potential-line instance built from a single-step `PLS` family and a single-edge `PPADS`
family, its intra-gadget and inter-gadget paths, both types of sinks (`PLS` local optima and
`PPADS` gadget sinks), `plsPpads_sink` with all hypotheses discharged, and uniform relations placed
in `SOPL` and `EOPL` through `PLS_inter_PPADS_subset_SOPL`, `SOPL_eq_PLS_inter_PPADS`,
`PLS_inter_PPAD_subset_EOPL`, and `EOPL_eq_PLS_inter_PPAD`. -/

namespace CslibFrontierTests.TFNPSOPLCollapse

open Cslib Cslib.BitString Cslib.Complexity Turing.MultiTapeTM

/-! ### Concrete combined `SOPL` instance on `1 + 2 + 2 = 5` bits

* `PLS` family `(n1, N1, C1)` on `{0, 1}`: `N1` maps both vertices to `0`, with `C1 (0) = 0` and
  `C1 (1) = 1 < 2 = B2`. Vertex `1` steps to the unique local optimum `0`.
* `PPADS` family `(n1, P2, S2)` on `{0, 1}`: single directed edge `0 → 1`, with unique sink `1`.
* Combined parameters: `m = 2`, `T = 4`, `K = 2`, `M = 2`, width `5` (`x` of width `1`, `z` and `r`
  of width `2`). -/

private def n1 : Unit → ℕ := fun _ => 1
private def N1 : Unit × List Bool → List Bool := fun _ => [false]
private def C1 : Unit × List Bool → ℕ := fun p => binaryValue p.2
private def S2 : Unit × List Bool → List Bool := fun _ => [true]
private def P2 : Unit × List Bool → List Bool := fun _ => [false]
private def B2 : Unit → ℕ := fun _ => 2

private abbrev succ := plsPpadsSucc n1 N1 C1 n1 P2 S2
private abbrev pred := plsPpadsPred n1 N1 C1 n1 P2 S2
private abbrev pot := plsPpadsPotential n1 C1 n1 B2

/-- Path 1 (surviving pigeon through the gadget and across the `PLS` step):
`(1, 0, 0) → (1, 0, 1) → (1, 0, 2) → (0, 2, 0)`, with potentials `4 < 5 < 6 < 8` and reversible
predecessor links at every step. -/
example :
    succ ((), [true, false, false, false, false]) = [true, false, false, false, true] ∧
    succ ((), [true, false, false, false, true]) = [true, false, false, true, false] ∧
    succ ((), [true, false, false, true, false]) = [false, true, false, false, false] ∧
    succ ((), [false, true, false, false, false]) = [false, true, false, false, false] ∧
    pred ((), [false, true, false, false, false]) = [true, false, false, true, false] ∧
    pred ((), [true, false, false, true, false]) = [true, false, false, false, true] ∧
    pred ((), [true, false, false, false, true]) = [true, false, false, false, false] ∧
    pot ((), [true, false, false, false, false]) = 4 ∧
    pot ((), [true, false, false, false, true]) = 5 ∧
    pot ((), [true, false, false, true, false]) = 6 ∧
    pot ((), [false, true, false, false, false]) = 8 := by
  decide

/-- Path 2 (shift step colliding with the `PPADS` sink inside the gadget of non-optimal `x = 1`):
`(1, 2, 0) → (1, 1, 1)`, where `(1, 1, 1)` (`[true, false, true, false, true]`) stops with
potential increase `4 < 5`. -/
example :
    succ ((), [true, true, false, false, false]) = [true, false, true, false, true] ∧
    succ ((), [true, false, true, false, true]) = [true, false, true, false, true] ∧
    pred ((), [true, false, true, false, true]) = [true, true, false, false, false] ∧
    pot ((), [true, true, false, false, false]) < pot ((), [true, false, true, false, true]) := by
  decide

/-- Both types of sinks appear in `sinkOfPotentialLineRel` of the combined instance:
* `[false, false, false, false, false]` (`0 ^ 5`) and `[false, true, false, false, false]`
  (`(0, 2, 0)`) are sinks at `PLS` local optimum `x = [false]`;
* `[true, false, true, false, true]` (`(1, 1, 1)`) is an internal gadget sink at non-optimal
  `x = [true]`, decoding to the `PPADS` sink `binaryWord 1 1 = [true]`;
* internal vertices `(1, 0, 0)` and `(1, 0, 2)` and unreachable `(1, 1, 0)` are not sinks. -/
example :
    let S := sinkOfPotentialLineRel (plsPpadsWidth n1 n1) pred succ pot ()
    S [false, false, false, false, false] ∧
      S [false, true, false, false, false] ∧
      S [true, false, true, false, true] ∧
      ¬S [true, false, false, false, false] ∧
      ¬S [true, false, false, true, false] ∧
      ¬S [true, false, true, false, false] ∧
      localOptRel n1 N1 C1 () [false] ∧
      ¬localOptRel n1 N1 C1 () [true] ∧
      sinkOfLineRel n1 P2 S2 () [true] ∧
      ¬sinkOfLineRel n1 P2 S2 () [false] := by
  unfold sinkOfPotentialLineRel localOptRel sinkOfLineRel
  decide

private theorem hlenU (F : Unit × List Bool → List Bool) (hF : ∀ p, (F p).length = 1)
    (u : List Bool) (_ : u.length = n1 ()) : (F ((), u)).length = n1 () := hF ((), u)

private theorem hB2 (u : List Bool) (hu : u.length = n1 ()) : C1 ((), u) < B2 () := by
  obtain ⟨c, rfl⟩ := List.length_eq_one_iff.mp hu
  cases c <;> decide

/-- `plsPpads_sink` instantiated on the concrete 5-bit combined instance with every hypothesis
discharged. -/
example (x z r : List Bool) (hx : x.length = 1) (hz : z.length = 2) (hr : r.length = 2)
    (h : sinkOfPotentialLineRel (plsPpadsWidth n1 n1) pred succ pot () (x ++ (z ++ r))) :
    localOptRel n1 N1 C1 () x ∨ sinkOfLineRel n1 P2 S2 () (binaryWord 1 (binaryValue z)) :=
  plsPpads_sink (hlenU N1 fun _ => rfl) (hlenU P2 fun _ => rfl) (hlenU S2 fun _ => rfl) hB2
    hx hz hr h

/-! ### Uniform family in `PLS ∩ PPAD` (and `PLS ∩ PPADS`), hence in `SOPL` and `EOPL`

On `{0, 1}` over `List Bool` instances, the single-edge relation `{[true]}` equals both
`localOptRel m1 M1 K1` (where `M1 _ = [true]` and `K1 (0) = 1 > K1 (1) = 0`) and
`endOfLineRel m1 Q1 T1` (where `0 → 1`). The collapses place it in `SOPL` and `EOPL` and check
both set equalities `SOPL = PLS ∩ PPADS` and `EOPL = PLS ∩ PPAD`. -/

private def m1 : List Bool → ℕ := fun _ => 1
private def T1 : List Bool × List Bool → List Bool := fun _ => [true]
private def Q1 : List Bool × List Bool → List Bool := fun _ => [false]
private def K1 : List Bool × List Bool → ℕ := fun p => 1 - binaryValue p.2

private theorem hm1 : ComputableInPolyTime m1 encBits encUnary := ComputableInPolyTime.const 1
private theorem hT1 : ComputableInPolyTime T1 (encPair encBits encBits) encBits :=
  ComputableInPolyTime.const [true]
private theorem hQ1 : ComputableInPolyTime Q1 (encPair encBits encBits) encBits :=
  ComputableInPolyTime.const [false]
private theorem hK1 : ComputableInPolyTime K1 (encPair encBits encBits) encNat := by
  unfold K1
  exact ComputableInPolyTime.binary_sub' (ComputableInPolyTime.const 1)
    (computableInPolyTime_binaryValue_comp (ComputableInPolyTime.snd encBits encBits))

private theorem hlen1 (F : List Bool × List Bool → List Bool) (hF : ∀ p, (F p).length = 1)
    (a u : List Bool) (_ : u.length = m1 a) : (F (a, u)).length = m1 a := hF (a, u)

private theorem localOpt_eq_endOfLine :
    localOptRel m1 T1 K1 = endOfLineRel m1 Q1 T1 := by
  funext a u
  change localOptRel m1 T1 K1 [] u = endOfLineRel m1 Q1 T1 [] u
  clear a
  unfold localOptRel endOfLineRel hasOut hasIn
  simp only [m1, Q1, T1, K1]
  apply propext
  rcases u with _ | ⟨c, _ | ⟨d, u⟩⟩
  · simp
  · cases c <;> decide
  · simp

private theorem pls1 : endOfLineRel m1 Q1 T1 ∈ PLS encBits := by
  rw [← localOpt_eq_endOfLine]
  exact localOptRel_mem_PLS hm1 hT1 hK1 (hlen1 T1 fun _ => rfl)

private theorem ppad1 : endOfLineRel m1 Q1 T1 ∈ PPAD encBits :=
  endOfLineRel_mem_PPAD hm1 hQ1 hT1 (hlen1 Q1 fun _ => rfl) (hlen1 T1 fun _ => rfl)

private theorem ppads1 : endOfLineRel m1 Q1 T1 ∈ PPADS encBits :=
  PPAD_subset_PPADS ppad1

example : endOfLineRel m1 Q1 T1 ∈ SOPL encBits :=
  PLS_inter_PPADS_subset_SOPL ⟨pls1, ppads1⟩

example : endOfLineRel m1 Q1 T1 ∈ SOPL encBits := by
  rw [SOPL_eq_PLS_inter_PPADS]
  exact ⟨pls1, ppads1⟩

example : endOfLineRel m1 Q1 T1 ∈ EOPL encBits :=
  PLS_inter_PPAD_subset_EOPL ⟨pls1, ppad1⟩

example : endOfLineRel m1 Q1 T1 ∈ EOPL encBits := by
  rw [EOPL_eq_PLS_inter_PPAD]
  exact ⟨pls1, ppad1⟩

end CslibFrontierTests.TFNPSOPLCollapse
