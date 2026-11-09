/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Complexity.Classes.TFNP.Subclasses.PotentialLine

/-! Concrete clients for `PPADS`, `SOPL` and `EOPL`: solutions and non-solutions of the
sink-of-line, end-of-potential-line and sink-of-potential-line relations on small graphs, an edge
removed by the potential, the circuit-style violation relations of Fearnley et al., and class
memberships of a nontrivial uniform family. -/

namespace CslibFrontierTests.TFNPPotentialLine

open Cslib Cslib.BitString Cslib.Complexity Turing.MultiTapeTM

/-! ### Two lines on `{0, 1} ^ 2`: `00 → 01` and `10 → 11` -/

private def n2 : Unit → ℕ := fun _ => 2

/-- Successor of the two-line graph `00 → 01`, `10 → 11`. -/
private def S2 (p : Unit × List Bool) : List Bool :=
  if p.2 = [false, false] then [false, true]
  else if p.2 = [true, false] then [true, true] else p.2

/-- Predecessor of the two-line graph `00 → 01`, `10 → 11`. -/
private def P2 (p : Unit × List Bool) : List Bool :=
  if p.2 = [false, true] then [false, false]
  else if p.2 = [true, true] then [true, false] else p.2

/-- A potential increasing along both edges. -/
private def V2 (p : Unit × List Bool) : ℕ :=
  if p.2 = [false, false] then 0 else if p.2 = [false, true] then 1
  else if p.2 = [true, false] then 2 else 3

/-- A potential increasing along `00 → 01` but not along `10 → 11`. -/
private def W2 (p : Unit × List Bool) : ℕ :=
  if p.2 = [true, true] then 0 else V2 p

/-! #### `PPADS`: proper sources are ends of lines, but not sinks -/

/-- The sink `11` solves `sinkOfLineRel`. -/
example : sinkOfLineRel n2 P2 S2 () [true, true] := by
  unfold sinkOfLineRel
  decide

/-- The proper source `10` solves `endOfLineRel` but not `sinkOfLineRel`. -/
example : endOfLineRel n2 P2 S2 () [true, false] ∧ ¬sinkOfLineRel n2 P2 S2 () [true, false] := by
  unfold sinkOfLineRel endOfLineRel
  decide

/-- The source `00` with an outgoing edge solves neither relation. -/
example : ¬endOfLineRel n2 P2 S2 () [false, false] ∧ ¬sinkOfLineRel n2 P2 S2 () [false, false] := by
  unfold sinkOfLineRel endOfLineRel
  decide

/-! #### `EOPL` and `SOPL` with a potential increasing along every edge -/

/-- The sinks `01` and `11` solve both potential-line relations. -/
example : sinkOfPotentialLineRel n2 P2 S2 V2 () [false, true] ∧
    sinkOfPotentialLineRel n2 P2 S2 V2 () [true, true] ∧
    endOfPotentialLineRel n2 P2 S2 V2 () [false, true] ∧
    endOfPotentialLineRel n2 P2 S2 V2 () [true, true] := by
  unfold sinkOfPotentialLineRel endOfPotentialLineRel
  decide

/-- The proper source `10` is an end of a potential line but not a sink of one. -/
example : endOfPotentialLineRel n2 P2 S2 V2 () [true, false] ∧
    ¬sinkOfPotentialLineRel n2 P2 S2 V2 () [true, false] := by
  unfold sinkOfPotentialLineRel endOfPotentialLineRel
  decide

/-- The distinguished source `00` is not a solution. -/
example : ¬endOfPotentialLineRel n2 P2 S2 V2 () [false, false] := by
  unfold endOfPotentialLineRel
  decide

/-! #### Pruning: the edge `10 → 11` does not increase the potential `W2` -/

/-- With `W2`, the edge `10 → 11` is pruned (`hasPotentialOut` fails although `hasOut` holds),
so the pruned graph has the single edge `00 → 01`. -/
example : hasOut n2 P2 S2 () [true, false] = true ∧
    hasPotentialOut n2 P2 S2 W2 () [true, false] = false := by
  decide

/-- After pruning, `10` and `11` are isolated: neither is an end of a potential line, although `11`
is still an end of the raw line. -/
example : ¬endOfPotentialLineRel n2 P2 S2 W2 () [true, false] ∧
    ¬endOfPotentialLineRel n2 P2 S2 W2 () [true, true] ∧
    endOfLineRel n2 P2 S2 () [true, true] ∧
    endOfPotentialLineRel n2 P2 S2 W2 () [false, true] := by
  unfold endOfLineRel endOfPotentialLineRel
  decide

/-- The pruned maps present the pruned graph: `potentialSucc` fixes `10`. -/
example : potentialSucc n2 P2 S2 W2 ((), [true, false]) = [true, false] ∧
    potentialSucc n2 P2 S2 W2 ((), [false, false]) = [false, true] := by
  decide

/-! #### The circuit-style violation relations of Fearnley et al. -/

/-- With `W2`, `10` is a potential (R2) violation, which is a sink-type violation. -/
example : endOfPotentialLineViolationRel n2 P2 S2 W2 () [true, false] ∧
    sinkOfPotentialLineViolationRel n2 P2 S2 W2 () [true, false] := by
  unfold endOfPotentialLineViolationRel sinkOfPotentialLineViolationRel LineSourcePromise
  decide

/-- With `V2`, the proper source `10` is a start-of-line (R1) violation, which is not a sink-type
violation; the source `00` is not a violation. -/
example : endOfPotentialLineViolationRel n2 P2 S2 V2 () [true, false] ∧
    ¬sinkOfPotentialLineViolationRel n2 P2 S2 V2 () [true, false] ∧
    ¬endOfPotentialLineViolationRel n2 P2 S2 V2 () [false, false] := by
  unfold endOfPotentialLineViolationRel sinkOfPotentialLineViolationRel LineSourcePromise
  decide

/-- The identity maps violate the promise `P (0 ^ n) = 0 ^ n ≠ S (0 ^ n)`, so `0 ^ n` is a
violation. -/
example : ¬LineSourcePromise n2 Prod.snd Prod.snd () ∧
    endOfPotentialLineViolationRel n2 Prod.snd Prod.snd V2 () [false, false] := by
  unfold endOfPotentialLineViolationRel LineSourcePromise
  decide

/-- The back-map: with `V2` the proper source `10` is its own (R1) witness, with `W2` the sink `11`
of the raw line is sent to its predecessor `10`, an (R2) witness, and when the promise fails every
vertex is sent to `00`. -/
example : potentialLineBack n2 P2 S2 V2 ((), [true, false]) = [true, false] ∧
    potentialLineBack n2 P2 S2 W2 ((), [true, true]) = [true, false] ∧
    potentialLineBack n2 Prod.snd Prod.snd V2 ((), [true, true]) = [false, false] := by
  decide

/-! ### A uniform polynomial-time family on `{0, 1}`: the single edge `0 → 1` -/

private def n1 : List Bool → ℕ := fun _ => 1
private def S1 : List Bool × List Bool → List Bool := fun _ => [true]
private def P1 : List Bool × List Bool → List Bool := fun _ => [false]
private def V1 : List Bool × List Bool → ℕ := fun p => binaryValue p.2

private theorem hn1 : ComputableInPolyTime n1 encBits encUnary := ComputableInPolyTime.const 1
private theorem hS1 : ComputableInPolyTime S1 (encPair encBits encBits) encBits :=
  ComputableInPolyTime.const [true]
private theorem hP1 : ComputableInPolyTime P1 (encPair encBits encBits) encBits :=
  ComputableInPolyTime.const [false]
private theorem hV1 : ComputableInPolyTime V1 (encPair encBits encBits) encNat :=
  computableInPolyTime_binaryValue_comp (ComputableInPolyTime.snd encBits encBits)
private theorem hlen1 (S : List Bool × List Bool → List Bool) (hS : ∀ p, (S p).length = 1)
    (a u : List Bool) (_ : u.length = n1 a) : (S (a, u)).length = n1 a := hS (a, u)

/-- In the single-edge family, `1` is the unique end of the potential line. -/
example : endOfPotentialLineRel n1 P1 S1 V1 [] [true] ∧
    ¬endOfPotentialLineRel n1 P1 S1 V1 [] [false] := by
  unfold endOfPotentialLineRel
  decide

private theorem eopl1 : endOfPotentialLineRel n1 P1 S1 V1 ∈ EOPL encBits :=
  endOfPotentialLineRel_mem_EOPL hn1 hP1 hS1 hV1 (hlen1 P1 fun _ => rfl) (hlen1 S1 fun _ => rfl)

example : endOfPotentialLineRel n1 P1 S1 V1 ∈ SOPL encBits := EOPL_subset_SOPL eopl1
example : endOfPotentialLineRel n1 P1 S1 V1 ∈ PLS encBits ∩ PPAD encBits :=
  EOPL_subset_PLS_inter_PPAD eopl1
example : endOfPotentialLineRel n1 P1 S1 V1 ∈ PPADS encBits :=
  PPAD_subset_PPADS (EOPL_subset_PPAD eopl1)
example : endOfPotentialLineRel n1 P1 S1 V1 ∈ PPP encBits :=
  PPADS_subset_PPP (SOPL_subset_PPADS (EOPL_subset_SOPL eopl1))
example : endOfPotentialLineRel n1 P1 S1 V1 ∈ TFNP encBits := EOPL_subset_TFNP eopl1

example : sinkOfPotentialLineRel n1 P1 S1 V1 ∈ PLS encBits ∩ PPADS encBits :=
  SOPL_subset_PLS_inter_PPADS
    (sinkOfPotentialLineRel_mem_SOPL hn1 hP1 hS1 hV1 (hlen1 P1 fun _ => rfl)
      (hlen1 S1 fun _ => rfl))

example : sinkOfLineRel n1 P1 S1 ∈ PPP encBits :=
  PPADS_subset_PPP
    (sinkOfLineRel_mem_PPADS hn1 hP1 hS1 (hlen1 P1 fun _ => rfl) (hlen1 S1 fun _ => rfl))

/-- The circuit-style relation of Fearnley et al. for the single-edge family is in `EOPL`. -/
example : endOfPotentialLineViolationRel n1 P1 S1 V1 ∈ EOPL encBits :=
  endOfPotentialLineViolationRel_mem_EOPL hn1 hP1 hS1 hV1 (hlen1 P1 fun _ => rfl)
    (hlen1 S1 fun _ => rfl)

end CslibFrontierTests.TFNPPotentialLine
