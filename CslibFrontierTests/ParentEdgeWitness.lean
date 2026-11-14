/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

import CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.ParentEdgeWitness

open Cslib.Circuits.Frontier.NativeChild

private abbrev groups : List ℕ := [0, 1, 1]
private abbrev ends : List (ℕ × ℕ) := [(1, 2), (0, 2), (1, 0)]

/- The parent sequence is [0, 2, 0, 1]: an edge may occur once as a row port and once
as a column port. The row witness has nonzero predecessor rank. -/
example : 1 < (portEdges groups 1 ends Prod.fst).length +
    (portEdges groups 1 ends Prod.snd).length ∧ parentEdge groups 1 ends 1 = 2 := by
  apply (parentEdge_witness_iff_bits groups 1 ends (width := 2) (rows := 2)
    (by decide) (by decide) (by decide)).mpr
  decide

/- The column witness needs both a nonzero row offset and a nonzero column rank. -/
example : 3 < (portEdges groups 1 ends Prod.fst).length +
    (portEdges groups 1 ends Prod.snd).length ∧ parentEdge groups 1 ends 3 = 1 := by
  apply (parentEdge_witness_iff_bits groups 1 ends (width := 2) (rows := 2)
    (by decide) (by decide) (by decide)).mpr
  decide

/- Certifying the same endpoint and prefix rank at the wrong offset is rejected. -/
example : ¬ (2 < (portEdges groups 1 ends Prod.fst).length +
    (portEdges groups 1 ends Prod.snd).length ∧ parentEdge groups 1 ends 2 = 1) := by
  rw [parentEdge_witness_iff_bits groups 1 ends (width := 2) (rows := 2)
    (by decide) (by decide) (by decide)]
  decide

/- With no matching ports, getD returns zero. The bounded characterization rejects it. -/
example : parentEdge [0] 1 [(0, 0)] 0 = 0 ∧
    ¬ (0 < (portEdges [0] 1 [(0, 0)] Prod.fst).length +
      (portEdges [0] 1 [(0, 0)] Prod.snd).length ∧ parentEdge [0] 1 [(0, 0)] 0 = 0) := by
  constructor
  · decide
  · rw [parentEdge_witness_iff]
    decide

/- Even when default endpoints have the selected group, an empty parent has no witness. -/
example : ¬ (0 < (portEdges [] 0 [] Prod.fst).length +
    (portEdges [] 0 [] Prod.snd).length ∧ parentEdge [] 0 [] 0 = 0) := by
  rw [parentEdge_witness_iff]
  decide

/- A full four-edge prefix needs three bits for its total. The logarithmic API accepts four. -/
example : 4 = portRank [1, 0] 1 (List.replicate 4 (0, 1)) Prod.fst 4 := by
  apply (eq_portRank_iff_clog_predecessor_bits [1, 0] 1 (List.replicate 4 (0, 1))
    Prod.fst (by decide) (by decide)).mpr
  decide

/- The same full-prefix total is read through the actual ordinary count-bit interface. -/
example : Cslib.Circuits.Boolean.CarrySaveQuery.Counting.count 4 3
    (portPredecessor [1, 0] 1 (List.replicate 4 (0, 1)) Prod.fst 4) 2 = true := by
  have h := count_portPredecessor [1, 0] 1 (List.replicate 4 (0, 1)) Prod.fst
    (bound := 4) (by decide) (2 : Fin 3)
  rw [List.length_replicate] at h
  exact h.trans (by decide)

/- Two bits would confuse the full count four with zero. This is why the total-count theorem
requires edgeCount < 2^width, rather than the non-strict rank bound. -/
example :
    (∀ bit : Fin 2, (0 : ℕ).testBit bit.val =
      (∑ candidate : Fin 4,
        (portPredecessor [1, 0] 1 (List.replicate 4 (0, 1)) Prod.fst 4 candidate).toNat).testBit
          bit.val) ∧
      0 ≠ portRank [1, 0] 1 (List.replicate 4 (0, 1)) Prod.fst 4 := by
  decide

/- The empty full prefix uses zero bits, with zero as its only bounded guess. -/
example : 0 = portRank [] 0 [] Prod.fst 0 := by
  apply (eq_portRank_iff_clog_predecessor_bits [] 0 [] Prod.fst
    (by decide) (by decide)).mpr
  intro bit
  exact Fin.elim0 bit
