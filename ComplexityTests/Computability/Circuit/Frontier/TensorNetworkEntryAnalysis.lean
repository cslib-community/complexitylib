/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import Complexity.Computability.Complexity.Classes.CountingSimulation.EntryAnalysis

/-!
# Tests for the contraction algorithm with entry procedures

The guard of the entry machine on a network of two parallel edges between a row vertex and a
column vertex, at the modulus of its number of edges and at another modulus; the guarded root is
well-formed and has no packets; an admissible input passes the guard; and the contraction
algorithm for entry procedures, instantiated at the entry procedure of tables, is correct with no
remaining hypothesis.
-/

@[expose] public section

namespace ComplexityTests.TensorNetworkEntryAnalysis

open Cslib Cslib.Circuits.Frontier Cslib.Circuits.Frontier.EntryContraction
  Cslib.Complexity.CountingSimulation
open Turing.MultiTapeTM (encList encNat)

/-- Two parallel edges between a row vertex with table `1, 2, 3, 4` and a column vertex of
ones. -/
abbrev twoEdges : DescribedNetwork (List ℕ) := ⟨2, [([0, 1], [1, 2, 3, 4]), ([0, 1], [1, 1, 1, 1])]⟩

/-! ### The guard -/

-- The guard holds at the modulus of the number of edges.
example : EntryContraction.guard (3, FastContraction.modulus 2, 1, twoEdges) = true := by decide

-- It fails at another modulus, and when the rows are not first.
example : EntryContraction.guard (3, [1, 1], 1, twoEdges) = false := by decide

example : EntryContraction.guard (3, FastContraction.modulus 2, 0, twoEdges) = false := by decide

-- The guarded root is well-formed and has no packets.
example : FastContraction.WF (rootCall (3, FastContraction.modulus 2, 1, twoEdges)) ∧
    FastContraction.PacketShape (rootCall (3, FastContraction.modulus 2, 1, twoEdges)) :=
  ⟨wf_rootCall (by decide), packetShape_rootCall _⟩

-- An admissible input passes the guard at the modulus, at every precision.
example (P : ℕ) {C s : ℕ} (hA : EntryAdmissible tableEntryCertificate C s (1, twoEdges)) :
    EntryContraction.guard (P, FastContraction.modulus twoEdges.numEdges, 1, twoEdges) = true :=
  guard_of_entryAdmissible hA

/-! ### Root descriptors along the recursion -/

-- Every root descriptor of a reached call comes from a vertex of the input with as many ports.
example (x : ℕ × List ℕ × ℕ × DescribedNetwork (List ℕ)) (y : FastContraction.Call (List ℕ))
    (hy : FastContraction.Reach FastContraction.nativeMk (rootCall x) y)
    (v : List ℕ × VertexDesc (List ℕ)) (hv : v ∈ y.net.vertices) (t : List ℕ)
    (ht : v.2 = .inl t) : ∃ w ∈ x.2.2.2.vertices, w.2 = t ∧ w.1.length = v.1.length := by
  obtain ⟨w, hw, hwt, hlen⟩ := hy.exists_root_of_inl hv ht
  change w ∈ List.map _ x.2.2.2.vertices at hw
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hw
  exact ⟨u, hu, Sum.inl_injective hwt, hlen⟩

/-! ### The contraction algorithm -/

/-- The contraction algorithm for the entry procedure of tables, with no remaining hypothesis. -/
noncomputable def tableAlgorithm :
    EntryContractionAlgorithm (encList encNat) tableEntry (EntryAdmissible tableEntryCertificate) :=
  entryContractionAlgorithm tableEntryCertificate

-- It is correct at the modulus of the number of edges.
example : GaloisRingArith.val 3 (FastContraction.modulus 2)
    (tableAlgorithm.core (3, FastContraction.modulus 2, 1, twoEdges)) =
      ((10 : ℕ) : GaloisRingArith.Ring 3 (FastContraction.modulus 2)) := by
  have hval := val_directCore_tableEntry 3 (FastContraction.modulus 2) twoEdges
  rw [val_directCore] at hval
  refine (tableAlgorithm.val_core 3 1 twoEdges).trans (hval.trans ?_)
  congr 1

-- Its bound holds for all constants.
example (C D : ℕ) : ∃ K : ℕ, ∀ (s P r : ℕ) (G : DescribedNetwork (List ℕ)), 2 ≤ s → 1 ≤ P →
    P ≤ D * s → EntryAdmissible tableEntryCertificate C s (r, G) →
      tableAlgorithm.certificate.time (P, FastContraction.modulus G.numEdges, r, G) ≤
          K * ((encInput (encList encNat) (P, FastContraction.modulus G.numEdges, r, G)).length +
            1) ^ K * 2 ^ (K * s / Nat.sqrt (Nat.log 2 s)) ∧
        tableAlgorithm.certificate.space (P, FastContraction.modulus G.numEdges, r, G) ≤
          K * ((encInput (encList encNat) (P, FastContraction.modulus G.numEdges, r, G)).length +
            1) ^ K :=
  tableAlgorithm.bound C D

end ComplexityTests.TensorNetworkEntryAnalysis
