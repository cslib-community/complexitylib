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
remaining hypothesis. That instance is an `EntryContractionAlgorithm` whose `bound` applies to an
admissible input, the network of two parallel edges at size `2`, so the interface is not vacuous.
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

/-! ### The interface is not vacuous -/

/-- The network of two parallel edges is admissible at size `2` with the entry procedure of
tables, for some constant. -/
theorem exists_entryAdmissible_twoEdges :
    ∃ C, EntryAdmissible tableEntryCertificate C 2 (1, twoEdges) := by
  obtain ⟨C₀, hC₀⟩ := exists_entryAdmissible_of_isPolynomial
    tableEntryCertificate_isPolynomial
  have h2 : ceilNineTenths 2 = 2 :=
    le_antisymm (ceilNineTenths_le (by norm_num)) ((le_ceilNineTenths_iff (by norm_num)).2
      (by norm_num))
  refine ⟨C₀ + 1, hC₀ (C₀ + 1) 2 1 twoEdges (by omega) (by decide) le_rfl (by simp) ?_⟩
  intro v hv
  rw [h2]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl <;> rfl

-- The bound of the instance applies to that admissible input: at size `2`, precision `1` and the
-- modulus of its two edges, the time and space of the certificate are within the bound.
example : ∃ C K : ℕ, EntryAdmissible tableEntryCertificate C 2 (1, twoEdges) ∧
    tableAlgorithm.certificate.time (1, FastContraction.modulus 2, 1, twoEdges) ≤
        K * ((encInput (encList encNat) (1, FastContraction.modulus 2, 1, twoEdges)).length +
          1) ^ K * 2 ^ (K * 2 / Nat.sqrt (Nat.log 2 2)) ∧
      tableAlgorithm.certificate.space (1, FastContraction.modulus 2, 1, twoEdges) ≤
        K * ((encInput (encList encNat) (1, FastContraction.modulus 2, 1, twoEdges)).length +
          1) ^ K := by
  obtain ⟨C, hC⟩ := exists_entryAdmissible_twoEdges
  obtain ⟨K, hK⟩ := tableAlgorithm.bound C 1
  exact ⟨C, K, hC, hK 2 1 1 twoEdges le_rfl le_rfl (by norm_num) hC⟩

end ComplexityTests.TensorNetworkEntryAnalysis
