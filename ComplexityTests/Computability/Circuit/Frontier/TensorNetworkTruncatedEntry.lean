/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import Complexity.Computability.Complexity.Classes.CountingSimulation.TruncatedEntry

/-!
# Tests for Theorem D.1 at truncation order `ℓ` for entry procedures

A network of two parallel edges between a row vertex and a column vertex is admissible at size `2`
with the entry procedure of tables, with its two vertices (`TruncEntryAdmissible` is not vacuous);
its specialization at a point is rows-first and admissible for the specialized entries; and the
truncated contraction algorithm for entry procedures, instantiated at the entry procedure of
tables, has no remaining hypothesis.
-/

@[expose] public section

namespace ComplexityTests.TensorNetworkTruncatedEntry

open Cslib Cslib.Circuits.Frontier Cslib.Circuits.Frontier.EntryContraction
  Cslib.Complexity.CountingSimulation
open Turing.MultiTapeTM (encList encNat)

/-- Two parallel edges between a row vertex with table `1, 2, 3, 4` and a column vertex of
ones. -/
abbrev twoEdges : DescribedNetwork (List ℕ) := ⟨2, [([0, 1], [1, 2, 3, 4]), ([0, 1], [1, 1, 1, 1])]⟩

/-- `⌈2 ^ (9/10)⌉ = 2`. -/
theorem ceilNineTenths_two : ceilNineTenths 2 = 2 :=
  le_antisymm (ceilNineTenths_le (by norm_num)) ((le_ceilNineTenths_iff (by norm_num)).2
    (by norm_num))

/-- The network is admissible at size `2` with the entry procedure of tables, for some constant. -/
theorem exists_entryAdmissible_twoEdges :
    ∃ C, 1 ≤ C ∧ EntryAdmissible tableEntryCertificate C 2 (1, twoEdges) := by
  obtain ⟨C₀, hC₀⟩ := exists_entryAdmissible_of_isPolynomial
    tableEntryCertificate_isPolynomial
  refine ⟨C₀ + 1, by omega, hC₀ (C₀ + 1) 2 1 twoEdges (by omega) (by decide) le_rfl (by simp) ?_⟩
  intro v hv
  rw [ceilNineTenths_two]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl <;> rfl

/-! ### Admissibility is not vacuous -/

-- With its two vertices, the network is admissible for Theorem D.1 at truncation order `ℓ`.
example : ∃ C, TruncEntryAdmissible tableEntryCertificate C 2 (1, twoEdges) := by
  obtain ⟨C, hC1, hC⟩ := exists_entryAdmissible_twoEdges
  exact ⟨C, hC, by simp only [List.length_cons, List.length_nil]; omega⟩

/-! ### Specialization -/

-- Specializing at the point `U` of `A_3 = (ℤ / 8)[U] / (U ^ 2 + U + 1)` keeps the network
-- rows-first.
example : (DescribedNetwork.specNet 3 2 [1, 1] [0, 1] twoEdges).IsRowsFirstBipartite 1 := by
  decide

-- Specialization keeps the network admissible, for the specialized entries.
example : ∃ C', EntryAdmissible (specEntryCertificate tableEntry tableEntryCertificate) C' 2
    (1, DescribedNetwork.specNet 3 2 [1, 1] [0, 1] twoEdges) := by
  obtain ⟨C, -, hC⟩ := exists_entryAdmissible_twoEdges
  obtain ⟨C', hC'⟩ := exists_entryAdmissible_specNet tableEntryCertificate C
  exact ⟨C', hC' 2 3 2 1 [1, 1] [0, 1] twoEdges hC⟩

/-! ### The truncated contraction algorithm -/

/-- The truncated contraction algorithm for the entry procedure of tables, with no remaining
hypothesis. Its certificate computes the contraction in `B_{P,ℓ}` on every input, by its type. -/
noncomputable def tableTruncAlgorithm :
    TruncatedContractionAlgorithm (encList encNat) tableEntry
      (TruncEntryAdmissible tableEntryCertificate) :=
  truncEntryContractionAlgorithm tableEntryCertificate

-- Its bound holds for all constants.
example (C D : ℕ) : ∃ K : ℕ, ∀ (s P ℓ r : ℕ) (G : DescribedNetwork (List ℕ)), 2 ≤ s → 1 ≤ P →
    P ≤ D * s → 1 ≤ ℓ → ℓ ≤ D * s → TruncEntryAdmissible tableEntryCertificate C s (r, G) →
      tableTruncAlgorithm.certificate.time (P, ℓ, r, G) ≤
          K * ((encTrunc (encList encNat) (P, ℓ, r, G)).length + 1) ^ K *
            2 ^ (K * s / Nat.sqrt (Nat.log 2 s)) ∧
        tableTruncAlgorithm.certificate.space (P, ℓ, r, G) ≤
          K * ((encTrunc (encList encNat) (P, ℓ, r, G)).length + 1) ^ K :=
  tableTruncAlgorithm.bound C D

end ComplexityTests.TensorNetworkTruncatedEntry
