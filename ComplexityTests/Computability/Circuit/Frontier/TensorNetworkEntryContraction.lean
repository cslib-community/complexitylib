/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import Complexity.Computability.Circuit.Frontier.TensorNetwork.EntryContraction

/-!
# Tests for the contraction interface with entry procedures

`⌈s ^ (9/10)⌉` at a few sizes. Direct summation with the entry procedure of tables, on a network
of two parallel edges between a row vertex and a column vertex, computes `1 + 2 + 3 + 4 = 10`,
which is `2` in `A_3 = (ℤ / 8)[U] / (U ^ 2 + U + 1)`. That network is admissible at size `2` with
the entry procedure of tables, for some constant (`EntryAdmissible` is not vacuous). An instance of
`EntryContractionAlgorithm` whose bound applies to that input is
`ComplexityTests.TensorNetworkEntryAnalysis.tableAlgorithm` (`TensorNetworkEntryAnalysis.lean`).
-/

@[expose] public section

namespace ComplexityTests.TensorNetworkEntryContraction

open Cslib Cslib.Circuits.Frontier Cslib.Circuits.Frontier.EntryContraction

/-! ### The nine-tenths power -/

example : ceilNineTenths 1 = 1 :=
  le_antisymm (ceilNineTenths_le (by norm_num)) ((le_ceilNineTenths_iff le_rfl).2 (by norm_num))

example : ceilNineTenths 2 = 2 :=
  le_antisymm (ceilNineTenths_le (by norm_num)) ((le_ceilNineTenths_iff (by norm_num)).2
    (by norm_num))

-- `1024 ^ (9/10) = 512` exactly.
example : ceilNineTenths 1024 = 512 :=
  le_antisymm (ceilNineTenths_le (by norm_num)) ((le_ceilNineTenths_iff (by norm_num)).2
    (by norm_num))

-- `⌈s ^ (9/10)⌉` is at most the degree bound of the schedule.
example : ceilNineTenths 1024 ≤ ContractionSchedule.degreeBound 1024 :=
  ceilNineTenths_le_degreeBound 1024

/-! ### Direct summation -/

/-- Two parallel edges between a row vertex with table `1, 2, 3, 4` and a column vertex of
ones. -/
abbrev twoEdges : DescribedNetwork (List ℕ) := ⟨2, [([0, 1], [1, 2, 3, 4]), ([0, 1], [1, 1, 1, 1])]⟩

-- Its contraction is `10`, which is `2` modulo `8`, a constant coefficient list over
-- `(ℤ / 8)[U] / (U ^ 2 + U + 1)`.
example : DescribedNetwork.sumValue SumOps.galois tableEntry (3, [1, 1]) twoEdges = [2, 0] := by
  decide

example : ExplicitTensorNetwork.contraction (R := ℕ) twoEdges = 10 := by decide

-- Direct summation is the contraction in `A_3`.
example : GaloisRingArith.val 3 [1, 1]
    (DescribedNetwork.sumValue SumOps.galois tableEntry (3, [1, 1]) twoEdges) =
      ((10 : ℕ) : GaloisRingArith.Ring 3 [1, 1]) := by
  rw [val_directCore_tableEntry]
  congr 1

/-! ### Admissibility is not vacuous -/

example : ∃ C, EntryAdmissible tableEntryCertificate C 2 (1, twoEdges) := by
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

end ComplexityTests.TensorNetworkEntryContraction
