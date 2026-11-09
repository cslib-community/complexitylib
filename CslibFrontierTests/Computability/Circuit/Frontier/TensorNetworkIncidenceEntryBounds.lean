/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.IncidenceEntryBounds

/-! # Actual incidence-entry resource and contraction clients -/

public section

namespace CslibFrontierTests.TensorNetworkIncidenceEntryBounds

open Cslib.Complexity Cslib.Circuits.Frontier Cslib.Circuits.Frontier.IncidenceNetwork

/-- Two tests, with three test-variable incidences in the single group. -/
def sys : List (List (List ℕ)) := [[[0], [1]], [[2]]]

example : descInc (rowVertex 4 2 1 sys [2] 0).2 = 3 := by decide
example : descInc (colVertex 4 1 3 sys [2] 0).2 = 0 := by decide
example : descInc (padRow 7).2 = 0 := by decide
example : descInc deadRow.2 = 0 := by decide
example : descInc (rowVertex 4 2 1 [] [2] 0).2 = 0 := by decide
example : sizeParam 5 = 10 := by decide

example : ∀ v ∈ (network 4 2 1 3 2 3 sys [2]).2.vertices, descInc v.2 ≤ 6 :=
  descInc_le (P := 4) (ℓ := 2) (J := 1) (K := 3) (s := 2) (n := 3)
    (sys := sys) (d := [2]) (by decide) (S := 2) (by decide)

/-- The uniform admissibility contract has actual instances at every sufficiently large size;
empty systems give genuine padded bipartite networks, rather than an empty admissibility class. -/
example : ∃ C n₀ : ℕ, ∀ n, n₀ ≤ n →
    TruncEntryAdmissible incCertificate C (sizeParam n) (lemmaNetwork n n [] []) := by
  obtain ⟨C, n₀, hC⟩ := exists_entry_admissible 1
  refine ⟨C, n₀, fun n hn => hC n hn n [] [] (by simp) le_rfl (by simp)
    (by simp) (by simp) ?_⟩
  simp [varDegree]

/-- The same concrete family is handled by the native truncated algorithm at polynomial order. -/
example : ∃ A n₀ : ℕ, ∀ n, n₀ ≤ n →
    let inp := (n + 1, n + 1, lemmaNetwork (2 * n) n [] [])
    let L := (encTrunc encDesc inp).length
    (CountingSimulation.truncEntryContractionAlgorithm incCertificate).certificate.time inp ≤
        A * (L + 1) ^ A * 2 ^ (A * sizeParam n / Nat.sqrt (Nat.log 2 (sizeParam n))) ∧
      (CountingSimulation.truncEntryContractionAlgorithm incCertificate).certificate.space inp ≤
        A * (L + 1) ^ A := by
  obtain ⟨A, n₀, hA⟩ := exists_sparseBranch_contraction_bound 1 1 (by decide)
  refine ⟨A, n₀, fun n hn => ?_⟩
  have hs : SubexponentialSAT.IncidenceBranching.IsSparseBranch 1 1 n [] := {
    vars_lt := by simp
    canonical := by simp
    length_le := by simp
    monomials_le := by simp
    degree_le := by simp
    scope_le := by simp
    varDegree_le := by simp [varDegree] }
  simpa only [List.length_nil, zero_add, one_mul] using hA n hn [] [] hs

end CslibFrontierTests.TensorNetworkIncidenceEntryBounds
