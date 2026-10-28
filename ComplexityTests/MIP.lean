/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Classes.IP.GraphNonIsomorphism
import Complexity.Computability.Complexity.Classes.IP.Shamir
import Complexity.Computability.Complexity.Classes.MIP

/-! Multiprover interactive proofs (`MIP₂` and `MIP`), non-communicating provers, deterministic
prover optimality, transcript consistency, and the upper bound `MIP ⊆ NEXP`. -/

namespace ComplexityTests.MIP

open Cslib Cslib.Complexity Cslib.Probability Turing.MultiTapeTM

/-! ### Non-communicating provers and transcript consistency -/

-- Querying channel `0` leaves channel `1`'s state untouched.
example (P : Fin 2 → Prover Unit) (word : List Bool) (s s' : ∀ i : Fin 2, (P i).State)
    (reply : List Bool)
    (hout : (reply, s') ∈ (((Prover.independent P).respond ((0 : Fin 2), word)).run s).support) :
    s' 1 = s 1 :=
  Prover.independent_state_eq_of_ne P ((0 : Fin 2), word) s s' reply (by decide : (1 : Fin 2) ≠ 0)
    hout

-- `projHistory` filters and extracts the `(query, reply)` pairs of a single prover channel, and
-- `consistentHist` checks whether two histories give identical replies on their common queries.
example :
    MIP.projHistory 0
      [(0, ([true], [false])), (1, ([false], [true])), (0, ([true, false], [true]))] =
      [([true], [false]), ([true, false], [true])] ∧
    MIP.projHistory 1
      [(0, ([true], [false])), (1, ([false], [true])), (0, ([true, false], [true]))] =
      [([false], [true])] ∧
    MIP.consistentHist
      [([true], [false]), ([false], [true])]
      [([true], [false]), ([true], [false])] = true ∧
    MIP.consistentHist
      [([true], [false])]
      [([true], [true])] = false :=
  ⟨rfl, rfl, rfl, rfl⟩

/-! ### Non-vacuity: concrete `IsMultiproverProof` instance -/

-- Every single-prover interactive proof embeds into a two-prover interactive proof via channel 0,
-- giving `GraphNonIsomorphism` completeness `1`, soundness `(17 / 32) ^ 2`, and membership in
-- `MIP₂`, `MIP`, and `NEXP` alongside `TQBF`.
example (x : Graph × Graph) :
    (x ∈ GraphNonIsomorphism →
      ∃ P : Fin 2 → Prover Unit,
        1 ≤ acceptProb
          (WordOracleComp.singleOracle (0 : Fin 2) (GraphNonIsomorphism.verifier x))
          (Prover.independent P)) ∧
    (x ∉ GraphNonIsomorphism →
      ∀ P : Fin 2 → Prover Unit,
        acceptProb
          (WordOracleComp.singleOracle (0 : Fin 2) (GraphNonIsomorphism.verifier x))
          (Prover.independent P) ≤ (17 / 32) ^ 2) :=
  ⟨(GraphNonIsomorphism.isInteractiveProof_verifier.isMultiproverProof_singleOracle
      (0 : Fin 2)).complete x,
    (GraphNonIsomorphism.isInteractiveProof_verifier.isMultiproverProof_singleOracle
      (0 : Fin 2)).sound x⟩

example :
    GraphNonIsomorphism ∈ MIP₂ (encPair encGraph encGraph) ∧
    GraphNonIsomorphism ∈ MIP (encPair encGraph encGraph) ∧
    GraphNonIsomorphism ∈ NEXP (encPair encGraph encGraph) ∧
    TQBF ∈ MIP₂ encQBF ∧
    TQBF ∈ NEXP encQBF :=
  ⟨IP_subset_MIP₂ _ GraphNonIsomorphism.mem_IP,
    MIP₂_subset_MIP _ (IP_subset_MIP₂ _ GraphNonIsomorphism.mem_IP),
    MIP₂_subset_NEXP _ (IP_subset_MIP₂ _ GraphNonIsomorphism.mem_IP),
    IP_subset_MIP₂ _ (PSPACE_subset_IP _ TQBF_pspaceComplete.1),
    MIP₂_subset_NEXP _ (IP_subset_MIP₂ _ (PSPACE_subset_IP _ TQBF_pspaceComplete.1))⟩

end ComplexityTests.MIP
