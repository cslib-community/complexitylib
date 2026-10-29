/-
Copyright (c) 2026 Erik Demaine, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.SAT.ExactOne.GeometryProfiles
public import Complexity.Computability.Complexity.Problems.SAT.ExactOne.GeometryProfilesPrefixData

/-!
# Certified source-boundary prefixes for positive exact-one profiles

The actual fifteen positive replacement profiles have their source incidences extended to the
cell boundary. The resulting finite certificates include all full real route contacts, simplicity,
nonincident vertices and the isolation of the cell boundary.

## Main definitions

* `profilePrefixGeometry`: the actual profile with source endpoints at boundary ports.

## Main results

* `profilePrefixGeometry_check`: full continuous certificates for all fifteen boundary profiles.
* `profilePrefixGeometry_signature`: exact alignment with the positive formula compiler.

## References

These are original geometric certificates for the cited exact-one clause constructions.
-/

@[expose] public section

namespace Cslib.Complexity.SAT.ExactOne

open Orthogonal

-- Each closed certificate checks all consecutive-segment pairs in a table of at most
-- sixty-six incidences. Separate declarations permit independent asynchronous elaboration.
private theorem profile0_prefix_check :
    LocalGeometry.PrefixCheck (profilePrefixGeometry (0 : ClauseProfile)) := by
  decide +kernel

private theorem profile1_prefix_check :
    LocalGeometry.PrefixCheck (profilePrefixGeometry (1 : ClauseProfile)) := by
  decide +kernel

private theorem profile2_prefix_check :
    LocalGeometry.PrefixCheck (profilePrefixGeometry (2 : ClauseProfile)) := by
  decide +kernel

private theorem profile3_prefix_check :
    LocalGeometry.PrefixCheck (profilePrefixGeometry (3 : ClauseProfile)) := by
  decide +kernel

private theorem profile4_prefix_check :
    LocalGeometry.PrefixCheck (profilePrefixGeometry (4 : ClauseProfile)) := by
  decide +kernel

private theorem profile5_prefix_check :
    LocalGeometry.PrefixCheck (profilePrefixGeometry (5 : ClauseProfile)) := by
  decide +kernel

private theorem profile6_prefix_check :
    LocalGeometry.PrefixCheck (profilePrefixGeometry (6 : ClauseProfile)) := by
  decide +kernel

private theorem profile7_prefix_check :
    LocalGeometry.PrefixCheck (profilePrefixGeometry (7 : ClauseProfile)) := by
  decide +kernel

private theorem profile8_prefix_check :
    LocalGeometry.PrefixCheck (profilePrefixGeometry (8 : ClauseProfile)) := by
  decide +kernel

private theorem profile9_prefix_check :
    LocalGeometry.PrefixCheck (profilePrefixGeometry (9 : ClauseProfile)) := by
  decide +kernel

private theorem profile10_prefix_check :
    LocalGeometry.PrefixCheck (profilePrefixGeometry (10 : ClauseProfile)) := by
  decide +kernel

private theorem profile11_prefix_check :
    LocalGeometry.PrefixCheck (profilePrefixGeometry (11 : ClauseProfile)) := by
  decide +kernel

private theorem profile12_prefix_check :
    LocalGeometry.PrefixCheck (profilePrefixGeometry (12 : ClauseProfile)) := by
  decide +kernel

private theorem profile13_prefix_check :
    LocalGeometry.PrefixCheck (profilePrefixGeometry (13 : ClauseProfile)) := by
  decide +kernel

private theorem profile14_prefix_check :
    LocalGeometry.PrefixCheck (profilePrefixGeometry (14 : ClauseProfile)) := by
  decide +kernel

/-- All fifteen source-boundary prefix drawings have full continuous certificates. -/
theorem profilePrefixGeometry_check (p : ClauseProfile) :
    LocalGeometry.PrefixCheck (profilePrefixGeometry p) := by
  fin_cases p
  · exact profile0_prefix_check
  · exact profile1_prefix_check
  · exact profile2_prefix_check
  · exact profile3_prefix_check
  · exact profile4_prefix_check
  · exact profile5_prefix_check
  · exact profile6_prefix_check
  · exact profile7_prefix_check
  · exact profile8_prefix_check
  · exact profile9_prefix_check
  · exact profile10_prefix_check
  · exact profile11_prefix_check
  · exact profile12_prefix_check
  · exact profile13_prefix_check
  · exact profile14_prefix_check

/-- Extending source incidences preserves the exact logical incidence signature. -/
theorem profilePrefixGeometry_signature (p : ClauseProfile) :
    ((profilePrefixGeometry p).incidenceRoutes.map fun e => (e.1, e.2.1)) =
      profileSignature p := by
  rw [← profileGeometry_signature]
  simp [profilePrefixGeometry, LocalGeometry.toPrefix, List.map_map, Function.comp_def]

/-- Each exposed source position is exactly its assigned boundary port after extension. -/
theorem profilePrefixGeometry_terminal_position (p : ClauseProfile) :
    ∀ i : Fin (profileSource p).length,
      (profilePrefixGeometry p).variablePosition
        ((profileGeometry p).terminalVariables.getD i 0) =
          (profileGeometry p).boundaryPorts.getD i (0, 0) := by
  fin_cases p <;> decide +kernel

/-- All auxiliary variables remain strictly inside the profile cell. -/
theorem profilePrefixGeometry_auxiliary_interior (p : ClauseProfile) :
    ∀ i : Fin (profilePrefixGeometry p).variablePositions.length,
      i.val ∉ (profilePrefixGeometry p).terminalVariables →
        let q := (profilePrefixGeometry p).variablePosition i
        0 < q.1 ∧ q.1 < 180000 ∧ 0 < q.2 ∧ q.2 < 180000 := by
  fin_cases p <;> decide +kernel

/-- All actual clause vertices remain strictly inside the profile cell. -/
theorem profilePrefixGeometry_clause_interior (p : ClauseProfile) :
    ∀ q ∈ (profilePrefixGeometry p).clausePositions,
      0 < q.1 ∧ q.1 < 180000 ∧ 0 < q.2 ∧ q.2 < 180000 := by
  fin_cases p <;> decide +kernel

/-- Source-boundary extension preserves the single incidence at every source placeholder. -/
theorem profilePrefixGeometry_terminal_degree (p : ClauseProfile) :
    ∀ v ∈ (profilePrefixGeometry p).terminalVariables,
      ((profilePrefixGeometry p).incidenceRoutes.map fun e => e.2.1).count v = 1 := by
  simpa [profilePrefixGeometry, LocalGeometry.toPrefix, List.map_map, Function.comp_def] using
    profileGeometry_terminal_degree p

/-- The actual finite prefix tables have constant vertex, route, segment and wire costs. -/
theorem profilePrefixGeometry_costs (p : ClauseProfile) :
    (profilePrefixGeometry p).variablePositions.length ≤ 29 ∧
      (profilePrefixGeometry p).clausePositions.length ≤ 22 ∧
      (profilePrefixGeometry p).incidenceRoutes.length ≤ 66 ∧
      (((profilePrefixGeometry p).incidenceRoutes.map fun e => e.2.2.length - 1).sum ≤ 113) ∧
      (((profilePrefixGeometry p).incidenceRoutes.map fun e => wireLength e.2.2).sum ≤
        652600) ∧ (profilePrefixGeometry p).size = 180000 := by
  fin_cases p <;> decide +kernel

end Cslib.Complexity.SAT.ExactOne
