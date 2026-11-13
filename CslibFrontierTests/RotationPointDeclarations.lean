/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

-- upstream: candidate

import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.PointDeclarations
import CslibFrontier.Computability.Complexity.Problems.CSP.RotationSystem.Nullary
import CslibFrontier.Computability.Complexity.Problems.CSP.RotationSystem.Symbols

/-! Raw-certificate transport through actual point, nullary and symbol changes. -/

namespace CslibFrontierTests.RotationPointDeclarations

open Cslib.Complexity Graph Graph.RotationCertificate
open Cslib.Logic.PL

private abbrev edges : List (ℕ × ℕ) := [(7, 8), (99, 99)]
private abbrev vertices : List ℕ := [7, 8, 99]
private abbrev morePoints : List ℕ := [1000, 99, 8, 7, 7, 2 ^ 250]

-- Two nontrivial components (one a loop) persist while declared points and duplicates vary.
private theorem raw_point_transport (c : RotationCertificate) :
    verifyGenusZero ⟨morePoints, edges⟩ c = verifyGenusZero ⟨vertices, edges⟩ c :=
  verifyGenusZero_redeclare vertices morePoints edges (by decide +kernel) (by decide +kernel) c

example : verifyGenusZero ⟨vertices, edges⟩ ⟨[0, 1, 3, 2]⟩ = true ∧
    verifyGenusZero ⟨morePoints, edges⟩ ⟨[0, 1, 3, 2]⟩ = true := by decide +kernel

example : verifyGenusZero ⟨morePoints, edges⟩ ⟨[0, 1, 3, 2]⟩ = true := by
  rw [raw_point_transport]
  decide +kernel

example : verifyGenusZero ⟨morePoints, edges⟩ ⟨[2 ^ 250]⟩ =
    verifyGenusZero ⟨vertices, edges⟩ ⟨[2 ^ 250]⟩ := raw_point_transport _

-- The endpoint guards matter: omitting an incident endpoint changes raw acceptance.
example : verifyGenusZero ⟨[7], [(7, 8)]⟩ ⟨[0, 1]⟩ = false ∧
    verifyGenusZero ⟨[7, 8], [(7, 8)]⟩ ⟨[0, 1]⟩ = true := by decide +kernel

-- Adding points cannot repair positive genus: actual rotation validation still passes.
example : verifyRotation ⟨[0, 8, 8], [(0, 0), (0, 0)]⟩ ⟨[2, 3, 1, 0]⟩ = true ∧
    verifyGenusZero ⟨[0, 8, 8], [(0, 0), (0, 0)]⟩ ⟨[2, 3, 1, 0]⟩ = false := by decide +kernel

example : verifyGenusZero ⟨[0, 8, 8], [(0, 0), (0, 0)]⟩ ⟨[2, 3, 1, 0]⟩ =
    verifyGenusZero ⟨[0], [(0, 0), (0, 0)]⟩ ⟨[2, 3, 1, 0]⟩ :=
  verifyGenusZero_redeclare [0] [0, 8, 8] [(0, 0), (0, 0)] (by decide) (by decide) _

example : verifyGenusZero ⟨[5, 5, 2 ^ 250], []⟩ ⟨[]⟩ = true ∧
    verifyGenusZero ⟨[], []⟩ ⟨[]⟩ = true := by decide +kernel

private abbrev body : CSP Bool ℕ := [⟨true, [7, 7]⟩, ⟨false, []⟩]

example :
    CSP.verifyRotationCertificate (body ++ [Constraint.mk false []]) ⟨[2, 3, 0, 1]⟩ = true := by
  rw [CSP.verifyRotationCertificate_append_nullary]
  decide +kernel

-- The relation tags may collapse. Constraint occurrences, including duplicates, do not.
private abbrev reversed : CSP Bool ℕ := [⟨true, [7, 9, 11]⟩, ⟨false, [7, 11, 9]⟩]
private abbrev sameOrder : CSP Bool ℕ := [⟨true, [7, 9, 11]⟩, ⟨false, [7, 9, 11]⟩]

example : CSP.verifyRotationCertificate (reversed.map fun c => ⟨(), c.scope⟩)
    ⟨[6, 3, 10, 5, 8, 1, 0, 9, 4, 11, 2, 7]⟩ = true := by
  rw [CSP.verifyRotationCertificate_mapRelation reversed (fun _ => ())]
  decide +kernel

example : CSP.verifyRotationCertificate (sameOrder.map fun c => ⟨(), c.scope⟩)
    ⟨[6, 3, 8, 5, 10, 1, 0, 9, 2, 11, 4, 7]⟩ = false := by
  rw [CSP.verifyRotationCertificate_mapRelation sameOrder (fun _ => ())]
  decide +kernel

end CslibFrontierTests.RotationPointDeclarations
