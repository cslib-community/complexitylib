/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

-- upstream: candidate

import Complexity.Computability.Complexity.Problems.CSP.RotationSystem.Certificate

/-! # Original cyclic CSP argument-order regression cases -/

open Cslib.Logic.PL Cslib.Complexity Cslib.Complexity.CSP

namespace CSPRotationCertificateTests

private def ternary : CSP Unit ℕ := [((), [0, 1, 2])]

example : verifyRotationCertificate ternary ⟨[0, 3, 2, 5, 4, 1]⟩ = true := by decide
-- The mirror still has numerical genus zero but reverses the original ternary order.
example : Graph.RotationCertificate.verifyGenusZero (incidenceGraph ternary)
    ⟨[0, 5, 2, 1, 4, 3]⟩ = true := by decide
example : verifyArgumentOrder ternary ⟨[0, 5, 2, 1, 4, 3]⟩ = false := by decide
example : verifyRotationCertificate ternary ⟨[0, 5, 2, 1, 4, 3]⟩ = false := by decide

-- The three arguments of one variable remain three parallel incidence edges.
example : verifyRotationCertificate ([((), [7, 7, 7])] : CSP Unit ℕ)
    ⟨[4, 3, 0, 5, 2, 1]⟩ = true := by decide
example : argumentPositions ([((), [7, 7, 7])] : CSP Unit ℕ) =
    [(0, 0), (0, 1), (0, 2)] := by decide

-- Identical constraint records remain distinct constraint vertices.
example : verifyRotationCertificate ([((), [7]), ((), [7])] : CSP Unit ℕ)
    ⟨[2, 1, 0, 3]⟩ = true := by decide

-- Nullaries have no ports; the order verifier does not test satisfiability.
example : verifyRotationCertificate ([((), [])] : CSP Unit ℕ) ⟨[]⟩ = true := by decide
example : verifyRotationCertificate ([(false, [])] : CSP Bool ℕ) ⟨[]⟩ = true := by decide
example : verifyArgumentOrder ([((), []), ((), [2 ^ 100])] : CSP Unit ℕ)
    ⟨[0, 1]⟩ = true := by decide
example : verifyRotationCertificate ([((), []), ((), [2 ^ 100])] : CSP Unit ℕ)
    ⟨[0, 1]⟩ = true := by decide

-- Malformed successor tables are rejected before any mathematical decoder is available.
example : verifyRotationCertificate ternary ⟨[0, 3, 2, 5, 4]⟩ = false := by decide
example : verifyRotationCertificate ternary ⟨[0, 3, 2, 5, 4, 2 ^ 100]⟩ = false := by decide

end CSPRotationCertificateTests
