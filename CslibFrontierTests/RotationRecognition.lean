/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

-- upstream: local-only (tests of the finite recognition compiler)

import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Recognition.Moves
import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Recognition.RecoveryInvariants
import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Recognition.RecoveryBudget
import CslibFrontier.Computability.PolyTime.Graph.RotationSystem.Recognition.Recovery

/-! Finite regression tests execute the actual sparse XOR solver and existing final checker.
They do not prove the still separate algebraic/topological criterion. -/

open Cslib.Complexity Cslib.Complexity.Graph Cslib.Complexity.Graph.RotationRecognition
open Cslib.Logic.PL

private def body (scopes : List (List ℕ)) : CSP Bool ℕ := scopes.map fun scope => (true, scope)

example : query (ofCSP (body [])) = true := by decide +kernel
example : query (ofCSP (body [[]])) = true := by decide +kernel
example : recoverCSP (body []) = some ⟨[]⟩ := by decide +kernel
example : recoverCSP (body [[]]) = some ⟨[]⟩ := by decide +kernel
example : !query (ofCSP (body [[0, 1, 2], [0, 1, 2]])) = true := by decide +kernel
example : query (ofCSP (body [[0, 1, 2], [0, 2, 1]])) = true := by decide +kernel
example : (recoverCSP (body [[0, 1, 2], [0, 2, 1]])).isSome = true := by decide +kernel
example : (recoverCSP (body [[0, 0, 0]])).isSome = true := by decide +kernel
example : (recoverCSP (body [[0], [0], [0]])).isSome = true := by decide +kernel
example : (recoverCSP (body
    [[2 ^ 250], [2 ^ 250], [2 ^ 250], [2 ^ 250], [2 ^ 250]])).isSome = true := by
  decide +kernel

private def allFree : FixedRotationInput := ⟨([0, 1], [(0, 0), (0, 1), (0, 1)]), [none, none]⟩

example : validate allFree = true := by decide +kernel
example : (subdivide allFree).length = 9 := by decide +kernel
example : (recover allFree).isSome = true := by decide +kernel
example : !(validate ⟨([1], []), [none]⟩) = true := by decide +kernel
example : !(validate ⟨([0], [(0, 1)]), [none]⟩) = true := by decide +kernel
example : !(validate ⟨([0], []), []⟩) = true := by decide +kernel
example : !(validate ⟨([0], []), [some [0]]⟩) = true := by decide +kernel
example : !(validate ⟨([0], [(0, 0)]), [some [0]]⟩) = true := by decide +kernel
example : !(validate ⟨([0], [(0, 0)]), [some [0, 0]]⟩) = true := by decide +kernel
example : !(validate ⟨([0], [(0, 0)]), [some [0, 2 ^ 250]]⟩) = true := by decide +kernel
example : validate ⟨([0], []), [some []]⟩ = true := by decide +kernel
example : validate ⟨([0], [(0, 0)]), [some [0, 1]]⟩ = true := by decide +kernel
example : query ⟨([0], [(0, 0)]), [some [0, 1]]⟩ = true := by decide +kernel
example : !query ⟨([0], [(0, 0), (0, 0)]), [some [0, 2, 1, 3]]⟩ = true := by decide +kernel
example : query ⟨([0], [(0, 0), (0, 0)]), [some [0, 1, 2, 3]]⟩ = true := by decide +kernel
example : validate (split allFree 0 [0]) = true := by decide +kernel
example : (split allFree 0 [0]).graph.2 = [(2, 0), (0, 1), (0, 1), (2, 0)] := by decide +kernel

/-- Every successful output uses the existing CSP verifier, independently of any criterion. -/
example {F : CSP Bool ℕ} {c : RotationCertificate} (h : recoverCSP F = some c) :
    CSP.verifyRotationCertificate F c = true := recoverCSP_sound h

example : ofCSP ([(true, [0]), (true, []), (true, [0])] : CSP Bool ℕ) =
  ofCSP ([(false, [0]), (false, []), (false, [0])] : CSP Bool ℕ) := by decide +kernel

private noncomputable def checkedCSP (F : CSP Bool ℕ) : Bool :=
  (recoverCSP F).elim false fun c => CSP.verifyRotationCertificate F c

example : checkedCSP (body [[0, 1, 2], [0, 2, 1]]) = true := by decide +kernel
example : checkedCSP (body [[0, 0, 0]]) = true := by decide +kernel
example : checkedCSP ([(false, []), (true, [])] : CSP Bool ℕ) = true := by decide +kernel

-- Huge unused relation metadata changes neither dense scopes nor fixed/free words.
example : ofCSP ([(2 ^ 250, [0, 0]), (0, [])] : CSP ℕ ℕ) =
    ofCSP ([(0, [0, 0]), (0, [])] : CSP ℕ ℕ) := by decide +kernel

-- The native program is uniform on arbitrary raw binary names and relation metadata.
example : Turing.MultiTapeTM.ComputableInPolyTime (recoverCSP (Rel := ℕ) (V := ℕ))
    (encCSP Turing.MultiTapeTM.encNat Turing.MultiTapeTM.encNat)
    (Turing.MultiTapeTM.encOption encRotationCertificate) :=
  recoverCSP_polyTime Turing.MultiTapeTM.encNat Turing.MultiTapeTM.encNat
