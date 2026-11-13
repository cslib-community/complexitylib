/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

-- upstream: local-only (tests of the finite recognition compiler)

import CslibFrontier.Computability.PolyTime.Graph.RotationSystem.Recognition.Recovery

/-! Small kernel-checked examples of frozen queries, successful candidate recovery and malformed
inputs, alongside ordinary theorem clients. These examples do not establish the separate
algebraic/topological criterion or test generated code. -/

open Cslib.Complexity Cslib.Complexity.Graph Cslib.Complexity.Graph.RotationRecognition
open Cslib.Logic.PL

private def body (scopes : List (List ℕ)) : CSP Bool ℕ := scopes.map fun scope => ⟨true, scope⟩

-- The named components preserve the literal compiler used by the native certificates.
example (I : FixedRotationInput) : subdivide I =
    I.graph.edges.zipIdx.flatMap (fun entry =>
      let a := I.graph.vertices.length + 2 * entry.2
      let b := a + 1
      [((entry.1.1, a), (I.orders.getD entry.1.1 none).isSome),
        ((a, b), false), ((b, entry.1.2), (I.orders.getD entry.1.2 none).isSome)]) := rfl

example (F : Frame) (e f : Segment × ℕ) : row F e f =
    ⟨moveLabels F.vertexCount e.2 e.1 f.1.1 ++
      moveLabels F.vertexCount f.2 f.1 e.1.1, crossing F.order e.1.1 f.1.1⟩ := rfl

example (I : FixedRotationInput) (v : ℕ) (block : List ℕ) : split I v block =
    ⟨⟨List.range (I.graph.vertices.length + 1),
        I.graph.edges.zipIdx.map (fun e =>
          (redirectEnd I.graph.vertices.length block (2 * e.2) e.1.1,
           redirectEnd I.graph.vertices.length block (2 * e.2 + 1) e.1.2)) ++
          [(I.graph.vertices.length, v)]⟩,
      I.orders ++ [some (block ++ [2 * I.graph.edges.length])]⟩ := rfl

example : query (ofCSP (body [])) = true := by decide +kernel
example : query (ofCSP (body [[]])) = true := by decide +kernel
example : recoverCSP (body []) = some ⟨[]⟩ := by decide +kernel
example : recoverCSP (body [[]]) = some ⟨[]⟩ := by decide +kernel
-- Nonempty success witnesses rule out an always-failing candidate search.
example : (recoverCSP (body [[0, 0, 0]])).isSome = true := by decide +kernel
example : (recoverCSP (body [[0], [0], [0]])).isSome = true := by decide +kernel
example : (recoverCSP (body [[], []])).isSome = true := by decide +kernel

private def allFree : FixedRotationInput := ⟨⟨[0, 1], [(0, 0), (0, 1), (0, 1)]⟩, [none, none]⟩

example : validate allFree = true := by decide +kernel
example : (subdivide allFree).length = 9 := by decide +kernel
example : (recover allFree).isSome = true := by decide +kernel
example : !(validate ⟨⟨[1], []⟩, [none]⟩) = true := by decide +kernel
example : !(validate ⟨⟨[0], [(0, 1)]⟩, [none]⟩) = true := by decide +kernel
example : !(validate ⟨⟨[0], []⟩, []⟩) = true := by decide +kernel
example : !(validate ⟨⟨[0], []⟩, [some [0]]⟩) = true := by decide +kernel
example : !(validate ⟨⟨[0], [(0, 0)]⟩, [some [0]]⟩) = true := by decide +kernel
example : !(validate ⟨⟨[0], [(0, 0)]⟩, [some [0, 0]]⟩) = true := by decide +kernel
example : !(validate ⟨⟨[0], [(0, 0)]⟩, [some [0, 2 ^ 250]]⟩) = true := by decide +kernel
example : validate ⟨⟨[0], []⟩, [some []]⟩ = true := by decide +kernel
example : validate ⟨⟨[0], [(0, 0)]⟩, [some [0, 1]]⟩ = true := by decide +kernel
example : query ⟨⟨[0], [(0, 0)]⟩, [some [0, 1]]⟩ = true := by decide +kernel
example : !query ⟨⟨[0], [(0, 0), (0, 0)]⟩, [some [0, 2, 1, 3]]⟩ = true := by decide +kernel
example : query ⟨⟨[0], [(0, 0), (0, 0)]⟩, [some [0, 1, 2, 3]]⟩ = true := by decide +kernel
example : validate (split allFree 0 [0]) = true := by decide +kernel
example : (split allFree 0 [0]).graph.edges = [(2, 0), (0, 1), (0, 1), (2, 0)] := by decide +kernel

/-- Every successful output uses the existing CSP verifier, independently of any criterion. -/
example {F : CSP Bool ℕ} {c : RotationCertificate} (h : recoverCSP F = some c) :
    CSP.verifyRotationCertificate F c = true := recoverCSP_sound h

example : ofCSP ([⟨true, [0]⟩, ⟨true, []⟩, ⟨true, [0]⟩] : CSP Bool ℕ) =
  ofCSP ([⟨false, [0]⟩, ⟨false, []⟩, ⟨false, [0]⟩] : CSP Bool ℕ) := by decide +kernel

-- Huge unused relation metadata changes neither dense scopes nor fixed/free words.
example : ofCSP ([⟨2 ^ 250, [0, 0]⟩, ⟨0, []⟩] : CSP ℕ ℕ) =
    ofCSP ([⟨0, [0, 0]⟩, ⟨0, []⟩] : CSP ℕ ℕ) := by decide +kernel

-- The native program is uniform on arbitrary raw binary names and relation metadata.
example : Turing.MultiTapeTM.ComputableInPolyTime (recoverCSP (Rel := ℕ) (V := ℕ))
    (encCSP Turing.MultiTapeTM.encNat Turing.MultiTapeTM.encNat)
    (Turing.MultiTapeTM.encOption encRotationCertificate) :=
  recoverCSP_polyTime Turing.MultiTapeTM.encNat Turing.MultiTapeTM.encNat
