/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Recognition.Parity
public import CslibFrontier.Computability.Complexity.Problems.CSP.RotationSystem.Certificate
import Mathlib.Data.List.GetD

/-!
# Bounded contiguous-block candidate recovery

Each candidate is tested by the concrete frozen XOR query. Selected dart ends are redirected to
one fresh hub, whose complete prescribed order is the block followed by a fresh connector end.
The connector need not be a graph-theoretic bridge. Earlier complete orders stay on the original
graph. Split query graphs are ephemeral: the loop stores only the current orders and block.

This finite self-reduction is original. Completeness requires the still separate full-query
criterion and a split/nonloop-contraction theorem for directed consecutive blocks. Neither is
assumed here. Every returned candidate is guarded by the existing numerical certificate checker;
the CSP entry additionally runs the existing original-argument-order checker.

## Main definitions

* `Cslib.Complexity.Graph.RotationRecognition.split`: ephemeral complete fixed/free query.
* `Cslib.Complexity.Graph.RotationRecognition.recover`: guarded existing graph certificate.
* `Cslib.Complexity.Graph.RotationRecognition.recoverCSP`: guarded original CSP certificate.
-/

public section

namespace Cslib.Complexity.Graph.RotationRecognition

open Turing.MultiTapeTM Cslib.Logic.PL

/-- Redirect one binary dart end exactly when it is selected in the block. -/
@[expose] def redirectEnd (hub : ℕ) (block : List ℕ) (dart old : ℕ) : ℕ :=
  if block.any (fun d => decide (d = dart)) then hub else old

/-- Redirect exactly the selected binary dart ends to a fresh hub `n`, retaining every old edge
position/end tag, then append connector `(n,v)`. The hub's complete word is `block ++ [2m]`.
For the intended split contract `v` is free and the nonempty duplicate-free block lies at `v`. -/
@[expose] def split (I : FixedRotationInput) (v : ℕ) (block : List ℕ) : FixedRotationInput :=
  ⟨(List.range (I.graph.1.length + 1),
      I.graph.2.zipIdx.map (fun e =>
        (redirectEnd I.graph.1.length block (2 * e.2) e.1.1,
         redirectEnd I.graph.1.length block (2 * e.2 + 1) e.1.2)) ++
        [(I.graph.1.length, v)]),
    I.orders ++ [some (block ++ [2 * I.graph.2.length])]⟩

/-- Darts still available as the next clockwise member of the current directed block. -/
@[expose] def remaining (I : FixedRotationInput) (v : ℕ) (block : List ℕ) : List ℕ :=
  (fiber I.graph v).filter fun d => !(block.any fun b => decide (b = d))

/-- First feasible append candidate, using the implemented native XOR query on each split. -/
@[expose] def nextCandidate (I : FixedRotationInput) (v : ℕ) (block : List ℕ) : Option ℕ :=
  (remaining I v block).find? fun d => query (split I v (block ++ [d]))

/-- One block extension. A completed block is retained; failed search remains `none`. -/
@[expose] def advance (I : FixedRotationInput) (v : ℕ)
    (state : Option (List ℕ)) : Option (List ℕ) :=
  state.elim none fun block =>
    if (remaining I v block).isEmpty then some block
    else (nextCandidate I v block).elim none fun d => some (block ++ [d])

/-- At most one extension per incident dart; an empty fiber is an empty complete word. -/
@[expose] def recoverWord (I : FixedRotationInput) (v : ℕ) : Option (List ℕ) :=
  let darts := fiber I.graph v
  (advance I v)^[darts.length - 1]
    (some (if darts.isEmpty then [] else [darts.headD 0]))

/-- Replace one order-table entry without growing the table. All other entries are retained. -/
@[expose] def prescribe (I : FixedRotationInput) (v : ℕ) (word : List ℕ) : FixedRotationInput :=
  ⟨I.graph, I.orders.zipIdx.map fun e => if e.2 = v then some word else e.1⟩

/-- Complete a free vertex; prior full orders are left intact. Failed candidate search is sticky. -/
@[expose] def completeVertex (state : Option FixedRotationInput) (v : ℕ) :
    Option FixedRotationInput :=
  state.elim none fun I =>
    if (I.orders.getD v none).isSome then some I
    else (recoverWord I v).elim none fun word => some (prescribe I v word)

/-- Recover original-graph full words, storing no query systems or earlier split graphs. -/
@[expose] def recoverOrders (I : FixedRotationInput) : Option FixedRotationInput :=
  (List.range I.graph.1.length).foldl completeVertex (some I)

/-- The binary successor table assembled from complete words on the original graph. -/
@[expose] def certificate (I : FixedRotationInput) : RotationCertificate :=
  ⟨(List.range (2 * I.graph.2.length)).map fun d =>
    let word := (I.orders.getD (I.graph.incidenceVertices.getD d 0) none).getD []
    nextInWord word (word.idxOf d)⟩

/-- Guard complete prescribed orders directly on a supplied successor table. -/
@[expose] def verifyFixed (I : FixedRotationInput) (c : RotationCertificate) : Bool :=
  I.orders.all fun order => order.elim true fun word =>
    word.zipIdx.all fun e => decide (c.successor.getD e.1 0 = nextInWord word e.2)

/-- Validate the input, test its actual XOR system, recover candidates, and guard the resulting
original-graph table with the existing numerical checker and the original complete orders. -/
@[expose] def recover (I : FixedRotationInput) : Option RotationCertificate :=
  if query I then
    (recoverOrders I).elim none fun J =>
      let c := certificate J
      if RotationCertificate.verifyGenusZero I.graph c && verifyFixed I c then some c else none
  else none

/-- Keep a prefix of dense vertices free and prescribe full fiber orders at the remaining vertices.
The raw binary cutoff is only compared, never used as a scan length. -/
@[expose] def freePrefix (G : Graph) (k : ℕ) : FixedRotationInput :=
  ⟨G, G.1.map fun v => if v < k then none else some (fiber G v)⟩

/-- Dense incidence input: variable vertices are free; each constraint position fixes its entire
actual occurrence word. Relation semantics and declared relation arities are never inspected. -/
@[expose] def ofCSP {Rel V : Type} [DecidableEq V] (F : CSP Rel V) : FixedRotationInput :=
  freePrefix (CSP.incidenceGraph F) F.numVars

/-- Bare CSP candidate recovery with the existing original CSP checker as its final guard. -/
@[expose] def recoverCSP {Rel V : Type} [DecidableEq V] (F : CSP Rel V) :
    Option RotationCertificate :=
  (recover (ofCSP F)).elim none fun c =>
    if CSP.verifyRotationCertificate F c then some c else none

/-- Split queries add exactly one vertex, regardless of binary names in malformed raw input. -/
@[simp] theorem length_split_vertices (I : FixedRotationInput) (v : ℕ) (block : List ℕ) :
    (split I v block).graph.1.length = I.graph.1.length + 1 := by simp [split]

/-- Split queries retain every listed edge and append exactly one connector. -/
@[simp] theorem length_split_edges (I : FixedRotationInput) (v : ℕ) (block : List ℕ) :
    (split I v block).graph.2.length = I.graph.2.length + 1 := by simp [split]

/-- A constructed table has exactly one successor per original binary dart index. -/
@[simp] theorem length_certificate (I : FixedRotationInput) :
    (certificate I).successor.length = 2 * I.graph.2.length := by simp [certificate]

/-- Every returned graph candidate passes the existing numerical checker unconditionally. -/
theorem recover_sound {I : FixedRotationInput} {c : RotationCertificate}
    (h : recover I = some c) :
    RotationCertificate.verifyGenusZero I.graph c = true ∧ verifyFixed I c = true := by
  unfold recover at h
  split at h
  · cases hx : recoverOrders I with
    | none => simp [hx] at h
    | some J =>
      simp only [hx, Option.elim_some] at h
      split at h
      · have hc : certificate J = c := Option.some.inj h
        subst c
        simpa only [Bool.and_eq_true] using (show
          (RotationCertificate.verifyGenusZero I.graph (certificate J) &&
            verifyFixed I (certificate J)) = true from by assumption)
      · contradiction
  · contradiction

/-- Every returned CSP candidate passes precisely the existing original CSP checker. -/
theorem recoverCSP_sound {Rel V : Type} [DecidableEq V] {F : CSP Rel V}
    {c : RotationCertificate} (h : recoverCSP F = some c) :
    CSP.verifyRotationCertificate F c = true := by
  unfold recoverCSP at h
  cases hx : recover (ofCSP F) with
  | none => simp [hx] at h
  | some d =>
    simp only [hx, Option.elim_some] at h
    split at h
    · have hc : d = c := Option.some.inj h
      subst c
      assumption
    · contradiction

end Cslib.Complexity.Graph.RotationRecognition
