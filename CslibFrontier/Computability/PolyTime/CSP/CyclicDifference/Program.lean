/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CSP.Table.CyclicDifference
public import CslibFrontier.Logics.Propositional.CSP.Table.ParityChain
public import CslibFrontier.Computability.Complexity.Problems.CSP.RotationSystem.Certificate
public import CslibFrontier.Computability.PolyTime.CSP.Table
public import CslibFrontier.Computability.PolyTime.CSP.Boolean

/-!
# Executable checked cyclic-difference compiler

The input is the original list CSP and a supplied ordered numerical rotation certificate.
Original variable names and certificate entries remain binary. Edge variables are dense actual
occurrence positions. Every enumeration is funded by actual constraint/scope/occurrence lists.
Static accepted-tuple and cyclic-difference tables depend only on the fixed language, with no
uniform language-preprocessing claim. In particular, no solver or recognizer is a parameter.

Black constraints use the ordered cyclic-difference tables. White scopes are the complete orbits
of `B⁻¹ A⁻¹`, enumerated by bounded scans in increasing edge-position order; their parity does
not depend on the starting point or direction. Long white scopes use a width-three parity chain.
Auxiliary blocks are consecutive and start immediately after the original occurrence positions.
Nullaries have no edge variables: true nullaries are omitted, and false nullaries are rejected
by the static relation-nonemptiness test. All malformed guards reject to two incompatible pins.

This is a numerical supplied-certificate implementation of the forward direction in
[DvorakKupec2015], Section 3, Lemma 5/Corollary 4/Theorem 2, printed pp. 439–440.
It asserts no geometric embedding construction, bare recognition, reverse reduction or solver.
The bounded scans, parity-chain expansion and binary encoding implementation are original.

## Main definitions

* `Cslib.Complexity.CSP.CyclicCompiler.compile`: total compiler on original raw typed inputs.
-/

public section

namespace Cslib.Complexity.CSP.CyclicCompiler

open Cslib.Logic.PL Cslib.Logic.PL.CSP Cslib.Logic.PL.CSP.Table
open Cslib.BitString Turing.MultiTapeTM
open Graph.RotationCertificate

variable {Rel : Type}

/-- The fixed accepted source truth table, including the exact declared arity. -/
@[expose] def sourceRows (arity : Rel → ℕ) (sem : Rel → List Bool → Bool)
    (r : Rel) : List (List Bool) := (enumList (arity r)).filter (sem r)

/-- Whether the canonical fixed relation has an accepted tuple. Empty symbols are rejected
only when they actually occur in the instance. -/
@[expose] def nonemptySymbol (arity : Rel → ℕ) (sem : Rel → List Bool → Bool)
    (r : Rel) : Bool := !(sourceRows arity sem r).isEmpty

/-- Constraint-side cyclic successor table, indexed by actual edge positions. -/
@[expose] def argumentTable (F : CSP Rel ℕ) : List ℕ :=
  F.occurrences.map fun (i, j, _) => argumentNextIndex F i j

/-- White face successor `B⁻¹ A⁻¹`: invert the supplied variable rotation by scanning its
actual list, then invert the actual cyclic argument successor list. Missing entries are total. -/
@[expose] def whiteTable (F : CSP Rel ℕ) (cert : Graph.RotationCertificate) : List ℕ :=
  (List.range F.occurrences.length).map fun edge =>
    (argumentTable F).idxOf (cert.successor.idxOf (2 * edge) / 2)

/-- Complete boundary of one candidate white orbit, in increasing edge-position order.
Repeated source vertices remain separate positions; parity is invariant under this enumeration. -/
@[expose] def whiteScope (F : CSP Rel ℕ) (cert : Graph.RotationCertificate)
    (edge : ℕ) : List ℕ :=
  (List.range F.occurrences.length).filter fun j =>
    orbitBool F.occurrences.length (whiteTable F cert) edge j

/-- Keep exactly the least position of each white orbit, including singleton orbits. -/
@[expose] def whiteScopes (F : CSP Rel ℕ) (cert : Graph.RotationCertificate) : List (List ℕ) :=
  ((List.range F.occurrences.length).filter fun edge =>
    faceRepBool F.occurrences.length (whiteTable F cert) edge).map (whiteScope F cert)

/-- Original cyclic scope order, with every argument replaced by its dense edge position. -/
@[expose] def blackScope (F : CSP Rel ℕ) (index : ℕ) (scope : List ℕ) : List ℕ :=
  (List.range scope.length).map fun j => (argumentPositions F).idxOf (index, j)

/-- One static difference table per positive actual constraint position. True nullaries are
handled by the outer nonemptiness guard and contribute no black dart orbit. -/
@[expose] def blackConstraints (arity : Rel → ℕ) (sem : Rel → List Bool → Bool)
    (F : CSP Rel ℕ) : CSP Table ℕ :=
  (F.zipIdx.filter fun ((_, scope), _) => !scope.isEmpty).map fun ((rel, scope), index) =>
    (differenceTable arity sem rel, blackScope F index scope)

/-- Fresh block prefix length. Only actual white boundary lists fund the allocated names. -/
@[expose] def auxiliaryPrefix (scopes : List (List ℕ)) (index : ℕ) : ℕ :=
  ((scopes.take index).map fun scope => scope.length - 3).sum

/-- Each white face gets exactly its own consecutive auxiliary block. -/
@[expose] def whiteConstraints (edges : ℕ) (scopes : List (List ℕ)) : CSP Table ℕ :=
  scopes.zipIdx.flatMap fun entry =>
    parityChain (edges + auxiliaryPrefix scopes entry.2) entry.1

/-- Output body after the input guards. No interpretation of a quotient or choice is executed. -/
@[expose] def body (arity : Rel → ℕ) (sem : Rel → List Bool → Bool)
    (F : CSP Rel ℕ) (cert : Graph.RotationCertificate) : CSP Table ℕ :=
  blackConstraints arity sem F ++ whiteConstraints F.occurrences.length (whiteScopes F cert)

/-- Actual total compiler. Bad arity, invalid rotations and occurring empty relations reject
honestly to an unsatisfiable edge instance whose two relations are even delta-matroids. -/
@[expose] def compile (arity : Rel → ℕ) (sem : Rel → List Bool → Bool)
    (input : CSP Rel ℕ × Graph.RotationCertificate) : CSP Table ℕ :=
  if validArity arity input.1 && verifyRotationCertificate input.1 input.2 &&
      input.1.all (fun c => nonemptySymbol arity sem c.1) then
    body arity sem input.1 input.2
  else rejectEdge

/-- The static nonemptiness test is exactly nonemptiness of the canonical relation. -/
theorem nonemptySymbol_eq_true_iff (arity : Rel → ℕ)
    (sem : Rel → List Bool → Bool) (r : Rel) :
    nonemptySymbol arity sem r = true ↔ (booleanRelation arity sem r).Nonempty := by
  constructor
  · intro h
    have hn : sourceRows arity sem r ≠ [] := by
      intro he
      simp only [nonemptySymbol, he, List.isEmpty_nil, Bool.not_true,
        Bool.false_eq_true] at h
    obtain ⟨word, hword⟩ := List.exists_mem_of_ne_nil _ hn
    obtain ⟨hw, hs⟩ := List.mem_filter.mp hword
    obtain ⟨x, _, rfl⟩ := List.mem_map.mp hw
    exact ⟨x, hs⟩
  · rintro ⟨x, hx⟩
    have hm : List.ofFn x ∈ sourceRows arity sem r :=
      List.mem_filter.mpr ⟨mem_enumList.mpr List.length_ofFn, hx⟩
    cases he : sourceRows arity sem r with
    | nil => simp only [he, List.not_mem_nil] at hm
    | cons row rows => simp only [nonemptySymbol, he, List.isEmpty_cons, Bool.not_false]

/-- Every listed white boundary is distinct and bounded by the actual occurrence count,
including for malformed certificates. -/
theorem whiteScope_bounds (F : CSP Rel ℕ) (cert : Graph.RotationCertificate) (edge : ℕ) :
    (whiteScope F cert edge).Nodup ∧
      (whiteScope F cert edge).length ≤ F.occurrences.length ∧
      ∀ j ∈ whiteScope F cert edge, j < F.occurrences.length := by
  refine ⟨List.nodup_range.filter _, ?_, ?_⟩
  · simpa only [whiteScope, List.length_range] using
      List.length_filter_le (fun j => orbitBool F.occurrences.length (whiteTable F cert) edge j)
        (List.range F.occurrences.length)
  · intro j hj
    exact List.mem_range.mp (List.mem_filter.mp hj).1

/-- No raw boundary scan emits more candidate white faces than original edges. -/
theorem length_whiteScopes_le (F : CSP Rel ℕ) (cert : Graph.RotationCertificate) :
    (whiteScopes F cert).length ≤ F.occurrences.length := by
  simpa only [whiteScopes, List.length_map, List.length_range] using
    List.length_filter_le
      (fun edge => faceRepBool F.occurrences.length (whiteTable F cert) edge)
      (List.range F.occurrences.length)

end Cslib.Complexity.CSP.CyclicCompiler
