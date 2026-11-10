/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (regression tests)

public import CslibFrontier.Computability.PolyTime.CNF.UpperDominationSharedQueries
meta import CslibFrontier.Computability.PolyTime.CNF.UpperDominationSharedQueries
meta import CslibFrontier.Computability.PolyTime.CNF.UpperDominationUnique
meta import CslibFrontier.Computability.PolyTime.CNF.UpperDomination

/-!
# Actual shared-marker clause writing and local parsimonious extension

Tiny tests vary the old port/selection bits and the single new marker. They do not enumerate
auxiliary gate cubes. Global graph-writer tests vary all relevant old K2 bits and the two fresh
markers; they do not stand in for a general finite-model count proof.
-/

public section

namespace SharedMarkerTests

open Cslib.Logic.PL Turing.MultiTapeTM
open UpperDomination.Unique.SharedMarkers

set_option linter.hashCommand false

/-- Actual first augmented predicate for K2, with ports/marker in the source path allocation. -/
@[expose] def edgeContext : Context :=
  let x : UpperDomination.Input := ((2, [[false, true], [true, false]]), 0)
  let a := UpperDomination.auxiliary x
  { left := a + 7, right := a + 8, marker := a + 9, last := false, boundary := false,
    terms := (UpperDomination.Unique.complete (UpperDomination.coreInput x)).getD 0 [] }

/-- Five relevant old bits; the rest of the original/query declaration is fixed only for testing. -/
@[expose] def oldBits (seed i : ℕ) : Bool :=
  let a := edgeContext.left - 7
  if i = 0 then Nat.testBit seed 0 else
  if i = 1 then Nat.testBit seed 1 else
  if i = a + 2 then Nat.testBit seed 2 else
  if i = edgeContext.left then Nat.testBit seed 3 else
  if i = edgeContext.right then Nat.testBit seed 4 else false

/-- Count only the two possible values of the one shared fresh marker. -/
@[expose] def extensions (c : Context) (σ : ℕ → Bool) : ℕ :=
  [false, true].countP fun b => (block c).eval (Function.update σ c.marker b)

/- One marker, independent of ordered duplicate pair terms; all written clauses have width <=3. -/
/-- info: (3, 7, true) -/
#guard_msgs in
#eval (edgeContext.terms.length, (block edgeContext).length,
  (block edgeContext).all fun cl => cl.length ≤ 3)

/- Every old assignment has exactly its intended zero or one extension, rather than two. -/
/-- info: true -/
#guard_msgs in
#eval (List.range 32).all fun seed =>
  let σ := oldBits seed
  extensions edgeContext σ ==
    if DNF.eval σ edgeContext.terms && (σ edgeContext.left != σ edgeContext.right) then 0 else 1

/- The final constant port ignores its dummy index, even if it equals the new marker. -/
/-- info: (1, 0, 3, true) -/
#guard_msgs in
#eval let c : Context :=
    { left := 0, right := 1, marker := 1, last := true, boundary := true,
      terms := [[(2, true)]] }
  (extensions c (fun i => i == 0 || i == 2),
    extensions c (fun i => i == 2), (block c).length,
    (block c).all fun cl => cl.length ≤ 3)

/- Empty terms activate equality unconditionally; empty predicates allow either port parity. -/
/-- info: (0, 1, 1) -/
#guard_msgs in
#eval let c : Context :=
    { left := 0, right := 1, marker := 2, last := false, boundary := false, terms := [[]] }
  (extensions c (fun i => i == 0), extensions { c with terms := [] } (fun i => i == 0),
    extensions c (fun _ => false))

/- Freshness matters: reusing the left port as the marker destroys unique extension. -/
/-- info: 2 -/
#guard_msgs in
#eval extensions
  { left := 0, right := 1, marker := 0, last := false, boundary := false, terms := [] }
  (fun _ => false)

example : ComputableInPolyTime block encContext VCOne.encSignedCNF := block_polytime

/-- Freshness is checked in the theorem, not replaced by an assumed functional output. -/
example (σ : ℕ → Bool) :
    (∃! b : Bool, (block
      { left := 0, right := 1, marker := 2, last := false, boundary := false,
        terms := [[(3, true)], [(4, true), (5, false)]] }).eval
          (Function.update σ 2 b) = true) ↔
      (DNF.eval σ [[(3, true)], [(4, true), (5, false)]] = true →
        (σ 0 ^^ σ 1) = false) := by
  apply extension_unique <;> simp; grind

/-- Original graph input; the suffix writer receives no precomputed clauses or gate counts. -/
@[expose] def graphInput : UpperDomination.Input := ((2, [[false, true], [true, false]]), 0)

/- The whole writer obeys both source variable and width bounds, not only the local block. -/
/-- info: (true, true, true) -/
#guard_msgs in
#eval let x := graphInput
  let n := IndependentDomination.order (UpperDomination.graph x)
  let N := oldDeclaration x + n
  (N == 6 * n + UpperDomination.auxiliary x - 1,
    (query x false).all fun c => c.length ≤ 3,
    (query x true).all fun c => c.all fun l => l.1 < N)

/-- The nine relevant old bits for K2: selections, marks, then five path variables. -/
@[expose] def graphBits (a N seed i : ℕ) : Bool :=
  if i < 2 then Nat.testBit seed i else
  if a + 2 ≤ i && i < a + 4 then Nat.testBit seed (i - (a + 2) + 2) else
  if a + 4 ≤ i && i < N then Nat.testBit seed (i - (a + 4) + 4)
  else false

/- Check global extension counts for both boundaries and every old selection/mark/path pattern.
Gate side clauses are omitted on both sides, so their falsity cannot make this test vacuous.
Only the two newly introduced marker bits are enumerated on the refined side. -/
/-- info: true -/
#guard_msgs in
#eval let x := graphInput
  let N := oldDeclaration x
  let a := UpperDomination.auxiliary x
  let sideLength := (TwoBoundary.BinaryFrontend.side (UpperDomination.build x)).length
  [false, true].all fun β =>
    let old : CNF ℕ :=
      (TwoBoundary.BinaryFrontend.query (UpperDomination.Unique.build x) β).drop sideLength
    let fresh : CNF ℕ := (query x β).drop sideLength
    (List.range 512).all fun seed =>
      let σ := graphBits a N seed
      let count := (List.range 4).countP fun mask => fresh.eval fun i =>
        if N ≤ i && i < N + 2 then
          Nat.testBit mask (i - N) else σ i
      count == if old.eval σ then 1 else 0

/- The single-vertex suffix substitutes the final boundary; the empty graph dispatch remains old. -/
/-- info: (true, true, true) -/
#guard_msgs in
#eval let one : UpperDomination.Input := ((1, [[false]]), 0)
  let zero : UpperDomination.Input := ((0, []), 0)
  ((context one true 0).last,
    (query one true).all fun c => c.length ≤ 3,
    match compile zero, TwoBoundary.BinaryFrontend.compile (UpperDomination.Unique.build zero) with
    | .inl a, .inl b => a == b
    | _, _ => false)

example : ComputableInPolyTime compile UpperDomination.encInput
    TwoBoundary.BinaryFrontend.encOutput := compile_polytime

example (x : UpperDomination.Input)
    (hn : 1 ≤ IndependentDomination.order (UpperDomination.graph x)) :
    oldDeclaration x + IndependentDomination.order (UpperDomination.graph x) =
      6 * IndependentDomination.order (UpperDomination.graph x) + UpperDomination.auxiliary x - 1 :=
  declaration x hn

end SharedMarkerTests
