/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (regression tests)

public import CslibFrontier.Computability.PolyTime.CNF.RegularInducedCore
meta import CslibFrontier.Computability.PolyTime.CNF.RegularInducedCore

/-!
# Compact regular induced-subgraph core clients

Only tiny tests enumerate selection words. The production writer enumerates fixed-length
neighbor sublists and introduces neither threshold nor subset-witness variables.
-/

public section

namespace RegularInducedTests

open Cslib.Logic.PL Turing.MultiTapeTM IndependentDomination RegularInducedCore

set_option linter.hashCommand false

/-- Complete graph as an original encoded adjacency matrix. -/
@[expose] def clique (n : ℕ) : Input :=
  (n, (List.range n).map fun u => (List.range n).map fun v => decide (u ≠ v))

/-- Test-only exhaustive count of original selections against the actual constructed core. -/
@[expose] def countWords (d : ℕ) (g : Input) : ℕ :=
  let p := build d g
  (List.range (2 ^ order g)).countP fun seed =>
    let x := Nat.testBit seed
    (TwoBoundary.BinaryFrontend.side p).eval x &&
      (TwoBoundary.BinaryFrontend.conditions p).all (DNF.eval x)

/- Empty selections remain permitted; d is vertex degree, with no edge/vertex factor change. -/
/-- info: (2, 5, 2, 1, 1, 1) -/
#guard_msgs in
#eval (countWords 2 (clique 3), countWords 2 (clique 4), countWords 3 (clique 4),
  countWords 3 (clique 3), countWords 2 (clique 0),
  countWords 2 (3, List.replicate 3 (List.replicate 3 false)))

/- Degree two permits a disjoint union of cycles, not just one Hamiltonian cycle. -/
/-- info: 4 -/
#guard_msgs in
#eval countWords 2
  (6, (List.range 6).map fun u => (List.range 6).map fun v => decide (u ≠ v ∧ u / 3 = v / 3))

/- The no-size path uses only 2v-1 variables; bounded subset writing is compiled into real CNF. -/
/-- info: true -/
#guard_msgs in
#eval
  let qs := TwoBoundary.BinaryFrontend.queries
    (TwoBoundary.BinaryFrontend.compile (build 2 (clique 3)))
  qs.length == 2 && qs.all fun (N, q) =>
    N == 5 && q.all fun c => c.length ≤ 4 && c.all fun l => l.1 < N

example : ComputableInPolyTime (build 3) encInput TwoBoundary.BinaryFrontend.encInput :=
  build_polytime 3

example (G : SimpleGraph (Fin 4)) [DecidableRel G.Adj] (x : Fin 4 → Bool) :
    ((finiteUpper 2 G).eval x = true ∧ ∀ p ∈ finiteConditions 2 G, DNF.eval x p = true) ↔
      G.IsSigmaRhoSet {2} Set.univ {u | x u = true} := finite_semantics 2 G x

end RegularInducedTests
