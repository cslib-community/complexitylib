/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (regression tests)

public import Complexity.Computability.Complexity.FineGrained.IndependentDominationInterval
public import ComplexityTests.PaperEndpoints.CardinalityInterval
meta import Complexity.Computability.PolyTime.CNF.IndependentDominationInterval
meta import Complexity.Computability.Complexity.FineGrained.TwoBoundaryFrontend
meta import ComplexityTests.PaperEndpoints.CardinalityInterval

/-! # Signed input-size graph counting and actual query writing

The small oracle enumerates original selections and computes gate traces; it does not enumerate
auxiliaries. Empty direct dispatch, mixed signed bounds and original-size tests are exercised.
-/

public section

open Cslib.Logic.PL Turing.MultiTapeTM Cslib.GenericRAM
open IndependentDominationInterval

set_option linter.hashCommand false

/-- Small test oracle for actual side clauses and overlapping neighborhood DNFs. -/
@[expose] def graphIntervalTestCount (x : Input) : ℕ :=
  let g := graph x
  let n := IndependentDomination.order g
  let (_, side, conditions) := build x
  (List.range (2 ^ n)).countP fun seed =>
    let vals := intervalTestValues n (lower x) (upper x) seed
    let σ := (vals.getD · false)
    side.eval σ && conditions.all (DNF.eval σ)

/-- Signed normalization and direct empty dispatch use the actual frontend. -/
@[expose] def graphSignedTestCount (x : Signed.Input) : ℕ := Signed.run graphIntervalTestCount x

/-- Three-vertex path, with overlapping closed neighborhoods. -/
@[expose] def testPath : IndependentDomination.Input :=
  (3, [[false, true, false], [true, false, true], [false, true, false]])

/-- info: (1, 1, 0, 0, 0, 2) -/
#guard_msgs in
#eval (graphSignedTestCount (testPath, 1, 1), graphSignedTestCount (testPath, 2, 2),
  graphSignedTestCount (testPath, 0, 0), graphSignedTestCount (testPath, 3, 100),
  graphSignedTestCount (testPath, 2, 1), graphSignedTestCount (testPath, -100, 2 ^ 512))

/-- info: (2, 3, 0, 1, 0) -/
#guard_msgs in
#eval (graphSignedTestCount ((2, [[false, true], [true, false]]), 1, 1),
  graphSignedTestCount
    ((3, [[false, true, true], [true, false, true], [true, true, false]]), 1, 1),
  graphSignedTestCount
    ((3, [[false, true, true], [true, false, true], [true, true, false]]), 2, 2),
  graphSignedTestCount ((3, List.replicate 3 (List.replicate 3 false)), 3, 3),
  graphSignedTestCount ((3, List.replicate 3 (List.replicate 3 false)), 0, 2))

/- Empty graphs bypass the supplied continuation; negative upper bounds reject. -/
/-- info: (1, 0, 0, 1, 0) -/
#guard_msgs in
#eval (Signed.run (fun _ => 999) ((0, []), 0, 0),
  Signed.run (fun _ => 999) ((0, []), 1, 0),
  Signed.run (fun _ => 999) ((0, []), -10, -1),
  Signed.run (fun _ => 999) ((0, []), -10, 10),
  graphSignedTestCount (testPath, -10, -1))

/- Actual two-query writing includes computed gates, with no full auxiliary cube traversal. -/
/-- info: (2, true, true) -/
#guard_msgs in
#eval let x : Input := (testPath, 1, 2)
  let qs := TwoBoundary.BinaryFrontend.queries (TwoBoundary.BinaryFrontend.compile (build x))
  (qs.length,
    qs.all fun (n, _) => n == 2 * IndependentDomination.order testPath + auxiliary x - 1,
    qs.all fun (_, q) => q.all fun c => c.length ≤ 3)

example : ComputableInPolyTime build encInput TwoBoundary.BinaryFrontend.encInput := build_polytime
example : ComputableInPolyTime Signed.normalize Signed.encInput encInput :=
  Signed.normalize_polytime

/- A negative upper bound normalizes to a contradictory interval, even with a negative lower. -/
example : Signed.normalize ((0, []), -10, -1) = ((0, []), 1, 0) := rfl

open Classical in
/-- Original vertex counts, both varying signed bounds, global space and sharp native clock. -/
example : ∃ count : Signed.Input → ℕ,
    ∃ cs : NativeCertificate count Signed.encInput encNat, ∃ C e A : ℕ,
      (∀ x, cs.space x ≤ C * ((Signed.encInput x).length + 1) ^ e) ∧
      ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (lo hi : ℤ),
        count (Signed.ofGraph G lo hi) =
          Fintype.card {x : Fin n → Bool // G.IsIndepSet {u | x u = true} ∧
            (∀ u, x u = true ∨ ∃ v, G.Adj u v ∧ x v = true) ∧
            lo ≤ (Cslib.BitString.weight x : ℤ) ∧ (Cslib.BitString.weight x : ℤ) ≤ hi} ∧
        cs.time (Signed.ofGraph G lo hi) ≤
          C * ((Signed.encInput (Signed.ofGraph G lo hi)).length + 1) ^ e *
            2 ^ (A * Nat.logLogSqrtLogScale n) := Signed.exists_count_sharp_certificate
