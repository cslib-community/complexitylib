/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (regression tests)

public import CslibFrontier.Computability.Complexity.FineGrained.RegularInducedInterval
public import CslibFrontierTests.PaperEndpoints.CardinalityInterval
public import CslibFrontierTests.PaperEndpoints.RegularInducedCore
meta import CslibFrontier.Computability.PolyTime.CNF.RegularInducedInterval
meta import CslibFrontierTests.PaperEndpoints.CardinalityInterval
meta import CslibFrontierTests.PaperEndpoints.RegularInducedCore

/-!
# Compact regular induced subgraphs with actual signed size tests

The tiny test oracle enumerates only original selections and computes their unique gate trace.
The production counter instead uses the proved native bounded-width counter and sharp resources.
-/

public section

namespace RegularInducedIntervalTests

open Cslib.Logic.PL Turing.MultiTapeTM Cslib.GenericRAM IndependentDominationInterval

set_option linter.hashCommand false

/-- Test-only original-selection oracle for the actual generated gate/degree formula. -/
@[expose] def naturalCount (d : ℕ) (x : Input) : ℕ :=
  let n := IndependentDomination.order (graph x)
  let (_, B, P) := RegularInducedInterval.build d x
  (List.range (2 ^ n)).countP fun seed =>
    let vals := intervalTestValues n (lower x) (upper x) seed
    let y := (vals.getD · false)
    B.eval y && P.all (DNF.eval y)

/-- The genuine signed normalization and empty dispatch around the tiny test oracle. -/
@[expose] def count (d : ℕ) (x : Signed.Input) : ℕ := Signed.run (naturalCount d) x

/- Sizes count vertices, not matching edges. Equal bounds, contradictions and signed caps vary. -/
/-- info: (1, 0, 1, 4, 0, 0, 0, 2) -/
#guard_msgs in
#eval (count 2 (RegularInducedTests.clique 3, 3, 3),
  count 2 (RegularInducedTests.clique 3, 1, 2),
  count 2 (RegularInducedTests.clique 3, 0, 0),
  count 2 (RegularInducedTests.clique 4, 3, 3),
  count 2 (RegularInducedTests.clique 4, 4, 4),
  count 2 (RegularInducedTests.clique 3, 3, 2),
  count 2 (RegularInducedTests.clique 3, -(2 ^ 512), -1),
  count 2 (RegularInducedTests.clique 3, -(2 ^ 512), 2 ^ 512))

/- Degree three, declared isolates and the genuine direct empty branch. -/
/-- info: (1, 1, 0, 1, 0, 0) -/
#guard_msgs in
#eval (count 3 (RegularInducedTests.clique 4, 4, 4),
  count 2 ((3, List.replicate 3 (List.replicate 3 false)), 0, 0),
  count 2 ((3, List.replicate 3 (List.replicate 3 false)), 1, 100),
  count 2 ((0, []), -1, 0), count 2 ((0, []), 1, 100), count 2 ((0, []), -100, -1))


/- Exact size distinguishes one cycle, two cycles and an impossible intermediate size. -/
/-- info: (2, 1, 0) -/
#guard_msgs in
#eval let g : IndependentDomination.Input :=
    (6, (List.range 6).map fun u => (List.range 6).map fun v => decide (u ≠ v ∧ u / 3 = v / 3))
  (count 2 (g, 3, 3), count 2 (g, 6, 6), count 2 (g, 4, 4))

open Classical in
/- A genuinely contradictory interval has no models of the actual compiled plan. -/
example (G : SimpleGraph (Fin 4)) [DecidableRel G.Adj] :
    TwoBoundary.BinaryFrontend.value (TwoBoundary.BinaryFrontend.compile
      (RegularInducedInterval.Signed.build 2 (Signed.ofGraph G 4 3))) = 0 := by
  rw [RegularInducedInterval.Signed.plan_count 2 (by decide)]
  apply Fintype.card_eq_zero_iff.mpr
  refine ⟨fun x => ?_⟩
  have hl := x.property.2.1
  have hh := x.property.2.2
  omega

/- Every emitted original-bound query has the compact gate-dependent declaration and width. -/
/-- info: (2, true, true) -/
#guard_msgs in
#eval let x : Signed.Input := (RegularInducedTests.clique 3, 3, 3)
  let qs := TwoBoundary.BinaryFrontend.queries
    (TwoBoundary.BinaryFrontend.compile (RegularInducedInterval.Signed.build 2 x))
  let a := auxiliary (Signed.normalize x)
  (qs.length, qs.all fun (N, _) => N == 2 * 3 + a - 1,
    qs.all fun (N, q) => q.all fun c => c.length ≤ 4 && c.all fun l => l.1 < N)

example : ComputableInPolyTime (RegularInducedInterval.Signed.build 3) Signed.encInput
    TwoBoundary.BinaryFrontend.encInput := RegularInducedInterval.Signed.build_polytime 3

open Classical in
/-- The actual interval counter has the real source clock and polynomial workspace globally. -/
example : ∃ count : Signed.Input → ℕ,
    ∃ cs : NativeCertificate count Signed.encInput encNat, ∃ C e A : ℕ,
      (∀ x, cs.space x ≤ C * ((Signed.encInput x).length + 1) ^ e) ∧
      ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (lo hi : ℤ),
        count (Signed.ofGraph G lo hi) =
          Fintype.card {x : Fin n → Bool // G.IsSigmaRhoSet {2} Set.univ {u | x u = true} ∧
            lo ≤ (Cslib.BitString.weight x : ℤ) ∧ (Cslib.BitString.weight x : ℤ) ≤ hi} ∧
        (16 ≤ n → (cs.time (Signed.ofGraph G lo hi) : ℝ) ≤ (C : ℝ) *
          ((Signed.encInput (Signed.ofGraph G lo hi)).length + 1 : ℕ) ^ e *
            (2 : ℝ) ^ ((A : ℝ) * Real.logLogSqrtLogScale n)) :=
  RegularInducedInterval.Signed.exists_count_realEta_certificate 2 (by decide)

open Classical in
/-- Positive counts give an actual native decision, retaining both signed bounds. -/
example : ∃ yes : Signed.Input → Bool,
    ∃ cs : NativeCertificate yes Signed.encInput encBool, ∃ C e A : ℕ,
      (∀ x, cs.space x ≤ C * ((Signed.encInput x).length + 1) ^ e) ∧
      ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (lo hi : ℤ),
        (yes (Signed.ofGraph G lo hi) = true ↔ ∃ x : Fin n → Bool,
          G.IsSigmaRhoSet {3} Set.univ {u | x u = true} ∧
            lo ≤ (Cslib.BitString.weight x : ℤ) ∧ (Cslib.BitString.weight x : ℤ) ≤ hi) ∧
        (16 ≤ n → (cs.time (Signed.ofGraph G lo hi) : ℝ) ≤ (C : ℝ) *
          ((Signed.encInput (Signed.ofGraph G lo hi)).length + 1 : ℕ) ^ e *
            (2 : ℝ) ^ ((A : ℝ) * Real.logLogSqrtLogScale n)) :=
  RegularInducedInterval.Signed.exists_decide_realEta_certificate 3 (by decide)

end RegularInducedIntervalTests
