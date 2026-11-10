/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (regression tests)

public import CslibFrontier.Computability.Complexity.FineGrained.UpperDomination
public import CslibFrontierTests.PaperEndpoints.CardinalityInterval
meta import CslibFrontier.Computability.PolyTime.CNF.UpperDomination
meta import CslibFrontierTests.PaperEndpoints.CardinalityInterval

/-! # Actual Upper Dominating Set construction and marking multiplicity

The tiny oracle enumerates original selection and mark words, and computes their unique gate
trace. It does not enumerate gate assignments. Production uses the proved sharp native counter.
-/

public section

namespace UpperDominationTests

open Cslib.Logic.PL Turing.MultiTapeTM Cslib.GenericRAM
open UpperDomination

set_option linter.hashCommand false

/-- Test-only evaluation of actual clauses/terms, preserving distinct private-mark choices. -/
@[expose] def count (x : Input) : ℕ :=
  let n := IndependentDomination.order (graph x)
  let (_, side, conditions) := build x
  ((List.range (2 ^ n)).map fun seed =>
    let trace := intervalTestValues n (threshold x).toNat n seed
    (List.range (2 ^ n)).countP fun marked =>
      let vals := trace ++ (List.range n).map (Nat.testBit marked)
      let y := (vals.getD · false)
      side.eval y && conditions.all (DNF.eval y)).sum

/- Empty and edgeless graphs; the original declaration includes every isolate. -/
/-- info: (1, 0, 1, 1, 1, 0) -/
#guard_msgs in
#eval (count ((0, []), 0), count ((0, []), 1), count ((0, []), -100),
  count ((3, List.replicate 3 (List.replicate 3 false)), 0),
  count ((3, List.replicate 3 (List.replicate 3 false)), 3),
  count ((3, List.replicate 3 (List.replicate 3 false)), 4))

/- An edge has two minimal dominating sets, each with three nonempty private-mark subsets. -/
/-- info: (6, 6, 0, 6, 0) -/
#guard_msgs in
#eval (count ((2, [[false, true], [true, false]]), 0),
  count ((2, [[false, true], [true, false]]), 1),
  count ((2, [[false, true], [true, false]]), 2),
  count ((2, [[false, true], [true, false]]), -(2 ^ 512)),
  count ((2, [[false, true], [true, false]]), 2 ^ 512))

/- P3 has a singleton set with seven markings and a two-leaf set with one marking. -/
/-- info: (8, 1, 0, 21, 0) -/
#guard_msgs in
#eval (count ((3, [[false, true, false], [true, false, true], [false, true, false]]), 1),
  count ((3, [[false, true, false], [true, false, true], [false, true, false]]), 2),
  count ((3, [[false, true, false], [true, false, true], [false, true, false]]), 3),
  count ((3, [[false, true, true], [true, false, true], [true, true, false]]), 1),
  count ((3, [[false, true, true], [true, false, true], [true, true, false]]), 2))

/- Adjacent selected vertices are allowed: upper domination is not independent domination. -/
/-- info: (6, 0, 16, 60) -/
#guard_msgs in
#eval (count ((4, [[false, true, false, true], [true, false, true, false],
  [false, true, false, true], [true, false, true, false]]), 2),
  count ((4, [[false, true, false, true], [true, false, true, false],
    [false, true, false, true], [true, false, true, false]]), 3),
  count ((4, [[false, true, false, false], [true, false, true, false],
    [false, true, false, true], [false, false, true, false]]), 2),
  count ((4, [[false, true, true, true], [true, false, true, true],
    [true, true, false, true], [true, true, true, false]]), 1))

/- The actual query writer includes all size gates and counts only original mark positions. -/
/-- info: (2, true, true) -/
#guard_msgs in
#eval Id.run do
  let x : Input := ((2, [[false, true], [true, false]]), 1)
  let qs := TwoBoundary.BinaryFrontend.queries (TwoBoundary.BinaryFrontend.compile (build x))
  return (qs.length, qs.all fun (n, _) => n == 4 * 2 + auxiliary x - 1,
    qs.all fun (n, q) => q.length ≤ 6000 * 2 ^ 3 &&
      q.all fun c => c.length ≤ 3 && c.all fun l => l.1 < n)

example : SimpleGraph.IsPrivateMarking (⊤ : SimpleGraph (Fin 2)) {0} {0, 1} := by
  refine ⟨?_, ?_, ?_⟩
  · intro w; exact ⟨0, rfl, by fin_cases w <;> simp [SimpleGraph.ClosedAdj]⟩
  · intro w _ u hu v hv _ _
    exact hu.trans hv.symm
  · intro u hu
    subst u
    exact ⟨0, by simp, Or.inl rfl⟩

open Classical in
/-- The public endpoint decides inclusion-minimal original sets, with variable signed thresholds
and the actual sharp native clock/global workspace. -/
example : ∃ decideUpper : Input → Bool, ∃ cs : NativeCertificate decideUpper encInput encBool,
    ∃ C e A : ℕ, (∀ x, cs.space x ≤ C * ((encInput x).length + 1) ^ e) ∧
      ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k : ℤ),
        (decideUpper (ofGraph G k) = true ↔ ∃ S : Set (Fin n),
          Minimal G.IsDominatingSet S ∧ k ≤ (Nat.card S : ℤ)) ∧
        (16 ≤ n → (cs.time (ofGraph G k) : ℝ) ≤ (C : ℝ) *
          ((encInput (ofGraph G k)).length + 1 : ℕ) ^ e *
            (2 : ℝ) ^ ((A : ℝ) * Real.logLogSqrtLogScale n)) :=
  exists_decide_realEta_certificate

end UpperDominationTests
