/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (regression tests)

public import Complexity.Computability.Complexity.FineGrained.UpperDominationUnique
public import ComplexityTests.PaperEndpoints.UpperDomination
meta import Complexity.Computability.PolyTime.CNF.UpperDominationUnique
meta import ComplexityTests.PaperEndpoints.CardinalityInterval
meta import ComplexityTests.PaperEndpoints.UpperDomination

/-!
# Exact original-set counts from the actual augmented marking construction

Tiny tests enumerate only original selection/mark words, computing their unique functional gate
trace. The production native counter is the proved sharp width-four counter, not this test oracle.
-/

public section

namespace UpperDominationUniqueTests

open Cslib.Logic.PL Turing.MultiTapeTM Cslib.GenericRAM
open UpperDomination

set_option linter.hashCommand false

/-- Test-only actual augmented clause/term evaluation, preserving the unique gate trace. -/
@[expose] def count (x : Input) : ℕ :=
  let n := IndependentDomination.order (graph x)
  let base := Unique.build x
  ((List.range (2 ^ n)).map fun seed =>
    let trace := intervalTestValues n (threshold x).toNat n seed
    (List.range (2 ^ n)).countP fun marked =>
      let bits := trace ++ (List.range n).map (Nat.testBit marked)
      let y := (bits.getD · false)
      (TwoBoundary.BinaryFrontend.side base).eval y &&
        (TwoBoundary.BinaryFrontend.conditions base).all (DNF.eval y)).sum

/- Empty graphs and declared isolates retain their ordinary minimal-set semantics. -/
/-- info: (1, 0, 1, 1, 1, 0) -/
#guard_msgs in
#eval (count ((0, []), 0), count ((0, []), 1), count ((0, []), -100),
  count ((3, List.replicate 3 (List.replicate 3 false)), 0),
  count ((3, List.replicate 3 (List.replicate 3 false)), 3),
  count ((3, List.replicate 3 (List.replicate 3 false)), 4))

/- Two original sets for an edge, rather than the approved old construction's six marking pairs. -/
/-- info: (2, 6, 2, 0, 2, 0) -/
#guard_msgs in
#eval (count ((2, [[false, true], [true, false]]), 0),
  UpperDominationTests.count ((2, [[false, true], [true, false]]), 0),
  count ((2, [[false, true], [true, false]]), 1),
  count ((2, [[false, true], [true, false]]), 2),
  count ((2, [[false, true], [true, false]]), -(2 ^ 512)),
  count ((2, [[false, true], [true, false]]), 2 ^ 512))

/- P3 has a singleton and a two-leaf minimal set. A triangle has exactly three singleton sets. -/
/-- info: (2, 1, 0, 3, 0) -/
#guard_msgs in
#eval (count ((3, [[false, true, false], [true, false, true], [false, true, false]]), 1),
  count ((3, [[false, true, false], [true, false, true], [false, true, false]]), 2),
  count ((3, [[false, true, false], [true, false, true], [false, true, false]]), 3),
  count ((3, [[false, true, true], [true, false, true], [true, true, false]]), 1),
  count ((3, [[false, true, true], [true, false, true], [true, true, false]]), 2))

/- C4 includes four adjacent pairs, as well as its two opposite pairs. P4 has four minimal sets. -/
/-- info: (6, 4, 4, 2) -/
#guard_msgs in
#eval (count ((4, [[false, true, false, true], [true, false, true, false],
  [false, true, false, true], [true, false, true, false]]), 2),
  count ((4, [[false, true, false, false], [true, false, true, false],
    [false, true, false, true], [false, false, true, false]]), 1),
  count ((4, [[false, true, true, true], [true, false, true, true],
    [true, true, false, true], [true, true, true, false]]), 1),
  count ((3, [[false, true, false], [true, false, false], [false, false, false]]), 2))

/- Actual emitted queries have the source dimension and width, without assignment enumeration. -/
/-- info: (2, true, true) -/
#guard_msgs in
#eval Id.run do
  let x : Input := ((2, [[false, true], [true, false]]), 1)
  let qs := TwoBoundary.BinaryFrontend.queries (TwoBoundary.BinaryFrontend.compile (Unique.build x))
  return (qs.length, qs.all fun (n, _) => n == 5 * 2 + auxiliary x - 1,
    qs.all fun (n, q) => q.length ≤ 6000 * 2 ^ 3 &&
      q.all fun c => c.length ≤ 4 && c.all fun l => l.1 < n)

example : SimpleGraph.IsCompletePrivateMarking (⊤ : SimpleGraph (Fin 2)) {0} Set.univ := by
  refine ⟨⟨?_, ?_, ?_⟩, fun w => Or.inl (Set.mem_univ w)⟩
  · intro w; exact ⟨0, rfl, by fin_cases w <;> simp [SimpleGraph.ClosedAdj]⟩
  · intro w _ u hu v hv _ _; exact hu.trans hv.symm
  · intro u hu; subst u; exact ⟨0, Set.mem_univ _, Or.inl rfl⟩

example : ¬SimpleGraph.IsCompletePrivateMarking (⊤ : SimpleGraph (Fin 2)) {0} {0} := by
  intro h
  have he := ((⊤ : SimpleGraph (Fin 2)).completePrivateMarking_iff {0} {0}).mp h |>.2
  have hm : (1 : Fin 2) ∈ (⊤ : SimpleGraph (Fin 2)).privateMarks {0} :=
    ⟨0, rfl, Or.inr (by decide), fun _ hv _ => hv⟩
  rw [← he] at hm
  norm_num at hm

open Classical in
/-- The public resource endpoint counts original minimal dominating sets, not marked pairs. -/
example : ∃ count : Input → ℕ, ∃ cs : NativeCertificate count encInput encNat, ∃ C e A : ℕ,
    (∀ x, cs.space x ≤ C * ((encInput x).length + 1) ^ e) ∧
    ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k : ℤ),
      count (ofGraph G k) =
        Fintype.card {S : Set (Fin n) // Minimal G.IsDominatingSet S ∧ k ≤ (Nat.card S : ℤ)} ∧
      (16 ≤ n → (cs.time (ofGraph G k) : ℝ) ≤ (C : ℝ) *
        ((encInput (ofGraph G k)).length + 1 : ℕ) ^ e *
          (2 : ℝ) ^ ((A : ℝ) * Real.logLogSqrtLogScale n)) :=
  Unique.exists_count_realEta_certificate

end UpperDominationUniqueTests
