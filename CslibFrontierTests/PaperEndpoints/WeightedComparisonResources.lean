/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (regression tests)

public import CslibFrontier.Computability.Complexity.FineGrained.WeightedComparisonSource
public import CslibFrontierTests.PaperEndpoints.WeightedComparison
meta import CslibFrontier.Computability.Complexity.FineGrained.WeightedComparisonDistribution
meta import CslibFrontier.Computability.PolyTime.CNF.WeightedComparison.Signed
meta import CslibFrontierTests.PaperEndpoints.WeightedComparison

/-!
# Actual binary weighted writers and joint-distribution clients

The tiny evaluator enumerates only original assignments and executes the actual complete gate
list, CNF and every original predicate. It tests the public traversal, preserving correlations
and zero bins. It is not the subexponential production counter or its resource premise.
-/

public section

open Cslib.Circuits Cslib.Circuits.Boolean Cslib.Circuits.Boolean.WeightedSum
open Cslib.Logic.PL Turing.MultiTapeTM

set_option linter.hashCommand false

/-- Tiny original-assignment evaluation of the actual augmented writer. -/
@[expose] def weightedAugmentedCount (r c : ℕ) (x : WithBase.Input) : ℕ :=
  let n := TwoBoundary.BinaryFrontend.declared (WithBase.original x)
  let code := Family.code (fun _ : Fin r => .eq) c (WithBase.frame x)
  let (_, side, predicates) := WithBase.build (fun _ : Fin r => .eq) c x
  (List.range (2 ^ n)).countP fun seed =>
    let vals := weightedTrace (List.ofFn (fun i : Fin n => seed.testBit i.val)) code.1
    let assignment := fun i => vals[i]?.getD false
    side.eval assignment && predicates.all (fun p => DNF.eval assignment p)

/-- Two complementary tests on the very same original bit, plus unchanged original predicates. -/
@[expose] def weightedCorrelated (P : List (DNF (Fin 1))) : Distribution.Input :=
  Distribution.ofData ([] : CNF (Fin 1)) P
    (fun _ : Fin 2 => fun _ => 1) (fun j _ => j.val == 0)

/-- info: [([0, 0], 0), ([0, 1], 1), ([1, 0], 1), ([1, 1], 0)] -/
#guard_msgs in
#eval Distribution.run 2 0 (weightedAugmentedCount 2 0) (weightedCorrelated [])

/- Both original predicate occurrences survive; their annotation multiplicity is unchanged. -/
/-- info: [([0, 0], 0), ([0, 1], 0), ([1, 0], 1), ([1, 1], 0)] -/
#guard_msgs in
#eval Distribution.run 2 0 (weightedAugmentedCount 2 0)
  (weightedCorrelated [[[(0, true)]], [[(0, true)]]])

/-- info: [([0, 0], 0), ([0, 1], 0), ([1, 0], 0), ([1, 1], 0)] -/
#guard_msgs in
#eval Distribution.run 2 0 (weightedAugmentedCount 2 0) (weightedCorrelated [[]])

/- A nonunit coefficient and a zero-weight unused original bit. Impossible bins stay present. -/
/-- info: [([0], 2), ([1], 0), ([2], 2), ([3], 0), ([4], 0)] -/
#guard_msgs in
#eval Distribution.run 1 1 (weightedAugmentedCount 1 1)
  (Distribution.ofData ([] : CNF (Fin 2)) [] (fun _ : Fin 1 => ![2, 0]) (fun _ _ => true))

/-- info: ([([0, 0], 1)], [([], 2)], [([0, 0], 0)]) -/
#guard_msgs in
#eval (Distribution.run 2 1 (weightedAugmentedCount 2 1)
    (Distribution.ofData ([] : CNF (Fin 0)) [] (fun _ : Fin 2 => Fin.elim0)
      (fun _ => Fin.elim0)),
  Distribution.run 0 0 (weightedAugmentedCount 0 0)
    (Distribution.ofData ([] : CNF (Fin 1)) [] (r := 0) Fin.elim0 Fin.elim0),
  Distribution.run 2 1 (weightedAugmentedCount 2 1)
    (Distribution.ofData ([[]] : CNF (Fin 0)) [] (fun _ : Fin 2 => Fin.elim0)
      (fun _ => Fin.elim0)))

/- Actual signed offset, zero coefficient, cancellation, and binary huge coefficients/targets. -/
/-- info: (2, [(2, false), (0, true)], 0) -/
#guard_msgs in
#eval SignedFrontend.normalize (2, ([-2, 0], -2))

/-- info: (true, true, 1) -/
#guard_msgs in
#eval ((SignedFrontend.normalize (2, ([-(2 ^ 512), 2 ^ 512], 0))).2.2 == 2 ^ 512,
  BinaryFrontend.entries (SignedFrontend.normalize (2, ([-(2 ^ 512), 2 ^ 512], 0))) ==
    [(2 ^ 512, false), (2 ^ 512, true)],
  (Family.code (fun _ : Fin 1 => .le) 1
    (2, ([[(2, true), (0, false)]], [2 ^ 1024]))).1.length)

/-- info: (4, 8, true) -/
#guard_msgs in
#eval ((Distribution.queries 2 0 (weightedCorrelated [])).length,
  (Distribution.queries 2 0 (weightedCorrelated [[[(0, true)]]])).length,
  TwoBoundary.BinaryFrontend.conditions (WithBase.build (fun _ : Fin 2 => .eq) 0
    (Distribution.request (weightedCorrelated [[[(0, true)]], [[(0, true)]]], [1, 0]))) ==
      TwoBoundary.BinaryFrontend.conditions
        (Distribution.original (weightedCorrelated [[[(0, true)]], [[(0, true)]]])))

/- These pin the resource endpoints, not a supplied evaluator/runtime contract. -/
example (op : Comparison) (c : ℕ) :
    ∃ cs : Cslib.GenericRAM.NativeCertificate (SignedFrontend.build op c)
        SignedFrontend.encInput VCOne.encSignedCNF, ∃ C e : ℕ,
      ∀ x, cs.time x ≤ C * ((SignedFrontend.encInput x).length + 1) ^ e ∧
        cs.space x ≤ C * ((SignedFrontend.encInput x).length + 1) ^ e :=
  exists_signed_generator_resources op c

example : ∃ count, ∃ cs : Cslib.GenericRAM.NativeCertificate count Distribution.encInput
    (encList Distribution.encEntry), ∃ C e : ℕ,
    ∀ x, cs.space x ≤ C * ((Distribution.encInput x).length + 1) ^ e := by
  obtain ⟨count, cs, C, e, _, hs, _⟩ :=
    Distribution.exists_distribution_realEta_certificate 2 0 1 1
  exact ⟨count, cs, C, e, hs⟩

example {n : ℕ} (weights : Fin 2 → Fin n → ℕ)
    (hw : ∀ j i, (weights j i : ℝ) ≤ (n : ℝ) ^ (1 / 2 : ℝ)) :
    ∀ j i, weights j i ≤ n ^ ⌈(1 / 2 : ℝ)⌉₊ :=
  weight_bound_of_parameter _ (by norm_num) le_rfl weights hw
