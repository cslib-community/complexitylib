/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (regression tests)

public import CslibFrontier.Computability.Complexity.FineGrained.ExactCover
meta import CslibFrontier.Computability.PolyTime.CNF.ExactCover

/-!
# Executed indexed Exact Cover frontend and complete resource clients

Only tiny emitted queries/original selections are enumerated in this test. The production
implementation uses the proved native counter, and never searches the original/auxiliary cube.
Cases retain equal candidates, repeated incidences, optional empty candidates and uncovered
universe elements. The universe may be much larger than the candidate parameter.
-/

public section

open Cslib.Logic.PL Turing.MultiTapeTM
open Cslib.Logic.PL.ExactCover

set_option linter.hashCommand false

/-- Tiny test-only exact interpretation of an emitted ordinary query. -/
@[expose] def coverTinyQuery (N : ℕ) (Q : CNF ℕ) : ℕ :=
  (List.range (2 ^ N)).countP fun seed => Q.eval fun i => seed.testBit i
/-- Execute the actual direct/tagged output, using the tiny test interpreter only for queries. -/
@[expose] def coverTinyExecute (x : Input) : ℕ :=
  match compile x with
  | .inl n => n
  | .inr (N, qf, qt) => coverTinyQuery N qf - coverTinyQuery N qt
/-- Independent original-choice evaluation, with set membership rather than occurrence count. -/
@[expose] def coverTinyOriginal (x : Input) : ℕ :=
  (List.range (2 ^ size x)).countP fun seed =>
    (List.range (universeSize x)).all fun v =>
      ((List.range (size x)).countP fun i => seed.testBit i &&
        ((candidates x).getD i []).contains v) == 1

/-- info: ([[(0, true), (1, true)]], 4, 4, 2) -/
#guard_msgs in
#eval (transpose (1, [[0], [0], []]), coverTinyExecute (1, [[0], [0], []]),
  coverTinyOriginal (1, [[0], [0], []]), coverTinyExecute (1, [[0, 0], [0]]))

/-- info: (1, 0, 8, 1, 0) -/
#guard_msgs in
#eval (coverTinyExecute (0, []), coverTinyExecute (1, []),
  coverTinyExecute (0, [[], [], []]), coverTinyExecute (2, [[0, 1]]),
  coverTinyExecute (2, [[0]]))

/-- info: (1, 0, 0, 2) -/
#guard_msgs in
#eval (coverTinyExecute (3, [[0, 1], [2]]),
  coverTinyExecute (3, [[0, 1], [1, 2], [0, 2]]),
  coverTinyExecute (3, [[0, 1], [2], []]) - coverTinyOriginal (3, [[0, 1], [2], []]),
  coverTinyExecute (20, [List.range 20, List.range 20]))

/- Every three-candidate family on the two-element universe, with indexed repetitions. -/
#guard ([[], [0], [1], [0, 1]] : List (List ℕ)).all fun a =>
  ([[], [0], [1], [0, 1]] : List (List ℕ)).all fun b =>
    ([[], [0], [1], [0, 1]] : List (List ℕ)).all fun c =>
      coverTinyExecute (2, [a, b, c]) == coverTinyOriginal (2, [a, b, c])

/- Raw source admission is checked explicitly; out-of-universe labels use the documented
intersection convention of the total program, rather than being asserted admitted inputs. -/
/-- info: (true, false, false, [[]]) -/
#guard_msgs in
#eval (admit (1, [[0, 0], []]), admit (0, [[0]]), admit (1, [[2 ^ 512]]),
  transpose (1, [[2 ^ 512]]))

/- No original-assignment enumeration in this 80-candidate direct branch. -/
example : compile (0, List.replicate 80 []) = .inl (2 ^ 80) := by decide
example : (ExactOne.BinaryPlan.encOutput (compile (0, List.replicate 80 []))).length = 82 := by
  decide

/-- info: (0, 2, true) -/
#guard_msgs in
#eval ((queries (3, [[0, 1], [2]])).length, (queries (1, [[0], [0], []])).length,
  (queries (20, [List.range 20, List.range 20])).all fun (N, q) =>
    N ≤ 2 * 2 - 2 && q.length ≤ 16 * 2 ^ 2 + 16 * 2 + 3)

example (x : Input) : WeightedRow.BinaryPlan.Output.count (compile x) = count x :=
  compile_count x

example (x : Input) : WeightedRow.BinaryPlan.WithinBudget (size x) 1 (compile x) :=
  compile_withinBudget x

example : ∃ counter : Input → ℕ,
    ∃ cs : Cslib.GenericRAM.NativeCertificate counter encInput encNat, ∃ C e A : ℕ,
      (∀ x, counter x = count x) ∧
      (∀ x, cs.space x ≤ C * ((encInput x).length + 1) ^ e) ∧
      ∀ x, cs.time x ≤ C * ((encInput x).length + 1) ^ e *
        2 ^ (A * Nat.logLogSqrtLogScale (size x)) := exists_count_sharp_certificate

example : ∃ decision : Input → Bool,
    ∃ cs : Cslib.GenericRAM.NativeCertificate decision encInput encBool, ∃ C e A : ℕ,
      (∀ x, decision x = true ↔ ∃ σ, IsCover x σ) ∧
      (∀ x, cs.space x ≤ C * ((encInput x).length + 1) ^ e) ∧
      ∀ x, 16 ≤ size x → (cs.time x : ℝ) ≤
        (C : ℝ) * ((encInput x).length + 1 : ℕ) ^ e *
          (2 : ℝ) ^ ((A : ℝ) * Real.logLogSqrtLogScale (size x)) :=
  exists_decision_realEta_certificate
