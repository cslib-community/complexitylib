/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CNF.ExactOneElimination
meta import CslibFrontier.Logics.Propositional.CNF.ExactOneElimination
meta import Mathlib.Data.Fintype.Basic
meta import Mathlib.Data.Fintype.Sum
meta import Mathlib.Data.Fintype.Pi
meta import Mathlib.Data.Fintype.Card
meta import Mathlib.Data.Finset.Insert
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! Executed elimination, rational failure cases and actual two-query assembly. -/

public section

open Cslib.LinearSystem Cslib.Logic.PL Cslib.Logic.PL.ExactOne Matrix

set_option linter.hashCommand false

/-- A rank-two system with repeated rows and an unused column. -/
@[expose] def triangularRows (i : Fin 4) : Fin 3 → ℚ :=
  if i = 0 then ![2, 3, 0] else ![0, 5, 0]

/- The candidate needs nonintegral arithmetic during back-substitution. -/
/-- info: ([0, 1], [1, 2, 0], true) -/
#guard_msgs in
#eval let r := eliminateCached (List.finRange 4) (List.finRange 3) triangularRows
        (fun i => if i = 0 then 8 else 10)
  (r.indices.map Fin.val, List.ofFn r.point, r.consistent)

/- A zero coefficient row with nonzero right-hand side is inconsistent. -/
/-- info: false -/
#guard_msgs in
#eval (eliminateCached (List.finRange 2) (List.finRange 1)
  (fun _ _ => (0 : ℚ)) (fun i => if i = 0 then 0 else 1)).consistent

/- A full-rank matrix whose first column needs a later original pivot row. -/
/-- info: ([1, 0], [1 / 2, 1 / 3], true) -/
#guard_msgs in
#eval let r := eliminateCached (List.finRange 2) (List.finRange 2)
        (fun i => if i = 0 then ![0, 3] else ![2, 0]) (fun _ => 1)
  (r.indices.map Fin.val, List.ofFn r.point, r.consistent)

/-- Forty declared bits, with eighty duplicate original rows. No Boolean-cube
or row-subset enumeration is feasible here; preprocessing still emits two CNFs. -/
@[expose] def wideScopes (_ : Fin 80) : Finset (Fin 40) := {0, 1}

/-- A computable counter for regression tests only, distinct from `declaredCount`. -/
@[expose] def bruteCount {W : Type*} [Fintype W] [DecidableEq W] (B : CNF W) : ℕ :=
  (Finset.univ.filter fun x : W → Bool => B.eval x = true).card

/-- Summarize without running a counter on a large query. -/
@[expose] def shape {V : Type*} [Fintype V] : CountPlan V → ℕ × ℕ × ℕ × ℕ
  | .direct n => (0, n, 0, 0)
  | .queries k q₀ q₁ => (2, Fintype.card V + k, q₀.length, q₁.length)

/-- info: (2, 40, 2, 4) -/
#guard_msgs in
#eval shape (preprocess ([] : CNF (Fin 40)) wideScopes (fun _ _ => true))

/-- The checked endpoint applies without assumed selected rows or rational witnesses. -/
example : (preprocess ([] : CNF (Fin 40)) wideScopes (fun _ _ => true)).value =
    sourceCount [] wideScopes (fun _ _ => true) := preprocess_correct _ _ _

/-- And the actual emitted syntax has the sharp declared-variable budget. -/
example : (preprocess ([] : CNF (Fin 40)) wideScopes (fun _ _ => true)).Budget 40 :=
  preprocess_budget _ (by simp) _ _

/-- Repeated signed equations, side constraints and a retained unused bit. -/
@[expose] def smallScopes (_ : Fin 5) : Finset (Fin 3) := {0, 1}

/-- info: ((2, 3, 3, 5), 2) -/
#guard_msgs in
#eval let plan := preprocess ([[(0, false)]] : CNF (Fin 3)) smallScopes (fun _ _ => true)
  (shape plan, plan.execute (fun _ => bruteCount))

/- A non-Boolean unique rational candidate is rejected by the direct branch. -/
/-- info: (0, 0, 0, 0) -/
#guard_msgs in
#eval shape (preprocess ([] : CNF (Fin 3))
  (fun i : Fin 3 => if i = 0 then {0, 1} else if i = 1 then {1, 2} else {0, 2})
  (fun _ _ => true))

/- A Boolean unique candidate satisfies the empty side CNF. -/
/-- info: (0, 1, 0, 0) -/
#guard_msgs in
#eval shape (preprocess ([] : CNF (Fin 2)) (fun i : Fin 2 => {i}) (fun _ _ => true))

/- Contradictory signs are detected as rational inconsistency. -/
/-- info: (0, 0, 0, 0) -/
#guard_msgs in
#eval shape (preprocess ([] : CNF (Fin 2)) (fun _ : Fin 2 => {0})
  (fun i _ => i == 0))

/- No exact-one equations leaves all three declared bits counted. -/
/-- info: ((2, 3, 0, 1), 8) -/
#guard_msgs in
#eval let plan := preprocess ([] : CNF (Fin 3))
        (fun i : Fin 0 => Fin.elim0 i) (fun i => Fin.elim0 i)
  (shape plan, plan.execute (fun _ => bruteCount))

/- Zero and one declared bit are inspected directly. -/
/-- info: (1, 2) -/
#guard_msgs in
#eval ((preprocess ([] : CNF (Fin 0)) (fun i : Fin 0 => Fin.elim0 i)
    (fun i => Fin.elim0 i)).execute (fun _ => bruteCount),
  (preprocess ([] : CNF (Fin 1)) (fun i : Fin 0 => Fin.elim0 i)
    (fun i => Fin.elim0 i)).execute (fun _ => bruteCount))

/-- Decode all possible signed scopes on two declared bits. -/
@[expose] def decodedScope (a : Fin 16) : Finset (Fin 2) :=
  Finset.univ.filter fun v => a.val.testBit v.val

/-- The upper two bits choose polarities; out-of-scope signs are irrelevant. -/
@[expose] def decodedPolarity (a : Fin 16) (v : Fin 2) : Bool :=
  a.val.testBit (v.val + 2)

/- Exhaustively execute all 256 ordered pairs of signed two-bit rows and compare
with a separate direct source count. This covers the non-small preprocessing path,
empty scopes, dependent and inconsistent systems, and non-Boolean candidates. -/
/-- info: true -/
#guard_msgs in
#eval (List.finRange 16).all fun a => (List.finRange 16).all fun b =>
  let S := fun i : Fin 2 => decodedScope (if i = 0 then a else b)
  let p := fun i : Fin 2 => decodedPolarity (if i = 0 then a else b)
  (preprocess ([] : CNF (Fin 2)) S p).execute (fun _ => bruteCount) == smallCount [] S p
