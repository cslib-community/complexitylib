/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CNF.ExactOneBinary
public import CslibFrontierTests.PaperEndpoints.ExactOneElimination
meta import CslibFrontier.Logics.Propositional.CNF.ExactOneBinary
meta import CslibFrontierTests.PaperEndpoints.ExactOneElimination

/-! Execute binary-selected original equations through direct and query branches. -/

public section

open Cslib.Logic.PL Cslib.Logic.PL.ExactOne

set_option linter.hashCommand false

/-- info: true -/
#guard_msgs in
#eval (List.finRange 16).all fun a => (List.finRange 16).all fun b =>
  let S := fun i : Fin 2 => decodedScope (if i = 0 then a else b)
  let p := fun i : Fin 2 => decodedPolarity (if i = 0 then a else b)
  (binaryPreprocess S p []).execute (fun _ => bruteCount) == smallCount [] S p

/-- info: (2, 40, 2, 4) -/
#guard_msgs in
#eval shape (binaryPreprocess wideScopes (fun _ _ => true) [])

/-- The actual binary backend preserves the count on all forty declared bits. -/
example : (binaryPreprocess wideScopes (fun _ _ => true) []).value =
    sourceCount [] wideScopes (fun _ _ => true) := binaryPreprocess_correct _ _ _

/-- The bound applies uniformly in both dimensions. -/
example {n m : ℕ} (S : Fin m → Finset (Fin n)) (p : Fin m → Fin n → Bool) :
    (binaryPreprocess S p []).Budget n := binaryPreprocess_budget S p [] (by simp)

/-- info: (0, 0, 0, 0) -/
#guard_msgs in
#eval shape (binaryPreprocess
  (fun i : Fin 3 => if i = 0 then {0, 1} else if i = 1 then {1, 2} else {0, 2})
  (fun _ _ : Fin 3 => true) [])

/-- info: (0, 1, 0, 0) -/
#guard_msgs in
#eval shape (binaryPreprocess (fun i : Fin 2 => {i}) (fun _ _ => true) [])

/-- info: (8, 2) -/
#guard_msgs in
#eval ((binaryPreprocess (fun i : Fin 0 => Fin.elim0 i)
    (fun i => Fin.elim0 i) ([] : CNF (Fin 3))).execute (fun _ => bruteCount),
  (binaryPreprocess (fun i : Fin 0 => Fin.elim0 i)
    (fun i => Fin.elim0 i) ([] : CNF (Fin 1))).execute (fun _ => bruteCount))
