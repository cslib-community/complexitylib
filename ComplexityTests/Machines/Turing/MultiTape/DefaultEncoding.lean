/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Default
import Complexity.Computability.Machines.Turing.MultiTape.Universal.Complexity

/-! Tests of `enc%`: it produces the spelled-out term, with no trace of the registry. -/

open Lean Meta Elab Term Command

namespace Turing.MultiTapeTM

/-- Fail unless two terms elaborate to syntactically equal expressions. -/
elab "assert_same_term " a:term " ~ " b:term : command => liftTermElabM do
  let a ← instantiateMVars (← elabTermAndSynthesize a none)
  let b ← instantiateMVars (← elabTermAndSynthesize b none)
  unless a == b do throwError "different terms{indentExpr a}\nand{indentExpr b}"

assert_same_term (enc% : (List ℕ × List Bool) × Option ℕ ↪ List Bool)
  ~ encPair (encPair (encList encNat) encBits) (encOption encNat)
assert_same_term (enc% : List (List Bool) ↪ List Bool) ~ encList encBits
assert_same_term (enc% : List (Option Bool) ↪ List Bool) ~ encList (encOption encBool)
assert_same_term (encPair enc% encUnary : List ℕ × ℕ ↪ List Bool)
  ~ encPair (encList encNat) encUnary

/-- Fail unless two terms agree up to reducible unfolding and `name` stays folded in the first. -/
elab "assert_keeps_folded " name:ident " in " a:term " ~ " b:term : command => liftTermElabM do
  let a ← instantiateMVars (← elabTermAndSynthesize a none)
  let b ← instantiateMVars (← elabTermAndSynthesize b none)
  unless ← withReducible (isDefEq a b) do
    throwError "different terms{indentExpr a}\nand{indentExpr b}"
  let c ← realizeGlobalConstNoOverloadWithInfo name
  unless a.containsConst (· == c) do throwError "{c} was unfolded in{indentExpr a}"

/-! Both encodings are determined by the function, and automation sees plain terms. -/

theorem cons_viaDefault :
    ComputableInPolyTime (fun q : List ℕ × ℕ => q.2 :: q.1) enc% enc% := by
  fun_prop

theorem cons_spelledOut : ComputableInPolyTime (fun q : List ℕ × ℕ => q.2 :: q.1)
    (encPair (encList encNat) encNat) (encList encNat) :=
  cons_viaDefault

run_cmd liftCoreM do
  let env ← getEnv
  unless (env.find? ``cons_viaDefault).get!.type == (env.find? ``cons_spelledOut).get!.type do
    throwError "`enc%` changed the statement"
  if (env.find? ``cons_viaDefault).get!.type.containsConst (· == ``DefaultEnc) then
    throwError "`DefaultEnc` survived elaboration"

/-! A local registration applies only in its section. -/

section
local instance (priority := high) : DefaultEnc ℕ := ⟨encUnary⟩
assert_same_term (enc% : List ℕ ↪ List Bool) ~ encList encUnary
end
assert_same_term (enc% : List ℕ ↪ List Bool) ~ encList encNat

/-! Registered terms stay folded: the Universal machine's abbreviations are not unfolded. -/

section
open Universal
local instance (priority := high) : DefaultEnc (Option ℕ) := ⟨eSym⟩
local instance (priority := high) : DefaultEnc TapeAct := ⟨eTA⟩
local instance : DefaultEnc Tape := ⟨eTape⟩
assert_keeps_folded eTA in (enc% : (List TapeAct × List Tape) × Tape ↪ List Bool)
  ~ encPair (encPair (encList eTA) (encList eTape)) eTape
end

/-! An unregistered type, a type without a default and a missing expected type are errors. -/

structure Unregistered where
  value : ℕ

/--
error: enc%: no default encoding is registered for
  Unregistered
-/
#guard_msgs in
example : Unregistered ↪ List Bool := enc%

/--
error: enc%: no default encoding is registered for
  ℤ
-/
#guard_msgs in
example : ℤ ↪ List Bool := enc%

/--
error: enc%: expected an encoding `α ↪ List Bool`, got
  ℕ
-/
#guard_msgs in
example : ℕ := enc%

end Turing.MultiTapeTM
