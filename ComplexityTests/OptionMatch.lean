/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.Option
import Complexity.Tactic.OptionMatch

/-! Tests of `option_match_to_elim` and of `fun_prop` on the resulting `Option.elim`. -/

public section

namespace ComplexityTests.OptionMatch

open Turing.MultiTapeTM

/-! A `match` is available to `fun_prop` as `Option.elim`, under binders and nested. -/

/-- A definition with nested matches, with the alternatives in either order. -/
def nested (o : Option ℕ) (b : ℕ) : ℕ × ℕ :=
  match o with
  | none => (b, 0)
  | some q =>
    match (if q = b then some q else none) with
    | some e => (e, q)
    | none => (q, 1)

example : (fun p : Option ℕ × ℕ => nested p.1 p.2) = fun p =>
    p.1.elim (p.2, 0) fun q => (if q = p.2 then some q else none).elim (q, 1) fun e => (e, q) := by
  unfold nested
  option_match_to_elim
  rfl

-- An alternative may use the discriminant.
example (o : Option ℕ) : (match o with | none => o | some x => o.map (· + x)) =
    o.elim o fun x => o.map (· + x) := by
  option_match_to_elim
  rfl

-- `Option.map` and `Option.any` unfold to a `match`.
example (o : Option ℕ) (f : ℕ → ℕ) : o.map f = o.elim none fun x => some (f x) := by
  unfold Option.map
  option_match_to_elim
  rfl

example (o : Option ℕ) (f : ℕ → Bool) : o.any f = o.elim false f := by
  unfold Option.any
  option_match_to_elim
  rfl

-- `Option.bind`, with a nested use.
example (o p : Option ℕ) (f : ℕ → ℕ → Option ℕ) :
    (o.bind fun x => p.bind (f x)) = o.elim none fun x => p.elim none (f x) := by
  option_match_to_elim
  rfl

/-- error: option_match_to_elim: no option match in the goal -/
#guard_msgs in
example (o : Option ℕ) (h : o.isSome) : (match o, h with | some x, _ => x) = o.get h := by
  option_match_to_elim

-- An alternative that takes its pattern apart is left unchanged.
/-- error: option_match_to_elim: no option match in the goal -/
#guard_msgs in
example (o : Option (ℕ × ℕ)) :
    (match o with | some (a, b) => a + b | none => 0) = o.elim 0 fun p => p.1 + p.2 := by
  option_match_to_elim

/-! A `match` is assembled by `fun_prop` with bounds up to constants, without an inhabitant of the
payload type. -/

example {α : Type} (enc : α ↪ List Bool) :
    ComputableInO (fun p : Option α × α => match p.1 with | none => p.2 | some a => a)
      (encPair (encOption enc) enc) enc
      (fun p => (encPair (encOption enc) enc p).length)
      fun p => (encPair (encOption enc) enc p).length := by
  option_match_to_elim
  refine .mono (by fun_prop) 8 (fun p => ?_) fun p => ?_
  all_goals
    rcases p with ⟨_ | a, d⟩ <;>
      simp only [Option.elim_none, Option.elim_some, length_encPair, encOption_some,
        List.length_cons] <;> omega

end ComplexityTests.OptionMatch
