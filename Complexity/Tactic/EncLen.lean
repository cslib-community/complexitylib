/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.List
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Option
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Pair
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Sum
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Unary
public meta import Lean.Elab.Tactic.Omega
public meta import Lean.Elab.Tactic.Simp

/-!
# Closing bounds on encoded lengths

`enc_len` expands encoded lengths into the lengths of their fields, then counts with `omega`.

The expansion is `simp only` with a fixed list of lemmas for the standard encodings, followed by
the lemmas given at the call. Local encodings stay visible there: `enc_len [eFoo_apply]`. The
location works as for `simp`, so hypotheses are expanded only when requested, as in
`enc_len at h ⊢`.

`omega` treats a product of two lengths as an atom, which it can match only when both sides
expanded to the same term. Bound a product by a fact in its own step, and bound each component by
one context length in its own step, so that the last `enc_len` only adds. Expanding everything at
once costs more: `omega` slows sharply with the number of atoms and facts.

The tactic fails when nothing expands, naming the plain `omega` that is then the right call, and
when `omega` cannot close the expanded goal, showing that goal.

## Main definitions

* `enc_len`: expand encoded lengths into their fields and close the bound with `omega`.
-/

public section

namespace Cslib.Tactic.EncLen

open Lean Parser.Tactic Elab Tactic Turing.MultiTapeTM

/-- `enc_len` closes a linear bound on encoded lengths: it expands them into the lengths of their
fields with `simp only`, then runs `omega`.

* `enc_len [eFoo_apply]` also unfolds the local encoding `eFoo`.
* `enc_len at h ⊢` also expands the hypothesis `h`; without a location only the goal is expanded.

Products of lengths are atoms for `omega`. Bound them by facts in context first. -/
syntax (name := encLen) "enc_len" (" [" (simpStar <|> simpErase <|> simpLemma),* "]")?
  (location)? : tactic

elab_rules : tactic
  | `(tactic| enc_len $[[$args,*]]? $[$loc]?) => do
    let args := (args.map (·.getElems)).getD #[]
    try
      evalTactic (← `(tactic| simp only [length_encPair, length_frame, encUnary_apply,
        List.length_replicate, encBits_apply, encBool_apply, encOption_none, encOption_some,
        encSum_inl, encSum_inr, List.length_nil, List.length_cons, List.length_append,
        $args,*] $[$loc]?))
    catch ex =>
      throwError "enc_len: the expansion failed: {ex.toMessageData}\n\
        If there is no encoded length to expand, use `omega`."
    if (← getUnsolvedGoals).isEmpty then return
    let goal ← getMainGoal
    try
      evalTactic (← `(tactic| omega))
    catch ex =>
      throwError "enc_len: `omega` could not close the expanded goal. Products are atoms, so \
        bound them by facts in context, and unfold local encodings with `enc_len [eFoo_apply]`.\n\
        {goal}\n{ex.toMessageData}"

end Cslib.Tactic.EncLen

end
