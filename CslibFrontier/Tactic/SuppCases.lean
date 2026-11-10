/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Languages.Probabilistic.Semantics
public import CslibFrontier.Probability.PMF.Uniform
public import CslibFrontier.Tactic.SuppCases.Init
public meta import Lean.Elab.Tactic.RCases
public meta import Lean.Elab.Tactic.Simp

/-!
# Inverting a support membership

A proof about a probabilistic program often starts from a hypothesis `h : x ∈ m.support` and
needs the intermediate results that produced `x`: for `m = p >>= f`, some `a ∈ p.support` with
`x ∈ (f a).support`, and so on through every `bind`, `map` and `pure` of the program. Written by
hand, each layer is one `obtain ⟨a, ha, h⟩ := (PMF.mem_support_bind_iff _ _ _).mp h`, or its
`OracleComp.supportWith` counterpart, and each returned value one more `cases` on an equation.

The simp set `supp_norm` does the rewriting, and `supp_cases h` does it and destructures the
result. The set covers `PMF` and the possible results `OracleComp.supportWith` of oracle
programs, including `OracleComp.support` and `ProbComp`. Membership in the support of

* `p >>= f`, `PMF.bind p f`: `∃ a, a ∈ p.support ∧ x ∈ (f a).support`;
* `f <$> p`, `PMF.map f p`: `∃ a, a ∈ p.support ∧ f a = x`;
* `pure a`, `PMF.pure a`: `x = a`;
* `if c then p else q`: `c ∧ x ∈ p.support ∨ ¬c ∧ x ∈ q.support`;
* a uniform draw (`ProbComp.unifFin`, `ProbComp.uniform`, `PMF.uniformOfFintype`) or a query
  answered from `Set.univ`: `True`, so the drawn value has no membership hypothesis;
* the law `ProbComp.eval m` of a program: as for `m`, through `PMF.bind`, `PMF.map` and
  `PMF.pure`.

The set then substitutes a returned value into the rest of a sequence (`exists_eq_left`) and
splits an equation of pairs into equations of their components (`Prod.mk.injEq`). The order of
the existentials is the order of the program, so `rcases` patterns follow its binds.

## Main definitions

* `supp_cases h`: rewrite `h` with `supp_norm` and destructure the result completely,
  substituting every equation one of whose sides is a local variable.
* `supp_cases h with pat`: rewrite `h` with `supp_norm` and destructure it with the `rcases`
  pattern `pat`.

## Main results

* `Cslib.Probability.PMF.mem_support_ite_iff`, `Cslib.OracleComp.mem_supportWith_ite_iff`:
  membership in the support of a conditional, as a disjunction over the condition.
-/

public section

namespace Cslib

/-- A value is in the support of a conditional distribution iff it is in the support of the branch
the condition selects. -/
theorem Probability.PMF.mem_support_ite_iff {α : Type*} (c : Prop) [Decidable c] (p q : PMF α)
    (x : α) : x ∈ (if c then p else q).support ↔ c ∧ x ∈ p.support ∨ ¬c ∧ x ∈ q.support := by
  by_cases hc : c <;> simp [hc]

/-- A possible result of a conditional program is a possible result of the branch the condition
selects. -/
theorem OracleComp.mem_supportWith_ite_iff {ι : Type*} {spec : OracleSpec ι} {α : Type*}
    {possible : (q : ι) → Set (spec q)} (c : Prop) [Decidable c] (p q : OracleComp spec α)
    (x : α) :
    x ∈ supportWith possible (if c then p else q) ↔
      c ∧ x ∈ supportWith possible p ∨ ¬c ∧ x ∈ supportWith possible q := by
  by_cases hc : c <;> simp [hc]

attribute [supp_norm]
  -- monad notation on `PMF`, and the law of a closed program
  Probability.PMF.monad_bind_eq_bind Probability.PMF.monad_pure_eq_pure PMF.monad_map_eq_map
  ProbComp.eval_bind ProbComp.eval_pure ProbComp.eval_map ProbComp.eval_unifFin
  ProbComp.eval_uniform
  -- supports of `PMF`
  PMF.mem_support_bind_iff PMF.mem_support_map_iff PMF.mem_support_pure_iff
  Probability.PMF.mem_support_ite_iff Probability.PMF.mem_support_uniformOfFintype
  -- possible results of oracle programs
  OracleComp.mem_supportWith_bind_iff OracleComp.mem_supportWith_map_iff
  OracleComp.supportWith_pure OracleComp.supportWith_query OracleComp.mem_supportWith_ite_iff
  ProbComp.mem_support_unifFin
  -- the shape of the result
  Set.mem_singleton_iff Set.mem_univ true_and and_true exists_eq_left Prod.mk.injEq
  -- a decided condition selects its branch
  not_true_eq_false not_false_eq_true false_and false_or or_false

end Cslib

end

public meta section

namespace Cslib.Tactic.SuppCases

open Lean Meta Elab Tactic Parser.Tactic

/-- Whether `e`, a set, is the support of a `PMF` or the possible results of an `OracleComp`
program. -/
private def isSupport (e : Expr) : Bool :=
  let f := e.cleanupAnnotations.headBeta.getAppFn
  f.isConstOf ``PMF.support || f.isConstOf ``Cslib.OracleComp.supportWith ||
    f.isConstOf ``Cslib.OracleComp.support

/-- Whether `e` states a membership in a support (`isSupport`). -/
private def isSupportMembership (e : Expr) : Bool :=
  match_expr e.cleanupAnnotations with
  | Membership.mem _ _ _ s _ => isSupport s
  | _ => false

/-- Destructure the hypotheses named `todo` in `g` completely: introduce the witness and proof of
each existential, split conjunctions, case on disjunctions, close the goal at `False` or at an
equation of distinct constructors, drop `True`, and substitute each equation one of whose sides is
a local variable. Hypotheses are tracked by name, since substituting reintroduces the hypotheses
that mention the eliminated variable under new identifiers; the names are fresh, so they show as
inaccessible. Returns the remaining goals. -/
private partial def destruct (g : MVarId) : List Name → MetaM (List MVarId)
  | [] => return [g]
  | n :: todo => g.withContext do
    let some d := (← getLCtx).findFromUserName? n | destruct g todo
    let type := (← instantiateMVars d.type).cleanupAnnotations
    let fresh (base : Name) : MetaM Name := mkFreshUserName base
    match_expr type with
    | False =>
      g.assign (← mkFalseElim (← g.getType) d.toExpr)
      return []
    | True => destruct (← g.clear d.fvarId) todo
    | Exists _ body =>
      let w ← fresh (if let .lam bn .. := body then bn else `w)
      let h ← fresh `h
      let #[s] ← g.cases d.fvarId #[{ varNames := [w, h] }] | throwError "supp_cases: \
        unexpected cases result"
      destruct s.mvarId (h :: todo)
    | And _ _ =>
      let l ← fresh `h
      let r ← fresh `h
      let #[s] ← g.cases d.fvarId #[{ varNames := [l, r] }] | throwError "supp_cases: \
        unexpected cases result"
      destruct s.mvarId (l :: r :: todo)
    | Or _ _ =>
      let l ← fresh `h
      let r ← fresh `h
      let #[sl, sr] ← g.cases d.fvarId #[{ varNames := [l] }, { varNames := [r] }]
        | throwError "supp_cases: unexpected cases result"
      return (← destruct sl.mvarId (l :: todo)) ++ (← destruct sr.mvarId (r :: todo))
    | Eq _ lhs rhs =>
      if lhs.isFVar || rhs.isFVar then
        if let some g' ← observing? (subst g d.fvarId) then
          return ← destruct g' todo
      else if let some #[] ← observing? (g.cases d.fvarId) then
        -- distinct constructors or literals
        return []
      destruct g todo
    | _ => destruct g todo

/-- `supp_cases h` inverts a hypothesis `h : x ∈ m.support`, where `m` is a `PMF` or an
`OracleComp` program (`OracleComp.supportWith`, `OracleComp.support`, `ProbComp`) built from
`bind`, `map`, `pure`, `if` and uniform draws. It rewrites `h` with the simp set `supp_norm` into
existentials over the supports of the parts of `m` and equations for its returned values, in the
order of the program, then destructures it:

* `supp_cases h` destructures completely: each intermediate result and each support hypothesis
  is introduced with an inaccessible name, conditionals split into one goal per branch, and every
  equation one of whose sides is a local variable is substituted. Use it when the rest of the
  proof needs no names, or refers to hypotheses by type (`‹_›`, `assumption`, `omega`).
* `supp_cases h with ⟨a, ha, b, hb, rfl⟩` destructures with an `rcases` pattern instead.
* `supp_cases h [foo_def, hc]` first adds the given simp lemmas to the rewriting, to unfold a
  named program or decide a condition.

It fails when `h` does not state a membership in a support, and when the simp set does not apply
to it, for instance because the program is a definition that must be unfolded first. -/
syntax (name := suppCases) "supp_cases " ident
  (" [" (simpStar <|> simpErase <|> simpLemma),* "]")? (" with " rcasesPatLo)? : tactic

elab_rules : tactic
  | `(tactic| supp_cases $h:ident $[[$args,*]]? $[with $pat]?) => focus <| withMainContext do
    let some d := (← getLCtx).findFromUserName? h.getId
      | throwError "supp_cases: unknown hypothesis `{h.getId}`"
    let type ← instantiateMVars d.type
    unless isSupportMembership type do
      throwError "supp_cases: `{h.getId}` does not state a membership in the support of a \
        distribution or program:{indentExpr type}"
    let args := (args.map (·.getElems)).getD #[]
    let normSet := mkIdent `supp_norm
    try
      evalTactic (← `(tactic| simp only [$normSet:ident, $args,*] at $h:ident))
    catch ex =>
      throwError "supp_cases: the simp set `supp_norm` does not apply to `{h.getId}`. If the \
        distribution is a definition or a local `let`, unfold it with \
        `supp_cases {h.getId} [foo]`.{indentExpr type}\n{ex.toMessageData}"
    if (← getUnsolvedGoals).isEmpty then return
    match pat with
    | some pat => evalTactic (← `(tactic| rcases $h:ident with $pat))
    | none => liftMetaTactic fun g => destruct g [h.getId]

end Cslib.Tactic.SuppCases

end
