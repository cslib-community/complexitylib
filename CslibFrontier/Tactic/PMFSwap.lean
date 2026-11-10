/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public meta import Lean.Elab.Tactic.Location

/-!
# Reordering independent samples

Two probabilistic experiments that draw the same independent samples in different orders have
the same law, by `PMF.bind_comm`. Proving such an equation by rewriting means navigating to each
swap (`conv_lhs => enter [2, a, 2, b]`) and stripping the common samples one at a time
(`congr 1 with x : 1`), and `simp [PMF.bind_comm]` loops on two samples of the same distribution.
The tactics here match samples by their distributions instead of their positions.

`pmf_swap` proves an equation `lhs = rhs` of distributions whose sides are chains of `PMF.bind`,
ending in `PMF.pure`, `PMF.map` or another distribution, the normal form of `simp only [pmf_norm]`.
It brings a sample of the right side that the left side draws independently of its earlier samples
to the front of both sides, by `PMF.bind_comm`, strips it, and continues with the continuations.
Samples of the same distribution may be matched in any order: the tactic searches for an order in
which the two sides become equal up to reducible unfolding, and then closes the goal. The search
has a budget, renewed after stripping each sample with a single possible partner, and the tactic
fails when it runs out. If no order works, it strips common samples and leaves the equation of the
remaining continuations, with the stripped samples as variables. It first strips samples whose
distribution occurs once on each side, which have only one possible partner, and then the first
matches of the others. `pmf_swap with x y` skips the search and strips exactly two samples, naming
them; plain `pmf_swap` strips every sample it can. It fails when it can strip no sample, listing
the samples of both sides and marking those that depend on earlier ones, which cannot move.

`pmf_hoist q` moves every sample of the distribution `q` in the goal, or in a hypothesis with
`at h`, as far toward the front of its chain as its independence allows. It works anywhere in the
goal, for instance inside a probability or an inequality, where `pmf_swap` does not apply.

Distributions are compared up to reducible unfolding, so a sample is found when it is written as
in the other side, possibly after `simp only [pmf_norm]`. A sample of a distribution that depends
on an earlier sample never moves past that sample.

## Main definitions

* `pmf_swap`: prove an equation of distributions that differ in the order of independent samples.
* `pmf_hoist`: move the samples of a given distribution to the front of their chains.
-/

public meta section

namespace Cslib.Tactic.PMFSwap

open Lean Meta Elab Tactic

/-- A step of a chain of samples: the distribution `head` and the continuation `cont`, so that the
chain is `head.bind cont`. -/
private structure Sample where
  /-- The distribution sampled. -/
  head : Expr
  /-- The rest of the chain, as a function of the sample. -/
  cont : Expr

/-- The first sample of `e`: `p.bind f` samples `p` and continues with `f`, and `p.map g`, which
is `p.bind (pure ∘ g)`, samples `p` and returns `g` of the sample. -/
private def sample? (e : Expr) : MetaM (Option Sample) := do
  match_expr e with
  | PMF.bind _ _ p f => return some { head := p, cont := f }
  | PMF.map α _ g p =>
    let n := if let .lam m .. := g then m else `x
    let cont ← withLocalDeclD n α fun x => do
      mkLambdaFVars #[x] (← mkAppM ``PMF.pure #[g.beta #[x]])
    return some { head := p, cont }
  | _ => return none

/-- Run `k x b` with a new variable `x` for the argument of the function `f`, where `b` is `f x`
reduced. -/
private def withBody {α : Type} (f : Expr) (k : Expr → Expr → MetaM α) : MetaM α := do
  let .forallE n dom _ _ ← whnf (← inferType f)
    | throwError "pmf_swap: expected a continuation, got{indentExpr f}"
  let n := if let .lam m .. := f then m else n
  withLocalDeclD n dom fun x => k x (f.beta #[x])

/-- The type of outcomes `α` of a distribution `p : PMF α`. -/
private def outcomeType (p : Expr) : MetaM Expr := do
  let ty ← instantiateMVars (← inferType p)
  let .app (.const ``PMF _) α := ty
    | throwError "pmf_swap: expected a distribution `PMF α`, got{indentExpr p}\n\
        of type{indentExpr ty}"
  return α

/-- `p.bind f = p.bind g` from `h : f = g`. -/
private def bindCongr (p f h : Expr) : MetaM Expr := do
  let F ← withLocalDeclD `k (← inferType f) fun k => do
    mkLambdaFVars #[k] (← mkAppM ``PMF.bind #[p, k])
  mkCongrArg F h

/-- The depths at which the chain `e` samples a distribution reducibly equal to `q`. A sample
whose distribution mentions an earlier sample is not equal to `q`, which is closed. -/
private partial def findDepths (q e : Expr) (depth : Nat := 0) : MetaM (Array Nat) := do
  let some s ← sample? e | return #[]
  let here ← withNewMCtxDepth <| withReducible <| isDefEq s.head q
  let rest ← withBody s.cont fun _ body => findDepths q body (depth + 1)
  return if here then #[depth] ++ rest else rest

/-- The first depth at which the chain `e` samples a distribution reducibly equal to `q`, assigning
the metavariables of `q`. -/
private partial def firstDepth? (q e : Expr) (depth : Nat := 0) : MetaM (Option Nat) := do
  let some s ← sample? e | return none
  if ← withReducible <| isDefEq s.head q then return some depth
  withBody s.cont fun _ body => firstDepth? q body (depth + 1)

/-- Move the sample at depth `k` of the chain `e`, whose distribution is reducibly equal to `q`
and independent of the earlier samples, to the front. Returns `q.bind g` and a proof of
`e = q.bind g`. -/
private partial def hoistAt (q e : Expr) : Nat → MetaM (Expr × Expr)
  | 0 => do
    let some s ← sample? e | throwError "pmf_swap: internal error: no sample to move"
    let e' ← mkAppM ``PMF.bind #[q, s.cont]
    return (e', ← mkExpectedTypeHint (← mkEqRefl e) (← mkEq e e'))
  | k + 1 => do
    let some s ← sample? e | throwError "pmf_swap: internal error: no sample to move"
    let p := s.head
    -- Inside the continuation, `fun x => q.bind (G x)`.
    let (hcont, G) ← withBody s.cont fun x body => do
      let (inner, h) ← hoistAt q body k
      return (← mkLambdaFVars #[x] h, ← mkLambdaFVars #[x] inner.appArg!)
    let h₁ ← bindCongr p s.cont (← mkFunExt hcont)
    -- `p.bind (fun x => q.bind (G x)) = q.bind (fun y => p.bind (fun x => G x y))`.
    let h₂ ← mkAppM ``PMF.bind_comm #[p, q, G]
    let .forallE xName xTy _ _ ← whnf (← inferType s.cont)
      | throwError "pmf_swap: internal error: continuation is not a function"
    let xName := if let .lam m .. := s.cont then m else xName
    let yName ← withBody s.cont fun x _ => do
      return if let .lam n .. := G.beta #[x] then n else `y
    let e' ← withLocalDeclD yName (← outcomeType q) fun y => do
      let pCont ← withLocalDeclD xName xTy fun x => do
        mkLambdaFVars #[x] (G.beta #[x, y])
      mkLambdaFVars #[y] (← mkAppM ``PMF.bind #[p, pCont])
    let e' ← mkAppM ``PMF.bind #[q, e']
    return (e', ← mkExpectedTypeHint (← mkEqTrans h₁ h₂) (← mkEq e e'))

/-- An alignment of `lhs = rhs`: a distribution `q` sampled independently at depth `kl` of `lhs`
and at depth `kr` of `rhs`. -/
private abbrev Alignment := Expr × Nat × Nat

/-- The ways to bring one sample to the front of both sides of `lhs = rhs`: the first sample of
`rhs` matched with each of its occurrences in `lhs`, and failing that the first sample of `lhs`
matched with each of its occurrences in `rhs`. Every proof by reordering matches the first sample
of `rhs` with some sample of `lhs`, so `search` loses nothing by trying only these. -/
private def alignments (lhs rhs : Expr) : MetaM (Array Alignment) := do
  if let some s ← sample? rhs then
    let ks ← findDepths s.head lhs
    unless ks.isEmpty do return ks.map ((s.head, ·, 0))
  if let some s ← sample? lhs then
    return (← findDepths s.head rhs).map ((s.head, 0, ·))
  return #[]

/-- The distributions of the samples of the chain `e` that do not depend on earlier samples. -/
private partial def independentHeads (e : Expr) (earlier : Array Expr := #[]) :
    MetaM (Array Expr) := do
  let some s ← sample? e | return #[]
  let dep := earlier.any fun x => s.head.containsFVar x.fvarId!
  let rest ← withBody s.cont fun x body => independentHeads body (earlier.push x)
  return if dep then rest else #[s.head] ++ rest

/-- A forced alignment of `lhs = rhs`: a sample of `rhs` whose distribution occurs exactly once on
each side, so that it has a single possible partner. -/
private def forced? (lhs rhs : Expr) : MetaM (Option Alignment) := do
  for q in ← independentHeads rhs do
    let kls ← findDepths q lhs
    let krs ← findDepths q rhs
    if let (#[kl], #[kr]) := (kls, krs) then return some (q, kl, kr)
  return none

/-- Carry out an alignment `(q, kl, kr)` of `lhs = rhs`: the continuations `f` and `g` and proofs
of `lhs = q.bind f` and `rhs = q.bind g`. -/
private def realize (lhs rhs : Expr) : Alignment → MetaM (Expr × Expr × Expr × Expr × Expr)
  | (q, kl, kr) => do
    let (lhs', hl) ← hoistAt q lhs kl
    let (rhs', hr) ← hoistAt q rhs kr
    return (q, lhs'.appArg!, rhs'.appArg!, hl, hr)

/-- A proof of `lhs = rhs` from `hl : lhs = q.bind f`, `hr : rhs = q.bind g` and `h : f = g`. -/
private def combine (lhs rhs q f hl hr h : Expr) : MetaM Expr := do
  let hmid ← bindCongr q f h
  let pf ← mkEqTrans (← mkEqTrans hl hmid) (← mkEqSymm hr)
  mkExpectedTypeHint pf (← mkEq lhs rhs)

/-- The number of steps of `search` for the goal and again after each forced alignment. -/
private def searchBudget : Nat := 256

/-- Search for a proof of `lhs = rhs` that aligns the samples of the two sides until the remaining
continuations are reducibly equal, trying every matching sample of the other side. Each call
spends one unit of `fuel`; when `fuel` reaches zero the search gives up, so `none` with no fuel
left means that the budget ran out, not that no matching exists. -/
private partial def search (fuel : IO.Ref Nat) (lhs rhs : Expr) : MetaM (Option Expr) := do
  if (← fuel.get) == 0 then return none
  fuel.modify (· - 1)
  if ← withNewMCtxDepth <| withReducible <| isDefEq lhs rhs then
    return some (← mkExpectedTypeHint (← mkEqRefl lhs) (← mkEq lhs rhs))
  for a in ← alignments lhs rhs do
    let (q, f, g, hl, hr) ← realize lhs rhs a
    let h? ← withBody f fun x fx => do
      let some h ← search fuel fx (g.beta #[x]) | return none
      return some (← mkLambdaFVars #[x] h)
    if let some h := h? then
      return some (← combine lhs rhs q f hl hr (← mkFunExt h))
  return none

/-- Strip one common sample from both sides of the goal `lhs = rhs` and introduce it as a variable
named `name?`, or an inaccessible one. A forced alignment comes first; otherwise, unless
`forcedOnly`, the first sample of `rhs` that `lhs` also draws. Returns the new goal, or `none` when
no sample can be aligned. -/
private def peel? (goal : MVarId) (name? : Option Name) (forcedOnly := false) :
    MetaM (Option MVarId) :=
  goal.withContext do
    let some (_, lhs, rhs) := (← instantiateMVars (← goal.getType)).cleanupAnnotations.eq?
      | return none
    let some a ← (do
        if let some a ← forced? lhs rhs then return some a
        if forcedOnly then return none
        return (← alignments lhs rhs)[0]?) | return none
    let (q, f, g, hl, hr) ← realize lhs rhs a
    let ty ← withBody f fun x fx => do mkForallFVars #[x] (← mkEq fx (g.beta #[x]))
    let m ← mkFreshExprSyntheticOpaqueMVar ty (← goal.getTag)
    goal.assign (← combine lhs rhs q f hl hr (← mkFunExt m))
    let (_, goal') ← match name? with
      | some n => m.mvarId!.intro n
      | none => m.mvarId!.intro1
    return some goal'

/-- The outcome of trying to close a goal by `search`. -/
private inductive Closed where
  /-- The goal is closed. -/
  | closed
  /-- No order of the samples makes the two sides equal. -/
  | noMatching
  /-- The budget ran out, and no remaining sample has a single possible partner. -/
  | outOfBudget

/-- Close the goal `g` by `search`. When the budget runs out, strip a sample with a single possible
partner, which every matching aligns the same way, and search the rest with a fresh budget. -/
private partial def closeGo (g : MVarId) : MetaM Closed := g.withContext do
  let some (_, lhs, rhs) := (← instantiateMVars (← g.getType)).cleanupAnnotations.eq?
    | return .noMatching
  let fuel ← IO.mkRef searchBudget
  if let some pf ← search fuel lhs rhs then
    g.assign pf
    return .closed
  if (← fuel.get) != 0 then return .noMatching
  let some g' ← peel? g none (forcedOnly := true) | return .outOfBudget
  closeGo g'

/-- Close the goal by `search`, as `closeGo`, assigning it only when it is closed. -/
private def close (goal : MVarId) : MetaM Closed := do
  let s ← saveState
  let r ← closeGo goal
  unless r matches .closed do s.restore
  return r

/-- The distributions sampled by the chain `e`, each marked when it depends on an earlier sample. -/
private partial def chainMsgs (e : Expr) (earlier : Array Expr := #[]) :
    MetaM (Array MessageData) := do
  let some s ← sample? e | return #[]
  let dep := earlier.any fun x => s.head.containsFVar x.fvarId!
  let msg ← addMessageContext
    m!"{s.head}{if dep then " (depends on an earlier sample)" else ""}"
  let rest ← withBody s.cont fun x body => chainMsgs body (earlier.push x)
  return #[msg] ++ rest

/-- The error when `pmf_swap` can strip no sample from `lhs = rhs`. -/
private def noCommonSample (lhs rhs : Expr) : MetaM MessageData := do
  let ls ← chainMsgs lhs
  let rs ← chainMsgs rhs
  if ls.isEmpty || rs.isEmpty then
    return m!"pmf_swap: both sides must be chains of `PMF.bind`; normalize them with \
      `simp only [pmf_norm]` first.\nLeft side:{indentExpr lhs}\nRight side:{indentExpr rhs}"
  let list (ms : Array MessageData) := indentD (MessageData.joinSep ms.toList Format.line)
  return m!"pmf_swap: the two sides have no independent sample in common.\n\
    Left side samples:{list ls}\nRight side samples:{list rs}\n\
    A sample can move to the front only when its distribution does not depend on earlier samples."

/-- `pmf_swap` proves an equation `lhs = rhs` of distributions whose sides draw the same
independent samples in different orders. Both sides are chains of `PMF.bind`, as produced by
`simp only [pmf_norm]`. The tactic brings a sample that both sides draw independently of their
earlier samples to the front of both, by `PMF.bind_comm`, strips it, and continues. Samples are
matched by their distributions, up to reducible unfolding, not by position.

If the samples can be matched so that the two sides become equal, up to reducible unfolding, the
goal is closed; samples of the same distribution are tried in every order. The search has a budget
of 256 steps, renewed after stripping each sample whose distribution occurs once on each side, and
the tactic fails when the budget runs out with no such sample left. If no order makes the sides
equal, `pmf_swap` strips common samples and leaves the equation of what remains, with the
stripped samples as variables: first the samples whose distribution occurs once on each side, then
the first match of each remaining sample of the right side, and fails when it can strip none.
`pmf_swap with x y` skips the search and strips exactly two samples in the same way, named in the
order they are stripped, and fails if it cannot. -/
syntax (name := pmfSwap) "pmf_swap" (" with" (ppSpace colGt binderIdent)+)? : tactic

@[inherit_doc pmfSwap]
elab_rules : tactic
  | `(tactic| pmf_swap $[with $xs*]?) => do
    let names : Array (Option Name) := (xs.getD #[]).map fun
      | `(binderIdent| $n:ident) => some n.getId
      | _ => none
    let goal ← getMainGoal
    goal.withContext do
      let target := (← instantiateMVars (← goal.getType)).cleanupAnnotations
      let some (ty, lhs, rhs) := target.eq?
        | throwError "pmf_swap: the goal is not an equation of distributions{indentExpr target}"
      unless (← whnfR ty).isAppOf ``PMF do
        throwError "pmf_swap: the goal is an equation in{indentExpr ty}\n\
          not an equation of distributions `PMF α`"
      if names.isEmpty then
        match ← close goal with
        | .closed => replaceMainGoal []; return
        | .outOfBudget => throwError "pmf_swap: the search for an order of the samples ran out \
            of its budget of {searchBudget} steps.\nStrip samples with `pmf_swap with x …`, or \
            reorder them with `pmf_hoist` or `PMF.bind_comm`, to leave fewer samples to match."
        | .noMatching => pure ()
      let mut g := goal
      let mut i := 0
      repeat
        if !names.isEmpty && i == names.size then break
        let some g' ← peel? g (names[i]?).join | break
        g := g'
        i := i + 1
      if i == 0 then throwError (← noCommonSample lhs rhs)
      if i < names.size then
        g.withContext do
          throwError "pmf_swap: only {i} of the {names.size} named samples can be stripped; \
            what remains is{indentExpr (← instantiateMVars (← g.getType))}"
      replaceMainGoal [g]

/-- `pmf_hoist q` moves every sample of the distribution `q`, in every chain of `PMF.bind` in the
goal, as far toward the front of its chain as possible, by `PMF.bind_comm`: past every earlier
sample, which `q` cannot depend on. `q` may contain holes `_`, which are filled by its first match.
Like `rw`, it then closes a goal that has become reflexive. `pmf_hoist q at h` works on the
hypothesis `h` instead. It fails when no sample of `q` moves. -/
syntax (name := pmfHoist) "pmf_hoist " term (Lean.Parser.Tactic.location)? : tactic

@[inherit_doc pmfHoist]
elab_rules : tactic
  | `(tactic| pmf_hoist $qStx $[$loc]?) => withMainContext do
    let q ← instantiateMVars (← elabTerm qStx none (mayPostpone := true))
    discard <| outcomeType q
    let hoisted ← IO.mkRef false
    let methods : Simp.Methods := {
      pre := fun e => do
        let some k ← firstDepth? q e | return .continue
        if k == 0 then return .continue
        let (e', pf) ← hoistAt (← instantiateMVars q) e k
        hoisted.set true
        return .visit { expr := e', proof? := some pf } }
    let ctx ← Simp.mkContext { zeta := false, iota := false, proj := false }
    let run (e : Expr) : MetaM Simp.Result := do
      hoisted.set false
      let (r, _) ← Simp.main e ctx (methods := methods)
      unless ← hoisted.get do
        throwError "pmf_hoist: no sample of{indentExpr q}\ncan move toward the front of its chain"
      return r
    withLocation (expandOptLocation (mkOptionalNode loc))
      (atLocal := fun h => do
        let goal ← getMainGoal
        let r ← run (← instantiateMVars (← h.getType))
        match ← applySimpResultToLocalDecl goal h r false with
        | none => replaceMainGoal []
        | some (_, g) => replaceMainGoal [g])
      (atTarget := do
        let goal ← getMainGoal
        let target ← instantiateMVars (← goal.getType)
        let goal ← applySimpResultToTarget goal target (← run target)
        -- Like `rw`, close a goal that has become reflexive.
        try withReducible goal.refl; replaceMainGoal []
        catch _ => replaceMainGoal [goal])
      (failed := fun _ => throwError "pmf_hoist: no sample of{indentExpr q}\ncan move")

end Cslib.Tactic.PMFSwap
