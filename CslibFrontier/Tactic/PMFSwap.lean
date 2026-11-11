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
remaining continuations, with the stripped samples as variables, unless `rfl` proves it. It first
strips samples whose distribution occurs once on each side, which have only one possible partner,
and then the first matches of the others. `pmf_swap with x y` skips the search and strips exactly
two samples, naming them in the order they occur in the right side; plain `pmf_swap` strips every
sample it can. It fails when it can strip no sample, listing the samples of both sides and marking
those that depend on earlier ones, which cannot move. `pmf_swap [h]` also moves samples past a
sampler `F`, a function of a continuation, given a commutation lemma
`h : μ.bind (fun b => F (k b)) = F (fun a => μ.bind fun b => k b a)`.

`pmf_hoist q` moves every sample of the distribution `q` in the goal, or in a hypothesis with
`at h`, as far toward the front of its chain as its independence allows. It works anywhere in the
goal, for instance inside a probability or an inequality, where `pmf_swap` does not apply.
`pmf_hoist (occ := n) q` moves only the `n`th sample of `q`, for chains that draw `q` more than
once.

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

/-- The head of an application, for a cheap test that an expression may be a sampler. -/
private inductive HeadKey where
  /-- A constant. -/
  | const (n : Name)
  /-- A local variable. -/
  | fvar (x : FVarId)
  deriving BEq

/-- The head of the application `e`, if it is a constant or a local variable. -/
private def headKey? (e : Expr) : Option HeadKey :=
  match e.getAppFn with
  | .const n _ => some (.const n)
  | .fvar x => some (.fvar x)
  | _ => none

/-- A commutation lemma `μ.bind (fun b => F (k b)) = F (fun a => μ.bind fun b => k b a)`, which
lets an independent sample of any `μ` move past the sampler `F`. -/
private structure Comm where
  /-- The lemma, with its metavariables abstracted. -/
  thm : AbstractMVarsResult
  /-- The lemma as written, for messages. -/
  stx : Syntax
  /-- The head of the sampler `F`. -/
  key : HeadKey
  /-- The number of arguments of the sampler `F`. -/
  arity : Nat

/-- The proof of the commutation lemma `c` applied to fresh metavariables, its two sides, and the
metavariables. -/
private def Comm.inst (c : Comm) : MetaM (Expr × Expr × Expr × Array Expr) := do
  let (ms, _, pf) ← openAbstractMVarsResult c.thm
  let (xs, _, ty) ← forallMetaTelescopeReducing (← instantiateMVars (← inferType pf))
  let some (_, lhs, rhs) := (← instantiateMVars ty).cleanupAnnotations.eq?
    | throwError "pmf_swap: {c.stx} is not an equation"
  return (mkAppN pf xs, lhs, rhs, ms ++ xs)

/-- The sampler `F` of a commutation lemma with sides `lhs` and `rhs`, of the form
`μ.bind (fun b => F (k b)) = F (fun a => μ.bind fun b => k b a)`. -/
private def samplerOf? (lhs rhs : Expr) : Option Expr := do
  let some (_, _, _, .lam _ _ body _) := lhs.app4? ``PMF.bind | none
  let .app F _ := body | none
  if F.hasLooseBVars then none
  let .app F' (.lam ..) := rhs | none
  if F' != F then none
  if F.getAppFn.isMVar then none
  return F

/-- Elaborate a commutation lemma for `pmf_swap [h]`. -/
private def elabComm (stx : Syntax) : TacticM Comm := do
  let thm ←
    withTheReader Term.Context (fun ctx => { ctx with ignoreTCFailures := true }) <|
      Term.withoutModifyingElabMetaStateWithInfo <| withRef stx <| Term.withoutErrToSorry do
        abstractMVars (← Term.elabTerm stx none)
  let c : Comm := { thm, stx, key := .const .anonymous, arity := 0 }
  let shape : Option (HeadKey × Nat) ← withNewMCtxDepth do
    let (_, lhs, rhs, _) ← c.inst
    return (samplerOf? lhs rhs).bind fun F => (headKey? F).map (·, F.getAppNumArgs)
  let some (key, arity) := shape
    | throwErrorAt stx "pmf_swap: {stx} is not a commutation lemma for a sampler `F`.\n\
        The expected form is\n  μ.bind (fun b => F (k b)) = F (fun a => μ.bind fun b => k b a)\n\
        for every distribution `μ`."
  return { c with key, arity }

/-- Assign the instance arguments among the metavariables `ms` by type class synthesis. -/
private def synthInstances (ms : Array Expr) : MetaM Unit := do
  for m in ms do
    let m ← instantiateMVars m
    if let .mvar id := m then
      if (← isClass? (← inferType m)).isSome then
        id.assign (← synthInstance (← inferType m))

/-- A distribution or a sampler: the head `head` of a sample, and `comm?` when it is a sampler
`head`, which is applied to the continuation, with the commutation lemma `comm?`. -/
private structure Pat where
  /-- The distribution, or the sampler. -/
  head : Expr
  /-- The commutation lemma of a sampler. -/
  comm? : Option Comm := none

/-- A step of a chain of samples: the distribution or sampler `head` and the continuation `cont`,
so that the chain is `head.bind cont`, or `head cont` for a sampler. -/
private structure Sample extends Pat where
  /-- The rest of the chain, as a function of the sample. -/
  cont : Expr

/-- `e` as an application `F k` of the sampler `F` of one of the commutation lemmas `comms`. -/
private def customSample? (comms : Array Comm) (e : Expr) : MetaM (Option Sample) := do
  if comms.isEmpty then return none
  let .app F k := e | return none
  let some key := headKey? F | return none
  for c in comms do
    unless c.key == key && c.arity == F.getAppNumArgs do continue
    let ok ← withNewMCtxDepth do
      let (_, _, rhs, _) ← c.inst
      let .app F' _ := rhs | return false
      withReducible <| isDefEq F' F
    if ok then return some { head := F, comm? := some c, cont := k }
  return none

/-- The first sample of `e`: `p.bind f` samples `p` and continues with `f`, `p.map g`, which
is `p.bind (pure ∘ g)`, samples `p` and returns `g` of the sample, and `F k`, for the sampler `F`
of one of the commutation lemmas `comms`, samples `F` and continues with `k`. -/
private def sample? (comms : Array Comm) (e : Expr) : MetaM (Option Sample) := do
  match_expr e with
  | PMF.bind _ _ p f => return some { head := p, cont := f }
  | PMF.map α _ g p =>
    let n := if let .lam m .. := g then m else `x
    let cont ← withLocalDeclD n α fun x => do
      mkLambdaFVars #[x] (← mkAppM ``PMF.pure #[g.beta #[x]])
    return some { head := p, cont }
  | _ => customSample? comms e

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

/-- The type of the samples of `p`: the outcomes of a distribution, or the argument of the
continuation of a sampler. -/
private def Pat.sampleType (p : Pat) : MetaM Expr := do
  if p.comm?.isNone then return ← outcomeType p.head
  let .forallE _ kTy _ _ ← whnf (← inferType p.head)
    | throwError "pmf_swap: internal error: a sampler is not a function"
  let .forallE _ α _ _ ← whnf kTy
    | throwError "pmf_swap: internal error: a continuation is not a function"
  return α

/-- The chain that samples `p` and continues with `k`. -/
private def Pat.front (p : Pat) (k : Expr) : MetaM Expr :=
  if p.comm?.isSome then return mkApp p.head k else mkAppM ``PMF.bind #[p.head, k]

/-- `p.front f = p.front g` from `h : f = g`. -/
private def stepCongr (p : Pat) (f h : Expr) : MetaM Expr := do
  let F ← withLocalDeclD `k (← inferType f) fun k => do mkLambdaFVars #[k] (← p.front k)
  mkCongrArg F h

/-- Whether `p` and `q` sample the same distribution, or the same sampler, up to reducible
unfolding. -/
private def sameHead (p q : Pat) : MetaM Bool := do
  if p.comm?.isSome != q.comm?.isSome then return false
  withNewMCtxDepth <| withReducible <| isDefEq p.head q.head

/-- The depths at which the chain `e` samples `q`, up to reducible unfolding. A sample whose
distribution mentions an earlier sample is not equal to `q`, which is closed. A sampler does not
move past another sampler, so the search for a sampler `q` stops at the first sampler. -/
private partial def findDepths (comms : Array Comm) (q : Pat) (e : Expr) (depth : Nat := 0) :
    MetaM (Array Nat) := do
  let some s ← sample? comms e | return #[]
  let here ← sameHead s.toPat q
  if q.comm?.isSome && s.comm?.isSome then return if here then #[depth] else #[]
  let rest ← withBody s.cont fun _ body => findDepths comms q body (depth + 1)
  return if here then #[depth] ++ rest else rest

/-- The first depth at which the chain `e` samples a distribution reducibly equal to `q`, assigning
the metavariables of `q`. -/
private partial def firstDepth? (q e : Expr) (depth : Nat := 0) : MetaM (Option Nat) := do
  let some s ← sample? #[] e | return none
  if ← withReducible <| isDefEq s.head q then return some depth
  withBody s.cont fun _ body => firstDepth? q body (depth + 1)

/-- A proof that the commutation lemma of `c` gives `lhs = rhs`. -/
private def commProof (c : Comm) (lhs rhs : Expr) : MetaM Expr := do
  let (pf, l, r, ms) ← c.inst
  unless ← isDefEq l lhs <&&> isDefEq r rhs do
    throwError "pmf_swap: {c.stx} does not prove{indentExpr (← mkEq lhs rhs)}"
  synthInstances ms
  let pf ← instantiateMVars pf
  if pf.hasExprMVar then
    throwError "pmf_swap: {c.stx} does not determine all of its arguments in{indentExpr lhs}"
  return pf

/-- A proof of `lhs = rhs`, where `lhs` samples `p` and then `q`, and `rhs` samples `q` and then
`p`, with the continuation `G` of both: `PMF.bind_comm` for two distributions, and the commutation
lemma for a sampler. -/
private def swapProof (p q : Pat) (G lhs rhs : Expr) : MetaM Expr :=
  match p.comm?, q.comm? with
  | none, none => mkAppM ``PMF.bind_comm #[p.head, q.head, G]
  | none, some c => commProof c lhs rhs
  | some c, none => do mkEqSymm (← commProof c rhs lhs)
  | some _, some _ => throwError "pmf_swap: internal error: two samplers do not commute"

/-- Move the sample at depth `k` of the chain `e`, which samples `q` independently of the earlier
samples, to the front. Returns `q.front g` and a proof of `e = q.front g`. -/
private partial def hoistAt (comms : Array Comm) (q : Pat) (e : Expr) :
    Nat → MetaM (Expr × Expr)
  | 0 => do
    let some s ← sample? comms e | throwError "pmf_swap: internal error: no sample to move"
    let e' ← q.front s.cont
    return (e', ← mkExpectedTypeHint (← mkEqRefl e) (← mkEq e e'))
  | k + 1 => do
    let some s ← sample? comms e | throwError "pmf_swap: internal error: no sample to move"
    let p := s.toPat
    -- Inside the continuation, `fun x => q.front (G x)`.
    let (hcont, G) ← withBody s.cont fun x body => do
      let (inner, h) ← hoistAt comms q body k
      return (← mkLambdaFVars #[x] h, ← mkLambdaFVars #[x] inner.appArg!)
    let h₁ ← stepCongr p s.cont (← mkFunExt hcont)
    let .forallE xName xTy _ _ ← whnf (← inferType s.cont)
      | throwError "pmf_swap: internal error: continuation is not a function"
    let xName := if let .lam m .. := s.cont then m else xName
    let yName ← withBody s.cont fun x _ => do
      return if let .lam n .. := G.beta #[x] then n else `y
    let lhs ← p.front (← withLocalDeclD xName xTy fun x => do
      mkLambdaFVars #[x] (← q.front (G.beta #[x])))
    let e' ← q.front (← withLocalDeclD yName (← q.sampleType) fun y => do
      let pCont ← withLocalDeclD xName xTy fun x => do mkLambdaFVars #[x] (G.beta #[x, y])
      mkLambdaFVars #[y] (← p.front pCont))
    -- `p` then `q` is `q` then `p`.
    let h₂ ← swapProof p q G lhs e'
    return (e', ← mkExpectedTypeHint (← mkEqTrans h₁ h₂) (← mkEq e e'))

/-- An alignment of `lhs = rhs`: a sample `q` drawn independently at depth `kl` of `lhs` and at
depth `kr` of `rhs`. -/
private abbrev Alignment := Pat × Nat × Nat

/-- The ways to bring one sample to the front of both sides of `lhs = rhs`: the first sample of
`rhs` matched with each of its occurrences in `lhs`, and failing that the first sample of `lhs`
matched with each of its occurrences in `rhs`. Every proof by reordering matches the first sample
of `rhs` with some sample of `lhs`, so `search` loses nothing by trying only these. -/
private def alignments (comms : Array Comm) (lhs rhs : Expr) : MetaM (Array Alignment) := do
  if let some s ← sample? comms rhs then
    let ks ← findDepths comms s.toPat lhs
    unless ks.isEmpty do return ks.map ((s.toPat, ·, 0))
  if let some s ← sample? comms lhs then
    return (← findDepths comms s.toPat rhs).map ((s.toPat, 0, ·))
  return #[]

/-- The samples of the chain `e` that do not depend on earlier samples. -/
private partial def independentHeads (comms : Array Comm) (e : Expr) (earlier : Array Expr := #[]) :
    MetaM (Array Pat) := do
  let some s ← sample? comms e | return #[]
  let dep := earlier.any fun x => s.head.containsFVar x.fvarId!
  let rest ← withBody s.cont fun x body => independentHeads comms body (earlier.push x)
  return if dep then rest else #[s.toPat] ++ rest

/-- A forced alignment of `lhs = rhs`: a sample of `rhs` whose distribution occurs exactly once on
each side, so that it has a single possible partner. -/
private def forced? (comms : Array Comm) (lhs rhs : Expr) : MetaM (Option Alignment) := do
  for q in ← independentHeads comms rhs do
    let kls ← findDepths comms q lhs
    let krs ← findDepths comms q rhs
    if let (#[kl], #[kr]) := (kls, krs) then return some (q, kl, kr)
  return none

/-- Carry out an alignment `(q, kl, kr)` of `lhs = rhs`: the continuations `f` and `g` and proofs
of `lhs = q.front f` and `rhs = q.front g`. -/
private def realize (comms : Array Comm) (lhs rhs : Expr) :
    Alignment → MetaM (Pat × Expr × Expr × Expr × Expr)
  | (q, kl, kr) => do
    let (lhs', hl) ← hoistAt comms q lhs kl
    let (rhs', hr) ← hoistAt comms q rhs kr
    return (q, lhs'.appArg!, rhs'.appArg!, hl, hr)

/-- A proof of `lhs = rhs` from `hl : lhs = q.front f`, `hr : rhs = q.front g` and `h : f = g`. -/
private def combine (lhs rhs : Expr) (q : Pat) (f hl hr h : Expr) : MetaM Expr := do
  let hmid ← stepCongr q f h
  let pf ← mkEqTrans (← mkEqTrans hl hmid) (← mkEqSymm hr)
  mkExpectedTypeHint pf (← mkEq lhs rhs)

/-- The number of steps of `search` for the goal and again after each forced alignment. -/
private def searchBudget : Nat := 256

/-- Search for a proof of `lhs = rhs` that aligns the samples of the two sides until the remaining
continuations are reducibly equal, trying every matching sample of the other side. Each call
spends one unit of `fuel`; when `fuel` reaches zero the search gives up, so `none` with no fuel
left means that the budget ran out, not that no matching exists. An alignment that a commutation
lemma does not prove is skipped. -/
private partial def search (comms : Array Comm) (fuel : IO.Ref Nat) (lhs rhs : Expr) :
    MetaM (Option Expr) := do
  if (← fuel.get) == 0 then return none
  fuel.modify (· - 1)
  if ← withNewMCtxDepth <| withReducible <| isDefEq lhs rhs then
    return some (← mkExpectedTypeHint (← mkEqRefl lhs) (← mkEq lhs rhs))
  for a in ← alignments comms lhs rhs do
    let some (q, f, g, hl, hr) ←
        if comms.isEmpty then some <$> realize comms lhs rhs a
        else observing? (realize comms lhs rhs a) | continue
    let h? ← withBody f fun x fx => do
      let some h ← search comms fuel fx (g.beta #[x]) | return none
      return some (← mkLambdaFVars #[x] h)
    if let some h := h? then
      return some (← combine lhs rhs q f hl hr (← mkFunExt h))
  return none

/-- Strip one common sample from both sides of the goal `lhs = rhs` and introduce it as an
inaccessible variable. A forced alignment comes first; otherwise, unless `forcedOnly`, the first
sample of `rhs` that `lhs` also draws. Returns the variable, its depth in `rhs` and the new goal,
or `none` when no sample can be aligned. -/
private def peel? (comms : Array Comm) (goal : MVarId) (forcedOnly := false) :
    MetaM (Option (FVarId × Nat × MVarId)) :=
  goal.withContext do
    let some (_, lhs, rhs) := (← instantiateMVars (← goal.getType)).cleanupAnnotations.eq?
      | return none
    let some a ← (do
        if let some a ← forced? comms lhs rhs then return some a
        if forcedOnly then return none
        return (← alignments comms lhs rhs)[0]?) | return none
    let (q, f, g, hl, hr) ← realize comms lhs rhs a
    let ty ← withBody f fun x fx => do mkForallFVars #[x] (← mkEq fx (g.beta #[x]))
    let m ← mkFreshExprSyntheticOpaqueMVar ty (← goal.getTag)
    goal.assign (← combine lhs rhs q f hl hr (← mkFunExt m))
    let (x, goal') ← m.mvarId!.intro1
    return some (x, a.2.2, goal')

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
private partial def closeGo (comms : Array Comm) (g : MVarId) : MetaM Closed := g.withContext do
  let some (_, lhs, rhs) := (← instantiateMVars (← g.getType)).cleanupAnnotations.eq?
    | return .noMatching
  let fuel ← IO.mkRef searchBudget
  if let some pf ← search comms fuel lhs rhs then
    g.assign pf
    return .closed
  if (← fuel.get) != 0 then return .noMatching
  let some (_, _, g') ← peel? comms g (forcedOnly := true) | return .outOfBudget
  closeGo comms g'

/-- Close the goal by `search`, as `closeGo`, assigning it only when it is closed. -/
private def close (comms : Array Comm) (goal : MVarId) : MetaM Closed := do
  let s ← saveState
  let r ← closeGo comms goal
  unless r matches .closed do s.restore
  return r

/-- The samples of the chain `e`, each marked when it depends on an earlier sample. -/
private partial def chainMsgs (comms : Array Comm) (e : Expr) (earlier : Array Expr := #[]) :
    MetaM (Array MessageData) := do
  let some s ← sample? comms e | return #[]
  let dep := earlier.any fun x => s.head.containsFVar x.fvarId!
  let msg ← addMessageContext
    m!"{s.head}{if dep then " (depends on an earlier sample)" else ""}"
  let rest ← withBody s.cont fun x body => chainMsgs comms body (earlier.push x)
  return #[msg] ++ rest

/-- The error when `pmf_swap` can strip no sample from `lhs = rhs`. -/
private def noCommonSample (comms : Array Comm) (lhs rhs : Expr) : MetaM MessageData := do
  let ls ← chainMsgs comms lhs
  let rs ← chainMsgs comms rhs
  if ls.isEmpty || rs.isEmpty then
    return m!"pmf_swap: both sides must be chains of `PMF.bind`; normalize them with \
      `simp only [pmf_norm]` first.\nLeft side:{indentExpr lhs}\nRight side:{indentExpr rhs}"
  let list (ms : Array MessageData) := indentD (MessageData.joinSep ms.toList Format.line)
  return m!"pmf_swap: the two sides have no independent sample in common.\n\
    Left side samples:{list ls}\nRight side samples:{list rs}\n\
    A sample can move to the front only when its distribution does not depend on earlier samples."

/-- The position in the original right side of the sample at depth `k` of the right side after
the samples at the positions `stripped` have been removed. -/
private def origPos (stripped : Array Nat) (k : Nat) : Nat := Id.run do
  let mut seen := 0
  for i in [0:k + stripped.size + 1] do
    if stripped.contains i then continue
    if seen == k then return i
    seen := seen + 1
  return k + stripped.size

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
the first match of each remaining sample of the right side, and fails when it can strip none. It
closes the remaining equation when `rfl` proves it.

`pmf_swap with x y` skips the search and strips exactly two samples in the same way, and fails if
it cannot. The names follow the order of the samples in the right side, whatever order they are
stripped in: on `(p.bind fun a => q.bind fun b => f a b) = q.bind fun b => p.bind fun a => g a b`,
`pmf_swap with y x` leaves `f x y = g x y`. The remaining equation is left as it is.

`pmf_swap [h₁, h₂]` also moves samples past a sampler `F`, a function of a continuation such as
`Game.runStatelessOracle o prog`, given commutation lemmas of the form
`h : μ.bind (fun b => F (k b)) = F (fun a => μ.bind fun b => k b a)` for every distribution `μ`.
An application `F k` is then a sample of `F` with continuation `k`. Two samplers do not move past
each other. -/
syntax (name := pmfSwap) "pmf_swap" (" [" term,* "]")? (" with" (ppSpace colGt binderIdent)+)? :
  tactic

@[inherit_doc pmfSwap]
elab_rules : tactic
  | `(tactic| pmf_swap $[[$hs,*]]? $[with $xs*]?) => do
    let comms ← ((hs.map (·.getElems)).getD #[]).mapM fun h => elabComm h
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
        match ← close comms goal with
        | .closed => replaceMainGoal []; return
        | .outOfBudget => throwError "pmf_swap: the search for an order of the samples ran out \
            of its budget of {searchBudget} steps.\nStrip samples with `pmf_swap with x …`, or \
            reorder them with `pmf_hoist` or `PMF.bind_comm`, to leave fewer samples to match."
        | .noMatching => pure ()
      let mut g := goal
      -- The stripped samples and their positions in the original right side.
      let mut stripped : Array (FVarId × Nat) := #[]
      repeat
        if !names.isEmpty && stripped.size == names.size then break
        let some (x, kr, g') ← peel? comms g | break
        stripped := stripped.push (x, origPos (stripped.map (·.2)) kr)
        g := g'
      if stripped.isEmpty then throwError (← noCommonSample comms lhs rhs)
      for (x, _) in stripped.qsort (·.2 < ·.2), n? in names do
        if let some n := n? then g ← g.rename x n
      if stripped.size < names.size then
        g.withContext do
          throwError "pmf_swap: only {stripped.size} of the {names.size} named samples can be \
            stripped; what remains is{indentExpr (← instantiateMVars (← g.getType))}"
      if names.isEmpty then
        let s ← saveState
        try
          g.refl
          replaceMainGoal []
          return
        catch _ => s.restore
      replaceMainGoal [g]

/-- An occurrence `(occ := n)` of a distribution, counted from 1. -/
syntax pmfHoistOcc := atomic("(" &"occ") " := " num ")"

/-- `pmf_hoist q` moves every sample of the distribution `q`, in every chain of `PMF.bind` in the
goal, as far toward the front of its chain as possible, by `PMF.bind_comm`: past every earlier
sample, which `q` cannot depend on. `q` may contain holes `_`, which are filled by its first match.
Like `rw`, it then closes a goal that has become reflexive. `pmf_hoist q at h` works on the
hypothesis `h` instead. It fails when no sample of `q` moves.

`pmf_hoist (occ := n) q` moves only the `n`th independent sample of `q`, counting from the front of
each chain and through the chains in the order they occur, the left side of an equation before the
right. When a chain draws `q` twice, it chooses which of the two `pmf_swap` or `congr 1 with x : 1`
then pairs with the first sample of the other side. It fails when that sample is already at the
front of its chain or there are fewer than `n` independent samples of `q`. -/
syntax (name := pmfHoist) "pmf_hoist " (pmfHoistOcc ppSpace)? term
  (Lean.Parser.Tactic.location)? : tactic

@[inherit_doc pmfHoist]
elab_rules : tactic
  | `(tactic| pmf_hoist $[(occ := $n?)]? $qStx $[$loc]?) => withMainContext do
    let occ? := n?.map (·.getNat)
    if occ? == some 0 then throwError "pmf_hoist: occurrences are counted from 1"
    let q ← instantiateMVars (← elabTerm qStx none (mayPostpone := true))
    discard <| outcomeType q
    let hoisted ← IO.mkRef false
    -- With `occ`, the number of independent samples of `q` in the chains visited so far.
    let seen ← IO.mkRef 0
    let methods : Simp.Methods := {
      pre := fun e => do
        if occ?.isSome && (← hoisted.get) then return .done { expr := e }
        let some k ← firstDepth? q e | return .continue
        let q ← instantiateMVars q
        let mut k := k
        if let some n := occ? then
          -- Count the samples of the whole chain here, and do not visit its subchains again.
          let ks ← findDepths #[] { head := q } e
          if ks.isEmpty then return .continue
          let before ← seen.get
          seen.set (before + ks.size)
          if before + ks.size < n then return .done { expr := e }
          k := ks[n - 1 - before]!
          if k == 0 then
            throwError "pmf_hoist: sample {n} of{indentExpr q}\nis already at the front of its \
              chain"
        if k == 0 then return .continue
        let (e', pf) ← hoistAt #[] { head := q } e k
        hoisted.set true
        let r : Simp.Result := { expr := e', proof? := some pf }
        return if occ?.isSome then .done r else .visit r }
    -- With `occ`, equal subterms are distinct occurrences, so simp must not memoize.
    let ctx ← Simp.mkContext
      { zeta := false, iota := false, proj := false, memoize := occ?.isNone }
    let run (e : Expr) : MetaM Simp.Result := do
      hoisted.set false
      seen.set 0
      let (r, _) ← Simp.main e ctx (methods := methods)
      unless ← hoisted.get do
        let q ← instantiateMVars q
        if let some n := occ? then
          throwError "pmf_hoist: there is no sample {n} of{indentExpr q}\n\
            the chains draw it independently {← seen.get} times"
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
