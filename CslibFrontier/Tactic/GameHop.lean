/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.Encryption.Basic
public import CslibFrontier.Crypto.Game.CloseTo
public import CslibFrontier.Crypto.Game.Order
public import CslibFrontier.Crypto.Game.UntilBad
public import CslibFrontier.Languages.Probabilistic.Norm
public import CslibFrontier.Probability.PMF.Bind
public meta import Lean.Elab.Tactic

/-!
# Tactics for cryptographic game hops and shared random draws

Cryptographic security proofs repeatedly step across explicit sequences of hybrid games and couple
shared leading `PMF.bind` (or `Game.runStatelessOracle`) stages while retaining support membership.
This module provides two focused, deterministic tactics that keep intermediate games and variable
couplings explicit in the proof script while removing routine triangle, symmetry, coercion, and
bind-coupling plumbing:

* `game_trans`: split a distinguishing-advantage, success-probability, or `CloseTo` bound along an
  explicit list of intermediate games or distributions, with optional `using [...]` hop discharge
  handling symmetry (`Game.advantage_comm`, `CloseTo.symm`), equality (`Game.advantage_self`,
  `CloseTo.refl`), and `ℝ≥0 → ℝ` coercion.
* `peel_binds`: normalize outer `ProbComp.eval` monadic binds at the head and peel shared leading
  `PMF.bind` and `Game.runStatelessOracle` stages on `Game.advantage`, `CloseTo`, or `PMF` equality
  goals, introducing each draw `x` together with `x_mem : x ∈ μ.support` and performing a one-step
  independent `PMF.bind_comm` / `Game.bind_runStatelessOracle_comm` / `Game.runStatelessOracle_comm`
  swap when the leading draw matches the opposite side's second draw.

## Main definitions

* `game_trans`: chain game-hop bounds across explicit intermediate games or distributions.
* `peel_binds`: peel coupled leading `PMF.bind` and `Game.runStatelessOracle` stages with support
  hypotheses.

## Main results

* `Cslib.Crypto.Game.coe_advantage_triangle_add`: real-valued triangle step combining two hop
  bounds.
* `Cslib.Crypto.Game.succProbability_le_of_advantage_pure_false_le`,
  `Cslib.Crypto.Game.coe_succProbability_le_of_advantage_pure_false_le`: bridge lemmas reducing
  one-sided `Game.succProbability` bounds to `Game.advantage · (PMF.pure false)`.
* `Cslib.Crypto.Game.coe_advantage_bind_le_of_support`,
  `Cslib.Crypto.Game.coe_advantage_runStatelessOracle_le_of_support`,
  `Cslib.Crypto.Game.closeTo_runStatelessOracle`,
  `Cslib.Crypto.Game.runStatelessOracle_congr_on_support`,
  `Cslib.Crypto.Game.runStatelessOracle_comm`: support-restricted and commutation bridge lemmas for
  `ℝ`-valued `Game.advantage`, `CloseTo`, and `Game.runStatelessOracle`.
-/

public section

namespace Cslib.Crypto.Game

open Probability
open scoped ENNReal NNReal

/-- Combine two real-valued game-hop bounds across an intermediate game. -/
theorem coe_advantage_triangle_add (g₀ g₁ g₂ : Game) {ε₁ ε₂ : ℝ}
    (h₁ : (advantage g₀ g₁ : ℝ) ≤ ε₁) (h₂ : (advantage g₁ g₂ : ℝ) ≤ ε₂) :
    (advantage g₀ g₂ : ℝ) ≤ ε₁ + ε₂ := by
  have htri := NNReal.coe_le_coe.mpr (advantage_triangle g₀ g₁ g₂)
  rw [NNReal.coe_add] at htri
  exact htri.trans (add_le_add h₁ h₂)

/-- Bounding `advantage g₀ (PMF.pure false) ≤ B` bounds `succProbability g₀ ≤ B`. -/
theorem succProbability_le_of_advantage_pure_false_le {g₀ : Game} {B : ℝ≥0}
    (h : advantage g₀ (PMF.pure false) ≤ B) :
    succProbability g₀ ≤ B :=
  (advantage_pure_false g₀) ▸ h

/-- Real-valued version of `succProbability_le_of_advantage_pure_false_le`. -/
theorem coe_succProbability_le_of_advantage_pure_false_le {g₀ : Game} {B : ℝ}
    (h : (advantage g₀ (PMF.pure false) : ℝ) ≤ B) :
    (succProbability g₀ : ℝ) ≤ B :=
  (congrArg NNReal.toReal (advantage_pure_false g₀)) ▸ h

/-- Support-restricted real-valued `PMF.bind` advantage bound. -/
theorem coe_advantage_bind_le_of_support {α : Type*} (μ : PMF α) (game1 game2 : α → Game)
    {ε : ℝ} (h : ∀ a ∈ μ.support, (advantage (game1 a) (game2 a) : ℝ) ≤ ε) :
    (advantage (μ.bind game1) (μ.bind game2) : ℝ) ≤ ε := by
  obtain ⟨a₀, ha₀⟩ := μ.support_nonempty
  let ε' : ℝ≥0 := ⟨ε, (NNReal.coe_nonneg _).trans (h a₀ ha₀)⟩
  exact NNReal.coe_le_coe.mpr
    (advantage_bind_le_of_support μ game1 game2 (ε := ε') fun a ha => h a ha)

/-- Support-restricted real-valued continuation bound for `runStatelessOracle`. -/
theorem coe_advantage_runStatelessOracle_le_of_support {α : Type}
    (o : List Bool → List Bool) (prog : WordOracleComp Unit α)
    (next₁ next₂ : α → Game) {ε : ℝ}
    (h : ∀ out ∈ (ProbComp.eval
      ((prog.runState fun req (s : Unit) => pure (o req.2, s)).run ())).support,
      (advantage (next₁ out.1) (next₂ out.1) : ℝ) ≤ ε) :
    (advantage (runStatelessOracle o prog next₁) (runStatelessOracle o prog next₂) : ℝ) ≤ ε :=
  coe_advantage_bind_le_of_support _ _ _ h

/-- Support-restricted `CloseTo` continuation bound for `runStatelessOracle`. -/
theorem closeTo_runStatelessOracle {α : Type}
    (o : List Bool → List Bool) (prog : WordOracleComp Unit α)
    (next₁ next₂ : α → Game) {ε : ℝ≥0∞}
    (h : ∀ out ∈ (ProbComp.eval
      ((prog.runState fun req (s : Unit) => pure (o req.2, s)).run ())).support,
      CloseTo (next₁ out.1) (next₂ out.1) ε) :
    CloseTo (runStatelessOracle o prog next₁) (runStatelessOracle o prog next₂) ε :=
  CloseTo.bind_right _ h

/-- Support-restricted continuation congruence for `runStatelessOracle`. -/
theorem runStatelessOracle_congr_on_support {α : Type}
    (o : List Bool → List Bool) (prog : WordOracleComp Unit α)
    (next₁ next₂ : α → Game)
    (h : ∀ out ∈ (ProbComp.eval
      ((prog.runState fun req (s : Unit) => pure (o req.2, s)).run ())).support,
      next₁ out.1 = next₂ out.1) :
    runStatelessOracle o prog next₁ = runStatelessOracle o prog next₂ :=
  Cslib.Probability.PMF.bind_congr_on_support _ _ _ h

/-- Commute two independent `runStatelessOracle` stages. -/
theorem runStatelessOracle_comm {α β : Type}
    (o₁ : List Bool → List Bool) (prog₁ : WordOracleComp Unit α)
    (o₂ : List Bool → List Bool) (prog₂ : WordOracleComp Unit β)
    (next : α → β → Game) :
    runStatelessOracle o₁ prog₁ (fun a => runStatelessOracle o₂ prog₂ (next a)) =
      runStatelessOracle o₂ prog₂ (fun b => runStatelessOracle o₁ prog₁ (fun a => next a b)) := by
  unfold runStatelessOracle
  exact PMF.bind_comm _ _ _

end Cslib.Crypto.Game

namespace Cslib.Tactic.GameHop

open Lean Meta Elab Tactic
open Cslib.Crypto Cslib.Probability

/-! ### Expression inspection and head normalization helpers -/

/-- Head-beta-reduce and substitute top-level `let` bindings (and local `let` `fvar`s of
`PMF`/`Game` type) at the root of `e` (definitionally equal by `beta`/`zeta`/`zetaDelta`). -/
private meta partial def stripSpineLetsM (e : Expr) : MetaM Expr := do
  match e.cleanupAnnotations.headBeta with
  | .letE _ _ val body _ => stripSpineLetsM (body.instantiate1 val)
  | .fvar fvarId =>
    let decl ← fvarId.getDecl
    if let some val := decl.value? then
      if (← whnfR decl.type).isAppOf ``PMF then
        return ← stripSpineLetsM val
    return e.cleanupAnnotations.headBeta
  | e' => return e'

/-- Cast a proof `h : a' = b'` to `a = b` when `a ≡ a'` and `b ≡ b'` definitionally. -/
private meta def castEqProof (a b h : Expr) : MetaM Expr := do
  mkExpectedTypeHint h (← mkEq a b)

/-- Compose optional equality proofs `e₀ = e₁` and `e₁ = e₂`. -/
private meta def chainEqOpt (e₀ e₂ : Expr) (h₁? h₂? : Option Expr) : MetaM (Option Expr) := do
  match h₁?, h₂? with
  | none, none => return none
  | some h₁, none => return some (← castEqProof e₀ e₂ h₁)
  | none, some h₂ => return some (← castEqProof e₀ e₂ h₂)
  | some h₁, some h₂ => return some (← castEqProof e₀ e₂ (← mkEqTrans h₁ h₂))

/-- Normalize only the outer head of a `PMF` expression into `PMF.bind` or `runStatelessOracle`
without unfolding named user definitions or traversing continuation bodies. -/
private meta partial def normalizeBindHead (e : Expr) : MetaM (Expr × Option Expr) := do
  let e0 ← stripSpineLetsM e
  if e0.isAppOfArity ``Bind.bind 6 then
    let args := e0.getAppArgs
    if args[0]!.cleanupAnnotations.isConstOf ``PMF then
      let eBind ← mkAppM ``PMF.bind #[args[4]!, args[5]!]
      let (eFinal, h?) ← normalizeBindHead eBind
      let h? ← match h? with
        | some h => pure (some (← castEqProof e eFinal h))
        | none =>
          if e == eFinal then pure none
          else pure (some (← castEqProof e eFinal (← mkEqRefl eFinal)))
      return (eFinal, h?)
  if e0.isAppOfArity ``Cslib.ProbComp.eval 2 then
    let prog0 ← stripSpineLetsM (e0.getAppArgs[1]!)
    if prog0.isAppOfArity ``Bind.bind 6 then
      let pargs := prog0.getAppArgs
      let m := pargs[4]!
      let k := pargs[5]!
      let hStep ← mkAppM ``Cslib.ProbComp.eval_bind #[m, k]
      let xName := match k.cleanupAnnotations with
        | .lam n _ _ _ => n
        | _ => `x
      let α₀ := pargs[2]!
      let evalM ← mkAppM ``Cslib.ProbComp.eval #[m]
      let newLam ← withLocalDecl xName .default α₀ fun x => do
        let kx := (mkApp k x).headBeta
        let evalKx ← mkAppM ``Cslib.ProbComp.eval #[kx]
        mkLambdaFVars #[x] evalKx
      let rhs ← mkAppM ``PMF.bind #[evalM, newLam]
      let hStep ← castEqProof e rhs hStep
      let (eFinal, hRest?) ← normalizeBindHead rhs
      return (eFinal, ← chainEqOpt e eFinal (some hStep) hRest?)
    return (e, none)
  if e0.isAppOfArity ``PMF.bind 4 then
    let args := e0.getAppArgs
    let p := args[2]!
    let f := args[3]!
    let (p', hp?) ← normalizeBindHead p
    let mut cur := e0
    let mut hCur? : Option Expr := none
    if let some hp := hp? then
      let cur' ← mkAppM ``PMF.bind #[p', f]
      let hCongr ← mkCongrArg (mkApp2 e0.getAppFn args[0]! args[1]!) hp
      let hStep ← mkCongrFun hCongr f
      hCur? := some (← castEqProof e cur' hStep)
      cur := cur'
    let p0 ← stripSpineLetsM p'
    if p0.isAppOfArity ``PMF.bind 4 then
      let pargs := p0.getAppArgs
      let q := pargs[2]!
      let g := pargs[3]!
      let hAssoc ← mkAppM ``PMF.bind_bind #[q, g, f]
      -- Preserve `g`'s user binder name in the reassociated lambda.
      let xName := match g.cleanupAnnotations with
        | .lam n _ _ _ => n
        | _ => `x
      let α₀ := pargs[0]!
      let newLam ← withLocalDecl xName .default α₀ fun x => do
        let gx := (mkApp g x).headBeta
        let inner ← mkAppM ``PMF.bind #[gx, f]
        mkLambdaFVars #[x] inner
      let rhs ← mkAppM ``PMF.bind #[q, newLam]
      let hAssoc ← castEqProof cur rhs hAssoc
      let hTot? ← chainEqOpt e rhs hCur? (some hAssoc)
      let (eFinal, hRest?) ← normalizeBindHead rhs
      return (eFinal, ← chainEqOpt e eFinal hTot? hRest?)
    if p0.isAppOfArity ``PMF.pure 2 then
      let a := p0.getAppArgs[1]!
      let hPure ← mkAppM ``PMF.pure_bind #[a, f]
      let rhs := (mkApp f a).headBeta
      let hPure ← castEqProof cur rhs hPure
      let hTot? ← chainEqOpt e rhs hCur? (some hPure)
      let (eFinal, hRest?) ← normalizeBindHead rhs
      return (eFinal, ← chainEqOpt e eFinal hTot? hRest?)
    if p0.isAppOfArity ``PMF.map 4 then
      let margs := p0.getAppArgs
      let α₀ := margs[0]!
      let g := margs[2]!
      let q := margs[3]!
      let hMap ← mkAppM ``PMF.bind_map #[q, g, f]
      let xName := match g.cleanupAnnotations with
        | .lam n _ _ _ => n
        | _ => match f.cleanupAnnotations with
          | .lam n _ _ _ => n
          | _ => `x
      let compName := if xName.isAnonymous then `x else xName
      let newLam ← withLocalDecl compName .default α₀ fun x => do
        let gx := (mkApp g x).headBeta
        let fgx := (mkApp f gx).headBeta
        mkLambdaFVars #[x] fgx
      let rhs ← mkAppM ``PMF.bind #[q, newLam]
      let hMap ← castEqProof cur rhs hMap
      let hTot? ← chainEqOpt e rhs hCur? (some hMap)
      let (eFinal, hRest?) ← normalizeBindHead rhs
      return (eFinal, ← chainEqOpt e eFinal hTot? hRest?)
    if p0.isAppOfArity ``Cslib.ProbComp.eval 2 then
      let innerProg ← stripSpineLetsM (p0.getAppArgs[1]!)
      if innerProg.isAppOfArity ``Functor.map 6 then
        let fargs := innerProg.getAppArgs
        let g := fargs[4]!
        let m := fargs[5]!
        let hEvalMap ← mkAppM ``Cslib.ProbComp.eval_map #[g, m]
        let mapped := (← inferType hEvalMap).getAppArgs[2]!
        let curMapped ← mkAppM ``PMF.bind #[mapped, f]
        let hCongr ← mkCongrFun (← mkCongrArg (mkApp2 cur.getAppFn args[0]! args[1]!)
          (← castEqProof p' mapped hEvalMap)) f
        let h1? ← chainEqOpt e curMapped hCur? (some hCongr)
        let (eFinal, hRest?) ← normalizeBindHead curMapped
        return (eFinal, ← chainEqOpt e eFinal h1? hRest?)
      if innerProg.isAppOfArity ``Pure.pure 4 then
        let a := innerProg.getAppArgs[3]!
        let hEvalPure ← mkAppM ``Cslib.ProbComp.eval_pure #[a]
        let pured := (← inferType hEvalPure).getAppArgs[2]!
        let curPured ← mkAppM ``PMF.bind #[pured, f]
        let hCongr ← mkCongrFun (← mkCongrArg (mkApp2 cur.getAppFn args[0]! args[1]!)
          (← castEqProof p' pured hEvalPure)) f
        let h1? ← chainEqOpt e curPured hCur? (some hCongr)
        let (eFinal, hRest?) ← normalizeBindHead curPured
        return (eFinal, ← chainEqOpt e eFinal h1? hRest?)
    if cur != e && hCur?.isNone then
      return (cur, some (← castEqProof e cur (← mkEqRefl cur)))
    return (cur, hCur?)
  if e0.isAppOfArity ``Game.runStatelessOracle 4 then
    if e0 != e then
      return (e0, some (← castEqProof e e0 (← mkEqRefl e0)))
    return (e, none)
  return (e, none)

/-! ### Bind-stage representation and adjacent-stage commutation -/

private inductive StageHead where
  | pmfBind (α β μ : Expr)
  | statelessOracle (α o prog : Expr)

private structure ParsedStage where
  head : StageHead
  binderType : Expr
  binderName : Name
  cont : Expr

private meta def parseStage? (e : Expr) : MetaM (Option ParsedStage) := do
  let e0 ← stripSpineLetsM e
  if e0.isAppOfArity ``PMF.bind 4 then
    let args := e0.getAppArgs
    let α := args[0]!
    let β := args[1]!
    let μ := args[2]!
    let f := args[3]!
    let bName := match f.cleanupAnnotations with
      | .lam n _ _ _ => n
      | _ => .anonymous
    return some { head := .pmfBind α β μ, binderType := α, binderName := bName, cont := f }
  if e0.isAppOfArity ``Bind.bind 6 then
    let args := e0.getAppArgs
    if args[0]!.cleanupAnnotations.isConstOf ``PMF then
      let α := args[2]!
      let β := args[3]!
      let μ := args[4]!
      let f := args[5]!
      let bName := match f.cleanupAnnotations with
        | .lam n _ _ _ => n
        | _ => .anonymous
      return some { head := .pmfBind α β μ, binderType := α, binderName := bName, cont := f }
  if e0.isAppOfArity ``Game.runStatelessOracle 4 then
    let args := e0.getAppArgs
    let α := args[0]!
    let o := args[1]!
    let prog := args[2]!
    let next := args[3]!
    let bName := match next.cleanupAnnotations with
      | .lam n _ _ _ => n
      | _ => .anonymous
    return some { head := .statelessOracle α o prog, binderType := α, binderName := bName,
                  cont := next }
  return none

private meta def StageHead.mentionsFVar (h : StageHead) (fvarId : FVarId) : Bool :=
  match h with
  | .pmfBind α _ μ => α.containsFVar fvarId || μ.containsFVar fvarId
  | .statelessOracle α o prog =>
    α.containsFVar fvarId || o.containsFVar fvarId || prog.containsFVar fvarId

private meta def mkStageApp (h : StageHead) (lam : Expr) : MetaM Expr :=
  match h with
  | .pmfBind _ _ μ => mkAppM ``PMF.bind #[μ, lam]
  | .statelessOracle _ o prog => mkAppM ``Game.runStatelessOracle #[o, prog, lam]

private meta def mkStagePrefix (h : StageHead) : MetaM Expr := do
  match h with
  | .pmfBind α β μ =>
    mkAppOptM ``PMF.bind #[some α, some β, some μ]
  | .statelessOracle α o prog =>
    mkAppOptM ``Game.runStatelessOracle #[some α, some o, some prog]

/-- Swap two adjacent independent bind stages `s₀` (outer, binder `y`) and `s₁` (inner, binder
`x`), constructing `(swappedExpr, proof : orig = swappedExpr)` and preserving user binder names. -/
private meta def swapAdjacentStages (orig : Expr) (s₀ : ParsedStage) : MetaM (Expr × Expr) := do
  let yName := if s₀.binderName.isAnonymous then `y else s₀.binderName
  withLocalDecl yName .default s₀.binderType fun y => do
    let innerRaw := (mkApp s₀.cont y).headBeta
    let (innerNorm, hNorm?) ← normalizeBindHead innerRaw
    let some s₁ ← parseStage? innerNorm
      | throwError "peel_binds: expected an inner `PMF.bind` or `runStatelessOracle` stage"
    let xName := if s₁.binderName.isAnonymous then `x else s₁.binderName
    if s₁.head.mentionsFVar y.fvarId! then
      throwError "peel_binds: cannot swap `{xName}` past `{yName}` because its distribution \
        depends on `{yName}`"
    let mut curOrig := orig
    let mut hPre? : Option Expr := none
    if let some hN := hNorm? then
      let lamNorm ← mkLambdaFVars #[y] innerNorm
      let midOrig ← mkStageApp s₀.head lamNorm
      let pref₀ ← mkStagePrefix s₀.head
      let hCongr ← mkCongrArg pref₀ (← mkFunExt (← mkLambdaFVars #[y] hN))
      hPre? := some (← castEqProof orig midOrig hCongr)
      curOrig := midOrig
    let f2 ← withLocalDecl xName .default s₁.binderType fun x => do
      let body := (mkApp s₁.cont x).headBeta
      mkLambdaFVars #[y, x] body
    let swappedLam ← withLocalDecl xName .default s₁.binderType fun x => do
      let innerAfter ← withLocalDecl yName .default s₀.binderType fun y' => do
        let b := (f2.beta #[y', x]).headBeta
        mkLambdaFVars #[y'] b
      let wrapped₀ ← mkStageApp s₀.head innerAfter
      mkLambdaFVars #[x] wrapped₀
    let swapped ← mkStageApp s₁.head swappedLam
    let hSwapRaw ← match s₀.head, s₁.head with
      | .pmfBind _ _ μ₀, .pmfBind _ _ μ₁ =>
        mkAppM ``PMF.bind_comm #[μ₀, μ₁, f2]
      | .pmfBind _ _ μ₀, .statelessOracle _ o₁ prog₁ =>
        mkAppM ``Game.bind_runStatelessOracle_comm #[μ₀, o₁, prog₁, f2]
      | .statelessOracle _ o₀ prog₀, .pmfBind _ _ μ₁ =>
        let f2Flip ← withLocalDecl xName .default s₁.binderType fun x =>
          withLocalDecl yName .default s₀.binderType fun y' => do
            mkLambdaFVars #[x, y'] ((f2.beta #[y', x]).headBeta)
        let hSymm ← mkAppM ``Game.bind_runStatelessOracle_comm #[μ₁, o₀, prog₀, f2Flip]
        mkEqSymm hSymm
      | .statelessOracle _ o₀ prog₀, .statelessOracle _ o₁ prog₁ =>
        mkAppM ``Game.runStatelessOracle_comm #[o₀, prog₀, o₁, prog₁, f2]
    let hSwap ← castEqProof curOrig swapped hSwapRaw
    let some hTot ← chainEqOpt orig swapped hPre? (some hSwap)
      | return (swapped, hSwap)
    return (swapped, hTot)

/-! ### Target decomposition for relational PMF / Game goals -/

private structure BinaryPMFTarget where
  lhs : Expr
  rhs : Expr
  /-- Rebuild the proposition with updated `(lhs', rhs')`. -/
  rebuild : Expr → Expr → MetaM Expr

/-- Decompose a proposition into `(L, R, rebuild)` for `Game.advantage`, `Encryption.advantage`,
`CloseTo`, or `PMF` equality. -/
private meta def decomposePMFTarget? (prop : Expr) : MetaM (Option BinaryPMFTarget) := do
  let p0 ← deltaExpand prop (· == ``Cslib.Crypto.Encryption.advantage)
  let p := p0.cleanupAnnotations
  if p.isAppOfArity ``CloseTo 4 then
    let args := p.getAppArgs
    let α := args[0]!
    let L := args[1]!
    let R := args[2]!
    let B := args[3]!
    return some {
      lhs := L
      rhs := R
      rebuild := fun L' R' => mkAppOptM ``CloseTo #[some α, some L', some R', some B]
    }
  if p.isAppOfArity ``Eq 3 then
    let args := p.getAppArgs
    let T := args[0]!
    let L := args[1]!
    let R := args[2]!
    if (← whnfR T).isAppOf ``PMF then
      return some {
        lhs := L
        rhs := R
        rebuild := fun L' R' => mkAppOptM ``Eq #[some T, some L', some R']
      }
  if p.isAppOfArity ``LE.le 4 then
    let args := p.getAppArgs
    let ty := args[0]!
    let inst := args[1]!
    let lhsLe := args[2]!.cleanupAnnotations
    let rhsLe := args[3]!.cleanupAnnotations
    if lhsLe.isAppOfArity ``Game.advantage 2 then
      let aargs := lhsLe.getAppArgs
      return some {
        lhs := aargs[0]!
        rhs := aargs[1]!
        rebuild := fun L' R' => do
          let adv ← mkAppM ``Game.advantage #[L', R']
          return mkApp4 p.getAppFn ty inst adv rhsLe
      }
    if lhsLe.isAppOfArity ``NNReal.toReal 1 then
      let inner := lhsLe.getAppArgs[0]!.cleanupAnnotations
      if inner.isAppOfArity ``Game.advantage 2 then
        let aargs := inner.getAppArgs
        return some {
          lhs := aargs[0]!
          rhs := aargs[1]!
          rebuild := fun L' R' => do
            let adv ← mkAppM ``Game.advantage #[L', R']
            let coeAdv := mkApp (mkConst ``NNReal.toReal) adv
            return mkApp4 p.getAppFn ty inst coeAdv rhsLe
        }
  return none

/-- Lift `hL? : L = L'` and `hR? : R = R'` to a propositional equality `oldProp = newProp`. -/
private meta def mkRebuildEq (origProp : Expr) (dec : BinaryPMFTarget)
    (L' R' : Expr) (hL? hR? : Option Expr) : MetaM (Expr × Expr) := do
  let newProp ← dec.rebuild L' R'
  let uL ← getLevel (← inferType dec.lhs)
  let uR ← getLevel (← inferType dec.rhs)
  let mut curProp ← dec.rebuild dec.lhs dec.rhs
  let mut hAcc? : Option Expr := none
  if origProp != curProp then
    hAcc? := some (← castEqProof origProp curProp (← mkEqRefl curProp))
  if let some hL := hL? then
    let ctxL ← withLocalDeclD `_L (← inferType dec.lhs) fun xL => do
      mkLambdaFVars #[xL] (← dec.rebuild xL dec.rhs)
    let midProp ← dec.rebuild L' dec.rhs
    let hStep := mkApp6 (mkConst ``congrArg [uL, .succ .zero])
      (← inferType dec.lhs) (mkSort .zero) dec.lhs L' ctxL (← castEqProof dec.lhs L' hL)
    hAcc? ← chainEqOpt origProp midProp hAcc? (some hStep)
    curProp := midProp
  if let some hR := hR? then
    let ctxR ← withLocalDeclD `_R (← inferType dec.rhs) fun xR => do
      mkLambdaFVars #[xR] (← dec.rebuild L' xR)
    let hStep := mkApp6 (mkConst ``congrArg [uR, .succ .zero])
      (← inferType dec.rhs) (mkSort .zero) dec.rhs R' ctxR (← castEqProof dec.rhs R' hR)
    hAcc? ← chainEqOpt origProp newProp hAcc? (some hStep)
  let hFinal := hAcc?.getD (mkApp2 (mkConst ``Eq.refl [.succ .zero]) (mkSort .zero) newProp)
  return (newProp, ← castEqProof origProp newProp hFinal)

/-! ### `peel_binds` syntax and elaborator -/

private inductive PeelMode where
  | advNNReal (B : Expr)
  | advReal (B : Expr)
  | closeTo (α B : Expr)
  | eqPMF (T : Expr)

private meta def classifyPeelGoal? (prop : Expr) :
    MetaM (Option (PeelMode × BinaryPMFTarget)) := do
  let p0 ← deltaExpand prop (· == ``Cslib.Crypto.Encryption.advantage)
  let some dec ← decomposePMFTarget? p0 | return none
  let p := p0.cleanupAnnotations
  if p.isAppOfArity ``CloseTo 4 then
    let args := p.getAppArgs
    return some (.closeTo args[0]! args[3]!, dec)
  if p.isAppOfArity ``Eq 3 then
    let args := p.getAppArgs
    return some (.eqPMF args[0]!, dec)
  if p.isAppOfArity ``LE.le 4 then
    let args := p.getAppArgs
    let lhsLe := args[2]!.cleanupAnnotations
    let B := args[3]!
    if lhsLe.isAppOfArity ``Game.advantage 2 then
      return some (.advNNReal B, dec)
    if lhsLe.isAppOfArity ``NNReal.toReal 1 then
      let inner := lhsLe.getAppArgs[0]!.cleanupAnnotations
      if inner.isAppOfArity ``Game.advantage 2 then
        return some (.advReal B, dec)
  return none

private meta def stagesDirectlyMatch (sL sR : ParsedStage) : MetaM Bool := do
  match sL.head, sR.head with
  | .pmfBind αL _ μL, .pmfBind αR _ μR =>
    withNewMCtxDepth <| withReducibleAndInstances (isDefEq αL αR <&&> isDefEq μL μR)
  | .statelessOracle αL oL progL, .statelessOracle αR oR progR =>
    withNewMCtxDepth <|
      withReducibleAndInstances (isDefEq αL αR <&&> isDefEq oL oR <&&> isDefEq progL progR)
  | _, _ => return false

/-- Check whether `e` has a 2nd stage that is independent of its 1st stage and matches `target`,
returning `some (eSwapped, hEq : e = eSwapped)` when so. -/
private meta def tryOneStepSwapMatch? (target : ParsedStage) (e : Expr) (s₀ : ParsedStage) :
    MetaM (Option (Expr × Expr)) := do
  let canSwap ← withLocalDeclD `y s₀.binderType fun y => do
    let innerRaw := (mkApp s₀.cont y).headBeta
    let (innerNorm, _) ← normalizeBindHead innerRaw
    let some s₁ ← parseStage? innerNorm | return false
    if s₁.head.mentionsFVar y.fvarId! then return false
    stagesDirectlyMatch target s₁
  unless canSwap do return none
  let (swapped, hSwap) ← swapAdjacentStages e s₀
  return some (swapped, hSwap)

/-- Inner implementation of `peelOneStage?`; callers wrap this in `saveState`/`restore` so any
speculative target replacement is rolled back cleanly when returning `none`. -/
private meta def peelOneStageCore? (goal : MVarId) (reqName? : Option Name) :
    MetaM (Option MVarId) := goal.withContext do
  let origTarget ← instantiateMVars (← goal.getType)
  let some (mode, dec) ← classifyPeelGoal? origTarget | return none
  let (LNorm, hLNorm?) ← normalizeBindHead dec.lhs
  let (RNorm, hRNorm?) ← normalizeBindHead dec.rhs
  let mut curGoal := goal
  let mut curL := LNorm
  let mut curR := RNorm
  if hLNorm?.isSome || hRNorm?.isSome || (← deltaExpand origTarget
      (· == ``Cslib.Crypto.Encryption.advantage)) != origTarget then
    let (normProp, hNormEq) ← mkRebuildEq origTarget dec LNorm RNorm hLNorm? hRNorm?
    curGoal ← curGoal.replaceTargetEq normProp hNormEq
  let some sLInit ← parseStage? curL | return none
  let some sRInit ← parseStage? curR | return none
  let mut sL := sLInit
  let mut sR := sRInit
  if !(← stagesDirectlyMatch sL sR) then
    if let some (RSwapped, hRSwap) ← tryOneStepSwapMatch? sL curR sR then
      let curProp ← instantiateMVars (← curGoal.getType)
      let some (_, decCur) ← classifyPeelGoal? curProp | return none
      let (swappedProp, hPropEq) ← mkRebuildEq curProp decCur curL RSwapped none (some hRSwap)
      curGoal ← curGoal.replaceTargetEq swappedProp hPropEq
      curR := RSwapped
      let some sR' ← parseStage? curR | return none
      sR := sR'
    else if let some (LSwapped, hLSwap) ← tryOneStepSwapMatch? sR curL sL then
      let curProp ← instantiateMVars (← curGoal.getType)
      let some (_, decCur) ← classifyPeelGoal? curProp | return none
      let (swappedProp, hPropEq) ← mkRebuildEq curProp decCur LSwapped curR (some hLSwap) none
      curGoal ← curGoal.replaceTargetEq swappedProp hPropEq
      curL := LSwapped
      let some sL' ← parseStage? curL | return none
      sL := sL'
    else
      return none
  let chosenName : Name := match reqName? with
    | some n => if n == `_ then `x else n
    | none =>
      if !sL.binderName.isAnonymous && !sL.binderName.isInternal then sL.binderName
      else if !sR.binderName.isAnonymous && !sR.binderName.isInternal then sR.binderName
      else `x
  let memName : Name :=
    if reqName? == some `_ then `_
    else Name.appendAfter chosenName "_mem"
  -- Construct the lemma application directly with `mkAppN` so uninstantiated bound metavariables
  -- `B` (such as `?ε_i` from `game_trans`) never trigger `mkAppOptM`'s metavariable check.
  let lemmaApp ← match sL.head, sR.head, mode with
    | .pmfBind αL _ μL, .pmfBind _ _ _, .advNNReal B => do
      let u ← getDecLevel αL
      pure (mkAppN (mkConst ``Game.advantage_bind_le_of_support [u]) #[αL, μL, sL.cont, sR.cont, B])
    | .pmfBind αL _ μL, .pmfBind _ _ _, .advReal B => do
      let u ← getDecLevel αL
      pure (mkAppN (mkConst ``Game.coe_advantage_bind_le_of_support [u])
        #[αL, μL, sL.cont, sR.cont, B])
    | .pmfBind αL βL μL, .pmfBind _ _ _, .closeTo _ B =>
      pure (mkAppN (mkConst ``CloseTo.bind_right []) #[αL, βL, μL, sL.cont, sR.cont, B])
    | .pmfBind αL βL μL, .pmfBind _ _ _, .eqPMF _ => do
      let u ← getDecLevel αL
      let v ← getDecLevel βL
      pure (mkAppN (mkConst ``Cslib.Probability.PMF.bind_congr_on_support [u, v])
        #[αL, βL, μL, sL.cont, sR.cont])
    | .statelessOracle αL oL progL, .statelessOracle _ _ _, .advNNReal B =>
      pure (mkAppN (mkConst ``Game.advantage_runStatelessOracle_le_of_support [])
        #[αL, oL, progL, sL.cont, sR.cont, B])
    | .statelessOracle αL oL progL, .statelessOracle _ _ _, .advReal B =>
      pure (mkAppN (mkConst ``Game.coe_advantage_runStatelessOracle_le_of_support [])
        #[αL, oL, progL, sL.cont, sR.cont, B])
    | .statelessOracle αL oL progL, .statelessOracle _ _ _, .closeTo _ B =>
      pure (mkAppN (mkConst ``Game.closeTo_runStatelessOracle [])
        #[αL, oL, progL, sL.cont, sR.cont, B])
    | .statelessOracle αL oL progL, .statelessOracle _ _ _, .eqPMF _ =>
      pure (mkAppN (mkConst ``Game.runStatelessOracle_congr_on_support [])
        #[αL, oL, progL, sL.cont, sR.cont])
    | _, _, _ => return none
  let .forallE _ premiseTy _ _ ← whnf (← inferType lemmaApp) | return none
  let g1MVar ← mkFreshExprSyntheticOpaqueMVar premiseTy (← curGoal.getTag)
  curGoal.assign (mkApp lemmaApp g1MVar)
  let (_, g2) ← g1MVar.mvarId!.intro chosenName
  let (_, g3) ← g2.intro memName
  -- Head-beta-reduce `(fun x => ...) x` on the peeled continuations only.
  g3.withContext do
    let t3 ← instantiateMVars (← g3.getType)
    if let some (_, dec3) ← classifyPeelGoal? t3 then
      let L3 := dec3.lhs.headBeta
      let R3 := dec3.rhs.headBeta
      if L3 != dec3.lhs || R3 != dec3.rhs then
        let newT3 ← dec3.rebuild L3 R3
        return some (← g3.replaceTargetDefEq newT3)
    return some g3

/-- Peel a single coupled stage from `goal`, using `reqName?` if provided.
Returns `some newGoal` on success, or restores `Meta.SavedState` and returns `none` if the leading
stages cannot be coupled (preventing leaked metavariables from head normalization or swaps). -/
private meta def peelOneStage? (goal : MVarId) (reqName? : Option Name) :
    MetaM (Option MVarId) := do
  let saved ← saveState
  match ← peelOneStageCore? goal reqName? with
  | some newGoal => return some newGoal
  | none =>
    saved.restore
    return none

/-- Binder name or `_` placeholder accepted by `peel_binds`. -/
syntax peelBinder := ident <|> "_"

/-- Peel shared leading `PMF.bind` and `Game.runStatelessOracle` stages on `Game.advantage`,
`Encryption.advantage`, `CloseTo`, or `PMF` equality goals, introducing each draw `x` and its
support witness `x_mem : x ∈ μ.support`.

* `peel_binds` peels all shared leading stages (performing a one-step independent `PMF.bind_comm`
  swap when a leading distribution matches the opposite side's second stage).
* `peel_binds x₁ x₂ ...` peels exactly those stages using the given binder names (`_` names the
  draw `x` and leaves its support witness inaccessible). -/
syntax (name := peelBinds) "peel_binds" (ppSpace colGt peelBinder)* : tactic

elab_rules : tactic
  | `(tactic| peel_binds $binders*) => withMainContext do
    let mut goal ← getMainGoal
    let origTarget ← instantiateMVars (← goal.getType)
    unless (← classifyPeelGoal? origTarget).isSome do
      throwError "peel_binds: expected a `Game.advantage`, `Encryption.advantage`, `CloseTo`, \
        or `PMF` equality goal{indentExpr origTarget}"
    if binders.isEmpty then
      let mut count := 0
      while true do
        match ← peelOneStage? goal none with
        | some g' =>
          goal := g'
          count := count + 1
        | none => break
      if count == 0 then
        throwError "peel_binds: leading stages do not match and cannot be aligned by a single \
          independent swap{indentExpr (← goal.getType)}"
      replaceMainGoal [goal]
    else
      for bStx in binders do
        let bName : Name ← match bStx with
          | `(peelBinder| $id:ident) => pure id.getId
          | `(peelBinder| _) => pure `_
          | _ => throwUnsupportedSyntax
        match ← peelOneStage? goal (some bName) with
        | some g' => goal := g'
        | none =>
          throwError "peel_binds: could not peel stage `{bName}`; leading distributions do not \
            match and cannot be aligned by a single independent swap\
            {indentExpr (← goal.getType)}"
      replaceMainGoal [goal]

/-! ### `game_trans` syntax and elaborator -/

private inductive HopMode where
  | advNNReal
  | advReal
  | closeTo (α : Expr)

private structure ParsedHopGoal where
  mode : HopMode
  start : Expr
  stop : Expr
  bound : Expr
  /-- Whether the original goal required an initial conversion (such as `Encryption.advantage`
  unfolding or `Game.succProbability` reduction) to reach `(mode, start, stop, bound)`. -/
  converted : Bool

/-- Reduce `Encryption.advantage` or `Game.succProbability` goals to `(HopMode, start, stop, B)`
and return the transformed `MVarId`. -/
private meta def prepareGameTransGoal (goal : MVarId) : MetaM (MVarId × ParsedHopGoal) :=
  goal.withContext do
    let orig ← instantiateMVars (← goal.getType)
    let unfolded ← deltaExpand orig (· == ``Cslib.Crypto.Encryption.advantage)
    let mut curGoal := goal
    let mut converted := false
    if unfolded != orig then
      curGoal ← curGoal.replaceTargetDefEq unfolded
      converted := true
    let p := unfolded.cleanupAnnotations
    if p.isAppOfArity ``CloseTo 4 then
      let args := p.getAppArgs
      return (curGoal, {
        mode := .closeTo args[0]!
        start := args[1]!
        stop := args[2]!
        bound := args[3]!
        converted
      })
    if p.isAppOfArity ``LE.le 4 then
      let args := p.getAppArgs
      let lhsLe := args[2]!.cleanupAnnotations
      let rhsLe := args[3]!.cleanupAnnotations
      if lhsLe.isAppOfArity ``Game.advantage 2 then
        let aargs := lhsLe.getAppArgs
        return (curGoal, {
          mode := .advNNReal
          start := aargs[0]!
          stop := aargs[1]!
          bound := rhsLe
          converted
        })
      if lhsLe.isAppOfArity ``Game.succProbability 1 then
        let g₀ := lhsLe.getAppArgs[0]!
        if rhsLe.isAppOfArity ``HAdd.hAdd 6 then
          let hargs := rhsLe.getAppArgs
          let s1 := hargs[4]!.cleanupAnnotations
          let s2 := hargs[5]!.cleanupAnnotations
          if s1.isAppOfArity ``Game.succProbability 1 then
            let g₁ := s1.getAppArgs[0]!
            let [g'] ← curGoal.apply (← mkAppOptM ``Game.succProbability_le_add_of_advantage_le
              #[some g₀, some g₁, some s2])
              | throwError "game_trans: unexpected subgoals reducing `Game.succProbability`"
            return (g', { mode := .advNNReal, start := g₀, stop := g₁, bound := s2,
                          converted := true })
          if s2.isAppOfArity ``Game.succProbability 1 then
            let g₁ := s2.getAppArgs[0]!
            let B := hargs[4]!
            let hComm ← mkAppM ``add_comm #[s2, B]
            let newRhs := (← inferType hComm).getAppArgs[1]!
            let hEq ← mkCongrArg (mkApp3 p.getAppFn args[0]! args[1]! lhsLe) (← mkEqSymm hComm)
            let gSwap ← curGoal.replaceTargetEq
              (mkApp4 p.getAppFn args[0]! args[1]! lhsLe newRhs) hEq
            let [g'] ← gSwap.apply (← mkAppOptM ``Game.succProbability_le_add_of_advantage_le
              #[some g₀, some g₁, some B])
              | throwError "game_trans: unexpected subgoals reducing `Game.succProbability`"
            return (g', { mode := .advNNReal, start := g₀, stop := g₁, bound := B,
                          converted := true })
        let [g'] ← curGoal.apply (← mkAppOptM ``Game.succProbability_le_of_advantage_pure_false_le
          #[some g₀, some rhsLe])
          | throwError "game_trans: unexpected subgoals reducing `Game.succProbability`"
        let pureFalse := (← g'.getType).getAppArgs[2]!.getAppArgs[1]!
        return (g', { mode := .advNNReal, start := g₀, stop := pureFalse, bound := rhsLe,
                      converted := true })
      if lhsLe.isAppOfArity ``NNReal.toReal 1 then
        let inner := lhsLe.getAppArgs[0]!.cleanupAnnotations
        if inner.isAppOfArity ``Game.advantage 2 then
          let aargs := inner.getAppArgs
          return (curGoal, {
            mode := .advReal
            start := aargs[0]!
            stop := aargs[1]!
            bound := rhsLe
            converted
          })
        if inner.isAppOfArity ``Game.succProbability 1 then
          let g₀ := inner.getAppArgs[0]!
          if rhsLe.isAppOfArity ``HAdd.hAdd 6 then
            let hargs := rhsLe.getAppArgs
            let s1 := hargs[4]!.cleanupAnnotations
            let s2 := hargs[5]!.cleanupAnnotations
            if s1.isAppOfArity ``NNReal.toReal 1 &&
                s1.getAppArgs[0]!.cleanupAnnotations.isAppOfArity ``Game.succProbability 1 then
              let g₁ := s1.getAppArgs[0]!.cleanupAnnotations.getAppArgs[0]!
              let [g'] ← curGoal.apply
                (← mkAppOptM ``Game.coe_succProbability_le_add_of_advantage_le
                  #[some g₀, some g₁, some hargs[5]!])
                | throwError "game_trans: unexpected subgoals reducing `(succProbability : ℝ)`"
              return (g', { mode := .advReal, start := g₀, stop := g₁, bound := hargs[5]!,
                            converted := true })
            if s2.isAppOfArity ``NNReal.toReal 1 &&
                s2.getAppArgs[0]!.cleanupAnnotations.isAppOfArity ``Game.succProbability 1 then
              let g₁ := s2.getAppArgs[0]!.cleanupAnnotations.getAppArgs[0]!
              let B := hargs[4]!
              let hComm ← mkAppM ``add_comm #[s2, B]
              let newRhs := (← inferType hComm).getAppArgs[1]!
              let hEq ← mkCongrArg (mkApp3 p.getAppFn args[0]! args[1]! lhsLe) (← mkEqSymm hComm)
              let gSwap ← curGoal.replaceTargetEq
                (mkApp4 p.getAppFn args[0]! args[1]! lhsLe newRhs) hEq
              let [g'] ← gSwap.apply
                (← mkAppOptM ``Game.coe_succProbability_le_add_of_advantage_le
                  #[some g₀, some g₁, some B])
                | throwError "game_trans: unexpected subgoals reducing `(succProbability : ℝ)`"
              return (g', { mode := .advReal, start := g₀, stop := g₁, bound := B,
                            converted := true })
          let [g'] ← curGoal.apply
            (← mkAppOptM ``Game.coe_succProbability_le_of_advantage_pure_false_le
              #[some g₀, some rhsLe])
            | throwError "game_trans: unexpected subgoals reducing `(succProbability : ℝ)`"
          let pureFalse := (← g'.getType).getAppArgs[2]!.getAppArgs[0]!.getAppArgs[1]!
          return (g', { mode := .advReal, start := g₀, stop := pureFalse, bound := rhsLe,
                        converted := true })
    throwError "game_trans: expected a `Game.advantage`, `Encryption.advantage`, \
      `Game.succProbability`, or `CloseTo` goal{indentExpr orig}"

private meta def HopMode.itemType (m : HopMode) : MetaM Expr :=
  match m with
  | .advNNReal | .advReal => return mkConst ``Game
  | .closeTo α => mkAppM ``PMF #[α]

private meta def HopMode.boundType (m : HopMode) : Expr :=
  match m with
  | .advNNReal => mkConst ``NNReal
  | .advReal => mkConst ``Real
  | .closeTo _ => mkConst ``ENNReal

private meta def HopMode.mkHopProp (m : HopMode) (a b ε : Expr) : MetaM Expr := do
  match m with
  | .advNNReal =>
    let adv ← mkAppM ``Game.advantage #[a, b]
    mkAppM ``LE.le #[adv, ε]
  | .advReal =>
    let adv ← mkAppM ``Game.advantage #[a, b]
    let coeAdv := mkApp (mkConst ``NNReal.toReal) adv
    mkAppM ``LE.le #[coeAdv, ε]
  | .closeTo α =>
    mkAppOptM ``CloseTo #[some α, some a, some b, some ε]

/-- Run a speculative `TacticM` elaboration `act`, rolling back both `Tactic.SavedState` and
`Core.State.messages` whenever `act` throws, logs an error message, or fails `check` (e.g. when
`elabByTactic` logs an error and synthesizes `sorryAx` without throwing). -/
private meta def runCleanProbe? {α : Type} (check : α → MetaM Bool) (act : TacticM α) :
    TacticM (Option α) := do
  let saved ← saveState
  let savedMsgs ← Core.getMessageLog
  Core.resetMessageLog
  try
    let res ← Term.withoutErrToSorry act
    let probeMsgs ← Core.getMessageLog
    if probeMsgs.hasErrors || !(← check res) then
      saved.restore
      Core.setMessageLog savedMsgs
      return none
    Core.setMessageLog (savedMsgs ++ probeMsgs)
    return some res
  catch _ =>
    saved.restore
    Core.setMessageLog savedMsgs
    return none

/-- Try elaborating `stx` at expected type `ty` without committing on failure, logged errors,
`sorryAx`, or uninstantiated metavariables. -/
private meta def tryElabTyped? (stx : Syntax) (ty : Expr) : TacticM (Option Expr) :=
  runCleanProbe?
    (fun e => do
      let tyInst ← instantiateMVars ty
      return !e.hasSorry && !tyInst.hasSorry && !e.hasExprMVar && !tyInst.hasExprMVar)
    do
      let v ← Term.elabTermEnsuringType stx (some ty)
      Term.synthesizeSyntheticMVarsNoPostponing
      instantiateMVars v

/-- Assign a zero-error hop proof to `hopGoal` from `hEq : a = b`. -/
private meta def assignZeroEqHop (hopGoal : MVarId) (mode : HopMode)
    (a εMVar hEq : Expr) : MetaM Unit := do
  let zeroExpr ← mkNumeral mode.boundType 0
  let _ ← isDefEq εMVar zeroExpr
  let reflHop ← match mode with
    | .advNNReal =>
      let hSelf ← mkAppM ``Game.advantage_self #[a]
      mkAppM ``le_of_eq #[hSelf]
    | .advReal =>
      let hSelf ← mkAppM ``Game.advantage_self #[a]
      let hCoe ← mkCongrArg (mkConst ``NNReal.toReal) hSelf
      let hZero := mkConst ``NNReal.coe_zero
      mkAppM ``le_of_eq #[← mkEqTrans hCoe hZero]
    | .closeTo _ =>
      mkAppM ``CloseTo.refl #[a]
  let itemTy ← mode.itemType
  let motive ← withLocalDeclD `_X itemTy fun x => do
    mkLambdaFVars #[x] (← mode.mkHopProp a x zeroExpr)
  hopGoal.assign (← mkEqNDRec motive reflHop hEq)

/-- Check `isDefEq x targetA` and `isDefEq y targetB` at `.instances` transparency (unfolding
`abbrev` and `let`, never `def` games), restoring state on mismatch. -/
private meta def matchHopEndpoints (x y targetA targetB : Expr) : MetaM Bool := do
  let saved ← saveState
  let ok ← withReducibleAndInstances (isDefEq x targetA <&&> isDefEq y targetB)
  unless ok do saved.restore
  return ok

/-- Match an already-elaborated hop proof `uExpr : uTy` against `(mode, a, b, εMVar)` without
unfolding `def` game bodies. -/
private meta def tryAssignElaboratedHop (hopGoal : MVarId) (mode : HopMode)
    (a b εMVar uExpr uTy : Expr) : MetaM Bool := do
  let tc := (← whnfR uTy).cleanupAnnotations
  if tc.isAppOfArity ``Eq 3 then
    let args := tc.getAppArgs
    let x := args[1]!
    let y := args[2]!
    if ← matchHopEndpoints x y a b then
      assignZeroEqHop hopGoal mode a εMVar uExpr
      return true
    if ← matchHopEndpoints x y b a then
      assignZeroEqHop hopGoal mode a εMVar (← mkEqSymm uExpr)
      return true
    return false
  if tc.isAppOfArity ``CloseTo 4 then
    if let .closeTo _ := mode then
      let args := tc.getAppArgs
      let x := args[1]!
      let y := args[2]!
      let epsRhs := args[3]!
      if ← matchHopEndpoints x y a b then
        let _ ← isDefEq εMVar epsRhs
        hopGoal.assign uExpr
        return true
      if ← matchHopEndpoints x y b a then
        let _ ← isDefEq εMVar epsRhs
        hopGoal.assign (← mkAppM ``CloseTo.symm #[uExpr])
        return true
    return false
  if tc.isAppOfArity ``LE.le 4 then
    let args := tc.getAppArgs
    let leTy := (← whnfR args[0]!).cleanupAnnotations
    let lhsExpr := args[2]!.cleanupAnnotations
    let epsRhs := args[3]!
    if leTy.isConstOf ``NNReal && lhsExpr.isAppOfArity ``Game.advantage 2 then
      let lArgs := lhsExpr.getAppArgs
      let x := lArgs[0]!
      let y := lArgs[1]!
      match mode with
      | .advNNReal =>
        if ← matchHopEndpoints x y a b then
          let _ ← isDefEq εMVar epsRhs
          hopGoal.assign uExpr
          return true
        if ← matchHopEndpoints x y b a then
          let _ ← isDefEq εMVar epsRhs
          let hComm ← mkAppM ``Game.advantage_comm #[a, b]
          hopGoal.assign (← mkAppM ``Eq.trans_le #[hComm, uExpr])
          return true
      | .advReal =>
        if ← matchHopEndpoints x y a b then
          let _ ← isDefEq εMVar (mkApp (mkConst ``NNReal.toReal) epsRhs)
          let advAB ← mkAppM ``Game.advantage #[a, b]
          let hIff ← mkAppOptM ``NNReal.coe_le_coe #[some advAB, some epsRhs]
          hopGoal.assign (← mkAppM ``Iff.mpr #[hIff, uExpr])
          return true
        if ← matchHopEndpoints x y b a then
          let _ ← isDefEq εMVar (mkApp (mkConst ``NNReal.toReal) epsRhs)
          let advAB ← mkAppM ``Game.advantage #[a, b]
          let hComm ← mkAppM ``Game.advantage_comm #[a, b]
          let hAligned ← mkAppM ``Eq.trans_le #[hComm, uExpr]
          let hIff ← mkAppOptM ``NNReal.coe_le_coe #[some advAB, some epsRhs]
          hopGoal.assign (← mkAppM ``Iff.mpr #[hIff, hAligned])
          return true
      | .closeTo _ => return false
    if leTy.isConstOf ``NNReal && lhsExpr.isAppOfArity ``Game.succProbability 1 then
      let x := lhsExpr.getAppArgs[0]!
      let pureFalse ← mkAppM ``PMF.pure #[mkConst ``Bool.false]
      let hAdvPure ← mkAppM ``Game.advantage_pure_false #[x]
      let hAdvLe ← mkAppM ``Eq.trans_le #[hAdvPure, uExpr]
      match mode with
      | .advNNReal =>
        if ← matchHopEndpoints x pureFalse a b then
          let _ ← isDefEq εMVar epsRhs
          hopGoal.assign hAdvLe
          return true
        if ← matchHopEndpoints x pureFalse b a then
          let _ ← isDefEq εMVar epsRhs
          let hComm ← mkAppM ``Game.advantage_comm #[a, b]
          hopGoal.assign (← mkAppM ``Eq.trans_le #[hComm, hAdvLe])
          return true
      | .advReal =>
        if ← matchHopEndpoints x pureFalse a b then
          let _ ← isDefEq εMVar (mkApp (mkConst ``NNReal.toReal) epsRhs)
          let advAB ← mkAppM ``Game.advantage #[a, b]
          let hIff ← mkAppOptM ``NNReal.coe_le_coe #[some advAB, some epsRhs]
          hopGoal.assign (← mkAppM ``Iff.mpr #[hIff, hAdvLe])
          return true
        if ← matchHopEndpoints x pureFalse b a then
          let _ ← isDefEq εMVar (mkApp (mkConst ``NNReal.toReal) epsRhs)
          let advAB ← mkAppM ``Game.advantage #[a, b]
          let hComm ← mkAppM ``Game.advantage_comm #[a, b]
          let hAligned ← mkAppM ``Eq.trans_le #[hComm, hAdvLe]
          let hIff ← mkAppOptM ``NNReal.coe_le_coe #[some advAB, some epsRhs]
          hopGoal.assign (← mkAppM ``Iff.mpr #[hIff, hAligned])
          return true
      | .closeTo _ => return false
    if let .advReal := mode then
      if leTy.isConstOf ``Real && lhsExpr.isAppOfArity ``NNReal.toReal 1 then
        let inner := lhsExpr.getAppArgs[0]!.cleanupAnnotations
        if inner.isAppOfArity ``Game.advantage 2 then
          let iArgs := inner.getAppArgs
          let x := iArgs[0]!
          let y := iArgs[1]!
          if ← matchHopEndpoints x y a b then
            let _ ← isDefEq εMVar epsRhs
            hopGoal.assign uExpr
            return true
          if ← matchHopEndpoints x y b a then
            let _ ← isDefEq εMVar epsRhs
            let hComm ← mkAppM ``Game.advantage_comm #[a, b]
            let hCoeComm ← mkCongrArg (mkConst ``NNReal.toReal) hComm
            hopGoal.assign (← mkAppM ``Eq.trans_le #[hCoeComm, uExpr])
            return true
        if inner.isAppOfArity ``Game.succProbability 1 then
          let x := inner.getAppArgs[0]!
          let pureFalse ← mkAppM ``PMF.pure #[mkConst ``Bool.false]
          let hAdvPure ← mkAppM ``Game.advantage_pure_false #[x]
          let hCoeAdvPure ← mkCongrArg (mkConst ``NNReal.toReal) hAdvPure
          let hAdvLe ← mkAppM ``Eq.trans_le #[hCoeAdvPure, uExpr]
          if ← matchHopEndpoints x pureFalse a b then
            let _ ← isDefEq εMVar epsRhs
            hopGoal.assign hAdvLe
            return true
          if ← matchHopEndpoints x pureFalse b a then
            let _ ← isDefEq εMVar epsRhs
            let hComm ← mkAppM ``Game.advantage_comm #[a, b]
            let hCoeComm ← mkCongrArg (mkConst ``NNReal.toReal) hComm
            hopGoal.assign (← mkAppM ``Eq.trans_le #[hCoeComm, hAdvLe])
            return true
  return false

/-- Solve a single hop subgoal `hopGoal` (`A` to `B` with bound `?ε`) from `uStx`, trying direct
orientation, symmetric orientation (`advantage_comm` / `CloseTo.symm`), `ℝ≥0 → ℝ` coercion, and
definitional/propositional equality (`A = B` or `B = A`). -/
private meta def solveHopGoalWith (hopGoal : MVarId) (mode : HopMode)
    (a b εMVar : Expr) (uStx : Syntax) : TacticM Unit := hopGoal.withContext do
  let hopTy ← instantiateMVars (← hopGoal.getType)
  -- Fast path: elaborate `uStx` once standalone and match endpoints at `.instances` transparency
  -- so distinct `def` games never trigger costly `whnf` unfolding.
  let rawElab? ← runCleanProbe?
    (fun (e, ty) => pure (!e.hasSorry && !ty.hasSorry && !e.hasExprMVar && !ty.hasExprMVar))
    do
      let v ← Term.elabTerm uStx none
      Term.synthesizeSyntheticMVarsNoPostponing
      let e ← instantiateMVars v
      let ty ← instantiateMVars (← inferType e)
      return (e, ty)
  if let some (uExpr, uTy) := rawElab? then
    if ← tryAssignElaboratedHop hopGoal mode a b εMVar uExpr uTy then
      return
    throwErrorAt uStx "game_trans: hop proof has type{indentExpr uTy}\n\
      which does not match expected hop (up to symmetry or equality){indentExpr hopTy}"
  -- Expected-type fallback for context-dependent terms such as `le_rfl`, `rfl`, or `by ...`.
  if let some prf ← tryElabTyped? uStx hopTy then
    hopGoal.assign prf
    return
  let revTy ← mode.mkHopProp b a εMVar
  if let some prfRev ← tryElabTyped? uStx revTy then
    let prf ← match mode with
      | .advNNReal =>
        let hComm ← mkAppM ``Game.advantage_comm #[a, b]
        mkAppM ``Eq.trans_le #[hComm, prfRev]
      | .advReal =>
        let hComm ← mkAppM ``Game.advantage_comm #[a, b]
        let hCoeComm ← mkCongrArg (mkConst ``NNReal.toReal) hComm
        mkAppM ``Eq.trans_le #[hCoeComm, prfRev]
      | .closeTo _ =>
        mkAppM ``CloseTo.symm #[prfRev]
    hopGoal.assign prf
    return
  let eqAB ← mkEq a b
  let eqBA ← mkEq b a
  let hEq? ← match ← tryElabTyped? uStx eqAB with
    | some h => pure (some h)
    | none =>
      match ← tryElabTyped? uStx eqBA with
      | some hRev => pure (some (← mkEqSymm hRev))
      | none => pure none
  if let some hEq := hEq? then
    assignZeroEqHop hopGoal mode a εMVar hEq
    return
  match mode with
  | .advNNReal =>
    let pureFalse ← mkAppM ``PMF.pure #[mkConst ``Bool.false]
    if ← withNewMCtxDepth (withReducibleAndInstances (isDefEq b pureFalse)) then
      let succA ← mkAppM ``Game.succProbability #[a]
      let succTy ← mkAppM ``LE.le #[succA, εMVar]
      if let some prfSucc ← tryElabTyped? uStx succTy then
        let hAdvPure ← mkAppM ``Game.advantage_pure_false #[a]
        hopGoal.assign (← mkAppM ``Eq.trans_le #[hAdvPure, prfSucc])
        return
    if ← withNewMCtxDepth (withReducibleAndInstances (isDefEq a pureFalse)) then
      let succB ← mkAppM ``Game.succProbability #[b]
      let succTy ← mkAppM ``LE.le #[succB, εMVar]
      if let some prfSucc ← tryElabTyped? uStx succTy then
        let hAdvPure ← mkAppM ``Game.advantage_pure_false #[b]
        let hComm ← mkAppM ``Game.advantage_comm #[a, b]
        hopGoal.assign
          (← mkAppM ``Eq.trans_le #[hComm, ← mkAppM ``Eq.trans_le #[hAdvPure, prfSucc]])
        return
  | .advReal =>
    let pureFalse ← mkAppM ``PMF.pure #[mkConst ``Bool.false]
    if ← withNewMCtxDepth (withReducibleAndInstances (isDefEq b pureFalse)) then
      let succA ← mkAppM ``Game.succProbability #[a]
      let coeSuccA := mkApp (mkConst ``NNReal.toReal) succA
      let succTy ← mkAppM ``LE.le #[coeSuccA, εMVar]
      if let some prfSucc ← tryElabTyped? uStx succTy then
        let hCoeAdvPure ← mkCongrArg (mkConst ``NNReal.toReal)
          (← mkAppM ``Game.advantage_pure_false #[a])
        hopGoal.assign (← mkAppM ``Eq.trans_le #[hCoeAdvPure, prfSucc])
        return
    if ← withNewMCtxDepth (withReducibleAndInstances (isDefEq a pureFalse)) then
      let succB ← mkAppM ``Game.succProbability #[b]
      let coeSuccB := mkApp (mkConst ``NNReal.toReal) succB
      let succTy ← mkAppM ``LE.le #[coeSuccB, εMVar]
      if let some prfSucc ← tryElabTyped? uStx succTy then
        let hCoeAdvPure ← mkCongrArg (mkConst ``NNReal.toReal)
          (← mkAppM ``Game.advantage_pure_false #[b])
        let hCoeComm ← mkCongrArg (mkConst ``NNReal.toReal)
          (← mkAppM ``Game.advantage_comm #[a, b])
        hopGoal.assign
          (← mkAppM ``Eq.trans_le #[hCoeComm, ← mkAppM ``Eq.trans_le #[hCoeAdvPure, prfSucc]])
        return
  | .closeTo _ => pure ()
  let prf ← Term.elabTermEnsuringType uStx (some hopTy)
  Term.synthesizeSyntheticMVarsNoPostponing
  hopGoal.assign prf

/-- Collect `(x, y)` argument pairs of `Game.advantage x y` occurrences in `e` without descending
into game bodies. -/
private meta partial def collectAdvPairs (e : Expr) : Array (Expr × Expr) :=
  let c := e.cleanupAnnotations
  if c.isAppOfArity ``Game.advantage 2 then
    let args := c.getAppArgs
    #[(args[0]!, args[1]!)]
  else if c.isApp then
    c.getAppArgs.foldl (fun acc a => acc ++ collectAdvPairs a) #[]
  else
    #[]

/-- Align `Game.advantage x y` summands in `e` to `Game.advantage y x` when `(y, x)` appears in
`bPairs` and `(x, y)` does not, returning `(e', h : e = e')`. -/
private meta partial def alignAdvSummands (bPairs : Array (Expr × Expr)) (e : Expr) :
    MetaM (Option (Expr × Expr)) := do
  let c := e.cleanupAnnotations
  if c.isAppOfArity ``Game.advantage 2 then
    let args := c.getAppArgs
    let x := args[0]!
    let y := args[1]!
    if !(← bPairs.anyM fun (u, v) => matchHopEndpoints x y u v) &&
        (← bPairs.anyM fun (u, v) => matchHopEndpoints y x u v) then
      let e' ← mkAppM ``Game.advantage #[y, x]
      let h ← mkAppM ``Game.advantage_comm #[x, y]
      return some (e', h)
    return none
  if c.isAppOfArity ``NNReal.toReal 1 then
    let arg := c.getAppArgs[0]!
    if let some (arg', h) ← alignAdvSummands bPairs arg then
      let fn := c.getAppFn
      return some (mkApp fn arg', ← mkCongrArg fn h)
    return none
  if c.isAppOfArity ``HAdd.hAdd 6 then
    let args := c.getAppArgs
    let lhs := args[4]!
    let rhs := args[5]!
    let l? ← alignAdvSummands bPairs lhs
    let r? ← alignAdvSummands bPairs rhs
    match l?, r? with
    | none, none => return none
    | some (lhs', hl), none =>
      let pre := mkApp4 c.getAppFn args[0]! args[1]! args[2]! args[3]!
      let e' := mkApp2 pre lhs' rhs
      let h ← mkCongrFun (← mkCongrArg pre hl) rhs
      return some (e', h)
    | none, some (rhs', hr) =>
      let pre := mkApp5 c.getAppFn args[0]! args[1]! args[2]! args[3]! lhs
      let e' := mkApp pre rhs'
      let h ← mkCongrArg pre hr
      return some (e', h)
    | some (lhs', hl), some (rhs', hr) =>
      let pre := mkApp4 c.getAppFn args[0]! args[1]! args[2]! args[3]!
      let e' := mkApp2 pre lhs' rhs'
      let h ← mkCongr (← mkCongrArg pre hl) hr
      return some (e', h)
  return none

/-- Attempt to automatically discharge a ground bound goal `sumExpr ≤ B` via reducible `rfl`,
associativity/commutativity with zeros, `Game.advantage_comm` alignment, or `ring` (on `ℝ≥0` / `ℝ`),
without unfolding `def`s. -/
private meta def tryAutoCloseBound (boundGoal : MVarId) (mode : HopMode)
    (sumExpr B : Expr) : TacticM Bool := boundGoal.withContext do
  let s₀ ← instantiateMVars sumExpr
  let b ← instantiateMVars B
  if s₀.hasExprMVar || b.hasExprMVar then
    return false
  let saved ← saveState
  let aligned? ← match mode with
    | .advNNReal | .advReal => alignAdvSummands (collectAdvPairs b) s₀
    | .closeTo _ => pure none
  let (curGoal, s) ← match aligned? with
    | none => pure (boundGoal, s₀)
    | some (s', hsEq) =>
      let prop' ← mkAppM ``LE.le #[s', b]
      let g' ← mkFreshExprSyntheticOpaqueMVar prop'
      boundGoal.assign (← mkAppM ``Eq.trans_le #[hsEq, g'])
      pure (g'.mvarId!, s')
  if ← withNewMCtxDepth (withReducibleAndInstances (isDefEq s b)) then
    let _ ← withReducibleAndInstances (isDefEq s b)
    curGoal.assign (← mkAppM ``le_refl #[s])
    return true
  try
    Term.withoutErrToSorry do
      let [eqGoal] ← curGoal.apply (← mkAppOptM ``le_of_eq #[none, none, some s, some b])
        | failure
      setGoals [eqGoal]
      match mode with
      | .advNNReal | .advReal =>
        let hasSubtypeVal := (s.find? (·.isConstOf ``Subtype.val)).isSome ||
          (b.find? (·.isConstOf ``Subtype.val)).isSome
        if hasSubtypeVal then
          evalTactic (← `(tactic| ((try simp only [NNReal.val_eq_coe]); ring)))
        else
          evalTactic (← `(tactic| ring))
      | .closeTo _ =>
        evalTactic (← `(tactic|
          ((try simp only [add_zero, zero_add]); with_reducible_and_instances ac_rfl)))
      unless (← getUnsolvedGoals).isEmpty do failure
    return true
  catch _ =>
    saved.restore
    return false

/-- Bracketed or comma-separated list of intermediate games or distributions for `game_trans`. -/
syntax gameTransMids := ("[" term,* "]") <|> (term,+)
/-- Bracketed list or single hop proof term for `game_trans ... using ...`. -/
syntax gameTransUsing := ("[" term,* "]") <|> term

/-- Step a `Game.advantage`, `(Game.advantage : ℝ)`, `Encryption.advantage`,
`Game.succProbability`, `(Game.succProbability : ℝ)`, or `CloseTo` goal across an explicit list of
intermediate games or distributions:

* `game_trans [g₁, g₂, ...]` (or `game_trans g₁, g₂, ...`) creates one hop subgoal per step
  (`G₀ → g₁`, `g₁ → g₂`, ..., `gₘ → Gₖ`) followed by a trailing bound subgoal
  `?ε₀ + ?ε₁ + ... + ?εₘ ≤ B`. One-sided `Game.succProbability G₀ ≤ B` goals (when `B` does not
  already add `Game.succProbability G₁`) hop from `G₀` to `PMF.pure false` and accept
  `Game.succProbability gₘ ≤ ε` hop proofs at `PMF.pure false`.
* `game_trans [g₁, g₂] using [h₀, h₁, h₂]` discharges hop subgoals directly (use `_` to leave a
  hop open), automatically orienting reversed `Game.advantage_comm` / `CloseTo.symm` bounds,
  lifting `ℝ≥0` advantage bounds to `ℝ`, turning equalities `A = B` into `0` error, and closing
  the trailing sum bound when it holds by `rfl`, `ac_rfl`, or `ring`.
* `game_trans` (with no intermediates) unfolds `Encryption.advantage`, reduces
  `Game.succProbability G₀ ≤ Game.succProbability G₁ + B` to `Game.advantage G₀ G₁ ≤ B`, or
  reduces `Game.succProbability G₀ ≤ B` to `Game.advantage G₀ (PMF.pure false) ≤ B`
  (`game_trans using [h]` also closes a single hop up to symmetry). -/
syntax (name := gameTrans) "game_trans" (ppSpace colGt gameTransMids)?
  (colGt " using " gameTransUsing)? : tactic

private meta def extractTermArrayMids (stx? : Option (TSyntax ``gameTransMids)) :
    TacticM (Array Syntax) := do
  let some stx := stx? | return #[]
  match stx with
  | `(gameTransMids| [$ts,*]) => return ts.getElems.map (·.raw)
  | `(gameTransMids| $ts:term,*) => return ts.getElems.map (·.raw)
  | _ => throwUnsupportedSyntax

private meta def extractTermArrayUsing (stx? : Option (TSyntax ``gameTransUsing)) :
    TacticM (Option (Array Syntax)) := do
  let some stx := stx? | return none
  match stx with
  | `(gameTransUsing| [$ts,*]) => return some (ts.getElems.map (·.raw))
  | `(gameTransUsing| $t:term) => return some #[t.raw]
  | _ => throwUnsupportedSyntax

elab_rules : tactic
  | `(tactic| game_trans $[$mids?]? $[using $using?]?) => withMainContext do
    let origGoals ← getUnsolvedGoals
    let mainGoal ← getMainGoal
    let siblingGoals := origGoals.drop 1
    let midStxs ← extractTermArrayMids mids?
    let usingStxs? ← extractTermArrayUsing using?
    let (curGoal, info) ← prepareGameTransGoal mainGoal
    -- Pure 0-intermediate conversion without `using`: leave the single converted goal directly!
    if midStxs.isEmpty && usingStxs?.isNone then
      unless info.converted do
        throwError "game_trans: supply at least one intermediate game/distribution \
          (e.g. `game_trans [g₁]`) or `using [h]`"
      setGoals (curGoal :: siblingGoals)
      return
    curGoal.withContext do
      let itemTy ← info.mode.itemType
      let mut pts : Array Expr := #[info.start]
      for mStx in midStxs do
        let gExpr ← Term.elabTermEnsuringType mStx (some itemTy)
        Term.synthesizeSyntheticMVarsNoPostponing
        pts := pts.push (← instantiateMVars gExpr)
      pts := pts.push info.stop
      let numHops := pts.size - 1
      if let some uArr := usingStxs? then
        if uArr.size != numHops then
          throwError "game_trans: {midStxs.size} intermediate item(s) produce {numHops} hop(s), \
            but `using` supplied {uArr.size} term(s)"
      let boundTy := info.mode.boundType
      let mut epsMVars : Array Expr := #[]
      let mut hopGoals : Array MVarId := #[]
      let mut hopProofs : Array Expr := #[]
      for i in [0:numHops] do
        let eps ← mkFreshExprMVar boundTy .natural (Name.mkSimple s!"ε_{i}")
        let hopProp ← info.mode.mkHopProp pts[i]! pts[i + 1]! eps
        let hopMVar ← mkFreshExprSyntheticOpaqueMVar hopProp (Name.mkSimple s!"hop_{i}")
        epsMVars := epsMVars.push eps
        hopGoals := hopGoals.push hopMVar.mvarId!
        hopProofs := hopProofs.push hopMVar
      -- Build left-associated sum `?ε₀ + ?ε₁ + ...`
      let mut sumExpr := epsMVars[0]!
      for i in [1:numHops] do
        sumExpr ← mkAppM ``HAdd.hAdd #[sumExpr, epsMVars[i]!]
      let boundProp ← mkAppM ``LE.le #[sumExpr, info.bound]
      let boundMVar ← mkFreshExprSyntheticOpaqueMVar boundProp `bound
      -- Chain the triangle proof across all hops + `boundMVar`.
      let mut accPrf := hopProofs[0]!
      for i in [1:numHops] do
        accPrf ← match info.mode with
          | .advNNReal =>
            let hTri ← mkAppM ``Game.advantage_triangle #[pts[0]!, pts[i]!, pts[i + 1]!]
            let hAdd ← mkAppM ``add_le_add #[accPrf, hopProofs[i]!]
            mkAppM ``le_trans #[hTri, hAdd]
          | .advReal =>
            mkAppM ``Game.coe_advantage_triangle_add
              #[pts[0]!, pts[i]!, pts[i + 1]!, accPrf, hopProofs[i]!]
          | .closeTo _ =>
            mkAppM ``CloseTo.trans #[accPrf, hopProofs[i]!]
      let fullPrf ← match info.mode with
        | .advNNReal | .advReal => mkAppM ``le_trans #[accPrf, boundMVar]
        | .closeTo _ => mkAppM ``CloseTo.mono #[accPrf, boundMVar]
      curGoal.assign fullPrf
      -- Discharge any non-hole `using` terms.
      let mut remainingHops : List MVarId := []
      if let some uArr := usingStxs? then
        for i in [0:numHops] do
          let uStx := uArr[i]!
          if uStx.isOfKind ``Lean.Parser.Term.hole then
            remainingHops := remainingHops ++ [hopGoals[i]!]
          else
            solveHopGoalWith hopGoals[i]! info.mode pts[i]! pts[i + 1]! epsMVars[i]! uStx
      else
        remainingHops := hopGoals.toList
      -- Instantiate metavariables in `boundMVar`'s target; auto-close if ground and immediate.
      let boundClosed ← if remainingHops.isEmpty then
          tryAutoCloseBound boundMVar.mvarId! info.mode sumExpr info.bound
        else
          pure false
      let mut finalNewGoals := remainingHops
      if !boundClosed then
        let instBoundTy ← instantiateMVars (← boundMVar.mvarId!.getType)
        let bGoal ← boundMVar.mvarId!.replaceTargetDefEq instBoundTy
        finalNewGoals := finalNewGoals ++ [bGoal]
      setGoals (finalNewGoals ++ siblingGoals)

end Cslib.Tactic.GameHop

end
