/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.Realization.Absorb
public import Mathlib.Tactic.FinCases

/-!
# The `realize` tactic

`realize` proves a goal `Realizes B p input output safe work` for a loop-free memory client `p`.
It walks the client syntax, unfolding definitions: `bind`, `pure`, the four memory queries and
`if` on a word equality or comparison. It keeps the argument layout itself: after each bind the
live words are the previous ones followed by the answer's encoding (`WordEncoding`), and every
operand is located among them by definitional equality. An operand that is not a live word is
first computed by an inserted `pure`, which leaves the program unchanged up to definitional
equality.

Each `pure` is certified by a `GlueComputable` proof assembled from the closure rules of
`Complexity.Computability.WordRAM.Glue`, one rule per syntactic form: projections, constants, and
the exact- or standard-basis arithmetic and bitwise operations. Exact subtraction, division and
remainder add their definedness conditions to the visible domain. The common envelope is the
maximum of every intermediate value; `realize` proves that it fits from the fit of the live
words, from the domain, and from the fit of the values it cannot derive, which become the visible
fit conditions. A value is derived when another fitting value dominates it, for example `a - b`
and `b` by `a`, or the summands by a sum.

Local work is absorbed (`Realizes.mono_mul`): every certificate built by `realize` has local work
`0`, so any local-work grading in the goal is accepted. Intermediate domains are stated in the
client's own terms, with the replies of earlier queries written as `s.mem a`, `s.frontier` and
updated memories.

After the composition, `realize` introduces `w d s hwords hmem h`: the word width, the
environment, the memory, the fit of the input words, memory well-formedness, and the goal's
domain. It splits the conjunctions and `if`s of the synthesized domain and leaves each remaining
condition as a goal. There is no search: every form has one rule, and an unsupported form is
reported with its subterm.

## Main definitions

* `realize`: the tactic.
-/

public meta section

namespace Cslib.Tactic.Realize

open Lean Meta Elab Tactic Cslib.DataStructure Cslib.WordRAM Cslib.WordRAM.Realization

/-- The live words of a realization environment. -/
private structure Env where
  /-- The environment type. -/
  ty : Expr
  /-- The number of live words. -/
  k : Nat
  /-- The encoding `ty ↪ (Fin k → ℕ)`. -/
  input : Expr
  /-- `atoms[i]` is `fun d => input d i` in weak-head normal form. -/
  atoms : Array Expr

/-- A certificate built by `realize`. -/
private structure Out where
  /-- A proof of `Realizes B prog input output safe (fun _ _ => 0)`. -/
  proof : Expr
  /-- The output encoding. -/
  output : Expr
  /-- The domain `fun w d s => …`, in the client's terms, definitionally equal to the proof's. -/
  safe : Expr

/-- `(i : Fin n)` as a numeral. -/
private def finLit (n i : Nat) : MetaM Expr :=
  mkNumeral (mkApp (mkConst ``Fin) (mkNatLit n)) i

/-- The number of words of an encoding `α ↪ (Fin l → ℕ)`. -/
private def encodingWidth (enc : Expr) : MetaM Nat := do
  let ty ← instantiateMVars (← inferType enc)
  let some (_, tgt) := ty.app2? ``Function.Embedding
    | throwError "realize: expected an encoding `α ↪ (Fin l → ℕ)`, got{indentExpr ty}"
  let n ← instantiateMVars tgt.bindingDomain!.appArg!
  if let some l ← (evalNat n).run then return l
  let some l ← (evalNat (← whnf n)).run
    | throwError "realize: the encoding width is not a numeral in{indentExpr ty}"
  return l

/-- The atoms of `enc x`, for `x` an expression in the environment variable. -/
private def encodingAtoms (enc x : Expr) (l : Nat) : MetaM (Array Expr) :=
  (Array.range l).mapM fun j => do
    whnf (mkApp (← mkAppM ``DFunLike.coe #[enc, x]) (← finLit l j))

/-- Locate an expression among the live words. -/
private def findAtom (atoms : Array Expr) (e : Expr) : MetaM (Option Nat) := do
  let e' ← whnf e
  for h : i in [0:atoms.size] do
    if ← withNewMCtxDepth (isDefEq e' atoms[i]) then return some i
  return none

/-- Reduce `(a, b).1` and `(a, b).2` everywhere. -/
private def reducePairs (e : Expr) : MetaM Expr :=
  Meta.transform e (post := fun e => do
    if e.isAppOfArity ``Prod.fst 3 then
      if let some (_, _, a, _) := e.appArg!.app4? ``Prod.mk then return .done a
    if e.isAppOfArity ``Prod.snd 3 then
      if let some (_, _, _, b) := e.appArg!.app4? ``Prod.mk then return .done b
    if let .proj ``Prod i s := e then
      if let some (_, _, a, b) := s.app4? ``Prod.mk then return .done (if i == 0 then a else b)
    return .continue)

/-- `φ₀ ∧ (φ₁ ∧ … φₙ)`, or `True`. -/
private def conj : List Expr → Expr
  | [] => mkConst ``True
  | [f] => f
  | f :: fs => mkAnd f (conj fs)

/-- Project the conjunct at `pos` out of a proof of `conj` of `size` facts. -/
private def conjunct (h : Expr) (size pos : Nat) : MetaM Expr := do
  let mut h := h
  for _ in [0:pos] do h ← mkAppM ``And.right #[h]
  if pos + 1 == size then return h
  mkAppM ``And.left #[h]

/-! ### Word glue -/

/-- The supported glue operations. -/
private inductive GOp
  | add | sub | mul | div | mod | and | or | xor | shiftLeft | shiftRight

/-- The glue rule name for an operation in the exact or standard basis. -/
private def GOp.rule (exact : Bool) : GOp → Name
  | .add => if exact then ``GlueComputable.add else ``GlueComputable.add_standard
  | .sub => if exact then ``GlueComputable.sub else ``GlueComputable.sub_standard
  | .mul => if exact then ``GlueComputable.mul else ``GlueComputable.mul_standard
  | .div => if exact then ``GlueComputable.div else ``GlueComputable.div_standard
  | .mod => if exact then ``GlueComputable.mod else ``GlueComputable.mod_standard
  | .and => if exact then ``GlueComputable.and else ``GlueComputable.and_standard
  | .or => if exact then ``GlueComputable.or else ``GlueComputable.or_standard
  | .xor => if exact then ``GlueComputable.xor else ``GlueComputable.xor_standard
  | .shiftLeft =>
    if exact then ``GlueComputable.shiftLeft else ``GlueComputable.shiftLeft_standard
  | .shiftRight =>
    if exact then ``GlueComputable.shiftRight else ``GlueComputable.shiftRight_standard

/-- The operator's heterogeneous-operation function. -/
private def GOp.fn : GOp → Name
  | .add => ``HAdd.hAdd | .sub => ``HSub.hSub | .mul => ``HMul.hMul | .div => ``HDiv.hDiv
  | .mod => ``HMod.hMod | .and => ``HAnd.hAnd | .or => ``HOr.hOr | .xor => ``HXor.hXor
  | .shiftLeft => ``HShiftLeft.hShiftLeft | .shiftRight => ``HShiftRight.hShiftRight

/-- Whether the result is at most the left operand. -/
private def GOp.belowLeft : GOp → Bool
  | .sub | .div | .mod | .and | .shiftRight => true
  | _ => false

/-- A glue expression over the live words. -/
private inductive GNode
  /-- A live word. -/
  | reg (i : Nat) (user : Expr)
  /-- A value independent of the environment. -/
  | const (c : Expr) (zero : Bool)
  /-- A binary operation. -/
  | bin (op : GOp) (user : Expr) (a b : GNode)

/-- The expression in the client's terms. -/
private def GNode.user : GNode → Expr
  | .reg _ u | .const u _ | .bin _ u _ _ => u

/-- Recognize a binary operation on natural numbers. -/
private def binOp? (e : Expr) : Option (GOp × Expr × Expr) :=
  [GOp.add, .sub, .mul, .div, .mod, .and, .or, .xor, .shiftLeft, .shiftRight].findSome? fun op =>
    if e.isAppOfArity op.fn 6 && (e.getArg! 0).isConstOf ``Nat then
      some (op, e.getArg! 4, e.getArg! 5)
    else none

/-- Parse a word-valued expression over the live words. -/
private partial def analyze (atoms : Array Expr) (d : Expr) (e : Expr) : MetaM GNode := do
  if let some i ← findAtom atoms e then return .reg i e
  if !e.containsFVar d.fvarId! then
    return .const e (← withNewMCtxDepth (isDefEq e (mkNatLit 0)))
  if let some (op, a, b) := binOp? e then
    return .bin op e (← analyze atoms d a) (← analyze atoms d b)
  let e' ← whnfR e
  if e' != e then return ← analyze atoms d e'
  throwError "realize: cannot compute{indentExpr e}\nfrom the live words{indentD
    (MessageData.joinSep (atoms.toList.map fun a => m!"{a}") ", ")}"

/-- A glue node numbered in depth-first order, with its value over the word vector. -/
private inductive ANode
  /-- A live word. -/
  | reg (idx : Nat) (val : Expr) (i : Nat)
  /-- A constant. -/
  | const (idx : Nat) (val : Expr) (zero : Bool)
  /-- A binary operation; `dom` numbers its definedness condition, if any. -/
  | bin (idx : Nat) (val : Expr) (op : GOp) (dom : Option Nat) (a b : ANode)

/-- The depth-first number. -/
private def ANode.idx : ANode → Nat
  | .reg i .. | .const i .. | .bin i .. => i

/-- The value over the word vector. -/
private def ANode.val : ANode → Expr
  | .reg _ v _ | .const _ v _ | .bin _ v .. => v

/-- The values of all nodes in depth-first order and the definedness conditions, over the word
vector and in the client's terms. -/
private structure Annot where
  /-- Node values over the word vector. -/
  vals : Array Expr := #[]
  /-- Definedness conditions over the word vector. -/
  domV : Array Expr := #[]
  /-- Definedness conditions in the client's terms. -/
  domU : Array Expr := #[]

/-- Number the nodes and compute their values over the word vector `v`. -/
private partial def annotate (exact : Bool) (k : Nat) (v : Expr) : GNode → StateT Annot MetaM ANode
  | .reg i _ => do
    let val := mkApp v (← finLit k i)
    let idx := (← get).vals.size
    modify fun st => { st with vals := st.vals.push val }
    return .reg idx val i
  | .const c zero => do
    let idx := (← get).vals.size
    modify fun st => { st with vals := st.vals.push c }
    return .const idx c zero
  | .bin op _ a b => do
    let idx := (← get).vals.size
    modify fun st => { st with vals := st.vals.push default }
    let a' ← annotate exact k v a
    let b' ← annotate exact k v b
    let val ← mkAppM op.fn #[a'.val, b'.val]
    modify fun st => { st with vals := st.vals.set! idx val }
    let dom? ← if exact then
        match op with
        | .sub => pure (some (← mkAppM ``LE.le #[b'.val, a'.val],
            ← mkAppM ``LE.le #[b.user, a.user]))
        | .div | .mod => pure (some (← mkAppM ``Ne #[b'.val, mkNatLit 0],
            ← mkAppM ``Ne #[b.user, mkNatLit 0]))
        | _ => pure none
      else pure none
    let dom ← match dom? with
      | some (fv, fu) => do
        let n := (← get).domV.size
        modify fun st => { st with domV := st.domV.push fv, domU := st.domU.push fu }
        pure (some n)
      | none => pure none
    return .bin idx val op dom a' b'

/-- The node's value in the client's terms, by depth-first number. -/
private partial def userVals (g : GNode) (acc : Array Expr := #[]) : Array Expr :=
  match g with
  | .reg _ u => acc.push u
  | .const c _ => acc.push c
  | .bin _ u a b => userVals b (userVals a (acc.push u))

/-- The nodes whose fit is a visible condition: `covered` says that a dominating value fits. -/
private partial def needNodes (exact : Bool) (n : ANode) (covered : Bool)
    (acc : Array Nat := #[]) : Array Nat :=
  match n with
  | .reg .. => acc
  | .const idx _ zero => if zero || covered then acc else acc.push idx
  | .bin idx _ op _ a b =>
    let acc := if op.belowLeft || covered then acc else acc.push idx
    match op with
    | .add | .or =>
      needNodes exact b true (needNodes exact a true acc)
    | .shiftLeft => needNodes exact b false (needNodes exact a true acc)
    | .sub => needNodes exact b exact (needNodes exact a false acc)
    | _ => needNodes exact b false (needNodes exact a false acc)

/-- Fit proofs of all nodes, indexed by depth-first number, mirroring `needNodes`. `self?` is the
node's fit from a dominating value. -/
private partial def fitProofs (exact : Bool) (k : Nat) (w hregs hdom hneed : Expr) (ndom : Nat)
    (needIdx : Array Nat) (n : ANode) (self? : Option Expr) :
    StateT (Array Expr) MetaM Expr := do
  let fitNeed (idx : Nat) : MetaM Expr := do
    let some pos := needIdx.findIdx? (· == idx) | throwError "realize: internal fit error"
    conjunct hneed needIdx.size pos
  let fitLe (p h : Expr) : MetaM Expr := mkAppM ``Cslib.WordRAM.Fits.of_le #[p, h]
  let record (idx : Nat) (p : Expr) : StateT (Array Expr) MetaM Expr := do
    modify fun acc => acc.set! idx p
    return p
  match n with
  | .reg idx _ i => record idx (mkApp hregs (← finLit k i))
  | .const idx _ zero =>
    if zero then
      record idx (← mkAppM ``Cslib.WordRAM.fits_zero #[w])
    else match self? with
      | some p => record idx p
      | none => record idx (← fitNeed idx)
  | .bin idx _ op dom a b =>
    if op.belowLeft then
      let pa ← fitProofs exact k w hregs hdom hneed ndom needIdx a none
      let pbDom ← match op, dom with
        | .sub, some di => pure (some (← fitLe pa (← conjunct hdom ndom di)))
        | _, _ => pure none
      let _ ← fitProofs exact k w hregs hdom hneed ndom needIdx b pbDom
      let le ← match op with
        | .sub => mkAppM ``Nat.sub_le #[a.val, b.val]
        | .div => mkAppM ``Nat.div_le_self #[a.val, b.val]
        | .mod => mkAppM ``Nat.mod_le #[a.val, b.val]
        | .and => mkAppOptM ``Nat.and_le_left #[a.val, b.val]
        | _ => mkAppM ``Nat.shiftRight_le #[a.val, b.val]
      record idx (← fitLe pa le)
    else
      let self ← match self? with
        | some p => pure p
        | none => fitNeed idx
      match op with
      | .add =>
        let _ ← fitProofs exact k w hregs hdom hneed ndom needIdx a
          (some (← fitLe self (← mkAppM ``Nat.le_add_right #[a.val, b.val])))
        let _ ← fitProofs exact k w hregs hdom hneed ndom needIdx b
          (some (← fitLe self (← mkAppM ``Nat.le_add_left #[b.val, a.val])))
      | .or =>
        let _ ← fitProofs exact k w hregs hdom hneed ndom needIdx a
          (some (← fitLe self (← mkAppOptM ``Nat.left_le_or #[a.val, b.val])))
        let _ ← fitProofs exact k w hregs hdom hneed ndom needIdx b
          (some (← fitLe self (← mkAppOptM ``Nat.right_le_or #[a.val, b.val])))
      | .shiftLeft =>
        let _ ← fitProofs exact k w hregs hdom hneed ndom needIdx a
          (some (← fitLe self (← mkAppOptM ``Nat.le_shiftLeft #[a.val, b.val])))
        let _ ← fitProofs exact k w hregs hdom hneed ndom needIdx b none
      | _ =>
        let _ ← fitProofs exact k w hregs hdom hneed ndom needIdx a none
        let _ ← fitProofs exact k w hregs hdom hneed ndom needIdx b none
      record idx self

/-- `max` on natural numbers through the linear order, as in `le_max_left` and `max_lt`. -/
private def natMax : MetaM Expr := do
  let nat := mkConst ``Nat
  mkAppOptM ``Max.max #[nat, ← mkAppOptM ``LinearOrder.toMax #[nat, none]]

/-- `max n₀ (max n₁ … nₘ)` from position `i`. -/
private partial def maxChain (maxFn : Expr) (vals : Array Expr) (i : Nat := 0) : Expr :=
  if i + 1 ≥ vals.size then vals[i]! else mkApp2 maxFn vals[i]! (maxChain maxFn vals (i + 1))

/-- `vals[pos] ≤ maxChain vals i`. -/
private partial def memProof (maxFn : Expr) (vals : Array Expr) (pos : Nat) (i : Nat := 0) :
    MetaM Expr := do
  if i + 1 ≥ vals.size then return ← mkAppM ``le_refl #[vals[i]!]
  if pos == i then return ← mkAppM ``le_max_left #[vals[i]!, maxChain maxFn vals (i + 1)]
  mkAppOptM ``le_max_of_le_right #[none, none, none, vals[i]!, none,
    ← memProof maxFn vals pos (i + 1)]

/-- `Fits w (maxChain vals i)` from the fit of every value. -/
private partial def fitChain (fits : Array Expr) (i : Nat := 0) : MetaM Expr := do
  if i + 1 ≥ fits.size then return fits[i]!
  mkAppM ``max_lt #[fits[i]!, ← fitChain fits (i + 1)]

/-- The `GlueComputable` certificate of a node, one closure rule per form. -/
private partial def glueProof (exact : Bool) (B kE P bound : Expr) (k : Nat)
    (hb : Nat → MetaM Expr) (hd : Nat → MetaM Expr) : ANode → MetaM Expr
  | .reg idx _ i => do
    mkAppOptM ``GlueComputable.proj #[B, kE, P, bound, ← finLit k i, ← hb idx]
  | .const idx c _ => do
    mkAppOptM ``GlueComputable.const #[B, kE, P, bound, c, ← hb idx]
  | .bin idx _ op dom a b => do
    let ga ← glueProof exact B kE P bound k hb hd a
    let gb ← glueProof exact B kE P bound k hb hd b
    match dom with
    | some di => mkAppM (op.rule exact) #[ga, gb, ← hd di, ← hb idx]
    | none => mkAppM (op.rule exact) #[ga, gb, ← hb idx]

/-- `![x₀, …, xₙ]`. -/
private def vecOf (xs : List Expr) : MetaM Expr := do
  match xs with
  | [] => mkAppOptM ``Matrix.vecEmpty #[mkConst ``Nat]
  | x :: xs => mkAppM ``Matrix.vecCons #[x, ← vecOf xs]

/-- `∀ i, GlueComputable B (fun v => ![f₀ v, …] i) P bound` from the coordinate certificates. -/
private partial def vecCoords (B kE P bound v : Expr) (vals proofs : Array Expr) (j : Nat) :
    MetaM Expr := do
  let l := vals.size
  withLocalDeclD `i (mkApp (mkConst ``Fin) (mkNatLit (l - j))) fun i => do
    let f ← mkLambdaFVars #[v] vals[j]!
    if j + 1 == l then
      return ← mkLambdaFVars #[i] (← mkAppOptM ``GlueComputable.vec_single
        #[B, kE, P, bound, f, proofs[j]!, i])
    let g ← mkLambdaFVars #[v] (← vecOf (vals.toList.drop (j + 1)))
    let tail ← vecCoords B kE P bound v vals proofs (j + 1)
    mkLambdaFVars #[i] (← mkAppOptM ``GlueComputable.vec_cons
      #[B, kE, P, bound, f, mkNatLit (l - j - 1), g, proofs[j]!, tail, i])

/-- Replace the maximal non-constructor subterms of `e` by local variables, then continue with
the skeleton and the pairs (variable, replaced subterm). -/
private partial def withSkeleton {β : Type} (e : Expr) (acc : Array (Expr × Expr))
    (k : Expr → Array (Expr × Expr) → MetaM β) : MetaM β := do
  let e' ← whnfR e
  if let .const c _ := e'.getAppFn then
    if let some (.ctorInfo info) := (← getEnv).find? c then
      if info.induct != ``Nat then
        let args := e'.getAppArgs
        let rec go (j : Nat) (newArgs : Array Expr) (acc : Array (Expr × Expr)) : MetaM β :=
          if h : j < args.size then
            if j < info.numParams then go (j + 1) (newArgs.push args[j]) acc
            else withSkeleton args[j] acc fun a' acc' => go (j + 1) (newArgs.push a') acc'
          else k (mkAppN e'.getAppFn newArgs) acc
        return ← go 0 #[] acc
  withLocalDeclD `z (← inferType e) fun z => k z (acc.push (z, e))

/-- The coordinates of `enc a` in the client's terms. Constructor applications are kept as a
skeleton so that the encoding reduces without unfolding the client's arithmetic. -/
private def coordinates (enc a : Expr) (l : Nat) : MetaM (Array Expr) :=
  withSkeleton a #[] fun skel holes => do
    let cs ← encodingAtoms enc skel l
    return cs.map fun c => c.replaceFVars (holes.map (·.1)) (holes.map (·.2))

/-! ### Realization -/

/-- The basis of the goal and whether it is the exact basis. -/
private structure Ctx where
  /-- The basis. -/
  basis : Expr
  /-- Whether the basis is `.exact`. -/
  exact : Bool
  /-- Whether the basis is `.standard`. -/
  standard : Bool

/-- `fun _ _ => 0`. -/
private def zeroWork (δ : Expr) : MetaM Expr :=
  withLocalDeclD `d δ fun d => withLocalDeclD `s (mkConst ``Memory.State) fun s =>
    mkLambdaFVars #[d, s] (mkNatLit 0)

/-- `fun _ _ _ => True`. -/
private def trueSafe (δ : Expr) : MetaM Expr :=
  withLocalDeclD `w (mkConst ``Nat) fun w => withLocalDeclD `d δ fun d =>
    withLocalDeclD `s (mkConst ``Memory.State) fun s => mkLambdaFVars #[w, d, s] (mkConst ``True)

/-- The input encoding of the continuation of a bind. -/
private def appendInput (env : Env) (answer : Expr) (l : Nat) : MetaM Expr := do
  let prod ← mkAppM ``Function.Embedding.prodMap #[env.input, answer]
  let app ← mkAppM ``Equiv.toEmbedding
    #[← mkAppOptM ``Fin.appendEquiv #[mkConst ``Nat, mkNatLit env.k, mkNatLit l]]
  mkAppM ``Function.Embedding.trans #[prod, app]

/-- The environment of the continuation of a bind whose answer has type `α`. -/
private def extend (env : Env) (α answer : Expr) (l : Nat) : MetaM Env := do
  let ty ← mkAppM ``Prod #[env.ty, α]
  let input ← appendInput env answer l
  let atoms ← withLocalDeclD `x ty fun x => do
    let x1 ← mkAppM ``Prod.fst #[x]
    let x2 ← mkAppM ``Prod.snd #[x]
    let old ← env.atoms.mapM fun a => whnf (a.beta #[x1])
    let new ← encodingAtoms answer x2 l
    (old ++ new).mapM fun a => mkLambdaFVars #[x] a
  return { ty, k := env.k + l, input, atoms }

/-- The reply and next memory of a client from memory `s`, in the client's terms. -/
private def replyState (m s : Expr) : MetaM (Expr × Expr) := do
  let m' ← whnfR m
  let generic := do
    let spec ← mkAppM ``Memory.spec #[mkNatLit 0]
    return (← mkAppM ``StateTransitionSpec.clientResult #[spec, s, m],
      ← mkAppM ``StateTransitionSpec.clientState #[spec, s, m])
  let mem ← mkAppM ``Memory.State.mem #[s]
  let frontier ← mkAppM ``Memory.State.frontier #[s]
  if m'.isAppOfArity ``PFunctor.FreeM.lift 2 then
    let op ← whnfR m'.appArg!
    if let some a := op.app1? ``Memory.Op.read then return (mkApp mem a, s)
    if let some (a, v) := op.app2? ``Memory.Op.write then
      return (mkConst ``Unit.unit,
        ← mkAppM ``Memory.State.mk #[← mkAppM ``Function.update #[mem, a, v], frontier])
    if let some n := op.app1? ``Memory.Op.alloc then
      return (frontier, ← mkAppM ``Memory.State.mk
        #[← mkAppM ``Cslib.WordRAM.clear #[mem, frontier, n], ← mkAppM ``HAdd.hAdd #[frontier, n]])
    if let some n := op.app1? ``Memory.Op.allocDirty then
      return (frontier, ← mkAppM ``Memory.State.mk #[mem, ← mkAppM ``HAdd.hAdd #[frontier, n]])
    return ← generic
  if m'.isAppOfArity ``Pure.pure 4 then return (m'.appArg!, s)
  if m'.isAppOfArity ``PFunctor.FreeM.pure 3 then return (m'.appArg!, s)
  generic

/-- The result type of a memory client. -/
private def resultType (body : Expr) : MetaM Expr := do
  let ty ← whnfR (← inferType body)
  unless ty.isAppOfArity ``PFunctor.FreeM 2 do
    throwError "realize: expected a memory client, got{indentExpr body}\nof type{indentExpr ty}"
  whnf ty.appArg!

/-- The encoding of an intermediate answer type. -/
private def encodingOf (α : Expr) : MetaM Expr := do
  let some inst ← synthInstance? (← mkAppM ``WordEncoding #[α])
    | throwError "realize: no `WordEncoding` instance for the answer type{indentExpr α}"
  let e ← mkAppOptM ``WordEncoding.encode #[α, inst]
  return (← unfoldProjInst? e).getD e

/-- `Bind.bind (pure a) cont` in `Memory.Prog`. -/
private def bindPure (a cont : Expr) : MetaM Expr := do
  let prog := mkConst ``Memory.Prog
  let pa ← mkAppOptM ``Pure.pure #[prog, none, mkConst ``Nat, a]
  mkAppOptM ``Bind.bind #[prog, none, mkConst ``Nat, none, pa, cont]

/-- Prove `∀ d i, output (f d) i = g i (input d)` coordinate by coordinate. -/
private def proveResult (ty : Expr) : TermElabM Expr := do
  let mvar ← mkFreshExprMVar ty
  let gs ← Tactic.run mvar.mvarId! do
    evalTactic (← `(tactic| (intro d i; fin_cases i <;> rfl)))
  unless gs.isEmpty do throwError "realize: could not match the result encoding:{indentExpr ty}"
  instantiateMVars mvar

/-- Certify `pure a` with the result encoding `out`, for the environment variable `d`. -/
private def realizePure (ctx : Ctx) (env : Env) (d : Expr) (atoms : Array Expr) (a out : Expr) :
    TermElabM Out := do
  let l ← encodingWidth out
  let coordsU ← coordinates out a l
  let gnodes ← coordsU.mapM fun c => liftMetaM (analyze atoms d c)
  unless ctx.exact || ctx.standard || gnodes.all (fun g => !(g matches .bin ..)) do
    throwError "realize: word arithmetic is certified in the exact and standard bases; the \
      goal's basis is{indentExpr ctx.basis}"
  let k := env.k
  let kE := mkNatLit k
  let B := ctx.basis
  let nat := mkConst ``Nat
  let finK := mkApp (mkConst ``Fin) kE
  let finL := mkApp (mkConst ``Fin) (mkNatLit l)
  let maxFn ← natMax
  withLocalDeclD `v (← mkArrow finK nat) fun v => do
    let (anodes, st) ← (gnodes.mapM (annotate ctx.exact k v)).run {}
    let uvals := gnodes.foldl (fun acc g => userVals g acc) #[]
    let domTy := conj st.domV.toList
    let P ← mkLambdaFVars #[v] domTy
    let bound ← mkLambdaFVars #[v]
      (if st.vals.isEmpty then mkNatLit 0 else maxChain maxFn st.vals)
    let hb (idx : Nat) : MetaM Expr := withLocalDeclD `hv domTy fun hv => do
      mkLambdaFVars #[v, hv] (← memProof maxFn st.vals idx)
    let hd (di : Nat) : MetaM Expr := withLocalDeclD `hv domTy fun hv => do
      mkLambdaFVars #[v, hv] (← conjunct hv st.domV.size di)
    let proofs ← anodes.mapM fun n => liftMetaM (glueProof ctx.exact B kE P bound k hb hd n)
    let vals := anodes.map (·.val)
    let gfun ← withLocalDeclD `i finL fun i => do
      mkLambdaFVars #[i, v] (mkApp (← vecOf vals.toList) i)
    let hcoord ← if l == 0 then
        withLocalDeclD `i finL fun i => do
          let ty ← mkAppM ``GlueComputable #[B, mkApp gfun i, P, bound]
          mkLambdaFVars #[i] (← mkAppOptM ``Fin.elim0 #[ty, i])
      else vecCoords B kE P bound v vals proofs 0
    withLocalDeclD `w nat fun w => do
      let needIdx := anodes.foldl (fun acc n => needNodes ctx.exact n false acc) #[]
      let needV ← needIdx.mapM fun i => mkAppM ``Fits #[w, st.vals[i]!]
      let needU ← needIdx.mapM fun i => mkAppM ``Fits #[w, uvals[i]!]
      let needTy := conj needV.toList
      let need ← mkLambdaFVars #[w, v] needTy
      let hregsTy ← withLocalDeclD `i finK fun i => do
        mkForallFVars #[i] (← mkAppM ``Fits #[w, mkApp v i])
      let hneed ← withLocalDeclD `hregs hregsTy fun hregs =>
        withLocalDeclD `hP domTy fun hP => withLocalDeclD `hn needTy fun hn => do
          let fits ← if st.vals.isEmpty then pure #[← mkAppM ``fits_zero #[w]] else do
            let (_, fits) ← (anodes.forM fun n => discard <|
              fitProofs ctx.exact k w hregs hP hn st.domV.size needIdx n none).run
                (Array.replicate st.vals.size default)
            pure fits
          mkLambdaFVars #[w, v, hregs, hP, hn] (← fitChain fits)
      let f ← mkLambdaFVars #[d] a
      let resTy ← withLocalDeclD `d env.ty fun d' => withLocalDeclD `i finL fun i => do
        let lhs := mkApp (← mkAppM ``DFunLike.coe #[out, f.beta #[d']]) i
        let rhs := mkApp2 gfun i (← mkAppM ``DFunLike.coe #[env.input, d'])
        mkForallFVars #[d', i] (← mkEq lhs rhs)
      let hresult ← proveResult resTy
      let proof ← mkAppM ``Realizes.pure₀
        #[env.input, out, f, gfun, need, hresult, hcoord, hneed]
      let safe ← withLocalDeclD `s (mkConst ``Memory.State) fun s =>
        mkLambdaFVars #[w, d, s] (mkAnd (conj st.domU.toList) (conj needU.toList))
      return { proof, output := out, safe }

/-- The output encoding of a certificate. -/
private def outputOf (proof : Expr) : MetaM Expr := do
  let ty ← instantiateMVars (← inferType proof)
  unless ty.isAppOfArity ``Realizes 10 do throwError "realize: internal error, not a certificate"
  return ty.getArg! 7

/-- Check a query's output encoding against the required one. -/
private def checkOutput (proof : Expr) (output? : Option Expr) : MetaM Expr := do
  let out ← outputOf proof
  if let some o := output? then
    unless ← isDefEq out o do
      throwError "realize: the query returns its answer encoded by{indentExpr out}\n\
        but the goal requires{indentExpr o}"
  return out

/-- The comparison of a branch condition: equality or `<`, with its operands. -/
private def parseCond (c : Expr) : MetaM (Name × Expr × Expr) := do
  if let some (ty, a, b) := c.eq? then
    if (← whnfR ty).isConstOf ``Nat then return (``Cond.eq, a, b)
  if c.isAppOfArity ``LT.lt 4 && (c.getArg! 0).isConstOf ``Nat then
    return (``Cond.lt, c.getArg! 2, c.getArg! 3)
  if c.isAppOfArity ``GT.gt 4 && (c.getArg! 0).isConstOf ``Nat then
    return (``Cond.lt, c.getArg! 3, c.getArg! 2)
  throwError "realize: a branch condition must be `a = b`, `a < b` or `a > b` on words, \
    got{indentExpr c}"

/-- Rebuild a branch condition with new operands. -/
private def rebuildCond (c a b : Expr) : MetaM Expr := do
  if c.isEq then mkEq a b
  else if c.isAppOfArity ``LT.lt 4 then mkAppM ``LT.lt #[a, b]
  else mkAppM ``GT.gt #[b, a]

/-- Whether the head is a client form `realize` handles directly. -/
private def isClientForm (e : Expr) : Bool :=
  e.isAppOfArity ``Bind.bind 6 || e.isAppOfArity ``PFunctor.FreeM.bind 5 ||
  e.isAppOfArity ``Pure.pure 4 || e.isAppOfArity ``PFunctor.FreeM.pure 3 ||
  e.isAppOfArity ``PFunctor.FreeM.lift 2 || e.isAppOfArity ``PFunctor.FreeM.liftBind 4 ||
  e.isAppOfArity ``ite 5

/-- Unfold definitions until a client form appears. -/
private partial def normBody (e : Expr) (fuel : Nat := 64) : MetaM Expr := do
  let e ← whnfR e
  if isClientForm e || fuel == 0 then return e
  if let some e' ← unfoldDefinition? e then return ← normBody e'.headBeta (fuel - 1)
  return e

/-- An optional answer that a `match` in the client inspects: a discriminant of an `Option` type
that depends on the environment variable `d`. -/
private def optionDiscr? (d body : Expr) : MetaM (Option Expr) := do
  let lctx ← getLCtx
  let found ← IO.mkRef (none : Option Expr)
  let _ ← Meta.transform body (pre := fun e => do
    if (← found.get).isSome then return .done e
    if let some app ← matchMatcherApp? e (alsoCasesOn := true) then
      for r in app.discrs do
        if r.containsFVar d.fvarId! &&
            (r.find? fun x => x.isFVar && !lctx.contains x.fvarId!).isNone then
          if (← whnfR (← inferType r)).isAppOfArity ``Option 1 then
            found.set (some r)
            return .done e
    return .continue)
  found.get

/-- Prove `∀ d, rhs = body` by a case split on the optional answer `r`. -/
private def proveSplit (d r ty : Expr) : MetaM Expr := do
  let mvar ← mkFreshExprMVar ty
  let (dfv, g) ← mvar.mvarId!.intro1
  let r' := r.replaceFVar d (mkFVar dfv)
  let (zs, g) ← g.generalize #[{ expr := r', xName? := `z }]
  for sg in ← g.cases zs[0]! do sg.mvarId.refl
  instantiateMVars mvar

mutual

/-- Certify a client `prog : δ → Memory.Prog α` in the environment `env`. -/
private partial def realizeProg (ctx : Ctx) (env : Env) (prog : Expr) (output? : Option Expr) :
    TermElabM Out :=
  withLocalDeclD `d env.ty fun d => do
    let atoms := env.atoms.map (·.beta #[d])
    let body ← normBody (prog.beta #[d]).headBeta
    realizeBody ctx env d atoms body output?

/-- Certify the body of a client for the environment variable `d`. -/
private partial def realizeBody (ctx : Ctx) (env : Env) (d : Expr) (atoms : Array Expr)
    (body : Expr) (output? : Option Expr) : TermElabM Out := do
  let k := env.k
  -- sequencing
  let bind? : Option (Expr × Expr) :=
    if body.isAppOfArity ``Bind.bind 6 then some (body.getArg! 4, body.getArg! 5)
    else if body.isAppOfArity ``PFunctor.FreeM.bind 5 then some (body.getArg! 3, body.getArg! 4)
    else none
  if let some (m, f) := bind? then return ← realizeBind ctx env d m f output?
  if body.isAppOfArity ``PFunctor.FreeM.liftBind 4 then
    let m ← mkAppOptM ``PFunctor.FreeM.lift #[body.getArg! 0, body.getArg! 2]
    return ← realizeBind ctx env d m (body.getArg! 3) output?
  -- return
  let pure? : Option Expr :=
    if body.isAppOfArity ``Pure.pure 4 then some body.appArg!
    else if body.isAppOfArity ``PFunctor.FreeM.pure 3 then some body.appArg!
    else none
  if let some a := pure? then
    let out ← match output? with
      | some o => pure o
      | none => encodingOf (← resultType body)
    return ← realizePure ctx env d atoms a out
  -- memory queries
  if body.isAppOfArity ``PFunctor.FreeM.lift 2 then
    let op ← whnfR body.appArg!
    let operands := op.getAppArgs
    for h : j in [0:operands.size] do
      if (← findAtom atoms operands[j]).isNone then
        let rebuilt ← withLocalDeclD `r (mkConst ``Nat) fun r => do
          mkLambdaFVars #[r] (mkApp2 (mkConst ``PFunctor.FreeM.lift
            body.getAppFn.constLevels!) (body.getArg! 0) (mkAppN op.getAppFn (operands.set j r)))
        return ← realizeBody ctx env d atoms (← bindPure operands[j] rebuilt) output?
    let idx ← operands.mapM fun a => do
      let some i ← findAtom atoms a | throwError "realize: internal error"
      finLit k i
    let input := env.input
    let kE := mkNatLit k
    let proof ← match op.getAppFn.constName? with
      | some ``Memory.Op.read =>
        mkAppOptM ``Realizes.read #[ctx.basis, env.ty, kE, input, idx[0]!]
      | some ``Memory.Op.write =>
        mkAppOptM ``Realizes.write #[ctx.basis, env.ty, kE, input, idx[0]!, idx[1]!]
      | some ``Memory.Op.alloc =>
        unless ctx.exact do
          throwError "realize: allocation is certified in the exact basis;\n\
            realize there and transfer with `Realizes.mapSimulates`"
        mkAppOptM ``Realizes.alloc #[env.ty, kE, input, idx[0]!]
      | some ``Memory.Op.allocDirty =>
        unless ctx.exact do
          throwError "realize: allocation is certified in the exact basis;\n\
            realize there and transfer with `Realizes.mapSimulates`"
        mkAppOptM ``Realizes.allocDirty #[env.ty, kE, input, idx[0]!]
      | _ => throwError "realize: unsupported memory operation{indentExpr op}"
    let output ← checkOutput proof output?
    return { proof, output, safe := ← trueSafe env.ty }
  -- branching
  if body.isAppOfArity ``ite 5 then
    let c := body.getArg! 1
    let inst := body.getArg! 2
    let t := body.getArg! 3
    let e := body.getArg! 4
    let (kind, a, b) ← parseCond c
    let ia? ← findAtom atoms a
    let ib? ← findAtom atoms b
    let (some ia, some ib) := (ia?, ib?) | do
      let x := if ia?.isNone then a else b
      let rebuilt ← withLocalDeclD `r (mkConst ``Nat) fun r => do
        let c' ← if ia?.isNone then rebuildCond c r b else rebuildCond c a r
        mkLambdaFVars #[r] (← mkAppM ``ite #[c', t, e])
      return ← realizeBody ctx env d atoms (← bindPure x rebuilt) output?
    let out ← match output? with
      | some o => pure o
      | none => encodingOf (← resultType body)
    let hp ← realizeProg ctx env (← mkLambdaFVars #[d] t) (some out)
    let hn ← realizeProg ctx env (← mkLambdaFVars #[d] e) (some out)
    let cond ← mkAppM kind #[← finLit k ia, ← finLit k ib]
    let proof ← mkAppM ``Realizes.branch₀ #[cond, hp.proof, hn.proof]
    let safe ← withLocalDeclD `w (mkConst ``Nat) fun w =>
      withLocalDeclD `s (mkConst ``Memory.State) fun s => do
        mkLambdaFVars #[w, d, s] (mkApp5 (mkConst ``ite [Level.one]) (mkSort Level.zero) c inst
          (hp.safe.beta #[w, d, s]) (hn.safe.beta #[w, d, s]))
    return { proof, output := out, safe }
  -- a `match` on an optional answer becomes a test of its presence tag
  let body ← Core.betaReduce body
  if let some r ← optionDiscr? d body then
    return ← realizeOptionSplit ctx env d atoms body r output?
  throwError "realize: unsupported client form{indentExpr body}\n\
    Expected `bind`, `pure`, a memory query, `if` on a word comparison,\n\
    or a `match` on an optional answer. Recursion on a runtime value is a loop\n\
    and needs a loop rule."

/-- Certify a client that matches on the optional answer `r`: it equals the branch on `r`'s
presence tag, with `r` replaced by `none` and by `some` of its payload. -/
private partial def realizeOptionSplit (ctx : Ctx) (env : Env) (d : Expr) (atoms : Array Expr)
    (body r : Expr) (output? : Option Expr) : TermElabM Out := do
  let rTy ← whnfR (← inferType r)
  let enc ← encodingOf rTy
  let words ← mkAppM ``DFunLike.coe #[enc, r]
  let l ← encodingWidth enc
  unless l == 2 do throwError "realize: expected a tag and payload encoding for{indentExpr r}"
  let tag := mkApp words (← finLit 2 0)
  let payload := mkApp words (← finLit 2 1)
  let cond ← mkEq tag (← mkNumeral (mkConst ``Nat) 0)
  let noneE ← mkAppOptM ``Option.none #[rTy.appArg!]
  let someE ← mkAppM ``Option.some #[payload]
  let bodyNone := body.replace fun e => if e == r then some noneE else none
  let bodySome := body.replace fun e => if e == r then some someE else none
  let rhs ← mkAppM ``ite #[cond, bodyNone, bodySome]
  let eq ← proveSplit d r (← mkForallFVars #[d] (← mkEq rhs body))
  let out ← realizeBody ctx env d atoms rhs output?
  let stmt ← mkAppM ``Realizes #[ctx.basis, ← mkLambdaFVars #[d] rhs, env.input, out.output,
    out.safe, ← zeroWork env.ty]
  let proof ← mkAppM ``Realizes.congr #[← mkExpectedTypeHint out.proof stmt, eq]
  return { out with proof }

/-- Certify `bind m f`: the first client, then the continuation over the extended environment. -/
private partial def realizeBind (ctx : Ctx) (env : Env) (d m f : Expr) (output? : Option Expr) :
    TermElabM Out := do
  let α ← resultType m
  let hP ← realizeProg ctx env (← mkLambdaFVars #[d] m) none
  let l ← encodingWidth hP.output
  let env' ← extend env α hP.output l
  let fd ← mkLambdaFVars #[d] f
  let q ← withLocalDeclD `x env'.ty fun x => do
    let x1 ← mkAppM ``Prod.fst #[x]
    let x2 ← mkAppM ``Prod.snd #[x]
    mkLambdaFVars #[x] (fd.beta #[x1, x2]).headBeta
  let hQ ← realizeProg ctx env' q output?
  let proof ← mkAppM ``Realizes.bind₀ #[hP.proof, hQ.proof]
  let safe ← withLocalDeclD `w (mkConst ``Nat) fun w =>
    withLocalDeclD `s (mkConst ``Memory.State) fun s => do
      let (r, s') ← replyState m s
      let pair ← mkAppM ``Prod.mk #[d, r]
      let sq ← reducePairs (hQ.safe.beta #[w, pair, s'])
      mkLambdaFVars #[w, d, s] (mkAnd (hP.safe.beta #[w, d, s]) sq)
  return { proof, output := hQ.output, safe }

end

/-- Split the conjunctions and `if`s of a synthesized domain into separate goals. -/
private partial def splitDomain (g : MVarId) : MetaM (List MVarId) := g.withContext do
  let t ← instantiateMVars (← g.getType)
  if t.isConstOf ``True then
    g.assign (mkConst ``True.intro)
    return []
  if t.isAppOfArity ``And 2 then
    let [g₁, g₂] ← g.apply (mkConst ``And.intro) | throwError "realize: internal split error"
    return (← splitDomain g₁) ++ (← splitDomain g₂)
  if t.isAppOfArity ``ite 5 then
    let c := t.getArg! 1
    let (gpos, gneg) ← g.byCases c `hc
    let pos ← gpos.mvarId.withContext do
      let eq ← mkAppOptM ``if_pos
        #[c, t.getArg! 2, mkFVar gpos.fvarId, t.getArg! 0, t.getArg! 3, t.getArg! 4]
      gpos.mvarId.replaceTargetEq (t.getArg! 3) eq
    let neg ← gneg.mvarId.withContext do
      let eq ← mkAppOptM ``if_neg
        #[c, t.getArg! 2, mkFVar gneg.fvarId, t.getArg! 0, t.getArg! 3, t.getArg! 4]
      gneg.mvarId.replaceTargetEq (t.getArg! 4) eq
    return (← splitDomain pos) ++ (← splitDomain neg)
  return [g]

end Cslib.Tactic.Realize

open Lean Meta Elab Tactic Cslib.WordRAM Cslib.WordRAM.Realization Cslib.Tactic.Realize in
/-- Prove `Realizes B p input output safe work` for a loop-free memory client `p`, leaving the
genuine fit and domain conditions as goals in the context `w d s hwords hmem h`. -/
elab "realize" : tactic => withMainContext do
  let goal ← getMainGoal
  let target ← instantiateMVars (← whnfR (← goal.getType))
  unless target.isAppOfArity ``Realizes 10 do
    throwError "realize: the goal is not a `Realizes` certificate:{indentExpr target}"
  let args := target.getAppArgs
  let δ := args[2]!
  let B := args[4]!
  let p := args[5]!
  let input := args[6]!
  let output := args[7]!
  let k ← encodingWidth input
  let exact ← withNewMCtxDepth (isDefEq B (mkConst ``Cslib.WordRAM.Basis.exact))
  let standard ← withNewMCtxDepth (isDefEq B (mkConst ``Cslib.WordRAM.Basis.standard))
  let atoms ← withLocalDeclD `d δ fun d => do
    (← encodingAtoms input d k).mapM (mkLambdaFVars #[d] ·)
  let env : Env := { ty := δ, k, input, atoms }
  let out ← realizeProg { basis := B, exact, standard } env p (some output)
  let zero ← zeroWork δ
  let stmt ← mkAppM ``Realizes #[B, p, input, output, out.safe, zero]
  unless ← isDefEq (← inferType out.proof) stmt do
    throwError "realize: internal error, the certificate does not match the client{indentExpr p}"
  let h ← mkExpectedTypeHint out.proof stmt
  let cons ← mkAppOptM ``Realizes.consequence #[B, args[0]!, args[1]!, δ, args[3]!, p, input,
    output, out.safe, zero, args[8]!, args[9]!, h]
  let [hsafe, hwork] ← goal.apply cons | throwError "realize: internal error in `consequence`"
  setGoals [hwork]
  evalTactic (← `(tactic| exact fun _ _ => Nat.zero_le _))
  let (_, g) ← hsafe.introN 6 [`w, `d, `s, `hwords, `hmem, `h]
  let g ← g.withContext do
    let t ← instantiateMVars (← g.getType)
    let g ← g.replaceTargetDefEq (← Core.betaReduce t)
    let hdecl := (← getLCtx).lastDecl.get!
    g.replaceLocalDeclDefEq hdecl.fvarId (← Core.betaReduce hdecl.type)
  setGoals [g]
  evalTactic (← `(tactic| try simp only [true_and, and_true, and_self, Nat.add_zero]))
  let gs ← getGoals
  let gs ← gs.flatMapM fun g => liftMetaM (splitDomain g)
  -- A condition repeated in the same context is proved once.
  let mut kept : Array MVarId := #[]
  for g in gs do
    let t ← instantiateMVars (← g.getType)
    let lctx := (← g.getDecl).lctx
    let dup? ← kept.findM? fun g' => do
      return (← g'.getDecl).lctx.decls.size == lctx.decls.size &&
        (← instantiateMVars (← g'.getType)) == t
    match dup? with
    | some g' => g.assign (mkMVar g')
    | none => kept := kept.push g
  setGoals kept.toList
