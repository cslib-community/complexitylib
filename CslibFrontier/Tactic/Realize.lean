/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WordRAM.Realization.WhileAbsorb
public import CslibFrontier.Computability.WordRAM.Realization.Reindex
public import CslibFrontier.Computability.WordRAM.Realization.Consequence

/-!
# The `realize` tactic

The tactic is available inside `Cslib.WordRAM`, or after `open Cslib.WordRAM` or
`open scoped Cslib.WordRAM`. Importing this module alone does not activate its syntax.

`realize` proves a goal `Realizes B p input output safe work` for a memory client `p`. It walks
the client syntax, unfolding definitions, with one rule per form:

* `bind`: compose the component work at the actual reply and next memory, absorbing fixed
  control work. After each bind the live words are the previous ones followed by the answer's
  encoding (`WordEncoding`); `realize` keeps this layout itself.
* `pure`: `Realizes.pure₀`, with each result word certified by a `GlueComputable` proof assembled
  from the closure rules of `CslibFrontier.Computability.WordRAM.Glue`: projections, constants, and
  the exact- or standard-basis arithmetic and bitwise operations. Conditional values, natural
  minima/maxima and Boolean decisions are lifted to paid branches, including inside returned
  constructors; only the selected alternative contributes fit and definedness conditions.
* the four memory queries: `Realizes.read`, `write`, `alloc` and `allocDirty`.
* a method with a local `Realizes` certificate: `Realizes.reindex`, selecting its
  arguments from live words before unfolding its implementation. Computed arguments are first
  staged by certified glue using the method's input encoding; the method's work is retained.
* `if` on natural `=`, `≠`, `<`, `≤`, `>` or `≥`, combined with `¬`, `∧` and `∨`:
  `Realizes.branch` (`branch₀` for zero component work), retaining short-circuiting.
  Named guards unfold to these forms.
* `match` on an optional word or word pair: the client equals the branch on its presence tag
  (`Realizes.congr`, proved by cases).
* `iterate step D n a`: `Realizes.iterateRuntime`, after
  adapting `D` and any captured live words to the whole environment. The source and reached-state
  domain and `iterationWork` are transported back to the client's original loop.
* `boundedWhile G step D n a`: `Realizes.whileBounded`. The guard
  `G D r` may be `a = b`, `a < b`, `a > b`, `a ≠ 0` (tested as `0 < a`), or `a + 1 ≤ b`
  (tested as `a < b`), with any decidability instance, over the live words and the state's words.
  An operand independent of the state is computed before the loop. The cutoff `n` is a ghost
  bound and is not computed.
  The certificate is transported to the client's guard, step and `D` (`boundedWhile_congr`,
  `whileSafe_imp`), so the loop's domain is `whileSafe G step …` in the client's terms, under
  the loop's valid history (`Realizes.consequence_valid`), ready for `whileSafe_of_measure`.

Operands are located among the live words by definitional equality. An operand that is not a
live word is first computed by an inserted `pure`, preserving the program by a checked equality.

Exact subtraction, division and remainder add their definedness conditions to the visible
domain. The common glue envelope is the maximum of every intermediate value; `realize` proves
that it fits from the fit of the live words, from the domain, and from the fit of the values it
cannot derive, which become the visible fit conditions. A value is derived when another fitting
value dominates it, for example `a - b` and `b` by `a`, or the summands by a sum.

Fixed glue and finite control work is absorbed (`Realizes.mono_mul`). Called methods retain
their work; binds sum it and branches select only the reached alternative's work. Loops retain
`iterationWork` or `whileWork`, including one control unit per reached iteration. A zero-work
body that begins with a query keeps the existing query-paid rule (`iterate₀` or `while₀`).
Intermediate domains and grades are stated in the client's own terms, with the replies of
earlier queries written as `s.mem a`, `s.frontier`, updated memories, or the interpreter's result
of a called method; a loop contributes its `iterationSafe` or `whileSafe` domain.

After composition, `realize` introduces `w d s hwords hmem h`: the word width, the environment,
memory, input fits, memory well-formedness and the goal's domain. Nonzero generated work also
adds the client's valid history as `hv`. It splits conjunctions and `if`s of the domain, then leaves
the generated work's comparison with the requested budget under the same entry assumptions.
Zero work and definitionally matching budgets close automatically. Local method certificates
are tried in context order; the remaining rule
selection follows the client syntax, without searching for bounds. An unsupported form is
reported with its subterm. A called method whose arguments are not all live words first stages
its whole encoded argument with a charged `pure` step. This also supports custom input encodings
without requiring a `WordEncoding` instance for the method's argument type.

Each certificate is stated for the client form as written, with its domain in the client's terms
(`certify`), so certificates compose syntactically. A bind's continuation domain is stated at the
first client's reply and next memory in closed form (`Realizes.bind₀_of_run`), not at the
interpreter's run. The kernel checks, locally at each form, that the rule's statement agrees.

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
  /-- A proof of `Realizes B prog input output safe work`. -/
  proof : Expr
  /-- The output encoding. -/
  output : Expr
  /-- The domain `fun w d s => …`, in the client's terms, definitionally equal to the proof's. -/
  safe : Expr
  /-- The local work in the client's terms, definitionally equal to the proof's. -/
  work : Expr

/-- `(i : Fin n)` as a numeral. -/
private def finLit (n i : Nat) : MetaM Expr :=
  mkNumeral (mkApp (mkConst ``Fin) (mkNatLit n)) i

/-- The number of words of an encoding `α ↪ (Fin l → ℕ)`. -/
private def encodingWidth (enc : Expr) : MetaM Nat := do
  let ty ← instantiateMVars (← inferType enc)
  let some (_, tgt) := ty.app2? ``Function.Embedding
    | throwError "realize: expected an encoding `α ↪ (Fin l → ℕ)`, got{indentExpr ty}"
  let .forallE _ dom _ _ ← whnf tgt
    | throwError "realize: expected an encoding `α ↪ (Fin l → ℕ)`, got{indentExpr ty}"
  let some n := (← whnf dom).app1? ``Fin
    | throwError "realize: expected an encoding `α ↪ (Fin l → ℕ)`, got{indentExpr ty}"
  let n ← instantiateMVars n
  if let some l ← (evalNat n).run then return l
  let some l ← (evalNat (← whnf n)).run
    | throwError "realize: the encoding width is not a numeral in{indentExpr ty}"
  return l

/-- The atoms of `enc x`, for `x` an expression in the environment variable. -/
private def encodingAtoms (enc x : Expr) (l : Nat) : MetaM (Array Expr) :=
  (Array.range l).mapM fun j => do
    whnf (mkApp (← mkAppM ``DFunLike.coe #[enc, x]) (← finLit l j))

/-- Locate an expression among the live words: syntactically after `whnf`, as the live words are
themselves in weak-head normal form, and otherwise by definitional equality. -/
private def findAtom (atoms : Array Expr) (e : Expr) : MetaM (Option Nat) := do
  let e' ← whnf e
  if let some i := atoms.findIdx? (· == e') then return some i
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

/-- Whether a grading is definitionally zero, without assigning its metavariables. -/
private def isZeroWork (δ work : Expr) : MetaM Bool := do
  withNewMCtxDepth <| withReducible <| isDefEq work (← zeroWork δ)

/-- The local-work grading of a completed certificate. -/
private def certificateWork (proof : Expr) : MetaM Expr := do
  let ty ← inferType proof
  unless ty.isAppOfArity ``Realizes 10 do
    throwError "realize: internal error reading a certificate's work"
  return ty.getArg! 9

/-- Absorb fixed finite composition control while retaining the component grades. -/
private def absorbControl (proof work : Expr) (factor : Nat) : TermElabM Expr := do
  let ty ← inferType proof
  let target := mkAppN ty.getAppFn (ty.getAppArgs.set! 9 work)
  let result ← mkFreshExprMVar target
  let args := ty.getAppArgs
  let transfer ← mkAppOptM ``Realizes.mono_mul
    #[args[4]!, args[2]!, args[3]!, args[0]!, args[1]!, args[5]!, args[6]!, args[7]!,
      args[8]!, args[9]!, work, proof, mkNatLit factor]
  let [bound] ← result.mvarId!.apply transfer
    | throwError "realize: internal error absorbing finite control"
  let h ← Term.withSynthesize <| Term.elabTermEnsuringType
    (← `(by intro d s; omega)) (some (← bound.getType))
  bound.assign h
  instantiateMVars result

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

/-- Prove `∀ d i, output (f d) i = g i (input d)` for `i : Fin l` by `Fin.cases`, with one `rfl` per
coordinate. Both sides are the same coordinate by construction of `g` (`coordinates`, `analyze`);
the kernel checks each `rfl`. -/
private def proveResult (ty : Expr) (l : Nat) : MetaM Expr :=
  forallBoundedTelescope ty (some 2) fun xs eq => do
    let #[d, i] := xs | throwError "realize: internal error in the result encoding"
    let P ← mkLambdaFVars #[i] eq
    -- a proof of `∀ j : Fin n, P (emb j)`
    let rec cover (n : Nat) (emb : Expr → MetaM Expr) : MetaM Expr := do
      let finN := mkApp (mkConst ``Fin) (mkNatLit n)
      match n with
      | 0 => withLocalDeclD `j finN fun j => do
        mkLambdaFVars #[j] (← mkAppOptM ``Fin.elim0 #[P.beta #[← emb j], j])
      | m + 1 => do
        let motive ← withLocalDeclD `j finN fun j => do mkLambdaFVars #[j] (P.beta #[← emb j])
        let goal := P.beta #[← emb (← mkNumeral finN 0)]
        let some (_, lhs, _) := goal.eq?
          | throwError "realize: internal error in the result encoding"
        let h0 ← mkExpectedTypeHint (← mkEqRefl lhs) goal
        let hs ← cover m fun j => do emb (← mkAppM ``Fin.succ #[j])
        mkAppOptM ``Fin.cases #[mkNatLit m, motive, h0, hs]
    mkLambdaFVars #[d] (← cover l pure)

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
      let hresult ← proveResult resTy l
      let proof ← mkAppM ``Realizes.pure₀
        #[env.input, out, f, gfun, need, hresult, hcoord, hneed]
      let safe ← withLocalDeclD `s (mkConst ``Memory.State) fun s =>
        mkLambdaFVars #[w, d, s] (mkAnd (conj st.domU.toList) (conj needU.toList))
      return { proof, output := out, safe, work := ← zeroWork env.ty }

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

/-- The native comparison of a word condition, equality or `<`, with its operands. -/
private def cond? (c : Expr) : MetaM (Option (Name × Expr × Expr)) := do
  if let some (ty, a, b) := c.eq? then
    if (← whnfR ty).isConstOf ``Nat then return some (``Cond.eq, a, b)
  if c.isAppOfArity ``LT.lt 4 && (c.getArg! 0).isConstOf ``Nat then
    return some (``Cond.lt, c.getArg! 2, c.getArg! 3)
  if c.isAppOfArity ``GT.gt 4 && (c.getArg! 0).isConstOf ``Nat then
    return some (``Cond.lt, c.getArg! 3, c.getArg! 2)
  return none

/-- The comparison of a branch condition: equality or `<`, with its operands. -/
private def parseCond (c : Expr) : MetaM (Name × Expr × Expr) := do
  if let some r ← cond? c then return r
  throwError "realize: a branch condition must combine word comparisons \
    (`=`, `≠`, `<`, `≤`, `>` or `≥`) using `¬`, `∧` or `∨`, \
    got{indentExpr c}"

/-- Expose named predicates throughout the logical guard while leaving word comparisons intact. -/
private partial def unfoldGuard (c : Expr) (fuel : Nat := 64) : MetaM Expr := do
  if let some name := c.getAppFn.constName? then
    if [``Eq, ``Ne, ``LT.lt, ``LE.le, ``GT.gt, ``GE.ge].contains name then
      return c
  if fuel == 0 then throwError "realize: branch guard unfolding exceeded its limit at{indentExpr c}"
  if c.isAppOfArity ``And 2 || c.isAppOfArity ``Or 2 then
    return mkApp2 c.getAppFn (← unfoldGuard (c.getArg! 0) (fuel - 1))
      (← unfoldGuard (c.getArg! 1) (fuel - 1))
  if c.isAppOfArity ``Not 1 then
    return mkApp c.getAppFn (← unfoldGuard c.appArg! (fuel - 1))
  let c' ← whnfR c
  if c' != c then return ← unfoldGuard c' (fuel - 1)
  if let some c' ← withTransparency .default (unfoldDefinition? c) then
    return ← unfoldGuard c' (fuel - 1)
  return c

/-- Lower a compound word test to native comparisons. Leave word operands and alternatives
untouched so their own rules retain live values, fit and selected-path safety. -/
private def normalizeBranch? (body : Expr) : MetaM (Option Simp.Result) := do
  let guard ← unfoldGuard (body.getArg! 1)
  let mut guardThms : SimpTheorems := {}
  guardThms ← guardThms.addConst ``ne_eq
  guardThms ← guardThms.addConst ``not_lt (inv := true)
  let ctx ← Simp.mkContext
    (config := { dsimp := false, zeta := false, proj := false, iota := false })
    (simpTheorems := #[guardThms]) (congrTheorems := ← getSimpCongrTheorems)
  let defaults := Simp.mkDefaultMethodsCore #[]
  let guardMethods : Simp.Methods := { defaults with
    pre := fun e => do
      if (← whnfR (← inferType e)).isConstOf ``Nat then return .done { expr := e }
      if e != guard && (← isProp e) then return .done { expr := e }
      defaults.pre e }
  let (condition, _) ← Simp.main guard ctx (methods := guardMethods)
  -- Rebuild decidability from the exposed formula. Its original instance can be hidden
  -- behind a named guard; conditional congruence checks the bridge for either instance.
  let h ← mkAppOptM ``ite_cond_congr #[some (body.getArg! 0), some (body.getArg! 1),
    some condition.expr, some (body.getArg! 2), none, some (body.getArg! 3),
    some (body.getArg! 4), some (← condition.getProof)]
  let some (_, _, canonical) := (← inferType h).eq?
    | throwError "realize: internal error rebuilding a branch condition"
  let mut thms : SimpTheorems := {}
  for name in [``ite_not, ``ite_and, ``ite_or] do
    thms ← thms.addConst name
  let methods : Simp.Methods := { defaults with
    pre := fun e => do
      if e == body.getArg! 3 || e == body.getArg! 4 then return .done { expr := e }
      if ← isProp e then return .done { expr := e }
      defaults.pre e }
  let (normalized, _) ← Simp.main canonical (ctx.setSimpTheorems #[thms]) (methods := methods)
  -- Each recursive call exposes an alias or simplifies the outer condition. Do not
  -- recurse merely because an unsupported condition acquired a different instance.
  if normalized.expr.isAppOfArity ``ite 5 &&
      normalized.expr.getArg! 1 != body.getArg! 1 then
    return some { normalized with proof? := some (← mkEqTrans h (← normalized.getProof)) }
  return none

/-- The comparison of a loop guard, with a checked equivalence to its native test.
Successor lower bounds use the predecessor directly, without computing a successor word. -/
private partial def parseGuard (g : Expr) (orig : Expr := g.headBeta) (fuel : Nat := 64) :
    MetaM (Name × Expr × Expr × Expr) := do
  let g := g.headBeta
  if let some (kind, a, b) ← cond? g then
    return (kind, a, b, ← mkAppM ``Iff.refl #[g])
  if let some (ty, a, z) := g.ne?.orElse fun _ => g.not?.bind Expr.eq? then
    if (← whnfR ty).isConstOf ``Nat && (← withNewMCtxDepth (isDefEq z (mkNatLit 0))) then
      return (``Cond.lt, z, a,
        ← mkAppM ``Iff.symm #[← mkAppOptM ``Nat.pos_iff_ne_zero #[a]])
  if (g.isAppOfArity ``LE.le 4 || g.isAppOfArity ``GE.ge 4) &&
      (g.getArg! 0).isConstOf ``Nat then
    let (a, b) := if g.isAppOfArity ``GE.ge 4 then (g.getArg! 3, g.getArg! 2)
      else (g.getArg! 2, g.getArg! 3)
    let a ← whnfR a
    let literal? ← getNatValue? a
    let add? := if let some (.add, p, q) := binOp? a then some (p, q)
      else if a.isAppOfArity ``Nat.add 2 then some (a.getArg! 0, a.getArg! 1) else none
    let pred? ← if let some (p, q) := add? then do
        let one ← withNewMCtxDepth (isDefEq q (mkNatLit 1))
        pure (if one then some p else none)
      else pure <| if a.isAppOfArity ``Nat.succ 1 then some (a.getArg! 0)
        else literal?.bind fun n => if n == 0 then none else some (mkNatLit (n - 1))
    if let some pred := pred? then
      return (``Cond.lt, pred, b, ← mkAppOptM ``Nat.succ_le_iff #[pred, b])
  if fuel != 0 then
    let g' ← whnfR g
    if g' != g then return ← parseGuard g' orig (fuel - 1)
    if let some g' ← unfoldDefinition? g then return ← parseGuard g' orig (fuel - 1)
  throwError "realize: a loop guard must be `a = b`, `a < b`, `a > b`, `a ≠ 0` \
    or `a + 1 ≤ b` on words, \
    got{indentExpr orig}"

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
  e.isAppOfArity ``ite 5 || e.isAppOfArity ``boundedWhile 8

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

/-- `∀ x s, 1 ≤ memoryCost (body x) s` for a loop body that begins with a query. -/
private def proveQuery (body ty : Expr) : MetaM Expr :=
  withLocalDeclD `x ty fun x => withLocalDeclD `s (mkConst ``Memory.State) fun s => do
    let b ← whnf (mkApp body x)
    unless b.isAppOfArity ``PFunctor.FreeM.liftBind 4 do
      throwError "realize: a loop body must begin with a memory query, which pays for the \
        iteration;\nthe body begins with{indentExpr b}"
    let pf ← mkAppM ``one_le_memoryCost_liftBind #[b.getArg! 2, b.getArg! 3, s]
    let goal ← mkAppM ``LE.le #[mkNatLit 1, ← mkAppM ``memoryCost #[mkApp body x, s]]
    mkLambdaFVars #[x, s] (← mkExpectedTypeHint pf goal)

/-- Keep query-paid loop control when the body has zero local work and begins with a query. -/
private def queryPayment? (body ty work : Expr) : TermElabM (Option Expr) := do
  unless ← isZeroWork ty work do return none
  let saved ← saveState
  try
    return some (← proveQuery body ty)
  catch _ =>
    saved.restore
    return none

/-- Transport a certificate's domain or work along an equality of its functions. -/
private def transportField (proof eq : Expr) (index : Nat) : MetaM Expr := do
  let ty ← inferType proof
  let wrap ← withLocalDeclD `field (← inferType (ty.getArg! index)) fun field =>
    mkLambdaFVars #[field] (mkAppN ty.getAppFn (ty.getAppArgs.set! index field))
  mkAppM ``Eq.mp #[← mkAppM ``congrArg #[wrap, eq], proof]

/-- State `proof` as `Realizes B prog input output safe work`, for the client `prog`
as written and the domain `safe` in the client's terms.

The rule's statement agrees with this one by construction: up to unfolding `prog`, reducing pair
projections, and evaluating the live words, which were located as the weak-head normal forms of
`input d i`. The kernel checks the agreement locally at each form. Elaboration does not re-check
it, because unfolding composed domains with nested interpreter runs grows with the client. -/
private def certify (ctx : Ctx) (env : Env) (proof prog output safe work : Expr) : MetaM Expr := do
  mkExpectedTypeHint proof
    (← mkAppM ``Realizes #[ctx.basis, prog, env.input, output, safe, work])

/-- Compose at a closed-form reply and next memory, retaining component work while absorbing
the bind's fixed control. The zero-work case keeps `Realizes.bind₀_of_run`. -/
private def bindRun (hP hQ reply next : Expr) : TermElabM Expr := do
  let pTy ← inferType hP
  let workP := pTy.getArg! 9
  let workQ ← certificateWork hQ
  let pZero ← isZeroWork (pTy.getArg! 2) workP
  let qZero ← isZeroWork ((← inferType hQ).getArg! 2) workQ
  if !pZero || !qZero then
    let (work, charged) ← withLocalDeclD `d (pTy.getArg! 2) fun d =>
      withLocalDeclD `s (mkConst ``Memory.State) fun s => do
        let pair ← mkAppM ``Prod.mk #[d, reply.beta #[d, s]]
        let wp := workP.beta #[d, s]
        let wq := workQ.beta #[pair, next.beta #[d, s]]
        let sum ← if pZero then pure wq else if qZero then pure wp
          else mkAppM ``HAdd.hAdd #[wp, wq]
        let charged ← mkAppM ``HAdd.hAdd
          #[← mkAppM ``HAdd.hAdd #[wp, wq], mkNatLit 1]
        return (← mkLambdaFVars #[d, s] (← reducePairs sum),
          ← mkLambdaFVars #[d, s] (← reducePairs charged))
    let proof ← mkAppM ``Realizes.bind #[hP, hQ]
    let ty ← inferType proof
    let proof ← mkExpectedTypeHint proof (mkAppN ty.getAppFn (ty.getAppArgs.set! 9 charged))
    return ← absorbControl proof work 1
  let refl (f : Expr) : MetaM Expr :=
    lambdaBoundedTelescope f 2 fun xs b => do mkLambdaFVars xs (← mkEqRefl b)
  mkAppM ``Realizes.bind₀_of_run #[hP, hQ, reply, next, ← refl reply, ← refl next]

/-- Expose pair projections to unification when a certificate packages curried arguments.
Other types remain whole metavariables: no data constructor or runtime value is guessed. -/
private partial def callArgument (ty : Expr) : MetaM Expr := do
  let ty ← whnfR ty
  if let some (a, b) := ty.app2? ``Prod then
    return mkAppN (mkConst ``Prod.mk ty.getAppFn.constLevels!)
      #[a, b, ← callArgument a, ← callArgument b]
  if let some (a, b) := ty.app2? ``Sigma then
    let x ← callArgument a
    return mkAppN (mkConst ``Sigma.mk ty.getAppFn.constLevels!)
      #[a, b, x, ← callArgument (b.beta #[x])]
  mkFreshExprMVar ty

/-- Wire a matched method's encoded argument to live words, retaining its domain. -/
private def reindexCall (env : Env) (d arg certificate : Expr) (positions : Array Nat) :
    TermElabM Out := do
  let ty ← instantiateMVars (← inferType certificate)
  unless ty.isAppOfArity ``Realizes 10 do
    throwError "realize: expected a `Realizes` method certificate{indentExpr ty}"
  let args := ty.getAppArgs
  let k := positions.size
  let finK := mkApp (mkConst ``Fin) (mkNatLit k)
  let finEnv := mkApp (mkConst ``Fin) (mkNatLit env.k)
  let rec indices : List Nat → MetaM Expr
    | [] => mkAppOptM ``Matrix.vecEmpty #[finEnv]
    | i :: is => do mkAppM ``Matrix.vecCons #[← finLit env.k i, ← indices is]
  let ix ← indices positions.toList
  let f ← mkLambdaFVars #[d] arg
  let hwTy ← withLocalDeclD `e env.ty fun e => withLocalDeclD `i finK fun i => do
    let lhs := mkApp (← mkAppM ``DFunLike.coe #[args[6]!, f.beta #[e]]) i
    let rhs := mkApp (← mkAppM ``DFunLike.coe #[env.input, e]) (mkApp ix i)
    mkForallFVars #[e, i] (← mkEq lhs rhs)
  let hw ← proveResult hwTy k
  let proof ← mkAppM ``Realizes.reindex #[certificate, f, env.input, ix, hw]
  let safe ← withLocalDeclD `w (mkConst ``Nat) fun w =>
    withLocalDeclD `s (mkConst ``Memory.State) fun s => do
      mkLambdaFVars #[w, d, s] (← reducePairs (mkApp3 args[8]! w arg s))
  let work ← withLocalDeclD `s (mkConst ``Memory.State) fun s => do
    mkLambdaFVars #[d, s] (← reducePairs (mkApp2 args[9]! arg s))
  return { proof, output := args[7]!, safe, work }

/-- Reuse a local method certificate before unfolding its body. Live arguments use static
wiring; otherwise a certified `pure` stage computes the argument in the callee's encoding. -/
private def tryRealizeCall (ctx : Ctx) (env : Env) (d : Expr) (atoms : Array Expr)
    (body : Expr) (output? : Option Expr) (stage : Expr → Expr → TermElabM Out) :
    TermElabM (Option Out) := do
  for decl in ← getLCtx do
    if decl.isImplementationDetail then continue
    let ty ← instantiateMVars decl.type
    unless ty.isAppOfArity ``Realizes 10 do continue
    let saved ← saveState
    try
      let args := ty.getAppArgs
      unless ← withReducible (isDefEq args[4]! ctx.basis) do
        throwError "realize: the method's basis differs"
      let arg ← callArgument args[2]!
      let called := (mkApp args[5]! arg).headBeta
      -- Solve dependent arguments in binder order without unfolding a matching method head.
      let matched ← if called.getAppFn == body.getAppFn &&
          called.getAppNumArgs == body.getAppNumArgs then
          (called.getAppArgs.zip body.getAppArgs).allM fun (a, b) => do
            let a ← whnfR a
            let b ← whnfR b
            -- Inherited instances such as a monad's `Pure` can be definitionally the direct
            -- instance after unfolding their implementation. Keep runtime data opaque.
            if (← isClass? (← inferType a)).isSome then
              withTransparency .default (isDefEq a b)
            else
              withReducible (isDefEq a b)
        else withReducible (isDefEq called body)
      unless matched do
        throwError "realize: the method does not match"
      let arg ← instantiateMVars arg
      if arg.hasMVar then throwError "realize: the method argument is undetermined"
      discard <| checkOutput decl.toExpr output?
      let k ← encodingWidth args[6]!
      let coords ← encodingAtoms args[6]! arg k
      let positions ← coords.mapM fun a => liftMetaM (findAtom atoms a)
      if positions.all Option.isSome then
        return some (← reindexCall env d arg decl.toExpr (positions.map Option.get!))
      -- Stage the typed argument, rather than guessing an inverse for its encoding. The pure
      -- bind reduces to the original call, and the existing glue rule charges its computation.
      let hP ← stage arg args[6]!
      let env' ← extend env args[2]! args[6]! k
      let hQ ← withLocalDeclD `x env'.ty fun x => do
        reindexCall env' x (← mkAppM ``Prod.snd #[x]) decl.toExpr
          ((Array.range k).map (env.k + ·))
      let (reply, next) ← withLocalDeclD `s (mkConst ``Memory.State) fun s => do
        return (← mkLambdaFVars #[d, s] arg, ← mkLambdaFVars #[d, s] s)
      let proof ← bindRun hP.proof hQ.proof reply next
      let safe ← withLocalDeclD `w (mkConst ``Nat) fun w =>
        withLocalDeclD `s (mkConst ``Memory.State) fun s => do
          mkLambdaFVars #[w, d, s] (mkAnd (hP.safe.beta #[w, d, s])
            (← reducePairs (mkApp3 args[8]! w arg s)))
      return some { proof, output := hQ.output, safe, work := ← certificateWork proof }
    catch _ => saved.restore
  return none

/-- Lift returned selections through their constructor/application context. Only the listed
equalities are used: arithmetic and method definitions are left for their existing rules. -/
private def normalizePure? (d : Expr) (atoms : Array Expr) (body : Expr) :
    TermElabM (Option Simp.Result) := do
  let interesting (e : Expr) : Bool :=
    e.isAppOfArity ``ite 5 || e.isAppOfArity ``decide 2 ||
      e.isAppOfArity ``Nat.min 2 || e.isAppOfArity ``Nat.max 2 ||
      ((e.isAppOfArity ``Min.min 4 || e.isAppOfArity ``Max.max 4) &&
        (e.getArg! 0).isConstOf ``Nat)
  if (body.appArg!.find? interesting).isNone then return none
  -- Constants and already encoded words remain glue values, including inside a mixed result.
  -- Expanding their selections would introduce comparisons and stronger fit obligations.
  let fixedOrLive (e : Expr) : MetaM Bool := do
    if !e.containsFVar d.fvarId! then return true
    -- Simp traverses reducibly; use the same transparency as the existing glue analysis.
    return (e.find? interesting).isSome &&
      (← withTransparency .default (findAtom atoms e)).isSome
  let mut thms : SimpTheorems := {}
  for name in [``Nat.min_def, ``Nat.max_def, ``ite_not] do
    thms ← thms.addConst name
  thms ← thms.addConst ``not_lt (inv := true)
  if (body.appArg!.find? (·.isAppOfArity ``decide 2)).isSome then
    let decideRule ← Term.elabTerm (← `(fun (p : Prop) [Decidable p] =>
      (show decide p = if p then true else false from by
        by_cases h : p
        · exact (decide_eq_true h).trans (ite_eq_left h).symm
        · exact (decide_eq_false h).trans (ite_eq_right h).symm))) none
    Term.synthesizeSyntheticMVarsNoPostponing
    thms ← thms.add (.other `realize_decide) #[] (← instantiateMVars decideRule)
  let ctx ← Simp.mkContext
    (config := { dsimp := false, zeta := false, proj := false, iota := false })
    (simpTheorems := #[thms]) (congrTheorems := ← getSimpCongrTheorems)
  let defaults := Simp.mkDefaultMethodsCore #[]
  let normalizeMethods : Simp.Methods := { defaults with
    pre := fun e => do
      if ← fixedOrLive e then return .done { expr := e }
      defaults.pre e }
  let (normalized, _) ← Simp.main body ctx (methods := normalizeMethods)
  let liftCtx := ctx.setSimpTheorems #[{}]
  let liftArgument (e : Expr) : MetaM (Option Simp.Result) := do
    let args := e.getAppArgs
    for h : i in [0:args.size] do
      let choice := args[i]
      unless choice.isAppOfArity ``ite 5 do continue
      if ← fixedOrLive choice then continue
      let f ← withLocalDeclD `selected (← inferType choice) fun selected => do
        mkLambdaFVars #[selected] (mkAppN e.getAppFn (args.set i selected))
      let proof ← mkAppOptM ``apply_ite #[none, none, f, choice.getArg! 1,
        choice.getArg! 2, choice.getArg! 3, choice.getArg! 4]
      let some (_, _, rhs) := (← inferType proof).eq?
        | throwError "realize: internal error lifting a conditional result"
      return some { expr := rhs, proof? := some proof }
    return none
  -- Stop at the first lifted choice. Traversing it would distribute one branch across
  -- another; its alternatives are instead certified recursively by the branch rule.
  let methods : Simp.Methods := { defaults with
    pre := fun e => do
      if e.isAppOfArity ``ite 5 || (← fixedOrLive e) then return .done { expr := e }
      defaults.pre e
    post := fun e => do
      if let some result ← liftArgument e then return .visit result
      defaults.post e }
  let (lifted, _) ← Simp.main normalized.expr liftCtx (methods := methods)
  if lifted.expr.isAppOfArity ``ite 5 then
    return some {
      expr := lifted.expr
      proof? := some (← mkEqTrans (← normalized.getProof) (← lifted.getProof)) }
  return none

mutual

/-- Certify a client `prog : δ → Memory.Prog α` in the environment `env`. -/
private partial def realizeProg (ctx : Ctx) (env : Env) (prog : Expr) (output? : Option Expr) :
    TermElabM Out :=
  withLocalDeclD `d env.ty fun d => do
    let atoms := env.atoms.map (·.beta #[d])
    let stage (a output : Expr) : TermElabM Out := do
      let body ← mkAppOptM ``Pure.pure #[mkConst ``Memory.Prog, none, none, a]
      realizeBody ctx env d atoms body (some output)
    if let some out ← tryRealizeCall ctx env d atoms (prog.beta #[d]).headBeta output? stage then
      return { out with proof := ← certify ctx env out.proof prog out.output out.safe out.work }
    let body ← normBody (prog.beta #[d]).headBeta
    let out ← realizeBody ctx env d atoms body output?
    return { out with proof := ← certify ctx env out.proof prog out.output out.safe out.work }

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
    let saved ← saveState
    try
      return ← realizePure ctx env d atoms a out
    catch ex =>
      saved.restore
      if let some normalized ← normalizePure? d atoms body then
        let out ← realizeBody ctx env d atoms normalized.expr (some out)
        let eq ← mkLambdaFVars #[d] (← mkEqSymm (← normalized.getProof))
        return { out with proof := ← mkAppM ``Realizes.congr #[out.proof, eq] }
      throw ex
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
    return { proof, output, safe := ← trueSafe env.ty, work := ← zeroWork env.ty }
  -- branching
  if body.isAppOfArity ``ite 5 then
    if (← cond? (body.getArg! 1)).isNone then
      if let some normalized ← normalizeBranch? body then
        let out ← realizeBody ctx env d atoms normalized.expr output?
        let eq ← mkLambdaFVars #[d] (← mkEqSymm (← normalized.getProof))
        return { out with proof := ← mkAppM ``Realizes.congr #[out.proof, eq] }
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
      let out ← realizeBody ctx env d atoms (← bindPure x rebuilt) output?
      let canonical := (rebuilt.beta #[x]).headBeta
      let hc ← mkExpectedTypeHint (← mkEqRefl c) (← mkEq (canonical.getArg! 1) c)
      let eq ← mkLambdaFVars #[d] (← mkAppOptM ``ite_cond_congr
        #[body.getArg! 0, canonical.getArg! 1, c, canonical.getArg! 2, inst, t, e, hc])
      return { out with proof := ← mkAppM ``Realizes.congr #[out.proof, eq] }
    let out ← match output? with
      | some o => pure o
      | none => encodingOf (← resultType body)
    let hp ← realizeProg ctx env (← mkLambdaFVars #[d] t) (some out)
    let hn ← realizeProg ctx env (← mkLambdaFVars #[d] e) (some out)
    let cond ← mkAppM kind #[← finLit k ia, ← finLit k ib]
    let nativeCond ← mkAppM ``test #[cond, ← mkAppM ``DFunLike.coe #[env.input, d]]
    let nativeInst ← synthInstance (← mkAppM ``Decidable #[nativeCond])
    let hc ← mkExpectedTypeHint (← mkEqRefl c) (← mkEq nativeCond c)
    let work ← withLocalDeclD `s (mkConst ``Memory.State) fun s => do
      mkLambdaFVars #[d, s] (← mkAppOptM ``ite
        #[mkConst ``Nat, c, inst, hp.work.beta #[d, s], hn.work.beta #[d, s]])
    let proof ← if (← isZeroWork env.ty hp.work) && (← isZeroWork env.ty hn.work) then
        mkAppM ``Realizes.branch₀ #[cond, hp.proof, hn.proof]
      else do
        let nativeWork ← withLocalDeclD `s (mkConst ``Memory.State) fun s => do
          mkLambdaFVars #[d, s] (← mkAppOptM ``ite
            #[mkConst ``Nat, nativeCond, nativeInst, hp.work.beta #[d, s], hn.work.beta #[d, s]])
        let h ← absorbControl (← mkAppM ``Realizes.branch #[cond, hp.proof, hn.proof])
          nativeWork 2
        let pointwise ← withLocalDeclD `s (mkConst ``Memory.State) fun s => do
          mkLambdaFVars #[s] (← mkAppOptM ``ite_cond_congr
            #[mkConst ``Nat, nativeCond, c, nativeInst, inst,
              hp.work.beta #[d, s], hn.work.beta #[d, s], hc])
        let eq ← mkAppM ``funext #[← mkLambdaFVars #[d]
          (← mkAppM ``funext #[pointwise])]
        transportField h eq 9
    let eq ← mkLambdaFVars #[d] (← mkAppOptM ``ite_cond_congr
      #[body.getArg! 0, nativeCond, c, nativeInst, inst, t, e, hc])
    let proof ← mkAppM ``Realizes.congr #[proof, eq]
    let safe ← withLocalDeclD `w (mkConst ``Nat) fun w =>
      withLocalDeclD `s (mkConst ``Memory.State) fun s => do
        mkLambdaFVars #[w, d, s] (mkApp5 (mkConst ``ite [Level.one]) (mkSort Level.zero) c inst
          (hp.safe.beta #[w, d, s]) (hn.safe.beta #[w, d, s]))
    let safeEq ← withLocalDeclD `w (mkConst ``Nat) fun w => do
      let pointwise ← withLocalDeclD `s (mkConst ``Memory.State) fun s => do
        mkLambdaFVars #[s] (← mkAppOptM ``ite_cond_congr
          #[mkSort Level.zero, nativeCond, c, nativeInst, inst,
            hp.safe.beta #[w, d, s], hn.safe.beta #[w, d, s], hc])
      mkLambdaFVars #[w] (← mkAppM ``funext #[← mkLambdaFVars #[d]
        (← mkAppM ``funext #[pointwise])])
    let proof ← transportField proof (← mkAppM ``funext #[safeEq]) 8
    return { proof, output := out, safe, work := ← certificateWork proof }
  -- a guarded loop
  if body.isAppOfArity ``boundedWhile 8 then
    return ← realizeWhile ctx env d atoms body output?
  -- a runtime-bounded loop
  if body.isAppOfArity ``iterate 6 then
    return ← realizeIterate ctx env d atoms (body.getArg! 1) (body.getArg! 2) (body.getArg! 3)
      (body.getArg! 4) (body.getArg! 5) output?
  -- a `match` on an optional answer becomes a test of its presence tag
  let body ← Core.betaReduce body
  if let some r ← optionDiscr? d body then
    return ← realizeOptionSplit ctx env d atoms body r output?
  throwError "realize: unsupported client form{indentExpr body}\n\
    Expected `bind`, `pure`, a memory query, `if` on a word comparison,\n\
    a `match` on an optional answer, `iterate` or `boundedWhile`.\n\
    Write recursion on a runtime value as one of these loops."

/-- Certify a client that matches on the optional answer `r`: it equals the branch on `r`'s
presence tag, with `r` replaced by `none` and by `some` of its payload. -/
private partial def realizeOptionSplit (ctx : Ctx) (env : Env) (d : Expr) (atoms : Array Expr)
    (body r : Expr) (output? : Option Expr) : TermElabM Out := do
  let rTy ← whnfR (← inferType r)
  let enc ← encodingOf rTy
  let words ← mkAppM ``DFunLike.coe #[enc, r]
  let l ← encodingWidth enc
  let payloadTy ← whnfR rTy.appArg!
  let payload ← if payloadTy.isConstOf ``Nat then
      unless l == 2 do
        throwError "realize: expected a tag and payload encoding for{indentExpr r}"
      pure (mkApp words (← finLit l 1))
    else if let some (a, b) := payloadTy.app2? ``Prod then
      unless (← whnfR a).isConstOf ``Nat && (← whnfR b).isConstOf ``Nat do
        throwError "realize: optional matches support a word or a pair of words, \
          got{indentExpr rTy}"
      unless l == 3 do
        throwError "realize: expected a tag and two payload words for{indentExpr r}"
      mkAppM ``Prod.mk #[mkApp words (← finLit l 1), mkApp words (← finLit l 2)]
    else
      throwError "realize: optional matches support a word or a pair of words, \
          got{indentExpr rTy}"
  let tag := mkApp words (← finLit l 0)
  let cond ← mkEq tag (← mkNumeral (mkConst ``Nat) 0)
  let noneE ← mkAppOptM ``Option.none #[rTy.appArg!]
  let someE ← mkAppM ``Option.some #[payload]
  let bodyNone := body.replace fun e => if e == r then some noneE else none
  let bodySome := body.replace fun e => if e == r then some someE else none
  let rhs ← mkAppM ``ite #[cond, bodyNone, bodySome]
  let eq ← proveSplit d r (← mkForallFVars #[d] (← mkEq rhs body))
  let out ← realizeBody ctx env d atoms rhs output?
  let h ← certify ctx env out.proof (← mkLambdaFVars #[d] rhs) out.output out.safe out.work
  let proof ← mkAppM ``Realizes.congr #[h, eq]
  return { out with proof }

/-- Certify `iterate step D n a`: copy the initial state and fuel, then run over the whole
environment (`iterate_congr`). Retain iteration work unless a query pays for each iteration. -/
private partial def realizeIterate (ctx : Ctx) (env : Env) (d : Expr) (atoms : Array Expr)
    (σ step D n a : Expr) (output? : Option Expr) : TermElabM Out := do
  unless ctx.exact do throwError "realize: loops are certified in the exact basis"
  let out ← match output? with
    | some o => pure o
    | none => encodingOf σ
  let l ← encodingWidth out
  let envB ← extend env σ out l
  let captured := step.containsFVar d.fvarId!
  -- the body over the whole environment
  let body ← if D == d && !captured then pure step else
    withLocalDeclD `x envB.ty fun x => do
      let x1 ← mkAppM ``Prod.fst #[x]
      let x2 ← mkAppM ``Prod.snd #[x]
      let Dx := (← mkLambdaFVars #[d] D).beta #[x1]
      mkLambdaFVars #[x] (mkApp (step.replaceFVar d x1) (← mkAppM ``Prod.mk #[Dx, x2]))
  let hB ← realizeProg ctx envB body (some out)
  let hq? ← queryPayment? body envB.ty hB.work
  let hLoop ← match hq? with
    | some hq => mkAppM ``Realizes.iterate₀ #[env.input, out, hB.proof, hq]
    | none => mkAppM ``Realizes.iterateRuntime #[env.input, out, hB.proof]
  -- the fuel, after the state
  let hN ← withLocalDeclD `x envB.ty fun x => do
    let x1 ← mkAppM ``Prod.fst #[x]
    let nx := (← mkLambdaFVars #[d] n).beta #[x1]
    let word ← encodingOf (mkConst ``Nat)
    let atomsX := envB.atoms.map (·.beta #[x])
    let o ← realizePure ctx envB x atomsX nx word
    pure o
  let hA ← realizePure ctx env d atoms a out
  -- both binds return a computed value and leave the memory unchanged
  let (nReply, nNext) ← withLocalDeclD `x envB.ty fun x =>
    withLocalDeclD `s (mkConst ``Memory.State) fun s => do
      let nx := (← mkLambdaFVars #[d] n).beta #[← mkAppM ``Prod.fst #[x]]
      return (← mkLambdaFVars #[x, s] nx, ← mkLambdaFVars #[x, s] s)
  let h2 ← bindRun hN.proof hLoop nReply nNext
  let (aReply, aNext) ← withLocalDeclD `s (mkConst ``Memory.State) fun s => do
    return (← mkLambdaFVars #[d, s] a, ← mkLambdaFVars #[d, s] s)
  let proof ← bindRun hA.proof h2 aReply aNext
  let safe ← withLocalDeclD `w (mkConst ``Nat) fun w =>
    withLocalDeclD `s (mkConst ``Memory.State) fun s => do
      let pair ← mkAppM ``Prod.mk #[d, a]
      let sn ← reducePairs (hN.safe.beta #[w, pair, s])
      let sl ← mkAppM ``iterationSafe #[body, hB.safe, w, d, n, a, s]
      mkLambdaFVars #[w, d, s] (mkAnd (hA.safe.beta #[w, d, s]) (mkAnd sn sl))
  let progR ← mkLambdaFVars #[d] (← mkAppM ``iterate #[body, d, n, a])
  let work ← certificateWork proof
  let proof ← certify ctx env proof progR out safe work
  if D == d && !captured then return { proof, output := out, safe, work }
  -- The adapted step agrees at this fixed environment, including any captured values.
  let hbody ← withLocalDeclD `x σ fun x => do
    let lhs := mkApp body (← mkAppM ``Prod.mk #[d, x])
    let rhs := mkApp step (← mkAppM ``Prod.mk #[D, x])
    mkLambdaFVars #[x] (← mkExpectedTypeHint (← mkEqRefl lhs) (← mkEq lhs rhs))
  let eq ← mkLambdaFVars #[d] (← mkAppOptM ``iterate_congr
    #[env.ty, σ, ← inferType D, body, step, d, D, hbody, n, a])
  let proof ← mkAppM ``Realizes.congr #[proof, eq]
  -- Keep the grade in the original loop's terms, including a captured environment.
  let (proof, work) ← if hq?.isSome then pure (proof, work) else do
    let state := mkConst ``Memory.State
    let pairTy ← mkAppM ``Prod #[← inferType D, σ]
    let clientWork ← withLocalDeclD `x pairTy fun x =>
      withLocalDeclD `s state fun s => do
        let pair ← mkAppM ``Prod.mk #[d, ← mkAppM ``Prod.snd #[x]]
        mkLambdaFVars #[x, s] (← reducePairs (hB.work.beta #[pair, s]))
    let work' ← withLocalDeclD `s state fun s => do
      mkLambdaFVars #[d, s] (← mkAppM ``iterationWork #[step, clientWork, D, n, a, s])
    let hw ← withLocalDeclD `x σ fun x => withLocalDeclD `s state fun s => do
      let lhs := hB.work.beta #[← mkAppM ``Prod.mk #[d, x], s]
      let rhs := clientWork.beta #[← mkAppM ``Prod.mk #[D, x], s]
      mkLambdaFVars #[x, s] (← mkExpectedTypeHint (← mkEqRefl lhs) (← mkEq lhs rhs))
    let pointwise ← withLocalDeclD `s state fun s => do
      let h ← mkAppOptM ``iterationWork_congr
        #[env.ty, σ, ← inferType D, body, step, hB.work, clientWork, d, D, hbody, hw, n, a, s]
      mkLambdaFVars #[s] (← mkExpectedTypeHint h
        (← mkEq (work.beta #[d, s]) (work'.beta #[d, s])))
    let workEq ← mkAppM ``funext #[← mkLambdaFVars #[d]
      (← mkAppM ``funext #[pointwise])]
    pure (← transportField proof workEq 9, work')
  if !captured then return { proof, output := out, safe, work }
  -- State the reached-state domain in the original loop's terms, as in `realizeWhile`.
  let nat := mkConst ``Nat
  let state := mkConst ``Memory.State
  let pairTy ← mkAppM ``Prod #[← inferType D, σ]
  let clientSafe ← withLocalDeclD `w nat fun w =>
    withLocalDeclD `x pairTy fun x =>
      withLocalDeclD `s state fun s => do
        let pair ← mkAppM ``Prod.mk #[d, ← mkAppM ``Prod.snd #[x]]
        mkLambdaFVars #[w, x, s] (← reducePairs (hB.safe.beta #[w, pair, s]))
  let safe' ← withLocalDeclD `w nat fun w => withLocalDeclD `s state fun s => do
    let pair ← mkAppM ``Prod.mk #[d, a]
    let sn ← reducePairs (hN.safe.beta #[w, pair, s])
    let sl ← mkAppM ``iterationSafe #[step, clientSafe, w, D, n, a, s]
    mkLambdaFVars #[w, d, s] (mkAnd (hA.safe.beta #[w, d, s]) (mkAnd sn sl))
  let pointwise ← withLocalDeclD `w nat fun w => withLocalDeclD `s state fun s => do
    let hs ← withLocalDeclD `x σ fun x => withLocalDeclD `t state fun t => do
      let lhs := hB.safe.beta #[w, ← mkAppM ``Prod.mk #[d, x], t]
      let rhs := clientSafe.beta #[w, ← mkAppM ``Prod.mk #[D, x], t]
      mkLambdaFVars #[x, t] (← mkExpectedTypeHint (← mkAppOptM ``Iff.rfl #[lhs])
        (mkApp2 (mkConst ``Iff) lhs rhs))
    let h ← mkAppOptM ``iterationSafe_congr
      #[env.ty, σ, ← inferType D, body, step, hB.safe, clientSafe, w, d, D, hbody, hs, n, a, s]
    let h ← mkAppM ``propext #[h]
    let pair ← mkAppM ``Prod.mk #[d, a]
    let sn ← reducePairs (hN.safe.beta #[w, pair, s])
    let wrap ← withLocalDeclD `p (mkSort Level.zero) fun p =>
      mkLambdaFVars #[p] (mkAnd (hA.safe.beta #[w, d, s]) (mkAnd sn p))
    mkLambdaFVars #[w, d, s] (← mkAppM ``congrArg
      #[wrap, h])
  let safeEq ← withLocalDeclD `w nat fun w => do
    let hd ← withLocalDeclD `e env.ty fun e => do
      mkLambdaFVars #[e] (← mkAppM ``funext #[mkApp2 pointwise w e])
    mkLambdaFVars #[w] (← mkAppM ``funext #[hd])
  let safeEq ← mkAppM ``funext #[safeEq]
  let proof ← transportField proof safeEq 8
  return { proof, output := out, safe := safe', work }

/-- Certify `boundedWhile G step D n a` for the environment variable `d`.

The guard becomes a native comparison of the live words and the state's words. An operand that
does not depend on the state, such as the `0` of `0 < r`, is computed first into one more live
word. The body runs over the environment and state, retaining `whileWork` unless its zero work
and initial query justify `Realizes.while₀`. The cutoff `n` is a ghost bound: it is never computed.
The certificate is
transported to the client's own guard, step and loop environment `D` (`boundedWhile_congr`,
`whileSafe_imp`), and the loop's domain may assume the loop's valid history
(`Realizes.consequence_valid`), which `whileSafe_of_measure` uses. -/
private partial def realizeWhile (ctx : Ctx) (env : Env) (d : Expr) (atoms : Array Expr)
    (body : Expr) (output? : Option Expr) : TermElabM Out := do
  let args := body.getAppArgs
  let (Δ, σ, G, inst, step, D, n, a) :=
    (args[0]!, args[1]!, args[2]!, args[3]!, args[4]!, args[5]!, args[6]!, args[7]!)
  let out ← match output? with
    | some o => pure o
    | none => encodingOf σ
  let l ← encodingWidth out
  let k := env.k
  let nat := mkConst ``Nat
  let state := mkConst ``Memory.State
  -- the comparison, its operands among the live words and the state's words (`none` for a
  -- computed operand), the computed operand, and the source-to-native guard equivalence
  let (kind, posA, posB, pre?, guardIff) ← withLocalDeclD `a σ fun x => do
    let (kind, oa, ob, hg) ← parseGuard (mkApp2 G D x)
    let words := atoms ++ (← encodingAtoms out x l)
    let locate (o : Expr) : MetaM (Option Nat) := do
      if let some i ← findAtom words o then return some i
      if o.containsFVar x.fvarId! then
        throwError "realize: a loop guard compares words; the operand{indentExpr o}\n\
          depends on the loop state but is not one of its words"
      return none
    let (ia, ib) := (← locate oa, ← locate ob)
    let pre? ← match ia, ib with
      | none, none => throwError "realize: the loop guard{indentExpr (mkApp2 G D x)}\n\
          does not depend on the loop state"
      | none, _ => pure (some oa)
      | _, none => pure (some ob)
      | _, _ => pure none
    return (kind, ia, ib, pre?, ← mkLambdaFVars #[x] hg)
  let word ← encodingOf nat
  let envP ← if pre?.isSome then extend env nat word 1 else pure env
  let cmp := envP.k + l
  let pos (i? : Option Nat) : MetaM Expr := finLit cmp <| match i? with
    | none => k
    | some i => if i < k || pre?.isNone then i else i + 1
  let cond ← mkAppM kind #[← pos posA, ← pos posB]
  -- `X` at the loop environment `e`, whose first component is `d` when an operand is computed
  let atEnv (X e : Expr) : MetaM Expr := do
    return X.replaceFVar d (← if pre?.isSome then mkAppM ``Prod.fst #[e] else pure e)
  -- the body over the loop environment and the state, and the ghost cutoff
  let envB ← extend envP σ out l
  let (bodyN, cutoff) ← withLocalDeclD `y envB.ty fun y => do
    let e ← mkAppM ``Prod.fst #[y]
    let x ← mkAppM ``Prod.mk #[← atEnv D e, ← mkAppM ``Prod.snd #[y]]
    return (← mkLambdaFVars #[y] (mkApp (← atEnv step e) x), ← mkLambdaFVars #[y] (← atEnv n e))
  let hB ← realizeProg ctx envB bodyN (some out)
  let hq? ← queryPayment? bodyN envB.ty hB.work
  let hLoop ← match hq? with
    | some hq => mkAppM ``Realizes.while₀ #[envP.input, out, cond, cutoff, hB.proof, hq]
    | none => mkAppM ``Realizes.whileBounded #[envP.input, out, cond, cutoff, hB.proof]
  -- the initial state, then the loop
  let (hA, h) ← withLocalDeclD `e envP.ty fun e => do
    let ae ← atEnv a e
    let hA ← realizePure ctx envP e (envP.atoms.map (·.beta #[e])) ae out
    let (reply, next) ← withLocalDeclD `s state fun s => do
      return (← mkLambdaFVars #[e, s] ae, ← mkLambdaFVars #[e, s] s)
    return (hA, ← bindRun hA.proof hLoop reply next)
  -- the computed operand, then the initial state and the loop
  let (hC?, h, e₀) ← match pre? with
    | none => pure (none, h, d)
    | some c => do
      let hC ← realizePure ctx env d atoms c word
      let (reply, next) ← withLocalDeclD `s state fun s => do
        return (← mkLambdaFVars #[d, s] c, ← mkLambdaFVars #[d, s] s)
      pure (some hC, ← bindRun hC.proof h reply next, ← mkAppM ``Prod.mk #[d, c])
  -- the native guard at the loop environment, and its agreement with the client's
  let (gN, iN) ← withLocalDeclD `e envP.ty fun e => withLocalDeclD `a σ fun x => do
    let words ← mkAppM ``DFunLike.coe
      #[← mkAppM ``appendWords #[envP.input, out], ← mkAppM ``Prod.mk #[e, x]]
    let t ← mkAppM ``test #[cond, words]
    return (← mkLambdaFVars #[e, x] t,
      ← mkLambdaFVars #[e, x] (← synthInstance (← mkAppM ``Decidable #[t])))
  let (hgU, hgN, hbU, hbN) ← withLocalDeclD `a σ fun x => do
    let gU := mkApp2 G D x
    let gn := mkApp2 gN e₀ x
    let hgU ← mkExpectedTypeHint (guardIff.beta #[x]) (mkApp2 (mkConst ``Iff) gU gn)
    let bU := mkApp step (← mkAppM ``Prod.mk #[D, x])
    let bN := mkApp bodyN (← mkAppM ``Prod.mk #[e₀, x])
    let hbU ← mkExpectedTypeHint (← mkEqRefl bU) (← mkEq bU bN)
    return (← mkLambdaFVars #[x] hgU, ← mkLambdaFVars #[x] (← mkAppM ``Iff.symm #[hgU]),
      ← mkLambdaFVars #[x] hbU, ← mkLambdaFVars #[x] (← mkEqSymm hbU))
  -- the client's loop
  let prog := (← instantiateMVars (← inferType h)).getArg! 5
  let eq ← mkLambdaFVars #[d] (← mkExpectedTypeHint
    (← mkAppOptM ``boundedWhile_congr #[envP.ty, Δ, σ, gN, iN, G, inst, bodyN, step, e₀, D,
      hgN, hbN, n, a])
    (← mkEq (mkApp prog d) body))
  let h ← mkAppM ``Realizes.congr #[h, eq]
  -- the domain in the client's terms: the body's domain at the client's loop environment
  let pairTy ← mkAppM ``Prod #[Δ, σ]
  let safeB ← withLocalDeclD `w nat fun w => withLocalDeclD `x pairTy fun x =>
    withLocalDeclD `s state fun s => do
      let y ← mkAppM ``Prod.mk #[e₀, ← mkAppM ``Prod.snd #[x]]
      mkLambdaFVars #[w, x, s] (← reducePairs (hB.safe.beta #[w, y, s]))
  let safe ← withLocalDeclD `w nat fun w => withLocalDeclD `s state fun s => do
    let spec ← mkAppM ``Memory.spec #[w]
    let valid ← mkAppM ``StateTransitionSpec.ValidHistory
      #[spec, s, ← mkAppM ``StateTransitionSpec.clientHistory #[spec, s, body]]
    let loop ← mkArrow valid
      (← mkAppOptM ``whileSafe #[Δ, σ, G, inst, step, safeB, w, D, n, a, s])
    let dom := mkAnd (← reducePairs (hA.safe.beta #[w, e₀, s])) loop
    mkLambdaFVars #[w, d, s] <| match hC? with
      | some hC => mkAnd (hC.safe.beta #[w, d, s]) dom
      | none => dom
  -- the client's domain implies the native one under the loop's valid history
  let cv ← mkAppOptM ``Realizes.consequence_valid
    #[none, none, none, none, none, none, none, none, none, none, safe, h]
  let hsafeTy := (← whnf (← inferType cv)).bindingDomain!
  let hsafe ← withLocalDeclD `w nat fun w => withLocalDeclD `s state fun s => do
    forallBoundedTelescope (← instantiateForall hsafeTy #[w, d, s]) (some 4) fun hs goal => do
      let #[_, _, hv, hd] := hs | throwError "realize: internal error in the loop domain"
      let part (h : Expr) : MetaM (Expr × Expr) := do
        return (← mkAppM ``And.left #[h], ← mkAppM ``And.right #[h])
      let (hcs, rest) ← match hC? with
        | some _ => do let (p, q) ← part hd; pure (some p, q)
        | none => pure (none, hd)
      let (has, hloop) ← part rest
      let hsU ← withLocalDeclD `a σ fun x => withLocalDeclD `s state fun s' =>
        withLocalDeclD `hg (mkApp2 G D x) fun hg => do
          let hs := mkApp3 safeB w (← mkAppM ``Prod.mk #[D, x]) s'
          withLocalDeclD `h hs fun hh => do
            let hN := mkApp3 hB.safe w (← mkAppM ``Prod.mk #[e₀, x]) s'
            mkLambdaFVars #[x, s', hg, hh] (← mkExpectedTypeHint hh hN)
      let ws ← mkAppOptM ``whileSafe_imp #[Δ, envP.ty, σ, G, inst, gN, iN, step, bodyN, D, e₀,
        safeB, hB.safe, w, hgU, hbU, hsU, none, none, none, mkApp hloop hv]
      let dom ← mkAppM ``And.intro #[has, ws]
      let pf ← match hcs with
        | some p => mkAppM ``And.intro #[p, dom]
        | none => pure dom
      mkLambdaFVars (#[w, d, s] ++ hs) (← mkExpectedTypeHint pf goal)
  let proof := mkApp cv hsafe
  let work ← certificateWork proof
  if hq?.isSome then return { proof, output := out, safe, work }
  let clientWork ← withLocalDeclD `x pairTy fun x =>
    withLocalDeclD `s state fun s => do
      let y ← mkAppM ``Prod.mk #[e₀, ← mkAppM ``Prod.snd #[x]]
      mkLambdaFVars #[x, s] (← reducePairs (hB.work.beta #[y, s]))
  let work' ← withLocalDeclD `s state fun s => do
    mkLambdaFVars #[d, s] (← mkAppOptM ``whileWork
      #[Δ, σ, G, inst, step, clientWork, D, n, a, s])
  let hw ← withLocalDeclD `x σ fun x => withLocalDeclD `s state fun s => do
    let lhs := hB.work.beta #[← mkAppM ``Prod.mk #[e₀, x], s]
    let rhs := clientWork.beta #[← mkAppM ``Prod.mk #[D, x], s]
    mkLambdaFVars #[x, s] (← mkExpectedTypeHint (← mkEqRefl lhs) (← mkEq lhs rhs))
  let pointwise ← withLocalDeclD `s state fun s => do
    let h ← mkAppOptM ``whileWork_congr
      #[envP.ty, Δ, σ, gN, iN, G, inst, bodyN, step, e₀, D, hB.work, clientWork,
        hgN, hbN, hw, n, a, s]
    mkLambdaFVars #[s] (← mkExpectedTypeHint h
      (← mkEq (work.beta #[d, s]) (work'.beta #[d, s])))
  let workEq ← mkAppM ``funext #[← mkLambdaFVars #[d]
    (← mkAppM ``funext #[pointwise])]
  return { proof := ← transportField proof workEq 9, output := out, safe, work := work' }

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
  -- the reply and next memory in the client's terms, so that the domain is stated in them
  let (reply, next) ← withLocalDeclD `s (mkConst ``Memory.State) fun s => do
    let (r, s') ← replyState m s
    return (← mkLambdaFVars #[d, s] r, ← mkLambdaFVars #[d, s] s')
  let proof ← bindRun hP.proof hQ.proof reply next
  let safe ← withLocalDeclD `w (mkConst ``Nat) fun w =>
    withLocalDeclD `s (mkConst ``Memory.State) fun s => do
      let pair ← mkAppM ``Prod.mk #[d, reply.beta #[d, s]]
      let sq ← reducePairs (hQ.safe.beta #[w, pair, next.beta #[d, s]])
      mkLambdaFVars #[w, d, s] (mkAnd (hP.safe.beta #[w, d, s]) sq)
  return { proof, output := hQ.output, safe, work := ← certificateWork proof }

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

/-- Present an entry obligation in the same source context as its domain and work budget. -/
private def entryGoal (g : MVarId) (keepHistory : Bool) : MetaM MVarId := do
  let (xs, g) ← g.introN 7 [`w, `d, `s, `hwords, `hmem, `hv, `h]
  -- Preserve the existing zero-work context: clients may introduce their own `hv` from `h`.
  let g ← if keepHistory then pure g else g.clear xs[5]!
  g.withContext do
    let g ← g.replaceTargetDefEq (← Core.betaReduce (← g.getType))
    let hdecl := (← getLCtx).lastDecl.get!
    g.replaceLocalDeclDefEq hdecl.fvarId (← Core.betaReduce hdecl.type)

end Cslib.Tactic.Realize

namespace Cslib.WordRAM

open Lean Meta Elab Tactic Cslib.WordRAM Cslib.WordRAM.Realization Cslib.Tactic.Realize in
/-- Prove `Realizes B p input output safe work`, leaving genuine fit, domain and budget
conditions in the entry context, with valid history also available for nonzero generated work. -/
scoped elab "realize" : tactic => withMainContext do
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
  -- `realizeProg` states the certificate for `p` itself, with the domain `out.safe`
  let out ← realizeProg { basis := B, exact, standard } env p (some output)
  let cons ← mkAppOptM ``Realizes.consequence_work
    #[B, δ, args[3]!, args[0]!, args[1]!, p, input, output, out.safe, args[8]!,
      out.work, args[9]!, out.proof]
  let [hsafe, hwork] ← goal.apply cons | throwError "realize: internal error in `consequence`"
  setGoals [hwork]
  let zero ← isZeroWork δ out.work
  if zero then
    evalTactic (← `(tactic| exact fun _ _ _ _ _ _ _ => Nat.zero_le _))
  else
    evalTactic (← `(tactic| try exact fun _ _ _ _ _ _ _ => le_rfl))
  let workGoals ← (← getGoals).mapM fun g => liftMetaM (entryGoal g true)
  let g ← entryGoal hsafe (!zero)
  setGoals [g]
  evalTactic (← `(tactic|
    try simp only [true_and, and_true, and_self, Nat.add_zero, iterationSafe_true]))
  let gs ← getGoals
  let gs ← gs.flatMapM fun g => liftMetaM (splitDomain g)
  -- A condition repeated in the same local context is proved once.
  let mut kept : Array MVarId := #[]
  for g in gs do
    let t ← instantiateMVars (← g.getType)
    let lctx := (← g.getDecl).lctx
    let dup? ← kept.findM? fun g' => do
      return (← g'.getDecl).lctx.getFVarIds == lctx.getFVarIds &&
        (← instantiateMVars (← g'.getType)) == t
    match dup? with
    | some g' => g.assign (mkMVar g')
    | none => kept := kept.push g
  setGoals (kept.toList ++ workGoals)

end Cslib.WordRAM
