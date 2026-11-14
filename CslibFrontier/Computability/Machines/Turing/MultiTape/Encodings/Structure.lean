/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.FunProp
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Degree.Bounds
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.FunProp
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimePrimitives
public meta import Lean.Elab.Command

/-!
# Encodings of structures as the tuple of their fields

`enc_structure eS : S where f₁ : e₁, …, fₙ : eₙ` declares the encoding of a structure as the framed
tuple of its fields, with everything a certificate needs to work with it:

* `eSFields`, the encoding of the tuple, and `eS`, the encoding of the structure;
* `eS_apply`, unfolding `eS` to `eSFields` of the tuple;
* `eS_fields_deg`, the linear map from a structure to the tuple of its fields;
* for each field `f`, the linear rules `eS_f_deg` and `eS_f_inO`, `eS_f_budget` retaining a
  caller's workspace budget, and `eS_f_polyTime` reading the field of a polynomial-time structure;
* for each field `f`, `eS_f_length_le` bounds its encoded word by the record word length;
* for each `flattened toParent : eParent` annotation, the same four rules for the parent projection;
* the constructor rules `eS_mk_deg` on tuples, `eS_mk_inO` adding up the bounds of its arguments,
  `eS_mk_budget` constructing a record whose fields share a workspace budget, and `eS_mk_polyTime`.

Public rules are registered as `scoped` `fun_prop` rules, activated by the declaration's
namespace. Private rules are registered with `local fun_prop` in the defining scope and are not
exported to importers. The optional `public` or `private` prefix sets the visibility of the
encoding, tuple abbreviation and every generated rule. Without a prefix all are public, even
outside a `public section`; `private enc_structure` keeps them private.

An applied structure type is also accepted: with `variable {n : ℕ}`, write
`enc_structure eS : S n where ...`. The parameter remains implicit in the generated declarations.

Explicit parameters can also be arguments of the command, for example
`enc_structure eRecord (α : Type) (eα : α ↪ List Bool) : Record α where value : eα, tag : encBits`.
The parameters are explicit arguments of every generated declaration, in the same order. Implicit
and instance parameters come from `variable`, as above. The generated binders keep plain names
(`a`, `x0`, `h0`, `γ`, …) for named arguments, unless the command's own terms use that name.

The fields `f₁, …, fₙ` must be the fields of `S`, each once and in declaration order, since that
order fixes the encoded words. A parent structure is listed either as its single field `toParent`,
encoded as one word, or as its own fields in place of `toParent`, which flattens them into the
tuple. In the latter case, `flattened toParent : eParent` additionally declares the parent encoding
and generates projection rules. Their proofs elaborate only when `eParent` has exactly the selected
word layout, so the annotation cannot silently change the encoding. `S` must be a structure, not a
class. The command checks this before declaring anything, and names the first unknown, repeated or
misplaced field, or all missing ones.

## Fields whose type depends on an earlier field

A field whose type mentions an earlier field, such as `element : Carrier desc`, is encoded as a word
by a function of the earlier fields: `element : (encode desc) using (encode_injective desc)` encodes
it as `encode desc element` in the slot `encBits`, where the term after `using` proves
`Function.Injective (encode desc)`. Both terms may name earlier fields, including through a listed
parent field, as in `toElement.desc`; each such name reads the field of the encoded structure. A
binder in these terms must not reuse the name of an earlier field, and an explicit parameter that
they mention must not share its name with an earlier field: the command reports the latter. The
field rules read the word `encode x.desc x.element`, and the constructor rules take each such
argument as a dependent function with a certificate for its word. There is no `eS_mk_deg` for such
a structure, since its tuple holds words rather than fields. An explicit parameter that only these
terms use does not occur in `eSFields`, which still takes it, like every generated declaration.
The command then marks `eSFields` `nolint unusedArguments`, provided these terms use every
parameter that `eSFields` does not. Both sides are decided on the elaborated terms, as by the
linter: a parameter is used when it occurs free, so a local binder that shares its name is not a
use. Otherwise `eSFields` stays linted, so a parameter that nothing uses is reported.
-/

public meta section

namespace Turing.MultiTapeTM

open Lean Elab Command Lean.Parser.Command

/-- `enc_structure eS : S where f₁ : e₁, f₂ : e₂` declares the encoding `eS` of the structure `S`
as the tuple of its fields encoded by `e₁`, `e₂`, with its rules. List every field of `S` once, in
declaration order, listing a parent either as `toParent` or as its fields; the command reports an
unknown, repeated or misplaced field, or all missing ones. Before `where`,
`flattened toParent : eParent` declares the encoding of a flattened parent and generates its
projection rules, provided its encoded word is definitionally the selected field tuple. A field
whose type depends on earlier fields is written `f : w using hw`, encoding it as the word `w f` for
an injective `w`. Explicit parameters `(p : T)` before the colon become explicit arguments of every
generated declaration. An optional `public` or `private` prefix applies to every generated
declaration; the default is public, independently of the surrounding section. Public `fun_prop`
rules are scoped; private ones are registered locally and do not export. -/
syntax (name := encStructure) (docComment)? (visibility)? "enc_structure " ident
  (" (" ident " : " term ")")* " : " term (" flattened " ident " : " term:max)* " where "
  (ident " : " term:max (" using " term:max)?),+ : command

private def app (base : Name) (suffix : String) : Ident :=
  mkIdent (base.appendAfter suffix)

/-- The tuple `(t₁, (t₂, …))`. -/
private def tuple (ts : Array Term) : MacroM Term := do
  let mut r := ts.back!
  for t in ts.pop.reverse do
    r ← `(($t, $r))
  return r

/-- The encoding `encPair e₁ (encPair e₂ …)`, or just `e₁` for one slot. -/
private def tupleEncoding (es : Array Term) : MacroM Term := do
  let mut r := es.back!
  for e in es.pop.reverse do
    r ← `(encPair $e $r)
  return r

/-- `h.snd'…snd'.fst'`: component `i` of the `n`-tuple `h`, for `ns` the calculus namespace. -/
private def component (ns : Name) (h : Term) (i n : Nat) : MacroM Term := do
  let snd := mkIdent (ns ++ `snd')
  let fst := mkIdent (ns ++ `fst')
  let mut r := h
  for _ in [0:i] do
    r ← `($snd $r)
  if i + 1 < n then r ← `($fst $r)
  return r

/-- The path of fields from the structure `s` to its field `n`, through parent fields when `n` is
inherited. -/
private partial def fieldPath? (env : Environment) (s n : Name) : Option (Array Name) :=
  if (getStructureFields env s).contains n then some #[n] else
    (getStructureFields env s).findSome? fun p =>
      (isSubobjectField? env s p).bind fun parent =>
        (fieldPath? env parent n).map (#[p] ++ ·)

/-- The fields of `s` to encode, given the listed paths: a parent field is replaced by its own
fields when a listed path passes through it. -/
private partial def frontier (env : Environment) (s : Name) (prefix_ : Array Name)
    (listed : Array (Array Name)) : Array (Array Name) :=
  (getStructureFields env s).flatMap fun f =>
    let p := prefix_.push f
    match isSubobjectField? env s f with
    | some parent =>
      if listed.any fun q => q.size > p.size && q.extract 0 p.size == p then
        frontier env parent p listed
      else #[p]
    | none => #[p]

/-- The projections along `path` from the structure `s`. -/
private def pathProjs (env : Environment) (s : Name) (path : Array Name) : Array Name := Id.run do
  let mut cur := s
  let mut r := #[]
  for f in path do
    r := r.push (cur ++ f)
    if let some p := isSubobjectField? env cur f then cur := p
  return r

/-- The field of `x` that the projections `projs` read. -/
private def readPath (projs : Array Name) (x : Term) : MacroM Term :=
  projs.foldlM (fun t c => `($(mkCIdent c) $t)) x

/-- The constructor of `s` applied to `leaf p` for each encoded path `p`, nesting the constructor
of each parent that the paths flatten. -/
private partial def nestCtor (env : Environment) (s : Name) (prefix_ : Array Name)
    (paths : Array (Array Name)) (leaf : Array Name → Term) : MacroM Term := do
  let args ← (getStructureFields env s).mapM fun f => do
    let p := prefix_.push f
    if paths.contains p then return leaf p
    match isSubobjectField? env s f with
    | some parent => `(($(← nestCtor env parent p paths leaf)))
    | none => Macro.throwError s!"enc_structure: no encoded path for the field {p}"
  return Syntax.mkApp (mkCIdent (getStructureCtor env s).name) args

/-- The first component of every identifier in `stx`. -/
private partial def identRoots (stx : Syntax) : Array Name :=
  match stx with
  | .ident _ _ n _ => #[n.getRoot]
  | .node _ _ args => args.flatMap identRoots
  | _ => #[]

/-- Replace each identifier `names[i]` in `t` by `vals[i]`, and the root of a dotted identifier
`names[i].f.g` by `vals[i]`, keeping `.f.g` as projections. -/
private def substIdents (names : Array Name) (vals : Array Term) (t : Term) : MacroM Term := do
  let r ← t.raw.replaceM fun stx => do
    if let .ident info _ n _ := stx then
      if let some i := names.idxOf? n then
        return some (← `(($(vals[i]!)))).raw
      if let some i := names.idxOf? n.getRoot then
        let mut r : Syntax := (← `(($(vals[i]!)))).raw
        for c in n.components.drop 1 do
          r := Syntax.node info ``Lean.Parser.Term.proj #[r, mkAtom ".", mkIdent c]
        return some r
    return none
  return ⟨r⟩

/-- The structure that `S` names and the paths of the listed fields, after checking that `S` is not
a class and that `fs` lists every field of it once, in declaration order, with each parent either
listed or replaced by its fields. Otherwise report the first unknown, repeated or misplaced field,
or all missing ones. -/
private def checkFields (S : Term) (fs : Array Ident) : CommandElabM (Name × Array (Array Name)) :=
  do
  let head ← match S with
    | `($id:ident) => pure id
    | `($id:ident $_args*) => pure id
    | _ => throwErrorAt S
        "enc_structure: expected a structure name, optionally applied to parameters"
  let s ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo head
  let env ← getEnv
  let sName := MessageData.ofConstName s
  unless isStructure env s do
    throwErrorAt S "enc_structure: `{sName}` is not a structure"
  if isClass env s then
    throwErrorAt S "enc_structure: `{sName}` is a class; only structures, whose fields are \
      explicit, can be encoded"
  let found := fs.filterMap fun f => fieldPath? env s f.getId
  let expected := frontier env s #[] found
  let order := m!"the fields of `{sName}` in declaration order are \
    {MessageData.joinSep (expected.toList.map fun p => m!"`{p.back!}`") ", "}"
  let mut seen : Array (Array Name) := #[]
  for f in fs do
    let n := f.getId
    let some p := fieldPath? env s n |
      throwErrorAt f "enc_structure: `{n}` is not a field of `{sName}`; {order}"
    let some i := expected.idxOf? p | do
      let child := (found.find? fun q => q.size > p.size && q.extract 0 p.size == p).map (·.back!)
      throwErrorAt f "enc_structure: the parent field `{n}` and its field `{child.getD n}` are \
        both listed; list either the parent field or its fields; {order}"
    if seen.contains p then
      throwErrorAt f "enc_structure: field `{n}` is listed twice; {order}"
    if let some prev := seen.back? then
      if i < expected.idxOf prev then
        throwErrorAt f "enc_structure: field `{n}` must come before `{prev.back!}`; {order}"
    seen := seen.push p
  let missing := expected.filter (!seen.contains ·)
  unless missing.isEmpty do
    let names := MessageData.joinSep (missing.toList.map fun p => m!"`{p.back!}`") ", "
    throwErrorAt S "enc_structure: missing {if missing.size = 1 then "field" else "fields"} \
      {names} of `{sName}`; {order}"
  return (s, seen)

/-- Whether `e` is the local `x` or reads a field of it through projections. -/
private partial def readsLocal (env : Environment) (x : Expr) (e : Expr) : Bool :=
  match e.consumeMData with
  | .fvar _ => e.consumeMData == x
  | .proj _ _ s => readsLocal env x s
  | e => match e.getAppFn with
    | .const c _ => match env.getProjectionFnInfo? c with
      | some info => e.getAppNumArgs == info.numParams + 1 && readsLocal env x e.appArg!
      | none => false
    | _ => false

/-- Whether the free variable `p` occurs in `e` outside the reads of the local `x`. -/
private def occursOutsideReads (env : Environment) (x p : Expr) (e : Expr) : Bool :=
  (e.replace fun s => if readsLocal env x s then some x else none).containsFVar p.fvarId!

/-- Whether `fieldsDecl` has an explicit parameter among `ps` that it does not use, and the word
or injectivity proof of a dependent field uses every such parameter. The unused parameters are
those that occur free in neither the value nor the type of `fieldsDecl` nor the type of another
parameter, as for the `unusedArguments` linter. `depTerms x` gives each dependent field's word and
proof, reading the earlier fields from `x : S`. These terms are elaborated against a local
`x : S`, and a parameter counts as used only when it occurs free in them outside the reads of `x`,
so a local binder that shares its name is not a use. Any failure leaves the declaration linted. -/
private def usingOnlyParams (fieldsDecl : Name) (ps : Array Ident) (S : Term)
    (depTerms : Term → MacroM (Array (Term × Term))) : CommandElabM Bool := liftTermElabM do
  let env ← getEnv
  let some ci ← withoutExporting do return (← getEnv).find? fieldsDecl | return false
  let some val := ci.value? | return false
  Meta.forallTelescope ci.type fun xs body => do
    if xs.size < ps.size then return false
    let params := xs.extract (xs.size - ps.size) xs.size
    for p in ps, v in params do
      unless (← v.fvarId!.getUserName) == p.getId do return false
    let value := val.beta xs
    let others (v : Expr) : MetaM Bool := xs.anyM fun w => do
      return w != v && (← w.fvarId!.getType).containsFVar v.fvarId!
    let unused ← params.filterM fun v => do
      return !value.containsFVar v.fvarId! && !body.containsFVar v.fvarId! && !(← others v)
    if unused.isEmpty then return false
    let s ← Term.saveState
    try
      Term.withoutErrToSorry do
        let sType ← Term.elabType S
        let xId := mkIdent (← withFreshMacroScope <| MonadQuotation.addMacroScope `x)
        Meta.withLocalDeclD xId.getId sType fun x => do
          let mut found : Array Expr := #[]
          for (w, hw) in ← liftMacroM (depTerms xId) do
            let wE ← Term.elabTerm w none
            let hwE ← Term.elabTerm hw (← Term.elabType (← `(Function.Injective $w)))
            Term.synthesizeSyntheticMVarsNoPostponing
            found := found.push (← instantiateMVars wE) |>.push (← instantiateMVars hwE)
          return unused.all fun v => found.any (occursOutsideReads env x v ·)
    catch _ => pure false
    finally s.restore (restoreInfo := true)

/-- Check that each annotated projection is a distinct parent field whose fields are flattened by
`paths`, and return its path and the indices of its encoded descendants. -/
private def checkFlattenedParents (env : Environment) (s : Name)
    (paths : Array (Array Name)) (parents : Array Ident) : CommandElabM
    (Array (Array Name × Array Nat)) := do
  let sName := MessageData.ofConstName s
  let mut seen : Array (Array Name) := #[]
  let mut checked := #[]
  for parent in parents do
    let n := parent.getId
    let some path := fieldPath? env s n |
      throwErrorAt parent "enc_structure: `{n}` is not a field of `{sName}`"
    let mut cur := s
    for f in path do
      let some next := isSubobjectField? env cur f |
        throwErrorAt parent "enc_structure: `{n}` is a field of `{sName}`, but not a parent field"
      cur := next
    if seen.contains path then
      throwErrorAt parent "enc_structure: flattened parent `{n}` is listed twice"
    let indices := (Array.range paths.size).filter fun i =>
      let p := paths[i]!
      p.size > path.size && p.extract 0 path.size == path
    if indices.isEmpty then
      throwErrorAt parent "enc_structure: parent field `{n}` is not flattened by the listed fields"
    seen := seen.push path
    checked := checked.push (path, indices)
  return checked

/-- Elaborate `enc_structure`: the encoding, its unfolding lemma and its rules. -/
@[command_elab encStructure] def elabEncStructure : CommandElab := fun stx => do
  let `($[$doc:docComment]? $[$vis:visibility]? enc_structure $eS:ident
      $[($ps:ident : $pts:term)]* : $S:term
      $[flattened $parents:ident : $parentEncs:term]* where
      $[$fs:ident : $es:term $[using $hws:term]?],*) :=
    stx | throwUnsupportedSyntax
  -- The syntax declaration parses both as terms; the repeated antiquotations are untyped.
  let pts : Array Term := pts.map (⟨·⟩)
  let es : Array Term := es.map (⟨·⟩)
  let parentEncs : Array Term := parentEncs.map (⟨·⟩)
  let vis : TSyntax ``Lean.Parser.Command.visibility ← match vis with
    | some v => pure v
    | none => `(visibility| public)
  let privateRules := match vis with
    | `(visibility| private) => true
    | _ => false
  let registerRule (decl : Ident) : CommandElabM Unit := do
    if privateRules then
      elabCommand (← `(attribute [local fun_prop] $decl:ident))
    else
      elabCommand (← `(attribute [scoped fun_prop] $decl:ident))
  let (s, paths) ← checkFields S fs
  let env ← getEnv
  let checkedParents ← checkFlattenedParents env s paths parents
  let name := eS.getId
  let n := fs.size
  let names := fs.map (·.getId)
  -- A dependent field's terms read earlier fields by name, which would shadow a parameter.
  for i in [0:n] do
    if let some hw := hws[i]! then
      let roots := identRoots es[i]! ++ identRoots hw
      for p in ps do
        if names.extract 0 i |>.contains p.getId then
          if roots.contains p.getId then
            throwErrorAt p "enc_structure: the parameter `{p.getId}` has the name of a field \
              that the word of `{names[i]!}` reads; rename the parameter"
  let projs := paths.map (pathProjs env s)
  -- A structure is simple when each field is its own word: no flattened parent or dependent field.
  let dependent := hws.any (·.isSome)
  let simple := !dependent && paths.all (·.size == 1)
  let params ← ps.zip pts |>.mapM fun (p, t) => `(bracketedBinder| ($p:ident : $t))
  let applied (id : Ident) : Term := Syntax.mkApp id (ps.map (fun p => (⟨p.raw⟩ : Term)))
  let eSTerm := applied eS
  -- The annotation fixes implicit section parameters even for a field that does not mention them.
  let encRef : Term ← `(($eSTerm : $S ↪ List Bool))
  -- Binders that callers may name keep plain names, unless the command's own terms use the name.
  let userNames := ps.map (·.getId) ++ identRoots S ++ pts.flatMap (identRoots ·) ++
    es.flatMap (identRoots ·) ++ parentEncs.flatMap (identRoots ·) ++
      hws.flatMap fun | some hw => identRoots hw | none => #[]
  let freshIdent (base : Name) : CommandElabM Ident := do
    return mkIdent (← withFreshMacroScope <| MonadQuotation.addMacroScope base)
  let plainIdent (base : Name) : CommandElabM Ident :=
    if userNames.contains base then freshIdent base else pure (mkIdent base)
  let a ← plainIdent `a
  -- The slot encoding of each field: `encBits` for a dependent field's word.
  let slots ← (Array.range n).mapM fun i => do
    if hws[i]!.isSome then `(encBits) else pure es[i]!
  -- `wordFn i vals`: the word function of the dependent field `i`, earlier fields having `vals`.
  let wordFn (i : Nat) (vals : Array Term) : MacroM Term :=
    substIdents (names.extract 0 i) (vals.extract 0 i) es[i]!
  -- `word i vals x`: the word of field `i` with value `x`, earlier fields having values `vals`.
  let word (i : Nat) (vals : Array Term) (x : Term) : MacroM Term := do
    if hws[i]!.isSome then `($(← wordFn i vals) $x) else pure x
  -- The word of field `i` of the structure `x`.
  let wordOf (i : Nat) (x : Term) : MacroM Term := do
    let reads ← projs.mapM (readPath · x)
    word i reads reads[i]!
  let fields := app name "Fields"
  let fieldsOf ← liftMacroM do tuple (← (Array.range n).mapM fun i => wordOf i a)
  let encoding ← liftMacroM <| tupleEncoding slots
  let fieldsTerm := applied fields
  let linE : Term ← `(fun a => List.length ($encRef a))
  elabCommand (← `($vis:visibility abbrev $fields:ident $params* := $encoding))
  let fieldsDecl ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo fields
  addDocStringCore fieldsDecl s!"The tuple of the fields of `{name}`."
  -- `eSFields` takes every parameter, so that all generated declarations share one argument list.
  -- A parameter that only a dependent field's word or proof uses reaches no slot. Mark
  -- `eSFields` only when those terms use every parameter that it does not, so that the linter
  -- still reports a parameter that nothing uses.
  if dependent then
    let depTerms (x : Term) : MacroM (Array (Term × Term)) := do
      let reads ← projs.mapM (readPath · x)
      (Array.range n).filterMapM fun i => do
        let some hw := hws[i]! | return none
        return some (← wordFn i reads, ← substIdents (names.extract 0 i) (reads.extract 0 i) hw)
    if ← usingOnlyParams fieldsDecl ps S depTerms then
      elabCommand (← `(attribute [nolint unusedArguments] $fields:ident))
  let inj : Term ← if simple then `(fun x y h => by cases x; cases y; simp_all) else do
    -- Match both structures, then recover each field from its word in field order, replacing the
    -- right field by the left one.
    let ls ← (Array.range n).mapM fun i => freshIdent (Name.mkSimple s!"l{i}")
    let rs ← (Array.range n).mapM fun i => freshIdent (Name.mkSimple s!"r{i}")
    let h ← freshIdent `h
    let t ← freshIdent `t
    let leaf (xs : Array Ident) (p : Array Name) : Term := ⟨xs[paths.idxOf p]!.raw⟩
    let lhs ← liftMacroM <| nestCtor env s #[] paths (leaf ls)
    let rhs ← liftMacroM <| nestCtor env s #[] paths (leaf rs)
    let lTerms : Array Term := ls.map (⟨·.raw⟩)
    let mut tacs : Array (TSyntax `tactic) := #[]
    for i in [0:n] do
      let e ← freshIdent (Name.mkSimple s!"e{i}")
      let wl ← liftMacroM <| word i lTerms lTerms[i]!
      let wr ← liftMacroM <| word i lTerms ⟨rs[i]!.raw⟩
      let comp ← liftMacroM do
        let mut r : Term := t
        for _ in [0:i] do r ← `(($r).2)
        if i + 1 < n then r ← `(($r).1)
        return r
      tacs := tacs.push (← `(tactic| have $e:ident : $wl = $wr := congrArg (fun $t => $comp) $h))
      if let some hw := hws[i]! then
        let hw ← liftMacroM <| substIdents (names.extract 0 i) (lTerms.extract 0 i) hw
        let w ← liftMacroM <| wordFn i lTerms
        tacs := tacs.push (← `(tactic| replace $e:ident := ($hw : Function.Injective $w) $e))
      tacs := tacs.push (← `(tactic| subst $(rs[i]!):ident))
    let mut tac ← `(tactic| rfl)
    for t' in tacs.reverse do
      tac ← `(tactic| ($t'; $tac))
    `(fun x y => match x, y with | $lhs, $rhs => fun $h => by $tac:tactic)
  elabCommand (← `($[$doc:docComment]? @[expose]
    $vis:visibility def $eS:ident $params* : $S ↪ List Bool :=
      (⟨fun $a => $fieldsOf, $inj⟩ : $S ↪ _).trans $fieldsTerm))
  elabCommand (← `(@[simp] $vis:visibility theorem $(app name "_apply") $params* ($a : $S) :
    $encRef $a = $fieldsTerm $fieldsOf := rfl))
  let fieldsDeg := app name "_fields_deg"
  let fieldsDegTerm := applied fieldsDeg
  elabCommand (← `($vis:visibility theorem $fieldsDeg:ident $params* :
    ComputableInDegree (fun $a : $S => $fieldsOf) $encRef $fieldsTerm 1 1 :=
      ComputableInDegree.of_eq fun _ => rfl))
  let g ← freshIdent `g
  let c ← freshIdent `c
  let declareProjectionRules (projection : Name) (fn compFn e degBody : Term) :
      CommandElabM Unit := do
    let deg := app name s!"_{projection}_deg"
    let degTerm := applied deg
    elabCommand (← `($vis:visibility theorem $deg:ident $params* :
      ComputableInDegree $fn $encRef $e 1 1 := $degBody))
    registerRule deg
    let inO := app name s!"_{projection}_inO"
    elabCommand (← `($vis:visibility theorem $inO:ident $params* :
      ComputableInO $fn $encRef $e $linE $linE := ComputableInDegree.inO_one $degTerm))
    registerRule inO
    let budgetRule := app name s!"_{projection}_budget"
    elabCommand (← `($vis:visibility theorem $budgetRule:ident $params*
      {γ : Type} {encIn : γ ↪ List Bool} {S : γ → ℕ} {$g : γ → $S}
      (h : ComputableInSpace $g encIn $encRef S) :
      ComputableInSpace $compFn encIn $e S :=
        ComputableInSpace.budget_comp_linear (f := $g) (g := $fn)
          (ComputableInSpace.of_inO (ComputableInDegree.inO_one $degTerm)) h))
    registerRule budgetRule
    let polyRule := app name s!"_{projection}_polyTime"
    elabCommand (← `($vis:visibility theorem $polyRule:ident $params*
      {γ : Type} {encIn : γ ↪ List Bool} {$g : γ → $S}
      (h : ComputableInPolyTime $g encIn $encRef) :
      ComputableInPolyTime $compFn encIn $e :=
        ComputableInPolyTime.comp (f := $fn) (g := $g)
          (ComputableInDegree.computableInPolyTime $degTerm) h))
    registerRule polyRule
  for f in fs, e in slots, i in Array.range n do
    -- The field read, as a function of the structure and applied to `g c`.
    let fn : Term ← if simple then pure (mkCIdent (s ++ f.getId)) else
      `(fun $a : $S => $(← liftMacroM <| wordOf i a))
    let ofG : Term ← if simple then `($(mkCIdent (s ++ f.getId)) ($g $c)) else
      liftMacroM <| wordOf i (← `(($g $c)))
    let compFn : Term ← `(fun $c => $ofG)
    let degBody ←
      liftMacroM <| component `Turing.MultiTapeTM.ComputableInDegree fieldsDegTerm i n
    declareProjectionRules f.getId fn compFn e degBody
    -- Size bounds describe encoded words, independently of a realizing machine's constants.
    let lengthRule := app name s!"_{f.getId}_length_le"
    let applyName := app name "_apply"
    elabCommand (← `($vis:visibility theorem $lengthRule:ident $params* ($a : $S) :
      ($e ($fn $a)).length ≤ ($encRef $a).length := by
        simp only [$applyName:ident, $fields:ident, length_encPair, encBits_apply] <;> omega))
  for parent in parents, parentEnc in parentEncs, checked in checkedParents do
    let (path, indices) := checked
    let parentProjs := pathProjs env s path
    let parentFn : Term ← `(fun $a : $S => $(← liftMacroM <| readPath parentProjs a))
    let parentOfG : Term ←
      `(fun $c => $(← liftMacroM <| readPath parentProjs (← `(($g $c)))))
    let mut parentDeg ← liftMacroM <|
      component `Turing.MultiTapeTM.ComputableInDegree fieldsDegTerm indices.back! n
    for i in indices.pop.reverse do
      let fieldDeg ← liftMacroM <|
        component `Turing.MultiTapeTM.ComputableInDegree fieldsDegTerm i n
      parentDeg ← `(ComputableInDegree.prod $fieldDeg $parentDeg)
    let degBody : Term ← `(ComputableInDegree.of_enc_eq $parentDeg fun _ => rfl)
    declareProjectionRules parent.getId parentFn parentOfG parentEnc degBody
  let p ← plainIdent `p
  let comps ← (List.range n).toArray.mapM fun i => do
    let mut t : Term ← `($p)
    for _ in [0:i] do
      t ← `(($t).2)
    if i + 1 < n then t ← `(($t).1)
    return t
  unless dependent do
    let mkApp ← liftMacroM <| nestCtor env s #[] paths fun q => comps[paths.idxOf q]!
    elabCommand (← `($vis:visibility theorem $(app name "_mk_deg"):ident $params* :
      ComputableInDegree (fun $p => $mkApp) $fieldsTerm $encRef 1 1 :=
        ComputableInDegree.of_eq fun _ => rfl))
    registerRule (app name "_mk_deg")
  -- the constructor, adding up the bounds of its arguments
  let names' (stem : String) :=
    (Array.range n).mapM fun i => plainIdent (Name.mkSimple s!"{stem}{i}")
  let xs ← names' "x"
  let hs ← names' "h"
  let Ts ← names' "T"
  let Ss ← names' "S"
  let xN (i : Nat) := xs[i]!
  let hN (i : Nat) := hs[i]!
  let TN (i : Nat) := Ts[i]!
  let SN (i : Nat) := Ss[i]!
  let x ← plainIdent `x
  let last := n - 1
  let mut sumT : Term ← `($(TN last) $x:ident)
  let mut sumS : Term ← `($(SN last) $x:ident)
  let mut prod : Term := hN last
  let mut prodPoly : Term := hN last
  for i in (List.range last).reverse do
    sumT ← `($(TN i) $x:ident + $sumT)
    sumS ← `($(SN i) $x:ident + $sumS)
    prod ← `(ComputableInO.prod $(hN i) $prod)
    prodPoly ← `(ComputableInPolyTime.prod $(hN i) $prodPoly)
  let args ← (Array.range n).mapM fun i => (`($(xN i) $x:ident) : CommandElabM Term)
  let appl ← liftMacroM <| nestCtor env s #[] paths fun q => args[paths.idxOf q]!
  let γ ← plainIdent `γ
  let encIn ← plainIdent `encIn
  -- The argument functions, dependent when a field's type mentions an earlier field.
  let xBinder (i : Nat) : CommandElabM (TSyntax ``Lean.Parser.Term.bracketedBinder) :=
    if simple then `(bracketedBinder| {$(xN i) : $γ → _})
    else `(bracketedBinder| {$(xN i) : ($c : $γ) → _})
  -- The function whose certificate the constructor rules take for argument `i`.
  let argFun (i : Nat) : CommandElabM Term := do
    if hws[i]!.isSome then
      let vals ← (Array.range n).mapM fun j => (`(($(xN j) $c)) : CommandElabM Term)
      `(fun $c => $(← liftMacroM <| word i vals vals[i]!))
    else pure (xN i)
  let mut binders : TSyntaxArray ``Lean.Parser.Term.bracketedBinder := #[]
  for i in [0:n] do
    binders := binders.push (← xBinder i)
    binders := binders.push (← `(bracketedBinder| {$(TN i) $(SN i) : $γ → ℕ}))
  for e in slots, i in Array.range n do
    binders := binders.push (← `(bracketedBinder|
      ($(hN i) : ComputableInO $(← argFun i) $encIn $e $(TN i) $(SN i))))
  elabCommand (← `($vis:visibility theorem $(app name "_mk_inO"):ident
    $params* {$γ : Type}
    {$encIn : $γ ↪ List Bool} $binders* :
    ComputableInO (fun $x => $appl) $encIn $encRef (fun $x => $sumT) fun $x => $sumS :=
      ComputableInO.of_enc_eq $prod fun _ => rfl))
  registerRule (app name "_mk_inO")
  let mut polyBinders : TSyntaxArray ``Lean.Parser.Term.bracketedBinder := #[]
  for j in [0:n] do
    polyBinders := polyBinders.push (← xBinder j)
  for e in slots, j in Array.range n do
    polyBinders := polyBinders.push (← `(bracketedBinder|
      ($(hN j) : ComputableInPolyTime $(← argFun j) $encIn $e)))
  elabCommand (← `($vis:visibility theorem $(app name "_mk_polyTime"):ident
    $params* {$γ : Type}
    {$encIn : $γ ↪ List Bool} $polyBinders* :
    ComputableInPolyTime (fun $x => $appl) $encIn $encRef :=
      ComputableInPolyTime.of_enc_eq $prodPoly fun _ => rfl))
  registerRule (app name "_mk_polyTime")
  let budget ← plainIdent `budget
  let mut budgetBinders : TSyntaxArray ``Lean.Parser.Term.bracketedBinder := #[]
  for j in [0:n] do
    budgetBinders := budgetBinders.push (← xBinder j)
  for e in slots, j in Array.range n do
    budgetBinders := budgetBinders.push (← `(bracketedBinder|
      ($(hN j) : ComputableInSpace $(← argFun j) $encIn $e $budget)))
  let mut budgetProd : Term := hN last
  for j in (List.range last).reverse do
    budgetProd ← `(ComputableInSpace.budget_prod $(hN j) $budgetProd)
  elabCommand (← `($vis:visibility theorem $(app name "_mk_budget"):ident
    $params* {$γ : Type}
    {$encIn : $γ ↪ List Bool} {$budget : $γ → ℕ} $budgetBinders* :
    ComputableInSpace (fun $x => $appl) $encIn $encRef $budget :=
      ComputableInSpace.of_enc_eq $budgetProd fun _ => rfl))
  registerRule (app name "_mk_budget")

end Turing.MultiTapeTM
