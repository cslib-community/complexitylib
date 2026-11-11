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
* the constructor rules `eS_mk_deg` on tuples, `eS_mk_inO` adding up the bounds of its arguments,
  `eS_mk_budget` constructing a record whose fields share a workspace budget, and `eS_mk_polyTime`.

The rules are `scoped` `fun_prop` rules, so that a program using the structure is assembled by
`fun_prop` inside the namespace of the declaration.

For a parameterized record, supply explicit parameters and apply its type, for example
`enc_structure eRecord (α : Type) (eα : α ↪ List Bool) : Record α where value : eα, tag : encBits`.
The parameters are explicit arguments of every generated declaration, in the same order.

The fields `f₁, …, fₙ` must be the fields of `S` (as `getStructureFields` lists them, so a parent
structure is the single field `toParent`), each once and in declaration order, since that order
fixes the encoded words. `S` must be a structure, not a class. The command checks this before
declaring anything, and names the first unknown, repeated or misplaced field, or all missing ones.
-/

public meta section

namespace Turing.MultiTapeTM

open Lean Elab Command

/-- `enc_structure eS : S where f₁ : e₁, f₂ : e₂` declares the encoding `eS` of the structure `S`
as the tuple of its fields encoded by `e₁`, `e₂`, with its rules. List every field of `S` once, in
declaration order; the command reports an unknown, repeated or misplaced field, or all missing
ones. -/
syntax (name := encStructure) (docComment)? "enc_structure " ident
  (" (" ident " : " term ")")* " : " term " where "
  (ident " : " term:max),+ : command

private def app (base : Name) (suffix : String) : Ident :=
  mkIdent (base.appendAfter suffix)

/-- The tuple `(t₁, (t₂, …))`. -/
private def tuple (ts : Array Term) : MacroM Term := do
  let mut r := ts.back!
  for t in ts.pop.reverse do
    r ← `(($t, $r))
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

/-- The parent field of the structure `s` through which `s` inherits the field `n`, if any. -/
private def parentField? (env : Environment) (s n : Name) : Option Name :=
  (getStructureFields env s).find? fun p =>
    match isSubobjectField? env s p with
    | some parent => (getStructureFieldsFlattened env parent).contains n
    | none => false

/-- The structure that `S` names, after checking that it is not a class and that `fs` lists every
field of it once, in declaration order. Otherwise report the first unknown, repeated or misplaced
field, or all missing ones. -/
private def checkFields (S : Term) (fs : Array Ident) : CommandElabM Name := do
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
  let expected := getStructureFields env s
  let order := m!"the fields of `{sName}` in declaration order are \
    {MessageData.joinSep (expected.toList.map fun n => m!"`{n}`") ", "}"
  let mut seen : Array Name := #[]
  for f in fs do
    let n := f.getId
    let some i := expected.idxOf? n | do
      if let some p := parentField? env s n then
        throwErrorAt f "enc_structure: `{n}` is inherited through the parent field `{p}`, so list \
          `{p}` instead; {order}"
      throwErrorAt f "enc_structure: `{n}` is not a field of `{sName}`; {order}"
    if seen.contains n then
      throwErrorAt f "enc_structure: field `{n}` is listed twice; {order}"
    if let some prev := seen.back? then
      if i < expected.idxOf prev then
        throwErrorAt f "enc_structure: field `{n}` must come before `{prev}`; {order}"
    seen := seen.push n
  let missing := expected.filter (!seen.contains ·)
  unless missing.isEmpty do
    let names := MessageData.joinSep (missing.toList.map fun n => m!"`{n}`") ", "
    throwErrorAt S "enc_structure: missing {if missing.size = 1 then "field" else "fields"} \
      {names} of `{sName}`; {order}"
  return s

/-- Elaborate `enc_structure`: the encoding, its unfolding lemma and its rules. -/
@[command_elab encStructure] def elabEncStructure : CommandElab := fun stx => do
  let `($[$doc:docComment]? enc_structure $eS:ident $[($ps:ident : $pts:term)]* :
      $S:term where $[$fs:ident : $es:term],*) :=
    stx | throwUnsupportedSyntax
  let s ← checkFields S fs
  -- the constructor, which need not be called `mk`
  let ctor := mkCIdent (getStructureCtor (← getEnv) s).name
  let name := eS.getId
  let params ← ps.zip pts |>.mapM fun (p, t) => `(bracketedBinder| ($p:ident : $t))
  let applied (id : Ident) : Term := Syntax.mkApp id (ps.map (fun p => (⟨p.raw⟩ : Term)))
  let eSTerm := applied eS
  -- Generated locals must not capture an explicit parameter of the same name.
  let freshIdent (base : Name) : CommandElabM Ident := do
    return mkIdent (← withFreshMacroScope <| MonadQuotation.addMacroScope base)
  let a ← freshIdent `a
  let (fields, encoding, fieldsOf, cmds) ← liftMacroM do
    let n := fs.size
    let tupleOf (x : Ident) : MacroM Term := do
      tuple (← fs.mapM fun f => `($(mkCIdent (s ++ f.getId)) $x))
    let tup ← tupleOf a
    let fieldsName := app name "Fields"
    let mut enc : Term := es.back!
    for e in es.pop.reverse do
      enc ← `(encPair $e $enc)
    return (fieldsName, enc, tup, (a, n))
  let (a, n) := cmds
  let fieldsTerm := applied fields
  let lin (e : Term) : CommandElabM Term := `(fun a => List.length ($e a))
  let linE ← lin eSTerm
  elabCommand (← `(public abbrev $fields:ident $params* := $encoding))
  addDocStringCore ((← getCurrNamespace) ++ fields.getId) s!"The tuple of the fields of `{name}`."
  elabCommand (← `($[$doc:docComment]? @[expose] public def $eS:ident $params* : $S ↪ List Bool :=
    (⟨fun $a => $fieldsOf, fun x y h => by cases x; cases y; simp_all⟩ : $S ↪ _).trans $fieldsTerm))
  elabCommand (← `(@[simp] public theorem $(app name "_apply") $params* ($a : $S) :
    $eSTerm $a = $fieldsTerm $fieldsOf := rfl))
  let fieldsDeg := app name "_fields_deg"
  let fieldsDegTerm := applied fieldsDeg
  elabCommand (← `(public theorem $fieldsDeg:ident $params* :
    ComputableInDegree (fun $a : $S => $fieldsOf) $eSTerm $fieldsTerm 1 1 :=
      ComputableInDegree.of_eq fun _ => rfl))
  let fieldsPoly : Term ← `((ComputableInPolyTime.of_eq fun _ => rfl :
    ComputableInPolyTime (fun $a : $S => $fieldsOf) $eSTerm $fieldsTerm))
  for f in fs, e in es, i in Array.range n do
    let proj := mkCIdent (s ++ f.getId)
    let deg := app name s!"_{f.getId}_deg"
    let degTerm := applied deg
    let body ← liftMacroM <| component `Turing.MultiTapeTM.ComputableInDegree fieldsDegTerm i n
    elabCommand (← `(@[scoped fun_prop] public theorem $deg:ident $params* :
      ComputableInDegree $proj $eSTerm $e 1 1 := $body))
    elabCommand (← `(@[scoped fun_prop] public theorem
      $(app name s!"_{f.getId}_inO"):ident $params* :
      ComputableInO $proj $eSTerm $e $linE $linE := ComputableInDegree.inO_one $degTerm))
    elabCommand (← `(@[scoped fun_prop] public theorem
      $(app name s!"_{f.getId}_budget"):ident $params*
      {γ : Type} {encIn : γ ↪ List Bool} {S : γ → ℕ} {g : γ → $S}
      (h : ComputableInSpace g encIn $eSTerm S) :
      ComputableInSpace (fun a => $proj (g a)) encIn $e S :=
        ComputableInSpace.budget_comp_linear
          (ComputableInSpace.of_inO (ComputableInDegree.inO_one $degTerm)) h))
    let poly ← liftMacroM <| component `Turing.MultiTapeTM.ComputableInPolyTime fieldsPoly i n
    elabCommand (← `(@[scoped fun_prop] public theorem
      $(app name s!"_{f.getId}_polyTime"):ident $params*
      {γ : Type} {encIn : γ ↪ List Bool} {g : γ → $S}
      (h : ComputableInPolyTime g encIn $eSTerm) :
      ComputableInPolyTime (fun a => $proj (g a)) encIn $e :=
        ComputableInPolyTime.comp $poly h))
  let p ← freshIdent `p
  let comps ← (List.range n).toArray.mapM fun i => do
    let mut t : Term ← `($p)
    for _ in [0:i] do
      t ← `(($t).2)
    if i + 1 < n then t ← `(($t).1)
    return t
  let mkApp : Term := Syntax.mkApp ctor comps
  elabCommand (← `(@[scoped fun_prop] public theorem $(app name "_mk_deg"):ident $params* :
    ComputableInDegree (fun $p => $mkApp) $fieldsTerm $eSTerm 1 1 :=
      ComputableInDegree.of_eq fun _ => rfl))
  -- the constructor, adding up the bounds of its arguments
  let names (stem : String) :=
    (Array.range n).mapM fun i => freshIdent (Name.mkSimple s!"{stem}{i}")
  let xs ← names "x"
  let hs ← names "h"
  let Ts ← names "T"
  let Ss ← names "S"
  let xN (i : Nat) := xs[i]!
  let hN (i : Nat) := hs[i]!
  let TN (i : Nat) := Ts[i]!
  let SN (i : Nat) := Ss[i]!
  let x ← freshIdent `x
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
  let appl : Term := Syntax.mkApp ctor args
  let γ ← freshIdent `γ
  let encIn ← freshIdent `encIn
  let mut binders : TSyntaxArray ``Lean.Parser.Term.bracketedBinder := #[]
  for i in [0:n] do
    binders := binders.push (← `(bracketedBinder| {$(xN i) : $γ → _}))
    binders := binders.push (← `(bracketedBinder| {$(TN i) $(SN i) : $γ → ℕ}))
  let mut i := 0
  for e in es do
    binders := binders.push (← `(bracketedBinder|
      ($(hN i) : ComputableInO $(xN i) $encIn $e $(TN i) $(SN i))))
    i := i + 1
  elabCommand (← `(@[scoped fun_prop] public theorem $(app name "_mk_inO"):ident
    $params* {$γ : Type}
    {$encIn : $γ ↪ List Bool} $binders* :
    ComputableInO (fun $x => $appl) $encIn $eSTerm (fun $x => $sumT) fun $x => $sumS :=
      ComputableInO.of_enc_eq $prod fun _ => rfl))
  let mut polyBinders : TSyntaxArray ``Lean.Parser.Term.bracketedBinder := #[]
  for j in [0:n] do
    polyBinders := polyBinders.push (← `(bracketedBinder| {$(xN j) : $γ → _}))
  for e in es, j in Array.range n do
    polyBinders := polyBinders.push (← `(bracketedBinder|
      ($(hN j) : ComputableInPolyTime $(xN j) $encIn $e)))
  elabCommand (← `(@[scoped fun_prop] public theorem $(app name "_mk_polyTime"):ident
    $params* {$γ : Type}
    {$encIn : $γ ↪ List Bool} $polyBinders* :
    ComputableInPolyTime (fun $x => $appl) $encIn $eSTerm :=
      ComputableInPolyTime.of_enc_eq $prodPoly fun _ => rfl))
  let budget ← freshIdent `budget
  let mut budgetBinders : TSyntaxArray ``Lean.Parser.Term.bracketedBinder := #[]
  for j in [0:n] do
    budgetBinders := budgetBinders.push (← `(bracketedBinder| {$(xN j) : $γ → _}))
  for e in es, j in Array.range n do
    budgetBinders := budgetBinders.push (← `(bracketedBinder|
      ($(hN j) : ComputableInSpace $(xN j) $encIn $e $budget)))
  let mut budgetProd : Term := hN last
  for j in (List.range last).reverse do
    budgetProd ← `(ComputableInSpace.budget_prod $(hN j) $budgetProd)
  elabCommand (← `(@[scoped fun_prop] public theorem $(app name "_mk_budget"):ident
    $params* {$γ : Type}
    {$encIn : $γ ↪ List Bool} {$budget : $γ → ℕ} $budgetBinders* :
    ComputableInSpace (fun $x => $appl) $encIn $eSTerm $budget :=
      ComputableInSpace.of_enc_eq $budgetProd fun _ => rfl))

end Turing.MultiTapeTM
