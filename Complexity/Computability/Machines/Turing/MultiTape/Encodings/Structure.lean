/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.FunProp
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Degree.Bounds
public meta import Lean.Elab.Command

/-!
# Encodings of structures as the tuple of their fields

`enc_structure eS : S where f₁ : e₁; …` declares the encoding of a structure as the framed tuple
of its fields, with everything a certificate needs to work with it:

* `eSFields`, the encoding of the tuple, and `eS`, the encoding of the structure;
* `eS_apply`, unfolding `eS` to `eSFields` of the tuple;
* `eS_fields_deg`, the linear map from a structure to the tuple of its fields;
* for each field `f`, the linear rules `eS_f_deg` and `eS_f_inO`;
* the constructor rules `eS_mk_deg`, on tuples, and `eS_mk_inO`, which adds up the bounds of its
  arguments.

The rules are `scoped` `fun_prop` rules, so that a program using the structure is assembled by
`fun_prop` inside the namespace of the declaration.

## Main definitions

* `enc_structure`: declare the encoding of a structure.
-/

public meta section

namespace Turing.MultiTapeTM

open Lean Elab Command

/-- `enc_structure eS : S where f₁ : e₁, f₂ : e₂` declares the encoding `eS` of the structure `S`
as the tuple of its fields encoded by `e₁`, `e₂`, with its rules. -/
syntax (name := encStructure) (docComment)? "enc_structure " ident " : " ident " where "
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

/-- Elaborate `enc_structure`: the encoding, its unfolding lemma and its rules. -/
@[command_elab encStructure] def elabEncStructure : CommandElab := fun stx => do
  let `($[$doc:docComment]? enc_structure $eS:ident : $S:ident where $[$fs:ident : $es:term],*) :=
    stx | throwUnsupportedSyntax
  let name := eS.getId
  let (fields, encoding, fieldsOf, cmds) ← liftMacroM do
    let a := mkIdent `a
    let n := fs.size
    let tupleOf (x : Ident) : MacroM Term := do
      tuple (← fs.mapM fun f => `($(mkIdent (x.getId ++ f.getId)):ident))
    let tup ← tupleOf a
    let fieldsName := app name "Fields"
    let mut enc : Term := es.back!
    for e in es.pop.reverse do
      enc ← `(encPair $e $enc)
    return (fieldsName, enc, tup, (a, n))
  let (a, n) := cmds
  let lin (e : Ident) : CommandElabM Term := `(fun a => List.length ($e a))
  let linE ← lin eS
  elabCommand (← `(public abbrev $fields:ident := $encoding))
  addDocStringCore ((← getCurrNamespace) ++ fields.getId) s!"The tuple of the fields of `{name}`."
  elabCommand (← `($[$doc:docComment]? @[expose] public def $eS:ident : $S ↪ List Bool :=
    (⟨fun $a => $fieldsOf, fun x y h => by cases x; cases y; simp_all⟩ : $S ↪ _).trans $fields))
  elabCommand (← `(@[simp] public theorem $(app name "_apply") ($a : $S) :
    $eS $a = $fields $fieldsOf := rfl))
  let fieldsDeg := app name "_fields_deg"
  elabCommand (← `(public theorem $fieldsDeg:ident :
    ComputableInDegree (fun $a : $S => $fieldsOf) $eS $fields 1 1 :=
      ComputableInDegree.of_eq fun _ => rfl))
  for f in fs, e in es, i in Array.range n do
    let proj := mkIdent (S.getId ++ f.getId)
    let deg := app name s!"_{f.getId}_deg"
    let body ← liftMacroM <| component `Turing.MultiTapeTM.ComputableInDegree fieldsDeg i n
    elabCommand (← `(@[scoped fun_prop] public theorem $deg:ident :
      ComputableInDegree $proj $eS $e 1 1 := $body))
    elabCommand (← `(@[scoped fun_prop] public theorem $(app name s!"_{f.getId}_inO"):ident :
      ComputableInO $proj $eS $e $linE $linE := ComputableInDegree.inO_one $deg))
  let p := mkIdent `p
  let comps ← (List.range n).toArray.mapM fun i => do
    let mut t : Term ← `($p)
    for _ in [0:i] do
      t ← `(($t).2)
    if i + 1 < n then t ← `(($t).1)
    return t
  let mkApp : Term := Syntax.mkApp (mkIdent (S.getId ++ `mk)) comps
  elabCommand (← `(@[scoped fun_prop] public theorem $(app name "_mk_deg"):ident :
    ComputableInDegree (fun $p => $mkApp) $fields $eS 1 1 :=
      ComputableInDegree.of_eq fun _ => rfl))
  -- the constructor, adding up the bounds of its arguments
  let xN (i : Nat) := mkIdent (Name.mkSimple s!"x{i}")
  let hN (i : Nat) := mkIdent (Name.mkSimple s!"h{i}")
  let TN (i : Nat) := mkIdent (Name.mkSimple s!"T{i}")
  let SN (i : Nat) := mkIdent (Name.mkSimple s!"S{i}")
  let x := mkIdent `x
  let last := n - 1
  let mut sumT : Term ← `($(TN last) $x:ident)
  let mut sumS : Term ← `($(SN last) $x:ident)
  let mut prod : Term := hN last
  for i in (List.range last).reverse do
    sumT ← `($(TN i) $x:ident + $sumT)
    sumS ← `($(SN i) $x:ident + $sumS)
    prod ← `(ComputableInO.prod $(hN i) $prod)
  let args ← (Array.range n).mapM fun i => (`($(xN i) $x:ident) : CommandElabM Term)
  let appl : Term := Syntax.mkApp (mkIdent (S.getId ++ `mk)) args
  let γ := mkIdent `γ
  let encIn := mkIdent `encIn
  let mut binders : TSyntaxArray ``Lean.Parser.Term.bracketedBinder := #[]
  for i in [0:n] do
    binders := binders.push (← `(bracketedBinder| {$(xN i) : $γ → _}))
    binders := binders.push (← `(bracketedBinder| {$(TN i) $(SN i) : $γ → ℕ}))
  let mut i := 0
  for e in es do
    binders := binders.push (← `(bracketedBinder|
      ($(hN i) : ComputableInO $(xN i) $encIn $e $(TN i) $(SN i))))
    i := i + 1
  elabCommand (← `(@[scoped fun_prop] public theorem $(app name "_mk_inO"):ident {$γ : Type}
    {$encIn : $γ ↪ List Bool} $binders* :
    ComputableInO (fun $x => $appl) $encIn $eS (fun $x => $sumT) fun $x => $sumS :=
      ComputableInO.of_enc_eq $prod fun _ => rfl))

end Turing.MultiTapeTM
