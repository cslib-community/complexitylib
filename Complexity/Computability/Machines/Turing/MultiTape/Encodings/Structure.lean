/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.FunProp
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Degree.Bounds
public import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimePrimitives
public meta import Lean.Elab.Command

/-!
# Encodings of structures as the tuple of their fields

`enc_structure eS binders : S where f₁ : e₁, …` declares the encoding of a structure as the framed
tuple of its fields, with everything a certificate needs to work with it:

* `eSFields`, the encoding of the tuple, and `eS`, the encoding of the structure;
* `eS_apply`, unfolding `eS` to `eSFields` of the tuple, which is not a `simp` lemma, so that
  lemmas stated about `eS` keep firing;
* `eS_fields_deg`, the linear map from a structure to the tuple of its fields;
* for each field `f`, the linear rules `eS_f_deg` and `eS_f_inO`, and `eS_f_polyTime`, which reads
  the field of a computed structure;
* the constructor rules `eS_mk_deg`, on tuples, `eS_mk_inO`, which adds up the bounds of its
  arguments, and `eS_mk_polyTime`.

The rules are `scoped` `fun_prop` rules, so that a program using the structure is assembled by
`fun_prop` inside the namespace of the declaration, or after `open scoped` of that namespace.
`global enc_structure` makes them ordinary `fun_prop` rules, for a structure in a public API.

The structure may have parameters, written as a term such as `Edge C`, and `eS` may take binders,
such as an encoding of a parameter. Explicit binders stay explicit arguments of `eS` and
`eSFields`, and are implicit in the rules that take hypotheses. An encoding built from
noncomputable parts is declared with `noncomputable enc_structure`.
-/

public meta section

namespace Turing.MultiTapeTM

open Lean Elab Command
open Lean.Parser.Term (attrInstance)

/-- `enc_structure eS binders : S where f₁ : e₁, f₂ : e₂` declares the encoding `eS` of the
structure `S` as the tuple of its fields encoded by `e₁`, `e₂`, with its rules. -/
syntax (name := encStructure) (docComment)? ("noncomputable ")? ("global ")? "enc_structure " ident
  (ppSpace bracketedBinder)* " : " term " where " (ident " : " term:max),+ : command

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

/-- The names bound by the explicit binders among `bs`, as arguments. -/
private def explicitArgs (bs : TSyntaxArray ``Lean.Parser.Term.bracketedBinder) : Array Term :=
  bs.flatMap fun b =>
    if b.raw.isOfKind ``Lean.Parser.Term.explicitBinder then
      b.raw[1].getArgs.map fun n => ⟨n⟩
    else #[]

/-- The binders `bs`, with explicit ones made implicit: a rule finds them by unification. -/
private def implicitBinders (bs : TSyntaxArray ``Lean.Parser.Term.bracketedBinder) :
    TSyntaxArray ``Lean.Parser.Term.bracketedBinder :=
  bs.map fun b =>
    if b.raw.isOfKind ``Lean.Parser.Term.explicitBinder then
      ⟨mkNode ``Lean.Parser.Term.implicitBinder #[mkAtom "{", b.raw[1], b.raw[2], mkAtom "}"]⟩
    else b

/-- The structure named at the head of the type `S`. -/
private def headName (S : Term) : CommandElabM Name :=
  match S with
  | `($f:ident $_*) | `($f:ident) => return f.getId
  | _ => throwErrorAt S "enc_structure: expected a structure, optionally applied to parameters"

/-- Elaborate `enc_structure`: the encoding, its unfolding lemma and its rules. -/
@[command_elab encStructure] def elabEncStructure : CommandElab := fun stx => do
  let `($[$doc:docComment]? $[noncomputable%$nc]? $[global%$gl]? enc_structure $eS:ident
      $bs:bracketedBinder* : $S:term where $[$fs:ident : $es:term],*) :=
    stx | throwUnsupportedSyntax
  let name := eS.getId
  let rule ← if gl.isSome then `(attrInstance| fun_prop) else `(attrInstance| scoped fun_prop)
  let struct ← headName S
  let args := explicitArgs bs
  let ibs := implicitBinders bs
  let a := mkIdent `a
  let n := fs.size
  let last := n - 1
  let (tup, enc) ← liftMacroM do
    let tup ← tuple (fs.map fun f => ⟨mkIdent (a.getId ++ f.getId)⟩)
    let mut enc : Term := es.back!
    for e in es.pop.reverse do
      enc ← `(encPair $e $enc)
    return (tup, enc)
  let fieldsName := app name "Fields"
  let fields : Term := Syntax.mkApp fieldsName args
  let encS : Term := Syntax.mkApp eS args
  let lin : Term ← `(fun a => List.length ($encS a))
  if nc.isSome then
    elabCommand (← `(public noncomputable abbrev $fieldsName:ident $bs* := $enc))
    elabCommand (← `($[$doc:docComment]? @[expose] public noncomputable def $eS:ident $bs* :
      $S ↪ List Bool :=
      (⟨fun $a => $tup, fun x y h => by cases x; cases y; simp_all⟩ : $S ↪ _).trans $fields))
  else
    elabCommand (← `(public abbrev $fieldsName:ident $bs* := $enc))
    elabCommand (← `($[$doc:docComment]? @[expose] public def $eS:ident $bs* : $S ↪ List Bool :=
      (⟨fun $a => $tup, fun x y h => by cases x; cases y; simp_all⟩ : $S ↪ _).trans $fields))
  addDocStringCore ((← getCurrNamespace) ++ fieldsName.getId)
    s!"The tuple of the fields of `{name}`."
  elabCommand (← `(public theorem $(app name "_apply") $bs* ($a : $S) :
    $encS $a = $fields $tup := rfl))
  let fieldsDeg := app name "_fields_deg"
  let fieldsDegT : Term := Syntax.mkApp fieldsDeg args
  elabCommand (← `(public theorem $fieldsDeg:ident $bs* :
    ComputableInDegree (fun $a : $S => $tup) $encS $fields 1 1 :=
      ComputableInDegree.of_eq fun _ => rfl))
  let fieldsPoly : Term ← `((ComputableInPolyTime.of_eq fun _ => rfl :
    ComputableInPolyTime (fun $a : $S => $tup) $encS $fields))
  let γ := mkIdent `γ
  let encIn := mkIdent `encIn
  let g := mkIdent `g
  let x := mkIdent `x
  for f in fs, e in es, i in Array.range n do
    let proj := mkIdent (struct ++ f.getId)
    let deg := app name s!"_{f.getId}_deg"
    let body ← liftMacroM <| component `Turing.MultiTapeTM.ComputableInDegree fieldsDegT i n
    elabCommand (← `(@[$rule:attrInstance] public theorem $deg:ident $bs* :
      ComputableInDegree ($proj : $S → _) $encS $e 1 1 := $body))
    let degT : Term := Syntax.mkApp deg args
    elabCommand (← `(@[$rule:attrInstance] public theorem
      $(app name s!"_{f.getId}_inO"):ident $bs* :
      ComputableInO ($proj : $S → _) $encS $e $lin $lin :=
        ComputableInDegree.inO_one $degT))
    let poly ← liftMacroM <| component `Turing.MultiTapeTM.ComputableInPolyTime fieldsPoly i n
    elabCommand (← `(@[$rule:attrInstance] public theorem
      $(app name s!"_{f.getId}_polyTime"):ident $ibs* {$γ : Type} {$encIn : $γ ↪ List Bool}
      {$g : $γ → $S}
      (h : ComputableInPolyTime $g $encIn $encS) :
      ComputableInPolyTime (fun $x => $proj ($g $x)) $encIn $e :=
        ComputableInPolyTime.comp $poly h))
  let p := mkIdent `p
  let comps ← (List.range n).toArray.mapM fun i => do
    let mut t : Term ← `($p)
    for _ in [0:i] do
      t ← `(($t).2)
    if i + 1 < n then t ← `(($t).1)
    return t
  let mk := mkIdent (struct ++ `mk)
  let mkApp : Term := Syntax.mkApp mk comps
  elabCommand (← `(@[$rule:attrInstance] public theorem $(app name "_mk_deg"):ident $bs* :
    ComputableInDegree (fun $p => ($mkApp : $S)) $fields $encS 1 1 :=
      ComputableInDegree.of_eq fun _ => rfl))
  -- the constructor, adding up the bounds of its arguments
  let xN (i : Nat) := mkIdent (Name.mkSimple s!"x{i}")
  let hN (i : Nat) := mkIdent (Name.mkSimple s!"h{i}")
  let TN (i : Nat) := mkIdent (Name.mkSimple s!"T{i}")
  let SN (i : Nat) := mkIdent (Name.mkSimple s!"S{i}")
  let mut sumT : Term ← `($(TN last) $x:ident)
  let mut sumS : Term ← `($(SN last) $x:ident)
  let mut prod : Term := hN last
  let mut prodPoly : Term := hN last
  for i in (List.range last).reverse do
    sumT ← `($(TN i) $x:ident + $sumT)
    sumS ← `($(SN i) $x:ident + $sumS)
    prod ← `(ComputableInO.prod $(hN i) $prod)
    prodPoly ← `(ComputableInPolyTime.prod $(hN i) $prodPoly)
  let appl : Term := Syntax.mkApp mk ((Array.range n).map fun i =>
    ⟨Syntax.mkApp (xN i) #[x]⟩)
  let mut fns : TSyntaxArray ``Lean.Parser.Term.bracketedBinder := #[]
  let mut bounds : TSyntaxArray ``Lean.Parser.Term.bracketedBinder := #[]
  let mut hsO : TSyntaxArray ``Lean.Parser.Term.bracketedBinder := #[]
  let mut hsPoly : TSyntaxArray ``Lean.Parser.Term.bracketedBinder := #[]
  for e in es, i in Array.range n do
    fns := fns.push (← `(bracketedBinder| {$(xN i) : $γ → _}))
    bounds := bounds.push (← `(bracketedBinder| {$(TN i) $(SN i) : $γ → ℕ}))
    hsO := hsO.push (← `(bracketedBinder|
      ($(hN i) : ComputableInO $(xN i) $encIn $e $(TN i) $(SN i))))
    hsPoly := hsPoly.push (← `(bracketedBinder|
      ($(hN i) : ComputableInPolyTime $(xN i) $encIn $e)))
  elabCommand (← `(@[$rule:attrInstance] public theorem $(app name "_mk_inO"):ident $ibs*
    {$γ : Type} {$encIn : $γ ↪ List Bool} $fns* $bounds* $hsO* :
    ComputableInO (fun $x => ($appl : $S)) $encIn $encS (fun $x => $sumT) fun $x => $sumS :=
      ComputableInO.of_enc_eq $prod fun _ => rfl))
  elabCommand (← `(@[$rule:attrInstance] public theorem $(app name "_mk_polyTime"):ident $ibs*
    {$γ : Type} {$encIn : $γ ↪ List Bool} $fns* $hsPoly* :
    ComputableInPolyTime (fun $x => ($appl : $S)) $encIn $encS :=
      ComputableInPolyTime.of_enc_eq $prodPoly fun _ => rfl))

end Turing.MultiTapeTM
