/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Sum
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.Sum
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.Cases
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Degree.Bounds
public meta import Lean.Elab.Command

/-!
# Encodings of non-recursive inductive types

`enc_inductive eT : T where | c₁ : e₁₁, e₁₂ | c₂ | …` declares the encoding of an inductive type
whose constructors take explicit, non-recursive fields. A value is mapped to a right-nested sum
with one summand per constructor, and the sum is encoded by `encSum`. The summand of a constructor
is the framed tuple of its fields, encoded as in `enc_structure`: the field encoding itself for
one field, `encUnit` for none. Constructor `i` of `n` is therefore tagged by `i` leading `true`
bits, followed by a `false` bit unless it is the last.

The command declares:

* `eTPayload`, the encoding of the sum, and `eT_toSum`, the map from `T` to the sum;
* `eT`, the encoding of `T`, and `eT_apply`, unfolding `eT x` to `eTPayload (eT_toSum x)`;
* `eT_toSum_deg`, the linear map to the sum;
* for each constructor `c`, the rule `eT_c_inO`, which adds up the bounds of its arguments;
* `eT_elim`, case analysis by constructor on the payloads, and its rule `eT_elim_inO`, which
  charges only the case taken.

The `toSum` and constructor rules are `scoped` `fun_prop` rules, as for `enc_structure`. The case
rule is stated for an input paired with the value, as `ComputableInO.sumElimSnd` is.

The command does not inspect the declaration for recursion, and it derives no recursive
encodings: each field encoding must already be available as an ordinary term, and the generated
certificates are relative to those encodings. A recursive field is accepted only when such an
encoding is supplied, for example `encUnary` for the field of `Nat.succ`. Fields that are
propositions, indices or implicit arguments are not supported.
-/

public meta section

namespace Turing.MultiTapeTM

open Lean Elab Command Term Meta

/-- `enc_inductive eT : T where | c₁ : e₁, e₂ | c₂` declares the encoding `eT` of the inductive
type `T`: constructor `c₁` with fields encoded by `e₁` and `e₂`, and constructor `c₂` without
fields. Constructors are listed in declaration order. -/
syntax (name := encInductive) (docComment)? "enc_inductive " ident " : " ident " where"
  (" | " ident (" : " term:max,+)?)+ : command

private def app (base : Name) (suffix : String) : Ident :=
  mkIdent (base.appendAfter suffix)

/-- The right-nested tuple of `ts`, or `()` for none. -/
private def tuple (ts : Array Term) : MacroM Term := do
  if ts.isEmpty then return ← `(())
  let mut r := ts.back!
  for t in ts.pop.reverse do
    r ← `(($t, $r))
  return r

/-- The right-nested `encPair` of `es`, or `encUnit` for none. -/
private def tupleEnc (es : Array Term) : MacroM Term := do
  if es.isEmpty then return ← `(encUnit)
  let mut r := es.back!
  for e in es.pop.reverse do
    r ← `(encPair $e $r)
  return r

/-- Inject `t` as summand `i` of a right-nested sum of `n` summands. -/
private def inject (t : Term) (i n : Nat) : MacroM Term := do
  let mut r := t
  if i + 1 < n then r ← `(Sum.inl $r)
  for _ in [0:i] do
    r ← `(Sum.inr $r)
  return r

/-- The summands of a right-nested sum type with `n` summands. -/
private partial def summands (t : Expr) : Nat → MetaM (Array Expr)
  | 0 => return #[]
  | 1 => return #[t]
  | n + 1 => do
    let t ← whnfR t
    let some (a, b) := t.app2? ``Sum |
      throwError "enc_inductive: expected a sum type, got{indentExpr t}"
    return #[a] ++ (← summands b n)

/-- Elaborate `enc_inductive`. -/
@[command_elab encInductive] def elabEncInductive : CommandElab := fun stx => do
  let `($[$doc:docComment]? enc_inductive $eT:ident : $T:ident where
      $[ | $cs:ident $[: $ess,*]?]*) := stx | throwUnsupportedSyntax
  let name := eT.getId
  let n := cs.size
  let encss : Array (Array Term) := ess.map fun o => (o.map (·.getElems)).getD #[]
  let payloads ← liftMacroM <| encss.mapM tupleEnc
  -- the encoding of the sum of the payloads
  let mut sumEnc : Term := payloads.back!
  for p in payloads.pop.reverse do
    sumEnc ← `(encSum $p $sumEnc)
  -- the encodings of the remaining summands, `rests[i]` for summands `i` to `n - 1`
  let mut rests : Array Term := #[payloads.back!]
  for p in payloads.pop.reverse do
    rests := #[← `(encSum $p $(rests[0]!))] ++ rests
  let payloadName := app name "Payload"
  elabCommand (← `(public abbrev $payloadName:ident := $sumEnc))
  addDocStringCore ((← getCurrNamespace) ++ payloadName.getId)
    s!"The encoding of the constructor payloads of `{name}`."
  -- the sum type, read back from the encoding
  let (sumTy, argTys) ← liftTermElabM do
    let some c := (← getEnv).find? ((← getCurrNamespace) ++ payloadName.getId) |
      throwError "enc_inductive: missing payload encoding"
    let ty ← whnfR (← instantiateMVars c.type)
    let some (σ, _) := ty.app2? ``Function.Embedding |
      throwError "enc_inductive: unexpected payload type{indentExpr ty}"
    let parts ← summands σ n
    return (← PrettyPrinter.delab σ, ← parts.mapM fun p => PrettyPrinter.delab p)
  let toSum := app name "_toSum"
  let alts ← liftMacroM <| (Array.range n).mapM fun i => do
    let xs := (Array.range encss[i]!.size).map fun j => mkIdent (Name.mkSimple s!"x{j}")
    let pat : Term := Syntax.mkApp (mkIdent (T.getId ++ cs[i]!.getId)) xs
    let rhs ← inject (← tuple xs) i n
    `(Lean.Parser.Term.matchAltExpr| | $pat => $rhs)
  elabCommand (← `(/-- The constructor payloads of a value, as a summand. -/
    @[expose] public def $toSum:ident : $T → $sumTy := fun x => match x with $alts:matchAlt*))
  elabCommand (← `($[$doc:docComment]? @[expose] public def $eT:ident : $T ↪ List Bool :=
    (⟨$toSum, fun x y h => by cases x <;> cases y <;> simp_all [$toSum:ident]⟩ :
      $T ↪ $sumTy).trans $payloadName))
  elabCommand (← `(@[simp] public theorem $(app name "_apply") (x : $T) :
    $eT x = $payloadName ($toSum x) := rfl))
  elabCommand (← `(@[scoped fun_prop] public theorem $(app name "_toSum_deg"):ident :
    ComputableInDegree $toSum $eT $payloadName 1 1 := ComputableInDegree.of_eq fun _ => rfl))
  -- constructor rules, adding up the bounds of the arguments
  let γ := mkIdent `γ
  let encIn := mkIdent `encIn
  let x := mkIdent `x
  for i in [0:n] do
    let es := encss[i]!
    let k := es.size
    let ctor := mkIdent (T.getId ++ cs[i]!.getId)
    let rule := app name s!"_{cs[i]!.getId}_inO"
    if k = 0 then
      elabCommand (← `(@[scoped fun_prop] public theorem $rule:ident {$γ : Type}
        {$encIn : $γ ↪ List Bool} :
        ComputableInO (fun _ : $γ => $ctor) $encIn $eT (fun $x => ($encIn $x).length)
          fun $x => ($encIn $x).length := ComputableInO.const _))
      continue
    let xN (j : Nat) := mkIdent (Name.mkSimple s!"x{j}")
    let hN (j : Nat) := mkIdent (Name.mkSimple s!"h{j}")
    let TN (j : Nat) := mkIdent (Name.mkSimple s!"T{j}")
    let SN (j : Nat) := mkIdent (Name.mkSimple s!"S{j}")
    let last := k - 1
    let mut sumT : Term ← `($(TN last) $x:ident)
    let mut sumS : Term ← `($(SN last) $x:ident)
    let mut pay : Term := hN last
    for j in (List.range last).reverse do
      sumT ← `($(TN j) $x:ident + $sumT)
      sumS ← `($(SN j) $x:ident + $sumS)
      pay ← `(ComputableInO.prod $(hN j) $pay)
    -- inject the payload: `inl` at its own summand, then `inr` for each earlier one
    let mut inj : Term := pay
    if i + 1 < n then
      inj ← `(ComputableInO.comp_linear (ComputableInO.inl $(payloads[i]!) $(rests[i + 1]!)) $inj)
    for j in (List.range i).reverse do
      inj ← `(ComputableInO.comp_linear (ComputableInO.inr $(payloads[j]!) $(rests[j + 1]!)) $inj)
    let args ← (Array.range k).mapM fun j => (`($(xN j) $x:ident) : CommandElabM Term)
    let appl : Term := Syntax.mkApp ctor args
    let mut binders : TSyntaxArray ``Lean.Parser.Term.bracketedBinder := #[]
    for j in [0:k] do
      binders := binders.push (← `(bracketedBinder| {$(xN j) : $γ → _}))
      binders := binders.push (← `(bracketedBinder| {$(TN j) $(SN j) : $γ → ℕ}))
    for j in [0:k] do
      binders := binders.push (← `(bracketedBinder|
        ($(hN j) : ComputableInO $(xN j) $encIn $(es[j]!) $(TN j) $(SN j))))
    elabCommand (← `(@[scoped fun_prop] public theorem $rule:ident {$γ : Type}
      {$encIn : $γ ↪ List Bool} $binders* :
      ComputableInO (fun $x => $appl) $encIn $eT (fun $x => $sumT) fun $x => $sumS :=
        ComputableInO.of_enc_eq $inj fun _ => rfl))
  -- case analysis on the payloads
  let elim := app name "_elim"
  let fN (i : Nat) := mkIdent (Name.mkSimple s!"f{i}")
  let mut elimBody : Term := fN (n - 1)
  for i in (List.range (n - 1)).reverse do
    elimBody ← `(Sum.elim $(fN i) $elimBody)
  let mut elimBinders : TSyntaxArray ``Lean.Parser.Term.bracketedBinder := #[]
  for i in [0:n] do
    elimBinders := elimBinders.push (← `(bracketedBinder| ($(fN i) : $(argTys[i]!) → ε)))
  elabCommand (← `(/-- Case analysis by constructor, on the constructor payloads. -/
    @[expose] public def $elim:ident {ε : Sort _} (v : $T) $elimBinders* : ε :=
      $elimBody ($toSum v)))
  -- its rule: nested `sumElimSnd`, pulled back along `toSum`
  let encP := mkIdent `encP
  let encE := mkIdent `encE
  let p := mkIdent `p
  let gN (i : Nat) := mkIdent (Name.mkSimple s!"g{i}")
  let hN (i : Nat) := mkIdent (Name.mkSimple s!"h{i}")
  let TN (i : Nat) := mkIdent (Name.mkSimple s!"T{i}")
  let SN (i : Nat) := mkIdent (Name.mkSimple s!"S{i}")
  let mut rb : TSyntaxArray ``Lean.Parser.Term.bracketedBinder := #[]
  for i in [0:n] do
    rb := rb.push (← `(bracketedBinder| {$(gN i) : π × $(argTys[i]!) → ε}))
    rb := rb.push (← `(bracketedBinder| {$(TN i) $(SN i) : π × $(argTys[i]!) → ℕ}))
  for i in [0:n] do
    rb := rb.push (← `(bracketedBinder|
      ($(hN i) : ComputableInO $(gN i) (encPair $encP $(payloads[i]!)) $encE $(TN i) $(SN i))))
  let a := mkIdent `a
  let lam (F : Nat → Ident) (i : Nat) : CommandElabM Term := `(fun $a => $(F i) ($p.1, $a))
  let fs ← (Array.range n).mapM (lam gN)
  let ts ← (Array.range n).mapM (lam TN)
  let ss ← (Array.range n).mapM (lam SN)
  let fnTerm : Term := Syntax.mkApp elim (#[← `($p.2)] ++ fs)
  let tTerm : Term := Syntax.mkApp elim (#[← `($p.2)] ++ ts)
  let sTerm : Term := Syntax.mkApp elim (#[← `($p.2)] ++ ss)
  let nLit := Syntax.mkNumLit (toString n)
  let mut nested : Term := hN (n - 1)
  for i in (List.range (n - 1)).reverse do
    nested ← `(ComputableInO.sumElimSnd $(hN i) $nested)
  let applyName := app name "_apply"
  elabCommand (← `(public theorem $(app name "_elim_inO"):ident {π ε : Type}
      {$encP : π ↪ List Bool} {$encE : ε ↪ List Bool} $rb* :
      ComputableInO (fun $p : π × $T => $fnTerm) (encPair $encP $eT) $encE
        (fun $p => $nLit * (encPair $encP $eT $p).length + $tTerm)
        fun $p => $nLit * (encPair $encP $eT $p).length + $sTerm := by
    refine (($nested).of_encIn_eq (fun q : π × $T => (q.1, $toSum q.2)) fun _ => rfl).mono_le
      ?_ ?_ <;>
    · rintro ⟨q, v⟩
      cases v <;>
      simp only [Function.comp_apply, $elim:ident, $toSum:ident, $applyName:ident, Sum.elim_inl,
        Sum.elim_inr, length_encPair, encSum_inl, encSum_inr, List.length_cons] <;>
      omega))

end Turing.MultiTapeTM
