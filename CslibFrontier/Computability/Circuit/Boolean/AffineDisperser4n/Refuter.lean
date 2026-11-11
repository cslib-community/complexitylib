/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Circuit.Boolean.AffineDisperser4n.Step
public import CslibFrontier.Computability.Circuit.Boolean.AffineDisperser4n
public import CslibFrontier.Computability.Complexity.Problems.XORSAT.Dense

/-!
# Deterministic polynomial-time refuter for `4n - 10d` circuits

This module implements the deterministic `poly(n, 2^d)`-time algorithm finding a disagreeing input
for any full-basis circuit of size `< 4n - 10d` against a `d`-affine disperser.
-/

public section

namespace Cslib.Circuits.Boolean.AffineDisperser4n

open Cslib.Circuits.Boolean.AffineDisperserCore
open Cslib.Circuits.Boolean.SemiCircuit
open Cslib.Complexity.XORSAT.Dense Cslib.Circuits Cslib.BitString

inductive StepChoice
  | deleteConstantGate (J : ℕ)
  | deleteDeadGate (J : ℕ)
  | deleteShortEqn (e : ℕ)
  | deleteUnitParam (x e : ℕ)
  | moveAffine (J : ℕ)
  | degeneratePair (p : ℕ)
  | partnersShareChild (p : ℕ)
  | pairInSystem (p : ℕ)
  | andOnPair (G p : ℕ)
  | swapAuxIn (G : ℕ)
  | pairCreation (G : ℕ)

def isNode (i : ℕ) : Arg → Bool
  | .const _ => false
  | .node j => decide (i = j)

def readsJ {n} (S : State n) (K : ℕ) (J : ℕ) : Bool :=
  let g := S.gate K
  isNode J g.left || isNode J g.right

def isGate {n} (S : State n) : Arg → Bool
  | .const _ => false
  | .node i => decide (i ∈ S.gates)

def findD2 {n} (S : State n) : Option ℕ :=
  (S.gates.sort (· ≤ ·)).find? fun J =>
    decide (∀ K ∈ S.gates, !readsJ S K J) && !(isNode J S.out.arg)

def findD3 {n} (S : State n) : Option ℕ :=
  (S.eqns.sort (· ≤ ·)).find? fun e =>
    decide ((S.eqn e).terms.card ≤ 2)

def childrenEq {n} (S : State n) (x : ℕ) (c : ℕ ⊕ ℕ) : Bool :=
  decide (S.children x = {c})

def findD4 {n} (S : State n) : Option (ℕ × ℕ) :=
  (S.unpaired.sort (· ≤ ·)).findSome? fun x =>
    (S.eqns.sort (· ≤ ·)).findSome? fun e =>
      if childrenEq S x (.inr e) then some (x, e) else none

def findMovable {n} (S : State n) : Option ℕ :=
  (S.gates.sort (· ≤ ·)).find? fun J =>
    decide (IsAffineOp (S.gate J).op) &&
    !(isGate S (S.gate J).left) &&
    !(isGate S (S.gate J).right)

def findDegeneratePair {n} (S : State n) : Option ℕ :=
  let badFsts := (S.pairs.filter (fun pr => S.deg pr.fst = 0 ∨ 2 ≤ S.deg pr.fst)).image ZeroPair.fst
  let badSnds := (S.pairs.filter (fun pr => S.deg pr.snd = 0 ∨ 2 ≤ S.deg pr.snd)).image ZeroPair.snd
  if h : badFsts.Nonempty then some (badFsts.max' h)
  else if h2 : badSnds.Nonempty then some (badSnds.max' h2)
  else none

def encodeChild : ℕ ⊕ ℕ → ℕ
  | .inl J => 2 * J
  | .inr e => 2 * e + 1

def decodeChild : ℕ → ℕ ⊕ ℕ
  | c => if c % 2 = 0 then .inl (c / 2) else .inr (c / 2)

def findPartnersShareChild {n} (S : State n) : Option (ℕ × (ℕ ⊕ ℕ)) :=
  let bad := S.pairs.filter fun pr => (S.children pr.fst ∩ S.children pr.snd).Nonempty
  let badFsts := bad.image ZeroPair.fst
  if h : badFsts.Nonempty then
    let fst := badFsts.max' h
    let snds := (bad.filter (fun pr => pr.fst = fst)).image ZeroPair.snd
    if hsnd : snds.Nonempty then
      let snd := snds.max' hsnd
      let childSet := S.children fst ∩ S.children snd
      let childEnc := childSet.image encodeChild
      if h2 : childEnc.Nonempty then
        some (fst, decodeChild (childEnc.max' h2))
      else none
    else none
  else none

def isConstantGate {n} (S : State n) (J : ℕ) : Bool :=
  match (S.gate J).left, (S.gate J).right with
  | .const _b1, .const _b2 => true
  | .const b1, _ => decide ((S.gate J).op b1 false = (S.gate J).op b1 true)
  | _, .const b2 => decide ((S.gate J).op false b2 = (S.gate J).op true b2)
  | .node u, .node v => decide (u = v)

def findD1 {n} (S : State n) : Option ℕ :=
  (S.gates.sort (· ≤ ·)).find? fun J =>
    decide (isConstantGate S J)

def findPairInSystem {n} (S : State n) : Option ℕ :=
  (S.eqns.sort (· ≤ ·)).findSome? fun e =>
    ((S.eqn e).terms.sort (· ≤ ·)).findSome? fun p =>
      if decide (S.Paired p) then some p else none

def findAndOnPair {n} (S : State n) : Option (ℕ × ℕ) :=
  (S.gates.sort (· ≤ ·)).findSome? fun G =>
    if decide (!IsAffineOp (S.gate G).op) then
      match (S.gate G).left, (S.gate G).right with
      | .node p, .node w =>
        if decide (p ≠ w ∧ p ∈ S.params ∧ w ∈ S.params) then
          if decide (S.Paired p) then some (G, p)
          else if decide (S.Paired w) then some (G, w)
          else none
        else none
      | _, _ => none
    else none

def chooseStep? {n} (S : State n) : Option StepChoice :=
  if let some J := findD1 S then some (.deleteConstantGate J)
  else if let some J := findD2 S then some (.deleteDeadGate J)
  else if let some e := findD3 S then some (.deleteShortEqn e)
  else if let some (x, e) := findD4 S then some (.deleteUnitParam x e)
  else if let some J := findMovable S then some (.moveAffine J)
  else if let some p := findDegeneratePair S then some (.degeneratePair p)
  else if let some (pr_fst, _H) := findPartnersShareChild S then some (.partnersShareChild pr_fst)
  else if let some p := findPairInSystem S then some (.pairInSystem p)
  else if let some (G, p) := findAndOnPair S then some (.andOnPair G p)
  else if hne : S.gates.Nonempty then
    let G := S.gates.min' hne
    if 0 < S.auxIn G then some (.swapAuxIn G)
    else some (.pairCreation G)
  else none

def toDenseRow (m : ℕ) (terms : Finset ℕ) (c : Bool) : Row :=
  ⟨(List.range m).map (fun i => decide (i ∈ terms)), c⟩

def evaluateAux {n} (S : State n) (a : ℕ) (val : ℕ → Bool) : Bool :=
  let sys : System := (S.eqns.sort (· ≤ ·)).map fun e =>
    toDenseRow S.m (S.eqn e).terms (S.eqn e).rhs
  let paramSys : System := (S.params.sort (· ≤ ·)).map fun p =>
    toDenseRow S.m {p} (val p)
  let aSys : System := [toDenseRow S.m {a} false]
  let F : System := sys ++ paramSys ++ aSys
  if Cslib.Complexity.XORSAT.Dense.decide ⟨S.m, F⟩ then false else true

def findAffineRep {n} (S : State n) (a : ℕ) : Bool × Finset ℕ :=
  let c := evaluateAux S a (fun _ => false)
  let T := S.params.filter fun y => evaluateAux S a (fun j => j == y) != c
  (c, T)

open Cslib.Circuits.Boolean.AffineDisperser4n
open Cslib.Circuits.Boolean.AffineDisperserCore
open Cslib.Circuits.Boolean.SemiCircuit
open Cslib.Complexity.XORSAT.Dense Cslib.Circuits Cslib.BitString

def findPair {n} (S : State n) (p : ℕ) : Option ZeroPair :=
  (S.params.sort (· ≤ ·)).findSome? fun r =>
    let prs : List ZeroPair := [
      ⟨p, false, r, false⟩, ⟨p, false, r, true⟩,
      ⟨p, true, r, false⟩, ⟨p, true, r, true⟩,
      ⟨r, false, p, false⟩, ⟨r, false, p, true⟩,
      ⟨r, true, p, false⟩, ⟨r, true, p, true⟩
    ]
    prs.find? (fun (pr : ZeroPair) => decide (pr ∈ S.pairs))

def applyStep {n} (S : State n) (choice : StepChoice) : State n :=
  match choice with
  | .deleteConstantGate J =>
    let g := S.gate J
    State.deleteGate S J (Lit.const (g.op false false))
  | .deleteDeadGate J =>
    State.deleteGate S J (Lit.const false)
  | .deleteShortEqn e =>
    let terms := (S.eqn e).terms.sort (· ≤ ·)
    match terms.find? (fun v => decide (v ∈ S.aux)) with
    | some v =>
      let rest := terms.filter (· ≠ v)
      let ℓ := if rest.isEmpty then Lit.const (S.eqn e).rhs
               else Lit.node rest.head! (S.eqn e).rhs
      State.deleteEqn S e v ℓ
    | none => State.dropEqn S e 0
  | .deleteUnitParam x e =>
    let terms := (S.eqn e).terms.sort (· ≤ ·)
    match terms.find? (fun v => decide (v ∈ S.aux)) with
    | some Q =>
      let T := (S.eqn e).terms.erase Q
      let S₁ := State.swap S x Q (S.eqn e).rhs T
      State.dropEqn S₁ e x
    | none => S
  | .moveAffine J => State.moveAffine S J S.freshEqn
  | .degeneratePair p =>
    match findPair S p with
    | some pr => State.fixConst S p (pr.bias p)
    | none => S
  | .partnersShareChild p =>
    match findPair S p with
    | some pr =>
      let r := pr.partner p
      let H_gate := (S.gates.sort (· ≤ ·)).find? (fun G => decide (Sum.inl G ∈ S.children p ∩ S.children r))
      match H_gate with
      | some G =>
          let φ (a b : Bool) := (S.gate G).op
            (if (S.gate G).left == Arg.node p then a else b)
            (if (S.gate G).right == Arg.node p then a else b)
          if φ pr.fstBias false == φ pr.fstBias true then
            State.fixConst S p (pr.bias p)
          else if φ false pr.sndBias == φ true pr.sndBias then
            State.fixConst S r (pr.bias r)
          else
            State.restrict S p (Lit.node r !(pr.fstBias ^^ pr.sndBias)) (S.pairsAvoid p)
      | none =>
        State.restrict S p (Lit.node r !(pr.fstBias ^^ pr.sndBias)) (S.pairsAvoid p)
    | none => S
  | .pairInSystem p =>
    match findPair S p with
    | some pr => State.fixConst S (pr.partner p) (pr.partnerBias p)
    | none => S
  | .andOnPair _ p =>
    match findPair S p with
    | some pr => State.fixConst S (pr.partner p) (pr.partnerBias p)
    | none => S
  | .swapAuxIn G =>
    let a := match (S.gate G).left, (S.gate G).right with
             | .node u, .node v => if decide (u ∈ S.aux) then some u else if decide (v ∈ S.aux) then some v else none
             | .node u, .const _ => if decide (u ∈ S.aux) then some u else none
             | .const _, .node v => if decide (v ∈ S.aux) then some v else none
             | _, _ => none
    let b := match (S.gate G).left, (S.gate G).right with
             | .node u, .node v => if decide (u ∈ S.aux) then some v else some u
             | .node u, .const _ => some u
             | .const _, .node v => some v
             | _, _ => none
    match a, b with
    | some a, some b =>
      let (c, T) := findAffineRep S a
      let y := (T.sort (· ≤ ·)).find? (fun u => decide (u ≠ b ∧ u ∈ S.unpaired ∧ 2 ≤ S.deg u))
      match y with
      | some y => State.swap S y a c T
      | none => S
    | _, _ => S
  | .pairCreation G =>
    let t1 := match (S.gate G).left with | .node u => u | _ => 0
    let t2 := match (S.gate G).right with | .node v => v | _ => 0
    let op := (S.gate G).op
    let α := decide (op true false == op true true)
    let β := decide (op false true == op true true)
    State.addPair S ⟨t1, α, t2, β⟩

def isFstOfAnyPair {n} (S : State n) (x : ℕ) : Bool :=
  match findPair S x with
  | some pr => decide (pr.fst = x)
  | none => false

def terminalVal {n} (S : State n) (d_params : List ℕ) (A : List Bool) (x : ℕ) : Bool :=
  match findPair S x with
  | some pr => if pr.fst = x then !pr.fstBias else
      match d_params.findIdx? (· = x) with
      | some i => A.getD i false
      | none => false
  | none =>
    match d_params.findIdx? (· = x) with
    | some i => A.getD i false
    | none => false

def getDParams {n} (S : State n) (d : ℕ) : List ℕ :=
  let F := (S.params.sort (· ≤ ·)).filter (fun x => !(isFstOfAnyPair S x))
  F.take d

def allAssignments : ℕ → List (List Bool)
  | 0 => [[]]
  | m + 1 => let r := allAssignments m; r.map (false :: ·) ++ r.map (true :: ·)

def findCounterexample {n} (C : Circuit (fullSignature 2 Bool) n 1) (f : BitString n → Bool) (d : ℕ) (S : State n) : Option (BitString n) :=
  let d_params := getDParams S d
  (allAssignments d).findSome? fun A =>
    let val_param := terminalVal S d_params A
    let val_all := fun y => if decide (y ∈ S.params) then val_param y else evaluateAux S y val_param
    let x_vec : BitString n := S.phi val_all
    if C.eval fullInterpretation x_vec 0 != f x_vec then some x_vec else none

def refuterLoop {n} (S : State n) (fuel : ℕ) : State n :=
  match fuel with
  | 0 => S
  | fuel' + 1 =>
    match chooseStep? S with
    | some choice => refuterLoop (applyStep S choice) fuel'
    | none => S

def refute {n d : ℕ} (C : Circuit (fullSignature 2 Bool) n 1) (f : BitString n → Bool) : BitString n :=
  let S_init := initialState C
  let S_final := refuterLoop S_init (S_init.m + S_init.s)
  match findCounterexample C f d S_final with
  | some x => x
  | none => fun _ => false

end Cslib.Circuits.Boolean.AffineDisperser4n
