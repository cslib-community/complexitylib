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
    if decide (isNode x S.out.arg) then none
    else (S.eqns.sort (· ≤ ·)).findSome? fun e =>
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

def degenerateLit {n} (S : State n) (J : ℕ) : Option Lit :=
  let g := S.gate J
  let op := g.op
  let eval (L R : Bool) : Bool :=
    let bL := match g.left with | .const b => b | .node _ => L
    let bR := match g.right with | .const b => b | .node _ => R
    op bL bR
  let oFF := eval false false
  let oFT := eval false true
  let oTF := eval true false
  let oTT := eval true true
  if oFF == oFT && oTF == oTT then
    if oFF == oTF then some (Lit.const oFF)
    else match g.left with
         | .node u => some (Lit.node u oFF)
         | .const _ => none
  else if oFF == oTF && oFT == oTT then
    if oFF == oFT then some (Lit.const oFF)
    else match g.right with
         | .node v => some (Lit.node v oFF)
         | .const _ => none
  else if let (.node u, .node v) := (g.left, g.right) then
    if u == v then
      if oFF == oTT then some (Lit.const oFF)
      else some (Lit.node u oFF)
    else none
  else none

def findD1 {n} (S : State n) : Option ℕ :=
  (S.gates.sort (· ≤ ·)).find? fun J =>
    decide ((degenerateLit S J).isSome)

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
  match S.out.arg with
  | .const _ => none
  | .node u =>
    if decide (u ∈ S.params) then none
    else if let some J := findD1 S then some (.deleteConstantGate J)
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
      else if decide (u = G) then none
      else some (.pairCreation G)
    else none

def toDenseRow (m : ℕ) (terms : Finset ℕ) (c : Bool) : Row :=
  ⟨(List.range m).map (fun i => decide (i ∈ terms)), c⟩

/-- A strict upper bound on the names of the parameters and auxiliary variables of `S`: the width
of the dense `XORSAT` systems built by `evaluateAux`. -/
def varBound {n} (S : State n) : ℕ :=
  (S.params ∪ S.aux).sup id + 1

def evaluateAux {n} (S : State n) (a : ℕ) (val : ℕ → Bool) : Bool :=
  let N := varBound S
  let sys : System := (S.eqns.sort (· ≤ ·)).map fun e =>
    toDenseRow N (S.eqn e).terms (S.eqn e).rhs
  let paramSys : System := (S.params.sort (· ≤ ·)).map fun p =>
    toDenseRow N {p} (val p)
  let aSys : System := [toDenseRow N {a} false]
  let F : System := sys ++ paramSys ++ aSys
  if Cslib.Complexity.XORSAT.Dense.decide ⟨N, F⟩ then false else true

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

def getChildren {n} (S : State n) (p : ℕ) : List (ℕ ⊕ ℕ) :=
  let inls := (S.gates.sort (· ≤ ·)).filterMap
    (fun J => if decide (Sum.inl J ∈ S.children p) then some (Sum.inl J) else none)
  let inrs := (S.eqns.sort (· ≤ ·)).filterMap
    (fun e => if decide (Sum.inr e ∈ S.children p) then some (Sum.inr e) else none)
  inls ++ inrs

def deleteChild {n} (S : State n) (child : ℕ ⊕ ℕ) : State n :=
  match child with
  | .inl J => State.deleteGate S J ((degenerateLit S J).getD (Lit.const false))
  | .inr e =>
    let terms := (S.eqn e).terms.sort (· ≤ ·)
    match terms.find? (fun v => decide (v ∈ S.aux)) with
    | some v =>
      let rest := terms.filter (· ≠ v)
      let ℓ := if rest.isEmpty then Lit.const (S.eqn e).rhs
               else Lit.node rest.head! (S.eqn e).rhs
      State.deleteEqn S e v ℓ
    | none => State.dropEqn S e 0

def applyStep {n} (S : State n) (choice : StepChoice) : State n :=
  match choice with
  | .deleteConstantGate J =>
    let l := (degenerateLit S J).getD (Lit.const false)
    State.deleteGate S J l
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
    | some pr =>
      if S.deg p == 0 then
        State.fixConst S (pr.partner p) (pr.partnerBias p)
      else
        let S₁ := State.fixConst S p (pr.bias p)
        match getChildren S p with
        | c0 :: c1 :: _ =>
          let S₂ := deleteChild S₁ c0
          deleteChild S₂ c1
        | _ => S₁
    | none => S
  | .partnersShareChild p =>
    match findPair S p with
    | some pr =>
      let r := pr.partner p
      let H_gate := (S.gates.sort (· ≤ ·)).find?
        (fun G => decide (Sum.inl G ∈ S.children p ∩ S.children r))
      match H_gate with
      | some G =>
          let φ (a b : Bool) := (S.gate G).op
            (if (S.gate G).left == Arg.node p then a else b)
            (if (S.gate G).right == Arg.node p then a else b)
          if φ pr.fstBias false == φ pr.fstBias true then
            let S₁ := State.fixConst S p (pr.bias p)
            State.deleteGate S₁ G ((degenerateLit S₁ G).getD (Lit.const false))
          else if φ false pr.sndBias == φ true pr.sndBias then
            let S₁ := State.fixConst S r (pr.bias r)
            State.deleteGate S₁ G ((degenerateLit S₁ G).getD (Lit.const false))
          else
            let S₁ := State.restrict S p (Lit.node r !(pr.fstBias ^^ pr.sndBias)) (S.pairsAvoid p)
            State.deleteGate S₁ G ((degenerateLit S₁ G).getD (Lit.const false))
      | none =>
        State.restrict S p (Lit.node r !(pr.fstBias ^^ pr.sndBias)) (S.pairsAvoid p)
    | none => S
  | .pairInSystem p =>
    match findPair S p with
    | some pr =>
      let r := pr.partner p
      let S₁ := State.fixConst S r (pr.partnerBias p)
      match (getChildren S r).head? with
      | some Hr => deleteChild S₁ Hr
      | none => S₁
    | none => S
  | .andOnPair G p =>
    match findPair S p with
    | some pr =>
      let r := pr.partner p
      let S₁ := State.fixConst S r (pr.partnerBias p)
      let S₂ := State.deleteGate S₁ G ((degenerateLit S₁ G).getD (Lit.const false))
      match (getChildren S r).head? with
      | some Hr => deleteChild S₂ Hr
      | none => S₂
    | none => S
  | .swapAuxIn G =>
    let a := match (S.gate G).left, (S.gate G).right with
             | .node u, .node v =>
               if decide (u ∈ S.aux) then some u
               else if decide (v ∈ S.aux) then some v else none
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
    let S₁ := State.addPair S ⟨t1, α, t2, β⟩
    let γ := op α β
    let S₂ := State.deleteGate S₁ G (Lit.const γ)
    let K_opt := (S.gates.sort (· ≤ ·)).find? (fun K => decide (K ≠ G) && readsJ S K G)
    match K_opt with
    | some K => State.deleteGate S₂ K ((degenerateLit S₂ K).getD (Lit.const false))
    | none => S₂

def isFstOfAnyPair {n} (S : State n) (x : ℕ) : Bool :=
  match findPair S x with
  | some pr => decide (pr.fst = x)
  | none => false

def terminalVal {n} (S : State n) (d_params : List ℕ) (A : List Bool) (x : ℕ) : Bool :=
  match findPair S x with
  | some pr => if pr.fst = x then pr.fstBias else
      match d_params.findIdx? (· = x) with
      | some i => A.getD i false
      | none => false
  | none =>
    match d_params.findIdx? (· = x) with
    | some i => A.getD i false
    | none => false



def refuterMeasure {n} (S : State n) : ℕ :=
  4 * (S.m + S.s) + 3 * S.gates.card + S.a +
    if h : S.gates.Nonempty then S.auxIn (S.gates.min' h) else 0

def allAssignments : ℕ → List (List Bool)
  | 0 => [[]]
  | m + 1 => let r := allAssignments m; r.map (false :: ·) ++ r.map (true :: ·)

def findCounterexample {n} (C : Circuit (fullSignature 2 Bool) n 1) (f : BitString n → Bool) (d : ℕ)
    (S : State n) : Option (BitString n) :=
  match S.out.arg with
  | .const _b =>
    let F := (S.params.sort (· ≤ ·)).filter (fun x => !(isFstOfAnyPair S x))
    let d_params := F.take d
    (allAssignments d).findSome? fun A =>
      let val_param := terminalVal S d_params A
      let val_all := fun y =>
        if decide (y ∈ S.params) then val_param y else evaluateAux S y val_param
      let x_vec : BitString n := S.phi val_all
      if C.eval fullInterpretation x_vec 0 != f x_vec then
        some x_vec
      else none
  | .node u =>
    let F := (S.params.sort (· ≤ ·)).filter (fun x => !(isFstOfAnyPair S x))
    if decide (u ∈ S.params) || S.gates.card == 0 then
      let (c_out, T_out) :=
        if decide (u ∈ S.params) then (false, ({u} : Finset ℕ)) else findAffineRep S u
      match F.find? (fun v => decide (v ∈ T_out)) with
      | some pivot =>
        let d_params := (F.filter (· ≠ pivot)).take d
        (allAssignments d).findSome? fun A =>
          let val_param_part := terminalVal S d_params A
          let T_erase := T_out.filter (· ≠ pivot)
          let xorSum := (T_erase.sort (· ≤ ·)).foldl (fun acc y => acc ^^ val_param_part y) false
          let pivot_val := c_out ^^ S.out.neg ^^ xorSum
          let val_param := fun y => if y = pivot then pivot_val else val_param_part y
          let val_all := fun y =>
            if decide (y ∈ S.params) then val_param y else evaluateAux S y val_param
          let x_vec : BitString n := S.phi val_all
          if C.eval fullInterpretation x_vec 0 != f x_vec then some x_vec else none
      | none =>
        let d_params := F.take d
        (allAssignments d).findSome? fun A =>
          let val_param := terminalVal S d_params A
          let val_all := fun y =>
            if decide (y ∈ S.params) then val_param y else evaluateAux S y val_param
          let x_vec : BitString n := S.phi val_all
          if C.eval fullInterpretation x_vec 0 != f x_vec then some x_vec else none
    else if hne : S.gates.Nonempty then
      let G := S.gates.min' hne
      let α := decide ((S.gate G).op true false == (S.gate G).op true true)
      let t1 := match (S.gate G).left with | .node x => x | _ => 0
      let d_params := (F.filter (· ≠ t1)).take d
      (allAssignments d).findSome? fun A =>
        let val_param_part := terminalVal S d_params A
        let val_param := fun y => if y = t1 then α else val_param_part y
        let val_all := fun y =>
          if decide (y ∈ S.params) then val_param y else evaluateAux S y val_param
        let x_vec : BitString n := S.phi val_all
        if C.eval fullInterpretation x_vec 0 != f x_vec then some x_vec else none
    else none

def refuterLoop {n} (S : State n) (fuel : ℕ) : State n :=
  match fuel with
  | 0 => S
  | fuel' + 1 =>
    match chooseStep? S with
    | some choice => refuterLoop (applyStep S choice) fuel'
    | none => S

def refute {n d : ℕ} (C : Circuit (fullSignature 2 Bool) n 1)
    (f : BitString n → Bool) : BitString n :=
  let S_init := initialState C
  let S_final := refuterLoop S_init (refuterMeasure S_init)
  match findCounterexample C f d S_final with
  | some x => x
  | none => fun _ => false

end Cslib.Circuits.Boolean.AffineDisperser4n
