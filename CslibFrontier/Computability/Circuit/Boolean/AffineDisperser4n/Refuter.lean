/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Circuit.Boolean.AffineDisperser4n.Step
public import CslibFrontier.Computability.Circuit.Boolean.AffineDisperser4n
public import CslibFrontier.Computability.Complexity.Problems.XORSAT.Dense

/-!
# Deterministic refuter for `4n - 10d` circuits

The refuter `refute` takes a full-basis circuit `C` and a Boolean function `f` and returns an
input. `RefuterProofs.lean` proves (`refute_correct`) that `C` and `f` disagree on that input
whenever `C.size + 10 * d < 4 * n` and `f` is a `d`-affine disperser. The `poly(n, 2^d)` running
time of the source is not formalized here.

`refute` runs gate elimination from `initialState C`. At each state `chooseStep?` selects one of
the cases of `State.Valid.exists_step`, and `applyStep` performs the concrete successor that the
corresponding lemma proves to be a step (`State.deleteConstraint`, `State.partnersShareChildStep`,
`State.andOnPairStep`, …). None of these needs the disperser property. Where the existence proof
uses it, `chooseStep?` stops instead: when the output is a constant, a parameter, an auxiliary
variable over no gates, or the minimal gate. `findCounterexample` then searches `2^d` inputs of an
affine subspace of dimension `d` on which the output is constant (affine representations of
auxiliary variables are computed by dense `XORSAT` elimination, `evaluateAux`).

## Main definitions

* `Cslib.Circuits.Boolean.AffineDisperser4n.chooseStep?`,
  `Cslib.Circuits.Boolean.AffineDisperser4n.applyStep`: choosing and performing a step.
* `Cslib.Circuits.Boolean.AffineDisperser4n.refuterLoop`,
  `Cslib.Circuits.Boolean.AffineDisperser4n.findCounterexample`,
  `Cslib.Circuits.Boolean.AffineDisperser4n.refute`: the refuter.
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.AffineDisperser4n

open Cslib.Circuits.Boolean.AffineDisperserCore
open Cslib.Circuits.Boolean.SemiCircuit
open Cslib.Complexity.XORSAT.Dense Cslib.Circuits Cslib.BitString

open State

/-- The step chosen by the refuter. -/
inductive StepChoice
  /-- `(D1)`: delete the degenerate gate `J`. -/
  | deleteConstantGate (J : ℕ)
  /-- `(D2)`: delete the gate `J`, which nothing reads. -/
  | deleteDeadGate (J : ℕ)
  /-- `(D3)`: delete the equation `e` of at most two terms. -/
  | deleteShortEqn (e : ℕ)
  /-- `(D4)`: unit-delete the parameter `x`, whose only child is the equation `e`. -/
  | deleteUnitParam (x e : ℕ)
  /-- Move the affine gate `J` into the affine system. -/
  | moveAffine (J : ℕ)
  /-- Case 2: the paired parameter `p` has degree `0` or at least `2`. -/
  | degeneratePair (p : ℕ)
  /-- Case 3: `p` is the first member of a pair whose members share a child. -/
  | partnersShareChild (p : ℕ)
  /-- Case 4: the paired parameter `p` occurs in an equation. -/
  | pairInSystem (p : ℕ)
  /-- Case 5a: the non-affine gate `G` reads the paired parameter `p` and another parameter. -/
  | andOnPair (G p : ℕ)
  /-- Case 5b, preparation: swap an auxiliary argument of the minimal gate `G`. -/
  | swapAuxIn (G : ℕ)
  /-- Case 5b: pair creation on the minimal gate `G`. -/
  | pairCreation (G : ℕ)

/-- Whether an argument is a gate of `S`. -/
def isGate {n} (S : State n) : Arg → Bool
  | .const _ => false
  | .node i => decide (i ∈ S.gates)

/-- Whether a gate is degenerate (`Gate.Degenerate`): it has a constant argument or two equal
arguments. -/
def isDegenerate (g : Gate) : Bool :=
  match g.left, g.right with
  | .const _, _ => true
  | _, .const _ => true
  | .node u, .node v => decide (u = v)

/-- `(D1)`: the least degenerate gate. -/
def findD1 {n} (S : State n) : Option ℕ :=
  (S.gates.sort (· ≤ ·)).find? fun J => isDegenerate (S.gate J)

/-- `(D2)`: the least gate that no gate and not the output reads. -/
def findD2 {n} (S : State n) : Option ℕ :=
  (S.gates.sort (· ≤ ·)).find? fun J =>
    decide ((∀ K ∈ S.gates, ¬ (S.gate K).Reads J) ∧ S.out.arg ≠ .node J)

/-- `(D3)`: the least equation with at most two terms. -/
def findD3 {n} (S : State n) : Option ℕ :=
  (S.eqns.sort (· ≤ ·)).find? fun e =>
    decide ((S.eqn e).terms.card ≤ 2)

/-- `(D4)`: the least unpaired parameter not read by the output whose only child is an equation,
with that equation. -/
def findD4 {n} (S : State n) : Option (ℕ × ℕ) :=
  (S.unpaired.sort (· ≤ ·)).findSome? fun x =>
    if S.out.arg = .node x then none
    else (S.eqns.sort (· ≤ ·)).findSome? fun e =>
      if S.children x = {.inr e} then some (x, e) else none

/-- The least affine gate reading no gate. -/
def findMovable {n} (S : State n) : Option ℕ :=
  (S.gates.sort (· ≤ ·)).find? fun J =>
    decide (IsAffineOp (S.gate J).op) &&
    !(isGate S (S.gate J).left) &&
    !(isGate S (S.gate J).right)

/-- Case 2: the least paired parameter of degree `0` or at least `2`. -/
def findDegeneratePair {n} (S : State n) : Option ℕ :=
  (S.params.sort (· ≤ ·)).find? fun p =>
    decide (S.Paired p ∧ (S.deg p = 0 ∨ 2 ≤ S.deg p))

/-- Case 3: the least first member of a pair whose members share a child. -/
def findPartnersShareChild {n} (S : State n) : Option ℕ :=
  (S.params.sort (· ≤ ·)).find? fun p =>
    decide (∃ pr ∈ S.pairs, pr.fst = p ∧ (S.children pr.fst ∩ S.children pr.snd).Nonempty)

/-- Case 4: the least paired parameter occurring in an equation. -/
def findPairInSystem {n} (S : State n) : Option ℕ :=
  (S.params.sort (· ≤ ·)).find? fun p =>
    decide (S.Paired p ∧ ∃ e ∈ S.eqns, p ∈ (S.eqn e).terms)

/-- Case 5a: the least non-affine gate reading two distinct parameters, one of them paired, with
a paired argument. -/
def findAndOnPair {n} (S : State n) : Option (ℕ × ℕ) :=
  (S.gates.sort (· ≤ ·)).findSome? fun G =>
    if ¬ IsAffineOp (S.gate G).op then
      match (S.gate G).left, (S.gate G).right with
      | .node p, .node w =>
        if p ≠ w ∧ p ∈ S.params ∧ w ∈ S.params then
          if S.Paired p then some (G, p)
          else if S.Paired w then some (G, w)
          else none
        else none
      | _, _ => none
    else none

/-- The step taken by the refuter in `S`, or `none` when `S` is terminal. -/
def chooseStep? {n} (S : State n) : Option StepChoice :=
  match S.out.arg with
  | .const _ => none
  | .node u =>
    if u ∈ S.params then none
    else if let some J := findD1 S then some (.deleteConstantGate J)
    else if let some J := findD2 S then some (.deleteDeadGate J)
    else if let some e := findD3 S then some (.deleteShortEqn e)
    else if let some (x, e) := findD4 S then some (.deleteUnitParam x e)
    else if let some J := findMovable S then some (.moveAffine J)
    else if let some p := findDegeneratePair S then some (.degeneratePair p)
    else if let some p := findPartnersShareChild S then some (.partnersShareChild p)
    else if let some p := findPairInSystem S then some (.pairInSystem p)
    else if let some (G, p) := findAndOnPair S then some (.andOnPair G p)
    else if hne : S.gates.Nonempty then
      let G := S.gates.min' hne
      if 0 < S.auxIn G then some (.swapAuxIn G)
      else if u = G then none
      else some (.pairCreation G)
    else none

/-- The dense `XORSAT` row of width `m` of the equation `∑ terms = c`. -/
def toDenseRow (m : ℕ) (terms : Finset ℕ) (c : Bool) : Row :=
  ⟨(List.range m).map (fun i => decide (i ∈ terms)), c⟩

/-- A strict upper bound on the names of the parameters and auxiliary variables of `S`: the width
of the dense `XORSAT` systems built by `evaluateAux`. -/
def varBound {n} (S : State n) : ℕ :=
  (S.params ∪ S.aux).sup id + 1

/-- The value of `a` in the solution of the affine system of `S` extending the parameter values
`val`: `false` exactly when the system together with `a = false` is satisfiable. -/
def evaluateAux {n} (S : State n) (a : ℕ) (val : ℕ → Bool) : Bool :=
  let N := varBound S
  let sys : System := (S.eqns.sort (· ≤ ·)).map fun e =>
    toDenseRow N (S.eqn e).terms (S.eqn e).rhs
  let paramSys : System := (S.params.sort (· ≤ ·)).map fun p =>
    toDenseRow N {p} (val p)
  let aSys : System := [toDenseRow N {a} false]
  let F : System := sys ++ paramSys ++ aSys
  if Cslib.Complexity.XORSAT.Dense.decide ⟨N, F⟩ then false else true

/-- The affine representation `(c, T)` of `a` in the parameters, read off from `evaluateAux` at
the zero assignment and at the unit assignments. -/
def findAffineRep {n} (S : State n) (a : ℕ) : Bool × Finset ℕ :=
  let c := evaluateAux S a (fun _ => false)
  let T := S.params.filter fun y => evaluateAux S a (fun j => j == y) != c
  (c, T)

/-- The pair of `S` containing `p`, found by searching the possible partners in `S.params`. -/
def findPair {n} (S : State n) (p : ℕ) : Option ZeroPair :=
  (S.params.sort (· ≤ ·)).findSome? fun r =>
    let prs : List ZeroPair := [
      ⟨p, false, r, false⟩, ⟨p, false, r, true⟩,
      ⟨p, true, r, false⟩, ⟨p, true, r, true⟩,
      ⟨r, false, p, false⟩, ⟨r, false, p, true⟩,
      ⟨r, true, p, false⟩, ⟨r, true, p, true⟩
    ]
    prs.find? (fun (pr : ZeroPair) => decide (pr ∈ S.pairs))

/-- The children of `p`: the gates reading it, then the equations containing it, in increasing
order. -/
def getChildren {n} (S : State n) (p : ℕ) : List (ℕ ⊕ ℕ) :=
  let inls := (S.gates.sort (· ≤ ·)).filterMap
    (fun J => if Sum.inl J ∈ S.children p then some (Sum.inl J) else none)
  let inrs := (S.eqns.sort (· ≤ ·)).filterMap
    (fun e => if Sum.inr e ∈ S.children p then some (Sum.inr e) else none)
  inls ++ inrs

/-- `(D4)` unit delete of the parameter `x` with only child the equation `e`: swap `x` with the
least auxiliary variable whose affine representation contains `x`, then drop `e` and `x`. -/
def unitDelete {n} (S : State n) (x e : ℕ) : State n :=
  match (S.aux.sort (· ≤ ·)).find? (fun Q => decide (x ∈ (findAffineRep S Q).2)) with
  | some Q => (S.swap x Q (findAffineRep S Q).1 (findAffineRep S Q).2).dropEqn e x
  | none => S

/-- The argument of `g` other than `p`. -/
def otherArg (g : Gate) (p : ℕ) : ℕ :=
  match g.left, g.right with
  | .node u, .node v => if u = p then v else u
  | _, _ => p

/-- A value `b` of the argument `w` of a non-affine gate `g` making `g` constant, with that
constant. -/
def fixArg (g : Gate) (w : ℕ) : Bool × Bool :=
  if g.right = .node w then
    let b := !decide (g.op false false = g.op true false)
    (b, g.op false b)
  else
    let b := !decide (g.op false false = g.op false true)
    (b, g.op b false)

/-- An auxiliary argument `a` of `g` with the other argument `b`. -/
def auxArgs {n} (S : State n) (g : Gate) : Option (ℕ × ℕ) :=
  match g.left, g.right with
  | .node u, .node v =>
    if u ∈ S.aux then some (u, v) else if v ∈ S.aux then some (v, u) else none
  | _, _ => none

/-- Apply the step `choice` to `S`. -/
def applyStep {n} (S : State n) (choice : StepChoice) : State n :=
  match choice with
  | .deleteConstantGate J => S.deleteConstraint (.inl J)
  | .deleteDeadGate J => S.deleteGate J (Lit.const false)
  | .deleteShortEqn e => S.deleteConstraint (.inr e)
  | .deleteUnitParam x e => unitDelete S x e
  | .moveAffine J => S.moveAffine J S.freshEqn
  | .degeneratePair p =>
    match findPair S p with
    | some pr =>
      if S.deg p = 0 then S.fixConst (pr.partner p) (pr.partnerBias p)
      else
        match getChildren S p with
        | N₁ :: N₂ :: _ => ((S.fixConst p (pr.bias p)).deleteConstraint N₁).deleteConstraint N₂
        | _ => S
    | none => S
  | .partnersShareChild p =>
    match findPair S p, getChildren S p with
    | some pr, H :: _ => S.partnersShareChildStep pr H
    | _, _ => S
  | .pairInSystem p =>
    match findPair S p with
    | some pr =>
      match getChildren S (pr.partner p), getChildren S p with
      | Hr :: _, .inr e :: _ =>
        let S₂ := (S.fixConst (pr.partner p) (pr.partnerBias p)).deleteConstraint Hr
        if S₂.deg p = 0 then S₂ else unitDelete S₂ p e
      | _, _ => S
    | none => S
  | .andOnPair G p =>
    match findPair S p with
    | some pr =>
      match getChildren S (pr.partner p) with
      | Hr :: _ =>
        let w := otherArg (S.gate G) p
        S.andOnPairStep G pr p w (findPair S w) (fixArg (S.gate G) w).1 (fixArg (S.gate G) w).2
          Hr
      | [] => S
    | none => S
  | .swapAuxIn G =>
    match auxArgs S (S.gate G) with
    | some (a, b) =>
      let rep := findAffineRep S a
      if rep.2 ⊆ {b} then
        S.deleteGate G ((S.gate G).subst a
          (if rep.2 = ∅ then Lit.const rep.1 else ⟨.node b, rep.1⟩)).lit
      else
        match (rep.2.sort (· ≤ ·)).find? (fun y => decide (y ≠ b ∧ y ∈ S.unpaired)) with
        | some y => S.swap y a rep.1 rep.2
        | none => S
    | none => S
  | .pairCreation G =>
    match (S.gate G).left, (S.gate G).right with
    | .node t₁, .node t₂ =>
      let op := (S.gate G).op
      let α := decide (op true false = op true true)
      let β := decide (op false true = op true true)
      match (S.gates.sort (· ≤ ·)).find? (fun K => decide (K ≠ G ∧ (S.gate K).Reads G)) with
      | some K =>
        ((S.addPair ⟨t₁, α, t₂, β⟩).deleteGate G (Lit.const (op α β))).deleteConstraint (.inl K)
      | none => S
    | _, _ => S

/-- Whether `x` is the first member of a pair of `S`. -/
def isFstOfAnyPair {n} (S : State n) (x : ℕ) : Bool :=
  match findPair S x with
  | some pr => decide (pr.fst = x)
  | none => false

/-- The parameter values of a terminal state used by `findCounterexample`: first members of pairs
take their bias, the parameters of `d_params` read `A`, and the others are `false`. -/
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



/-- The measure decreased by every step of the refuter. -/
def refuterMeasure {n} (S : State n) : ℕ :=
  4 * (S.m + S.s) + 3 * S.gates.card + S.a +
    if h : S.gates.Nonempty then S.auxIn (S.gates.min' h) else 0

/-- All Boolean lists of length `m`. -/
def allAssignments : ℕ → List (List Bool)
  | 0 => [[]]
  | m + 1 => let r := allAssignments m; r.map (false :: ·) ++ r.map (true :: ·)

/-- Search the `2^d` assignments of a terminal state for an input on which `C` and `f` disagree. -/
def findCounterexample {n} (C : Circuit (fullSignature 2 Bool) n 1) (f : BitString n → Bool)
    (d : ℕ) (S : State n) : Option (BitString n) :=
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

/-- Apply refuter steps until a terminal state is reached or `fuel` runs out. -/
def refuterLoop {n} (S : State n) (fuel : ℕ) : State n :=
  match fuel with
  | 0 => S
  | fuel' + 1 =>
    match chooseStep? S with
    | some choice => refuterLoop (applyStep S choice) fuel'
    | none => S

/-- The refuter: run gate elimination from the initial state of `C`, then search the terminal state
for an input on which `C` and `f` disagree. -/
def refute {n d : ℕ} (C : Circuit (fullSignature 2 Bool) n 1)
    (f : BitString n → Bool) : BitString n :=
  let S_init := initialState C
  let S_final := refuterLoop S_init (refuterMeasure S_init)
  match findCounterexample C f d S_final with
  | some x => x
  | none => fun _ => false

end Cslib.Circuits.Boolean.AffineDisperser4n
