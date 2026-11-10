/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.CookLevin.Correctness
public import CslibFrontier.Computability.Complexity.Fagin.Layout

/-!
# Relation variables and first-order formulas for the ESO tableau sentence

Given a deterministic multi-tape Turing machine `tm : MultiTapeTM m Bool State` (`[Fintype State]
[DecidableEq State]`) and a bundle `r : FO.TableauRels L' m State` of relation symbols over a
first-order language `L'`, this file defines the relation-variable index types and first-order
component formulas of the existential second-order tableau sentence on `Fin B`.

## Main definitions

* `Cslib.Logic.FO.UnaryTableauVar`, `Cslib.Logic.FO.BinaryTableauVar`,
  `Cslib.Logic.FO.TableauVar`, `Cslib.Logic.FO.tableauArity`: existential second-order relation
  variables and their arities.
* `Cslib.Logic.FO.TableauRels`: bundle of the 12 relation-symbol families used by the first-order
  tableau formulas.
* `Cslib.Logic.FO.endPosSentence`, `Cslib.Logic.FO.initSentence`, `Cslib.Logic.FO.stepSentence`,
  `Cslib.Logic.FO.acceptSentence`: the four component sentences of the tableau matrix.

## References

* [R. Fagin, *Generalized first-order spectra and polynomial-time recognizable sets*][Fagin1974]
* [N. Immerman, *Descriptive Complexity*][Immerman1999]
* [C. H. Papadimitriou, *Computational Complexity*][Papadimitriou94], Theorem 8.3
-/

@[expose] public section

namespace Cslib.Logic

open FirstOrder FirstOrder.Language FirstOrder.Language.Structure
open Turing Turing.MultiTapeTM Turing.MultiTapeTM.Feature
open Cslib.Complexity

namespace FO

/-! ### Relation variables of the ESO tableau sentence -/

/-- Indices of the unary relation variables of the ESO tableau sentence:
* `.inl ()`: `endPos` (holds of the unique element `e = u.length + w.length`),
* `.inr (.inl ())`: `certBit` (holds of input position `j` for `u.length < j ≤ e` when
  `w[j - 1 - u.length] = true`),
* `.inr (.inr (.inl q))`: `state q` at time `t`,
* `.inr (.inr (.inr o))`: `out o` at time `t`. -/
abbrev UnaryTableauVar (State : Type) : Type :=
  Unit ⊕ Unit ⊕ Option State ⊕ OutView

/-- Indices of the binary relation variables of the ESO tableau sentence:
* `.inl ()`: `inPos` at `(t, j)`,
* `.inr (.inl i)`: `head i (+a)` at `(t, a)`,
* `.inr (.inr (.inl i))`: `head i (-a)` at `(t, a)`,
* `.inr (.inr (.inr (.inl (i, s))))`: `cell i (+a) s` at `(t, a)`,
* `.inr (.inr (.inr (.inr (i, s))))`: `cell i (-a) s` at `(t, a)`. -/
abbrev BinaryTableauVar (m : ℕ) : Type :=
  Unit ⊕ Fin m ⊕ Fin m ⊕ (Fin m × Option Bool) ⊕ (Fin m × Option Bool)

/-- Indices of all existential relation variables of the ESO tableau sentence. -/
abbrev TableauVar (m : ℕ) (State : Type) : Type :=
  UnaryTableauVar State ⊕ BinaryTableauVar m

/-- Arity assignment for `TableauVar m State`. -/
def tableauArity (m : ℕ) (State : Type) : TableauVar m State → ℕ
  | .inl _ => 1
  | .inr _ => 2

/-- Bundle of the 12 relation-symbol families used by the first-order tableau formulas over `L'`. -/
structure TableauRels (L' : Language.{0, 0}) (m : ℕ) (State : Type) where
  /-- Strict linear order `<` on `Fin B`. -/
  lt : L'.Relations 2
  /-- Unary relation holding of the unique element `z = u.length`. -/
  uLen : L'.Relations 1
  /-- Unary relation holding of `p < u.length` when `u[p] = true`. -/
  uBit : L'.Relations 1
  /-- Unary relation holding of the unique certificate end position `e = u.length + w.length`. -/
  endPos : L'.Relations 1
  /-- Unary relation holding of `j ∈ (u.length, e]` when `w[j - 1 - u.length] = true`. -/
  certBit : L'.Relations 1
  /-- Unary relation family for `(Feature.state q).Holds (cfg t)`. -/
  state : Option State → L'.Relations 1
  /-- Unary relation family for `(Feature.out o).Holds (cfg t)`. -/
  out : OutView → L'.Relations 1
  /-- Binary relation for `(Feature.inPos j).Holds (cfg t)`. -/
  inPos : L'.Relations 2
  /-- Binary relation family for `(Feature.head i (+a)).Holds (cfg t)`. -/
  headPos : Fin m → L'.Relations 2
  /-- Binary relation family for `(Feature.head i (-a)).Holds (cfg t)`. -/
  headNeg : Fin m → L'.Relations 2
  /-- Binary relation family for `(Feature.cell i (+a) s).Holds (cfg t)`. -/
  cellPos : Fin m → Option Bool → L'.Relations 2
  /-- Binary relation family for `(Feature.cell i (-a) s).Holds (cfg t)`. -/
  cellNeg : Fin m → Option Bool → L'.Relations 2

section Formulas

variable {L' : Language.{0, 0}} {m : ℕ} {State : Type} (r : TableauRels L' m State)

/-- Sentence asserting that `r.endPos` holds of a unique element `e`, and that `r.uLen ≤ e` and `e`
is not the maximum element (`e + 1 < B`). -/
noncomputable def endPosSentence : L'.Sentence :=
  closeEx (Fin 1) (
    rel₁ r.endPos 0 ⊓
      Formula.iExs (Fin 1) (rel₁ r.uLen (.inr 0) ⊓ le r.lt (.inr 0) (.inl 0)) ⊓
      ∼(isMax r.lt 0)) ⊓
    closeAll (Fin 2) ((rel₁ r.endPos 0 ⊓ rel₁ r.endPos 1) ⟹ varEq 0 1)

/-- Formula expressing `inputAt (u ++ w) j = s` at variable `vJ : V`. -/
noncomputable def inputAtFormula (s : Option Bool) {V : Type*} (vJ : V) : L'.Formula V :=
  match s with
  | none =>
    isZero r.lt vJ ⊔
      Formula.iExs (Fin 1) (rel₁ r.endPos (.inr 0) ⊓ lt r.lt (.inr 0) (.inl vJ))
  | some true =>
    Formula.iExs (Fin 2) (
      succ r.lt (.inr 0) (.inl vJ) ⊓ rel₁ r.uLen (.inr 1) ⊓
        lt r.lt (.inr 0) (.inr 1) ⊓ rel₁ r.uBit (.inr 0)) ⊔
      Formula.iExs (Fin 2) (
        rel₁ r.uLen (.inr 0) ⊓ rel₁ r.endPos (.inr 1) ⊓
          lt r.lt (.inr 0) (.inl vJ) ⊓ le r.lt (.inl vJ) (.inr 1) ⊓ rel₁ r.certBit (.inl vJ))
  | some false =>
    Formula.iExs (Fin 2) (
      succ r.lt (.inr 0) (.inl vJ) ⊓ rel₁ r.uLen (.inr 1) ⊓
        lt r.lt (.inr 0) (.inr 1) ⊓ ∼(rel₁ r.uBit (.inr 0))) ⊔
      Formula.iExs (Fin 2) (
        rel₁ r.uLen (.inr 0) ⊓ rel₁ r.endPos (.inr 1) ⊓
          lt r.lt (.inr 0) (.inl vJ) ⊓ le r.lt (.inl vJ) (.inr 1) ⊓ ∼(rel₁ r.certBit (.inl vJ)))

/-- Formula expressing `(Feature.inRead s).Holds (cfg t)` at time variable `vT : V`. -/
noncomputable def inReadFormula (s : Option Bool) {V : Type*} (vT : V) : L'.Formula V :=
  Formula.iExs (Fin 1) (
    rel₂ r.inPos (.inl vT) (.inr 0) ⊓ inputAtFormula r s (.inr 0))

/-- Formula expressing `(Feature.read i s).Holds (cfg t)` at time variable `vT : V`. -/
noncomputable def readFormula (i : Fin m) (s : Option Bool) {V : Type*} (vT : V) : L'.Formula V :=
  Formula.iExs (Fin 1) (
    (rel₂ (r.headPos i) (.inl vT) (.inr 0) ⊓ rel₂ (r.cellPos i s) (.inl vT) (.inr 0)) ⊔
      (rel₂ (r.headNeg i) (.inl vT) (.inr 0) ⊓ rel₂ (r.cellNeg i s) (.inl vT) (.inr 0)))

/-- Formula expressing `(Feature.sit y).Holds (cfg t)` at time variable `vT : V`. -/
noncomputable def sitFormula (y : Situation m State) {V : Type*} (vT : V) : L'.Formula V :=
  rel₁ (r.state (some y.1)) vT ⊓
    inReadFormula r y.2.1 vT ⊓
    Formula.iInf fun i : Fin m => readFormula r i (y.2.2 i) vT

/-- Formula expressing that the input head moves to `vJ` from its position at time `vT` under
direction `d`. -/
noncomputable def inPosPrevFormula (d : SignType) {V : Type*} (vT vJ : V) : L'.Formula V :=
  match d with
  | .zero => rel₂ r.inPos vT vJ
  | .neg =>
    (isZero r.lt vJ ⊓ rel₂ r.inPos vT vJ) ⊔
      Formula.iExs (Fin 1) (succ r.lt (.inl vJ) (.inr 0) ⊓ rel₂ r.inPos (.inl vT) (.inr 0))
  | .pos =>
    Formula.iExs (Fin 1) (
      rel₁ r.endPos (.inr 0) ⊓ succ r.lt (.inr 0) (.inl vJ) ⊓
        rel₂ r.inPos (.inl vT) (.inl vJ)) ⊔
      Formula.iExs (Fin 2) (
        rel₁ r.endPos (.inr 1) ⊓ le r.lt (.inr 0) (.inr 1) ⊓
          succ r.lt (.inr 0) (.inl vJ) ⊓ rel₂ r.inPos (.inl vT) (.inr 0))

/-- Formula expressing that a work-tape head moves to signed offset `vA` from its position at time
`vT` under effective direction `d` (where `d = .pos` means moving away from `0` and `d = .neg`
means moving toward `0`, crossing into `headOpp` at `1` when `vA = 0` and `d = .pos`). -/
noncomputable def headPrevFormula (headSame headOpp : L'.Relations 2) (d : SignType)
    {V : Type*} (vT vA : V) : L'.Formula V :=
  match d with
  | .zero => rel₂ headSame vT vA
  | .pos =>
    (isZero r.lt vA ⊓ Formula.iExs (Fin 1) (
        succ r.lt (.inl vA) (.inr 0) ⊓ rel₂ headOpp (.inl vT) (.inr 0))) ⊔
      Formula.iExs (Fin 1) (
        succ r.lt (.inr 0) (.inl vA) ⊓ rel₂ headSame (.inl vT) (.inr 0))
  | .neg =>
    Formula.iExs (Fin 1) (
      succ r.lt (.inl vA) (.inr 0) ⊓ rel₂ headSame (.inl vT) (.inr 0))

variable [Fintype State] [DecidableEq State] (tm : MultiTapeTM m Bool State)

/-- Right-hand side of the step equation for `state q'` at time `vT`. -/
noncomputable def stateStepRHS (q' : Option State) {V : Type*} (vT : V) : L'.Formula V :=
  (rel₁ (r.state none) vT ⊓ if q' = none then ⊤ else ⊥) ⊔
    Formula.iSup fun y : Situation m State =>
      (if (tm.actionOf y).state = q' then ⊤ else ⊥) ⊓ sitFormula r y vT

/-- Right-hand side of the step equation for `out o` at time `vT`. -/
noncomputable def outStepRHS (o : OutView) {V : Type*} (vT : V) : L'.Formula V :=
  (rel₁ (r.state none) vT ⊓ rel₁ (r.out o) vT) ⊔
    Formula.iSup fun p : Situation m State × OutView =>
      (if p.2.push (tm.actionOf p.1).output = o then ⊤ else ⊥) ⊓
        sitFormula r p.1 vT ⊓ rel₁ (r.out p.2) vT

/-- Right-hand side of the step equation for `inPos` at time `vT` and position `vJ`. -/
noncomputable def inPosStepRHS {V : Type*} (vT vJ : V) : L'.Formula V :=
  (rel₁ (r.state none) vT ⊓ rel₂ r.inPos vT vJ) ⊔
    Formula.iSup fun y : Situation m State =>
      sitFormula r y vT ⊓ inPosPrevFormula r (tm.actionOf y).inputTape vT vJ

/-- Right-hand side of the step equation for a work-tape head at time `vT` and offset `vA`, with
orientation `sign` (`1` for `+a`, `-1` for `-a`). -/
noncomputable def headStepRHS (headSame headOpp : L'.Relations 2) (sign : SignType) (i : Fin m)
    {V : Type*} (vT vA : V) : L'.Formula V :=
  (rel₁ (r.state none) vT ⊓ rel₂ headSame vT vA) ⊔
    Formula.iSup fun y : Situation m State =>
      sitFormula r y vT ⊓
        headPrevFormula r headSame headOpp (sign * ((tm.actionOf y).workTapes i).2) vT vA

/-- Right-hand side of the step equation for a work-tape cell at time `vT` and offset `vA`. -/
noncomputable def cellStepRHS (headSame : L'.Relations 2) (cellSame : Option Bool → L'.Relations 2)
    (i : Fin m) (s : Option Bool) {V : Type*} (vT vA : V) : L'.Formula V :=
  (rel₂ (cellSame s) vT vA ⊓ (rel₁ (r.state none) vT ⊔ ∼(rel₂ headSame vT vA))) ⊔
    Formula.iSup fun p : Situation m State × Option Bool =>
      (if ((tm.actionOf p.1).workTapes i).1.getD p.2 = s then ⊤ else ⊥) ⊓
        sitFormula r p.1 vT ⊓ rel₂ headSame vT vA ⊓ rel₂ (cellSame p.2) vT vA

/-- Sentence fixing all basic features at `t = 0`. -/
noncomputable def initSentence : L'.Sentence :=
  closeAll (Fin 1) (
    isZero r.lt 0 ⟹
      ((Formula.iInf fun q : Option State =>
          rel₁ (r.state q) 0 ⇔ (if q = some tm.q₀ then ⊤ else ⊥)) ⊓
        (Formula.iInf fun o : OutView =>
          rel₁ (r.out o) 0 ⇔ (if o = .empty then ⊤ else ⊥)) ⊓
        Formula.iAlls (Fin 1) (
          rel₂ r.inPos (.inl 0) (.inr 0) ⇔
            Formula.iExs (Fin 1) (isZero r.lt (.inr 0) ⊓ succ r.lt (.inr 0) (.inl (.inr 0)))) ⊓
        Formula.iInf fun i : Fin m =>
          Formula.iAlls (Fin 1) (
            (rel₂ (r.headPos i) (.inl 0) (.inr 0) ⇔ isZero r.lt (.inr 0)) ⊓
              (rel₂ (r.headNeg i) (.inl 0) (.inr 0) ⇔ isZero r.lt (.inr 0)) ⊓
              Formula.iInf fun s : Option Bool =>
                (rel₂ (r.cellPos i s) (.inl 0) (.inr 0) ⇔ (if s = none then ⊤ else ⊥)) ⊓
                  (rel₂ (r.cellNeg i s) (.inl 0) (.inr 0) ⇔ (if s = none then ⊤ else ⊥)))))

/-- Sentence imposing the step equations from `t` to `t + 1` for all basic features. -/
noncomputable def stepSentence : L'.Sentence :=
  closeAll (Fin 2) (
    succ r.lt 0 1 ⟹
      ((Formula.iInf fun q' : Option State =>
          rel₁ (r.state q') 1 ⇔ stateStepRHS r tm q' 0) ⊓
        (Formula.iInf fun o : OutView =>
          rel₁ (r.out o) 1 ⇔ outStepRHS r tm o 0) ⊓
        Formula.iAlls (Fin 1) (
          rel₂ r.inPos (.inl 1) (.inr 0) ⇔ inPosStepRHS r tm (.inl 0) (.inr 0)) ⊓
        Formula.iInf fun i : Fin m =>
          Formula.iAlls (Fin 1) (
            (rel₂ (r.headPos i) (.inl 1) (.inr 0) ⇔
                headStepRHS r tm (r.headPos i) (r.headNeg i) .pos i (.inl 0) (.inr 0)) ⊓
              (rel₂ (r.headNeg i) (.inl 1) (.inr 0) ⇔
                headStepRHS r tm (r.headNeg i) (r.headPos i) .neg i (.inl 0) (.inr 0)) ⊓
              Formula.iInf fun s : Option Bool =>
                (rel₂ (r.cellPos i s) (.inl 1) (.inr 0) ⇔
                    cellStepRHS r tm (r.headPos i) (r.cellPos i) i s (.inl 0) (.inr 0)) ⊓
                  (rel₂ (r.cellNeg i s) (.inl 1) (.inr 0) ⇔
                    cellStepRHS r tm (r.headNeg i) (r.cellNeg i) i s (.inl 0) (.inr 0)))))

/-- Sentence asking that at the maximum time step `B - 1`, the machine is halted (`state none`)
with output `[true]` (`out (.one true)`). -/
noncomputable def acceptSentence : L'.Sentence :=
  closeAll (Fin 1) (
    isMax r.lt 0 ⟹ (rel₁ (r.state none) 0 ⊓ rel₁ (r.out (.one true)) 0))

end Formulas

end FO

end Cslib.Logic
