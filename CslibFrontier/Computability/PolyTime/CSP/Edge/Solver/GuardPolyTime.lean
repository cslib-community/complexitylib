/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PolyTime.CSP.Edge.Solver.Guard
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Fold
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.EraseDupsBy

/-!
# Native polynomial time for the complete edge-model guard

The certificates cover every raw binary-arity table and binary-name CSP, including malformed
widths. All row, row-pair and coordinate loops are funded by explicit framed lists. Local
working indices and counts use unary encodings; original arities and variable names stay binary.
-/

public section

namespace Cslib.Complexity.CSP.EdgeSolver

open Cslib.Logic.PL Cslib.Logic.PL.CSP Turing.MultiTapeTM Cslib.BitString

private theorem poly_parity :
    ComputableInPolyTime wordParity (encList encBool) encBool := by
  unfold wordParity
  simp only [List.foldr_eq_foldl]
  apply ComputableInPolyTime.of_tidy
  apply ComputableTidilyInPolyTime.foldl_of_bounded_growth
    (encA := encBool) (encL := encList encBool) (encB := encBool)
    (ComputableInPolyTime.id' (encIn := encList encBool)).tidy
    (ComputableInPolyTime.const false).tidy
    (show ComputableInPolyTime (fun p : Bool × Bool => p.1 ^^ p.2)
      (encPair encBool encBool) encBool from by fun_prop).tidy
    (growth := 0)
  intro state value
  cases state <;> cases value <;> decide

private theorem poly_parityWith {α : Type} {e : α ↪ List Bool} {f : α → List Bool}
    (hf : ComputableInPolyTime f e (encList encBool)) :
    ComputableInPolyTime (fun x => wordParity (f x)) e encBool := poly_parity.comp hf

attribute [local fun_prop] poly_parityWith EdgeAugmenting.poly_zipIdx EdgeAugmenting.poly_flip
  EdgeAugmenting.poly_semWith

private theorem poly_lookupWith {α : Type} {e : α ↪ List Bool}
    {bits : α → List Bool} {index : α → ℕ}
    (hb : ComputableInPolyTime bits e (encList encBool))
    (hi : ComputableInPolyTime index e encUnary) :
    ComputableInPolyTime (fun x => (bits x).getD (index x) false) e encBool :=
  ComputableInPolyTime.listGetDWithInput hb hi false

private theorem poly_flipWith {α : Type} {e : α ↪ List Bool}
    {bits : α → List Bool} {indices : α → List ℕ}
    (hb : ComputableInPolyTime bits e (encList encBool))
    (hi : ComputableInPolyTime indices e (encList encUnary)) :
    ComputableInPolyTime (fun x => EdgeAugmenting.flip (bits x) (indices x)) e
      (encList encBool) := EdgeAugmenting.poly_flip.comp (hb.prod hi)

attribute [local fun_prop] poly_lookupWith poly_flipWith

/-- Table first, then the two framed Boolean rows in order. -/
private abbrev encPairInput := encPair encTable
  (encPair (encList encBool) (encList encBool))

private theorem poly_checkPair : ComputableInPolyTime
    (fun p : Table × List Bool × List Bool => checkPair p.1 p.2.1 p.2.2)
    encPairInput encBool := by
  unfold checkPair
  have hp : ComputableInPolyTime
      (fun p : Table × List Bool × List Bool => decide (wordParity p.2.1 = wordParity p.2.2))
      encPairInput encBool := by fun_prop
  have he : ComputableInPolyTime
      (fun p : (Table × List Bool × List Bool) × (Bool × ℕ) =>
        p.1.2.1.zipIdx.any fun (b, j) => b != p.1.2.2.getD j false &&
          p.1.1.sem (EdgeAugmenting.flip p.1.2.1 [p.2.2, j]))
      (encPair encPairInput (encPair encBool encUnary)) encBool := by
    apply ComputableInPolyTime.anyWithInput
      (show ComputableInPolyTime
        (fun p : (Table × List Bool × List Bool) × (Bool × ℕ) => p.1.2.1.zipIdx)
        (encPair encPairInput (encPair encBool encUnary))
        (encList (encPair encBool encUnary)) from by fun_prop)
    fun_prop
  have hs : ComputableInPolyTime
      (fun p : (Table × List Bool × List Bool) × (Bool × ℕ) =>
        p.2.1 == p.1.2.2.getD p.2.2 false ||
        p.1.2.1.zipIdx.any fun (b, j) => b != p.1.2.2.getD j false &&
          p.1.1.sem (EdgeAugmenting.flip p.1.2.1 [p.2.2, j]))
      (encPair encPairInput (encPair encBool encUnary)) encBool := by fun_prop
  have ha : ComputableInPolyTime
      (fun p : Table × List Bool × List Bool => p.2.1.zipIdx.all fun (a, i) =>
        a == p.2.2.getD i false || p.2.1.zipIdx.any fun (b, j) =>
          b != p.2.2.getD j false && p.1.sem (EdgeAugmenting.flip p.2.1 [i, j]))
      encPairInput encBool := by
    apply ComputableInPolyTime.allWithInput
      (show ComputableInPolyTime (fun p : Table × List Bool × List Bool => p.2.1.zipIdx)
        encPairInput (encList (encPair encBool encUnary)) from by fun_prop)
    exact hs
  exact ComputableInPolyTime.bool_and.comp (hp.prod ha)

private theorem poly_checkPairWith {α : Type} {e : α ↪ List Bool}
    {t : α → Table} {x y : α → List Bool}
    (ht : ComputableInPolyTime t e encTable)
    (hx : ComputableInPolyTime x e (encList encBool))
    (hy : ComputableInPolyTime y e (encList encBool)) :
    ComputableInPolyTime (fun a => checkPair (t a) (x a) (y a)) e encBool :=
  poly_checkPair.comp (ht.prod (hx.prod hy))

attribute [local fun_prop] poly_checkPairWith

/-- A full constraint guard is ordinary native polynomial-time on all raw tables and scopes. -/
@[fun_prop] theorem computableInPolyTime_checkConstraint :
    ComputableInPolyTime checkConstraint (encConstraint encTable encNat) encBool := by
  unfold checkConstraint
  have hlen : ComputableInPolyTime (fun c : Constraint Table ℕ => c.2.length)
      (encConstraint encTable encNat) encUnary := by fun_prop
  have hwidth : ComputableInPolyTime
      (fun c : Constraint Table ℕ => decide (c.1.arity = c.2.length))
      (encConstraint encTable encNat) encBool :=
    ComputableInPolyTime.decide_eq' (by fun_prop)
      (ComputableInPolyTime.unary_to_binary.comp hlen)
  fun_prop

/-- The edge incidence check scans actual scopes and names, including arbitrarily sparse
binary names. Its count results are unary and bounded by the explicit occurrence list. -/
@[fun_prop] theorem computableInPolyTime_checkEdge :
    ComputableInPolyTime checkEdge (encCSP encTable encNat) encBool := by
  unfold checkEdge
  have hnodup : ComputableInPolyTime
      (fun p : CSP Table ℕ × Constraint Table ℕ => decide p.2.2.Nodup)
      (encPair (encCSP encTable encNat) (encConstraint encTable encNat)) encBool :=
    ComputableInPolyTime.decide_nodup (by fun_prop)
  have hcount : ComputableInPolyTime
      (fun p : CSP Table ℕ × ℕ => p.1.vars.count p.2)
      (encPair (encCSP encTable encNat) encNat) encUnary :=
    .of_tidy (ComputableTidilyInPolyTime.countWithInput
      (show ComputableInPolyTime (fun p : CSP Table ℕ × ℕ => p.1.vars)
        (encPair (encCSP encTable encNat) encNat) (encList encNat) from by fun_prop).tidy
      (ComputableInPolyTime.snd _ _).tidy)
  fun_prop

/-- Every check in the full model guard is supplied internally by native machines.
No input validity or relation-recognition premise appears in the runtime certificate. -/
@[fun_prop] theorem computableInPolyTime_checkModel :
    ComputableInPolyTime checkModel (encCSP encTable encNat) encBool := by
  unfold checkModel
  fun_prop

end Cslib.Complexity.CSP.EdgeSolver
