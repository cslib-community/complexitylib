/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.CarrySaveLeaf
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.Deterministic
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.MapOutput

/-!
# Native counting leaves for the streamed carry-save evaluator

The native counting evaluator is turned into a claim checker by relabeling its emitted Boolean.
Its actual run on persistent traversal storage discharges both leaf contracts of the cyclic
controller. No leaf oracle or uncharged normalization remains in the resulting finite machine.
-/

public noncomputable section

namespace Turing.MultiTapeATM.CarrySaveCounting

open MultiTapeTM Cslib.CountingLeaf Cslib.Circuits.Boolean
open Cslib.Circuits.Boolean.CarrySaveQuery

/-- The counting leaves addressed by the physical, possibly padded, tape words. -/
@[expose] def leaves (predicate : List Bool × ℕ → Bool) (context count width : List Bool) :
    List Bool → Cslib.BitString (ofBits width + ofBits width) :=
  fun path => Counting.leafPair (ofBits count) (ofBits width)
    (fun j => predicate (context, j)) (Cslib.BitString.binaryValue path)

/-- Relabel a native leaf output as agreement with the requested Boolean claim, with no added
transitions, then view its deterministic run as an alternating computation. -/
@[expose] def claimLeaf {k : ℕ} {S : Type} (leaf : Bool → MultiTapeTM (k + 12) Bool S)
    (carry claim : Bool) : MultiTapeATM (k + 12) Bool S :=
  ofTMs (fun _ => (leaf carry).mapOutput (fun answer => answer == claim)) (fun _ => false)

/-- A concrete deterministic leaf run supplies both cyclic-controller contracts at its actual
clock. Output relabeling and deterministic lifting preserve every transition and the full initial
storage. The native run premise is discharged by the counting-leaf compiler in clients. -/
theorem leaf_contracts {k : ℕ} {S : Type}
    (native : Bool → MultiTapeTM (k + 12) Bool S) (predicate : List Bool × ℕ → Bool)
    (input context count width : List Bool) (leafTime sizeBudget : ℕ)
    (hr : ∀ (height bits path unary : List Bool) (frontier : ℤ) (status carry : Bool),
      height.length + bits.length + path.length ≤ sizeBudget →
      let cfg := CarrySaveLeaf.initial k input context count width height bits path unary
        frontier status
      (native carry).runFrom (cfg.withState (some (native carry).q₀)) leafTime =
        (CarrySaveLeaf.completed (CarrySaveLeaf.prepared cfg carry)
          (CarrySaveLeaf.query context count width path bits carry)
          [runRaw predicate (CarrySaveLeaf.query context count width path bits carry)]).withState
            (State' := S) none) :
    CarrySaveStream.LeafBound (claimLeaf native) leafTime sizeBudget input
      (CarrySaveLeaf.scratch k context count width) ∧
    CarrySaveStream.LeafCorrect (leaves predicate context count width) (claimLeaf native)
      leafTime sizeBudget input (CarrySaveLeaf.scratch k context count width) := by
  have hrun (height bits path unary : List Bool) (frontier : ℤ) (status carry claim : Bool)
      (hb : height.length + bits.length + path.length ≤ sizeBudget) :
      let cfg := CarrySaveLeaf.initial k input context count width height bits path unary
        frontier status
      ((native carry).mapOutput (fun answer => answer == claim)).runFrom
        (cfg.withState (some (native carry).q₀))
        (leafTime) =
      ((CarrySaveLeaf.completed (CarrySaveLeaf.prepared cfg carry)
        (CarrySaveLeaf.query context count width path bits carry)
        [runRaw predicate (CarrySaveLeaf.query context count width path bits carry)]).withState
          (State' := S) none).mapOutput (fun answer => answer == claim) := by
    have h := hr height bits path unary frontier status carry hb
    have hm := runFrom_mapOutput (native carry) (fun answer => answer == claim)
      ((CarrySaveLeaf.initial k input context count width height bits path unary frontier
        status).withState (some (native carry).q₀))
      (leafTime)
    have hi :
        (((CarrySaveLeaf.initial k input context count width height bits path unary frontier
          status).withState (some (native carry).q₀)).mapOutput (fun answer => answer == claim)) =
        (CarrySaveLeaf.initial k input context count width height bits path unary frontier
          status).withState (some (native carry).q₀) := by
      apply Cfg.ext <;> simp [Cfg.mapOutput, CarrySaveLeaf.initial, Cfg.withState]
    rw [hi, h] at hm
    exact hm
  constructor
  · intro height bits path unary frontier status carry claim _ hb
    rw [claimLeaf, haltsWithin_ofTMs_const_iff]
    change (((native carry).mapOutput (fun answer => answer == claim)).runFrom
      ((CarrySaveLeaf.initial k input context count width height bits path unary frontier
        status).withState (some (native carry).q₀)) _).state = none
    rw [hrun height bits path unary frontier status carry claim hb]
    rfl
  · intro height bits path unary frontier status carry claim _ hb _
    rw [claimLeaf, acceptsWithin_ofTMs_const_iff]
    change
      ((((native carry).mapOutput (fun answer => answer == claim)).runFrom
        ((CarrySaveLeaf.initial k input context count width height bits path unary frontier
          status).withState (some (native carry).q₀)) _).state = none ∧
       (((native carry).mapOutput (fun answer => answer == claim)).runFrom
        ((CarrySaveLeaf.initial k input context count width height bits path unary frontier
          status).withState (some (native carry).q₀)) _).output = [true]) ↔ _
    rw [hrun height bits path unary frontier status carry claim hb]
    change (none = (none : Option S) ∧
      [runRaw predicate (CarrySaveLeaf.query context count width path bits carry) == claim] =
        [true]) ↔ _
    rw [runRaw_eq_value]
    change (none = (none : Option S) ∧
      [value (leaves predicate context count width) ⟨path, 0, carry, ofBits bits⟩ == claim] =
        [true]) ↔ _
    simp [ofBits_eq_lsbValue]

/-- Native counting machines satisfy the stream controller's physical leaf contracts with a
single polynomial clock for every bounded path and padded bit-index word. -/
theorem exists_leaves (predicate : List Bool × ℕ → Bool)
    (hp : ComputableInPolyTime predicate (encPair encBits encNat) encBool) :
    ∃ (k : ℕ) (S : Type) (_ : Finite S)
      (leaf : Bool → Bool → MultiTapeATM (k + 12) Bool S) (c d : ℕ),
      ∀ (input context count width : List Bool) (sizeBudget : ℕ),
        CarrySaveStream.LeafBound leaf
          (CarrySaveLeaf.clock c d context count width sizeBudget) sizeBudget input
          (CarrySaveLeaf.scratch k context count width) ∧
        CarrySaveStream.LeafCorrect (leaves predicate context count width) leaf
          (CarrySaveLeaf.clock c d context count width sizeBudget) sizeBudget input
          (CarrySaveLeaf.scratch k context count width) := by
  obtain ⟨k, S, hS, native, c, d, hr⟩ := CarrySaveLeaf.exists_counting predicate hp
  refine ⟨k, S, hS, claimLeaf native, c, d, ?_⟩
  intro input context count width sizeBudget
  apply leaf_contracts native predicate input context count width
    (CarrySaveLeaf.clock c d context count width sizeBudget) sizeBudget
  intro height bits path unary frontier status carry hb
  exact hr input context count width height bits path unary frontier status carry
    sizeBudget (by omega)

/-- Actual alternating leaf machines supply the complete counting traversal at their own clock.
The controller preserves the leaf-time coefficient and charges every traversal transition. -/
theorem spec_of_leaves {k : ℕ} {S : Type}
    (leaf : Bool → Bool → MultiTapeATM (k + 12) Bool S)
    (predicate : List Bool × ℕ → Bool) (input context count width : List Bool)
    (leafTime sizeBudget : ℕ)
    (hleafTime : CarrySaveStream.LeafBound leaf leafTime sizeBudget input
      (CarrySaveLeaf.scratch k context count width))
    (hleaf : CarrySaveStream.LeafCorrect (leaves predicate context count width) leaf
      leafTime sizeBudget input (CarrySaveLeaf.scratch k context count width))
    (height bits path unary : List Bool) (depth : ℕ) (frontier : ℤ) (status carry claim : Bool)
    (hfront : CarrySaveStream.Frontier unary frontier depth)
    (hsize : height.length + bits.length + path.length + depth ≤ sizeBudget)
    (hheight : Cslib.BitString.lsbValue height = depth)
    (hbits : Cslib.BitString.lsbValue bits < ofBits width) :
    let atm := CarrySaveStream.machine leaf carry claim
    let cfg := (CarrySaveLeaf.initial k input context count width height bits path unary
      frontier status).withState (some atm.toPTM.toNTM.q₀)
    let time := CarrySaveStream.budget leafTime depth height bits
    atm.HaltsWithin time cfg ∧
      (atm.AcceptsWithin time cfg ↔
        value (leaves predicate context count width)
          ⟨path, depth, carry, Cslib.BitString.lsbValue bits⟩ = claim) := by
  constructor
  · simpa only [CarrySaveLeaf.initial, CarrySaveStream.machine_q₀] using
      CarrySaveStream.haltsWithin_budget leaf leafTime sizeBudget hleafTime depth height bits
        path unary frontier status carry claim hfront hsize
  · simpa only [CarrySaveLeaf.initial, CarrySaveStream.machine_q₀] using
      CarrySaveStream.acceptsWithin_budget (leaves predicate context count width) leaf leafTime
        sizeBudget hleafTime hleaf depth height bits path unary frontier status carry claim
        hfront hsize hheight hbits

/-- One finite alternating machine evaluates every bounded carry-save counting query from
the actual stream tapes. All native leaf computation and traversal steps are charged. -/
theorem exists_evaluator (predicate : List Bool × ℕ → Bool)
    (hp : ComputableInPolyTime predicate (encPair encBits encNat) encBool) :
    ∃ (k : ℕ) (S : Type) (_ : Finite S)
      (atm : Bool → Bool → MultiTapeATM (k + 12) Bool S) (c d : ℕ),
      ∀ (input context count width height bits path unary : List Bool)
        (depth : ℕ) (frontier : ℤ) (status carry claim : Bool) (sizeBudget : ℕ),
        CarrySaveStream.Frontier unary frontier depth →
        height.length + bits.length + path.length + depth ≤ sizeBudget →
        Cslib.BitString.lsbValue height = depth →
        Cslib.BitString.lsbValue bits < ofBits width →
        let cfg := (CarrySaveLeaf.initial k input context count width height bits path unary
          frontier status).withState (some (atm carry claim).toPTM.toNTM.q₀)
        let time := CarrySaveStream.budget
          (CarrySaveLeaf.clock c d context count width sizeBudget) depth height bits
        (atm carry claim).HaltsWithin time cfg ∧
        ((atm carry claim).AcceptsWithin time cfg ↔
          value (leaves predicate context count width)
            ⟨path, depth, carry, Cslib.BitString.lsbValue bits⟩ = claim) := by
  obtain ⟨k, S, hS, leaf, c, d, hl⟩ := exists_leaves predicate hp
  let := hS
  let := Fintype.ofFinite S
  refine ⟨k, CarrySaveStream.State S, inferInstance, CarrySaveStream.machine leaf, c, d, ?_⟩
  intro input context count width height bits path unary depth frontier status carry claim
    sizeBudget hfront hsize hheight hbits
  obtain ⟨ht, ha⟩ := hl input context count width sizeBudget
  exact spec_of_leaves leaf predicate input context count width _ sizeBudget ht ha height bits
    path unary depth frontier status carry claim hfront hsize hheight hbits

end Turing.MultiTapeATM.CarrySaveCounting
