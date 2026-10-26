/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeLoops
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
public import Complexity.Computability.Machines.Turing.MultiTape.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Complexity.Foundations.Data.List.Fold

/-!
# Polynomial-time folds

The polynomial-time counterparts of Christian Reitwiessner's degree-bounded fold rules. A
`SizedListEncoding` accounts for list lengths, elements and suffixes, leaving only a polynomial
bound on the intermediate accumulator. The step may carry a fixed parameter. Prefix invariants
propagate by a pure list rule, independently of the resource certificates.

## Main results

* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.foldl'`: a fold with bounded accumulators.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.foldlWith`: a fold with a fixed parameter.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.foldl_spec`: one prefix invariant proves
  both polynomial-time computation and the final postcondition.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.foldlWith_spec`: the same contract with a
  computed captured parameter.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.foldlWith_of_bounded_growth`: input-dependent
  additive growth on the values occurring in the runtime list.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.foldlWithInput_of_bounded_growth`: the same
  contract for a callback that captures the original input.

The specification interface is adapted from `IsPolyTime.list_foldl_spec` in the cslib
`crypto` branch, using the tidy machine calculus for the underlying computation.
-/

@[expose] public section

namespace Turing.MultiTapeTM.ComputableTidilyInPolyTime

variable {γ α β π : Type} {encIn : γ ↪ List Bool} {encA : α ↪ List Bool}
  {encB : β ↪ List Bool} {encL : List α ↪ List Bool} {encP : π ↪ List Bool}
  [ListEncoding encA encL] [SizedListEncoding encA encL]

/-- A left fold is polynomial-time when its step is polynomial-time and its intermediate
accumulators have polynomially bounded encoded length. -/
theorem foldl' {list : γ → List α} {init : γ → β} {step : β → α → β}
    (hlist : ComputableTidilyInPolyTime list encIn encL)
    (hinit : ComputableTidilyInPolyTime init encIn encB)
    (hstep : ComputableTidilyInPolyTime (fun p : β × α => step p.1 p.2)
      (encPair encB encA) encB)
    {B : γ → ℕ} (hB : PolyBounded (fun x => (encIn x).length) B)
    (hstates : ∀ x, ∀ i ≤ (list x).length,
      (encB (((list x).take i).foldl step (init x))).length ≤ B x) :
    ComputableTidilyInPolyTime (fun x => (list x).foldl step (init x)) encIn encB := by
  obtain ⟨_, _, hlist⟩ := hlist.exists_degree
  obtain ⟨_, _, hinit⟩ := hinit.exists_degree
  obtain ⟨_, _, hstep⟩ := hstep.exists_degree
  obtain ⟨c, d, hB⟩ := hB.exists_le
  exact (ComputableTidilyInDegree.foldl' hlist hinit hstep
    (show DegreeBounded (fun x => (encIn x).length) B d from ⟨c, hB⟩)
    hstates).computableTidilyInPolyTime

/-- A polynomial-time fold whose step also uses a fixed, polynomial-time computable parameter. -/
theorem foldlWith {par : γ → π} {list : γ → List α} {init : γ → β}
    {step : π → β → α → β}
    (hpar : ComputableTidilyInPolyTime par encIn encP)
    (hlist : ComputableTidilyInPolyTime list encIn encL)
    (hinit : ComputableTidilyInPolyTime init encIn encB)
    (hstep : ComputableTidilyInPolyTime (fun p : (π × β) × α => step p.1.1 p.1.2 p.2)
      (encPair (encPair encP encB) encA) encB)
    {B : γ → ℕ} (hB : PolyBounded (fun x => (encIn x).length) B)
    (hstates : ∀ x, ∀ i ≤ (list x).length,
      (encB (((list x).take i).foldl (step (par x)) (init x))).length ≤ B x) :
    ComputableTidilyInPolyTime (fun x => (list x).foldl (step (par x)) (init x)) encIn encB := by
  obtain ⟨_, _, hpar⟩ := hpar.exists_degree
  obtain ⟨_, _, hlist⟩ := hlist.exists_degree
  obtain ⟨_, _, hinit⟩ := hinit.exists_degree
  obtain ⟨_, _, hstep⟩ := hstep.exists_degree
  obtain ⟨c, d, hB⟩ := hB.exists_le
  exact (ComputableTidilyInDegree.foldlWith hpar hlist hinit hstep
    (show DegreeBounded (fun x => (encIn x).length) B d from ⟨c, hB⟩)
    hstates).computableTidilyInPolyTime

/-- A prefix invariant supplies both the accumulator bound and the final postcondition for a
fold with a captured parameter. The size bound may depend on the original input and need not be
computable. The step certificate is uniform jointly in the parameter, accumulator and element. -/
theorem foldlWith_spec {par : γ → π} {list : γ → List α} {init : γ → β}
    {step : π → β → α → β}
    (hpar : ComputableTidilyInPolyTime par encIn encP)
    (hlist : ComputableTidilyInPolyTime list encIn encL)
    (hinit : ComputableTidilyInPolyTime init encIn encB)
    (hstep : ComputableTidilyInPolyTime (fun p : (π × β) × α => step p.1.1 p.1.2 p.2)
      (encPair (encPair encP encB) encA) encB)
    (invariant : γ → List α → β → Prop)
    (hbase : ∀ x, invariant x [] (init x))
    (hpreserve : ∀ x consumed state value, consumed ++ [value] <+: list x →
      invariant x consumed state → invariant x (consumed ++ [value]) (step (par x) state value))
    {size : γ → ℕ} (hsize : PolyBounded (fun x => (encIn x).length) size)
    (hbound : ∀ x consumed state, consumed <+: list x → invariant x consumed state →
      (encB state).length ≤ size x) :
    ComputableTidilyInPolyTime (fun x => (list x).foldl (step (par x)) (init x)) encIn encB ∧
      ∀ x, invariant x (list x) ((list x).foldl (step (par x)) (init x)) := by
  have htrace (x : γ) (i : ℕ) (hi : i ≤ (list x).length) :
      invariant x ((list x).take i) (((list x).take i).foldl (step (par x)) (init x)) := by
    apply List.foldl_take_invariant (list x) (step (par x)) (init x)
      (fun i state => invariant x ((list x).take i) state) (by simpa using hbase x) ?_ i hi
    intro j hj state hstate
    simpa only [List.take_succ_eq_append_getElem hj] using
      hpreserve x ((list x).take j) state (list x)[j]
        (by simpa only [List.take_succ_eq_append_getElem hj] using
          List.take_prefix (j + 1) (list x)) hstate
  exact ⟨foldlWith hpar hlist hinit hstep hsize
    (fun x i hi => hbound x ((list x).take i) _ (List.take_prefix ..) (htrace x i hi)),
    fun x => by simpa using htrace x (list x).length le_rfl⟩

/-- A prefix invariant supplies both the accumulator bound and the final postcondition.
The size bound may depend on the original input and need not be computable. The list and step
must have uniform polynomial-time certificates. -/
theorem foldl_spec {list : γ → List α} {init : γ → β} {step : β → α → β}
    (hlist : ComputableTidilyInPolyTime list encIn encL)
    (hinit : ComputableTidilyInPolyTime init encIn encB)
    (hstep : ComputableTidilyInPolyTime (fun p : β × α => step p.1 p.2)
      (encPair encB encA) encB)
    (invariant : γ → List α → β → Prop)
    (hbase : ∀ x, invariant x [] (init x))
    (hpreserve : ∀ x consumed state value, consumed ++ [value] <+: list x →
      invariant x consumed state → invariant x (consumed ++ [value]) (step state value))
    {size : γ → ℕ} (hsize : PolyBounded (fun x => (encIn x).length) size)
    (hbound : ∀ x consumed state, consumed <+: list x → invariant x consumed state →
      (encB state).length ≤ size x) :
    ComputableTidilyInPolyTime (fun x => (list x).foldl step (init x)) encIn encB ∧
      ∀ x, invariant x (list x) ((list x).foldl step (init x)) :=
  foldlWith_spec (step := fun (_ : Bool) => step) (const false) hlist hinit
    (hstep.comp ((fst (encPair encBool encB) encA).snd'.prod (snd _ _)))
    invariant hbase hpreserve hsize hbound

/-- A captured fold may add a polynomial amount of storage per element, measured against the
original input. The growth bound covers every accumulator and each element in the runtime list;
the joint step certificate still covers all parameters, accumulators and elements. -/
theorem foldlWith_of_bounded_growth {par : γ → π} {list : γ → List α} {init : γ → β}
    {step : π → β → α → β}
    (hpar : ComputableTidilyInPolyTime par encIn encP)
    (hlist : ComputableTidilyInPolyTime list encIn encL)
    (hinit : ComputableTidilyInPolyTime init encIn encB)
    (hstep : ComputableTidilyInPolyTime (fun p : (π × β) × α => step p.1.1 p.1.2 p.2)
      (encPair (encPair encP encB) encA) encB)
    {growth : γ → ℕ} (hpoly : PolyBounded (fun x => (encIn x).length) growth)
    (hgrowth : ∀ x state value, value ∈ list x →
      (encB (step (par x) state value)).length ≤ (encB state).length + growth x) :
    ComputableTidilyInPolyTime (fun x => (list x).foldl (step (par x)) (init x)) encIn encB := by
  refine (foldlWith_spec hpar hlist hinit hstep
    (fun x consumed state => (encB state).length ≤
      (encB (init x)).length + consumed.length * growth x)
    (by simp) ?_
    (hinit.polyBounded_length.add (hlist.polyBounded_length.mul hpoly)) ?_).1
  · intro x consumed state value hprefix hs
    have := hgrowth x state value (hprefix.subset (by simp))
    simp only [List.length_append, List.length_singleton, Nat.add_mul, Nat.one_mul]
    lia
  · intro x consumed state hprefix hs
    have hlen := hprefix.length_le.trans
      (SizedListEncoding.length_le (encA := encA) (encL := encL) (list x))
    exact hs.trans (Nat.add_le_add_left (Nat.mul_le_mul_right (growth x) hlen) _)

omit [ListEncoding encA encL] [SizedListEncoding encA encL] in
/-- A fold callback may capture its original input. Growth is needed only on elements of the
runtime list, for every accumulator. Joint computation and encoding evidence lets automation
choose compatible list and callback certificates; paired growth obligations select a common
polynomial bound. The general `foldlWith_of_bounded_growth` contract takes separate premises. -/
theorem foldlWithInput_of_bounded_growth {list : γ → List α} {init : γ → β}
    {step : γ → β → α → β}
    (hinit : ComputableTidilyInPolyTime init encIn encB)
    (hcompute : ComputableTidilyInPolyTime list encIn encL ∧
      ComputableTidilyInPolyTime (fun p : (γ × β) × α => step p.1.1 p.1.2 p.2)
        (encPair (encPair encIn encB) encA) encB ∧
      ListEncoding encA encL ∧ SizedListEncoding encA encL)
    {growth : γ → ℕ} (hbound : PolyBounded (fun x => (encIn x).length) growth ∧
      ∀ x state value, value ∈ list x →
      (encB (step x state value)).length ≤ (encB state).length + growth x) :
    ComputableTidilyInPolyTime (fun x => (list x).foldl (step x) (init x)) encIn encB := by
  let := hcompute.2.2.1
  let := hcompute.2.2.2
  exact foldlWith_of_bounded_growth id' hcompute.1 hinit hcompute.2.1 hbound.1 hbound.2

/-- Constant additive growth discharges the fold's intermediate-size obligation. -/
theorem foldl_of_bounded_growth {list : γ → List α} {init : γ → β} {step : β → α → β}
    (hlist : ComputableTidilyInPolyTime list encIn encL)
    (hinit : ComputableTidilyInPolyTime init encIn encB)
    (hstep : ComputableTidilyInPolyTime (fun p : β × α => step p.1 p.2)
      (encPair encB encA) encB)
    {growth : ℕ}
    (hgrowth : ∀ state value, (encB (step state value)).length ≤
      (encB state).length + growth) :
    ComputableTidilyInPolyTime (fun x => (list x).foldl step (init x)) encIn encB :=
  foldlWith_of_bounded_growth (step := fun (_ : Bool) => step) (const false) hlist hinit
    (hstep.comp ((fst (encPair encBool encB) encA).snd'.prod (snd _ _)))
    (.const growth) (fun _ state value _ => hgrowth state value)

end Turing.MultiTapeTM.ComputableTidilyInPolyTime

/-! ### Plain captured-input folds -/
