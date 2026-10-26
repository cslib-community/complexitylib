/-
Copyright (c) 2026 Erik Demaine, Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Christian Reitwiessner, Samuel Schlesinger
-/
module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListPrimitives
public import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeOptionPrimitives
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.List.Index
import Complexity.Computability.Machines.Turing.MultiTape.Internal.EqualityPrimitives
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.Bounds
import Mathlib.Data.List.GetD


import Diag1155.Measure
/-! # Direct plain list lookup and first occurrence

Unary dropping uses the existing full-prefix fold and the codec's bare tail machine.
Fixed-default lookup uses the bare head machine, without an inhabitedness assumption.
First occurrence uses the original credited Boolean/counter fold.
-/


diag1155_install
@[expose] public section
namespace Turing.MultiTapeTM.ComputableInPolyTime
open Cslib Internal.ListIndex
variable {α : Type} {encA : α ↪ List Bool}

private theorem tailPlain {encL : List α ↪ List Bool} [ListEncoding encA encL] :
    ComputableInPolyTime List.tail encL encL := by
  obtain ⟨c, k, Q, hfin, tm, htm⟩ := ListEncoding.tail (enc₁ := encA) (enc := encL)
  exact ⟨fun n => c * (n + 1), fun n => c * (n + 1), by fun_prop, by fun_prop,
    k, Q, hfin, tm, fun l => htm l⟩

private theorem headPlain {encL : List α ↪ List Bool} [ListEncoding encA encL] (d : α) :
    ComputableInPolyTime (fun l : List α => l.headD d) encL encA := by
  obtain ⟨c, k, Q, hfin, tm, htm⟩ := ListEncoding.headD (enc₁ := encA) (enc := encL) d
  exact ⟨fun n => c * (n + 1), fun n => c * (n + 1), by fun_prop, by fun_prop,
    k, Q, hfin, tm, fun l => htm l⟩

/-- Drop a unary number of elements, retaining arbitrary sized list encodings. -/
theorem dropUnary {encL : List α ↪ List Bool} [ListEncoding encA encL]
    [SizedListEncoding encA encL] :
    ComputableInPolyTime (fun p : List α × ℕ => p.1.drop p.2)
      (encPair encL encUnary) encL := by
  have heq (l : List α) (n : ℕ) :
      (List.replicate n true).foldl (fun acc _ => acc.tail) l = l.drop n := by
    simp [List.foldl_const, List.tail_iterate]
  have h := foldl' (encA := encBool) (encL := encBits)
    (list := fun p : List α × ℕ => List.replicate p.2 true) (step := fun acc _ => acc.tail)
    ((of_eq (encIn := encUnary) (encOut := encBits) fun _ => rfl).comp (snd encL encUnary))
    (fst encL encUnary) ((tailPlain (encA := encA) (encL := encL)).comp (fst encL encBool))
    (B := fun p => (encPair encL encUnary p).length) .self (fun p i _ => by
      rw [List.take_replicate, heq]
      have := SizedListEncoding.length_drop_le (encA := encA) (encL := encL) p.1 (min i p.2)
      simp only [length_encPair]
      omega)
  simpa only [heq] using h

/-- Read an optional head in any list encoding, without an inhabitant of the element type. -/
@[fun_prop]
theorem head? (enc : α ↪ List Bool) {encL : List α ↪ List Bool}
    [_inst3 : ListEncoding enc encL] :
    ComputableInPolyTime List.head? encL (encOption enc) := by
  rcases isEmpty_or_nonempty α with h | h
  · exact of_finite _
  · obtain ⟨fallback⟩ := h
    have hempty : ComputableInPolyTime List.isEmpty encL encBool := by
      obtain ⟨c, k, Q, hfin, tm, htm⟩ := ListEncoding.isEmpty (enc₁ := enc) (enc := encL)
      exact ⟨fun n => c * (n + 1), fun n => c * (n + 1), by fun_prop, by fun_prop,
        k, Q, hfin, tm, fun l => htm l⟩
    have hread := hempty.ite (const none) ((optionSome enc).comp (headPlain fallback))
    convert hread using 1
    funext values
    cases values <;> rfl

/-- Look up a computed unary index, returning `none` outside a computed list. The list certificate
determines its encoding before proof search checks the corresponding operation and size rules. -/
@[fun_prop]
theorem getElem? {α γ : Type} {encA : α ↪ List Bool} {encIn : γ ↪ List Bool}
    {encL : List α ↪ List Bool}
    {list : γ → List α} {index : γ → ℕ}
    (hlist : ComputableInPolyTime list encIn encL)
    (hindex : ComputableInPolyTime index encIn encUnary)
    [ListEncoding encA encL] [SizedListEncoding encA encL] :
    ComputableInPolyTime (fun x => (list x)[index x]?) encIn (encOption encA) := by
  simpa only [Function.comp_def, List.head?_drop] using
    (head? encA).comp ((dropUnary (encA := encA)).comp (hlist.prod hindex))

/-- Lookup with an explicit default and unary index, in any sized list encoding. -/
@[fun_prop]
theorem listGetD {encL : List α ↪ List Bool} [ListEncoding encA encL]
    [SizedListEncoding encA encL] (d : α) :
    ComputableInPolyTime (fun p : List α × ℕ => p.1.getD p.2 d)
      (encPair encL encUnary) encA := by
  simpa only [Function.comp_def, List.headD_eq_head?_getD, List.head?_drop,
    List.getD_eq_getElem?_getD] using (headPlain d).comp (dropUnary (encA := encA))

/-- The first occurrence, or the list length when absent; the returned index is unary. -/
@[fun_prop]
theorem idxOf [DecidableEq α] (enc : α ↪ List Bool) :
    ComputableInPolyTime (fun p : List α × α => p.1.idxOf p.2)
      (encPair (encList enc) enc) encUnary := by
  have heq : ComputableInPolyTime (fun p : α × α => decide (p.1 = p.2))
      (encPair enc enc) encBool := (ComputableInO.eq enc).computableInPolyTime
    (.of_forall_le 1 2 fun p => by simp only [length_encPair]; nlinarith) .self
  have hor : ComputableInPolyTime (fun p : Bool × Bool => p.1 || p.2)
      (encPair encBool encBool) encBool := of_finite _
  have hstep : ComputableInPolyTime
      (fun q : (α × (Bool × ℕ)) × α => idxStep q.1.1 q.1.2 q.2)
      (encPair (encPair enc (encPair encBool encUnary)) enc) (encPair encBool encUnary) := by
    have hq := fst (encPair enc (encPair encBool encUnary)) enc
    have hn := hq.snd'.snd'
    have ha := snd (encPair enc (encPair encBool encUnary)) enc
    exact (hor.comp (hq.snd'.fst'.prod (heq.comp (ha.prod hq.fst')))).ite
      ((const true).prod hn) ((const false).prod (unary_succ.comp hn))
  have h := foldlWith_of_bounded_growth (snd (encList enc) enc) (fst (encList enc) enc)
    (const (false, 0)) hstep
    (growth := fun _ => 1) (.const 1) (by
      intro p state value _
      unfold idxStep
      split <;> simp)
  simpa only [Function.comp_def, foldl_idxStep, Bool.false_eq_true, ite_false, Nat.zero_add]
    using (snd encBool encUnary).comp h

/-- Find a computed value's first occurrence in a computed list. -/
@[fun_prop]
theorem idxOfWithInput {α γ : Type} {encA : α ↪ List Bool} {encIn : γ ↪ List Bool}
    [DecidableEq α] {list : γ → List α} {value : γ → α}
    (hlist : ComputableInPolyTime list encIn (encList encA))
    (hvalue : ComputableInPolyTime value encIn encA) :
    ComputableInPolyTime (fun x => (list x).idxOf (value x)) encIn encUnary :=
  (idxOf encA).comp (hlist.prod hvalue)

end Turing.MultiTapeTM.ComputableInPolyTime
