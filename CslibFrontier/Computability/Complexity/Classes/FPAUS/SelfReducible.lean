/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Unary
public import Mathlib.Data.Finset.Card

/-!
# Self-reducible witness families

A family of finite witness sets `W x`, with witnesses bit strings, is **self-reducible** when the
witnesses of an instance `x` all have one computable length `len x`, and, when that length is
positive, the witnesses beginning with the bit `b` are exactly `b :: w` for the witnesses `w` of a
computable instance `child x b` that is no longer than `x` and has witness length `len x - 1`
[Jerrum, Valiant and Vazirani][JerrumValiantVazirani1986],
[Sinclair, Lecture 4, Section 4.2.1][Sinclair2025]. Satisfying assignments of a Boolean formula
are the standard example: `child φ b` substitutes `b` for the first variable.

This is the form in which each step fixes one bit; more general forms of self-reducibility, fixing
several symbols per step, are not covered. The structure records the explicit reduction maps as
data, together with polynomial-time certificates for them and for the base case `len x = 0`,
where the only possible witness is the empty word.

## Main definitions

* `Cslib.Complexity.SelfReducible`: a self-reduction of a witness family.

## Main results

* `Cslib.Complexity.SelfReducible.card_filter_head`: the witnesses beginning with `b` are counted
  by the child.
* `Cslib.Complexity.SelfReducible.card_eq_add`: `|W x| = |W (child x false)| + |W (child x true)|`.
* `Cslib.Complexity.SelfReducible.eq_singleton_nil`: at length `0` a nonempty family is `{[]}`.

## References

* [M. R. Jerrum, L. G. Valiant, V. V. Vazirani, *Random generation of combinatorial structures from
  a uniform distribution*][JerrumValiantVazirani1986]
* [A. Sinclair, *CS294 Partition Functions*, Lecture 4, Section 4.2.1][Sinclair2025]
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

variable {α : Type}

/-- A **self-reduction** of the witness family `W` on instances encoded by `enc`: every witness
of `x` has length `len x`, and, when `len x > 0`, the witnesses of `x` beginning with `b` are the
words `b :: w` for `w ∈ W (child x b)`, where `child x b` is no longer than `x` and has witness
length `len x - 1`. The witness length (in unary), the reduction and the base-case membership test
`[] ∈ W x` are polynomial-time. -/
structure SelfReducible (enc : α ↪ List Bool) (W : α → Finset (List Bool)) where
  /-- The common length of the witnesses of an instance. -/
  len : α → ℕ
  /-- The instance whose witnesses are the tails of the witnesses beginning with a given bit. -/
  child : α → Bool → α
  /-- Witnesses of `x` have length `len x`. -/
  length_eq : ∀ x, ∀ w ∈ W x, w.length = len x
  /-- Prefixing `b` maps the witnesses of `child x b` onto those of `x` beginning with `b`. -/
  cons_mem_iff : ∀ x, 0 < len x → ∀ b w, b :: w ∈ W x ↔ w ∈ W (child x b)
  /-- One step of the reduction shortens witnesses by one bit. -/
  len_child : ∀ x, 0 < len x → ∀ b, len (child x b) = len x - 1
  /-- One step of the reduction does not lengthen the encoded instance. -/
  length_child_le : ∀ x, 0 < len x → ∀ b, (enc (child x b)).length ≤ (enc x).length
  /-- The witness length is polynomial-time, in unary. -/
  len_polytime : ComputableInPolyTime len enc encUnary
  /-- The reduction step is polynomial-time. -/
  child_polytime :
    ComputableInPolyTime (fun p : α × Bool => child p.1 p.2) (encPair enc encBool) enc
  /-- Membership of the empty word is polynomial-time; it decides the base case `len x = 0`. -/
  nil_mem_polytime : ComputableInPolyTime (fun x => decide ([] ∈ W x)) enc encBool

namespace SelfReducible

variable {enc : α ↪ List Bool} {W : α → Finset (List Bool)} (R : SelfReducible enc W)
include R

/-- The witnesses of `x` beginning with `b` are counted by `child x b`. -/
theorem card_filter_head {x : α} (hx : 0 < R.len x) (b : Bool) :
    ((W x).filter (fun w => w.head? = some b)).card = (W (R.child x b)).card := by
  refine Finset.card_bij' (fun w _ => w.tail) (fun w _ => b :: w) ?_ ?_ ?_ ?_
  · intro w hw
    rw [Finset.mem_filter] at hw
    obtain ⟨hw, hhead⟩ := hw
    cases w with
    | nil => simp at hhead
    | cons c w =>
      simp only [List.head?_cons, Option.some.injEq] at hhead
      subst hhead
      exact (R.cons_mem_iff x hx c w).1 hw
  · intro w hw
    exact Finset.mem_filter.2 ⟨(R.cons_mem_iff x hx b w).2 hw, rfl⟩
  · intro w hw
    rw [Finset.mem_filter] at hw
    cases w with
    | nil => simp at hw
    | cons c w =>
      simp only [List.head?_cons, Option.some.injEq] at hw
      simp [hw.2]
  · intro w _
    rfl

/-- **Self-reducibility splits the count**: for `len x > 0`,
`|W x| = |W (child x false)| + |W (child x true)|`. -/
theorem card_eq_add {x : α} (hx : 0 < R.len x) :
    (W x).card = (W (R.child x false)).card + (W (R.child x true)).card := by
  rw [← R.card_filter_head hx false, ← R.card_filter_head hx true,
    ← Finset.card_filter_add_card_filter_not (s := W x) (fun w => w.head? = some false)]
  congr 1
  refine congrArg Finset.card (Finset.filter_congr fun w hw => ?_)
  have hlen := R.length_eq x w hw
  cases w with
  | nil => simp at hlen; omega
  | cons c w => cases c <;> simp

/-- At witness length `0` the only possible witness is the empty word. -/
theorem subset_singleton_nil {x : α} (hx : R.len x = 0) : W x ⊆ {[]} := by
  intro w hw
  rw [Finset.mem_singleton, ← List.length_eq_zero_iff, R.length_eq x w hw, hx]

/-- At witness length `0` a family with a witness is exactly `{[]}`. -/
theorem eq_singleton_nil {x : α} (hx : R.len x = 0) (hW : 0 < (W x).card) : W x = {[]} :=
  (Finset.subset_singleton_iff.1 (R.subset_singleton_nil hx)).resolve_left
    (Finset.card_pos.1 hW).ne_empty

/-- An instance without witnesses has children without witnesses. -/
theorem card_child_eq_zero {x : α} (hx : 0 < R.len x) (h : (W x).card = 0) (b : Bool) :
    (W (R.child x b)).card = 0 := by
  have := R.card_eq_add hx
  cases b <;> omega

end SelfReducible

end Cslib.Complexity
