/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
public import CslibFrontier.Computability.Machines.Turing.MultiTape.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Polynomial-time membership tests

Reduction maps and verifiers test membership as they are written on paper, for example keeping
the pairs `(u, v)` with `(u, v) ∉ G.2`. `fun_prop` already certifies `decide` of conjunctions,
disjunctions, equalities and disequalities
(`Turing.MultiTapeTM.ComputableTidilyInPolyTime.decide_and` and its neighbours). This file adds
negation and membership of a computed value in a computed list, so such tests need no rewriting
into Boolean operations before `fun_prop` or `polytime` runs. Membership is decided by scanning
the list for an equal element (`Turing.MultiTapeTM.ComputableTidilyInPolyTime.anyWithInput`).

## Main results

* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.decide_not`: negating a decided proposition.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.decide_mem`: membership in a computed list.
-/

public section

namespace Turing.MultiTapeTM.ComputableTidilyInPolyTime

variable {γ α : Type} {encIn : γ ↪ List Bool} {encA : α ↪ List Bool}

/-- Negation of an efficiently decidable proposition uses the standard Boolean encoding. -/
@[fun_prop]
theorem decide_not {p : γ → Prop} [∀ x, Decidable (p x)]
    (h : ComputableTidilyInPolyTime (fun x => decide (p x)) encIn encBool) :
    ComputableTidilyInPolyTime (fun x => decide ¬p x) encIn encBool := by
  simpa only [Function.comp_def, _root_.decide_not] using bool_not.comp h

/-- Membership of a computed value in a computed list is decided by scanning the list for an equal
element. -/
@[fun_prop]
theorem decide_mem {list : γ → List α} {value : γ → α} [∀ x, Decidable (value x ∈ list x)]
    (hlist : ComputableTidilyInPolyTime list encIn (encList encA))
    (hvalue : ComputableTidilyInPolyTime value encIn encA) :
    ComputableTidilyInPolyTime (fun x => decide (value x ∈ list x)) encIn encBool := by
  classical
  have hscan (x : γ) : decide (value x ∈ list x) = (list x).any fun b => decide (b = value x) := by
    rw [Bool.eq_iff_iff, decide_eq_true_eq, List.any_eq_true]
    exact ⟨fun h => ⟨_, h, decide_eq_true rfl⟩, fun ⟨b, hb, e⟩ => of_decide_eq_true e ▸ hb⟩
  simp only [hscan]
  exact anyWithInput (test := fun x b => decide (b = value x)) hlist
    (decide_eq' (snd _ _) (hvalue.comp (fst _ _)))

end Turing.MultiTapeTM.ComputableTidilyInPolyTime

/-! ### Plain polynomial-time automation -/

namespace Turing.MultiTapeTM.ComputableInPolyTime

/-- Membership of a computed value in a computed list is decided by scanning the list for an equal
element. -/
@[fun_prop]
theorem decide_mem {γ : Type}
    {α : Type}
    {encIn : γ ↪ List Bool}
    {encA : α ↪ List Bool}
    {list : γ → List α}
    {value : γ → α}
    [_inst6 : (x : γ) → Decidable (value x ∈ list x)]
    (hlist : ComputableInPolyTime list encIn (encList encA))
    (hvalue : ComputableInPolyTime value encIn encA) :
    ComputableInPolyTime
  (fun (x : γ) => Decidable.decide (value x ∈ list x)) encIn encBool :=
  .of_tidy (@Turing.MultiTapeTM.ComputableTidilyInPolyTime.decide_mem γ α encIn encA list value
      _inst6 hlist.tidy hvalue.tidy)

/-- Negation of an efficiently decidable proposition uses the standard Boolean encoding. -/
@[fun_prop]
theorem decide_not {γ : Type}
    {encIn : γ ↪ List Bool}
    {p : γ → Prop}
    [_inst3 : (x : γ) → Decidable (p x)]
    (h : ComputableInPolyTime (fun (x : γ) => Decidable.decide (p x)) encIn
  encBool) :
    ComputableInPolyTime (fun (x : γ) => Decidable.decide ¬p x) encIn
  encBool :=
  .of_tidy (@Turing.MultiTapeTM.ComputableTidilyInPolyTime.decide_not γ encIn p _inst3 h.tidy)

end Turing.MultiTapeTM.ComputableInPolyTime
