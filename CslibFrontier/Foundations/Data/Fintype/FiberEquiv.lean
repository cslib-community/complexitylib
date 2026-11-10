/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/SetTheory/Cardinal/Finite.lean`, which has `Nat.card`
-- and imports `Equiv.ofFiberEquiv` and `Fintype.card`)

public import CslibFrontier.Init
public import Mathlib.Data.Fintype.Card
public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.SetTheory.Cardinal.NatCard

/-!
# Label-preserving bijections and fiber cardinalities

Two labelings `f : α → γ` and `g : β → γ` of finite types are related by a label-preserving
bijection `e : α ≃ β`, `g (e a) = f a`, exactly when every label is used equally often:
the fibers of `f` and `g` have the same cardinality, or equivalently the multisets of labels
`univ.val.map f` and `univ.val.map g` agree. Mathlib builds the bijection from fiberwise ones
(`Equiv.ofFiberEquiv`); this file records the resulting characterization.

## Main results

* `Equiv.exists_apply_eq_iff_card_fiber_eq`: a label-preserving bijection exists exactly when all
  fibers have equal cardinality.
* `Equiv.exists_apply_eq_iff_map_univ_eq`: the same condition as an equation of label multisets.
* `Multiset.count_map_univ`: the multiplicity of a label is the cardinality of its fiber.
* `Multiset.map_univ_eq_iff_card_fiber_eq`: the label multiset of `f` is a given multiset `s`
  exactly when every element of `s` labels as many points as its multiplicity and every label of
  `f` occurs in `s`.
-/

public section

variable {α β γ : Type*}

namespace Equiv

/-- **Label-preserving bijections.** Labelings `f : α → γ` and `g : β → γ` of finite types are
related by a bijection `e` with `g (e a) = f a` exactly when every label `c` is the label of equally
many points of `α` and of `β`. -/
theorem exists_apply_eq_iff_card_fiber_eq [Finite α] [Finite β] {f : α → γ} {g : β → γ} :
    (∃ e : α ≃ β, ∀ a, g (e a) = f a) ↔
      ∀ c, Nat.card {a // f a = c} = Nat.card {b // g b = c} := by
  refine ⟨fun ⟨e, he⟩ c => Nat.card_congr (e.subtypeEquiv fun a => by rw [he]), fun h => ?_⟩
  exact ⟨ofFiberEquiv fun c => (Finite.card_eq.1 (h c)).some, ofFiberEquiv_map _⟩

end Equiv

namespace Multiset

/-- In the multiset of labels of `f : α → γ` on a finite type, the multiplicity of a label is the
number of points carrying it. -/
theorem count_map_univ [Fintype α] [DecidableEq γ] (f : α → γ) (c : γ) :
    (Finset.univ.val.map f).count c = Nat.card {a // f a = c} := by
  rw [Multiset.count_map, Nat.card_eq_fintype_card, Fintype.card_subtype]
  simp only [eq_comm (a := c)]
  rfl

/-- The multiset of labels of `f : α → γ` on a finite type is `s` exactly when every element `c`
of `s` labels as many points as its multiplicity in `s`, and every label of `f` lies in `s`. -/
theorem map_univ_eq_iff_card_fiber_eq [Fintype α] [DecidableEq γ] {f : α → γ}
    {s : Multiset γ} :
    Finset.univ.val.map f = s ↔
      (∀ c ∈ s, Nat.card {a // f a = c} = s.count c) ∧ ∀ a, f a ∈ s := by
  constructor
  · rintro rfl
    exact ⟨fun c _ => (count_map_univ f c).symm,
      fun a => mem_map_of_mem f (Finset.mem_univ_val a)⟩
  · rintro ⟨hs, hf⟩
    refine ext.2 fun c => ?_
    rw [count_map_univ]
    by_cases hc : c ∈ s
    · exact hs c hc
    · rw [count_eq_zero.2 hc, Nat.card_eq_zero]
      exact Or.inl ⟨fun ⟨a, ha⟩ => hc (ha ▸ hf a)⟩

end Multiset

namespace Equiv

/-- **Label-preserving bijections, multiset form.** Labelings `f : α → γ` and `g : β → γ` of finite
types are related by a bijection `e` with `g (e a) = f a` exactly when they have the same multiset
of labels. -/
theorem exists_apply_eq_iff_map_univ_eq [Fintype α] [Fintype β] {f : α → γ} {g : β → γ} :
    (∃ e : α ≃ β, ∀ a, g (e a) = f a) ↔
      Finset.univ.val.map f = Finset.univ.val.map g := by
  classical
  rw [exists_apply_eq_iff_card_fiber_eq, Multiset.ext]
  simp only [Multiset.count_map_univ]

end Equiv
