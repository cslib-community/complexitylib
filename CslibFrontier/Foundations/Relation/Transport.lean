/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Logic.Relation

/-!
# Transporting reflexive–transitive closure along maps

Mathlib's `Relation.ReflTransGen.lift` carries paths forward along any map. The converse needs
an injective map whose range contains every vertex reachable from the image of the source: then
paths between images pull back to paths in the domain. Bijections satisfy this automatically.

## Main results

* `Relation.reflTransGen_onFun_iff`: closure of a pulled-back relation along an injective map
  whose range contains every reachable vertex.
* `Relation.reflTransGen_equiv_iff`: closure is invariant under a bijection carrying one edge
  relation to the other.
-/

public section

namespace Relation

variable {α β : Type*}

/-- Closure of `r` pulled back along an injective map `f` is closure of `r` between images,
provided every vertex reachable from `f a` lies in the range of `f`. -/
theorem reflTransGen_onFun_iff {f : α → β} (hf : Function.Injective f) {r : β → β → Prop}
    {a b : α} (hrange : ∀ y, ReflTransGen r (f a) y → ∃ x, f x = y) :
    ReflTransGen (fun x y => r (f x) (f y)) a b ↔ ReflTransGen r (f a) (f b) := by
  refine ⟨fun h => h.lift f fun _ _ h => h, fun h => ?_⟩
  suffices ∀ y, ReflTransGen r (f a) y → ∀ x, f x = y →
      ReflTransGen (fun x y => r (f x) (f y)) a x from this _ h b rfl
  intro y hy
  induction hy with
  | refl => exact fun x hx => hf hx ▸ .refl
  | @tail c d hc hcd ih =>
    intro x hx
    obtain ⟨z, rfl⟩ := hrange c hc
    exact (ih z rfl).tail (hx ▸ hcd)

/-- Reachability is invariant under a bijection that carries one edge relation to the other. -/
theorem reflTransGen_equiv_iff (e : α ≃ β) {r : α → α → Prop} {s : β → β → Prop}
    (h : ∀ a b, r a b ↔ s (e a) (e b)) (a b : α) :
    ReflTransGen r a b ↔ ReflTransGen s (e a) (e b) := by
  have hr : r = fun x y => s (e x) (e y) := funext₂ fun x y => propext (h x y)
  subst hr
  exact reflTransGen_onFun_iff e.injective fun y _ => ⟨e.symm y, e.apply_symm_apply y⟩

end Relation
