/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Cslib.Algorithms.Lean.Query.FreeM
public import Mathlib.Algebra.Group.Hom.Defs

/-!
# Changing the cost monoid of a query program

`FreeM.cost oracle weight p` adds up the weights of the queries along the path of `p` under
`oracle`. An additive monoid homomorphism `f : T →+ T'` commutes with this sum: `f` of the cost
with weights `weight` is the cost with weights `f ∘ weight`. For example, with
`f = Nat.castAddMonoidHom ℝ`, an exact natural-number cost transfers to a real-valued cost bound.

## Main results

* `Cslib.FreeM.map_cost`: `f (p.cost oracle weight) = p.cost oracle (f ∘ weight)`.
-/

public section

namespace Cslib.FreeM

universe u v t w x

variable {F : Type u → Type v} {α : Type u}

/-- An additive monoid homomorphism commutes with the weighted query cost. -/
theorem map_cost {T : Type t} {T' : Type w} {G : Type x} [AddMonoid T] [AddMonoid T']
    [FunLike G T T'] [AddMonoidHomClass G T T'] (f : G) (oracle : {ι : Type u} → F ι → ι)
    (weight : {ι : Type u} → F ι → T) (p : FreeM F α) :
    f (p.cost oracle weight) = p.cost oracle (fun q => f (weight q)) := by
  induction p with
  | pure a => rw [cost_pure, cost_pure, map_zero]
  | lift_bind op cont ih =>
    change f ((FreeM.lift op >>= cont).cost oracle weight) =
      (FreeM.lift op >>= cont).cost oracle (fun q => f (weight q))
    rw [cost_liftBind, cost_liftBind, map_add, ih]

end Cslib.FreeM
