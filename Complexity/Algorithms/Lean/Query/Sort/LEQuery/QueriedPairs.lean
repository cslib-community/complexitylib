/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Cslib.Algorithms.Lean.Query.Sort.LEQuery

/-!
# The comparisons made along an oracle's path

`Cslib.Query.LEQuery.queriedPairs oracle p` lists, in order, the pairs `(a, b)` that the
comparison program `p : FreeM (LEQuery α) γ` asks about (`a ≤ b`?) along the path that `oracle`
determines. It has exactly `p.countQueries oracle` entries, and two oracles that answer these
comparisons alike drive `p` along the same path, so they make the same comparisons and lead to the
same result. These facts are the bookkeeping behind adversary and fooling arguments for
comparison lower bounds.

## Main definitions

* `Cslib.Query.LEQuery.queriedPairs`: the comparisons made along an oracle's path.

## Main results

* `Cslib.Query.LEQuery.length_queriedPairs`: one entry per comparison.
* `Cslib.Query.LEQuery.queriedPairs_eq_of_agree`, `Cslib.Query.LEQuery.eval_eq_of_agree`: two
  oracles that answer the comparisons along the first one's path alike make the same comparisons
  and produce the same result.
-/

public section

namespace Cslib.Query

variable {α γ : Type}

/-- The pairs `(a, b)` compared (`a ≤ b`?) along the path of `p` that `oracle` determines, in
order. -/
def LEQuery.queriedPairs (oracle : {ι : Type} → LEQuery α ι → ι) :
    FreeM (LEQuery α) γ → List (α × α)
  | .pure _ => []
  | .liftBind (.le a b) cont => (a, b) :: LEQuery.queriedPairs oracle (cont (oracle (.le a b)))

@[simp] theorem LEQuery.queriedPairs_pure (oracle : {ι : Type} → LEQuery α ι → ι) (x : γ) :
    LEQuery.queriedPairs oracle (pure x : FreeM (LEQuery α) γ) = [] := by
  rw [LEQuery.queriedPairs.eq_def]; rfl

@[simp] theorem LEQuery.queriedPairs_liftBind (oracle : {ι : Type} → LEQuery α ι → ι) (a b : α)
    (cont : Bool → FreeM (LEQuery α) γ) :
    LEQuery.queriedPairs oracle (FreeM.lift (.le a b) >>= cont) =
      (a, b) :: LEQuery.queriedPairs oracle (cont (oracle (.le a b))) := by
  rw [LEQuery.queriedPairs.eq_def]; rfl

/-- One entry per comparison: the list of compared pairs has length `p.countQueries oracle`. -/
@[simp] theorem LEQuery.length_queriedPairs (oracle : {ι : Type} → LEQuery α ι → ι)
    (p : FreeM (LEQuery α) γ) :
    (LEQuery.queriedPairs oracle p).length = p.countQueries oracle := by
  induction p with
  | pure x => rfl
  | lift_bind op cont ih =>
    cases op with
    | le a b =>
      change ((a, b) :: LEQuery.queriedPairs oracle (cont (oracle (.le a b)))).length =
        (FreeM.lift (.le a b) >>= cont).countQueries oracle
      rw [FreeM.countQueries_liftBind, List.length_cons, ih, Nat.add_comm]

/-- If `oracle'` answers every comparison along `oracle`'s path of `p` as `oracle` does, then it
drives `p` along the same path and makes the same comparisons. -/
theorem LEQuery.queriedPairs_eq_of_agree (oracle oracle' : {ι : Type} → LEQuery α ι → ι)
    (p : FreeM (LEQuery α) γ)
    (hagree : ∀ a b, (a, b) ∈ LEQuery.queriedPairs oracle p →
      oracle (.le a b) = oracle' (.le a b)) :
    LEQuery.queriedPairs oracle' p = LEQuery.queriedPairs oracle p := by
  induction p with
  | pure x => rfl
  | lift_bind op cont ih =>
    cases op with
    | le a b =>
      change (a, b) :: LEQuery.queriedPairs oracle' (cont (oracle' (.le a b))) =
        (a, b) :: LEQuery.queriedPairs oracle (cont (oracle (.le a b)))
      have hab := hagree a b (List.mem_cons_self ..)
      rw [← hab, ih _ fun c d hcd => hagree c d (List.mem_cons_of_mem _ hcd)]

/-- If `oracle'` answers every comparison along `oracle`'s path of `p` as `oracle` does, then `p`
evaluates to the same result under both. -/
theorem LEQuery.eval_eq_of_agree (oracle oracle' : {ι : Type} → LEQuery α ι → ι)
    (p : FreeM (LEQuery α) γ)
    (hagree : ∀ a b, (a, b) ∈ LEQuery.queriedPairs oracle p →
      oracle (.le a b) = oracle' (.le a b)) :
    p.eval oracle' = p.eval oracle := by
  induction p with
  | pure x => rfl
  | lift_bind op cont ih =>
    cases op with
    | le a b =>
      change (FreeM.lift (.le a b) >>= cont).eval oracle' =
        (FreeM.lift (.le a b) >>= cont).eval oracle
      have hab := hagree a b (List.mem_cons_self ..)
      rw [FreeM.eval_liftBind, FreeM.eval_liftBind, ← hab]
      exact ih _ fun c d hcd => hagree c d (List.mem_cons_of_mem _ hcd)

end Cslib.Query
