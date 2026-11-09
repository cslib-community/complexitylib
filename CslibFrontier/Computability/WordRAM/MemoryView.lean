/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WordRAM.ListArray
public import Mathlib.Data.Set.Function

/-!
# Keeping semantic memory views through frames

The existing finite-footprint assertions and block/list representations transport along ordinary
`Set.EqOn` frames. The frame may cover more than the live view: unused cells need not have a
specified value. Compose frames with `Set.EqOn.trans`; `Modifies.eqOn` connects finite write
footprints to the same interface. None of these rules requires initialization or disjointness
between read-only views.

## Main results

* `HeapAssertion.keep`: retain an assertion whose footprint lies inside an equality frame.
* `Block.Realizes.keep`, `Block.HoldsList.keep`: retain exact array and list readback.
* `Modifies.eqOn`: reads disjoint from the permitted writes agree.
* `ram_keep h using hf`: apply a keep rule and check interval containment with `omega`.
-/

public section

namespace Cslib.WordRAM

/-- A write frame agrees on every set disjoint from its permitted writes. -/
theorem Modifies.eqOn {writes : Finset ℕ} {before after : ℕ → ℕ} {reads : Set ℕ}
    (h : Modifies writes before after) (hd : Disjoint reads (writes : Set ℕ)) :
    Set.EqOn after before reads :=
  fun _ ha => h _ (fun hw => Set.disjoint_left.mp hd ha hw)

/-- An equality frame retains every assertion whose finite support it covers. Read-only views
may overlap; only the required equality on their live cells matters. -/
theorem HeapAssertion.keep {P : HeapAssertion} {before after : ℕ → ℕ} {reads : Set ℕ}
    (h : P.holds before) (hf : Set.EqOn after before reads)
    (hspan : (P.footprint : Set ℕ) ⊆ reads) : P.holds after :=
  P.supported (fun _ ha => (hf (hspan ha)).symm) h

/-- Exact block readback survives an equality frame containing the block. -/
theorem Block.Realizes.keep {b : Block} {before after : ℕ → ℕ}
    {values : Fin b.length → ℕ} {reads : Set ℕ}
    (h : b.Realizes before values) (hf : Set.EqOn after before reads)
    (hspan : Set.Ico b.base (b.base + b.length) ⊆ reads) : b.Realizes after values := by
  apply HeapAssertion.keep (P := HeapAssertion.array b.base b.length values) h hf
  intro a ha
  exact hspan (Block.mem_footprint.mp ha)

/-- List readback survives an equality frame containing its occupied cells. -/
theorem Block.HoldsList.keep {base : ℕ} {xs : List ℕ} {before after : ℕ → ℕ}
    {reads : Set ℕ} (h : Block.HoldsList base xs before)
    (hf : Set.EqOn after before reads)
    (hspan : Set.Ico base (base + xs.length) ⊆ reads) : Block.HoldsList base xs after :=
  Block.Realizes.keep h hf hspan

/-- Retain an existing semantic memory view using an equality frame. The tactic only discharges
containment of its support; the caller supplies the view and the actual memory frame. -/
scoped syntax (name := ramKeepFrame) "ram_keep " term " using " term : tactic

open Lean Meta Elab Tactic in
elab_rules : tactic
  | `(tactic| ram_keep $h:term using $hf:term) => withMainContext do
    let supplied ← Term.elabTerm hf none
    let (proof, frameType) ← forallTelescopeReducing (← inferType supplied) fun xs conclusion => do
      unless xs.size == 2 do
        throwError "expected a memory equality with one address and one region premise"
      let some (_, lhs, rhs) := conclusion.eq? |
        throwError "expected a memory equality"
      let predicate ← mkLambdaFVars #[xs[0]!] (← inferType xs[1]!)
      let reads ← mkAppM ``Set.ofPred #[predicate]
      let after ← mkLambdaFVars #[xs[0]!] lhs
      let before ← mkLambdaFVars #[xs[0]!] rhs
      let frameType ← mkAppM ``Set.EqOn #[after, before, reads]
      let proof ← mkLambdaFVars xs (mkAppN supplied xs)
      let .lam n domain body _ := proof | throwError "expected an address binder"
      return (Expr.lam n domain body .implicit, frameType)
    let name ← mkFreshUserName `ramKeepFrame
    let (_, goal) ← (← getMainGoal).note name proof (some frameType)
    replaceMainGoal [goal]
    let frame := mkIdent name
    let containment ← `(tactic|
      (intro a ha
       simp only [Finset.mem_coe, Block.mem_footprint, Block.Owns,
         Set.mem_ofPred_eq, Set.mem_Ico, Set.mem_Iio, Set.mem_Ici, Set.mem_union,
         Set.mem_inter_iff,
         List.length_map, List.length_reverse, List.length_nil, List.length_cons] at ha ⊢
       omega))
    evalTactic (← `(tactic| first
      | exact HeapAssertion.keep $h $frame (by $containment:tactic)
      | exact Block.HoldsList.keep $h $frame (by $containment:tactic)
      | exact Block.Realizes.keep $h $frame (by $containment:tactic)
      | exact ($h).keep $frame (by $containment:tactic) (by $containment:tactic)))

/-- Retain a block or list through one actual store outside its occupied interval. This uses
`Block.Realizes.update_of_not_owns`; the dirty cell's stored value is unrestricted. -/
scoped syntax (name := ramKeepStores) "ram_keep " term : tactic

macro_rules
  | `(tactic| ram_keep $h:term) => `(tactic| first
    | exact $h
    | exact Block.Realizes.update_of_not_owns (by ram_keep $h) (by
        intro ha
        simp only [Block.Owns, List.length_map, List.length_reverse,
          List.length_append, List.length_singleton, List.length_nil, List.length_cons] at ha
        omega) _)

end Cslib.WordRAM
