/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.SymAnd
public import Mathlib.Data.Finset.Option

/-!
# Restricting `SYM ∘ AND` circuits

A `SYM ∘ AND` circuit on slots `T` is restricted along a partial map `ρ : T → Option ι` by reading
slot `t` from input `i` when `ρ t = some i` and fixing it to `false` when `ρ t = none`
(`Circuits.Boolean.SymAnd.restrict`). The AND gates reading a fixed slot are never satisfied, so
they are dropped; the others read the inputs their slots are sent to. The restricted circuit
computes the original one on the valuation `t ↦ (ρ t).elim false x`
(`SymAnd.eval_restrict`), and has no more AND gates (`SymAnd.size_restrict_le`) and no larger
fan-in (`SymAnd.fanIn_restrict_le`).

This turns a `SYM ∘ AND` circuit reading all the slots of a modular tower
(`SymAnd.exists_eval_eq_eval_run`) into a circuit over the inputs alone, the other slots starting
at `false`.

## Main definitions

* `Cslib.Circuits.Boolean.SymAnd.restrict`: restriction along a partial map of slots to inputs.

## Main results

* `Cslib.Circuits.Boolean.SymAnd.eval_restrict`: what the restriction computes.
* `Cslib.Circuits.Boolean.SymAnd.size_restrict_le`, `SymAnd.fanIn_restrict_le`: restriction does
  not increase size or fan-in.
-/

public section

namespace Cslib.Circuits.Boolean

namespace SymAnd

open Finset

variable {T ι : Type*} [DecidableEq ι]

/-- The restriction of `C` along `ρ`: slot `t` reads input `i` when `ρ t = some i` and is fixed to
`false` when `ρ t = none`. AND gates reading a fixed slot are dropped. -/
@[expose] def restrict (C : SymAnd T) (ρ : T → Option ι) : SymAnd ι :=
  ⟨(C.gates.filter fun S => ∀ t ∈ S, (ρ t).isSome).map fun S => S.biUnion fun t => (ρ t).toFinset,
    C.out⟩

/-- **What the restriction computes**: `C` on the valuation reading slot `t` from `x` through `ρ`,
and `false` where `ρ` is undefined. -/
theorem eval_restrict (C : SymAnd T) (ρ : T → Option ι) (x : ι → Bool) :
    (C.restrict ρ).eval x = C.eval fun t => (ρ t).elim false x := by
  simp only [eval, count, restrict]
  congr 1
  rw [Multiset.countP_map, Multiset.countP_eq_card_filter, Multiset.filter_filter]
  congr 1
  refine Multiset.filter_congr fun S _ => ?_
  constructor
  · rintro ⟨hx, hsome⟩ t ht
    obtain ⟨i, hi⟩ := Option.isSome_iff_exists.1 (hsome t ht)
    rw [hi]
    exact hx i (mem_biUnion.2 ⟨t, ht, by simp [hi]⟩)
  · intro h
    have hsome : ∀ t ∈ S, (ρ t).isSome := fun t ht => by
      have := h t ht
      cases hρ : ρ t with
      | none => rw [hρ] at this; cases this
      | some i => rfl
    refine ⟨fun i hi => ?_, hsome⟩
    obtain ⟨t, ht, hit⟩ := mem_biUnion.1 hi
    have := h t ht
    rw [Option.mem_toFinset, Option.mem_def] at hit
    rwa [hit] at this

/-- Restriction does not increase the number of AND gates. -/
theorem size_restrict_le (C : SymAnd T) (ρ : T → Option ι) : (C.restrict ρ).size ≤ C.size := by
  simp only [size, restrict, Multiset.card_map]
  exact Multiset.card_le_card (Multiset.filter_le _ _)

/-- Restriction does not increase the fan-in. -/
theorem fanIn_restrict_le (C : SymAnd T) (ρ : T → Option ι) : (C.restrict ρ).fanIn ≤ C.fanIn := by
  refine fanIn_le_iff.2 fun S' hS' => ?_
  simp only [restrict, Multiset.mem_map, Multiset.mem_filter] at hS'
  obtain ⟨S, ⟨hS, -⟩, rfl⟩ := hS'
  calc #(S.biUnion fun t => (ρ t).toFinset) ≤ #S * 1 :=
        card_biUnion_le_card_mul _ _ _ fun t _ => by
          rw [Option.card_toFinset]
          cases ρ t <;> simp
    _ = #S := mul_one _
    _ ≤ C.fanIn := card_le_fanIn hS

end SymAnd

end Cslib.Circuits.Boolean
