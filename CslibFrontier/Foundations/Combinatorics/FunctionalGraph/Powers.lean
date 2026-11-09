/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Combinatorics.FunctionalGraph
public import Mathlib.Algebra.GCDMonoid.Finset
public import Mathlib.Algebra.GCDMonoid.Nat
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# The number of distinct powers of a finite map

For `f : α → α` on a finite type, let `μ` be the longest transient depth (`maxTransientDepth`)
and `λ` the least common multiple of the cycle lengths (`cyclePeriod`). Two powers `f^[a]` and
`f^[b]` with `a < b` agree exactly when `μ ≤ a` and `λ ∣ b - a` (`iterate_eq_iterate_iff`), so
`f` has exactly `μ + λ` distinct powers (`card_range_iterate`). On an empty type `μ = 0` and
`λ = 1`: the only power is the empty function.

## Main definitions

* `Cslib.FunctionalGraph.maxTransientDepth`: the longest transient depth `μ`.
* `Cslib.FunctionalGraph.cyclePeriod`: the least common multiple `λ` of the cycle lengths.

## Main results

* `Cslib.FunctionalGraph.iterate_eq_iterate_iff`: when two powers agree.
* `Cslib.FunctionalGraph.iterate_eq_iterate_reduce`: every power is one of the first `μ + λ`.
* `Cslib.FunctionalGraph.card_range_iterate`: exactly `μ + λ` distinct powers.

## References

* Adapted from lean/Proofs/NumberOfPowers.lean in
  [S. Schlesinger,
  *Square-root circuit bounds for iterated functions*][Schlesinger2026IteratedFunctions].
-/

@[expose] public section

namespace Cslib.FunctionalGraph

universe u
variable {α : Type u} [Fintype α] (f : α → α)


/-- The longest transient depth `μ` over all states. -/
noncomputable def maxTransientDepth : ℕ := Finset.univ.sup (transientDepth f)

/-- The least common multiple `λ` of all cycle lengths. -/
noncomputable def cyclePeriod : ℕ := Finset.univ.lcm (cycleLength f)

/-- The least common multiple of all cycle lengths is positive. -/
theorem cyclePeriod_pos : 0 < cyclePeriod f := by
  apply Nat.pos_of_ne_zero
  intro h
  obtain ⟨x, _, hx⟩ := Finset.lcm_eq_zero_iff.mp h
  exact (cycleLength_pos f x).ne' hx

/-- Two powers `f^[a]` and `f^[b]` with `a < b` coincide iff `μ ≤ a` and `λ ∣ b - a`. -/
theorem iterate_eq_iterate_iff {a b : ℕ} (hab : a < b) :
    f^[a] = f^[b] ↔ maxTransientDepth f ≤ a ∧ cyclePeriod f ∣ b - a := by
  rw [funext_iff]
  simp only [iterate_apply_eq_iterate_apply_iff f _ hab, maxTransientDepth, cyclePeriod,
    Finset.sup_le_iff, Finset.lcm_dvd_iff, Finset.mem_univ, true_implies]
  exact forall_and

/-- Every power past `μ` reduces to one of the first `μ + λ` powers. -/
theorem iterate_eq_iterate_reduce {T : ℕ} (hT : maxTransientDepth f ≤ T) :
    f^[T] = f^[maxTransientDepth f + (T - maxTransientDepth f) % cyclePeriod f] := by
  set μ := maxTransientDepth f
  set p := cyclePeriod f
  have hdiv := Nat.div_add_mod (T - μ) p
  have hle : μ + (T - μ) % p ≤ T := by
    have := Nat.mod_le (T - μ) p
    lia
  rcases hle.lt_or_eq with hlt | heq
  · refine ((iterate_eq_iterate_iff f hlt).mpr ⟨by lia, ?_⟩).symm
    exact ⟨(T - μ) / p, by lia⟩
  · rw [heq]

/-- The powers `f^[0], …, f^[μ + λ - 1]` are pairwise distinct. -/
theorem iterate_injective_below :
    Function.Injective
      (fun i : Fin (maxTransientDepth f + cyclePeriod f) => f^[i.val]) := by
  intro i j h
  by_contra hne
  have key (i j : Fin (maxTransientDepth f + cyclePeriod f)) (hij : i.val < j.val)
      (h : f^[i.val] = f^[j.val]) : False := by
    obtain ⟨hμ, hd⟩ := (iterate_eq_iterate_iff f hij).mp h
    have := Nat.le_of_dvd (by lia) hd
    have := j.isLt
    lia
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hij | hji
  · exact key i j hij h
  · exact key j i hji h.symm

/-- **The number of powers.**  A map on a finite type has exactly `μ + λ` distinct powers. -/
theorem card_range_iterate :
    Nat.card (Set.range fun T : ℕ => f^[T]) = maxTransientDepth f + cyclePeriod f := by
  have hrange : Set.range (fun T : ℕ => f^[T]) =
      Set.range (fun i : Fin (maxTransientDepth f + cyclePeriod f) => f^[i.val]) := by
    ext g
    constructor
    · rintro ⟨T, rfl⟩
      by_cases hT : T < maxTransientDepth f + cyclePeriod f
      · exact ⟨⟨T, hT⟩, rfl⟩
      · have hm := Nat.mod_lt (T - maxTransientDepth f) (cyclePeriod_pos f)
        exact ⟨⟨_, by lia⟩, (iterate_eq_iterate_reduce f (by lia)).symm⟩
    · rintro ⟨i, rfl⟩
      exact ⟨i.val, rfl⟩
  rw [hrange, Nat.card_range_of_injective (iterate_injective_below f)]
  simp

end Cslib.FunctionalGraph
