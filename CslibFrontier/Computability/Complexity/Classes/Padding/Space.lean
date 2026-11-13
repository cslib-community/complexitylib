/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.Space.Basic
public import CslibFrontier.Computability.Complexity.Reduction
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.Bounds
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Frame
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.PolynomialPadding
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.OCombinators
import CslibFrontier.Foundations.Data.Nat.AffineBound
import Mathlib.Tactic.Linarith

/-!
# Polynomial padding for deterministic space

The padded language of `A` with exponent `k` consists of the words `x` carrying a word
`y = unframe x` framed at their start, with `(y.length + 1) ^ k ≤ x.length` and `y ∈ A`
(`Cslib.Complexity.spacePadded`). If `A` is in deterministic space `O((n + 1) ^ (b * k))`, then
its padded language is in deterministic space `O((n + 1) ^ b)`
(`Cslib.Complexity.spacePadded_mem_DSPACE`). The decider tests the padding in linear space
(`Turing.MultiTapeTM.computableInO_polynomialPaddingGuard`). When the test passes, it writes `y`
and decides it within space `O((|y| + 1) ^ (b * k)) ≤ O(|x| ^ b)`. Otherwise it rejects. The
padding map `y ↦ frame y ++ 1^((|y| + 1) ^ k)` is computable in polynomial time
(`Cslib.Complexity.polyTimeReducible_spacePadded`), so every problem reduces to its padded
language.

Space is measured by visited work cells, as in `Cslib.Complexity.DSPACE`. The bridges between
`DSPACE` and the quantitative calculus `Turing.MultiTapeTM.ComputableInO`
(`Cslib.Complexity.computableInO_indicator_of_mem_DSPACE`,
`Cslib.Complexity.setOf_mem_DSPACE_of_computableInO`) are the space counterparts of the `DTIME`
ones in `CslibFrontier.Computability.Complexity.Classes.Time`.

This is the padding technique of [Arora and Barak, §2.6.2][AroraBarak07] for space. With the space
hierarchy theorem it shows that `DSPACE n` is not closed under polynomial-time reductions
(`CslibFrontier.Computability.Complexity.Classes.Space.Separation`).

## Main definitions

* `Cslib.Complexity.spacePadded`: the polynomially padded language.

## Main results

* `Cslib.Complexity.computableInO_indicator_of_mem_DSPACE`,
  `Cslib.Complexity.setOf_mem_DSPACE_of_computableInO`: `DSPACE` in the quantitative calculus.
* `Cslib.Complexity.spacePadded_mem_DSPACE`: padding into deterministic space.
* `Cslib.Complexity.polyTimeReducible_spacePadded`: every problem reduces to its padded language.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, web draft of January
  2007][AroraBarak07]
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

variable {α : Type} {enc : α ↪ List Bool}

/-- A problem in `DSPACE enc s` is decided by a machine computing its indicator within some time
and within space `O(s n)`, on instances whose encoding has length `n`. -/
theorem computableInO_indicator_of_mem_DSPACE {A : Set α} {s : ℕ → ℕ}
    (h : A ∈ DSPACE enc s) :
    ∃ T : α → ℕ, ComputableInO (indicator A) enc encBool T fun a => s (enc a).length := by
  obtain ⟨c₁, c₂, t, hA⟩ := h
  refine ⟨fun a => t (enc a).length, .of_bounds hA (c₁ + c₂ + 1) (fun a => ?_) (fun a => ?_)
    fun a => ?_⟩
  · nlinarith
  · nlinarith
  · simp only [encBool_apply, List.length_singleton]
    nlinarith

/-- A Boolean function, computable within a space bound of the length of the encoded instance,
decides a problem within that space. -/
theorem setOf_mem_DSPACE_of_computableInO {f : α → Bool} {T S : α → ℕ} {s : ℕ → ℕ}
    (h : ComputableInO f enc encBool T S) (hS : ∀ a, S a ≤ s (enc a).length) :
    {a | f a = true} ∈ DSPACE enc s := by
  obtain ⟨c, hc, -⟩ := h
  refine mem_DSPACE_iff.mpr ⟨c, c, fun a => c * (T a + 1),
    decidableInTimeAndSpace_iff.mpr ⟨f, hc.mono (fun _ => le_rfl) fun a => ?_, fun _ => Iff.rfl⟩⟩
  have := Nat.mul_le_mul_left c (hS a)
  rw [Nat.mul_add, Nat.mul_one]
  omega

/-- The language `A` padded with exponent `k`: the words `x` carrying a word `y = unframe x` of `A`
framed at their start, of length at least `(y.length + 1) ^ k`. -/
def spacePadded (A : Set (List Bool)) (k : ℕ) : Set (List Bool) :=
  {x | ((unframe x).length + 1) ^ k ≤ x.length ∧ unframe x ∈ A}

/-- The padded word `frame y ++ 1^((|y| + 1) ^ k)` is in the padded language exactly when `y ∈ A`.
-/
theorem frame_append_replicate_mem_spacePadded_iff {A : Set (List Bool)} {k : ℕ}
    (y : List Bool) :
    frame y ++ List.replicate ((y.length + 1) ^ k) true ∈ spacePadded A k ↔ y ∈ A := by
  simp only [spacePadded, Set.mem_ofPred_eq, unframe_frame_append, List.length_append,
    length_frame, List.length_replicate]
  exact and_iff_right (by omega)

/-- **Every problem reduces to its padded language**, by the polynomial-time padding map
`y ↦ frame y ++ 1^((|y| + 1) ^ k)`, for `k ≥ 1`. -/
theorem polyTimeReducible_spacePadded (A : Set (List Bool)) {k : ℕ} (hk : 1 ≤ k) :
    PolyTimeReducible encBits encBits A (spacePadded A k) := by
  refine ⟨_, (computableInO_polynomialPadding hk).computableInPolyTime
    ⟨fun n => (n + 1) ^ (2 * k), by fun_prop, fun _ => le_rfl⟩
    ⟨fun n => (n + 1) ^ k, by fun_prop, fun _ => le_rfl⟩, fun y => ?_⟩
  exact (frame_append_replicate_mem_spacePadded_iff y).symm

/-- **Padding into deterministic space.** If `A` is in deterministic space `O((n + 1) ^ (b * k))`,
with `1 ≤ b`, then its padded language with exponent `k` is in deterministic space
`O((n + 1) ^ b)`. -/
theorem spacePadded_mem_DSPACE {A : Set (List Bool)} {b k : ℕ} (hb : 1 ≤ b)
    (hA : A ∈ DSPACE encBits (fun n => (n + 1) ^ (b * k))) :
    spacePadded A k ∈ DSPACE encBits (fun n => (n + 1) ^ b) := by
  classical
  obtain ⟨T, hT⟩ := computableInO_indicator_of_mem_DSPACE hA
  have hunframe : ComputableInO unframe encBits encBits (fun x => x.length) fun x => x.length :=
    .of_linear (.of_unframe fun _ => rfl)
  have hdec := (computableInO_polynomialPaddingGuard k).ite (hT.comp hunframe)
    (ComputableInO.const (encIn := encBits) (encMid := encBool) false)
  have hset : spacePadded A k = {x | (if decide (((unframe x).length + 1) ^ k ≤ x.length) then
      indicator A (unframe x) else false) = true} := by
    ext x
    by_cases hg : ((unframe x).length + 1) ^ k ≤ x.length <;>
      simp [spacePadded, hg, indicator]
  rw [hset]
  refine DSPACE_mono_of_le_mul_add (s₁ := fun n => 3 * (n + 1) ^ b) (C := 3) (fun n => by omega)
    (setOf_mem_DSPACE_of_computableInO hdec fun x => ?_)
  have hlin : x.length + 1 ≤ (x.length + 1) ^ b := Nat.le_self_pow (by omega) _
  simp only [encBits_apply]
  split_ifs with hg
  · have hpad : ((unframe x).length + 1) ^ (b * k) ≤ (x.length + 1) ^ b := by
      rw [Nat.mul_comm, pow_mul]
      exact Nat.pow_le_pow_left ((of_decide_eq_true hg).trans (Nat.le_succ _)) b
    have hu := length_unframe_le x
    omega
  · omega

end Cslib.Complexity
