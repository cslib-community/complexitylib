/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Combinatorics.MajorityTree
public import CslibFrontier.Foundations.Data.Code.LocalListDecoding
public import Mathlib.Data.Fintype.BigOperators

/-!
# Self-correction of Reed–Muller codes by interpolation along lines

A received word `w` that differs from a Reed–Muller codeword `p` of degree `d` on few points can
be corrected by reading `w` at `d + 1` points `x + ν i • v` of a line through `x`, for fixed
distinct nonzero nodes `ν i`, and interpolating: `p x = ∑ i, λ i * p (x + ν i • v)` for the
Lagrange weights `λ i` of the nodes at `0` (`Cslib.Code.lagrangeDecode_eq_of_mem_reedMuller`). Each
queried point is uniformly distributed over the directions `v`, so at every point `x` at most
`(d + 1) * Δ(w, p)` directions make the step err (`Cslib.Code.card_lagrangeDecode_ne_le`)
[Arora and Barak, Chapter 19][AroraBarak09]. Combined with ternary majority trees
(`Cslib.majTree`, `Cslib.exists_forall_majTree_eq`), this corrects `w` everywhere on a bounded set
with fixed directions.

## Main definitions

* `Cslib.Code.lagrangeWeight`, `Cslib.Code.lagrangeDecode`: interpolation along a line.

## Main results

* `Cslib.Code.lagrangeDecode_eq_of_mem_reedMuller`: interpolation is exact on codewords.
* `Cslib.Code.card_lagrangeDecode_ne_le`: few directions err.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09], Chapter 19
-/

@[expose] public section

namespace Cslib.Code

open Finset Polynomial

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d : ℕ}

/-- The Lagrange weight of the node `ν i` at `0`. -/
noncomputable def lagrangeWeight (ν : Fin (d + 1) ↪ F) (i : Fin (d + 1)) : F :=
  (Lagrange.basis univ ν i).eval 0

omit [Fintype F] [DecidableEq F] in
/-- A polynomial of degree at most `d` is determined at `0` by its values at `d + 1` nodes. -/
theorem eval_zero_eq_sum_lagrangeWeight (ν : Fin (d + 1) ↪ F) {P : F[X]}
    (hP : P.natDegree ≤ d) : P.eval 0 = ∑ i, lagrangeWeight ν i * P.eval (ν i) := by
  have hdeg : P.degree < #(univ : Finset (Fin (d + 1))) := by
    rw [card_univ, Fintype.card_fin]
    exact degree_le_natDegree.trans_lt (by exact_mod_cast Nat.lt_succ_of_le hP)
  conv_lhs => rw [Lagrange.eq_interpolate (s := univ) (v := ν) (ν.injective.injOn) hdeg]
  rw [Lagrange.interpolate_apply, eval_finsetSum]
  refine sum_congr rfl fun i _ => ?_
  rw [eval_mul, eval_C, lagrangeWeight, mul_comm]

/-- **Interpolation along a line**: the combination of the values of `w` at the points
`x + ν i • v` with the Lagrange weights at `0`. -/
noncomputable def lagrangeDecode (ν : Fin (d + 1) ↪ F) (w : (Fin m → F) → F)
    (x v : Fin m → F) : F :=
  ∑ i, lagrangeWeight ν i * w (x + ν i • v)

omit [Fintype F] [DecidableEq F] in
/-- **Interpolation is exact on codewords** of the Reed–Muller code of degree `d`, for every
direction. -/
theorem lagrangeDecode_eq_of_mem_reedMuller (ν : Fin (d + 1) ↪ F) {p : (Fin m → F) → F}
    (hp : p ∈ reedMuller F m d) (x v : Fin m → F) : lagrangeDecode ν p x v = p x := by
  obtain ⟨P, hP, hPeval⟩ := exists_natDegree_le_eval_eq_of_mem_reedMuller hp x v
  have hx : p x = P.eval 0 := by rw [hPeval, zero_smul, add_zero]
  rw [lagrangeDecode, hx, eval_zero_eq_sum_lagrangeWeight ν hP]
  simp only [hPeval]

/-- **Few directions err.** At every point `x`, at most `(d + 1) * Δ(w, p)` directions `v` make
interpolation along the line through `x` in the direction `v` err, when the nodes are nonzero. -/
theorem card_lagrangeDecode_ne_le (ν : Fin (d + 1) ↪ F) (hν : ∀ i, ν i ≠ 0)
    {p : (Fin m → F) → F} (hp : p ∈ reedMuller F m d) (w : (Fin m → F) → F) (x : Fin m → F) :
    #{v | lagrangeDecode ν w x v ≠ p x} ≤ (d + 1) * #{y | w y ≠ p y} := by
  set E : Finset (Fin m → F) := {y | w y ≠ p y}
  have hsub : ({v | lagrangeDecode ν w x v ≠ p x} : Finset (Fin m → F)) ⊆
      univ.biUnion fun i => univ.filter fun v => x + ν i • v ∈ E := by
    intro v hv
    rw [mem_filter] at hv
    by_contra hnot
    simp only [mem_biUnion, mem_univ, true_and, mem_filter, not_exists, E, ne_eq,
      not_not] at hnot
    refine hv.2 ((sum_congr rfl fun i _ => ?_).trans (lagrangeDecode_eq_of_mem_reedMuller ν hp x v))
    rw [hnot i]
  refine (card_le_card hsub).trans ((card_biUnion_le).trans ?_)
  calc ∑ i, #(univ.filter fun v => x + ν i • v ∈ E) ≤ ∑ _i : Fin (d + 1), #E :=
        sum_le_sum fun i _ => card_le_card_of_injOn (fun v => x + ν i • v)
          (fun v hv => by simpa using hv)
          (fun v _ v' _ h => smul_right_injective _ (hν i) (add_left_cancel h))
    _ = (d + 1) * #E := by rw [sum_const, card_univ, Fintype.card_fin, smul_eq_mul]

end Cslib.Code
