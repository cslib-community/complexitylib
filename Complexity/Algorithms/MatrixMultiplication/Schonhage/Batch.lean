/-
Copyright (c) 2026 Anthropic, PBC, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.MatrixMultiplication.Schonhage.Levels

/-!
# Batch correctness of the tensor product

## Main results

* `bilinearProduct_arrays_eq_mul`: exact integer matrix multiplication at selected strings.
* `batch_product_spec`: arbitrary output strings with `m` inner levels.

The batch arrays vanish on strings with the wrong number of inner positions.
The coefficient rules select equal inner indices and the specified outer row and column,
yielding the usual product of integer matrices.

## References

Adapted selectively from [AlmanWilliams2026, Section 2] and
[Anthropic's pinned formal source](https://github.com/anthropics/formal-math/tree/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/3sum-apsp/ThreeSumApsp/Sec2).
Source pin: `16a5ce41304fcdaea4e0be7c132e1c361dc26da5`. These are finite mathematical
counts and identities; they give no native program or instruction-cost certificate.
-/

@[expose] public section

open Finset

namespace Cslib.Algorithms.MatrixMultiplication.Schonhage

/-! ### Cardinalities of index types -/

/-- The outer-index type has `N0 L m` elements. -/
theorem card_outerStr (L m : ℕ) : Fintype.card (OuterStr L m) = N0 L m := by
  simp [N0]

/-- The inner-index type has `D m` elements. -/
theorem card_innerStr (m : ℕ) : Fintype.card (InnerStr m) = D m := by
  simp [D]

/-- There are `K L m` subsets of `Fin L` with cardinality `m`. -/
theorem card_subsets_eq_K (L m : ℕ) :
    (univ.filter fun Q : Finset (Fin L) => Q.card = m).card = K L m := by
  rw [univ_filter_card_eq, card_powersetCard, card_univ, Fintype.card_fin, K]

/-! ### The input arrays -/

/-- The entry of the left input array at the string with inner set `Q`, outer part `r` and inner
part `π` is `X_Q[r, π]`. -/
@[simp]
theorem arrayL_leftStrOf {L m : ℕ} (X : Finset (Fin L) → LeftMat L m) (Q : Finset (Fin L))
    (hQ : Q.card = m) (r : OuterStr L m) (π : InnerStr m) :
    arrayL m X (leftStrOf Q hQ r π) = X Q r π := by
  have h : (innerSetL (leftStrOf Q hQ r π)).card = m := by rw [innerSetL_leftStrOf, hQ]
  rw [arrayL, dite_eq_left h, outerPartL_leftStrOf, innerPartL_leftStrOf, innerSetL_leftStrOf]

/-- The entry of the right input array at the string with inner set `Q`, inner part `π` and outer
part `c` is `Y_Q[π, c]`. -/
@[simp]
theorem arrayR_rightStrOf {L m : ℕ} (Y : Finset (Fin L) → RightMat L m) (Q : Finset (Fin L))
    (hQ : Q.card = m) (π : InnerStr m) (c : OuterStr L m) :
    arrayR m Y (rightStrOf Q hQ π c) = Y Q π c := by
  have h : (innerSetR (rightStrOf Q hQ π c)).card = m := by rw [innerSetR_rightStrOf, hQ]
  rw [arrayR, dite_eq_left h, innerPartR_rightStrOf, outerPartR_rightStrOf, innerSetR_rightStrOf]

/-! ### Coefficients and batch correctness -/

/-- The inner-output coefficient selects equal inner index pairs (Section 2.3.3).
Checked directly on `coefficient`; no polynomial coefficient bridge is assumed. -/
theorem coefficient_z0 (s : LeftVar) (t : RightVar) :
    coefficient s t .z0 = if ∃ i j, s = .p i j ∧ t = .q i j then 1 else 0 := by
  decide +revert

/-- With two outer inputs, the outer-output coefficient selects exactly the matching row
and column (Section 2.3.3). -/
theorem coefficient_x_y_z (i' j' i j : Fin 3) :
    coefficient (.x i') (.y j') (.z i j) = if i' = i ∧ j' = j then 1 else 0 := by
  decide +revert

/-- The statement on `γ(x_i', y_j', z_ij)` as it is used: if `s` and `t` are outer and
`γ(s, t, z_ij) ≠ 0`, then `(s, t) = (x_i, y_j)`. -/
private theorem eq_x_y_of_gamma_ne_zero {s : LeftVar} {t : RightVar} {i j : Fin 3}
    (hs : ¬ s.IsInner) (ht : ¬ t.IsInner) (h : coefficient s t (.z i j) ≠ 0) : s = .x i ∧ t = .y j
      := by
  rcases s with i' | _
  · rcases t with j' | _
    · by_contra hne
      exact h ((coefficient_x_y_z i' j' i j).trans
        (ite_eq_right fun ⟨hi, hj⟩ => hne ⟨hi ▸ rfl, hj ▸ rfl⟩))
    · exact (ht trivial).elim
  · exact (hs trivial).elim

/-- The summands of Lemma 8 that can be nonzero. Let `w` be the output string with inner
set `Q`, row `r` and column `c`. If `γ(u_ℓ, v_ℓ, w_ℓ) ≠ 0` at every level and the inner sets of `u`
and `v` have `m` elements, then `u` has inner set `Q`, outer part `r` and some inner part `π`, and
`v` has inner set `Q`, outer part `c` and the inner part with the same indices. -/
private theorem exists_of_summand_ne_zero {L m : ℕ} (Q : Finset (Fin L)) (hQ : Q.card = m)
    (r c : OuterStr L m) {u : LeftStr L} {v : RightStr L}
    (hγ : ∀ ℓ, coefficient (u ℓ) (v ℓ) (outStrOf Q hQ r c ℓ) ≠ 0) (hu : (innerSetL u).card = m)
    (hv : (innerSetR v).card = m) : ∃ π, u = leftStrOf Q hQ r π ∧ v = rightStrOf Q hQ π c := by
  simp only [outStrOf, forall_iff_orderEmbOfFin_and_compl Q hQ, glue_orderEmbOfFin,
    glue_orderEmbOfFin_compl] at hγ
  obtain ⟨hγin, hγout⟩ := hγ
  -- at a level ℓ ∈ Q we have w_ℓ = z₀ […] So (u_ℓ, v_ℓ) = (p_ij, q_ij) for some i, j.
  have hin : ∀ k, ∃ ij : Fin 2 × Fin 2,
      u (Finset.orderEmbOfFin Q hQ k) = .p ij.1 ij.2 ∧ v (Finset.orderEmbOfFin Q hQ k) = .q ij.1
        ij.2 := fun k => by
    by_contra hne
    exact hγin k ((coefficient_z0 _ _).trans (ite_eq_right fun ⟨i, j, h⟩ => hne ⟨(i, j), h⟩))
  choose π hπ using hin
  -- Thus u and v have an inner variable at every level of Q, and their inner sets are therefore
  -- exactly Q.  So u_ℓ and v_ℓ are outer at the levels outside Q.
  have huQ : innerSetL u = Q :=
    filter_eq_of_forall_orderEmbOfFin Q hQ (fun k => by rw [(hπ k).1]; trivial) hu
  have hvQ : innerSetR v = Q :=
    filter_eq_of_forall_orderEmbOfFin Q hQ (fun k => by rw [(hπ k).2]; trivial) hv
  have huout := ((filter_eq_iff_orderEmbOfFin_and_compl Q hQ).mp huQ).2
  have hvout := ((filter_eq_iff_orderEmbOfFin_and_compl Q hQ).mp hvQ).2
  -- at a level ℓ ∉ Q we have w_ℓ = z_ij for some i, j […] so (u_ℓ, v_ℓ) = (x_i, y_j).
  have hout : ∀ k, u ((Qᶜ.orderEmbOfFin (card_compl_of_card_eq Q hQ)) k) = .x (r k) ∧ v
    ((Qᶜ.orderEmbOfFin (card_compl_of_card_eq Q hQ)) k) = .y (c k) :=
    fun k => eq_x_y_of_gamma_ne_zero (huout k) (hvout k) (hγout k)
  exact ⟨π, (eq_glue_iff Q hQ).mpr ⟨fun k => (hπ k).1, fun k => (hout k).1⟩,
    (eq_glue_iff Q hQ).mpr ⟨fun k => (hπ k).2, fun k => (hout k).2⟩⟩

/-- In the proof of Lemma 9: the coefficient of the summand of `π` is 1. -/
private theorem prod_gamma_eq_one {L m : ℕ} (Q : Finset (Fin L)) (hQ : Q.card = m)
    (r c : OuterStr L m) (π : InnerStr m) :
    ∏ ℓ, coefficient (leftStrOf Q hQ r π ℓ) (rightStrOf Q hQ π c ℓ) (outStrOf Q hQ r c ℓ) = 1 := by
  have hone : ∀ ℓ,
      coefficient (leftStrOf Q hQ r π ℓ) (rightStrOf Q hQ π c ℓ) (outStrOf Q hQ r c ℓ) = 1 := by
    simp only [forall_iff_orderEmbOfFin_and_compl Q hQ, leftStrOf, rightStrOf, outStrOf,
      glue_orderEmbOfFin, glue_orderEmbOfFin_compl]
    exact ⟨fun _ => (coefficient_z0 _ _).trans (ite_eq_left ⟨_, _, rfl, rfl⟩),
      fun _ => (coefficient_x_y_z _ _ _ _).trans (ite_eq_left ⟨rfl, rfl⟩)⟩
  exact prod_eq_one fun ℓ _ => hone ℓ

/-- At the output string for a size-`m` set `Q` and indices `r`, `c`, the bilinear product of
the batch arrays equals `(X Q * Y Q) r c`. The matrices have arbitrary integer entries
(cf. [AlmanWilliams2026, Lemma 9]). -/
theorem bilinearProduct_arrays_eq_mul {L m : ℕ} (X : Finset (Fin L) → LeftMat L m)
    (Y : Finset (Fin L) → RightMat L m) (Q : Finset (Fin L)) (hQ : Q.card = m)
    (r c : OuterStr L m) :
    bilinearProduct (arrayL m X) (arrayR m Y) (outStrOf Q hQ r c) = (X Q * Y Q) r c := by
  -- To show: `∑_{(u,v)} ∏_ℓ γ(u_ℓ, v_ℓ, w_ℓ) a[u] b[v] = ∑_π X_Q[r, π] Y_Q[π, c]`. The right-hand
  -- side is the part of the left-hand side over the pairs `(u, v)` that belong to some `π`.
  rw [tensor_expansion, Matrix.mul_apply, ← Fintype.sum_prod_type']
  symm
  refine Fintype.sum_of_injective (fun π => (leftStrOf Q hQ r π, rightStrOf Q hQ π c)) ?_ _ _ ?_ ?_
  · -- There is one such summand for each of the D strings π.
    exact fun π π' h => (leftStrOf_inj.mp (congrArg Prod.fst h)).2
  · -- Every other summand is zero.  a[u] b[v] ≠ 0 requires the inner sets of u and v to have
    -- exactly m elements.
    rintro ⟨u, v⟩ hnot
    by_contra hne
    obtain ⟨⟨hγ, ha⟩, hb⟩ : ((∏ ℓ, coefficient (u ℓ) (v ℓ) (outStrOf Q hQ r c ℓ)) ≠ 0
        ∧ arrayL m X u ≠ 0) ∧ arrayR m Y v ≠ 0 := by
      simpa only [mul_ne_zero_iff] using hne
    obtain ⟨π, rfl, rfl⟩ := exists_of_summand_ne_zero Q hQ r c
      (fun ℓ => prod_ne_zero_iff.mp hγ ℓ (mem_univ ℓ))
      (by_contra fun h => ha (dite_eq_right h)) (by_contra fun h => hb (dite_eq_right h))
    exact hnot ⟨π, rfl⟩
  · -- The summand of `π` is `1 · X_Q[r, π] · Y_Q[π, c]`.
    intro π
    rw [prod_gamma_eq_one, one_mul, arrayL_leftStrOf, arrayR_rightStrOf]

/-- An output string with exactly `m` inner levels selects the product of the two matrices
indexed by its inner set, at its extracted row and column. This is an equality of integer
values for the arrays `arrayL m X` and `arrayR m Y` (cf. [AlmanWilliams2026, Lemma 9]). -/
theorem batch_product_spec {L m : ℕ} (X : Finset (Fin L) → LeftMat L m) (Y : Finset (Fin L) →
  RightMat L m)
    (w : OutStr L) (h : (innerSetO w).card = m) :
    bilinearProduct (arrayL m X) (arrayR m Y) w
      = (X (innerSetO w) * Y (innerSetO w)) (rowO w h) (colO w h) := by
  -- `w` is the output string with the inner set, the row and the column of `w`.
  conv_lhs => rw [outStr_eq_outStrOf h rfl h]
  exact bilinearProduct_arrays_eq_mul X Y (innerSetO w) h (rowO w h) (colO w h)

/-- `Full.result` on the batch arrays agrees with the matrix product for every size-`m` set
`Q` and every row and column index. -/
theorem Full.arrays_eq_mul {L m : ℕ} (X : Finset (Fin L) → LeftMat L m)
    (Y : Finset (Fin L) → RightMat L m) (Q : Finset (Fin L)) (hQ : Q.card = m)
    (r c : OuterStr L m) :
    Full.result L (arrayL m X) (arrayR m Y) (outStrOf Q hQ r c) = (X Q * Y Q) r c := by
  rw [Full.result_eq_bilinearProduct]
  exact bilinearProduct_arrays_eq_mul X Y Q hQ r c

end Cslib.Algorithms.MatrixMultiplication.Schonhage
