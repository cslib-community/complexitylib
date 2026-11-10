/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.LinearAlgebra.Tensor.Degeneration
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.Lagrange

/-!
# From shared-left packings to packings with independent left inputs

A shared-left degeneration computes `w` targets `F i` that share one left input. To compute
them with independent left inputs `A i`, interpolate ([Pass][Pass2026], Lemma 3.4): batch the
left inputs into one polynomial `A(ξ)` with `A(i) = A i`, and the `w` column blocks `B i j` of
the `i`-th right input into `B'_i(ξ)` with `B'_i(i + ε j) = B i j`. At each of `2 w - 1`
evaluation points `ξ = k` all targets share the left input `A(k)`, so the shared-left
degeneration applies; interpolating the `2 w - 1` outputs, which are polynomials in `ξ` of degree
at most `2 w - 2`, and evaluating at `ξ = i + ε j` recovers `F i (A i) (B i j)` modulo `ε`, because
`A(i + ε j) ≡ A i` modulo `ε`. The denominators `ε ^ (w - 1)` of the right encodings are
cleared by raising the order, and the inner degeneration is used with `ε` replaced by `ε ^ w`
so that its error survives the division.

The result (`IsSLDegen.separate`) is a degeneration, of order `w h + w - 1`, of `2 w - 1`
independent copies of `S ⊗ mm 1 1 u` to the direct sum of the targets `F i ⊗ mm 1 1 w`, each
target now with `w` column blocks and its own left input.

## Main results

* `Cslib.Tensor.IsSLDegen.separate`: [Pass][Pass2026], Lemma 3.4.

## References

* [R. Pass, *Matrix Multiplication from Polynomial Packings*][Pass2026], Lemma 3.4
-/

@[expose] public section

namespace Cslib.Tensor

open Finset Polynomial

variable {K : Type*} [Field K] [CharZero K] {X Y Z X' Y' Z' : Type*}

/-! ### Structural helpers -/

omit [Field K] [CharZero K] in
/-- Mapping entries commutes with direct sums when the map fixes `0`. -/
private theorem map_dsum {R R' : Type*} [Zero R] [Zero R'] {ι : Type*} [DecidableEq ι]
    (f : R → R') (hf : f 0 = 0) (G : ι → Tensor R X Y Z) :
    (dsum G).map f = dsum fun i => (G i).map f := by
  funext x y z
  simp only [Tensor.map_apply, dsum_apply, apply_ite f, hf]

omit [Field K] [CharZero K] in
/-- A direct sum of reindexed tensors is a reindexed direct sum. -/
private theorem dsum_reindex {R : Type*} [Zero R] {ι : Type*} [DecidableEq ι] (e₁ : X ≃ X')
    (e₂ : Y ≃ Y') (e₃ : Z ≃ Z') (G : ι → Tensor R X Y Z) :
    dsum (fun i => reindex e₁ e₂ e₃ (G i)) =
      reindex (Equiv.prodCongr (Equiv.refl ι) e₁) (Equiv.prodCongr (Equiv.refl ι) e₂)
        (Equiv.prodCongr (Equiv.refl ι) e₃) (dsum G) :=
  rfl

omit [Field K] [CharZero K] in
/-- Direct sums are linear in the summands. -/
private theorem dsum_add_smul {R : Type*} [Semiring R] {ι : Type*} [DecidableEq ι] (a b : R)
    (G G' : ι → Tensor R X Y Z) :
    dsum (fun i => a • G i + b • G' i) = a • dsum G + b • dsum G' := by
  funext x y z
  simp only [dsum_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> simp

/-! ### Substituting `ε ↦ ε ^ w` -/

omit [CharZero K] in
/-- Substituting `ε ↦ ε ^ w` in a shared-left degeneration of order `h` gives one of order
`w h` whose error is divisible by `ε ^ (w h + w)`. -/
private theorem IsSLDegen.expand [Fintype X'] [Fintype Y'] [Fintype Z'] [DecidableEq X']
    {f : X → X'} {h : ℕ} {T : Tensor K X Y Z} {S : Tensor K X' Y' Z'} (hT : IsSLDegen f h T S)
    (w : ℕ) :
    ∃ (β : Matrix Y' Y K[X]) (γ : Matrix Z Z' K[X]) (E : Tensor K[X] X Y Z),
      restrict (incl f) β γ (S.map C) =
        (Polynomial.X ^ (w * h) : K[X]) • T.map C +
          (Polynomial.X ^ (w * h + w) : K[X]) • E := by
  obtain ⟨β, γ, E, hE⟩ := hT
  let φ : K[X] →+* K[X] := (Polynomial.expand K w).toRingHom
  have hX : φ Polynomial.X = Polynomial.X ^ w := expand_X w
  have hC : ∀ a : K, φ (C a) = C a := fun a => expand_C w a
  refine ⟨β.map φ, γ.map φ, E.map φ, ?_⟩
  have h1 : (restrict (incl f) β γ (S.map C)).map φ =
      restrict (incl f) (β.map φ) (γ.map φ) (S.map C) := by
    rw [map_restrict, map_incl]
    congr 1
    funext x y z
    simp only [Tensor.map_apply, hC]
  rw [← h1, hE, show w * h + w = w * (h + 1) by ring]
  funext x y z
  simp only [Tensor.map_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul,
    map_pow, hX, hC, ← pow_mul]

/-! ### Lagrange interpolation at the nodes `0, …, m - 1` -/

/-- The nodes `0, …, m - 1` are distinct in characteristic zero. -/
private theorem node_injective (m : ℕ) : Function.Injective fun k : Fin m => (k.val : K) :=
  Nat.cast_injective.comp Fin.val_injective

omit [CharZero K] in
/-- The Lagrange basis polynomial of the node `k` among `0, …, m - 1`. -/
private noncomputable def lag (m : ℕ) (k : Fin m) : K[X] :=
  Lagrange.basis univ (fun t : Fin m => (t.val : K)) k

private theorem lag_natDegree {m : ℕ} (k : Fin m) : (lag (K := K) m k).natDegree = m - 1 := by
  rw [lag, Lagrange.natDegree_basis (Set.injOn_of_injective (node_injective m)) (mem_univ k),
    card_univ, Fintype.card_fin]

private theorem lag_eval {m : ℕ} (k k' : Fin m) :
    (lag (K := K) m k).eval (k'.val : K) = if k = k' then 1 else 0 := by
  rw [lag]
  split_ifs with h
  · subst h
    exact Lagrange.eval_basis_self (Set.injOn_of_injective (node_injective m)) (mem_univ k)
  · exact Lagrange.eval_basis_of_ne (s := univ) (v := fun t : Fin m => (t.val : K)) h (mem_univ k')

/-- A polynomial over `K[ε]` of degree below `m` is the interpolation of its values at the
nodes `0, …, m - 1`. -/
private theorem eq_sum_eval_lag {m : ℕ} (p : K[X][X]) (hp : p.natDegree < m) :
    p = ∑ k : Fin m, C (p.eval (C (k.val : K))) * (lag (K := K) m k).map C := by
  refine eq_of_natDegree_lt_card_of_eval_eq p _
    (f := fun k : Fin m => (C (k.val : K) : K[X])) (C_injective.comp (node_injective (K := K) m))
    ?_ ?_
  · intro k'
    simp [eval_finsetSum, lag_eval, apply_ite C, sum_ite_eq']
  · rw [Fintype.card_fin, max_lt_iff]
    refine ⟨hp, lt_of_le_of_lt (natDegree_sum_le_of_forall_le (n := m - 1) _ _ fun k _ => ?_)
      (by omega)⟩
    exact (natDegree_C_mul_le _ _).trans (natDegree_map_le.trans (lag_natDegree k).le)

omit [CharZero K] in
/-- The value of a polynomial at `a + ε b` is its value at `a` modulo `ε`. -/
private theorem X_dvd_eval_sub (p : K[X]) (a b : K) :
    (Polynomial.X : K[X]) ∣ (p.map C).eval (C a + Polynomial.X * C b) - C (p.eval a) := by
  have h := sub_dvd_eval_sub (C a + Polynomial.X * C b) (C a) (p.map C)
  rw [add_sub_cancel_left, eval_map_apply] at h
  exact (dvd_mul_right _ _).trans h

/-! ### The right encoder polynomials -/

omit [CharZero K] in
/-- The polynomial `∏_{j' ≠ j} (ξ - (i + ε j')) / (j - j')` over `K[ε]`: it vanishes at
`ξ = i + ε j'` for `j' ≠ j` and equals `ε ^ (w - 1)` at `ξ = i + ε j`. -/
private noncomputable def rightPoly {w : ℕ} (i j : Fin w) : K[X][X] :=
  ∏ j' ∈ univ.erase j, (Polynomial.X - C (C (i.val : K) + Polynomial.X * C (j'.val : K))) *
    C (C ((j.val : K) - (j'.val : K))⁻¹)

omit [CharZero K] in
private theorem rightPoly_natDegree_le {w : ℕ} (i j : Fin w) :
    (rightPoly (K := K) i j).natDegree ≤ w - 1 := by
  refine (natDegree_prod_le _ _).trans
    ((sum_le_sum (g := fun _ => 1) fun j' _ => ?_).trans ?_)
  · refine natDegree_mul_le.trans ?_
    rw [natDegree_C, add_zero]
    exact natDegree_X_sub_C_le _
  · rw [sum_const, card_erase_of_mem (mem_univ j), card_univ, Fintype.card_fin, smul_eq_mul,
      mul_one]

private theorem rightPoly_eval {w : ℕ} (i j j' : Fin w) :
    (rightPoly (K := K) i j).eval (C (i.val : K) + Polynomial.X * C (j'.val : K)) =
      if j = j' then Polynomial.X ^ (w - 1) else 0 := by
  rw [rightPoly, eval_prod]
  split_ifs with hj
  · subst hj
    rw [show w - 1 = #(univ.erase j) by
      rw [card_erase_of_mem (mem_univ j), card_univ, Fintype.card_fin], ← prod_const]
    refine prod_congr rfl fun j'' hj'' => ?_
    have hne : (j.val : K) - (j''.val : K) ≠ 0 :=
      sub_ne_zero.mpr fun h => (mem_erase.mp hj'').1 (node_injective (K := K) w h).symm
    rw [eval_mul, eval_sub, eval_X, eval_C, eval_C, add_sub_add_left_eq_sub, ← mul_sub, ← C_sub,
      mul_assoc, ← C_mul, mul_inv_cancel₀ hne, C_1, mul_one]
  · refine prod_eq_zero (mem_erase.mpr ⟨Ne.symm hj, mem_univ j'⟩) ?_
    simp

/-! ### The encoders and the decoder -/

omit [CharZero K] in
/-- The left encoder: the `w` left inputs `A i` are batched into `A(ξ) = ∑ᵢ ℓᵢ(ξ) A i`,
with `ℓᵢ` the Lagrange basis at `0, …, w - 1`, and evaluated at the `2 w - 1` nodes. -/
private noncomputable def leftEnc [DecidableEq X] (w : ℕ) :
    Matrix (Fin (2 * w - 1) × X) (Fin w × (X × (Fin 1 × Fin 1))) K[X] :=
  Matrix.of fun kx ix =>
    if kx.2 = ix.2.1 then C ((lag (K := K) w ix.1).eval (kx.1.val : K)) else 0

omit [CharZero K] in
/-- The right encoder: the column blocks `B i j` of the `i`-th right input are batched into
`B'ᵢ(ξ) = ∑ⱼ rightPoly i j (ξ) B i j` and evaluated at the `2 w - 1` nodes. -/
private noncomputable def rightEnc [DecidableEq Y] (w : ℕ) :
    Matrix (Fin (2 * w - 1) × (Fin w × Y)) (Fin w × (Y × (Fin 1 × Fin w))) K[X] :=
  Matrix.of fun kiy iyj =>
    if kiy.2.1 = iyj.1 ∧ kiy.2.2 = iyj.2.1 then
      (rightPoly (K := K) iyj.1 iyj.2.2.2).eval (C (kiy.1.val : K))
    else 0

omit [CharZero K] in
/-- The decoder: interpolate the `2 w - 1` outputs of the `i`-th target and evaluate at
`ξ = i + ε j`. -/
private noncomputable def dec [DecidableEq Z] (w : ℕ) :
    Matrix (Fin w × (Z × (Fin 1 × Fin w))) (Fin (2 * w - 1) × (Fin w × Z)) K[X] :=
  Matrix.of fun izj kiz =>
    if izj.1 = kiz.2.1 ∧ izj.2.1 = kiz.2.2 then
      ((lag (K := K) (2 * w - 1) kiz.1).map C).eval
        (C (izj.1.val : K) + Polynomial.X * C (izj.2.2.2.val : K))
    else 0

omit [CharZero K] in
/-- The entries of the encoded shared-left sum: a single sum over the nodes. -/
private theorem restrict_enc_apply [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X]
    [DecidableEq Y] [DecidableEq Z] {w : ℕ}
    (F : Fin w → Tensor K X Y Z) (i i' i'' : Fin w) (x : X) (a : Fin 1 × Fin 1) (y : Y)
    (b : Fin 1) (j : Fin w) (z : Z) (c : Fin 1) (j' : Fin w) :
    restrict (leftEnc w) (rightEnc w) (dec w) ((dsum fun _ : Fin (2 * w - 1) => slSum F).map C)
      (i, (x, a)) (i', (y, (b, j))) (i'', (z, (c, j'))) =
      if i' = i'' then
        C (F i' x y z) * ∑ k : Fin (2 * w - 1), C ((lag (K := K) w i).eval (k.val : K)) *
          (rightPoly (K := K) i' j).eval (C (k.val : K)) *
          ((lag (K := K) (2 * w - 1) k).map C).eval
            (C (i'.val : K) + Polynomial.X * C (j'.val : K))
      else 0 := by
  simp only [restrict, Fintype.sum_prod_type, leftEnc, rightEnc, dec, Matrix.of_apply,
    Tensor.map_apply, dsum_apply, slSum_apply]
  simp only [apply_ite C, C_0, ite_and, mul_ite, ite_mul, zero_mul, mul_zero, sum_ite_irrel,
    sum_const_zero, sum_ite_eq, sum_ite_eq', mem_univ, ite_true]
  by_cases hi : i' = i''
  · subst hi
    rw [ite_eq_left rfl, ite_eq_left rfl, mul_sum]
    exact sum_congr rfl fun k _ => by ring
  · rw [ite_eq_right (Ne.symm hi), ite_eq_right hi]

/-- **Interpolation in `ξ`** ([Pass][Pass2026], Lemma 3.4): encoding and decoding `2 w - 1`
independent copies of the shared-left sum `slSum F` computes the direct sum of the targets
`F i ⊗ mm 1 1 w` times `ε ^ (w - 1)`, with an error divisible by `ε ^ w`. -/
private theorem exists_restrict_dsum_slSum [Fintype X] [Fintype Y] [Fintype Z] {w : ℕ}
    (F : Fin w → Tensor K X Y Z) :
    ∃ (α : Matrix (Fin (2 * w - 1) × X) (Fin w × (X × (Fin 1 × Fin 1))) K[X])
      (β : Matrix (Fin (2 * w - 1) × (Fin w × Y)) (Fin w × (Y × (Fin 1 × Fin w))) K[X])
      (γ : Matrix (Fin w × (Z × (Fin 1 × Fin w))) (Fin (2 * w - 1) × (Fin w × Z)) K[X])
      (E : Tensor K[X] (Fin w × (X × (Fin 1 × Fin 1))) (Fin w × (Y × (Fin 1 × Fin w)))
        (Fin w × (Z × (Fin 1 × Fin w)))),
      restrict α β γ ((dsum fun _ : Fin (2 * w - 1) => slSum F).map C) =
        (Polynomial.X ^ (w - 1) : K[X]) • (dsum fun i => tprod (F i) (mm 1 1 w)).map C +
          (Polynomial.X ^ w : K[X]) • E := by
  classical
  suffices h : ∀ x₀ y₀ z₀, ∃ e : K[X],
      restrict (leftEnc w) (rightEnc w) (dec w)
        ((dsum fun _ : Fin (2 * w - 1) => slSum F).map C) x₀ y₀ z₀ =
        Polynomial.X ^ (w - 1) * C ((dsum fun i => tprod (F i) (mm 1 1 w)) x₀ y₀ z₀) +
          Polynomial.X ^ w * e by
    choose E hE using h
    exact ⟨leftEnc w, rightEnc w, dec w, E,
      funext fun x₀ => funext fun y₀ => funext fun z₀ => hE x₀ y₀ z₀⟩
  rintro ⟨i, x, a⟩ ⟨i', y, b, j⟩ ⟨i'', z, c, j'⟩
  rw [restrict_enc_apply]
  simp only [dsum_apply, tprod_apply, mm_apply, Fin.fin_one_eq_zero, true_and]
  by_cases hi : i' = i''
  · subst hi
    obtain ⟨w', rfl⟩ : ∃ w', w = w' + 1 := ⟨w - 1, by have := i.pos; omega⟩
    simp only [Nat.add_sub_cancel, and_true, ite_true]
    set θ : K[X] := C (i'.val : K) + Polynomial.X * C (j'.val : K) with hθ
    have hp : ((lag (K := K) (w' + 1) i).map C * rightPoly (K := K) i' j).natDegree <
        2 * (w' + 1) - 1 := by
      refine lt_of_le_of_lt natDegree_mul_le ?_
      have h1 : ((lag (K := K) (w' + 1) i).map C).natDegree ≤ w' + 1 - 1 :=
        natDegree_map_le.trans (lag_natDegree i).le
      have h2 := rightPoly_natDegree_le (K := K) i' j
      omega
    have hsum : ∑ k : Fin (2 * (w' + 1) - 1), C ((lag (K := K) (w' + 1) i).eval (k.val : K)) *
        (rightPoly (K := K) i' j).eval (C (k.val : K)) *
        ((lag (K := K) (2 * (w' + 1) - 1) k).map C).eval θ =
        ((lag (K := K) (w' + 1) i).map C).eval θ * (rightPoly (K := K) i' j).eval θ := by
      rw [← eval_mul]
      conv_rhs => rw [eq_sum_eval_lag _ hp]
      rw [eval_finsetSum]
      refine sum_congr rfl fun k _ => ?_
      rw [eval_mul, eval_C, eval_mul, eval_map_apply]
    obtain ⟨r, hr⟩ := X_dvd_eval_sub (lag (K := K) (w' + 1) i) (i'.val : K) (j'.val : K)
    rw [sub_eq_iff_eq_add] at hr
    refine ⟨if j = j' then C (F i' x y z) * r else 0, ?_⟩
    rw [hsum, hθ, rightPoly_eval, ← hθ, hr, lag_eval, Nat.add_sub_cancel]
    split_ifs <;> subst_vars <;> simp only [C_0, C_1, mul_zero, mul_one, add_zero] <;> ring
  · refine ⟨0, ?_⟩
    simp [hi]

/-- **From shared-left to independent left inputs** ([Pass][Pass2026], Lemma 3.4): a shared-left
degeneration of order `h` of `u` copies of `S` to the targets `F i`, `i < w`, gives a
degeneration of order `w h + w - 1` of `2 w - 1` independent copies of `S ⊗ mm 1 1 u` to the
direct sum of the targets `F i ⊗ mm 1 1 w`. -/
theorem IsSLDegen.separate [Finite X] [Finite Y] [Finite Z] [Fintype X'] [Fintype Y']
    [Fintype Z'] [DecidableEq X'] {w u h : ℕ}
    {f : X → X'} {F : Fin w → Tensor K X Y Z} {S : Tensor K X' Y' Z'}
    (hF : IsSLDegen f h (slSum F) (slSum fun _ : Fin u => S)) :
    IsDegen (w * h + w - 1) (Tensor.dsum fun i => Tensor.tprod (F i) (mm 1 1 w))
      (Tensor.dsum fun _ : Fin (2 * w - 1) => Tensor.tprod S (mm 1 1 u)) := by
  classical
  cases nonempty_fintype X
  cases nonempty_fintype Y
  cases nonempty_fintype Z
  rcases Nat.eq_zero_or_pos w with rfl | hw
  · exact ⟨0, 0, 0, 0, funext fun x => x.1.elim0⟩
  obtain ⟨β₀, γ₀, E₀, h₀⟩ := hF.expand w
  obtain ⟨α₁, β₁, γ₁, E₁, h₁⟩ := exists_restrict_dsum_slSum (K := K) F
  -- `2 w - 1` independent copies of the expanded shared-left degeneration
  have h₀' : restrict (blockDiag fun _ : Fin (2 * w - 1) => (incl f : Matrix X' X K[X]))
      (blockDiag fun _ => β₀) (blockDiag fun _ => γ₀)
      ((Tensor.dsum fun _ : Fin (2 * w - 1) => slSum fun _ : Fin u => S).map C) =
      (Polynomial.X ^ (w * h) : K[X]) • (Tensor.dsum fun _ : Fin (2 * w - 1) => slSum F).map C +
        (Polynomial.X ^ (w * h + w) : K[X]) • Tensor.dsum fun _ : Fin (2 * w - 1) => E₀ := by
    rw [map_dsum C C_0, ← restrict_dsum, map_dsum C C_0, ← dsum_add_smul]
    simp only [h₀]
  -- compose with the interpolation step
  have h₂ : restrict (blockDiag (fun _ : Fin (2 * w - 1) => (incl f : Matrix X' X K[X])) * α₁)
      (blockDiag (fun _ => β₀) * β₁) (γ₁ * blockDiag fun _ => γ₀)
      ((Tensor.dsum fun _ : Fin (2 * w - 1) => slSum fun _ : Fin u => S).map C) =
      (Polynomial.X ^ (w * h + w - 1) : K[X]) •
          (Tensor.dsum fun i => Tensor.tprod (F i) (mm 1 1 w)).map C +
        (Polynomial.X ^ (w * h + w - 1 + 1) : K[X]) •
          (E₁ + restrict α₁ β₁ γ₁ (Tensor.dsum fun _ : Fin (2 * w - 1) => E₀)) := by
    rw [← restrict_restrict, h₀', restrict_add, restrict_smul, restrict_smul, h₁, smul_add,
      smul_smul, smul_smul, ← pow_add, ← pow_add, show w * h + (w - 1) = w * h + w - 1 by omega,
      show w * h + w - 1 + 1 = w * h + w by omega, smul_add, add_assoc]
  have h₃ : IsDegen (w * h + w - 1) (Tensor.dsum fun i => Tensor.tprod (F i) (mm 1 1 w))
      (Tensor.dsum fun _ : Fin (2 * w - 1) => slSum fun _ : Fin u => S) := ⟨_, _, _, _, h₂⟩
  -- identify the source with `2 w - 1` copies of `S ⊗ mm 1 1 u`
  obtain ⟨e₁, e₂, e₃, hsl⟩ : ∃ e₁ e₂ e₃,
      slSum (fun _ : Fin u => S) = reindex e₁ e₂ e₃ (Tensor.tprod S (mm 1 1 u)) :=
    ⟨_, _, _, slSum_const u S⟩
  rw [hsl, dsum_reindex] at h₃
  have h₄ := h₃.reindex_source (Equiv.prodCongr (Equiv.refl (Fin (2 * w - 1))) e₁).symm
    (Equiv.prodCongr (Equiv.refl (Fin (2 * w - 1))) e₂).symm
    (Equiv.prodCongr (Equiv.refl (Fin (2 * w - 1))) e₃).symm
  rwa [reindex_symm_reindex] at h₄

end Cslib.Tensor
