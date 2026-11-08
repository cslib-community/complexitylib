/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate

public import Complexity.Foundations.LinearAlgebra.Tensor.Amplify
public import Complexity.Foundations.LinearAlgebra.Tensor.Primal
public import Complexity.Foundations.LinearAlgebra.Tensor.Separate
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# The round, the finite identity and `ω ≤ 9/4` at the level of rank

The product `Q d a b = T ⊗ T^{12} ⊗ T^{13}` of the canonical tensor
`T = canonical d a b = tpow d (full a b) ⊗ tpow d (mid a b)` with its two role exchanges
([Pass][Pass2026], Lemma 4.1) contains every leg permutation of `full a b` equally often, so
exchanging `a` and `b` only permutes its factors (`isRestriction_Q_swap`); at `a = b = 1` it is
matrix multiplication (`isRestriction_mm_tprod_Q_one`), and its rank is at most
`(a + b - 1) ^ (6 d)` (`rank_Q`).

A **column packing** `ColumnPacking d a b b' w u H` is a degeneration of `2 w` independent copies
of `canonical d a b' ⊗ mm 1 1 u` to `w` copies of `canonical d a b ⊗ mm 1 1 w`: the output of
amplification and separation of the primal packing (`columnPacking_of_count`), with
`u = c ^ (2 d)` and `w` the square of the number of words with a prescribed number of middle
letters. A **round** ([Pass][Pass2026], Lemma 4.2) tensors a column packing with its two role
exchanges, reducing all three matrix dimensions, and applies this twice through the symmetry
`Q d L L' ≅ Q d L' L`, increasing both polynomial lengths from `L` to `L'`
(`isDegen_round`).

Iterating `k` rounds from `L₀ = 1` ([Pass][Pass2026], Theorem 4.3) gives a degeneration of
`64 ^ k w ^ 3` copies of `Q d L_k L_k ⊗ mm (w ^ 2) (w ^ 2) (w ^ 2)` to `mm v v v` with
`v = w ^ 2 Λ ^ k`, hence a border rank bound `64 ^ k w ^ 9 (2 L_k - 1) ^ (6 d)`, and Bini's
conversion gives exact rank bounds on tensor powers. Choosing `c`, `d`, `k` and the power
(`exists_rank_mm_lt_rpow`, [Pass][Pass2026], Corollary 4.4) yields, for every `τ > 9/4`, a side
`v ≥ 2` and an exact bilinear algorithm for `v × v` matrix multiplication with fewer than
`v ^ τ` multiplications.

## Main definitions

* `Cslib.Tensor.Q`: the product of the canonical tensor with its two role exchanges.
* `Cslib.Tensor.ColumnPacking`: the packings a round consumes.

## Main results

* `Cslib.Tensor.isRestriction_Q_swap`, `Cslib.Tensor.rank_Q`,
  `Cslib.Tensor.isRestriction_mm_tprod_Q_one`: [Pass][Pass2026], Lemma 4.1.
* `Cslib.Tensor.columnPacking_of_count`: from the primal packing to a column packing.
* `Cslib.Tensor.ColumnPacking.cube_mm`, `Cslib.Tensor.isDegen_round`: [Pass][Pass2026],
  Lemma 4.2.
* `Cslib.Tensor.exists_rank_mm_lt_rpow`: [Pass][Pass2026], Theorem 4.3 and Corollary 4.4.

## References

* [R. Pass, *Matrix Multiplication from Polynomial Packings*][Pass2026], §4
-/

@[expose] public section

namespace Cslib.Tensor

open Finset Matrix

variable {K : Type*}

/-! ### The product `Q` -/

section CommRing

variable [CommRing K]

/-- The product `Q_{a,b} = T ⊗ T^{12} ⊗ T^{13}` of the canonical tensor with its two role
exchanges ([Pass][Pass2026], Lemma 4.1). All three legs have the same index type. -/
def Q (d a b : ℕ) :
    Tensor K (((Fin d → Fin (a + b - 1)) × (Fin d → Fin (a + b - 1))) ×
        ((Fin d → Fin (a + b - 1)) × (Fin d → Fin (a + b - 1))) ×
        ((Fin d → Fin (a + b - 1)) × (Fin d → Fin (a + b - 1))))
      (((Fin d → Fin (a + b - 1)) × (Fin d → Fin (a + b - 1))) ×
        ((Fin d → Fin (a + b - 1)) × (Fin d → Fin (a + b - 1))) ×
        ((Fin d → Fin (a + b - 1)) × (Fin d → Fin (a + b - 1))))
      (((Fin d → Fin (a + b - 1)) × (Fin d → Fin (a + b - 1))) ×
        ((Fin d → Fin (a + b - 1)) × (Fin d → Fin (a + b - 1))) ×
        ((Fin d → Fin (a + b - 1)) × (Fin d → Fin (a + b - 1)))) :=
  tprod (canonical d a b) (tprod (swap12 (canonical d a b)) (swap13 (canonical d a b)))

/-- Exchanging the lengths of a full product exchanges its inputs, on the padded index sets
([Pass][Pass2026], equation (9)). -/
private theorem full_finCongr {a b : ℕ} (h : a + b - 1 = b + a - 1) (p q r : Fin (a + b - 1)) :
    (full b a : Tensor K _ _ _) (finCongr h p) (finCongr h q) (finCongr h r) = full a b q p r := by
  simp only [full_apply, finCongr_apply, Fin.val_cast]
  exact if_congr (by omega) rfl rfl

/-- **Symmetry of `Q`** ([Pass][Pass2026], Lemma 4.1): exchanging the lengths permutes the
factors, so `Q d a b` is a restriction of `Q d b a`. The six factors of `Q d a b` are, in order,
`Full_{a,b}`, `Mid_{a,b}`, `Full_{b,a}`, `Full_{b,a}^{13}`, `Full_{a,b}^{13}` and `Mid_{b,a}`
(with `Full_{b,a} = Full_{a,b}^{12}`); exchanging `a` and `b` permutes them by the involution
`(0 2) (1 5) (3 4)`. -/
theorem isRestriction_Q_swap (d a b : ℕ) :
    IsRestriction (Q d a b : Tensor K _ _ _) (Q d b a) := by
  have hs : a + b - 1 = b + a - 1 := by omega
  let c : (Fin d → Fin (a + b - 1)) ≃ (Fin d → Fin (b + a - 1)) :=
    Equiv.piCongrRight fun _ => finCongr hs
  let e : ((Fin d → Fin (b + a - 1)) × (Fin d → Fin (b + a - 1))) ×
        ((Fin d → Fin (b + a - 1)) × (Fin d → Fin (b + a - 1))) ×
        ((Fin d → Fin (b + a - 1)) × (Fin d → Fin (b + a - 1))) ≃
      ((Fin d → Fin (a + b - 1)) × (Fin d → Fin (a + b - 1))) ×
        ((Fin d → Fin (a + b - 1)) × (Fin d → Fin (a + b - 1))) ×
        ((Fin d → Fin (a + b - 1)) × (Fin d → Fin (a + b - 1))) :=
    { toFun := fun u => ((c.symm u.2.1.1, c.symm u.2.2.2),
        ((c.symm u.1.1, c.symm u.2.2.1), (c.symm u.2.1.2, c.symm u.1.2)))
      invFun := fun x => ((c x.2.1.1, c x.2.2.2), ((c x.1.1, c x.2.2.1), (c x.2.1.2, c x.1.2)))
      left_inv := fun u => by simp
      right_inv := fun x => by simp }
  suffices h : (Q d a b : Tensor K _ _ _) = reindex e e e (Q d b a) by
    rw [h]
    exact isRestriction_reindex _ _ _ _
  funext x y z
  simp only [Q, canonical, mid, tprod_apply, tpow_apply, swap12_apply, swap13_apply, swap23_apply,
    reindex_apply, e, c, Equiv.coe_fn_symm_mk, Equiv.piCongrRight_apply, Pi.map_apply,
    full_finCongr]
  ring

/-- At `a = b = 1`, `Q` with matrix dimensions `[p, q, r]` computes matrix multiplication
([Pass][Pass2026], Lemma 4.1): every entry of `Q d 1 1` is `1`. -/
theorem isRestriction_mm_tprod_Q_one (d p q r : ℕ) :
    IsRestriction (mm p q r : Tensor K _ _ _) (tprod (Q d 1 1) (mm p q r)) := by
  classical
  have hQ : ∀ x y z, (Q d 1 1 : Tensor K _ _ _) x y z = 1 := fun x y z => by
    simp [Q, canonical, mid]
  let o : Fin (1 + 1 - 1) := ⟨0, by omega⟩
  let x₀ := ((fun _ : Fin d => o, fun _ : Fin d => o),
    ((fun _ : Fin d => o, fun _ : Fin d => o), (fun _ : Fin d => o, fun _ : Fin d => o)))
  refine ⟨incl fun a => (x₀, a), incl fun b => (x₀, b), (incl fun c => (x₀, c))ᵀ, ?_⟩
  rw [restrict_incl]
  funext a b c
  simp [hQ]

/-! ### Column packings and the round -/

/-- A **column packing** with parameters `w, u, H`: `w` copies of `canonical d a b ⊗ mm 1 1 w`
are a degeneration of order `H` of `2 w` copies of `canonical d a b' ⊗ mm 1 1 u`. -/
def ColumnPacking (d a b b' w u H : ℕ) : Prop :=
  IsDegen H (dsum fun _ : Fin w => tprod (canonical d a b : Tensor K _ _ _) (mm 1 1 w))
    (dsum fun _ : Fin (2 * w) => tprod (canonical d a b') (mm 1 1 u))

/-- The reindexing of `tprod_dsum_cube`. -/
private def cubeEquiv (ι X X' X'' X₂ X₃ X₄ : Type*) :
    (ι × ι × ι) × ((X × (X'' × X₃)) × (X' × (X₂ × X₄))) ≃
      (ι × (X × X')) × ((ι × (X'' × X₂)) × (ι × (X₃ × X₄))) where
  toFun p := ((p.1.1, (p.2.1.1, p.2.2.1)),
    ((p.1.2.1, (p.2.1.2.1, p.2.2.2.1)), (p.1.2.2, (p.2.1.2.2, p.2.2.2.2))))
  invFun q := ((q.1.1, q.2.1.1, q.2.2.1),
    ((q.1.2.1, (q.2.1.2.1, q.2.2.2.1)), (q.1.2.2, (q.2.1.2.2, q.2.2.2.2))))
  left_inv _ := rfl
  right_inv _ := rfl

/-- Three direct sums of tensor products of pairs, tensored, form a direct sum over triples of
the regrouped tensor products. -/
private theorem tprod_dsum_cube {ι : Type*} [DecidableEq ι]
    {X Y Z X' Y' Z' X'' Y'' Z'' X₂ Y₂ Z₂ X₃ Y₃ Z₃ X₄ Y₄ Z₄ : Type*} (A : Tensor K X Y Z)
    (B : Tensor K X' Y' Z') (A' : Tensor K X'' Y'' Z'') (B' : Tensor K X₂ Y₂ Z₂)
    (A'' : Tensor K X₃ Y₃ Z₃) (B'' : Tensor K X₄ Y₄ Z₄) :
    tprod (dsum fun _ : ι => tprod A B)
        (tprod (dsum fun _ : ι => tprod A' B') (dsum fun _ : ι => tprod A'' B'')) =
      reindex (cubeEquiv ι X X' X'' X₂ X₃ X₄) (cubeEquiv ι Y Y' Y'' Y₂ Y₃ Y₄)
        (cubeEquiv ι Z Z' Z'' Z₂ Z₃ Z₄)
        (dsum fun _ : ι × ι × ι => tprod (tprod A (tprod A' A'')) (tprod B (tprod B' B''))) := by
  ext ⟨⟨i, x, x'⟩, ⟨⟨j, x'', x₂⟩, ⟨l, x₃, x₄⟩⟩⟩ ⟨⟨i', y, y'⟩, ⟨⟨j', y'', y₂⟩, ⟨l', y₃, y₄⟩⟩⟩
    ⟨⟨i'', z, z'⟩, ⟨⟨j'', z'', z₂⟩, ⟨l'', z₃, z₄⟩⟩⟩
  simp only [tprod_apply, dsum_apply, reindex_apply, cubeEquiv, Equiv.coe_fn_symm_mk,
    Prod.mk.injEq, ite_zero_mul_ite_zero]
  exact if_congr (by tauto) (by ring) rfl

/-- `T ⊗ mm (k p) …` is a restriction of
`(T ⊗ (mm 1 1 k ⊗ mm 1 1 k^{12} ⊗ mm 1 1 k^{13})) ⊗ mm p p p`. -/
private theorem isRestriction_tprod_mm_mul {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor K X Y Z) (k p : ℕ) :
    IsRestriction (tprod T (mm (k * p) (k * p) (k * p)))
      (tprod (tprod T (tprod (mm 1 1 k) (tprod (swap12 (mm 1 1 k)) (swap13 (mm 1 1 k)))))
        (mm p p p)) := by
  rw [tprod_assoc]
  refine (IsRestriction.tprod (IsRestriction.refl T) ?_).trans (isRestriction_of_reindex _ _ _ _)
  refine IsRestriction.trans ?_
    (IsRestriction.tprod (isRestriction_mm_tprod_swaps k) (IsRestriction.refl _))
  rw [tprod_mm_mm]
  exact isRestriction_of_reindex _ _ _ _

/-- The converse of `isRestriction_tprod_mm_mul`. -/
private theorem isRestriction_tprod_mm_mul' {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor K X Y Z) (k p : ℕ) :
    IsRestriction
      (tprod (tprod T (tprod (mm 1 1 k) (tprod (swap12 (mm 1 1 k)) (swap13 (mm 1 1 k)))))
        (mm p p p))
      (tprod T (mm (k * p) (k * p) (k * p))) := by
  rw [tprod_assoc]
  refine (isRestriction_reindex _ _ _ _).trans (IsRestriction.tprod (IsRestriction.refl T) ?_)
  refine (IsRestriction.tprod (isRestriction_tprod_swaps_mm k) (IsRestriction.refl _)).trans ?_
  rw [tprod_mm_mm]
  exact isRestriction_reindex _ _ _ _

/-- **Cubing a column packing** ([Pass][Pass2026], proof of Lemma 4.2): a column packing
tensored with its two role exchanges and with `mm p p p` is a degeneration of `(2 w) ^ 3` copies
of `Q d a b' ⊗ mm (u p) (u p) (u p)` to `w ^ 3` copies of `Q d a b ⊗ mm (w p) (w p) (w p)`. -/
theorem ColumnPacking.cube_mm {d a b b' w u H : ℕ} (h : ColumnPacking (K := K) d a b b' w u H)
    (p : ℕ) :
    IsDegen (3 * H)
      (dsum fun _ : Fin (w ^ 3) => tprod (Q d a b : Tensor K _ _ _) (mm (w * p) (w * p) (w * p)))
      (dsum fun _ : Fin ((2 * w) ^ 3) => tprod (Q d a b') (mm (u * p) (u * p) (u * p))) := by
  classical
  have h₃ := IsDegen.tprod h (IsDegen.tprod (IsDegen.swap12 h) (IsDegen.swap13 h))
  simp only [swap12_dsum, swap13_dsum, swap12_tprod, swap13_tprod, tprod_dsum_cube] at h₃
  have h₄ := (h₃.of_reindex_target.of_reindex_source.tprod
    (IsDegen.of_isRestriction (IsRestriction.refl (mm p p p : Tensor K _ _ _))))
  rw [tprod_dsum_left, tprod_dsum_left] at h₄
  have h₅ := h₄.of_reindex_target.of_reindex_source
  rw [show H + (H + H) + 0 = 3 * H by ring] at h₅
  refine IsRestriction.trans_isDegen ?_ (h₅.trans_isRestriction ?_)
  · exact (isRestriction_dsum_const_of_card_le
      (le_of_eq (by simp [Fintype.card_prod]; ring)) _).trans
      (IsRestriction.dsum fun _ => isRestriction_tprod_mm_mul _ w p)
  · exact (IsRestriction.dsum fun _ => isRestriction_tprod_mm_mul' _ u p).trans
      (isRestriction_dsum_const_of_card_le (le_of_eq (by simp [Fintype.card_prod]; ring)) _)

/-- **A round** ([Pass][Pass2026], Lemma 4.2): column packings for `(L, L, L')` and `(L', L, L')`
and `Λ` with `u ^ 2 Λ ≤ w ^ 2` give, for every `x`, a degeneration of `64 w ^ 3` copies of
`Q d L' L' ⊗ mm (w ^ 2 x) …` to `w ^ 3` copies of `Q d L L ⊗ mm (w ^ 2 Λ x) …`: cube the first
packing at side `w Λ x`, rename its sources by `Q d L L' ≅ Q d L' L`, and feed them to eight
copies of the cube of the second packing at side `u Λ x`. -/
theorem isDegen_round {d L L' w u H Λ : ℕ} (h₁ : ColumnPacking (K := K) d L L L' w u H)
    (h₂ : ColumnPacking (K := K) d L' L L' w u H) (hΛ : u ^ 2 * Λ ≤ w ^ 2) (x : ℕ) :
    ∃ H', IsDegen H'
      (dsum fun _ : Fin (w ^ 3) =>
        tprod (Q d L L : Tensor K _ _ _) (mm (w ^ 2 * Λ * x) (w ^ 2 * Λ * x) (w ^ 2 * Λ * x)))
      (dsum fun _ : Fin (64 * w ^ 3) =>
        tprod (Q d L' L') (mm (w ^ 2 * x) (w ^ 2 * x) (w ^ 2 * x))) := by
  classical
  -- the first packing, cubed, with its sources renamed to `Q d L' L`
  have hA := (h₁.cube_mm (w * Λ * x)).trans_isRestriction (IsRestriction.dsum fun _ =>
    IsRestriction.tprod (isRestriction_Q_swap d L L') (IsRestriction.refl _))
  -- eight copies of the second packing, cubed
  have hB := IsDegen.dsum fun _ : Fin 8 => h₂.cube_mm (u * Λ * x)
  rw [dsum_dsum, dsum_dsum] at hB
  have hB' := hB.of_reindex_target.of_reindex_source
  -- the sources of the first feed the targets of the second
  have hmid : IsRestriction
      (dsum fun _ : Fin ((2 * w) ^ 3) => tprod (Q d L' L : Tensor K _ _ _)
        (mm (u * (w * Λ * x)) (u * (w * Λ * x)) (u * (w * Λ * x))))
      (dsum fun _ : Fin 8 × Fin (w ^ 3) => tprod (Q d L' L : Tensor K _ _ _)
        (mm (w * (u * Λ * x)) (w * (u * Λ * x)) (w * (u * Λ * x)))) :=
    (IsRestriction.dsum fun _ => IsRestriction.tprod (IsRestriction.refl _)
      (isRestriction_mm_of_eq (by ring) (by ring) (by ring))).trans
      (isRestriction_dsum_const_of_card_le (le_of_eq (by simp [Fintype.card_prod]; ring)) _)
  -- pad the final sources to side `w ^ 2 x`
  have hle : u * (u * Λ * x) ≤ w ^ 2 * x :=
    calc u * (u * Λ * x) = u ^ 2 * Λ * x := by ring
      _ ≤ w ^ 2 * x := Nat.mul_le_mul_right x hΛ
  have hend : IsRestriction
      (dsum fun _ : Fin 8 × Fin ((2 * w) ^ 3) => tprod (Q d L' L' : Tensor K _ _ _)
        (mm (u * (u * Λ * x)) (u * (u * Λ * x)) (u * (u * Λ * x))))
      (dsum fun _ : Fin (64 * w ^ 3) =>
        tprod (Q d L' L' : Tensor K _ _ _) (mm (w ^ 2 * x) (w ^ 2 * x) (w ^ 2 * x))) :=
    (IsRestriction.dsum fun _ => IsRestriction.tprod (IsRestriction.refl _)
      (isRestriction_mm_of_le hle)).trans
      (isRestriction_dsum_const_of_card_le (le_of_eq (by simp [Fintype.card_prod]; ring)) _)
  refine ⟨_, IsRestriction.trans_isDegen (IsRestriction.dsum fun _ => IsRestriction.tprod
    (IsRestriction.refl _) (isRestriction_mm_of_eq (by ring) (by ring) (by ring)))
    ((hA.trans_isRestriction hmid).trans (hB'.trans_isRestriction hend))⟩

end CommRing

section Field

variable [Field K] [CharZero K]

/-- **Rank of `Q`** ([Pass][Pass2026], Lemma 4.1 and Lemma 2.3): each of the `6 d` factors has
rank at most `a + b - 1`. -/
theorem rank_Q (d a b : ℕ) : Rank ((a + b - 1) ^ (6 * d)) (Q d a b : Tensor K _ _ _) := by
  have hc : Rank ((a + b - 1) ^ d * (a + b - 1) ^ d) (canonical d a b : Tensor K _ _ _) :=
    ((rank_full a b).tpow d).tprod ((rank_mid a b).tpow d)
  refine (hc.tprod (hc.swap12.tprod hc.swap13)).mono (le_of_eq ?_)
  ring

/-- **From the primal packing to a column packing** ([Pass][Pass2026], Theorem 3.1, Lemma 3.2
and Lemma 3.4): for `a, b, t ≥ 1`, `c t ≥ a + 2 b - 1` and any `h` (only `h ≤ d` gives a
nonempty packing), with `w₀` the number of words `Fin d → Fin (c + 2)` whose number of letters
equal to the middle letter `c + 1` is `h`,
there is a column packing from length `b + t` to length `b` with `w = w₀ ^ 2` and
`u = c ^ (2 d)`. -/
theorem columnPacking_of_count {a b c t d h : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (ht : 1 ≤ t)
    (hc : a + 2 * b - 1 ≤ c * t) :
    ColumnPacking (K := K) d a b (b + t)
      ((univ.filter fun w : Fin d → Fin (c + 2) =>
        (univ.filter fun i => w i = Fin.last (c + 1)).card = h).card ^ 2) (c ^ (2 * d))
      ((univ.filter fun w : Fin d → Fin (c + 2) =>
        (univ.filter fun i => w i = Fin.last (c + 1)).card = h).card ^ 2 * (2 * d) +
        (univ.filter fun w : Fin d → Fin (c + 2) =>
          (univ.filter fun i => w i = Fin.last (c + 1)).card = h).card ^ 2 - 1) := by
  classical
  -- the primal packing, with its targets written as `fullOrMid`
  have hprim := isSLDegen_primal (K := K) ha hb ht hc
  have hT : primalTargets (K := K) a b c = fullOrMid (K := K) a b {Fin.last (c + 1)} := by
    funext j
    by_cases hj : j = Fin.last (c + 1)
    · subst hj
      simp [primalTargets, fullOrMid]
    · have hjc : j.val ≤ c := by
        have := j.isLt
        have := Fin.val_ne_of_ne hj
        rw [Fin.val_last] at this
        omega
      simp [primalTargets, fullOrMid, hj, hjc]
  rw [hT] at hprim
  -- amplify, and keep the balanced pairs of words, numbered by `Fin (w₀ ^ 2)`
  set W := univ.filter fun w : Fin d → Fin (c + 2) =>
    (univ.filter fun i => w i = Fin.last (c + 1)).card = h with hW
  let e : Fin (W.card ^ 2) ≃ W × W :=
    (Fintype.equivFinOfCardEq (by simp [Fintype.card_prod, sq])).symm
  have hres := (hprim.amplify d).slSum_comp (fun i => ((e i).1.1, (e i).2.1)) fun i j hij =>
    e.injective (Prod.ext (Subtype.ext (congrArg Prod.fst hij))
      (Subtype.ext (congrArg Prod.snd hij)))
  choose E hE using fun i : Fin (W.card ^ 2) =>
    exists_reindex_eq_canonical (K := K) a b {Fin.last (c + 1)} (e i).1.1 (e i).2.1
      (by simpa using (Finset.mem_filter.1 (e i).1.2).2)
      (by simpa using (Finset.mem_filter.1 (e i).2.2).2)
  -- separate the left inputs
  have hsep := hres.separate
  rw [mul_one] at hsep
  refine IsRestriction.trans_isDegen ?_ (hsep.trans_isRestriction ?_)
  · refine IsRestriction.dsum fun i => IsRestriction.tprod ?_ (IsRestriction.refl _)
    rw [Function.comp_apply, hE i]
    exact isRestriction_of_reindex _ _ _ _
  · exact isRestriction_dsum_const_of_card_le (by simp) _

/-! ### Iterating rounds and the finite identity -/

/-- The length after one round, for `c ≥ 2`: `L + ⌈(3 L - 1) / (c - 1)⌉`, so that
`c ⌈(3 L - 1) / (c - 1)⌉ ≥ 3 L - 1 + ⌈(3 L - 1) / (c - 1)⌉` ([Pass][Pass2026], proof of
Theorem 4.3). -/
def nextLength (c L : ℕ) : ℕ :=
  L + (3 * L - 1 + (c - 2)) / (c - 1)

/-- The lengths of the rounds: `L₀ = 1` and `L_{j+1} = nextLength c L_j`. -/
def roundLength (c : ℕ) : ℕ → ℕ
  | 0 => 1
  | j + 1 => nextLength c (roundLength c j)

/-- The shift of a round satisfies the primal packing's condition at both lengths. -/
theorem nextLength_spec {c L : ℕ} (hc : 2 ≤ c) (hL : 1 ≤ L) :
    1 ≤ nextLength c L - L ∧ L + 2 * L - 1 ≤ c * (nextLength c L - L) ∧
      nextLength c L + 2 * L - 1 ≤ c * (nextLength c L - L) := by
  obtain ⟨m, rfl⟩ : ∃ m, c = m + 2 := ⟨c - 2, by omega⟩
  have e₁ : m + 2 - 1 = m + 1 := by omega
  have e₂ : m + 2 - 2 = m := by omega
  simp only [nextLength, e₁, e₂, Nat.add_sub_cancel_left]
  have hdm := Nat.div_add_mod (3 * L - 1 + m) (m + 1)
  have hml := Nat.mod_lt (3 * L - 1 + m) (Nat.succ_pos m)
  have h2 : (m + 2) * ((3 * L - 1 + m) / (m + 1)) =
      (m + 1) * ((3 * L - 1 + m) / (m + 1)) + (3 * L - 1 + m) / (m + 1) := by ring
  rw [h2]
  generalize (3 * L - 1 + m) / (m + 1) = q at hdm h2 ⊢
  generalize (3 * L - 1 + m) % (m + 1) = r at hdm hml
  generalize hP : (m + 1) * q = P at hdm h2 ⊢
  have hq : 1 ≤ q := by
    rcases Nat.eq_zero_or_pos q with hq | hq
    · subst hq
      rw [mul_zero] at hP
      omega
    · exact hq
  omega

/-- **Iterated rounds** ([Pass][Pass2026], proof of Theorem 4.3): `k` rounds from `L₀ = 1` give a
degeneration of `64 ^ k w ^ 3` copies of `Q d L_k L_k ⊗ mm (w ^ 2) …` to `w ^ 3` copies of
`Q d 1 1 ⊗ mm (w ^ 2 Λ ^ k) …`, hence a degeneration of `unit (64 ^ k w ^ 9 (2 L_k - 1) ^ (6 d))`
to `mm v v v` with `v = w ^ 2 Λ ^ k`. -/
theorem isDegen_mm_unit_of_rounds {c d w u H Λ : ℕ} (hw : 1 ≤ w)
    (hpack : ∀ L, 1 ≤ L → ColumnPacking (K := K) d L L (nextLength c L) w u H ∧
      ColumnPacking (K := K) d (nextLength c L) L (nextLength c L) w u H)
    (hΛ : u ^ 2 * Λ ≤ w ^ 2) (k : ℕ) :
    ∃ H', IsDegen H'
      (mm (w ^ 2 * Λ ^ k) (w ^ 2 * Λ ^ k) (w ^ 2 * Λ ^ k) : Tensor K _ _ _)
      (unit (64 ^ k * w ^ 9 * (2 * roundLength c k - 1) ^ (6 * d))) := by
  classical
  have hL : ∀ j, 1 ≤ roundLength c j := fun j => by
    induction j with
    | zero => exact le_rfl
    | succ j ih => exact ih.trans (Nat.le_add_right _ _)
  -- `j` rounds from `L₀ = 1`
  have key : ∀ j x, ∃ H', IsDegen H'
      (dsum fun _ : Fin (w ^ 3) => tprod (Q d 1 1 : Tensor K _ _ _)
        (mm (w ^ 2 * Λ ^ j * x) (w ^ 2 * Λ ^ j * x) (w ^ 2 * Λ ^ j * x)))
      (dsum fun _ : Fin (64 ^ j * w ^ 3) => tprod (Q d (roundLength c j) (roundLength c j))
        (mm (w ^ 2 * x) (w ^ 2 * x) (w ^ 2 * x))) := by
    intro j
    induction j with
    | zero =>
      intro x
      refine ⟨0, IsDegen.of_isRestriction ?_⟩
      exact (IsRestriction.dsum fun _ => IsRestriction.tprod (IsRestriction.refl _)
        (isRestriction_mm_of_eq (by ring) (by ring) (by ring))).trans
        (isRestriction_dsum_const_of_card_le (by simp) _)
    | succ j ih =>
      intro x
      obtain ⟨H₁, h₁⟩ := ih (Λ * x)
      obtain ⟨H₂, h₂⟩ := isDegen_round (hpack _ (hL j)).1 (hpack _ (hL j)).2 hΛ x
      have h₃ := IsDegen.dsum fun _ : Fin (64 ^ j) => h₂
      rw [dsum_dsum, dsum_dsum] at h₃
      have h₄ := h₃.of_reindex_target.of_reindex_source
      refine ⟨_, IsRestriction.trans_isDegen (IsRestriction.dsum fun _ => IsRestriction.tprod
        (IsRestriction.refl _) (isRestriction_mm_of_eq (by ring) (by ring) (by ring)))
        ((h₁.trans_isRestriction ?_).trans (h₄.trans_isRestriction ?_))⟩
      · exact (IsRestriction.dsum fun _ => IsRestriction.tprod (IsRestriction.refl _)
          (isRestriction_mm_of_eq (by ring) (by ring) (by ring))).trans
          (isRestriction_dsum_const_of_card_le (le_of_eq (by simp)) _)
      · exact isRestriction_dsum_const_of_card_le
          (le_of_eq (by simp [Fintype.card_prod]; ring)) _
  obtain ⟨H', hk⟩ := key k 1
  refine ⟨H', IsRestriction.trans_isDegen ?_ (hk.trans_isRestriction ?_)⟩
  · refine (isRestriction_mm_tprod_Q_one d _ _ _).trans ?_
    refine IsRestriction.trans ?_ (isRestriction_dsum_const ⟨0, Nat.pow_pos hw⟩ _)
    exact IsRestriction.tprod (IsRestriction.refl _)
      (isRestriction_mm_of_eq (by ring) (by ring) (by ring))
  · have := Rank.dsum (64 ^ k * w ^ 3)
      (Rank.tprod (rank_Q (K := K) d (roundLength c k) (roundLength c k))
        (rank_mm (R := K) (w ^ 2 * 1) (w ^ 2 * 1) (w ^ 2 * 1)))
    refine this.mono (le_of_eq ?_)
    rw [show roundLength c k + roundLength c k - 1 = 2 * roundLength c k - 1 by omega]
    ring

/-! ### The parameters -/

/-- A geometric sequence with ratio below one, times a linear factor, eventually drops below any
other geometric sequence: `C (D m + 1) a ^ m < b ^ m` for some `m ≥ 1` when `0 ≤ a < b`. -/
private theorem exists_lt_pow_of_lt {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (C D : ℝ) :
    ∃ m : ℕ, 1 ≤ m ∧ C * (D * m + 1) * a ^ m < b ^ m := by
  have hb : 0 < b := ha.trans_lt hab
  have hq0 : 0 ≤ a / b := div_nonneg ha hb.le
  have hq1 : a / b < 1 := (div_lt_one hb).2 hab
  have h1 : Filter.Tendsto (fun m : ℕ => C * (D * m + 1) * (a / b) ^ m) Filter.atTop
      (nhds 0) := by
    have := ((tendsto_self_mul_const_pow_of_lt_one hq0 hq1).const_mul (C * D)).add
      ((tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).const_mul C)
    simp only [mul_zero, add_zero] at this
    exact this.congr fun m => by ring
  obtain ⟨m, hm, hm1⟩ :=
    ((h1.eventually_lt_const one_pos).and (Filter.eventually_ge_atTop 1)).exists
  refine ⟨m, hm1, ?_⟩
  rwa [div_pow, ← mul_div_assoc, div_lt_one (pow_pos hb m)] at hm

/-- The growth factor of the lengths of the rounds, `ρ = 1 + 3 / (c - 1)`
([Pass][Pass2026], proof of Theorem 4.3). -/
private noncomputable def rho (c : ℕ) : ℝ := 1 + 3 / ((c : ℝ) - 1)

private theorem one_lt_sub_one {c : ℕ} (hc : 2 ≤ c) : (0 : ℝ) < (c : ℝ) - 1 := by
  have : (2 : ℝ) ≤ c := by exact_mod_cast hc
  linarith

private theorem rho_nonneg {c : ℕ} (hc : 2 ≤ c) : 0 ≤ rho c :=
  add_nonneg zero_le_one (div_nonneg (by norm_num) (one_lt_sub_one hc).le)

private theorem one_le_rho {c : ℕ} (hc : 2 ≤ c) : 1 ≤ rho c :=
  le_add_of_nonneg_right (div_nonneg (by norm_num) (one_lt_sub_one hc).le)

/-- One round increases the length by at most the factor `ρ`, plus one. -/
private theorem nextLength_le {c L : ℕ} (hc : 2 ≤ c) (hL : 1 ≤ L) :
    (nextLength c L : ℝ) ≤ rho c * L + 1 := by
  have hc1 := one_lt_sub_one hc
  have h1 : ((3 * L - 1 + (c - 2) : ℕ) : ℝ) = 3 * L + c - 3 := by
    rw [show 3 * L - 1 + (c - 2) = 3 * L + c - 3 by omega, Nat.cast_sub (by omega)]
    push_cast
    ring
  have h2 : ((c - 1 : ℕ) : ℝ) = c - 1 := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  have h3 : (((3 * L - 1 + (c - 2)) / (c - 1) : ℕ) : ℝ) ≤
      ((3 * L - 1 + (c - 2) : ℕ) : ℝ) / ((c - 1 : ℕ) : ℝ) := Nat.cast_div_le
  rw [h1, h2] at h3
  rw [nextLength, Nat.cast_add, rho]
  calc (L : ℝ) + (((3 * L - 1 + (c - 2)) / (c - 1) : ℕ) : ℝ)
      ≤ L + (3 * L + c - 3) / ((c : ℝ) - 1) := by linarith
    _ = (1 + 3 / ((c : ℝ) - 1)) * L + 1 - 2 / ((c : ℝ) - 1) := by
      field_simp
      ring
    _ ≤ (1 + 3 / ((c : ℝ) - 1)) * L + 1 := by
      have : 0 ≤ 2 / ((c : ℝ) - 1) := div_nonneg (by norm_num) hc1.le
      linarith

/-- The lengths of the rounds grow at most geometrically:
`L_j ≤ ((c + 2) / 3) ρ ^ j - (c - 1) / 3`. -/
private theorem roundLength_le {c : ℕ} (hc : 2 ≤ c) (j : ℕ) :
    (roundLength c j : ℝ) ≤ ((c : ℝ) + 2) / 3 * rho c ^ j - ((c : ℝ) - 1) / 3 := by
  have hc1 := one_lt_sub_one hc
  have hρ : rho c * ((c : ℝ) - 1) / 3 = ((c : ℝ) - 1) / 3 + 1 := by
    rw [rho]
    field_simp
  have hL : ∀ j, 1 ≤ roundLength c j := fun j => by
    induction j with
    | zero => exact le_rfl
    | succ j ih => exact ih.trans (Nat.le_add_right _ _)
  induction j with
  | zero =>
    rw [roundLength, pow_zero, mul_one]
    push_cast
    linarith
  | succ j ih =>
    rw [roundLength]
    refine (nextLength_le hc (hL j)).trans ?_
    have := mul_le_mul_of_nonneg_left ih (rho_nonneg hc)
    rw [pow_succ]
    nlinarith [hρ, this]

/-- The choice of `c` ([Pass][Pass2026], Corollary 4.4): for `τ > 9/4`,
`6 log ρ < 4 τ log (1 + 2 / c)` for large `c`, since `log ρ ≤ 3 / (c - 1)` and
`log (1 + 2 / c) ≥ 2 / (c + 2)`. -/
private theorem exists_c {τ : ℝ} (hτ : 9 / 4 < τ) :
    ∃ c : ℕ, 2 ≤ c ∧ 6 * Real.log (rho c) < 4 * τ * Real.log (1 + 2 / (c : ℝ)) := by
  have h18 : 0 < 8 * τ - 18 := by linarith
  refine ⟨⌈(8 * τ + 36) / (8 * τ - 18)⌉₊ + 2, by omega, ?_⟩
  set c : ℕ := ⌈(8 * τ + 36) / (8 * τ - 18)⌉₊ + 2 with hc
  have hcR : (8 * τ + 36) / (8 * τ - 18) < c := by
    rw [hc]
    push_cast
    linarith [Nat.le_ceil ((8 * τ + 36) / (8 * τ - 18))]
  have hc2 : (2 : ℝ) ≤ c := by
    rw [hc]
    push_cast
    linarith [Nat.cast_nonneg (α := ℝ) ⌈(8 * τ + 36) / (8 * τ - 18)⌉₊]
  have hc1 : (0 : ℝ) < (c : ℝ) - 1 := by linarith
  have hc0 : (0 : ℝ) < c := by linarith
  have hc0' : (c : ℝ) ≠ 0 := hc0.ne'
  have hc2' : (c : ℝ) + 2 ≠ 0 := by linarith
  have hl : Real.log (rho c) ≤ 3 / ((c : ℝ) - 1) := by
    have := Real.log_le_sub_one_of_pos (x := rho c)
      (add_pos one_pos (div_pos (by norm_num) hc1))
    simp only [rho] at this ⊢
    linarith
  have hr : 2 / ((c : ℝ) + 2) ≤ Real.log (1 + 2 / c) := by
    have := Real.one_sub_inv_le_log_of_pos (x := 1 + 2 / (c : ℝ)) (by positivity)
    refine le_trans (le_of_eq ?_) this
    field_simp
    ring
  have key : 18 / ((c : ℝ) - 1) < 8 * τ / ((c : ℝ) + 2) := by
    rw [div_lt_div_iff₀ hc1 (by linarith)]
    have := (div_lt_iff₀ h18).1 hcR
    nlinarith
  calc 6 * Real.log (rho c) ≤ 6 * (3 / ((c : ℝ) - 1)) := by linarith
    _ = 18 / ((c : ℝ) - 1) := by ring
    _ < 8 * τ / ((c : ℝ) + 2) := key
    _ = 4 * τ * (2 / ((c : ℝ) + 2)) := by ring
    _ ≤ 4 * τ * Real.log (1 + 2 / c) := mul_le_mul_of_nonneg_left hr (by linarith)

/-- The choice of `d` ([Pass][Pass2026], proof of Theorem 4.3): once `c` is fixed, for large
`d` the words outnumber `(d + 1) c ^ d`, and the loss `4 τ log (2 (d + 1))` of the floor and the
counting, together with the `64` of the round, is absorbed by the gain `4 τ d log (1 + 2/c) -
6 d log ρ`, which is linear in `d`. -/
private theorem exists_d {c : ℕ} (hc : 2 ≤ c) {τ : ℝ}
    (hlam : 6 * Real.log (rho c) < 4 * τ * Real.log (1 + 2 / (c : ℝ))) :
    ∃ d : ℕ, 1 ≤ d ∧ ((d : ℝ) + 1) * (c : ℝ) ^ d < ((c : ℝ) + 2) ^ d ∧
      Real.log 64 + 6 * d * Real.log (rho c) + 4 * τ * Real.log (2 * (d + 1)) <
        4 * τ * d * Real.log (1 + 2 / (c : ℝ)) := by
  have hc0 : (0 : ℝ) < c := by exact_mod_cast (by omega : 0 < c)
  set σ := Real.log (1 + 2 / (c : ℝ)) with hσ
  set ρ := Real.log (rho c)
  have hσ0 : 0 < σ := by
    rw [hσ]
    apply Real.log_pos
    have : 0 < 2 / (c : ℝ) := by positivity
    linarith
  -- `log (d + 1) / d → 0`
  have h1 : Filter.Tendsto (fun d : ℕ => Real.log (d + 1) / d) Filter.atTop (nhds 0) := by
    have := (Real.tendsto_pow_log_div_mul_add_atTop 1 (-1) 1 one_ne_zero).comp
      (Filter.tendsto_atTop_add_const_right _ (1 : ℝ) tendsto_natCast_atTop_atTop)
    refine this.congr fun d => ?_
    simp only [Function.comp_apply, pow_one]
    congr 1
    ring
  have h2 : Filter.Tendsto (fun d : ℕ =>
      (Real.log 64 + 4 * τ * Real.log 2) / d + 4 * τ * (Real.log (d + 1) / d))
      Filter.atTop (nhds 0) := by
    have := (tendsto_const_div_atTop_nhds_zero_nat (Real.log 64 + 4 * τ * Real.log 2)).add
      (h1.const_mul (4 * τ))
    simpa using this
  have hlam' : 0 < 4 * τ * σ - 6 * ρ := by linarith
  obtain ⟨d, ⟨hd1, hd2⟩, hd⟩ :=
    (((h1.eventually_lt_const hσ0).and (h2.eventually_lt_const hlam')).and
      (Filter.eventually_ge_atTop 1)).exists
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  refine ⟨d, hd, ?_, ?_⟩
  · rw [div_lt_iff₀ hd0, mul_comm, ← Real.log_pow] at hd1
    have := (Real.log_lt_log_iff (by positivity) (by positivity)).1 hd1
    rwa [one_add_div hc0.ne', div_pow, lt_div_iff₀ (by positivity)] at this
  · have e : (Real.log 64 + 4 * τ * Real.log 2) / d + 4 * τ * (Real.log (d + 1) / d) =
        (Real.log 64 + 4 * τ * Real.log 2 + 4 * τ * Real.log (d + 1)) / d := by ring
    rw [e, div_lt_iff₀ hd0] at hd2
    rw [Real.log_mul two_ne_zero (by positivity)]
    nlinarith [hd2]

/-- **The finite identity** ([Pass][Pass2026], Theorem 4.3 and Corollary 4.4): for every
`τ > 9/4` there is a side `v ≥ 2` and an exact bilinear algorithm for `v × v` matrix
multiplication with fewer than `v ^ τ` multiplications.

The parameters: `c` from `exists_c`, `d` from `exists_d`, the number `h` of middle letters from
`exists_card_filter_count_ge`, `w = w₀ ^ 2`, `u = c ^ (2 d)`, `Λ = ⌊w₀ / c ^ d⌋ ^ 4`, so that
`64 ρ ^ (6 d) < Λ ^ τ`; then `k` rounds give a degeneration of `unit r'` to `mm V V V` with
`r' < V ^ τ`, and Bini's conversion gives the exact algorithm for a tensor power. -/
theorem exists_rank_mm_lt_rpow {τ : ℝ} (hτ : 9 / 4 < τ) :
    ∃ v r : ℕ, 2 ≤ v ∧ (r : ℝ) < (v : ℝ) ^ τ ∧ Rank r (mm v v v : Tensor K _ _ _) := by
  classical
  have hτ0 : 0 < τ := by linarith
  obtain ⟨c, hc, hlam⟩ := exists_c hτ
  obtain ⟨d, hd, hd1, hd2⟩ := exists_d hc hlam
  have hc0 : (0 : ℝ) < c := by exact_mod_cast (by omega : 0 < c)
  have hc0' : (c : ℝ) ≠ 0 := hc0.ne'
  have hρ0 := rho_nonneg hc
  -- the balanced words
  obtain ⟨h, -, hcount⟩ := exists_card_filter_count_ge (c + 2) d {Fin.last (c + 1)}
  simp only [Finset.mem_singleton] at hcount
  set w₀ := (univ.filter fun w : Fin d → Fin (c + 2) =>
    (univ.filter fun i => w i = Fin.last (c + 1)).card = h).card with hw₀
  have hcountR : ((c : ℝ) + 2) ^ d ≤ ((d : ℝ) + 1) * w₀ := by exact_mod_cast hcount
  have hw₀c : c ^ d < w₀ := by
    have : ((d : ℝ) + 1) * (c : ℝ) ^ d < ((d : ℝ) + 1) * w₀ := hd1.trans_le hcountR
    exact_mod_cast lt_of_mul_lt_mul_left this (by positivity)
  -- the parameters `w`, `u`, `Λ`
  set y := w₀ / c ^ d with hy
  have hcd : 0 < c ^ d := Nat.pow_pos (by omega)
  have hy1 : 1 ≤ y := (Nat.le_div_iff_mul_le hcd).2 (by simpa using hw₀c.le)
  have hy2 : w₀ < (y + 1) * c ^ d := (Nat.div_lt_iff_lt_mul hcd).1 (Nat.lt_succ_self _)
  set w := w₀ ^ 2 with hw
  set u := c ^ (2 * d) with hu
  set Λ := y ^ 4 with hΛdef
  have hw1 : 1 ≤ w := Nat.one_le_pow _ _ (by omega)
  have hΛ : u ^ 2 * Λ ≤ w ^ 2 := by
    calc u ^ 2 * Λ = (y * c ^ d) ^ 4 := by rw [hu, hΛdef]; ring
      _ ≤ w₀ ^ 4 := Nat.pow_le_pow_left (Nat.div_mul_le_self _ _) 4
      _ = w ^ 2 := by rw [hw]; ring
  set H := w * (2 * d) + w - 1 with hH
  -- the column packings of every round
  have hpack : ∀ L, 1 ≤ L → ColumnPacking (K := K) d L L (nextLength c L) w u H ∧
      ColumnPacking (K := K) d (nextLength c L) L (nextLength c L) w u H := by
    intro L hL
    obtain ⟨ht, h1, h2⟩ := nextLength_spec hc hL
    have hle : L ≤ nextLength c L := Nat.le_add_right _ _
    constructor
    · have := columnPacking_of_count (K := K) (d := d) (h := h) hL hL ht h1
      rwa [Nat.add_sub_cancel' hle] at this
    · have := columnPacking_of_count (K := K) (d := d) (h := h) (hL.trans hle) hL ht h2
      rwa [Nat.add_sub_cancel' hle] at this
  -- `64 ρ ^ (6 d) < Λ ^ τ`
  set σ := Real.log (1 + 2 / (c : ℝ)) with hσ
  have hσ' : σ = Real.log ((c : ℝ) + 2) - Real.log c := by
    rw [hσ, one_add_div hc0', Real.log_div (by linarith) hc0']
  have hy1R : (1 : ℝ) ≤ y := by exact_mod_cast hy1
  have hy0 : (0 : ℝ) < y := by linarith
  have hρpos : 0 < rho c := lt_of_lt_of_le one_pos (one_le_rho hc)
  have hlogy : d * σ - Real.log (2 * (d + 1)) < Real.log y := by
    have hlt : ((c : ℝ) + 2) ^ d < 2 * ((d : ℝ) + 1) * y * (c : ℝ) ^ d := by
      have h1 : (w₀ : ℝ) < (y + 1) * (c : ℝ) ^ d := by exact_mod_cast hy2
      have h2 : (y : ℝ) + 1 ≤ 2 * y := by linarith
      have h3 : (0 : ℝ) < (c : ℝ) ^ d := by positivity
      have h4 : (0 : ℝ) ≤ (d : ℝ) + 1 := by positivity
      nlinarith [mul_le_mul_of_nonneg_right h2 h3.le,
        mul_lt_mul_of_pos_left h1 (by positivity : (0 : ℝ) < d + 1)]
    have := Real.log_lt_log (by positivity) hlt
    rw [Real.log_pow, Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_pow,
      Real.log_mul two_ne_zero (by positivity)] at this
    rw [hσ', Real.log_mul two_ne_zero (by positivity)]
    nlinarith [this]
  have hΛτ : 64 * rho c ^ (6 * d) < (Λ : ℝ) ^ τ := by
    have hΛR : (Λ : ℝ) = (y : ℝ) ^ 4 := by rw [hΛdef]; push_cast; ring
    rw [← Real.log_lt_log_iff (mul_pos (by norm_num) (pow_pos hρpos _)) (by rw [hΛR]; positivity),
      Real.log_rpow (by rw [hΛR]; positivity), hΛR, Real.log_pow,
      Real.log_mul (by norm_num) (pow_pos hρpos _).ne', Real.log_pow]
    have := mul_lt_mul_of_pos_left hlogy (by positivity : (0 : ℝ) < 4 * τ)
    push_cast
    nlinarith [hd2, this]
  have hΛ2 : 2 ≤ Λ := by
    rcases Nat.lt_or_ge Λ 2 with hcon | hcon
    · exfalso
      have h1 : (Λ : ℝ) ≤ 1 := by exact_mod_cast Nat.lt_succ_iff.1 hcon
      have h2 : (Λ : ℝ) ^ τ ≤ 1 := Real.rpow_le_one (Nat.cast_nonneg _) h1 hτ0.le
      have h3 : (1 : ℝ) ≤ rho c ^ (6 * d) := one_le_pow₀ (one_le_rho hc)
      linarith
    · exact hcon
  -- the number of rounds
  have hw0 : (0 : ℝ) < w := by exact_mod_cast hw1
  obtain ⟨k, hk1, hk⟩ := exists_lt_pow_of_lt (mul_nonneg (by norm_num) (pow_nonneg hρ0 _)) hΛτ
    ((w : ℝ) ^ 9 * (2 * ((c : ℝ) + 2) / 3) ^ (6 * d) / (w : ℝ) ^ (2 * τ)) 0
  simp only [zero_mul, zero_add, mul_one] at hk
  rw [div_mul_eq_mul_div, div_lt_iff₀ (Real.rpow_pos_of_pos hw0 _)] at hk
  set V := w ^ 2 * Λ ^ k with hV
  set r' := 64 ^ k * w ^ 9 * (2 * roundLength c k - 1) ^ (6 * d) with hr'
  have hL : ∀ j, 1 ≤ roundLength c j := fun j => by
    induction j with
    | zero => exact le_rfl
    | succ j ih => exact ih.trans (Nat.le_add_right _ _)
  have hr'V : (r' : ℝ) < (V : ℝ) ^ τ := by
    have hLk : ((2 * roundLength c k - 1 : ℕ) : ℝ) ≤ 2 * ((c : ℝ) + 2) / 3 * rho c ^ k := by
      have h1 : ((2 * roundLength c k - 1 : ℕ) : ℝ) ≤ 2 * (roundLength c k : ℝ) := by
        exact_mod_cast Nat.sub_le _ _
      have h2 := roundLength_le hc k
      have h3 : (0 : ℝ) ≤ ((c : ℝ) - 1) / 3 := div_nonneg (one_lt_sub_one hc).le (by norm_num)
      nlinarith
    have hVR : (V : ℝ) ^ τ = (w : ℝ) ^ (2 * τ) * ((Λ : ℝ) ^ τ) ^ k := by
      rw [hV]
      push_cast
      rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast_mul (by positivity),
        ← Real.rpow_natCast_mul (by positivity), mul_comm (k : ℝ),
        Real.rpow_mul_natCast (by positivity)]
      norm_num
    rw [hVR, hr']
    push_cast
    calc (64 : ℝ) ^ k * (w : ℝ) ^ 9 * ((2 * roundLength c k - 1 : ℕ) : ℝ) ^ (6 * d)
        ≤ 64 ^ k * (w : ℝ) ^ 9 * (2 * ((c : ℝ) + 2) / 3 * rho c ^ k) ^ (6 * d) := by
          gcongr
      _ = (w : ℝ) ^ 9 * (2 * ((c : ℝ) + 2) / 3) ^ (6 * d) * (64 * rho c ^ (6 * d)) ^ k := by
          rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul]
          ring
      _ < (w : ℝ) ^ (2 * τ) * ((Λ : ℝ) ^ τ) ^ k := hk.trans_eq (mul_comm _ _)
  -- the rounds and Bini's conversion
  obtain ⟨H', hdeg⟩ := isDegen_mm_unit_of_rounds (K := K) (c := c) hw1 hpack hΛ k
  obtain ⟨D, hrank⟩ := hdeg.exists_rank_tpow
  obtain ⟨m, hm1, hm⟩ := exists_lt_pow_of_lt (Nat.cast_nonneg r') hr'V 1 D
  rw [one_mul] at hm
  have hV2 : 2 ≤ V := by
    rw [hV]
    calc 2 ≤ 2 ^ k := Nat.le_self_pow (by omega) 2
      _ ≤ Λ ^ k := Nat.pow_le_pow_left hΛ2 k
      _ ≤ w ^ 2 * Λ ^ k := Nat.le_mul_of_pos_left _ (by positivity)
  refine ⟨V ^ m, (D * m + 1) * r' ^ m, (hV2.trans (Nat.le_self_pow (by omega) V)), ?_,
    Rank.of_isRestriction (isRestriction_mm_pow_tpow V m) (hrank m)⟩
  push_cast
  rw [← Real.rpow_natCast_mul (by positivity), mul_comm (m : ℝ),
    Real.rpow_mul_natCast (by positivity)]
  exact hm

end Field

end Cslib.Tensor
