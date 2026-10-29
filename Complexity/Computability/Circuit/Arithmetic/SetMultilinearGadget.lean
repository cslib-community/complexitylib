/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Arithmetic.SigmaPi
public import Complexity.Foundations.Data.MvPolynomial.SetMultilinearProjectionProd

/-!
# The product gadget of set-multilinearization

Gate simulation turns a formula into one computing its set-multilinear parts
[Forbes2024, Cor. 27]. A product gate `f = ∏ j, f j` is simulated by the *product gadget*
`SPFormula.mulGadget`, a formula computing the part `π_S(f)` of `f` on a set `S` of blocks from
formulas `g j T` computing the parts `π_T(f j)` of the factors. It writes out the expansion
`MvPolynomial.smProj_prod_eq_sum_sign` of `π_S(f)`:

`π_S(f) = A ∑_P ∑_{π ∈ Perm P} sgn π ∑_{Y ⊆ Z} (-1) ^ #Y ∏_{q ∈ orbits π}
  ∑_{j ∉ Y} u_j ^ #q ∏_{T ∈ q} π_T(f j)`,

where `P` runs over the set partitions of `S`, `Z` is the set of factors with constant term `0`,
`A` is the product of the other constant terms and `u_j` the inverse of the constant term of
`f j` (or `1` when it is `0`). It is `0` when `#S < #Z`. The scalars ride on the edges of the sum
gates. The gadget

* computes `π_S(f)` (`SPFormula.polynomial_mulGadget`);
* is syntactically set-multilinear on `S` when each `g j T` is on `T`
  (`SPFormula.isSetMultilinear_mulGadget`): each sum over `j` has children on the same union of
  the parts in an orbit, and the factors of each product sit on disjoint sets of blocks;
* has product-depth at most two more than the `g j T` (`SPFormula.productDepth_mulGadget_le`);
* has at most `gadgetCost d * (1 + card ι + ∑ j, w j)` nodes, when each `g j T` with `T ⊆ S` has at
  most `w j` (`SPFormula.nodeCount_mulGadget_le`). The factor `gadgetCost d` depends only on the
  number `d` of blocks, not on the fan-in of the product gate: the number of products of sums is
  at most `(d + 1) ^ d · d! · 2 ^ d` (set partitions, permutations, subsets of `Z`).

The formula is built from sum and product gates over finite sets of children
(`SPFormula.sumOn`, `SPFormula.prodOn`).

## Main definitions

* `Cslib.Circuits.Arithmetic.SPFormula.sumOn`, `Cslib.Circuits.Arithmetic.SPFormula.prodOn`: sum
  and product gates over the formulas indexed by a finite set.
* `Cslib.Circuits.Arithmetic.SPFormula.mulGadget`: the product gadget.
* `Cslib.Circuits.Arithmetic.SPFormula.gadgetCost`: its size factor
  `2 * (2 * (d + 1) ^ 2) ^ (d + 1)`.

## Main results

* `Cslib.Circuits.Arithmetic.SPFormula.polynomial_mulGadget`,
  `Cslib.Circuits.Arithmetic.SPFormula.isSetMultilinear_mulGadget`,
  `Cslib.Circuits.Arithmetic.SPFormula.productDepth_mulGadget_le`,
  `Cslib.Circuits.Arithmetic.SPFormula.nodeCount_mulGadget_le`: the four properties above.

## References

* [M. A. Forbes, *Low-depth algebraic circuit lower bounds over any field*][Forbes2024], Lemma 26
  and its proof, pp. 31:13–31:14. Forbes computes the surjective permanents of the proof by
  Corollary 22 (p. 31:12), reducing them to permanents by Lemma 21 (p. 31:12) and expanding those
  by the partition form of the Binet–Minc identity, Theorem 13 (p. 31:10). The gadget here uses
  instead inclusion–exclusion in place of Lemma 21 and the permutation form of the Binet–Minc
  identity in place of Theorem 13 (`Matrix.rectPermSurj_eq_sum_sign_prod_sameCycle`), and is
  original, as are its explicit size bound and the formulas `sumOn` and `prodOn`.
-/

@[expose] public section

namespace Cslib.Circuits.Arithmetic.SPFormula

open Finset MvPolynomial Equiv Equiv.Perm

variable {K : Type*} {n d : ℕ} {ι : Type*}

/-! ### Gates over finite sets -/

/-- The sum gate over the formulas `G i` for `i ∈ s`, with edge constants `c i`. -/
noncomputable def sumOn (s : Finset ι) (c : ι → K) (G : ι → SPFormula K n) : SPFormula K n :=
  add (fun j => c (s.equivFin.symm j)) fun j => G (s.equivFin.symm j)

/-- The product gate over the formulas `G i` for `i ∈ s`. -/
noncomputable def prodOn (s : Finset ι) (G : ι → SPFormula K n) : SPFormula K n :=
  mul fun j => G (s.equivFin.symm j)

section Gates

variable (s : Finset ι) (c : ι → K) (G : ι → SPFormula K n)

/-- A sum gate over a finite set computes the linear combination of its children. -/
theorem polynomial_sumOn [CommSemiring K] :
    (sumOn s c G).polynomial = ∑ i ∈ s, C (c i) * (G i).polynomial := by
  rw [sumOn, polynomial_add, ← sum_coe_sort s]
  exact s.equivFin.symm.sum_comp fun i : s => C (c i) * (G i).polynomial

/-- A product gate over a finite set computes the product of its children. -/
theorem polynomial_prodOn [CommSemiring K] :
    (prodOn s G).polynomial = ∏ i ∈ s, (G i).polynomial := by
  rw [prodOn, polynomial_mul, ← prod_coe_sort s]
  exact s.equivFin.symm.prod_comp fun i : s => (G i).polynomial

/-- A sum gate over a finite set has one node more than its children. -/
theorem nodeCount_sumOn : (sumOn s c G).nodeCount = ∑ i ∈ s, (G i).nodeCount + 1 := by
  rw [sumOn, Formula.nodeCount_gate, ← sum_coe_sort s]
  congr 1
  exact s.equivFin.symm.sum_comp fun i : s => (G i).nodeCount

/-- A product gate over a finite set has one node more than its children. -/
theorem nodeCount_prodOn : (prodOn s G).nodeCount = ∑ i ∈ s, (G i).nodeCount + 1 := by
  rw [prodOn, Formula.nodeCount_gate, ← sum_coe_sort s]
  congr 1
  exact s.equivFin.symm.sum_comp fun i : s => (G i).nodeCount

variable {s G}

/-- A sum gate does not add to the product-depth. -/
theorem productDepth_sumOn_le {p : ℕ} (h : ∀ i ∈ s, (G i).productDepth ≤ p) :
    (sumOn s c G).productDepth ≤ p := by
  rw [sumOn, productDepth_add]
  exact Finset.sup_le fun j _ => h _ (s.equivFin.symm j).2

/-- A product gate adds one to the product-depth. -/
theorem productDepth_prodOn_le {p : ℕ} (h : ∀ i ∈ s, (G i).productDepth ≤ p) :
    (prodOn s G).productDepth ≤ p + 1 := by
  rw [prodOn, productDepth_mul]
  exact Nat.add_le_add_right (Finset.sup_le fun j _ => h _ (s.equivFin.symm j).2) 1

/-- A sum gate over children set-multilinear on `S` is set-multilinear on `S`. -/
theorem isSetMultilinear_sumOn {blk : Fin n → Fin d} {S : Finset (Fin d)}
    (h : ∀ i ∈ s, (G i).IsSetMultilinear blk S) : (sumOn s c G).IsSetMultilinear blk S :=
  .add _ _ S fun j => h _ (s.equivFin.symm j).2

/-- A product gate over children set-multilinear on pairwise disjoint sets `T i` is
set-multilinear on their union. -/
theorem isSetMultilinear_prodOn {blk : Fin n → Fin d}
    {T : ι → Finset (Fin d)} (hT : (s : Set ι).PairwiseDisjoint T)
    (h : ∀ i ∈ s, (G i).IsSetMultilinear blk (T i)) :
    (prodOn s G).IsSetMultilinear blk (s.biUnion T) := by
  have hmul := IsSetMultilinear.mul (blk := blk) (fun j => G (s.equivFin.symm j))
    (fun j => T (s.equivFin.symm j))
    (fun j k hjk => hT (s.equivFin.symm j).2 (s.equivFin.symm k).2
      fun h => hjk (s.equivFin.symm.injective (Subtype.ext h)))
    fun j => h _ (s.equivFin.symm j).2
  rw [prodOn]
  convert hmul using 1
  ext x
  simp only [mem_biUnion, mem_univ, true_and]
  constructor
  · rintro ⟨i, hi, hx⟩
    exact ⟨s.equivFin ⟨i, hi⟩, by simpa using hx⟩
  · rintro ⟨j, hx⟩
    exact ⟨_, (s.equivFin.symm j).2, hx⟩

end Gates

/-! ### The product gadget -/

section Gadget

variable [Field K] [DecidableEq K] [Fintype ι] [DecidableEq ι]

/-- The factors with constant term `0`. -/
def mulGadget.zeroCols (a : ι → K) : Finset ι :=
  {j | a j = 0}

/-- The scale of a factor: the inverse of its constant term, or `1` if that is `0`. -/
def mulGadget.colScale (a : ι → K) (j : ι) : K :=
  if a j = 0 then 1 else (a j)⁻¹

open mulGadget

/-- **The product gadget** (original; it simulates a product gate as in [Forbes2024, Lemma 26]):
from formulas `g j T` for the parts on `T` of the factors of a product with constant terms `a j`,
the formula for the part on `S` of the product given by `MvPolynomial.smProj_prod_eq_sum_sign`,
or `0` if more than `#S` constant terms vanish. -/
noncomputable def mulGadget (S : Finset (Fin d)) (a : ι → K)
    (g : ι → Finset (Fin d) → SPFormula K n) : SPFormula K n :=
  if #S < #(zeroCols a) then zero else
    sumOn (univ : Finset (Finpartition S)) (fun _ => ∏ j ∈ (zeroCols a)ᶜ, a j) fun P =>
      sumOn (univ : Finset (Perm P.parts)) (fun π => ((sign π : ℤ) : K)) fun π =>
        sumOn (zeroCols a).powerset (fun Y => (-1) ^ #Y) fun Y =>
          prodOn (univ : Finset (Quotient (SameCycle.setoid π))) fun q =>
            sumOn Yᶜ (fun j => colScale a j ^ #{r | Quotient.mk _ r = q}) fun j =>
              prodOn {r | Quotient.mk _ r = q} fun r => g j r

variable {S : Finset (Fin d)} {a : ι → K} {g : ι → Finset (Fin d) → SPFormula K n}

/-- **The product gadget computes the part of the product** (original). -/
theorem polynomial_mulGadget {blk : Fin n → Fin d} {f : ι → MvPolynomial (Fin n) K}
    (ha : ∀ j, constantCoeff (f j) = a j) (hg : ∀ j T, (g j T).polynomial = smProj blk T (f j)) :
    (mulGadget S a g).polynomial = smProj blk S (∏ j, f j) := by
  have hZ (j : ι) : j ∈ zeroCols a ↔ constantCoeff (f j) = 0 := by
    rw [zeroCols, mem_filter, ha]
    exact and_iff_right (mem_univ j)
  rw [mulGadget]
  split_ifs with h
  · rw [polynomial_zero,
      smProj_prod_eq_zero_of_card_lt blk f (fun j hj => (hZ j).1 hj) h]
  · have hu₀ (j : ι) (hj : j ∈ zeroCols a) : colScale a j = 1 := by
      have hj' : a j = 0 := ha j ▸ (hZ j).1 hj
      simp only [colScale, hj', ↓reduceIte]
    have hu (j : ι) (hj : j ∉ zeroCols a) : colScale a j * constantCoeff (f j) = 1 := by
      have hj' : a j ≠ 0 := fun h' => hj ((hZ j).2 (h' ▸ ha j))
      simp only [colScale, hj', ↓reduceIte, ha]
      exact inv_mul_cancel₀ hj'
    rw [smProj_prod_eq_sum_sign blk S f hZ hu₀ hu]
    simp only [polynomial_sumOn, polynomial_prodOn, hg, ha, mul_sum]

/-- **The product gadget is set-multilinear on `S`** (original) when each `g j T` is
set-multilinear on `T`. -/
theorem isSetMultilinear_mulGadget {blk : Fin n → Fin d}
    (hg : ∀ j T, (g j T).IsSetMultilinear blk T) : (mulGadget S a g).IsSetMultilinear blk S := by
  rw [mulGadget]
  split_ifs
  · exact isSetMultilinear_zero S
  refine isSetMultilinear_sumOn _ fun P _ => isSetMultilinear_sumOn _ fun π _ =>
    isSetMultilinear_sumOn _ fun Y _ => ?_
  -- The rows of an orbit, as a set of blocks.
  let U : Quotient (SameCycle.setoid π) → Finset (Fin d) :=
    fun q => ({r | Quotient.mk (SameCycle.setoid π) r = q} : Finset P.parts).biUnion Subtype.val
  have hrows (q : Quotient (SameCycle.setoid π)) :
      Set.PairwiseDisjoint
        (({r | Quotient.mk (SameCycle.setoid π) r = q} : Finset P.parts) : Set P.parts)
        Subtype.val :=
    fun r _ r' _ hne => P.disjoint r.2 r'.2 (Subtype.coe_ne_coe.2 hne)
  have hU : (univ : Finset (Quotient (SameCycle.setoid π))).biUnion U = S := by
    refine Eq.trans ?_ P.biUnion_parts
    ext x
    simp only [U, mem_biUnion, mem_filter, mem_univ, true_and, id]
    constructor
    · rintro ⟨q, r, -, hx⟩
      exact ⟨r, r.2, hx⟩
    · rintro ⟨t, ht, hx⟩
      exact ⟨Quotient.mk _ ⟨t, ht⟩, ⟨t, ht⟩, rfl, hx⟩
  have hdisj : ((univ : Finset (Quotient (SameCycle.setoid π))) : Set _).PairwiseDisjoint U := by
    intro q _ q' _ hqq'
    refine (disjoint_biUnion_left _ _ _).2 fun r hr =>
      (disjoint_biUnion_right _ _ _).2 fun r' hr' => ?_
    have hne : r ≠ r' := by
      rintro rfl
      exact hqq' ((mem_filter.1 hr).2.symm.trans (mem_filter.1 hr').2)
    exact P.disjoint r.2 r'.2 (Subtype.coe_ne_coe.2 hne)
  refine (congrArg (IsSetMultilinear blk _) hU).mp ?_
  exact isSetMultilinear_prodOn hdisj fun q _ => isSetMultilinear_sumOn _ fun j _ =>
    isSetMultilinear_prodOn (hrows q) fun r _ => hg j r

/-- **The product gadget adds at most two to the product-depth** (original). -/
theorem productDepth_mulGadget_le {p : ℕ} (hg : ∀ j T, (g j T).productDepth ≤ p) :
    (mulGadget S a g).productDepth ≤ p + 2 := by
  rw [mulGadget]
  split_ifs
  · rw [productDepth_zero]
    exact Nat.zero_le _
  exact productDepth_sumOn_le _ fun P _ => productDepth_sumOn_le _ fun π _ =>
    productDepth_sumOn_le _ fun Y _ => productDepth_prodOn_le fun q _ =>
      productDepth_sumOn_le _ fun j _ => productDepth_prodOn_le fun r _ => hg j r

end Gadget

/-- The size factor of the product gadget on `d` blocks: `2 * (2 * (d + 1) ^ 2) ^ (d + 1)`. It
bounds `4 (d + 1)` times the number of products of sums, at most `(d + 1) ^ d · d! · 2 ^ d`. -/
def gadgetCost (d : ℕ) : ℕ :=
  2 * (2 * (d + 1) ^ 2) ^ (d + 1)

/-- The product of the counts of set partitions, permutations and subsets, with the slack of the
gadget, is at most `gadgetCost d`. -/
private theorem four_mul_le_gadgetCost (d : ℕ) :
    4 * ((d + 1) ^ d * (d.factorial * 2 ^ d)) * (d + 1) ≤ gadgetCost d := by
  have hf : d.factorial ≤ (d + 1) ^ d :=
    (Nat.factorial_le_pow d).trans (Nat.pow_le_pow_left (Nat.le_succ d) d)
  have h1 : 1 ≤ d + 1 := Nat.succ_pos d
  calc 4 * ((d + 1) ^ d * (d.factorial * 2 ^ d)) * (d + 1)
      ≤ 4 * ((d + 1) ^ d * ((d + 1) ^ d * 2 ^ d)) * (d + 1) := by gcongr
    _ ≤ 4 * ((d + 1) ^ d * ((d + 1) ^ d * 2 ^ d)) * (d + 1) * (d + 1) :=
        Nat.le_mul_of_pos_right _ h1
    _ = gadgetCost d := by
        rw [gadgetCost, mul_pow, ← pow_mul]
        ring

section Size

variable [Field K] [DecidableEq K] [Fintype ι] [DecidableEq ι]

open mulGadget

/-- **The size of the product gadget** (original): if each `g j T` with `T ⊆ S` has at most `w j`
nodes, the gadget has at most `gadgetCost d * (1 + card ι + ∑ j, w j)` nodes. -/
theorem nodeCount_mulGadget_le {S : Finset (Fin d)} {a : ι → K}
    {g : ι → Finset (Fin d) → SPFormula K n} {w : ι → ℕ}
    (hg : ∀ j T, T ⊆ S → (g j T).nodeCount ≤ w j) :
    (mulGadget S a g).nodeCount ≤ gadgetCost d * (1 + Fintype.card ι + ∑ j, w j) := by
  set m := Fintype.card ι
  set W := ∑ j, w j
  have hpos : 0 < gadgetCost d * (1 + m + W) :=
    Nat.mul_pos (by unfold gadgetCost; positivity) (by omega)
  rw [mulGadget]
  split_ifs with hZ
  · rw [nodeCount_zero]
    exact hpos
  have hSd : #S ≤ d := (card_le_univ S).trans_eq (Fintype.card_fin d)
  set τ := d * W + d * (m + 1) + 1
  -- The product over the orbits of a permutation of the parts of `P`.
  have hL3 (P : Finpartition S) (π : Perm P.parts) (Y : Finset ι) :
      (prodOn (univ : Finset (Quotient (SameCycle.setoid π))) fun q =>
        sumOn Yᶜ (fun j => colScale a j ^ #{r | Quotient.mk _ r = q}) fun j =>
          prodOn {r | Quotient.mk _ r = q} fun r => g j r).nodeCount ≤ τ := by
    have hk : #P.parts ≤ d := P.card_parts_le_card.trans hSd
    have hL5 (q : Quotient (SameCycle.setoid π)) (j : ι) :
        (prodOn ({r | Quotient.mk _ r = q} : Finset P.parts) fun r => g j r).nodeCount ≤
          #{r | Quotient.mk _ r = q} * w j + 1 := by
      rw [nodeCount_prodOn]
      refine Nat.add_le_add_right
        ((sum_le_sum fun (r : P.parts) _ => hg j r (P.le r.2)).trans ?_) 1
      rw [sum_const, smul_eq_mul]
    have hL4 (q : Quotient (SameCycle.setoid π)) :
        (sumOn Yᶜ (fun j => colScale a j ^ #{r | Quotient.mk _ r = q}) fun j =>
          prodOn {r | Quotient.mk _ r = q} fun r => g j r).nodeCount ≤
            #{r | Quotient.mk _ r = q} * W + (m + 1) := by
      rw [nodeCount_sumOn]
      calc _ ≤ ∑ j ∈ Yᶜ, (#{r | Quotient.mk _ r = q} * w j + 1) + 1 :=
            Nat.add_le_add_right (sum_le_sum fun j _ => hL5 q j) 1
        _ ≤ ∑ j, (#{r | Quotient.mk _ r = q} * w j + 1) + 1 :=
            Nat.add_le_add_right (sum_le_sum_of_subset (subset_univ _)) 1
        _ = _ := by
            rw [sum_add_distrib, ← mul_sum, sum_const, card_univ, smul_eq_mul, mul_one]
            ring
    rw [nodeCount_prodOn]
    have hfib : ∑ q : Quotient (SameCycle.setoid π), #{r | Quotient.mk _ r = q} = #P.parts := by
      have hc : #(univ : Finset P.parts) = #P.parts := by rw [card_univ, Fintype.card_coe]
      rw [← hc, card_eq_sum_card_fiberwise (f := Quotient.mk (SameCycle.setoid π))
          (t := univ) fun _ _ => mem_univ _]
    have hq : Fintype.card (Quotient (SameCycle.setoid π)) ≤ d :=
      (Fintype.card_quotient_le _).trans ((Fintype.card_coe _).trans_le hk)
    calc _ ≤ ∑ q : Quotient (SameCycle.setoid π),
          (#{r | Quotient.mk _ r = q} * W + (m + 1)) + 1 :=
          Nat.add_le_add_right (sum_le_sum fun q _ => hL4 q) 1
      _ = #P.parts * W + Fintype.card (Quotient (SameCycle.setoid π)) * (m + 1) + 1 := by
          rw [sum_add_distrib, ← sum_mul, hfib, sum_const, card_univ, smul_eq_mul]
      _ ≤ d * W + d * (m + 1) + 1 := by gcongr
  -- The sums over the subsets of `Z`, the permutations and the set partitions.
  have hL2 (P : Finpartition S) (π : Perm P.parts) :
      (sumOn (zeroCols a).powerset (fun Y => (-1 : K) ^ #Y) fun Y =>
        prodOn (univ : Finset (Quotient (SameCycle.setoid π))) fun q =>
          sumOn Yᶜ (fun j => colScale a j ^ #{r | Quotient.mk _ r = q}) fun j =>
            prodOn {r | Quotient.mk _ r = q} fun r => g j r).nodeCount ≤ 2 ^ d * τ + 1 := by
    rw [nodeCount_sumOn]
    refine Nat.add_le_add_right ((sum_le_sum fun Y _ => hL3 P π Y).trans ?_) 1
    rw [sum_const, card_powerset, smul_eq_mul]
    exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right two_pos ((not_lt.1 hZ).trans hSd))
  have hL1 (P : Finpartition S) :
      (sumOn (univ : Finset (Perm P.parts)) (fun π => ((sign π : ℤ) : K)) fun π =>
        sumOn (zeroCols a).powerset (fun Y => (-1 : K) ^ #Y) fun Y =>
          prodOn (univ : Finset (Quotient (SameCycle.setoid π))) fun q =>
            sumOn Yᶜ (fun j => colScale a j ^ #{r | Quotient.mk _ r = q}) fun j =>
              prodOn {r | Quotient.mk _ r = q} fun r => g j r).nodeCount ≤
        d.factorial * (2 ^ d * τ + 1) + 1 := by
    rw [nodeCount_sumOn]
    refine Nat.add_le_add_right ((sum_le_sum fun π _ => hL2 P π).trans ?_) 1
    rw [sum_const, card_univ, Fintype.card_perm, Fintype.card_coe, smul_eq_mul]
    exact Nat.mul_le_mul_right _
      (Nat.factorial_le (P.card_parts_le_card.trans hSd))
  rw [nodeCount_sumOn]
  have hB : Fintype.card (Finpartition S) ≤ (d + 1) ^ d :=
    (Fintype.card_finpartition_le S).trans <|
      (Nat.pow_le_pow_left (hSd.trans (Nat.le_succ d)) _).trans
        (Nat.pow_le_pow_right (Nat.succ_pos d) hSd)
  have hL0 := Nat.add_le_add_right ((sum_le_sum fun P _ => hL1 P).trans_eq
    (by rw [sum_const, card_univ, smul_eq_mul])) 1
  refine hL0.trans ?_
  -- Arithmetic.
  set B := Fintype.card (Finpartition S)
  set X := d.factorial * 2 ^ d
  have hX : 1 ≤ X := Nat.mul_pos (Nat.factorial_pos d) (Nat.two_pow_pos d)
  have hτ : τ ≤ (d + 1) * (1 + m + W) := by
    simp only [τ]
    nlinarith
  have hfac : d.factorial ≤ X * τ := (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos d)).trans
    (Nat.le_mul_of_pos_right _ (by omega))
  have hXτ : 1 ≤ X * τ := Nat.mul_pos hX (by omega)
  have hB1 : 1 ≤ B := Fintype.card_pos
  calc B * (d.factorial * (2 ^ d * τ + 1) + 1) + 1
      = B * (X * τ) + B * d.factorial + B + 1 := by simp only [X]; ring
    _ ≤ B * (X * τ) + B * (X * τ) + B * (X * τ) + B * (X * τ) := by
        have e1 : B * d.factorial ≤ B * (X * τ) := Nat.mul_le_mul_left _ hfac
        have e2 : B ≤ B * (X * τ) := Nat.le_mul_of_pos_right _ hXτ
        linarith
    _ = 4 * (B * X) * τ := by ring
    _ ≤ 4 * ((d + 1) ^ d * X) * ((d + 1) * (1 + m + W)) := by gcongr
    _ = 4 * ((d + 1) ^ d * X) * (d + 1) * (1 + m + W) := by ring
    _ ≤ gadgetCost d * (1 + m + W) := Nat.mul_le_mul_right _ (four_mul_le_gadgetCost d)

end Size

end Cslib.Circuits.Arithmetic.SPFormula
