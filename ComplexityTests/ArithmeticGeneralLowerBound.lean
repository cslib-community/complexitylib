/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

import Complexity.Computability.Circuit.Arithmetic.GeneralLowerBound

/-!
# Set-multilinearization and the lower bound for formulas over any field

The set-multilinear part of the formula `x₀ · (x₁ + 1)` on both blocks computes the
set-multilinear part `x₀ x₁` of its polynomial, with product-depth exactly two and at most
`smCost 2 * 5 = 116640` nodes. The part of `x₀ · (x₀ + 1)` on its one block has `17` nodes, against
the bound `smCost 1 * 5 = 1280`. The part of `x₀ · x₁` on one block is the formula `0`, since both
factors vanish at `0`.

The headline holds over every field, of any characteristic, with no set-multilinearity
hypothesis. At `d = 1331 = 11 ^ 3`, `Δ = 1`, `k = 614760` and `n ≥ 2 ^ k`, where
`d ^ (1 / (4 ^ Δ - 1)) = 11`, the left side exceeds `1`: the bound reads
`2 ^ 30738 ≤ smCost 1331 * nodeCount F` with `smCost 1331 ≤ 2 ^ 30638`, so every formula of
product-depth one computing `IMM_{n,1331}` has at least `2 ^ 100` nodes. This is far below the
trivial count of `n ^ 2` input leaves, one for each variable of a middle matrix. The bound beats
that count only when `d ^ (1 / (4 ^ Δ - 1)) > 50`: at `d = 132651 = 51 ^ 3`, `Δ = 1`,
`k = 98162880` and `n = 2 ^ k`, every such formula has more than `d n ^ 2` nodes. The hypotheses
are met by the sum over paths (`immFormula`). At small `d`, such as `d = 11` with `Δ = 1`, the
bound is trivial: `d ^ (1 / 3) < 10` makes the exponent negative.
-/

namespace ComplexityTests.ArithmeticGeneralLowerBound

open Cslib.Circuits Cslib.Circuits.Arithmetic Cslib.Circuits.Arithmetic.SPFormula MvPolynomial

/-! ### Set-multilinearization -/

/-- The formula `x₀ · (x₁ + 1)`, over two blocks of one variable each. -/
private noncomputable def F01 : SPFormula ℚ 2 :=
  .mul ![.input 0, add ![1, 1] ![.input 1, const 1]]

/-- A sum gate over a finite set is at least as deep as each of its children. -/
private theorem le_productDepth_sumOn {ι : Type*} {s : Finset ι} {c : ι → ℚ}
    {G : ι → SPFormula ℚ 2} {i : ι} (hi : i ∈ s) :
    (G i).productDepth ≤ (sumOn s c G).productDepth := by
  rw [sumOn, productDepth_add]
  simpa using Finset.le_sup (f := fun j => (G (s.equivFin.symm j)).productDepth)
    (Finset.mem_univ (s.equivFin ⟨i, hi⟩))

/-- A product gate over a finite set is deeper than each of its children. -/
private theorem lt_productDepth_prodOn {ι : Type*} {s : Finset ι} {G : ι → SPFormula ℚ 2} {i : ι}
    (hi : i ∈ s) : (G i).productDepth < (prodOn s G).productDepth := by
  rw [prodOn, productDepth_mul, Nat.lt_succ_iff]
  simpa using Finset.le_sup (f := fun j => (G (s.equivFin.symm j)).productDepth)
    (Finset.mem_univ (s.equivFin ⟨i, hi⟩))

/-- The constant terms of the factors of `x₀ · (x₁ + 1)` are `0` and `1`. -/
private theorem constantCoeff_F01_args (j : Fin 2) :
    constantCoeff (polynomial (![Formula.input 0, add ![1, 1] ![.input 1, const 1]] j :
      SPFormula ℚ 2)) = ![0, 1] j := by
  fin_cases j <;> simp [polynomial_add, polynomial_input, polynomial_const]

/-- The product of `x₀ · (x₁ + 1)` becomes the two levels of products of the gadget: the
set-multilinear part on both blocks has product-depth exactly `2 = 2 * F01.productDepth`. -/
example : (smPart (fun i : Fin 2 => i) Finset.univ F01).productDepth = 2 := by
  have hF : F01.productDepth = 1 := by simp [F01, productDepth_add]
  refine le_antisymm ((productDepth_smPart_le _ _).trans (by rw [hF])) ?_
  rw [F01, SPFormula.mul, smPart, mulGadget]
  split_ifs with hZ
  · exact absurd hZ (by simp only [mulGadget.zeroCols, constantCoeff_F01_args]; decide)
  have hr : ({0} : Finset (Fin 2)) ∈ (⊥ : Finpartition (Finset.univ : Finset (Fin 2))).parts := by
    simp [Finpartition.parts_bot]
  refine (le_productDepth_sumOn (Finset.mem_univ ⊥)).trans' <|
    (le_productDepth_sumOn (Finset.mem_univ 1)).trans' <|
    (le_productDepth_sumOn (Finset.empty_mem_powerset _)).trans' <|
    Nat.succ_le_of_lt <| (lt_productDepth_prodOn (Finset.mem_univ
      (Quotient.mk _ ⟨{0}, hr⟩))).trans_le' <|
    (le_productDepth_sumOn (i := 1) (by simp)).trans' <|
    Nat.succ_le_of_lt ((Nat.zero_le _).trans_lt (lt_productDepth_prodOn (i := ⟨{0}, hr⟩) (by simp)))

/-- On the two blocks, the size bound for `x₀ · (x₁ + 1)` evaluates to
`smCost 2 ^ 1 * 5 = 23328 * 5`. -/
example : (smPart (fun i : Fin 2 => i) Finset.univ F01).nodeCount ≤ 116640 := by
  have hF : F01.productDepth = 1 := by simp [F01, productDepth_add]
  refine (nodeCount_smPart_le _ _).trans_eq ?_
  rw [hF]
  simp [F01, smCost, gadgetCost]

/-- The formula `x₀ · (x₀ + 1)`, over one block of one variable. -/
private noncomputable def G1 : SPFormula ℚ 1 :=
  .mul ![.input 0, add ![1, 1] ![.input 0, const 1]]

/-- The set-multilinear part on the block of `x₀ · (x₀ + 1)` has `17` nodes: one set partition,
one permutation, the two subsets of the factor `x₀` with constant term `0`, and a product of sums
of products of the parts of the factors (`1` node for `x₀`, `3` for `x₀ + 1`). This is far below
the bound `smCost 1 ^ 1 * 5 = 1280`. -/
example : (smPart (fun i : Fin 1 => i) Finset.univ G1).nodeCount = 17 ∧
    smCost 1 ^ G1.productDepth * G1.nodeCount = 1280 := by
  have hG : G1.productDepth = 1 := by
    rw [G1, productDepth_mul, add_eq_right, ← Nat.le_zero, Finset.sup_le_iff]
    intro j _
    fin_cases j <;> simp [productDepth_add]
  refine ⟨?_, by rw [hG]; simp [G1, smCost, gadgetCost]⟩
  have ha (j : Fin 2) : constantCoeff (polynomial (![Formula.input 0, add ![1, 1]
      ![.input 0, const 1]] j : SPFormula ℚ 1)) = ![0, 1] j := by
    fin_cases j <;> simp [polynomial_add, polynomial_input, polynomial_const]
  have hg (j : Fin 2) (T : Finset (Fin 1)) : (smPart (fun i : Fin 1 => i) T
      (![Formula.input 0, add ![1, 1] ![.input 0, const 1]] j : SPFormula ℚ 1)).nodeCount =
      ![1, 3] j := by
    fin_cases j <;> simp [smPart, add] <;> split_ifs <;> rfl
  rw [G1, SPFormula.mul, smPart, mulGadget]
  split_ifs with hZ
  · exact absurd hZ (by simp only [mulGadget.zeroCols, ha]; decide)
  simp only [nodeCount_sumOn, nodeCount_prodOn, hg, Finset.sum_const, smul_eq_mul]
  have hZ0 : mulGadget.zeroCols (fun j => constantCoeff (polynomial (![Formula.input 0,
      add ![1, 1] ![.input 0, const 1]] j : SPFormula ℚ 1))) = {0} := by
    simp only [mulGadget.zeroCols, ha]
    decide
  have hAtom : IsAtom (Finset.univ : Finset (Fin 1)) := ⟨by decide, by decide⟩
  let : Unique (Finpartition (Finset.univ : Finset (Fin 1))) :=
    hAtom.uniqueFinpartition (P := ⊥)
  rw [hZ0, Fintype.sum_unique]
  set P : Finpartition (Finset.univ : Finset (Fin 1)) := default
  have hP : Subsingleton P.parts :=
    Finset.card_le_one_iff_subsingleton_coe.1 (P.card_parts_le_card.trans (by simp))
  obtain ⟨t, ht⟩ := P.parts_nonempty (by simp)
  have hr (r : P.parts) : r = ⟨t, ht⟩ := Subsingleton.elim _ _
  rw [Fintype.sum_subsingleton _ (1 : Equiv.Perm P.parts),
    show ({0} : Finset (Fin 2)).powerset = {∅, {0}} by decide, Finset.sum_pair (by decide),
    Fintype.sum_subsingleton _ (Quotient.mk _ ⟨t, ht⟩),
    Fintype.sum_subsingleton _ (Quotient.mk _ ⟨t, ht⟩), Finset.compl_empty,
    show ({0} : Finset (Fin 2))ᶜ = {1} by decide, Fin.sum_univ_two, Finset.sum_singleton,
    show ({r | ⟦r⟧ = ⟦⟨t, ht⟩⟧} : Finset P.parts) = {⟨t, ht⟩} by ext r; simp [hr r]]
  simp

/-- The part on both blocks of `x₀ · (x₁ + 1)` is `x₀ x₁`. -/
example : (smPart (fun i : Fin 2 => i) Finset.univ F01).polynomial = X 0 * X 1 := by
  have h01 : IsSetMultilinear (fun i : Fin 2 => i) Finset.univ (X 0 * X 1 : MvPolynomial _ ℚ) := by
    have h := (isSetMultilinear_X (K := ℚ) (fun i : Fin 2 => i) 0).mul
      (isSetMultilinear_X _ 1) (by decide)
    rwa [show ({0} ∪ {1} : Finset (Fin 2)) = Finset.univ by decide] at h
  have h0 : smProj (fun i : Fin 2 => i) Finset.univ (X 0 : MvPolynomial _ ℚ) = 0 := by
    rw [smProj_X, ite_eq_right (by decide)]
  simp only [polynomial_smPart, F01, polynomial_mul, polynomial_add, polynomial_input,
    polynomial_const, Fin.prod_univ_two, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, map_one, one_mul, mul_add, mul_one, smProj_add,
    h01.smProj_eq_self, h0, add_zero]

/-- The formula `x₀ · x₁`, over two blocks of one variable each. -/
private noncomputable def F11 : SPFormula ℚ 2 :=
  .mul ![.input 0, .input 1]

/-- Its part on one block is the formula `0`: both factors vanish at `0`, and `#{0} < 2`. -/
example : smPart (fun i : Fin 2 => i) {0} F11 = zero := by
  rw [F11, SPFormula.mul, smPart, mulGadget, ite_eq_left]
  have h (j : Fin 2) :
      constantCoeff (polynomial (![Formula.input 0, Formula.input 1] j : SPFormula ℚ 2)) = 0 := by
    fin_cases j <;> exact constantCoeff_X ℚ _
  simp only [mulGadget.zeroCols, h, Finset.filter_true, Finset.card_singleton, Finset.card_univ,
    Fintype.card_fin]
  decide

/-! ### The headline, nonvacuously -/

/-- The size factor for `d + 1 ≤ 2 ^ b`: `2 * (d + 1) ^ 2 ≤ 2 ^ (2 b + 1)`, so
`smCost d = 4 * (2 * (d + 1) ^ 2) ^ (d + 1) ≤ 2 ^ ((2 b + 1) (d + 1) + 2)`. -/
private theorem smCost_le_of_le {d b : ℕ} (hd : d + 1 ≤ 2 ^ b) :
    smCost d ≤ 2 ^ ((2 * b + 1) * (d + 1) + 2) := by
  have h1 : 2 * (d + 1) ^ 2 ≤ 2 ^ (2 * b + 1) :=
    calc 2 * (d + 1) ^ 2 ≤ 2 * (2 ^ b) ^ 2 := by gcongr
      _ = 2 ^ (2 * b + 1) := by ring
  calc smCost d = 4 * (2 * (d + 1) ^ 2) ^ (d + 1) := by
        rw [smCost, gadgetCost]
        ring
    _ ≤ 4 * (2 ^ (2 * b + 1)) ^ (d + 1) := by gcongr
    _ = 2 ^ ((2 * b + 1) * (d + 1) + 2) := by
        rw [pow_add, ← pow_mul]
        ring

/-- `smCost 1331 ≤ 2 ^ 30638`. -/
private theorem smCost_le : smCost 1331 ≤ 2 ^ 30638 :=
  (smCost_le_of_le (b := 11) (by norm_num)).trans_eq
    (congrArg (2 ^ ·) (by norm_num : (2 * 11 + 1) * (1331 + 1) + 2 = 30638))

/-- `1331 ^ (1 / (4 ^ 1 - 1)) = 11`. -/
private theorem rpow_eq : (1331 : ℝ) ^ (1 / (4 ^ 1 - 1 : ℝ)) = 11 := by
  rw [show (1 / (4 ^ 1 - 1 : ℝ)) = ((3 : ℕ) : ℝ)⁻¹ by norm_num,
    show (1331 : ℝ) = 11 ^ 3 by norm_num, Real.pow_rpow_inv_natCast (by norm_num) (by norm_num)]

/-- **The lower bound over any field** at `d = 1331`, `Δ = 1`, `k = 614760` and `n ≥ 2 ^ k`: every
formula of product-depth one computing `IMM_{n,1331}` has at least `2 ^ 100` nodes. This only
shows that the left side exceeds `1`: such a formula has an input leaf for each of the at least
`n ^ 2` variables of `IMM_{n,1331}`. -/
private theorem two_pow_le_nodeCount {K : Type*} [Field K] {n : ℕ} [NeZero n]
    (hn : 2 ^ 614760 ≤ n) {F : SPFormula K (1331 * (n * n))} (hFΔ : F.productDepth ≤ 1)
    (hFP : rename (immVarEquiv n 1331) F.polynomial = imm K n 1331) :
    2 ^ 100 ≤ F.nodeCount := by
  have h := two_rpow_le_of_imm (immVarEquiv n 1331) (k := 614760) (Δ := 1) (by norm_num) hn
    le_rfl hFΔ hFP
  simp only [Nat.cast_ofNat] at h
  rw [rpow_eq,
    show (614760 : ℝ) * (11 / 20 - 1 / 2) = ((30738 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
    pow_one] at h
  have hc : (smCost 1331 : ℝ) ≤ 2 ^ 30638 := by exact_mod_cast smCost_le
  have h' : (2 : ℝ) ^ 30638 * 2 ^ 100 ≤ 2 ^ 30638 * F.nodeCount := by
    rw [← pow_add]
    exact h.trans (mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg _))
  exact_mod_cast le_of_mul_le_mul_left h' (by positivity)

/-- The sum over paths for `IMM_{n,1331}` meets the hypotheses. -/
example {K : Type*} [Field K] {n : ℕ} [NeZero n] (hn : 2 ^ 614760 ≤ n) :
    2 ^ 100 ≤ (immFormula K n 1331).nodeCount :=
  two_pow_le_nodeCount hn (productDepth_immFormula_le _) (rename_polynomial_immFormula _)

/-! ### The headline beats the variable count -/

/-- `smCost 132651 ≤ 2 ^ 4908126`. -/
private theorem smCost_le' : smCost 132651 ≤ 2 ^ 4908126 :=
  (smCost_le_of_le (b := 18) (by norm_num)).trans_eq
    (congrArg (2 ^ ·) (by norm_num : (2 * 18 + 1) * (132651 + 1) + 2 = 4908126))

/-- `132651 ^ (1 / (4 ^ 1 - 1)) = 51`. -/
private theorem rpow_eq' : (132651 : ℝ) ^ (1 / (4 ^ 1 - 1 : ℝ)) = 51 := by
  rw [show (1 / (4 ^ 1 - 1 : ℝ)) = ((3 : ℕ) : ℝ)⁻¹ by norm_num,
    show (132651 : ℝ) = 51 ^ 3 by norm_num, Real.pow_rpow_inv_natCast (by norm_num) (by norm_num)]

/-- **The lower bound beats the variable count** at `d = 132651 = 51 ^ 3`, `Δ = 1`,
`k = 98162880` and `n = 2 ^ k`: every formula of product-depth one computing `IMM_{n,132651}` has
more than `d n ^ 2` nodes, more than the number of variables of `IMM_{n,132651}`. Here
`d ^ (1 / (4 ^ Δ - 1)) = 51 > 50`, the bound reads `2 ^ (2 k + 18 + 4908126) ≤
smCost 132651 * nodeCount F` with `smCost 132651 ≤ 2 ^ 4908126`, and `d < 2 ^ 18`. -/
private theorem lt_nodeCount {K : Type*} [Field K] {n k : ℕ} [NeZero n] (hk : k = 98162880)
    (hn : n = 2 ^ k) {F : SPFormula K (132651 * (n * n))} (hFΔ : F.productDepth ≤ 1)
    (hFP : rename (immVarEquiv n 132651) F.polynomial = imm K n 132651) :
    132651 * n ^ 2 < F.nodeCount := by
  have h := two_rpow_le_of_imm (immVarEquiv n 132651) (k := k) (Δ := 1)
    (by rw [hk]; norm_num) hn.ge le_rfl hFΔ hFP
  simp only [Nat.cast_ofNat] at h
  have hexp : (k : ℝ) * (51 / 20 - 1 / 2) = ((4908126 + (2 * k + 18) : ℕ) : ℝ) := by
    rw [hk]
    norm_num
  rw [rpow_eq', hexp, Real.rpow_natCast, pow_one] at h
  have hc : (smCost 132651 : ℝ) ≤ 2 ^ 4908126 := by exact_mod_cast smCost_le'
  have h' : (2 : ℝ) ^ 4908126 * 2 ^ (2 * k + 18) ≤ 2 ^ 4908126 * F.nodeCount := by
    rw [← pow_add]
    exact h.trans (mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg _))
  have hE : 2 ^ (2 * k + 18) ≤ F.nodeCount := by
    exact_mod_cast le_of_mul_le_mul_left h' (by positivity)
  have hn2 : n ^ 2 = 2 ^ (2 * k) := by rw [hn, ← pow_mul, mul_comm]
  refine lt_of_lt_of_le ?_ hE
  rw [hn2, pow_add, mul_comm (2 ^ (2 * k))]
  exact Nat.mul_lt_mul_of_pos_right (by norm_num) (by positivity)

/-- The sum over paths for `IMM_{n,132651}` meets the hypotheses. -/
example {K : Type*} [Field K] (n : ℕ) [NeZero n] (hn : n = 2 ^ 98162880) :
    132651 * n ^ 2 < (immFormula K n 132651).nodeCount :=
  lt_nodeCount rfl hn (productDepth_immFormula_le _) (rename_polynomial_immFormula _)

end ComplexityTests.ArithmeticGeneralLowerBound
