/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.FormulaOps
public import CslibFrontier.Foundations.Data.MvPolynomial.PartialEval
public import CslibFrontier.Foundations.Data.MvPolynomial.SchwartzZippel
public import CslibFrontier.Foundations.Data.MvPolynomial.Substitution

/-!
# The Nisan–Wigderson generator for formulas

For a polynomial `f` in `m` variables and `n` embeddings `S i : Fin m ↪ L` of its variables into
a set `L` of seed variables, the *Nisan–Wigderson generator* `nwGenerator f S` is the tuple of
polynomials `f(z|S i)`, `i < n`: `f` on the seed variables of block `i`.

**Hybrid argument.** If `f` is multilinear, any two blocks share at most `a` seed variables, and
a nonzero polynomial `C` computed by a formula of product-depth at most `Δ` vanishes at the
generator, then some nonzero polynomial `P` in `m + 1` variables, computed by a formula of
product-depth at most `Δ + 1` and with at most `C.nodeCount * (2 ^ a * (a + 1) + 2)` nodes, has
`f` as a root in its last variable (`exists_root_formula_of_generator_vanishing`). The hybrids
`H k` replace the first `k` inputs of `C` by the generator; `H 0 ≠ 0` and `H n = 0`, so
`H i ≠ 0 = H (i + 1)` for some `i`. Assigning constants to the seed variables outside block `i`
and to the inputs after `i` keeps `H i` nonzero (`MvPolynomial.exists_aeval_sumElim_ne_zero`);
each generator polynomial `j < i` becomes a multilinear polynomial in the at most `a` variables
block `j` shares with block `i`, so a sum of at most `2 ^ a` monomials (`SPFormula.ofSparse`).
Substituting `f` for the input `i` gives `H (i + 1)` with the same constants, which is zero.

**Hitting set.** If instead `C` does not vanish at the generator, the composition has total
degree at most `C.nodeCount * d` for `f` of total degree at most `d`, so it is nonzero at a point
of the grid `{0, …, C.nodeCount * d} ^ L` (`exists_eval_nwGenerator_ne_zero`). The images of the
grid points form `generatorHittingSet`, of at most `(D + 1) ^ |L|` points.

The root of `P` is turned into a formula for `f` by a separate theorem on low-degree roots, which
this module does not use.

## Main definitions

* `Cslib.Circuits.Arithmetic.nwGenerator`: the Nisan–Wigderson generator.
* `Cslib.Circuits.Arithmetic.generatorHittingSet`: its values on a grid.

## Main results

* `Cslib.Circuits.Arithmetic.exists_root_formula_of_generator_vanishing`: the hybrid argument.
* `Cslib.Circuits.Arithmetic.exists_eval_nwGenerator_ne_zero`,
  `Cslib.Circuits.Arithmetic.exists_mem_generatorHittingSet_eval_ne_zero`: a composition with the
  generator that is nonzero is nonzero on the grid.
* `Cslib.Circuits.Arithmetic.card_generatorHittingSet_le`: the size of the hitting set.

## References

* [N. Nisan, A. Wigderson, *Hardness vs randomness*][NisanWigderson1994]: the generator.
* [V. Kabanets, R. Impagliazzo, *Derandomizing polynomial identity tests means proving circuit
  lower bounds*][KabanetsImpagliazzo2004]: the hybrid argument for arithmetic circuits.
* [Z. Dvir, A. Shpilka, A. Yehudayoff, *Hardness-randomness tradeoffs for bounded depth
  arithmetic circuits*][DvirShpilkaYehudayoff2009]: the hybrid argument at bounded depth.
* [C.-N. Chou, M. Kumar, N. Solomon, *Closure results for polynomial
  factorization*][ChouKumarSolomon2019], arXiv:1803.05933, Lemma 7.1 and Theorem 2.3: the
  hybrid argument and the hitting set for constant-depth circuits. Here the restricted generator
  polynomials are written as sums of monomials, which adds one to the product-depth.
-/

@[expose] public section

namespace Cslib.Circuits.Arithmetic

open Finset MvPolynomial

variable {K L : Type*} {m n : ℕ}

/-- The **Nisan–Wigderson generator**: the polynomial `f` on the seed variables `S i` of block
`i`, for every `i`. -/
noncomputable def nwGenerator [CommSemiring K] (f : MvPolynomial (Fin m) K)
    (S : Fin n → (Fin m ↪ L)) : Fin n → MvPolynomial L K :=
  fun i => rename (S i) f

/-- The generator polynomial of block `i` is `f` renamed along `S i`. -/
@[simp] theorem nwGenerator_apply [CommSemiring K] (f : MvPolynomial (Fin m) K)
    (S : Fin n → (Fin m ↪ L)) (i : Fin n) : nwGenerator f S i = rename (S i) f :=
  rfl

/-! ### The hybrid argument -/

section Hybrid

/-- The input `j` of the hybrid `k`: the generator polynomial of block `j` if `j < k`, the
variable `x_j` otherwise. -/
private noncomputable def hybridInput [CommSemiring K] (f : MvPolynomial (Fin m) K)
    (S : Fin n → (Fin m ↪ L)) (k : ℕ) (j : Fin n) : MvPolynomial (L ⊕ Fin n) K :=
  if (j : ℕ) < k then rename Sum.inl (nwGenerator f S j) else X (Sum.inr j)

/-- The variables kept at the hybrid step `i`: the seed variable `S i k` goes to the variable
`k`, the input `x_i` to the last variable, and every other variable to itself in the left
summand, where it receives a constant. -/
private noncomputable def freeVar (S : Fin n → (Fin m ↪ L)) (i : Fin n) :
    L ⊕ Fin n → (L ⊕ Fin n) ⊕ Fin (m + 1)
  | .inl l => Function.extend (S i) (fun k => .inr k.castSucc) (fun l => .inl (.inl l)) l
  | .inr j => if j = i then .inr (Fin.last m) else .inl (.inr j)

private theorem injective_freeVar (S : Fin n → (Fin m ↪ L)) (i : Fin n) :
    Function.Injective (freeVar S i) := by
  refine Function.LeftInverse.injective
    (g := Sum.elim id (Fin.lastCases (.inr i) fun k => .inl (S i k))) ?_
  rintro (l | j)
  · by_cases hl : ∃ k, S i k = l
    · obtain ⟨k, rfl⟩ := hl
      simp [freeVar, (S i).injective.extend_apply]
    · simp [freeVar, Function.extend_apply' _ _ _ hl]
  · by_cases hj : j = i
    · subst hj
      simp [freeVar]
    · simp [freeVar, hj]

/-- The specialization at the hybrid step `i` with the constants `v`. -/
private noncomputable def specialize [CommSemiring K] (S : Fin n → (Fin m ↪ L)) (i : Fin n)
    (v : L ⊕ Fin n → K) : L ⊕ Fin n → MvPolynomial (Fin (m + 1)) K :=
  Sum.elim (fun a => C (v a)) X ∘ freeVar S i

section

variable [CommSemiring K] {S : Fin n → (Fin m ↪ L)} {i : Fin n} {v : L ⊕ Fin n → K}

private theorem specialize_inl_apply (k : Fin m) :
    specialize S i v (.inl (S i k)) = X k.castSucc := by
  simp [specialize, freeVar, (S i).injective.extend_apply]

private theorem specialize_inl_of_not {l : L} (hl : ¬∃ k, S i k = l) :
    specialize S i v (.inl l) = C (v (.inl l)) := by
  simp [specialize, freeVar, Function.extend_apply' _ _ _ hl]

private theorem specialize_inr_self : specialize S i v (.inr i) = X (Fin.last m) := by
  simp [specialize, freeVar]

private theorem specialize_inr_of_ne {j : Fin n} (hj : j ≠ i) :
    specialize S i v (.inr j) = C (v (.inr j)) := by
  simp [specialize, freeVar, hj]

end

/-- A polynomial that is a variable or a constant has a sum of monomials of at most three
nodes. -/
private theorem nodeCount_ofSparse_X_or_C_le [CommSemiring K] [Nontrivial K]
    {q : MvPolynomial (Fin (m + 1)) K} (hq : (∃ x, q = X x) ∨ ∃ c, q = C c) :
    (SPFormula.ofSparse q).nodeCount ≤ 3 := by
  refine (SPFormula.nodeCount_ofSparse_le q).trans ?_
  rcases hq with ⟨x, rfl⟩ | ⟨c, rfl⟩
  · simp [support_X, totalDegree_X]
  · rw [totalDegree_C, C_apply]
    have := card_le_card (support_monomial_subset (s := (0 : Fin (m + 1) →₀ ℕ)) (a := c))
    rw [card_singleton] at this
    omega

/-- **The hybrid argument** ([KabanetsImpagliazzo2004]; [ChouKumarSolomon2019], Lemma 7.1). If
`f` is multilinear, any two blocks share at most `a` seed variables, and a nonzero polynomial
computed by a formula `C` of product-depth at most `Δ` vanishes at the generator, then a nonzero
polynomial in `m + 1` variables, computed by a formula of product-depth at most `Δ + 1` and with
at most `C.nodeCount * (2 ^ a * (a + 1) + 2)` nodes, vanishes when `f` is substituted for its
last variable. -/
theorem exists_root_formula_of_generator_vanishing [Field K] [Infinite K] [DecidableEq L]
    {f : MvPolynomial (Fin m) K} (hmul : ∀ i, f.degreeOf i ≤ 1)
    {S : Fin n → (Fin m ↪ L)} {a : ℕ}
    (hS : ∀ i j, i ≠ j → #(univ.map (S i) ∩ univ.map (S j)) ≤ a)
    {C : SPFormula K n} {Δ : ℕ} (hΔ : C.productDepth ≤ Δ) (hC : C.polynomial ≠ 0)
    (hvan : aeval (nwGenerator f S) C.polynomial = 0) :
    ∃ F : SPFormula K (m + 1), F.productDepth ≤ Δ + 1 ∧
      F.nodeCount ≤ C.nodeCount * (2 ^ a * (a + 1) + 2) ∧
      F.polynomial ≠ 0 ∧ aeval (Fin.lastCases f X) F.polynomial = 0 := by
  classical
  set H : ℕ → MvPolynomial (L ⊕ Fin n) K := fun k => aeval (hybridInput f S k) C.polynomial
    with hH
  have H0 : H 0 ≠ 0 := by
    have : H 0 = rename Sum.inr C.polynomial := by
      have h0 : hybridInput f S 0 = X ∘ Sum.inr := funext fun j => by simp [hybridInput]
      rw [rename_eq_aeval, ← h0]
    rw [this]
    exact (map_ne_zero_iff _ (rename_injective _ Sum.inr_injective)).2 hC
  have Hn : H n = 0 := by
    have : H n = rename Sum.inl (aeval (nwGenerator f S) C.polynomial) := by
      have hn : hybridInput f S n = fun j => rename Sum.inl (nwGenerator f S j) :=
        funext fun j => by simp [hybridInput]
      rw [comp_aeval_apply, ← hn]
    rw [this, hvan, map_zero]
  obtain ⟨i, hi, hHi, hHi1⟩ : ∃ i < n, H i ≠ 0 ∧ H (i + 1) = 0 := by
    by_contra! h
    have : ∀ k ≤ n, H k ≠ 0 := fun k =>
      Nat.rec (fun _ => H0) (fun k ih hk => h k (by omega) (ih (by omega))) k
    exact this n le_rfl Hn
  set i' : Fin n := ⟨i, hi⟩ with hi'
  obtain ⟨v, hv⟩ := exists_aeval_sumElim_ne_zero
    ((map_ne_zero_iff _ (rename_injective _ (injective_freeVar S i'))).2 hHi)
  rw [aeval_rename] at hv
  change aeval (specialize S i' v) (H i) ≠ 0 at hv
  set ψ := specialize S i' v with hψ
  set G : Fin n → SPFormula K (m + 1) :=
    fun j => SPFormula.ofSparse (aeval ψ (hybridInput f S i j)) with hG
  have hpoly : (SPFormula.substFormula G C).polynomial = aeval ψ (H i) := by
    rw [SPFormula.polynomial_substFormula, hH, comp_aeval_apply]
    simp [hG]
  refine ⟨SPFormula.substFormula G C, ?_, ?_, hpoly ▸ hv, ?_⟩
  · exact (SPFormula.productDepth_substFormula_le
      (fun j => SPFormula.productDepth_ofSparse_le _) C).trans (Nat.add_le_add_right hΔ 1)
  · refine SPFormula.nodeCount_substFormula_le (fun j => ?_) (by omega) C
    by_cases hj : (j : ℕ) < i
    · have hji : j ≠ i' := fun h => by simp [h, hi'] at hj
      set A : Finset (Fin m) := univ.filter fun k => ∃ k', S i' k' = S j k with hA
      have hcard : #A ≤ a := by
        refine le_trans ?_ (hS i' j (Ne.symm hji))
        rw [← card_map (S j)]
        refine card_le_card fun l hl => ?_
        obtain ⟨k, hk, rfl⟩ := mem_map.1 hl
        obtain ⟨k', hk'⟩ := (mem_filter.1 hk).2
        exact mem_inter.2 ⟨mem_map.2 ⟨k', mem_univ _, hk'⟩, mem_map_of_mem _ (mem_univ _)⟩
      have hg : aeval ψ (hybridInput f S i j) = aeval (fun k => ψ (.inl (S j k))) f := by
        simp [hybridInput, hj, aeval_rename, Function.comp_def]
      have hAX : ∀ k ∈ A, ∃ x, ψ (.inl (S j k)) = X x := fun k hk => by
        obtain ⟨k', hk'⟩ := (mem_filter.1 hk).2
        exact ⟨k'.castSucc, by rw [← hk', hψ, specialize_inl_apply]⟩
      have hAC : ∀ k ∉ A, ∃ c, ψ (.inl (S j k)) = MvPolynomial.C c := fun k hk =>
        ⟨v (.inl (S j k)), specialize_inl_of_not (by simpa [hA] using hk)⟩
      have h1 := (card_support_aeval_le_of_degreeOf_le_one hmul hAX hAC).trans
        (Nat.pow_le_pow_right two_pos hcard)
      have h2 := (totalDegree_aeval_le_card_of_degreeOf_le_one hmul hAX hAC).trans hcard
      refine (SPFormula.nodeCount_ofSparse_le _).trans ?_
      rw [hg]
      have := Nat.mul_le_mul h1 (Nat.add_le_add_right h2 1)
      omega
    · have hg : aeval ψ (hybridInput f S i j) = ψ (.inr j) := by
        simp [hybridInput, hj]
      have hpos : 1 ≤ 2 ^ a * (a + 1) := Nat.mul_pos (Nat.two_pow_pos a) (Nat.succ_pos a)
      refine (nodeCount_ofSparse_X_or_C_le ?_).trans (by omega)
      rw [hg]
      by_cases hji : j = i'
      · exact .inl ⟨_, by rw [hji]; exact specialize_inr_self⟩
      · exact .inr ⟨_, specialize_inr_of_ne hji⟩
  · have key (j : Fin n) : aeval (Fin.lastCases f X) (aeval ψ (hybridInput f S i j)) =
        aeval (Fin.lastCases f X) (aeval ψ (hybridInput f S (i + 1) j)) := by
      by_cases hji : j = i'
      · subst hji
        simp [hybridInput, hi', aeval_rename, Function.comp_def, hψ, specialize_inl_apply,
          specialize_inr_self, comp_aeval_apply, aeval_X_left_apply]
      · have hji' : (j : ℕ) ≠ i := fun h => hji (Fin.ext h)
        have : (j : ℕ) < i ↔ (j : ℕ) < i + 1 := by omega
        simp only [hybridInput, this]
    have hsub (k : ℕ) : aeval (Fin.lastCases f X) (aeval ψ (H k)) = aeval
        (fun j => aeval (Fin.lastCases f X) (aeval ψ (hybridInput f S k j))) C.polynomial := by
      rw [hH]
      dsimp only
      rw [comp_aeval_apply (hybridInput f S k) (aeval ψ), comp_aeval_apply]
    rw [hpoly, hsub, funext key, ← hsub, hHi1, map_zero, map_zero]

end Hybrid

/-! ### The hitting set -/

section Grid

/-- **A composition with the generator that is nonzero is nonzero on a grid.** If `f` has total
degree at most `d` and the composition of the polynomial of `C` with the generator is nonzero,
it is nonzero at a point of `{0, …, C.nodeCount * d} ^ L`. -/
theorem exists_eval_nwGenerator_ne_zero [Field K] [CharZero K] [Finite L]
    {f : MvPolynomial (Fin m) K} {S : Fin n → (Fin m ↪ L)} {d : ℕ} (hd : f.totalDegree ≤ d)
    {C : SPFormula K n} (hC : aeval (nwGenerator f S) C.polynomial ≠ 0) :
    ∃ z : L → K, (∀ l, ∃ k ≤ C.nodeCount * d, z l = k) ∧
      eval (fun i => eval z (nwGenerator f S i)) C.polynomial ≠ 0 := by
  classical
  set grid := (range (C.nodeCount * d + 1)).image (Nat.cast : ℕ → K)
  have hdeg : (aeval (nwGenerator f S) C.polynomial).totalDegree < #grid := by
    rw [card_image_of_injective _ Nat.cast_injective, card_range, Nat.lt_succ_iff]
    exact (totalDegree_aeval_le_mul (fun i => (totalDegree_rename_le _ f).trans hd) _).trans
      (Nat.mul_le_mul_right d C.totalDegree_polynomial_le_nodeCount)
  obtain ⟨z, hz, hne⟩ := exists_eval_ne_zero_of_totalDegree_lt_card hC hdeg
  refine ⟨z, fun l => ?_, ?_⟩
  · obtain ⟨k, hk, hzk⟩ := mem_image.1 (hz l)
    exact ⟨k, Nat.lt_succ_iff.1 (mem_range.1 hk), hzk.symm⟩
  · rwa [← aeval_eq_eval, comp_aeval_apply] at hne

open Classical in
/-- The **hitting set of the generator**: its values at the points of the grid `{0, …, D} ^ L`. -/
noncomputable def generatorHittingSet [CommRing K] [Fintype L] [DecidableEq L]
    (f : MvPolynomial (Fin m) K) (S : Fin n → (Fin m ↪ L)) (D : ℕ) : Finset (Fin n → K) :=
  (Fintype.piFinset fun _ : L => (range (D + 1)).image (Nat.cast : ℕ → K)).image
    fun z i => eval z (nwGenerator f S i)

/-- The hitting set of the generator has at most `(D + 1) ^ |L|` points. -/
theorem card_generatorHittingSet_le [CommRing K] [Fintype L] [DecidableEq L]
    (f : MvPolynomial (Fin m) K) (S : Fin n → (Fin m ↪ L)) (D : ℕ) :
    #(generatorHittingSet f S D) ≤ (D + 1) ^ Fintype.card L := by
  classical
  rw [generatorHittingSet]
  refine card_image_le.trans ?_
  rw [Fintype.card_piFinset, prod_const, card_univ]
  exact Nat.pow_le_pow_left (card_image_le.trans (card_range _).le) _

/-- **The generator hits nonvanishing compositions.** If `f` has total degree at most `d` and
the composition of the polynomial of `C` with the generator is nonzero, the polynomial of `C` is
nonzero at a point of `generatorHittingSet f S (C.nodeCount * d)`. -/
theorem exists_mem_generatorHittingSet_eval_ne_zero [Field K] [CharZero K] [Fintype L]
    [DecidableEq L] {f : MvPolynomial (Fin m) K} {S : Fin n → (Fin m ↪ L)} {d : ℕ}
    (hd : f.totalDegree ≤ d) {C : SPFormula K n}
    (hC : aeval (nwGenerator f S) C.polynomial ≠ 0) :
    ∃ x ∈ generatorHittingSet f S (C.nodeCount * d), eval x C.polynomial ≠ 0 := by
  classical
  obtain ⟨z, hz, hne⟩ := exists_eval_nwGenerator_ne_zero hd hC
  rw [generatorHittingSet]
  refine ⟨_, mem_image.2 ⟨z, Fintype.mem_piFinset.2 fun l => ?_, rfl⟩, hne⟩
  obtain ⟨k, hk, hzk⟩ := hz l
  exact mem_image.2 ⟨k, mem_range.2 (Nat.lt_succ_of_le hk), hzk.symm⟩

end Grid

end Cslib.Circuits.Arithmetic
