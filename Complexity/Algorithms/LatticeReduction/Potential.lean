/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Algorithms.LatticeReduction.Reduced

/-!
# The LLL potential and the bound on exchange steps

The LLL algorithm ([LenstraLenstraLovasz1982], (1.15)–(1.21)) changes a family
`b : Fin n → E` by two kinds of steps:

* a *size-reduction step* `bᵢ ← bᵢ - r bⱼ` with `j < i` and `r ∈ ℤ`
  (`Cslib.Algorithms.LatticeReduction.IsSizeStep`);
* an *exchange step* that swaps `bᵢ` and `bᵢ₊₁` when the exchange condition (1.5) fails at `i`
  (`Cslib.Algorithms.LatticeReduction.IsSwapStep`).

Both steps preserve the integer span and linear independence. Size reduction leaves all
Gram–Schmidt vectors unchanged, and rounding `μᵢⱼ` makes `|μᵢⱼ| ≤ 1/2`
(`Cslib.Algorithms.LatticeReduction.abs_gramSchmidtCoeff_round_le`). An exchange step changes
the `i`-th Gram–Schmidt vector to `b*ᵢ₊₁ + μᵢ₊₁,ᵢ b*ᵢ`
(`Cslib.Algorithms.LatticeReduction.gramSchmidt_swap_self`, (1.22)).

The termination argument of (1.23) and (1.26) uses the prefix Gram determinants
`dₖ = ∏_{j<k} ‖b*ⱼ‖² = det (⟪bᵢ, bⱼ⟫)_{i,j<k}`
(`Cslib.Algorithms.LatticeReduction.gramPrefixDet`,
`Cslib.Algorithms.LatticeReduction.gramPrefixDet_eq_det`) and the potential
`D = ∏_{k<n} dₖ` (`Cslib.Algorithms.LatticeReduction.potential`). Size-reduction steps do not
change `D`, and an exchange step multiplies it by less than `δ`
(`Cslib.Algorithms.LatticeReduction.IsSwapStep.potential_lt`). When all inner products
`⟪bᵢ, bⱼ⟫` are integers (`Cslib.Algorithms.LatticeReduction.HasIntegralGram`, as for `bᵢ ∈ ℤᵐ`)
and `b` is linearly independent, each `dₖ` is a positive integer, so `D ≥ 1`. If moreover
`‖bᵢ‖² ≤ B`, then `D ≤ B^{n(n-1)/2}`. Hence along any run of such steps the number `s` of
exchange steps satisfies `(1/δ)ˢ ≤ B^{n(n-1)/2}`
(`Cslib.Algorithms.LatticeReduction.inv_pow_swapCount_le`), i.e.
`s ≤ (n(n-1)/2) log B / log (1/δ)` (`Cslib.Algorithms.LatticeReduction.swapCount_le`).

This bounds exchange steps only. An executable LLL algorithm, the bound on the arithmetic
operations and bit sizes of (1.26), and a polynomial-time statement are not formalized here.

## Main definitions

* `Cslib.Algorithms.LatticeReduction.gramPrefixDet`, `Cslib.Algorithms.LatticeReduction.potential`:
  the quantities `dₖ` and `D` of (1.23)–(1.24).
* `Cslib.Algorithms.LatticeReduction.HasIntegralGram`: integral inner products.
* `Cslib.Algorithms.LatticeReduction.IsSizeStep`, `Cslib.Algorithms.LatticeReduction.IsSwapStep`:
  the two kinds of LLL steps.
* `Cslib.Algorithms.LatticeReduction.swapCount`: the number of exchange steps in a run.

## Main results

* `Cslib.Algorithms.LatticeReduction.IsSwapStep.potential_lt`: an exchange step decreases `D` by
  a factor less than `δ`.
* `Cslib.Algorithms.LatticeReduction.one_le_potential`,
  `Cslib.Algorithms.LatticeReduction.potential_le`: `1 ≤ D ≤ B^{n(n-1)/2}`.
* `Cslib.Algorithms.LatticeReduction.inv_pow_swapCount_le`,
  `Cslib.Algorithms.LatticeReduction.swapCount_le`: the bound on the number of exchange steps.

## References

* [A. K. Lenstra, H. W. Lenstra Jr. and L. Lovász, *Factoring polynomials with rational
  coefficients*][LenstraLenstraLovasz1982]
-/

public section

namespace Cslib.Algorithms.LatticeReduction

open InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}

/-- The prefix Gram determinant `dₖ = ∏_{j<k} ‖b*ⱼ‖²` of [LenstraLenstraLovasz1982], (1.24)–(1.25).
The product runs over the indices `j < k` of `Fin n`. -/
@[expose] noncomputable def gramPrefixDet (b : Fin n → E) (k : ℕ) : ℝ :=
  ∏ j ∈ Finset.univ.filter (fun j : Fin n => (j : ℕ) < k), ‖gramSchmidt ℝ b j‖ ^ 2

/-- The potential `D = ∏_{k<n} dₖ` of [LenstraLenstraLovasz1982], (1.23). The factor `d₀` is `1`. -/
@[expose] noncomputable def potential (b : Fin n → E) : ℝ :=
  ∏ k ∈ Finset.range n, gramPrefixDet b k

/-- For linearly independent `b`, every `dₖ` is positive. -/
theorem gramPrefixDet_pos {b : Fin n → E} (hb : LinearIndependent ℝ b) (k : ℕ) :
    0 < gramPrefixDet b k :=
  Finset.prod_pos fun j _ => pow_pos (norm_pos_iff.2 (gramSchmidt_ne_zero j hb)) 2

/-- For linearly independent `b`, the potential is positive. -/
theorem potential_pos {b : Fin n → E} (hb : LinearIndependent ℝ b) : 0 < potential b :=
  Finset.prod_pos fun k _ => gramPrefixDet_pos hb k

private theorem isLowerSet_range_castLE {k : ℕ} (hk : k ≤ n) :
    IsLowerSet (Set.range (Fin.castLE hk)) := by
  rintro a c hca ⟨d, rfl⟩
  exact ⟨⟨c, lt_of_le_of_lt hca d.isLt⟩, Fin.ext rfl⟩

/-- `dₖ` is the Gram determinant of `b₀, …, bₖ₋₁` ([LenstraLenstraLovasz1982], (1.24)–(1.25)). -/
theorem gramPrefixDet_eq_det (b : Fin n → E) {k : ℕ} (hk : k ≤ n) :
    gramPrefixDet b k = (Matrix.gram ℝ (b ∘ Fin.castLE hk)).det := by
  rw [det_gram_eq_prod_norm_gramSchmidt_sq, gramPrefixDet]
  symm
  refine Finset.prod_bij (fun j _ => Fin.castLE hk j) ?_ ?_ ?_ ?_
  · intro j _
    simp
  · intro j₁ _ j₂ _ h
    exact Fin.castLE_injective hk h
  · intro j hj
    refine ⟨⟨j, (Finset.mem_filter.1 hj).2⟩, Finset.mem_univ _, Fin.ext rfl⟩
  · intro j _
    rw [gramSchmidt_comp b (Fin.strictMono_castLE hk) (isLowerSet_range_castLE hk)]
    rfl

/-- All inner products `⟪bᵢ, bⱼ⟫` are integers, as for a basis of a sublattice of `ℤᵐ`. -/
@[expose] def HasIntegralGram (b : Fin n → E) : Prop :=
  ∀ i j, ∃ z : ℤ, inner ℝ (b i) (b j) = z

/-- With integral inner products, every `dₖ` with `k ≤ n` is an integer. -/
theorem exists_int_gramPrefixDet {b : Fin n → E} (hb : HasIntegralGram b) {k : ℕ}
    (hk : k ≤ n) : ∃ z : ℤ, gramPrefixDet b k = z := by
  choose Z hZ using hb
  refine ⟨(Matrix.of fun i j : Fin k => Z (Fin.castLE hk i) (Fin.castLE hk j)).det, ?_⟩
  rw [gramPrefixDet_eq_det b hk, Int.cast_det]
  congr 1
  ext i j
  simp only [Matrix.gram_apply, Function.comp_apply, hZ, Matrix.map_apply, Matrix.of_apply]

/-- With integral inner products and linear independence, `1 ≤ dₖ` for `k ≤ n`. -/
theorem one_le_gramPrefixDet {b : Fin n → E} (hli : LinearIndependent ℝ b)
    (hb : HasIntegralGram b) {k : ℕ} (hk : k ≤ n) : 1 ≤ gramPrefixDet b k := by
  obtain ⟨z, hz⟩ := exists_int_gramPrefixDet hb hk
  have hpos := gramPrefixDet_pos hli k
  rw [hz] at hpos ⊢
  exact_mod_cast (Int.cast_pos.1 hpos : 0 < z)

/-- With integral inner products and linear independence, `1 ≤ D`
([LenstraLenstraLovasz1982], (1.26)). -/
theorem one_le_potential {b : Fin n → E} (hli : LinearIndependent ℝ b)
    (hb : HasIntegralGram b) : 1 ≤ potential b :=
  Finset.one_le_prod₀ fun _ hk =>
    one_le_gramPrefixDet hli hb (le_of_lt (Finset.mem_range.1 hk))

/-- If `‖bᵢ‖² ≤ B` for all `i`, then `dₖ ≤ Bᵏ` for `k ≤ n`. -/
theorem gramPrefixDet_le {b : Fin n → E} {B : ℝ} (hB : ∀ i, ‖b i‖ ^ 2 ≤ B) {k : ℕ}
    (hk : k ≤ n) : gramPrefixDet b k ≤ B ^ k := by
  have hcard : (Finset.univ.filter fun j : Fin n => (j : ℕ) < k).card = k := by
    rw [Fin.card_filter_val_lt, min_eq_right hk]
  calc gramPrefixDet b k
      ≤ ∏ _j ∈ Finset.univ.filter (fun j : Fin n => (j : ℕ) < k), B :=
        Finset.prod_le_prod₀ (fun j _ => sq_nonneg _) fun j _ =>
          (pow_le_pow_left₀ (norm_nonneg _) (norm_gramSchmidt_le ℝ b j) 2).trans (hB j)
    _ = B ^ k := by rw [Finset.prod_const, hcard]

/-- If `‖bᵢ‖² ≤ B` for all `i`, then `D ≤ B^{n(n-1)/2}` ([LenstraLenstraLovasz1982], (1.26)). -/
theorem potential_le {b : Fin n → E} {B : ℝ} (hB : ∀ i, ‖b i‖ ^ 2 ≤ B) :
    potential b ≤ B ^ (n * (n - 1) / 2) := by
  calc potential b ≤ ∏ k ∈ Finset.range n, B ^ k :=
        Finset.prod_le_prod₀ (fun k _ => Finset.prod_nonneg fun j _ => sq_nonneg _)
          fun k hk => gramPrefixDet_le hB (le_of_lt (Finset.mem_range.1 hk))
    _ = B ^ (n * (n - 1) / 2) := by rw [Finset.prod_pow_eq_pow_sum, Finset.sum_range_id]

/-- Integral inner products pass to families inside the integer span. -/
theorem HasIntegralGram.of_span_le {b c : Fin n → E} (hb : HasIntegralGram b)
    (hc : ∀ i, c i ∈ Submodule.span ℤ (Set.range b)) : HasIntegralGram c := by
  choose Z hZ using hb
  intro i j
  obtain ⟨u, hu⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 (hc i)
  obtain ⟨w, hw⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 (hc j)
  refine ⟨∑ k, ∑ l, u k * w l * Z k l, ?_⟩
  rw [← hu, ← hw, sum_inner]
  push_cast
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [inner_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [← Int.cast_smul_eq_zsmul ℝ, ← Int.cast_smul_eq_zsmul ℝ, inner_smul_left, inner_smul_right,
    hZ]
  simp only [conj_trivial]
  ring

/-- A size-reduction step `bᵢ ← bᵢ - r bⱼ` with `j < i` and `r ∈ ℤ`. -/
@[expose] def IsSizeStep (b c : Fin n → E) : Prop :=
  ∃ i j : Fin n, j < i ∧ ∃ r : ℤ, c = Function.update b i (b i - r • b j)

/-- A size-reduction step leaves every Gram–Schmidt vector unchanged. -/
theorem IsSizeStep.gramSchmidt_eq {b c : Fin n → E} (h : IsSizeStep b c) :
    gramSchmidt ℝ c = gramSchmidt ℝ b := by
  obtain ⟨i, j, hji, r, rfl⟩ := h
  have hv : -(r • b j) ∈ Submodule.span ℝ (b '' Set.Iio i) := by
    refine neg_mem ?_
    rw [← Int.cast_smul_eq_zsmul ℝ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, hji, rfl⟩)
  rw [sub_eq_add_neg]
  exact gramSchmidt_update_add b hv

omit [InnerProductSpace ℝ E] in
/-- A size-reduction step preserves the integer span. -/
theorem IsSizeStep.span_eq {b c : Fin n → E} (h : IsSizeStep b c) :
    Submodule.span ℤ (Set.range c) = Submodule.span ℤ (Set.range b) := by
  obtain ⟨i, j, hji, r, rfl⟩ := h
  exact Submodule.span_range_update_sub_smul (ne_of_lt hji) b r

/-- A size-reduction step leaves the potential unchanged. -/
theorem IsSizeStep.potential_eq {b c : Fin n → E} (h : IsSizeStep b c) :
    potential c = potential b := by
  simp only [potential, gramPrefixDet, h.gramSchmidt_eq]

/-- A size-reduction step preserves linear independence. -/
theorem IsSizeStep.linearIndependent {b c : Fin n → E} (h : IsSizeStep b c)
    (hb : LinearIndependent ℝ b) : LinearIndependent ℝ c := by
  rw [← Matrix.det_gram_ne_zero_iff_linearIndependent (𝕜 := ℝ)] at hb ⊢
  rwa [det_gram_eq_prod_norm_gramSchmidt_sq, h.gramSchmidt_eq,
    ← det_gram_eq_prod_norm_gramSchmidt_sq]

/-- After `bᵢ ← bᵢ - r bⱼ` with `j < i`, the coefficients of row `i` become `μᵢₗ - r μⱼₗ`
(as in [LenstraLenstraLovasz1982], (1.18)). -/
theorem gramSchmidtCoeff_update_sub_smul (b : Fin n → E) {i j : Fin n} (hji : j < i) (r : ℤ)
    (l : Fin n) :
    gramSchmidtCoeff ℝ (Function.update b i (b i - r • b j)) i l =
      gramSchmidtCoeff ℝ b i l - r * gramSchmidtCoeff ℝ b j l := by
  have hgs : gramSchmidt ℝ (Function.update b i (b i - r • b j)) = gramSchmidt ℝ b :=
    IsSizeStep.gramSchmidt_eq ⟨i, j, hji, r, rfl⟩
  simp only [gramSchmidtCoeff, hgs, Function.update_self]
  rw [← Int.cast_smul_eq_zsmul ℝ, inner_sub_right, inner_smul_right]
  ring

/-- Subtracting `round μᵢⱼ` times `bⱼ` makes `|μᵢⱼ| ≤ 1/2`, for linearly independent `b`. -/
theorem abs_gramSchmidtCoeff_round_le {b : Fin n → E} (hli : LinearIndependent ℝ b) {i j : Fin n}
    (hji : j < i) :
    |gramSchmidtCoeff ℝ (Function.update b i
        (b i - round (gramSchmidtCoeff ℝ b i j) • b j)) i j| ≤ 1 / 2 := by
  rw [gramSchmidtCoeff_update_sub_smul b hji,
    gramSchmidtCoeff_self ℝ (gramSchmidt_ne_zero j hli), mul_one]
  exact abs_sub_round _

/-- An exchange step: swap `bᵢ` and `bᵢ₊₁` when condition (1.5) fails at `i`. -/
@[expose] def IsSwapStep (δ : ℝ) (b c : Fin n → E) : Prop :=
  ∃ i j : Fin n, (j : ℕ) = i + 1 ∧ ¬ ExchangeCondAt δ b i j ∧ c = b ∘ Equiv.swap i j

/-- An exchange step preserves the integer span. -/
theorem IsSwapStep.span_eq {δ : ℝ} {b c : Fin n → E} (h : IsSwapStep δ b c) :
    Submodule.span ℤ (Set.range c) = Submodule.span ℤ (Set.range b) := by
  obtain ⟨i, j, -, -, rfl⟩ := h
  rw [Set.range_comp, (Equiv.swap i j).range_eq_univ, Set.image_univ]

/-- An exchange step preserves linear independence. -/
theorem IsSwapStep.linearIndependent {δ : ℝ} {b c : Fin n → E} (h : IsSwapStep δ b c)
    (hb : LinearIndependent ℝ b) : LinearIndependent ℝ c := by
  obtain ⟨i, j, -, -, rfl⟩ := h
  exact hb.comp _ (Equiv.swap i j).injective

private theorem Iio_succ_eq_insert {i j : Fin n} (hij : (j : ℕ) = i + 1) :
    Finset.Iio j = insert i (Finset.Iio i) := by
  ext l
  simp only [Finset.mem_Iio, Finset.mem_insert, Fin.lt_def, Fin.ext_iff]
  omega

/-- Swapping `bᵢ` and `bᵢ₊₁` leaves the Gram–Schmidt vectors before `i` unchanged. -/
theorem gramSchmidt_swap_of_lt {b : Fin n → E} {i j l : Fin n} (hij : (j : ℕ) = i + 1)
    (hl : l < i) : gramSchmidt ℝ (b ∘ Equiv.swap i j) l = gramSchmidt ℝ b l := by
  refine gramSchmidt_congr_Iic fun m hm => ?_
  have hmi : m ≠ i := ne_of_lt (lt_of_le_of_lt hm hl)
  have hmj : m ≠ j := by
    intro h; subst h; rw [Fin.lt_def] at hl; rw [Fin.le_def] at hm; omega
  simp only [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne hmi hmj]

/-- After swapping `bᵢ` and `bᵢ₊₁`, the new `i`-th Gram–Schmidt vector is
`b*ᵢ₊₁ + μ (i+1) i • b*ᵢ` ([LenstraLenstraLovasz1982], (1.22)). -/
theorem gramSchmidt_swap_self (b : Fin n → E) {i j : Fin n} (hij : (j : ℕ) = i + 1) :
    gramSchmidt ℝ (b ∘ Equiv.swap i j) i =
      gramSchmidt ℝ b j + gramSchmidtCoeff ℝ b j i • gramSchmidt ℝ b i := by
  have hlt : i < j := by rw [Fin.lt_def]; omega
  have himg : (b ∘ Equiv.swap i j) '' Set.Iio i = b '' Set.Iio i := by
    refine Set.image_congr fun m hm => ?_
    have hmi : m ≠ i := ne_of_lt hm
    have hmj : m ≠ j := ne_of_lt (lt_trans hm hlt)
    simp only [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne hmi hmj]
  have hci : (b ∘ Equiv.swap i j) i = b j := by simp
  symm
  refine eq_gramSchmidt_of_sub_mem_of_mem_orthogonal ?_ ?_
  · rw [himg, hci, ← span_gramSchmidt_Iio ℝ b i]
    have hexp := gramSchmidt_add_sum_coeff (𝕜 := ℝ) b j
    rw [Iio_succ_eq_insert hij, Finset.sum_insert (by simp)] at hexp
    have : gramSchmidt ℝ b j + gramSchmidtCoeff ℝ b j i • gramSchmidt ℝ b i - b j =
        -∑ l ∈ Finset.Iio i, gramSchmidtCoeff ℝ b j l • gramSchmidt ℝ b l := by
      conv_lhs => rw [hexp]
      abel
    rw [this]
    refine neg_mem (Submodule.sum_mem _ fun l hl => Submodule.smul_mem _ _ ?_)
    exact Submodule.subset_span ⟨l, Finset.mem_Iio.1 hl, rfl⟩
  · rw [himg]
    refine add_mem ?_ (Submodule.smul_mem _ _ (gramSchmidt_mem_orthogonal_span_Iio ℝ b i))
    refine Submodule.orthogonal_le ?_ (gramSchmidt_mem_orthogonal_span_Iio ℝ b j)
    exact Submodule.span_mono (Set.image_mono (Set.Iio_subset_Iio (le_of_lt hlt)))

/-- An exchange step at `i` makes `‖b*ᵢ‖²` smaller than `δ` times its old value. -/
theorem IsSwapStep.exists_norm_sq_lt {δ : ℝ} {b c : Fin n → E} (h : IsSwapStep δ b c) :
    ∃ i j : Fin n, (j : ℕ) = i + 1 ∧ c = b ∘ Equiv.swap i j ∧
      ‖gramSchmidt ℝ c i‖ ^ 2 < δ * ‖gramSchmidt ℝ b i‖ ^ 2 := by
  obtain ⟨i, j, hij, hnot, rfl⟩ := h
  refine ⟨i, j, hij, rfl, ?_⟩
  rw [gramSchmidt_swap_self b hij]
  exact lt_of_not_ge hnot

/-- `dₗ₊₁ = dₗ ‖b*ₗ‖²`. -/
theorem gramPrefixDet_succ (b : Fin n → E) (l : Fin n) :
    gramPrefixDet b (l + 1) = gramPrefixDet b l * ‖gramSchmidt ℝ b l‖ ^ 2 := by
  have hset : Finset.univ.filter (fun m : Fin n => (m : ℕ) < l + 1) =
      insert l (Finset.univ.filter fun m : Fin n => (m : ℕ) < l) := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
    omega
  rw [gramPrefixDet, hset, Finset.prod_insert (by simp), mul_comm]
  rfl

/-- Swapping `bᵢ` and `bᵢ₊₁` leaves `dₘ` unchanged for `m ≤ i`. -/
theorem gramPrefixDet_swap_of_le {b : Fin n → E} {i j : Fin n} (hij : (j : ℕ) = i + 1)
    {m : ℕ} (hm : m ≤ i) : gramPrefixDet (b ∘ Equiv.swap i j) m = gramPrefixDet b m := by
  refine Finset.prod_congr rfl fun l hl => ?_
  have hl' : l < i := by
    rw [Fin.lt_def]; exact lt_of_lt_of_le (Finset.mem_filter.1 hl).2 hm
  rw [gramSchmidt_swap_of_lt hij hl']

/-- Swapping `bᵢ` and `bᵢ₊₁` leaves `dₘ` unchanged for `i + 1 < m ≤ n`. -/
theorem gramPrefixDet_swap_of_lt {b : Fin n → E} {i j : Fin n} (hij : (j : ℕ) = i + 1)
    {m : ℕ} (hjm : (j : ℕ) < m) (hm : m ≤ n) :
    gramPrefixDet (b ∘ Equiv.swap i j) m = gramPrefixDet b m := by
  rw [gramPrefixDet_eq_det _ hm, gramPrefixDet_eq_det _ hm]
  have hi : (i : ℕ) < m := by omega
  have hcomp : (b ∘ Equiv.swap i j) ∘ Fin.castLE hm =
      (b ∘ Fin.castLE hm) ∘ Equiv.swap (⟨i, hi⟩ : Fin m) ⟨j, hjm⟩ := by
    funext l
    simp only [Function.comp_apply]
    rw [(Fin.castLE_injective hm).map_swap]
    rfl
  have hsub : Matrix.gram ℝ ((b ∘ Fin.castLE hm) ∘ Equiv.swap (⟨i, hi⟩ : Fin m) ⟨j, hjm⟩) =
      (Matrix.gram ℝ (b ∘ Fin.castLE hm)).submatrix (Equiv.swap (⟨i, hi⟩ : Fin m) ⟨j, hjm⟩)
        (Equiv.swap (⟨i, hi⟩ : Fin m) ⟨j, hjm⟩) := rfl
  rw [hcomp, hsub, Matrix.det_submatrix_equiv_self]

/-- An exchange step decreases the potential by a factor less than `δ`
([LenstraLenstraLovasz1982], (1.23)). -/
theorem IsSwapStep.potential_lt {δ : ℝ} {b c : Fin n → E} (h : IsSwapStep δ b c)
    (hb : LinearIndependent ℝ b) : potential c < δ * potential b := by
  obtain ⟨i, j, hij, rfl, hlt⟩ := h.exists_norm_sq_lt
  have hmem : (i : ℕ) + 1 ∈ Finset.range n := Finset.mem_range.2 (by omega)
  have hrest : ∏ m ∈ (Finset.range n).erase (i + 1), gramPrefixDet (b ∘ Equiv.swap i j) m =
      ∏ m ∈ (Finset.range n).erase (i + 1), gramPrefixDet b m := by
    refine Finset.prod_congr rfl fun m hm => ?_
    obtain ⟨hne, hmn⟩ := Finset.mem_erase.1 hm
    rcases le_or_gt m i with hle | hgt
    · exact gramPrefixDet_swap_of_le hij hle
    · exact gramPrefixDet_swap_of_lt hij (by omega) (le_of_lt (Finset.mem_range.1 hmn))
  have hpos : 0 < ∏ m ∈ (Finset.range n).erase (i + 1), gramPrefixDet b m :=
    Finset.prod_pos fun m _ => gramPrefixDet_pos hb m
  have hkey : gramPrefixDet (b ∘ Equiv.swap i j) (i + 1) < δ * gramPrefixDet b (i + 1) := by
    rw [gramPrefixDet_succ, gramPrefixDet_succ, gramPrefixDet_swap_of_le hij le_rfl]
    have := gramPrefixDet_pos hb i
    nlinarith
  rw [potential, potential, ← Finset.mul_prod_erase _ _ hmem, ← Finset.mul_prod_erase _ _ hmem,
    hrest, ← mul_assoc]
  exact mul_lt_mul_of_pos_right hkey hpos

/-- A size-reduction step preserves integral inner products. -/
theorem HasIntegralGram.of_isSizeStep {b c : Fin n → E} (hb : HasIntegralGram b)
    (h : IsSizeStep b c) : HasIntegralGram c :=
  hb.of_span_le fun i => h.span_eq ▸ Submodule.subset_span ⟨i, rfl⟩

/-- An exchange step preserves integral inner products. -/
theorem HasIntegralGram.of_isSwapStep {δ : ℝ} {b c : Fin n → E} (hb : HasIntegralGram b)
    (h : IsSwapStep δ b c) : HasIntegralGram c :=
  hb.of_span_le fun i => h.span_eq ▸ Submodule.subset_span ⟨i, rfl⟩

/-- One step of the LLL algorithm: a size-reduction step or an exchange step. -/
@[expose] def IsStep (δ : ℝ) (b c : Fin n → E) : Prop :=
  IsSizeStep b c ∨ IsSwapStep δ b c

open Classical in
/-- The number of exchange steps among the first `T` steps of a run `b`. -/
noncomputable def swapCount (δ : ℝ) (b : ℕ → Fin n → E) (T : ℕ) : ℕ :=
  ((Finset.range T).filter fun t => IsSwapStep δ (b t) (b (t + 1))).card

/-- Unfolding `swapCount` by one step. -/
theorem swapCount_succ (δ : ℝ) (b : ℕ → Fin n → E) (T : ℕ)
    [Decidable (IsSwapStep δ (b T) (b (T + 1)))] :
    swapCount δ b (T + 1) =
      swapCount δ b T + if IsSwapStep δ (b T) (b (T + 1)) then 1 else 0 := by
  classical
  unfold swapCount
  rw [Finset.range_add_one, Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (by simp)]
  · rfl

private theorem run_invariant {δ : ℝ} (hδ : 0 < δ) {b : ℕ → Fin n → E}
    (hli : LinearIndependent ℝ (b 0)) (hint : HasIntegralGram (b 0))
    (T : ℕ) (hstep : ∀ t < T, IsStep δ (b t) (b (t + 1))) :
    LinearIndependent ℝ (b T) ∧ HasIntegralGram (b T) ∧
      potential (b T) * δ⁻¹ ^ swapCount δ b T ≤ potential (b 0) := by
  classical
  induction T with
  | zero => exact ⟨hli, hint, by simp [swapCount]⟩
  | succ T ih =>
    obtain ⟨hliT, hintT, hpotT⟩ := ih fun t ht => hstep t (Nat.lt_succ_of_lt ht)
    rw [swapCount_succ]
    by_cases hs : IsSwapStep δ (b T) (b (T + 1))
    · simp only [hs, ↓reduceIte]
      rw [pow_succ]
      refine ⟨hs.linearIndependent hliT, hintT.of_isSwapStep hs, ?_⟩
      have hlt := hs.potential_lt hliT
      have hinv : potential (b (T + 1)) * δ⁻¹ ≤ potential (b T) := by
        rw [← div_eq_mul_inv, div_le_iff₀ hδ]
        linarith
      calc potential (b (T + 1)) * (δ⁻¹ ^ swapCount δ b T * δ⁻¹)
          = potential (b (T + 1)) * δ⁻¹ * δ⁻¹ ^ swapCount δ b T := by ring
        _ ≤ potential (b T) * δ⁻¹ ^ swapCount δ b T :=
          mul_le_mul_of_nonneg_right hinv (pow_nonneg (inv_nonneg.2 hδ.le) _)
        _ ≤ potential (b 0) := hpotT
    · have hsz : IsSizeStep (b T) (b (T + 1)) := (hstep T (Nat.lt_succ_self T)).resolve_right hs
      simp only [hs, ↓reduceIte, add_zero]
      rw [hsz.potential_eq]
      exact ⟨hsz.linearIndependent hliT, hintT.of_isSizeStep hsz, hpotT⟩

/-- Bound on the number of exchange steps ([LenstraLenstraLovasz1982], proof of (1.26)): along
any run of `T` size-reduction and exchange steps from a linearly independent `b₀` with integral
inner products and `‖b₀ᵢ‖² ≤ B`, the number `s` of exchange steps satisfies
`(1/δ)ˢ ≤ B^{n(n-1)/2}`. -/
theorem inv_pow_swapCount_le {δ B : ℝ} (hδ : 0 < δ) {b : ℕ → Fin n → E}
    (hli : LinearIndependent ℝ (b 0)) (hint : HasIntegralGram (b 0)) (hB : ∀ i, ‖b 0 i‖ ^ 2 ≤ B)
    (T : ℕ) (hstep : ∀ t < T, IsStep δ (b t) (b (t + 1))) :
    δ⁻¹ ^ swapCount δ b T ≤ B ^ (n * (n - 1) / 2) := by
  obtain ⟨hliT, hintT, hpotT⟩ := run_invariant hδ hli hint T hstep
  have h1 := one_le_potential hliT hintT
  calc δ⁻¹ ^ swapCount δ b T ≤ potential (b T) * δ⁻¹ ^ swapCount δ b T :=
        le_mul_of_one_le_left (pow_nonneg (inv_nonneg.2 hδ.le) _) h1
    _ ≤ potential (b 0) := hpotT
    _ ≤ B ^ (n * (n - 1) / 2) := potential_le hB

/-- Logarithmic form: at most `(n(n-1)/2) log B / log (1/δ)` exchange steps, i.e.
`O(n² log B)` for fixed `δ < 1`. -/
theorem swapCount_le {δ B : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) {b : ℕ → Fin n → E}
    (hli : LinearIndependent ℝ (b 0)) (hint : HasIntegralGram (b 0)) (hB : ∀ i, ‖b 0 i‖ ^ 2 ≤ B)
    (T : ℕ) (hstep : ∀ t < T, IsStep δ (b t) (b (t + 1))) :
    (swapCount δ b T : ℝ) ≤ (n * (n - 1) / 2 : ℕ) * Real.log B / Real.log δ⁻¹ := by
  have h := inv_pow_swapCount_le hδ hli hint hB T hstep
  have hpos : 0 < δ⁻¹ ^ swapCount δ b T := pow_pos (inv_pos.2 hδ) _
  have hlog := Real.log_le_log hpos h
  rw [Real.log_pow, Real.log_pow] at hlog
  have hl : 0 < Real.log δ⁻¹ := Real.log_pos (one_lt_inv₀ hδ |>.2 hδ1)
  rw [le_div_iff₀ hl]
  exact hlog

end Cslib.Algorithms.LatticeReduction
