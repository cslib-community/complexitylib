/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.LatticeReduction.Potential
public import CslibFrontier.Algorithms.LatticeReduction.RationalGramSchmidt
public import Mathlib.Data.Rat.Floor

/-!
# The LLL algorithm

The basis reduction algorithm of [LenstraLenstraLovasz1982], (1.15)–(1.21), on the rows of an
integer matrix `B : Vector (Vector ℤ m) n`, with exact rational arithmetic. Its rows, viewed in
`EuclideanSpace ℝ (Fin m)`, are `Cslib.Algorithms.LatticeReduction.realRows B`.

Each round of `Cslib.Algorithms.LatticeReduction.lllLoop δ` at stage `0 < k < n` computes the
Gram–Schmidt rows (`Cslib.Algorithms.LatticeReduction.gramSchmidtRows`), achieves `|μₖ,ₖ₋₁| ≤ 1/2`
by one rounding step (1.18), and then either swaps `bₖ₋₁, bₖ` and steps back when the exchange
condition (1.5) fails (Case 1, (1.19)), or size-reduces the rest of row `k` (1.21) and advances
(Case 2, (1.20)). The source indexes the basis from `1`; stage `k` here is stage `k + 1` of the
source. Unlike (1.18) and (1.21), which reduce only when `|μᵢⱼ| > 1/2`, each size-reduction step
subtracts `⌊μᵢⱼ⌉ bⱼ` unconditionally; this is a no-op when `|μᵢⱼ| < 1/2`, and at `μᵢⱼ = 1/2` it
replaces `μᵢⱼ` by `-1/2`.

`Cslib.Algorithms.LatticeReduction.lll` runs the loop with `δ = 3/4` for
`n + 2 (3 (⌊log₂ B⌋ + 1) · n(n-1)/2 + 1)` rounds, where `B = ∑ᵢ ‖bᵢ‖²`. The proof that this is
enough is the potential argument of (1.23)–(1.26): every swap divides `D = ∏ dᵢ` by more than
`4/3`, every other round advances `k`, and `1 ≤ D ≤ B^{n(n-1)/2}`.

The source notes after (1.5) that `3/4` "may be replaced by any fixed real number y with
1/4 < y < 1". `Cslib.Algorithms.LatticeReduction.lllWith δ` runs the same loop with parameter `δ`
for `n + 2 (⌈δ/(1-δ)⌉ (⌊log₂ B⌋ + 1) · n(n-1)/2 + 1)` rounds: by Bernoulli's inequality
`(1/δ)^⌈δ/(1-δ)⌉ ≥ 2`, so each swap still divides `D` by more than `1/δ`. For `δ = 3/4` this is the
budget of `lll` (`Cslib.Algorithms.LatticeReduction.lll_eq_lllWith`).

## Main definitions

* `Cslib.Algorithms.LatticeReduction.gramSchmidtRows`: the Gram–Schmidt rows of an integer matrix.
* `Cslib.Algorithms.LatticeReduction.lllLoop`: the LLL loop with parameter `δ` and a round budget.
* `Cslib.Algorithms.LatticeReduction.lll`: the LLL algorithm with `δ = 3/4`.
* `Cslib.Algorithms.LatticeReduction.lllWith`: the LLL algorithm with a parameter `δ`.

## Main results

* `Cslib.Algorithms.LatticeReduction.lllLoop_spec`: the loop invariant, for any `δ > 0` (its
  hypotheses can hold only for `δ < 1`).
* `Cslib.Algorithms.LatticeReduction.isReduced_lll`: on linearly independent rows the output is
  `3/4`-reduced and linearly independent.
* `Cslib.Algorithms.LatticeReduction.span_lll`: the output spans the same lattice.
* `Cslib.Algorithms.LatticeReduction.isReduced_lllWith`,
  `Cslib.Algorithms.LatticeReduction.span_lllWith`: the same for `lllWith δ` with `0 < δ < 1`.
* `Cslib.Algorithms.LatticeReduction.dotProduct_lll_zero_le`: Proposition (1.11) for the output,
  `|b₀|² ≤ 2ⁿ |x|²` for every nonzero lattice vector `x` of `n + 1` rows.
* `Cslib.Algorithms.LatticeReduction.dotProduct_lllWith_zero_le`: the same for `lllWith δ` with
  `1/4 < δ < 1` and the factor `(4/(4δ - 1))ⁿ` of the remark after (1.9).
* `Cslib.Algorithms.LatticeReduction.linearIndependent_realRows_iff`: linear independence is
  decided by the integer Gram determinant.

The running time is not formalized: each round costs `O(n² m)` rational operations by
construction, but there is no cost model here, and the bit-size bound of (1.26) is not proved.

## References

* [A. K. Lenstra, H. W. Lenstra Jr. and L. Lovász, *Factoring polynomials with rational
  coefficients*][LenstraLenstraLovasz1982]
-/

public section

namespace Cslib.Algorithms.LatticeReduction

open InnerProductSpace

variable {m n : ℕ}

/-! ### Integer bases -/

/-- The rows of an integer basis as a family of integer vectors. -/
def rows (B : Vector (Vector ℤ m) n) : Fin n → Fin m → ℤ :=
  fun i k => B[i][k]

@[simp] theorem rows_apply (B : Vector (Vector ℤ m) n) (i : Fin n) (k : Fin m) :
    rows B i k = B[i][k] := by
  simp only [rows]

/-- The coordinate embedding `ℤᵐ → ℝᵐ`. -/
noncomputable def intToEuclidean : (Fin m → ℤ) →ₗ[ℤ] EuclideanSpace ℝ (Fin m) where
  toFun v := WithLp.toLp 2 fun k => (v k : ℝ)
  map_add' v w := by ext k; simp
  map_smul' r v := by ext k; simp

theorem intToEuclidean_eq_ratToEuclidean (v : Fin m → ℤ) :
    intToEuclidean v = ratToEuclidean fun k => (v k : ℚ) := by
  ext k; simp [intToEuclidean]

theorem intToEuclidean_injective : Function.Injective (intToEuclidean (m := m)) := by
  intro v w h
  funext k
  have := congrArg (fun x : EuclideanSpace ℝ (Fin m) => x k) h
  simpa [intToEuclidean] using this

/-- The rows of `B` as vectors of `ℝᵐ`. -/
noncomputable def realRows (B : Vector (Vector ℤ m) n) : Fin n → EuclideanSpace ℝ (Fin m) :=
  intToEuclidean ∘ rows B

theorem realRows_eq_intToEuclidean (B : Vector (Vector ℤ m) n) (i : Fin n) :
    realRows B i = intToEuclidean (rows B i) := by
  simp only [realRows, Function.comp_apply]

theorem realRows_apply (B : Vector (Vector ℤ m) n) (i : Fin n) :
    realRows B i = ratToEuclidean fun k => (B[i][k] : ℚ) := by
  simp only [realRows, Function.comp_apply, intToEuclidean_eq_ratToEuclidean, rows]

theorem inner_realRows (B : Vector (Vector ℤ m) n) (i j : Fin n) :
    inner ℝ (realRows B i) (realRows B j) = ((dotProduct (rows B i) (rows B j) : ℤ) : ℝ) := by
  rw [realRows_apply, realRows_apply, inner_ratToEuclidean]
  simp [dotProduct, rows]

theorem norm_sq_realRows (B : Vector (Vector ℤ m) n) (i : Fin n) :
    ‖realRows B i‖ ^ 2 = ((dotProduct (rows B i) (rows B i) : ℤ) : ℝ) := by
  rw [← real_inner_self_eq_norm_sq, inner_realRows]

theorem hasIntegralGram_realRows (B : Vector (Vector ℤ m) n) : HasIntegralGram (realRows B) :=
  fun i j => ⟨_, inner_realRows B i j⟩

theorem span_realRows (B : Vector (Vector ℤ m) n) :
    Submodule.span ℤ (Set.range (realRows B)) =
      (Submodule.span ℤ (Set.range (rows B))).map intToEuclidean := by
  rw [realRows, Set.range_comp, Submodule.span_image]

/-- An integer combination of the rows of `B`, embedded in `ℝᵐ`, lies in the lattice spanned by
`realRows B`. -/
theorem mem_span_realRows_of_eq_sum {B : Vector (Vector ℤ m) n} {v : Fin m → ℤ} {e : Fin n → ℤ}
    (h : v = ∑ i, e i • rows B i) :
    intToEuclidean v ∈ Submodule.span ℤ (Set.range (realRows B)) := by
  rw [span_realRows]
  refine Submodule.mem_map_of_mem ?_
  rw [h]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

/-- The rows of `B` cast to `ℚ`. -/
def castRows (B : Vector (Vector ℤ m) n) : Vector (Vector ℚ m) n :=
  B.map fun v => v.map (Int.cast : ℤ → ℚ)

/-- The Gram–Schmidt rows of `B`, computed exactly in `ℚ` with `O(n² m)` operations. -/
def gramSchmidtRows (B : Vector (Vector ℤ m) n) : Vector (Vector ℚ m) n :=
  gramSchmidtRowsAux (castRows B) n

/-- `G` holds the Gram–Schmidt vectors of the rows of `B`. -/
def IsGramSchmidtRows (G : Vector (Vector ℚ m) n) (B : Vector (Vector ℤ m) n) : Prop :=
  ∀ j : Fin n, ratToEuclidean (fun k : Fin m => G[j][k]) = gramSchmidt ℝ (realRows B) j

theorem IsGramSchmidtRows.ratToEuclidean_eq {G : Vector (Vector ℚ m) n}
    {B : Vector (Vector ℤ m) n} (hG : IsGramSchmidtRows G B) (j : Fin n) :
    ratToEuclidean (fun k : Fin m => G[j][k]) = gramSchmidt ℝ (realRows B) j :=
  hG j

theorem isGramSchmidtRows_gramSchmidtRows (B : Vector (Vector ℤ m) n) :
    IsGramSchmidtRows (gramSchmidtRows B) B := by
  intro j
  have h : (fun l : Fin n => ratToEuclidean fun k : Fin m => (castRows B)[l][k]) = realRows B := by
    funext l
    rw [realRows_apply]
    simp [castRows]
  rw [gramSchmidtRows, gramSchmidtRowsAux_spec _ n j j.isLt, h]

theorem IsGramSchmidtRows.of_isSizeStep {G : Vector (Vector ℚ m) n} {B C : Vector (Vector ℤ m) n}
    (hG : IsGramSchmidtRows G B) (h : IsSizeStep (realRows B) (realRows C)) :
    IsGramSchmidtRows G C := by
  intro j
  rw [h.gramSchmidt_eq]
  exact hG j

/-- `μᵢⱼ = ⟨b*ⱼ, bᵢ⟩ / ‖b*ⱼ‖²`, computed from the Gram–Schmidt rows `G`. -/
def gsCoeff (G : Vector (Vector ℚ m) n) (B : Vector (Vector ℤ m) n) (i j : Fin n) : ℚ :=
  projCoeff (fun k : Fin m => G[j][k]) (fun k : Fin m => (B[i][k] : ℚ))

theorem IsGramSchmidtRows.cast_gsCoeff {G : Vector (Vector ℚ m) n} {B : Vector (Vector ℤ m) n}
    (hG : IsGramSchmidtRows G B)
    (i j : Fin n) : (gsCoeff G B i j : ℝ) = gramSchmidtCoeff ℝ (realRows B) i j := by
  rw [gsCoeff, cast_projCoeff, hG j, ← realRows_apply, gramSchmidtCoeff]
  simp

/-! ### Size reduction -/

/-- Replace row `i` by `bᵢ - r bⱼ`. -/
def subRow (B : Vector (Vector ℤ m) n) (i j : Fin n) (r : ℤ) : Vector (Vector ℤ m) n :=
  B.set i (Vector.ofFn fun k => B[i][k] - r * B[j][k])

theorem rows_subRow (B : Vector (Vector ℤ m) n) (i j : Fin n) (r : ℤ) :
    rows (subRow B i j r) = Function.update (rows B) i (rows B i - r • rows B j) := by
  funext i' k
  by_cases h : i' = i
  · subst h
    simp [rows, subRow]
  · have h' : (i : ℕ) ≠ i' := fun e => h (Fin.ext e.symm)
    simp [rows, subRow, Function.update_of_ne h, h']

theorem realRows_subRow (B : Vector (Vector ℤ m) n) (i j : Fin n) (r : ℤ) :
    realRows (subRow B i j r) =
      Function.update (realRows B) i (realRows B i - r • realRows B j) := by
  simp only [realRows, rows_subRow, Function.comp_update, map_sub, map_zsmul, Function.comp_apply]

/-- One size-reduction step `bᵢ ← bᵢ - ⌊μᵢⱼ⌉ bⱼ` ([LenstraLenstraLovasz1982], (1.18)), performed
unconditionally (the source performs it only when `|μᵢⱼ| > 1/2`). -/
def reduceStep (G : Vector (Vector ℚ m) n) (B : Vector (Vector ℤ m) n) (i j : Fin n) :
    Vector (Vector ℤ m) n :=
  subRow B i j (round (gsCoeff G B i j))

theorem isSizeStep_reduceStep (G : Vector (Vector ℚ m) n) (B : Vector (Vector ℤ m) n)
    {i j : Fin n} (hji : j < i) : IsSizeStep (realRows B) (realRows (reduceStep G B i j)) :=
  ⟨i, j, hji, _, realRows_subRow B i j _⟩

theorem rows_reduceStep_of_ne (G : Vector (Vector ℚ m) n) (B : Vector (Vector ℤ m) n)
    {i j i' : Fin n} (h : i' ≠ i) : rows (reduceStep G B i j) i' = rows B i' := by
  rw [reduceStep, rows_subRow, Function.update_of_ne h]

theorem span_reduceStep (G : Vector (Vector ℚ m) n) (B : Vector (Vector ℤ m) n) {i j : Fin n}
    (hji : j < i) : Submodule.span ℤ (Set.range (rows (reduceStep G B i j))) =
      Submodule.span ℤ (Set.range (rows B)) := by
  rw [reduceStep, rows_subRow, Submodule.span_range_update_sub_smul (ne_of_lt hji)]

/-- After the step `bᵢ ← bᵢ - ⌊μᵢⱼ⌉ bⱼ`, `|μᵢⱼ| ≤ 1/2`. -/
theorem IsGramSchmidtRows.abs_gramSchmidtCoeff_reduceStep_le {G : Vector (Vector ℚ m) n}
    {B : Vector (Vector ℤ m) n} (hG : IsGramSchmidtRows G B) {i j : Fin n} (hji : j < i)
    (hli : LinearIndependent ℝ (realRows B)) :
    |gramSchmidtCoeff ℝ (realRows (reduceStep G B i j)) i j| ≤ 1 / 2 := by
  rw [reduceStep, realRows_subRow, ← Rat.round_cast (α := ℝ), hG.cast_gsCoeff]
  exact abs_gramSchmidtCoeff_round_le hli hji

/-- The step `bᵢ ← bᵢ - r bⱼ` leaves `μᵢₗ` unchanged for `l > j`. -/
theorem gramSchmidtCoeff_reduceStep_of_lt (G : Vector (Vector ℚ m) n) (B : Vector (Vector ℤ m) n)
    {i j l : Fin n} (hji : j < i) (hjl : j < l) :
    gramSchmidtCoeff ℝ (realRows (reduceStep G B i j)) i l =
      gramSchmidtCoeff ℝ (realRows B) i l := by
  rw [reduceStep, realRows_subRow, gramSchmidtCoeff_update_sub_smul _ hji,
    gramSchmidtCoeff_eq_zero_of_lt ℝ _ hjl, mul_zero, sub_zero]

/-- Size-reduce row `i` against rows `t - 1, …, 0`, in this order, using the Gram–Schmidt rows
`G` (which size reduction does not change). -/
def reduceRow (G : Vector (Vector ℚ m) n) (i : Fin n) :
    ℕ → Vector (Vector ℤ m) n → Vector (Vector ℤ m) n
  | 0, B => B
  | t + 1, B => if h : t < n then reduceRow G i t (reduceStep G B i ⟨t, h⟩) else B

theorem reduceRow_spec (G : Vector (Vector ℚ m) n) (i : Fin n) :
    ∀ (t : ℕ) (B : Vector (Vector ℤ m) n), t ≤ i → IsGramSchmidtRows G B →
    LinearIndependent ℝ (realRows B) →
    Relation.ReflTransGen IsSizeStep (realRows B) (realRows (reduceRow G i t B)) ∧
    (∀ i', i' ≠ i → rows (reduceRow G i t B) i' = rows B i') ∧
    (∀ l : Fin n, (l : ℕ) < t → |gramSchmidtCoeff ℝ (realRows (reduceRow G i t B)) i l| ≤ 1 / 2) ∧
    (∀ l : Fin n, t ≤ (l : ℕ) → l < i →
      gramSchmidtCoeff ℝ (realRows (reduceRow G i t B)) i l =
        gramSchmidtCoeff ℝ (realRows B) i l) := by
  intro t
  induction t with
  | zero =>
    intro B _ _ _
    exact ⟨Relation.ReflTransGen.refl, fun _ _ => rfl, fun l hl => absurd hl (Nat.not_lt_zero _),
      fun _ _ _ => rfl⟩
  | succ t ih =>
    intro B ht hG hli
    have htn : t < n := by omega
    have hti : (⟨t, htn⟩ : Fin n) < i := by
      change t < (i : ℕ); omega
    simp only [reduceRow, htn, dite_true]
    have hstep := isSizeStep_reduceStep G B hti
    obtain ⟨h1, h2, h3, h4⟩ := ih (reduceStep G B i ⟨t, htn⟩) (by omega) (hG.of_isSizeStep hstep)
      (hstep.linearIndependent hli)
    refine ⟨Relation.ReflTransGen.head hstep h1, fun i' hi' => ?_, fun l hl => ?_,
      fun l hl hli' => ?_⟩
    · rw [h2 i' hi', rows_reduceStep_of_ne G B hi']
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hl with hl | hl
      · exact h3 l hl
      · have hlt : (⟨t, htn⟩ : Fin n) = l := Fin.ext hl.symm
        subst hlt
        rw [h4 _ le_rfl hti]
        exact hG.abs_gramSchmidtCoeff_reduceStep_le hti hli
    · rw [h4 l (by omega) hli']
      exact gramSchmidtCoeff_reduceStep_of_lt G B hti (by change t < (l : ℕ); omega)

theorem reflTransGen_isSizeStep {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {b c : Fin n → E} (h : Relation.ReflTransGen IsSizeStep b c) :
    gramSchmidt ℝ c = gramSchmidt ℝ b ∧ potential c = potential b ∧
      (LinearIndependent ℝ b → LinearIndependent ℝ c) ∧
      Submodule.span ℤ (Set.range c) = Submodule.span ℤ (Set.range b) := by
  induction h with
  | refl => exact ⟨rfl, rfl, id, rfl⟩
  | tail _ hs ih =>
    obtain ⟨h1, h2, h3, h4⟩ := ih
    exact ⟨hs.gramSchmidt_eq.trans h1, hs.potential_eq.trans h2,
      fun hb => hs.linearIndependent (h3 hb), hs.span_eq.trans h4⟩

theorem span_reduceRow (G : Vector (Vector ℚ m) n) (i : Fin n) :
    ∀ (t : ℕ) (B : Vector (Vector ℤ m) n), t ≤ i →
    Submodule.span ℤ (Set.range (rows (reduceRow G i t B))) =
      Submodule.span ℤ (Set.range (rows B)) := by
  intro t
  induction t with
  | zero => intro B _; rfl
  | succ t ih =>
    intro B ht
    have htn : t < n := by omega
    have hti : (⟨t, htn⟩ : Fin n) < i := by
      change t < (i : ℕ); omega
    simp only [reduceRow, htn, dite_true]
    rw [ih _ (by omega), reduceStep, rows_subRow,
      Submodule.span_range_update_sub_smul (ne_of_lt hti)]

/-! ### Exchange -/

theorem rows_swap (B : Vector (Vector ℤ m) n) (i j : Fin n) :
    rows (B.swap i j) = rows B ∘ Equiv.swap i j := by
  funext l k
  simp only [rows, Function.comp_apply, Fin.getElem_fin, Vector.getElem_swap,
    Equiv.swap_apply_def]
  by_cases h1 : l = i
  · subst h1; simp
  · by_cases h2 : l = j
    · subst h2
      have : (l : ℕ) ≠ i := fun e => h1 (Fin.ext e)
      simp [h1, this]
    · have e1 : (l : ℕ) ≠ i := fun e => h1 (Fin.ext e)
      have e2 : (l : ℕ) ≠ j := fun e => h2 (Fin.ext e)
      simp [h1, h2, e1, e2]

theorem realRows_swap (B : Vector (Vector ℤ m) n) (i j : Fin n) :
    realRows (B.swap i j) = realRows B ∘ Equiv.swap i j := by
  simp only [realRows, rows_swap, Function.comp_assoc]

theorem span_rows_swap (B : Vector (Vector ℤ m) n) (i j : Fin n) :
    Submodule.span ℤ (Set.range (rows (B.swap i j))) =
      Submodule.span ℤ (Set.range (rows B)) := by
  rw [rows_swap, Set.range_comp, (Equiv.swap i j).range_eq_univ, Set.image_univ]

/-- The exchange condition (1.5) at `(i, j)`, computed from the Gram–Schmidt rows `G`. -/
@[expose] def exchangeCondQ (δ : ℚ) (G : Vector (Vector ℚ m) n) (B : Vector (Vector ℤ m) n)
    (i j : Fin n) : Prop :=
  δ * dotProduct (fun k : Fin m => G[i][k]) (fun k : Fin m => G[i][k]) ≤
    dotProduct (fun k : Fin m => G[j][k]) (fun k : Fin m => G[j][k]) +
      gsCoeff G B j i ^ 2 * dotProduct (fun k : Fin m => G[i][k]) (fun k : Fin m => G[i][k])

instance (δ : ℚ) (G : Vector (Vector ℚ m) n) (B : Vector (Vector ℤ m) n) (i j : Fin n) :
    Decidable (exchangeCondQ δ G B i j) := by
  unfold exchangeCondQ; infer_instance

theorem IsGramSchmidtRows.exchangeCondQ_iff {G : Vector (Vector ℚ m) n} {B : Vector (Vector ℤ m) n}
    (hG : IsGramSchmidtRows G B) (δ : ℚ) {i j : Fin n} (hij : i < j) :
    exchangeCondQ δ G B i j ↔ ExchangeCondAt (δ : ℝ) (realRows B) i j := by
  rw [ExchangeCondAt, norm_sq_gramSchmidt_add_smul _ hij, ← hG i, ← hG j, norm_sq_ratToEuclidean,
    norm_sq_ratToEuclidean, ← hG.cast_gsCoeff, exchangeCondQ]
  constructor <;> intro h
  · exact_mod_cast h
  · exact_mod_cast h

/-- Swap rows `i` and `j`. -/
def swapRows (B : Vector (Vector ℤ m) n) (i j : Fin n) : Vector (Vector ℤ m) n :=
  B.swap i j

theorem realRows_swapRows (B : Vector (Vector ℤ m) n) (i j : Fin n) :
    realRows (swapRows B i j) = realRows B ∘ Equiv.swap i j := by
  rw [swapRows, realRows_swap]

theorem span_rows_swapRows (B : Vector (Vector ℤ m) n) (i j : Fin n) :
    Submodule.span ℤ (Set.range (rows (swapRows B i j))) =
      Submodule.span ℤ (Set.range (rows B)) := by
  rw [swapRows, span_rows_swap]

/-! ### The loop -/

/-- The first `k` vectors are reduced: size reduced in rows `< k` and the exchange condition at
consecutive pairs below `k`. -/
def PrefixReduced {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (δ : ℝ)
    (b : Fin n → E) (k : ℕ) : Prop :=
  (∀ i j : Fin n, (i : ℕ) < k → j < i → |gramSchmidtCoeff ℝ b i j| ≤ 1 / 2) ∧
    ∀ i j : Fin n, (j : ℕ) < k → (j : ℕ) = i + 1 → ExchangeCondAt δ b i j

section Prefix

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem PrefixReduced.zero (δ : ℝ) (b : Fin n → E) : PrefixReduced δ b 0 :=
  ⟨fun _ _ hi _ => absurd hi (Nat.not_lt_zero _), fun _ _ hj _ => absurd hj (Nat.not_lt_zero _)⟩

theorem PrefixReduced.one (δ : ℝ) (b : Fin n → E) : PrefixReduced δ b 1 :=
  ⟨fun i j hi hji => absurd hji (by rw [Fin.lt_def]; omega), fun i j hj hij => by omega⟩

theorem PrefixReduced.isReduced {δ : ℝ} {b : Fin n → E} {k : ℕ} (hb : PrefixReduced δ b k)
    (hk : n ≤ k) : IsReduced δ b :=
  ⟨fun i j hji => hb.1 i j (lt_of_lt_of_le i.isLt hk) hji,
    fun i j hij => hb.2 i j (lt_of_lt_of_le j.isLt hk) hij⟩

theorem PrefixReduced.mono {δ : ℝ} {b : Fin n → E} {k k' : ℕ} (hb : PrefixReduced δ b k)
    (h : k' ≤ k) : PrefixReduced δ b k' :=
  ⟨fun i j hi hji => hb.1 i j (by omega) hji, fun i j hj hij => hb.2 i j (by omega) hij⟩

theorem PrefixReduced.congr {δ : ℝ} {b c : Fin n → E} {k : ℕ} (hb : PrefixReduced δ b k)
    (h : ∀ i : Fin n, (i : ℕ) < k → c i = b i) : PrefixReduced δ c k := by
  have hgs : ∀ i : Fin n, (i : ℕ) < k → gramSchmidt ℝ c i = gramSchmidt ℝ b i := fun i hi =>
    gramSchmidt_congr_Iic fun j hj => h j (by have := Fin.le_def.1 hj; omega)
  have hmu : ∀ i j : Fin n, (i : ℕ) < k → j ≤ i →
      gramSchmidtCoeff ℝ c i j = gramSchmidtCoeff ℝ b i j := by
    intro i j hi hji
    rw [gramSchmidtCoeff, gramSchmidtCoeff, hgs j (by have := Fin.le_def.1 hji; omega), h i hi]
  refine ⟨fun i j hi hji => ?_, fun i j hj hij => ?_⟩
  · rw [hmu i j hi hji.le]; exact hb.1 i j hi hji
  · have hi : (i : ℕ) < k := by omega
    have hle : i ≤ j := by rw [Fin.le_def]; omega
    unfold ExchangeCondAt
    rw [hgs i hi, hgs j hj, hmu j i hj hle]
    exact hb.2 i j hj hij

theorem PrefixReduced.succ {δ : ℝ} {b : Fin n → E} {k : ℕ} (hb : PrefixReduced δ b k) (hk : k < n)
    (hsize : ∀ l : Fin n, (l : ℕ) < k → |gramSchmidtCoeff ℝ b ⟨k, hk⟩ l| ≤ 1 / 2)
    (hex : ∀ h : 0 < k, ExchangeCondAt δ b ⟨k - 1, by omega⟩ ⟨k, hk⟩) :
    PrefixReduced δ b (k + 1) := by
  refine ⟨fun i j hi hji => ?_, fun i j hj hij => ?_⟩
  · rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | hi
    · exact hb.1 i j hi hji
    · have : i = ⟨k, hk⟩ := Fin.ext hi
      subst this
      exact hsize j hji
  · rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | hj
    · exact hb.2 i j hj hij
    · have hk1 : k - 1 < n := by omega
      have hj' : j = ⟨k, hk⟩ := Fin.ext hj
      subst hj'
      have hi' : i = ⟨k - 1, hk1⟩ := Fin.ext (by simp only at hij ⊢; omega)
      subst hi'
      exact hex (by simp only at hij; omega)

end Prefix

/-- The LLL loop ([LenstraLenstraLovasz1982], (1.15)–(1.21)) with parameter `δ` in place of
`3/4`, for at most `fuel` rounds, at stage `k` (stage `k + 1` of the source). For `0 < k < n`
it computes the Gram–Schmidt rows, achieves `|μₖ,ₖ₋₁| ≤ 1/2` (1.18), and then either swaps
`bₖ₋₁, bₖ` and steps back (Case 1, when (1.5) fails at `(k - 1, k)`) or size-reduces the rest of
row `k` (1.21) and advances (Case 2). Each round costs `O(n² m)` rational operations. -/
def lllLoop (δ : ℚ) : ℕ → Vector (Vector ℤ m) n → ℕ → Vector (Vector ℤ m) n
  | 0, B, _ => B
  | fuel + 1, B, k =>
    if hk : k < n then
      if k = 0 then lllLoop δ fuel B 1
      else
        let G := gramSchmidtRows B
        let B₁ := reduceStep G B ⟨k, hk⟩ ⟨k - 1, by omega⟩
        if exchangeCondQ δ G B₁ ⟨k - 1, by omega⟩ ⟨k, hk⟩ then
          lllLoop δ fuel (reduceRow G ⟨k, hk⟩ (k - 1) B₁) (k + 1)
        else lllLoop δ fuel (swapRows B₁ ⟨k - 1, by omega⟩ ⟨k, hk⟩) (k - 1)
    else B

theorem span_lllLoop (δ : ℚ) : ∀ (fuel : ℕ) (B : Vector (Vector ℤ m) n) (k : ℕ),
    Submodule.span ℤ (Set.range (rows (lllLoop δ fuel B k))) =
      Submodule.span ℤ (Set.range (rows B)) := by
  intro fuel
  induction fuel with
  | zero => intro B k; rfl
  | succ fuel ih =>
    intro B k
    rw [lllLoop]
    dsimp only
    split_ifs with hk h0 hex
    · rw [ih]
    · rw [ih, span_reduceRow _ _ _ _ (by simp only; omega),
        span_reduceStep _ _ (by rw [Fin.mk_lt_mk]; omega)]
    · rw [ih, span_rows_swapRows, span_reduceStep _ _ (by rw [Fin.mk_lt_mk]; omega)]
    · rfl

/-- Invariant of the LLL loop: with `0 < δ`, the potential below `δ⁻¹ ^ s` and enough fuel, the
loop returns a `δ`-reduced linearly independent family. Since the potential of linearly
independent integer rows is at least `1`, the hypotheses can hold only for `δ < 1`. -/
theorem lllLoop_spec {δ : ℚ} (hδ0 : 0 < δ) : ∀ (fuel : ℕ) (B : Vector (Vector ℤ m) n) (k s : ℕ),
    LinearIndependent ℝ (realRows B) → PrefixReduced (δ : ℝ) (realRows B) k →
    potential (realRows B) < ((δ : ℝ)⁻¹) ^ s → n - k + 2 * s ≤ fuel →
    IsReduced (δ : ℝ) (realRows (lllLoop δ fuel B k)) ∧
      LinearIndependent ℝ (realRows (lllLoop δ fuel B k)) := by
  have hδ0' : (0 : ℝ) < δ := by exact_mod_cast hδ0
  have hpos : ∀ B : Vector (Vector ℤ m) n, LinearIndependent ℝ (realRows B) →
      1 ≤ potential (realRows B) :=
    fun B hB => one_le_potential hB (hasIntegralGram_realRows B)
  intro fuel
  induction fuel with
  | zero =>
    intro B k s hli hpre hpot hfuel
    have hs : s = 0 := by omega
    subst hs
    rw [pow_zero] at hpot
    exact absurd hpot (not_lt.2 (hpos B hli))
  | succ fuel ih =>
    intro B k s hli hpre hpot hfuel
    rw [lllLoop]
    dsimp only
    by_cases hk : k < n
    swap
    · -- `k = n`: done.
      simp only [hk, dite_false]
      exact ⟨hpre.isReduced (not_lt.1 hk), hli⟩
    simp only [hk, dite_true]
    split_ifs with h0 hex
    · -- `k = 0`: nothing to do; advance to `1`.
      exact ih B 1 s hli (PrefixReduced.one _ _) hpot (by omega)
    all_goals
      have hk1 : (⟨k - 1, by omega⟩ : Fin n) < ⟨k, hk⟩ := by rw [Fin.mk_lt_mk]; omega
      have hG := isGramSchmidtRows_gramSchmidtRows B
      have hstep := isSizeStep_reduceStep (gramSchmidtRows B) B hk1
      set B₁ := reduceStep (gramSchmidtRows B) B ⟨k, hk⟩ ⟨k - 1, by omega⟩ with hB₁
      have hG₁ : IsGramSchmidtRows (gramSchmidtRows B) B₁ := hG.of_isSizeStep hstep
      have hli₁ := hstep.linearIndependent hli
      have hrow₁ : ∀ i : Fin n, i ≠ ⟨k, hk⟩ → rows B₁ i = rows B i := fun i hi =>
        rows_reduceStep_of_ne _ _ hi
    · -- Case 2: the exchange condition holds; reduce the rest of row `k` and advance.
      obtain ⟨h1, h2, h3, h4⟩ :=
        reduceRow_spec (gramSchmidtRows B) ⟨k, hk⟩ (k - 1) B₁ (by simp only; omega) hG₁ hli₁
      set B' := reduceRow (gramSchmidtRows B) ⟨k, hk⟩ (k - 1) B₁ with hB'
      obtain ⟨hgs, hpot', hli', -⟩ := reflTransGen_isSizeStep (Relation.ReflTransGen.head hstep h1)
      refine ih B' (k + 1) s (hli' hli) ?_ (hpot'.symm ▸ hpot) (by omega)
      have hpre' : PrefixReduced (δ : ℝ) (realRows B') k :=
        hpre.congr fun i hi => by
          have hne : i ≠ ⟨k, hk⟩ := fun h => by rw [h] at hi; exact lt_irrefl _ hi
          simp only [realRows, Function.comp_apply]
          rw [h2 i hne, hrow₁ i hne]
      have hmu : gramSchmidtCoeff ℝ (realRows B') ⟨k, hk⟩ ⟨k - 1, by omega⟩ =
          gramSchmidtCoeff ℝ (realRows B₁) ⟨k, hk⟩ ⟨k - 1, by omega⟩ :=
        h4 _ (by simp only; omega) hk1
      refine hpre'.succ hk (fun l hl => ?_) fun _ => ?_
      · rcases Nat.lt_or_ge (l : ℕ) (k - 1) with hl' | hl'
        · exact h3 l hl'
        · have hl'' : l = ⟨k - 1, by omega⟩ := Fin.ext (by simp only; omega)
          rw [hl'', hmu]
          exact hG.abs_gramSchmidtCoeff_reduceStep_le hk1 hli
      · have hex' := (hG₁.exchangeCondQ_iff δ hk1).1 hex
        have hgs₁ := (reflTransGen_isSizeStep h1).1
        unfold ExchangeCondAt at hex' ⊢
        rw [hgs₁, hmu]
        exact hex'
    · -- Case 1: the exchange condition fails; swap `bₖ₋₁, bₖ` and step back.
      have hswap : IsSwapStep (δ : ℝ) (realRows B₁)
          (realRows (swapRows B₁ ⟨k - 1, by omega⟩ ⟨k, hk⟩)) := by
        refine ⟨⟨k - 1, by omega⟩, ⟨k, hk⟩, by simp only; omega, ?_, realRows_swapRows _ _ _⟩
        rw [← hG₁.exchangeCondQ_iff δ hk1]
        exact hex
      have hpot' := hstep.potential_eq
      have hlt := hswap.potential_lt hli₁
      obtain _ | s := s
      · rw [pow_zero, ← hpot'] at hpot
        exact absurd hpot (not_lt.2 (hpos B₁ hli₁))
      refine ih _ (k - 1) s (hswap.linearIndependent hli₁) ?_ ?_ (by omega)
      · refine (hpre.mono (Nat.sub_le k 1)).congr fun i hi => ?_
        have hne1 : i ≠ ⟨k - 1, by omega⟩ := fun h => by rw [h] at hi; simp only at hi; omega
        have hne2 : i ≠ ⟨k, hk⟩ := fun h => by rw [h] at hi; simp only at hi; omega
        rw [realRows_swapRows, Function.comp_apply, Equiv.swap_apply_of_ne_of_ne hne1 hne2]
        simp only [realRows, Function.comp_apply]
        rw [hrow₁ i hne2]
      · calc potential (realRows (swapRows B₁ ⟨k - 1, by omega⟩ ⟨k, hk⟩))
            < (δ : ℝ) * potential (realRows B₁) := hlt
          _ = (δ : ℝ) * potential (realRows B) := by rw [hpot']
          _ < (δ : ℝ) * ((δ : ℝ)⁻¹) ^ (s + 1) := mul_lt_mul_of_pos_left hpot hδ0'
          _ = ((δ : ℝ)⁻¹) ^ s := by
            rw [pow_succ]; field_simp

/-! ### The algorithm -/

/-- `B = ∑ᵢ ‖bᵢ‖²`, a bound on the squared length of every input vector. -/
def sqNormSum (B : Vector (Vector ℤ m) n) : ℕ :=
  (∑ i, dotProduct (rows B i) (rows B i)).toNat

theorem norm_sq_realRows_le (B : Vector (Vector ℤ m) n) (i : Fin n) :
    ‖realRows B i‖ ^ 2 ≤ (sqNormSum B : ℝ) := by
  have hnn : 0 ≤ ∑ i, dotProduct (rows B i) (rows B i) :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun k _ => mul_self_nonneg _
  have hle : dotProduct (rows B i) (rows B i) ≤ ∑ i, dotProduct (rows B i) (rows B i) :=
    Finset.single_le_sum (fun i _ => Finset.sum_nonneg fun k _ => mul_self_nonneg _)
      (Finset.mem_univ i)
  have hcast : ((sqNormSum B : ℤ) : ℝ) =
      ((∑ i, dotProduct (rows B i) (rows B i) : ℤ) : ℝ) := by
    rw [sqNormSum, Int.toNat_of_nonneg hnn]
  rw [norm_sq_realRows, ← Int.cast_natCast, hcast]
  exact_mod_cast hle

/-- The number of exchange steps allowed by the potential argument: `3 (⌊log₂ B⌋ + 1) · n(n-1)/2`
bounds `log_{4/3} B^{n(n-1)/2}`. -/
def swapBudget (n B : ℕ) : ℕ :=
  3 * (Nat.log 2 B + 1) * (n * (n - 1) / 2)

/-- The number of exchange steps per doubling of the potential allowed for the parameter `δ`:
`⌈δ / (1 - δ)⌉`, so that `δ⁻¹ ^ swapFactor δ ≥ 2` for `0 < δ < 1` (`two_le_inv_pow_swapFactor`).
For `δ = 3/4` it is `3`. -/
def swapFactor (δ : ℚ) : ℕ :=
  ⌈δ / (1 - δ)⌉₊

/-- The number of exchange steps allowed by the potential argument for the parameter `δ`:
`⌈δ / (1 - δ)⌉ (⌊log₂ B⌋ + 1) · n(n-1)/2` bounds `log_{1/δ} B^{n(n-1)/2}`. -/
def swapBudgetOf (δ : ℚ) (n B : ℕ) : ℕ :=
  swapFactor δ * (Nat.log 2 B + 1) * (n * (n - 1) / 2)

theorem swapFactor_three_div_four : swapFactor (3 / 4) = 3 := by
  rw [swapFactor, show (3 / 4 : ℚ) / (1 - 3 / 4) = ((3 : ℕ) : ℚ) by norm_num, Nat.ceil_natCast]

theorem swapBudgetOf_three_div_four (n B : ℕ) : swapBudgetOf (3 / 4) n B = swapBudget n B := by
  rw [swapBudgetOf, swapFactor_three_div_four, swapBudget]

/-- Bernoulli's inequality gives `δ⁻¹ ^ ⌈δ / (1 - δ)⌉ ≥ 2` for `0 < δ < 1`. -/
theorem two_le_inv_pow_swapFactor {δ : ℚ} (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    (2 : ℝ) ≤ ((δ : ℝ)⁻¹) ^ swapFactor δ := by
  have hδ0' : (0 : ℝ) < δ := by exact_mod_cast hδ0
  have hδ1' : (δ : ℝ) < 1 := by exact_mod_cast hδ1
  have hc : (δ : ℝ) / (1 - δ) ≤ swapFactor δ := by
    have h := Nat.le_ceil (δ / (1 - δ))
    rw [swapFactor]
    exact_mod_cast h
  have ha : (-2 : ℝ) ≤ (1 - δ) / δ := by
    have : 0 ≤ (1 - (δ : ℝ)) / δ := div_nonneg (by linarith) hδ0'.le
    linarith
  have hb := one_add_mul_le_pow ha (swapFactor δ)
  have hinv : 1 + (1 - (δ : ℝ)) / δ = (δ : ℝ)⁻¹ := by field_simp; ring
  rw [hinv] at hb
  have h1 : (1 : ℝ) ≤ (swapFactor δ : ℝ) * ((1 - δ) / δ) := by
    have hpos : (0 : ℝ) < (1 - δ) / δ := div_pos (by linarith) hδ0'
    calc (1 : ℝ) = (δ / (1 - δ)) * ((1 - δ) / δ) := by field_simp
      _ ≤ (swapFactor δ : ℝ) * ((1 - δ) / δ) := mul_le_mul_of_nonneg_right hc hpos.le
  linarith

/-- The potential of an integer basis is below `δ⁻¹ ^ (swapBudgetOf δ n B + 1)`, where
`B = ∑ᵢ ‖bᵢ‖²`, for `0 < δ < 1`. -/
theorem potential_realRows_lt_inv_pow {δ : ℚ} (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (B : Vector (Vector ℤ m) n) :
    potential (realRows B) < ((δ : ℝ)⁻¹) ^ (swapBudgetOf δ n (sqNormSum B) + 1) := by
  have hδ0' : (0 : ℝ) < δ := by exact_mod_cast hδ0
  have hδ1' : (δ : ℝ) < 1 := by exact_mod_cast hδ1
  have hgt : (1 : ℝ) < (δ : ℝ)⁻¹ := one_lt_inv_iff₀.2 ⟨hδ0', hδ1'⟩
  have h1 := potential_le (norm_sq_realRows_le B)
  have h2 : (sqNormSum B : ℝ) ≤ 2 ^ (Nat.log 2 (sqNormSum B) + 1) := by
    exact_mod_cast (Nat.lt_pow_succ_log_self (by norm_num) (sqNormSum B)).le
  have h3 := two_le_inv_pow_swapFactor hδ0 hδ1
  calc potential (realRows B) ≤ (sqNormSum B : ℝ) ^ (n * (n - 1) / 2) := h1
    _ ≤ ((2 : ℝ) ^ (Nat.log 2 (sqNormSum B) + 1)) ^ (n * (n - 1) / 2) :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) h2 _
    _ ≤ ((((δ : ℝ)⁻¹) ^ swapFactor δ) ^ (Nat.log 2 (sqNormSum B) + 1)) ^ (n * (n - 1) / 2) :=
        pow_le_pow_left₀ (by positivity) (pow_le_pow_left₀ (by norm_num) h3 _) _
    _ = ((δ : ℝ)⁻¹) ^ swapBudgetOf δ n (sqNormSum B) := by
        rw [← pow_mul, ← pow_mul, swapBudgetOf, mul_assoc]
    _ < ((δ : ℝ)⁻¹) ^ (swapBudgetOf δ n (sqNormSum B) + 1) :=
        pow_lt_pow_right₀ hgt (Nat.lt_succ_self _)

/-- The case `δ = 3/4` of `potential_realRows_lt_inv_pow`. -/
theorem potential_realRows_lt (B : Vector (Vector ℤ m) n) :
    potential (realRows B) < (((3 / 4 : ℚ) : ℝ))⁻¹ ^ (swapBudget n (sqNormSum B) + 1) := by
  rw [← swapBudgetOf_three_div_four]
  exact potential_realRows_lt_inv_pow (by norm_num) (by norm_num) B

/-- The LLL algorithm ([LenstraLenstraLovasz1982], (1.15)–(1.21)) with parameter `δ` in place
of `3/4` on the rows of an integer matrix, run for at most `n + 2 (swapBudgetOf δ n B + 1)`
rounds. The source allows any fixed `δ` with `1/4 < δ < 1` (remark after (1.5)); termination and
reducedness need only `0 < δ < 1` (`isReduced_lllWith`), and `1/4 < δ` is used for the
approximation bound (`dotProduct_lllWith_zero_le`). -/
def lllWith (δ : ℚ) (B : Vector (Vector ℤ m) n) : Vector (Vector ℤ m) n :=
  lllLoop δ (n + 2 * (swapBudgetOf δ n (sqNormSum B) + 1)) B 0

/-- Correctness of LLL with parameter `0 < δ < 1`: on linearly independent rows, the output is
`δ`-reduced and linearly independent. -/
theorem isReduced_lllWith {δ : ℚ} (hδ0 : 0 < δ) (hδ1 : δ < 1) (B : Vector (Vector ℤ m) n)
    (hB : LinearIndependent ℝ (realRows B)) :
    IsReduced (δ : ℝ) (realRows (lllWith δ B)) ∧
      LinearIndependent ℝ (realRows (lllWith δ B)) :=
  lllLoop_spec hδ0 (n + 2 * (swapBudgetOf δ n (sqNormSum B) + 1)) B 0
    (swapBudgetOf δ n (sqNormSum B) + 1) hB (PrefixReduced.zero _ _)
    (potential_realRows_lt_inv_pow hδ0 hδ1 B) (by omega)

/-- LLL with any parameter preserves the lattice. -/
theorem span_lllWith (δ : ℚ) (B : Vector (Vector ℤ m) n) :
    Submodule.span ℤ (Set.range (rows (lllWith δ B))) =
      Submodule.span ℤ (Set.range (rows B)) :=
  span_lllLoop _ _ _ _

/-- The LLL algorithm ([LenstraLenstraLovasz1982], (1.15)–(1.21)) with `δ = 3/4` on the rows of
an integer matrix, run for at most `n + 2 (swapBudget n B + 1)` rounds. -/
def lll (B : Vector (Vector ℤ m) n) : Vector (Vector ℤ m) n :=
  lllLoop (3 / 4) (n + 2 * (swapBudget n (sqNormSum B) + 1)) B 0

theorem lll_eq_lllWith (B : Vector (Vector ℤ m) n) : lll B = lllWith (3 / 4) B := by
  rw [lll, lllWith, swapBudgetOf_three_div_four]

/-- Correctness of LLL: on linearly independent rows, the output is `3/4`-reduced and linearly
independent. -/
theorem isReduced_lll (B : Vector (Vector ℤ m) n) (hB : LinearIndependent ℝ (realRows B)) :
    IsReduced (3 / 4) (realRows (lll B)) ∧ LinearIndependent ℝ (realRows (lll B)) := by
  have h := isReduced_lllWith (δ := 3 / 4) (by norm_num) (by norm_num) B hB
  have hδ : ((3 / 4 : ℚ) : ℝ) = 3 / 4 := by norm_num
  rw [hδ, ← lll_eq_lllWith] at h
  exact h

/-- LLL preserves the lattice. -/
theorem span_lll (B : Vector (Vector ℤ m) n) :
    Submodule.span ℤ (Set.range (rows (lll B))) = Submodule.span ℤ (Set.range (rows B)) :=
  span_lllLoop _ _ _ _

theorem norm_sq_intToEuclidean (v : Fin m → ℤ) :
    ‖intToEuclidean v‖ ^ 2 = ((dotProduct v v : ℤ) : ℝ) := by
  rw [intToEuclidean_eq_ratToEuclidean, norm_sq_ratToEuclidean]
  simp [dotProduct]

/-- Proposition (1.11) of [LenstraLenstraLovasz1982] with the constant of the remark after
(1.9): for `1/4 < δ < 1` and `n + 1` linearly independent integer rows, the first row of
`lllWith δ B` satisfies `|b₀|² ≤ (4/(4δ - 1))ⁿ |x|²` for every nonzero `x` in the lattice. As
`δ → 1` the factor tends to `(4/3)ⁿ`. -/
theorem dotProduct_lllWith_zero_le {δ : ℚ} (hδ : 1 / 4 < δ) (hδ1 : δ < 1)
    (B : Vector (Vector ℤ m) (n + 1)) (hB : LinearIndependent ℝ (realRows B)) {x : Fin m → ℤ}
    (hx : x ∈ Submodule.span ℤ (Set.range (rows B))) (hx0 : x ≠ 0) :
    ((dotProduct (rows (lllWith δ B) 0) (rows (lllWith δ B) 0) : ℤ) : ℚ) ≤
      (4 / (4 * δ - 1)) ^ n * ((dotProduct x x : ℤ) : ℚ) := by
  obtain ⟨hred, -⟩ := isReduced_lllWith (by linarith) hδ1 B hB
  have hmem : intToEuclidean x ∈ Submodule.span ℤ (Set.range (realRows (lllWith δ B))) := by
    rw [span_realRows, span_lllWith]
    exact Submodule.mem_map_of_mem hx
  have hne : intToEuclidean x ≠ 0 := fun h =>
    hx0 (intToEuclidean_injective (h.trans (map_zero _).symm))
  have hδ' : (1 : ℝ) / 4 < δ := by
    rw [show (1 : ℝ) / 4 = ((1 / 4 : ℚ) : ℝ) by norm_num]
    exact Rat.cast_lt.2 hδ
  have hδ1' : (δ : ℝ) ≤ 1 := by exact_mod_cast hδ1.le
  have h := hred.norm_sq_le hδ' hδ1' hmem hne
  rw [norm_sq_intToEuclidean, norm_sq_realRows] at h
  exact_mod_cast h

/-- For `n + 1` linearly independent integer rows, the first output row satisfies
`|b₀|² ≤ 2ⁿ |x|²` for every nonzero `x` in the lattice. This is (1.11) of
[LenstraLenstraLovasz1982], `|b₁|² ≤ 2ⁿ⁻¹ |x|²` for `n` vectors in the source's indexing. -/
theorem dotProduct_lll_zero_le (B : Vector (Vector ℤ m) (n + 1))
    (hB : LinearIndependent ℝ (realRows B)) {x : Fin m → ℤ}
    (hx : x ∈ Submodule.span ℤ (Set.range (rows B))) (hx0 : x ≠ 0) :
    dotProduct (rows (lll B) 0) (rows (lll B) 0) ≤ 2 ^ n * dotProduct x x := by
  have h := dotProduct_lllWith_zero_le (δ := 3 / 4) (by norm_num) (by norm_num) B hB hx hx0
  rw [← lll_eq_lllWith] at h
  norm_num at h
  exact_mod_cast h

/-- A decidable criterion for the hypothesis of `isReduced_lll`: the integer Gram determinant
is nonzero. -/
theorem linearIndependent_realRows_iff (B : Vector (Vector ℤ m) n) :
    LinearIndependent ℝ (realRows B) ↔
      (Matrix.of fun i j => dotProduct (rows B i) (rows B j)).det ≠ 0 := by
  rw [← Matrix.det_gram_ne_zero_iff_linearIndependent (𝕜 := ℝ)]
  have h : Matrix.gram ℝ (realRows B) =
      (Int.castRingHom ℝ).mapMatrix (Matrix.of fun i j => dotProduct (rows B i) (rows B j)) := by
    ext i j
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, eq_intCast, ← inner_realRows]
    rfl
  rw [h, ← RingHom.map_det, eq_intCast, Int.cast_ne_zero]

end Cslib.Algorithms.LatticeReduction
