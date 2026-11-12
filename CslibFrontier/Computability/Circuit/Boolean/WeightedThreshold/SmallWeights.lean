/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/

module
-- upstream: candidate

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.LinearAlgebra.Matrix.AbsoluteValue
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Basic.Real.Basic

/-!
# Small integer weights for threshold functions

A threshold function `[t ≤ ∑ cᵢ xᵢ]` of `N` Boolean inputs, with arbitrary nonnegative integer
weights, is also a strict threshold function `[θ < ∑ uᵢ xᵢ]` with integer weights and bias of
absolute value at most `(N + 1) · (N + 1)!` (`Cslib.SmallWeights.exists_small_threshold`)
[Muroga][Muroga1971].

The separating weight vectors `v` with `±(x, -1) ⬝ v ≥ 1` on every input `x` form a polyhedron
whose rows span. Moving a feasible point along a direction orthogonal to its tight rows until a
further row becomes tight (`Cslib.SmallWeights.exists_tightRank_lt`) reaches a point whose tight
rows span (`Cslib.SmallWeights.exists_span_tight_eq_top`), so `N + 1` linearly independent rows
are tight there (`Cslib.SmallWeights.exists_tight_basis`). By Cramer's rule the adjugate of their
matrix, whose entries lie in `{-1, 0, 1}`, gives an integer point with every row at least `1` and
coordinates bounded through `Matrix.det_le` (`Cslib.SmallWeights.exists_int_point`).

## Main results

* `Cslib.SmallWeights.exists_tight_basis`: a vertex of a feasible polyhedron whose rows span.
* `Cslib.SmallWeights.exists_int_point`: integer points from a vertex.
* `Cslib.SmallWeights.exists_small_threshold`: Muroga's small weights.

## References

* [S. Muroga, *Threshold Logic and Its Applications*][Muroga1971]
-/

@[expose] public section

namespace Cslib.SmallWeights

open Finset Module Matrix

variable {ι : Type*} [Finite ι] {m : ℕ}

/-- The rows of `r` tight at `v`: those with `r j ⬝ᵥ v = 1`. -/
noncomputable def tight (r : ι → Fin m → ℝ) (v : Fin m → ℝ) : Set (Fin m → ℝ) :=
  r '' {j | r j ⬝ᵥ v = 1}

/-- The rank of the rows tight at `v`. -/
noncomputable def tightRank (r : ι → Fin m → ℝ) (v : Fin m → ℝ) : ℕ :=
  finrank ℝ (Submodule.span ℝ (tight r v))

omit [Finite ι] in
theorem tightRank_le (r : ι → Fin m → ℝ) (v : Fin m → ℝ) : tightRank r v ≤ m :=
  (Submodule.finrank_le _).trans_eq (by simp)

/-- A linear functional on `Fin m → ℝ` is the dot product with its values on the basis vectors. -/
theorem dual_apply_eq_dotProduct (f : Module.Dual ℝ (Fin m → ℝ)) (x : Fin m → ℝ) :
    f x = x ⬝ᵥ fun i => f (Pi.single i 1) := by
  rw [LinearMap.pi_apply_eq_sum_univ f x, dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_eq_mul]
  congr 2
  funext j
  simp [Pi.single_apply, eq_comm]

/-- **One step towards a vertex**: if the rows tight at a feasible point do not span, moving along
a direction orthogonal to them makes a further row tight, so the tight rank grows. -/
theorem exists_tightRank_lt (r : ι → Fin m → ℝ) (hspan : Submodule.span ℝ (Set.range r) = ⊤)
    {v : Fin m → ℝ} (hv : ∀ j, 1 ≤ r j ⬝ᵥ v) (hlt : Submodule.span ℝ (tight r v) ≠ ⊤) :
    ∃ v' : Fin m → ℝ, (∀ j, 1 ≤ r j ⬝ᵥ v') ∧ tightRank r v < tightRank r v' := by
  have : Fintype ι := Fintype.ofFinite ι
  obtain ⟨f₀, hf₀, hker⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hlt)
  -- some row is not annihilated
  have hrow : ∃ j, f₀ (r j) ≠ 0 := by
    by_contra h
    push Not at h
    apply hf₀
    have : Submodule.span ℝ (Set.range r) ≤ LinearMap.ker f₀ :=
      Submodule.span_le.mpr (Set.range_subset_iff.mpr fun j => h j)
    rw [hspan, top_le_iff] at this
    exact LinearMap.ker_eq_top.mp this
  obtain ⟨j₀, hj₀⟩ := hrow
  -- orient the functional so that `j₀` decreases
  let f : Module.Dual ℝ (Fin m → ℝ) := if f₀ (r j₀) < 0 then f₀ else -f₀
  have hfj₀ : f (r j₀) < 0 := by
    simp only [f]
    split_ifs with h
    · exact h
    · simp only [LinearMap.neg_apply, neg_neg_iff_pos]
      exact lt_of_le_of_ne (not_lt.mp h) (Ne.symm hj₀)
  have hfker : Submodule.span ℝ (tight r v) ≤ LinearMap.ker f := by
    intro x hx
    have := hker hx
    simp only [LinearMap.mem_ker] at this ⊢
    simp only [f]
    split_ifs <;> simp [this]
  set d : Fin m → ℝ := fun i => f (Pi.single i 1)
  have hfd (x : Fin m → ℝ) : f x = x ⬝ᵥ d := dual_apply_eq_dotProduct f x
  -- the decreasing rows and the step length
  set J := univ.filter fun j => r j ⬝ᵥ d < 0
  have hJ : J.Nonempty := ⟨j₀, by simpa [J, ← hfd] using hfj₀⟩
  let ratio : ι → ℝ := fun j => (r j ⬝ᵥ v - 1) / -(r j ⬝ᵥ d)
  obtain ⟨j₁, hj₁J, hj₁⟩ := J.exists_min_image ratio hJ
  have hj₁d : r j₁ ⬝ᵥ d < 0 := (mem_filter.mp hj₁J).2
  set t := ratio j₁
  have ht : 0 ≤ t := div_nonneg (by linarith [hv j₁]) (by linarith)
  set v' := v + t • d
  have hdot (j : ι) : r j ⬝ᵥ v' = r j ⬝ᵥ v + t * (r j ⬝ᵥ d) := by
    simp [v', dotProduct_add, dotProduct_smul]
  refine ⟨v', fun j => ?_, ?_⟩
  · rw [hdot]
    by_cases hj : r j ⬝ᵥ d < 0
    · have hle : t ≤ ratio j := hj₁ j (mem_filter.mpr ⟨mem_univ _, hj⟩)
      have hpos : 0 < -(r j ⬝ᵥ d) := by linarith
      have : t * -(r j ⬝ᵥ d) ≤ r j ⬝ᵥ v - 1 := by
        have := mul_le_mul_of_nonneg_right hle hpos.le
        rwa [div_mul_cancel₀ _ hpos.ne'] at this
      linarith
    · have := mul_nonneg ht (not_lt.mp hj)
      linarith [hv j]
  · -- the tight rows at `v` stay tight, and `j₁` becomes tight
    have hsub : tight r v ⊆ tight r v' := by
      rintro _ ⟨j, hj, rfl⟩
      refine ⟨j, ?_, rfl⟩
      have hj' : r j ⬝ᵥ v = 1 := hj
      have h0 : f (r j) = 0 := hfker (Submodule.subset_span ⟨j, hj, rfl⟩)
      change r j ⬝ᵥ v' = 1
      rw [hdot, ← hfd, h0, mul_zero, add_zero, hj']
    have hj₁t : r j₁ ∈ tight r v' := by
      refine ⟨j₁, ?_, rfl⟩
      change r j₁ ⬝ᵥ v' = 1
      rw [hdot]
      have hne : r j₁ ⬝ᵥ d ≠ 0 := hj₁d.ne
      simp only [t, ratio]
      field_simp
      ring
    have hnot : r j₁ ∉ Submodule.span ℝ (tight r v) := by
      intro hmem
      have h0 : f (r j₁) = 0 := hfker hmem
      rw [hfd] at h0
      linarith
    have hlt' : Submodule.span ℝ (tight r v) < Submodule.span ℝ (tight r v') := by
      refine lt_of_le_of_ne (Submodule.span_mono hsub) fun heq => hnot ?_
      rw [heq]
      exact Submodule.subset_span hj₁t
    exact Submodule.finrank_lt_finrank_of_lt hlt'

/-- **A vertex of a feasible polyhedron whose rows span**: some feasible point has tight rows
spanning the whole space. -/
theorem exists_span_tight_eq_top (r : ι → Fin m → ℝ) (hspan : Submodule.span ℝ (Set.range r) = ⊤)
    (hfeas : ∃ v : Fin m → ℝ, ∀ j, 1 ≤ r j ⬝ᵥ v) :
    ∃ v : Fin m → ℝ, (∀ j, 1 ≤ r j ⬝ᵥ v) ∧ Submodule.span ℝ (tight r v) = ⊤ := by
  classical
  let P : ℕ → Prop := fun k => ∃ v : Fin m → ℝ, (∀ j, 1 ≤ r j ⬝ᵥ v) ∧ k ≤ tightRank r v
  have hP0 : P 0 := by
    obtain ⟨v, hv⟩ := hfeas
    exact ⟨v, hv, Nat.zero_le _⟩
  obtain ⟨v, hv, hK⟩ := Nat.findGreatest_spec (Nat.zero_le m) hP0
  refine ⟨v, hv, ?_⟩
  by_contra hne
  obtain ⟨v', hv', hlt⟩ := exists_tightRank_lt r hspan hv hne
  have hPv' : P (tightRank r v') := ⟨v', hv', le_rfl⟩
  have := Nat.le_findGreatest (tightRank_le r v') hPv'
  omega

/-- **Tight linearly independent rows at a vertex**: there are a feasible point and `m` linearly
independent rows that are tight at it. -/
theorem exists_tight_basis (r : ι → Fin m → ℝ) (hspan : Submodule.span ℝ (Set.range r) = ⊤)
    (hfeas : ∃ v : Fin m → ℝ, ∀ j, 1 ≤ r j ⬝ᵥ v) :
    ∃ (σ : Fin m → ι) (v : Fin m → ℝ), (∀ j, 1 ≤ r j ⬝ᵥ v) ∧ (∀ k, r (σ k) ⬝ᵥ v = 1) ∧
      LinearIndependent ℝ (fun k => r (σ k)) := by
  classical
  obtain ⟨v, hv, htop⟩ := exists_span_tight_eq_top r hspan hfeas
  obtain ⟨b, hbsub, hbspan, hbli⟩ := exists_linearIndependent ℝ (tight r v)
  have hbfin : b.Finite := hbli.setFinite
  have : Fintype b := hbfin.fintype
  let B : Basis b ℝ (Fin m → ℝ) := Basis.mk hbli (by rw [Subtype.range_coe, hbspan, htop])
  have hcard : Fintype.card b = m := by
    rw [← Module.finrank_eq_card_basis B, Module.finrank_fin_fun]
  let e : Fin m ≃ b := (Fintype.equivFinOfCardEq hcard).symm
  have hmem (k : Fin m) : ∃ j, r j ⬝ᵥ v = 1 ∧ r j = (e k : Fin m → ℝ) := by
    obtain ⟨j, hj, hjr⟩ := hbsub (e k).2
    exact ⟨j, hj, hjr⟩
  choose σ hσ hσr using hmem
  refine ⟨σ, v, hv, hσ, ?_⟩
  have : (fun k => r (σ k)) = (fun x : b => (x : Fin m → ℝ)) ∘ e := funext fun k => hσr k
  rw [this]
  exact hbli.comp e e.injective

/-- The real vector of an integer vector. -/
abbrev toReal (x : Fin m → ℤ) : Fin m → ℝ := fun i => (x i : ℝ)

theorem toReal_dotProduct (x y : Fin m → ℤ) :
    toReal x ⬝ᵥ toReal y = ((x ⬝ᵥ y : ℤ) : ℝ) := by
  simp [dotProduct]

omit [Finite ι] in
/-- **Integer weights from a vertex, by Cramer's rule**: if the integer rows `R` with entries in
`[-1, 1]` have a feasible point at which `m` linearly independent rows `R ∘ σ` are tight, there is
an integer point with every row at least `1` and every coordinate at most `m · m!` in absolute
value. -/
theorem exists_int_point (R : ι → Fin m → ℤ) (hR : ∀ j i, |R j i| ≤ 1) (σ : Fin m → ι)
    (v : Fin m → ℝ) (hv : ∀ j, 1 ≤ toReal (R j) ⬝ᵥ v) (htight : ∀ k, toReal (R (σ k)) ⬝ᵥ v = 1)
    (hli : LinearIndependent ℝ (fun k => toReal (R (σ k)))) :
    ∃ u : Fin m → ℤ, (∀ j, 1 ≤ R j ⬝ᵥ u) ∧ ∀ i, |u i| ≤ m * m.factorial := by
  classical
  let A : Matrix (Fin m) (Fin m) ℤ := Matrix.of fun k i => R (σ k) i
  let AR : Matrix (Fin m) (Fin m) ℝ := (Int.castRingHom ℝ).mapMatrix A
  have hAR : AR.row = fun k => toReal (R (σ k)) := rfl
  have hdetR : AR.det ≠ 0 := by
    have := (Matrix.linearIndependent_row_iff_isUnit (A := AR)).mp (hAR ▸ hli)
    exact (Matrix.isUnit_iff_isUnit_det AR).mp this |>.ne_zero
  have hdet : A.det ≠ 0 := by
    intro h
    apply hdetR
    rw [show AR.det = ((Int.castRingHom ℝ) A.det) from (RingHom.map_det _ _).symm, h, map_zero]
  have hAv : AR *ᵥ v = fun _ => 1 := funext fun k => htight k
  let w : Fin m → ℤ := A.adjugate *ᵥ fun _ => 1
  have hw : toReal w = (A.det : ℝ) • v := by
    have hadj : (Int.castRingHom ℝ).mapMatrix A.adjugate * AR = (A.det : ℝ) • 1 := by
      rw [← map_mul, Matrix.adjugate_mul]
      ext i j
      rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.smul_apply, Matrix.smul_apply,
        Matrix.one_apply, Matrix.one_apply]
      split_ifs <;> simp
    have := congrArg (· *ᵥ v) hadj
    simp only [← Matrix.mulVec_mulVec, hAv, Matrix.smul_mulVec, Matrix.one_mulVec] at this
    rw [← this]
    funext i
    simp [w, toReal, Matrix.mulVec, dotProduct]
  refine ⟨A.det.sign • w, fun j => ?_, fun i => ?_⟩
  · have hreal : ((R j ⬝ᵥ (A.det.sign • w) : ℤ) : ℝ) =
        ((|A.det| : ℤ) : ℝ) * (toReal (R j) ⬝ᵥ v) := by
      rw [dotProduct_smul, smul_eq_mul, Int.cast_mul, ← toReal_dotProduct, hw, dotProduct_smul,
        smul_eq_mul, ← Int.sign_mul_self_eq_abs]
      push_cast
      ring
    have hpos : (1 : ℝ) ≤ ((|A.det| : ℤ) : ℝ) := by exact_mod_cast Int.one_le_abs hdet
    have : (1 : ℝ) ≤ ((R j ⬝ᵥ (A.det.sign • w) : ℤ) : ℝ) := by
      rw [hreal]
      nlinarith [hv j]
    exact_mod_cast this
  · -- each adjugate entry is a determinant of a matrix with entries in `[-1, 1]`
    have hentry (k : Fin m) : |A.adjugate i k| ≤ m.factorial := by
      rw [Matrix.adjugate_apply]
      have := Matrix.det_le (abv := AbsoluteValue.abs) (x := (1 : ℤ))
        (A := A.updateRow k (Pi.single i 1)) fun a b => by
          by_cases hak : a = k
          · subst hak
            simp only [Matrix.updateRow_self, Pi.single_apply]
            split_ifs <;> simp
          · rw [Matrix.updateRow_ne hak]
            exact hR _ _
      simpa [Fintype.card_fin] using this
    have hsign : |A.det.sign| ≤ 1 := by
      rcases Int.sign_trichotomy A.det with h | h | h <;> simp [h]
    calc |(A.det.sign • w) i| = |A.det.sign| * |w i| := by simp [abs_mul]
      _ ≤ 1 * |w i| := mul_le_mul_of_nonneg_right hsign (abs_nonneg _)
      _ = |∑ k, A.adjugate i k| := by simp [w, Matrix.mulVec, dotProduct]
      _ ≤ ∑ k, |A.adjugate i k| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _k : Fin m, (m.factorial : ℤ) := Finset.sum_le_sum fun k _ => hentry k
      _ = m * m.factorial := by simp

/-- The dot product with an appended last coordinate. -/
theorem snoc_dotProduct_snoc {R : Type*} [CommSemiring R] {N : ℕ} (x y : Fin N → R) (a b : R) :
    (Fin.snoc x a : Fin (N + 1) → R) ⬝ᵥ Fin.snoc y b = x ⬝ᵥ y + a * b := by
  simp [dotProduct, Fin.sum_univ_castSucc]

/-- The weight bound `(N + 1) · (N + 1)!` of `N`-input threshold functions. -/
def weightBound (N : ℕ) : ℕ := (N + 1) * (N + 1).factorial

/-- **Muroga's small weights** [Muroga][Muroga1971]: a threshold
function with nonnegative integer weights `c` and threshold `t` on `N` inputs is also a strict
threshold function with integer weights and threshold of absolute value at most
`(N + 1) · (N + 1)!`. -/
theorem exists_small_threshold {N : ℕ} (c : Fin N → ℕ) (t : ℕ) :
    ∃ (u : Fin N → ℤ) (θ : ℤ), (∀ i, |u i| ≤ weightBound N) ∧ |θ| ≤ weightBound N ∧
      ∀ x : Fin N → Bool, (t ≤ ∑ i, c i * (x i).toNat ↔ θ < ∑ i, u i * (x i).toNat) := by
  classical
  let val : (Fin N → Bool) → Fin N → ℤ := fun x i => ((x i).toNat : ℤ)
  let sgn : (Fin N → Bool) → ℤ := fun x => if t ≤ ∑ i, c i * (x i).toNat then 1 else -1
  let R : (Fin N → Bool) → Fin (N + 1) → ℤ := fun x => sgn x • Fin.snoc (val x) (-1)
  have hsgn (x : Fin N → Bool) : |sgn x| = 1 := by simp only [sgn]; split_ifs <;> simp
  have hR : ∀ x k, |R x k| ≤ 1 := by
    intro x k
    simp only [R, Pi.smul_apply, smul_eq_mul, abs_mul, hsgn, one_mul]
    induction k using Fin.lastCases with
    | last => simp
    | cast i => simp only [Fin.snoc_castSucc, val]; cases x i <;> simp
  -- the rows span
  have hspan : Submodule.span ℝ (Set.range fun x => toReal (R x)) = ⊤ := by
    set S := Submodule.span ℝ (Set.range fun x => toReal (R x))
    have hmem (x : Fin N → Bool) : toReal (Fin.snoc (val x) (-1)) ∈ S := by
      have hsq : (sgn x : ℝ) * sgn x = 1 := by simp only [sgn]; split_ifs <;> norm_num
      have : toReal (Fin.snoc (val x) (-1)) = (sgn x : ℝ) • toReal (R x) := by
        funext k
        simp only [toReal, R, Pi.smul_apply, smul_eq_mul, Int.cast_mul]
        rw [← mul_assoc, hsq, one_mul]
      rw [this]
      exact S.smul_mem _ (Submodule.subset_span ⟨x, rfl⟩)
    have hlast : (Pi.single (Fin.last N) 1 : Fin (N + 1) → ℝ) ∈ S := by
      have h := S.neg_mem (hmem fun _ => false)
      convert h using 1
      funext k
      induction k using Fin.lastCases with
      | last => simp [toReal]
      | cast i => simp [toReal, val, Fin.castSucc_ne_last]
    have hcast (i : Fin N) : (Pi.single i.castSucc 1 : Fin (N + 1) → ℝ) ∈ S := by
      have h := S.add_mem (hmem fun j => decide (j = i)) hlast
      convert h using 1
      funext k
      induction k using Fin.lastCases with
      | last => simp [toReal, Fin.castSucc_ne_last]
      | cast j =>
        by_cases hij : j = i
        · subst hij; simp [toReal, val, Fin.castSucc_ne_last]
        · simp [toReal, val, hij, Fin.castSucc_ne_last,
            Fin.castSucc_injective N |>.ne hij]
    rw [eq_top_iff, ← (Pi.basisFun ℝ (Fin (N + 1))).span_eq, Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    induction k using Fin.lastCases with
    | last => simpa using hlast
    | cast i => simpa using hcast i
  -- a feasible point
  have hfeas : ∃ v : Fin (N + 1) → ℝ, ∀ x, 1 ≤ toReal (R x) ⬝ᵥ v := by
    refine ⟨Fin.snoc (fun i => 2 * (c i : ℝ)) (2 * t - 1), fun x => ?_⟩
    have hdot : toReal (R x) ⬝ᵥ (Fin.snoc (fun i => 2 * (c i : ℝ)) (2 * t - 1)) =
        (sgn x : ℝ) * (2 * ((∑ i, c i * (x i).toNat : ℕ) : ℝ) - (2 * t - 1)) := by
      have : toReal (R x) = Fin.snoc (fun i => (sgn x : ℝ) * (val x i : ℝ)) (-(sgn x : ℝ)) := by
        funext k
        induction k using Fin.lastCases with
        | last => simp [toReal, R]
        | cast i => simp [toReal, R]
      rw [this, snoc_dotProduct_snoc]
      simp only [dotProduct, val, Int.cast_natCast]
      push_cast
      have hsum : ∑ i, (sgn x : ℝ) * ((x i).toNat : ℝ) * (2 * (c i : ℝ)) =
          (sgn x : ℝ) * (2 * ∑ i, (c i : ℝ) * ((x i).toNat : ℝ)) := by
        rw [Finset.mul_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
      rw [hsum]
      ring
    rw [hdot]
    simp only [sgn]
    split_ifs with h
    · have : (t : ℝ) ≤ ((∑ i, c i * (x i).toNat : ℕ) : ℝ) := by exact_mod_cast h
      push_cast at this ⊢
      linarith
    · have : ((∑ i, c i * (x i).toNat : ℕ) : ℝ) + 1 ≤ t := by
        exact_mod_cast Nat.lt_of_not_le h
      push_cast at this ⊢
      linarith
  obtain ⟨σ, v, hv, htight, hli⟩ := exists_tight_basis _ hspan hfeas
  obtain ⟨u, hu, hub⟩ := exists_int_point R hR σ v hv htight hli
  refine ⟨fun i => u i.castSucc, u (Fin.last N), fun i => by simpa [weightBound] using hub _,
    by simpa [weightBound] using hub _, fun x => ?_⟩
  have hrow : R x ⬝ᵥ u = sgn x * (∑ i, u i.castSucc * (x i).toNat - u (Fin.last N)) := by
    have : u = Fin.snoc (fun i => u i.castSucc) (u (Fin.last N)) := by
      funext k
      induction k using Fin.lastCases <;> simp
    rw [this, show R x = sgn x • Fin.snoc (val x) (-1) from rfl, smul_dotProduct,
      snoc_dotProduct_snoc]
    simp only [dotProduct, val, smul_eq_mul, Fin.snoc_castSucc, Fin.snoc_last]
    rw [Finset.sum_congr rfl fun i _ => mul_comm ((x i).toNat : ℤ) (u i.castSucc)]
    ring
  have h1 := hu x
  rw [hrow] at h1
  simp only [sgn] at h1
  split_ifs at h1 with h
  · exact ⟨fun _ => by linarith, fun _ => h⟩
  · exact ⟨fun h' => absurd h' h, fun h' => by linarith⟩

end Cslib.SmallWeights
