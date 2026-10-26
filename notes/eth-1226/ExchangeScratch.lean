import Mathlib

/-! Scratch: §4.1–4.2 exchange structure (research prototype). -/

open Finset Matrix

namespace Scratch1226X

variable {α : Type*} [Fintype α] [DecidableEq α] [LinearOrder α] {Q : ℕ}

/-- Auxiliary labels: a pair `(a_u s, d_u s)` at every position `s`. -/
abbrev Label (α : Type*) (Q : ℕ) := Fin Q → α × α

/-- Exchange the two entries at every position of `S`. -/
def exch (S : Finset (Fin Q)) (u : Label α Q) : Label α Q :=
  fun s => if s ∈ S then (u s).swap else u s

omit [Fintype α] [DecidableEq α] [LinearOrder α] in
theorem exch_exch (S T : Finset (Fin Q)) (u : Label α Q) :
    exch T (exch S u) = exch (symmDiff S T) u := by
  funext s
  by_cases hS : s ∈ S <;> by_cases hT : s ∈ T <;> simp [exch, hS, hT, Finset.mem_symmDiff]

/-- The permutation matrix of `exch S`: `(Π_S ζ) u = ζ (exch S u)`. -/
def exchMatrix (S : Finset (Fin Q)) : Matrix (Label α Q) (Label α Q) ℚ :=
  of fun u y => if y = exch S u then 1 else 0

omit [LinearOrder α] in
theorem exchMatrix_mulVec (S : Finset (Fin Q)) (ζ : Label α Q → ℚ) (u : Label α Q) :
    (exchMatrix S *ᵥ ζ) u = ζ (exch S u) := by
  simp [exchMatrix, mulVec, dotProduct]

omit [LinearOrder α] in
theorem exchMatrix_mul (S T : Finset (Fin Q)) :
    (exchMatrix S * exchMatrix T : Matrix (Label α Q) (Label α Q) ℚ) =
      exchMatrix (symmDiff S T) := by
  ext u y
  simp only [exchMatrix, mul_apply, of_apply]
  rw [Finset.sum_eq_single (exch S u)]
  · simp [exch_exch]
  · intro b _ hb; simp [hb]
  · simp

/-- `W₀ = ½ Σ_s (I − Π_s)`. -/
def W0 : Matrix (Label α Q) (Label α Q) ℚ :=
  (1 / 2 : ℚ) • ∑ s : Fin Q, (1 - exchMatrix {s})

/-! ### The product eigenbasis -/

/-- One-position basis functions on `α × α`: for `a ≤ b`, the indicator of `{(a, b), (b, a)}`;
for `a > b`, `e_(a,b) − e_(b,a)`. -/
def psi1 (k z : α × α) : ℚ :=
  if k.1 ≤ k.2 then (if (z.1 = k.1 ∧ z.2 = k.2) ∨ (z.1 = k.2 ∧ z.2 = k.1) then 1 else 0)
  else (if z.1 = k.1 ∧ z.2 = k.2 then 1 else 0) - (if z.1 = k.2 ∧ z.2 = k.1 then 1 else 0)

/-- The sign of `psi1 k` under the swap. -/
def eps (k : α × α) : ℚ := if k.1 ≤ k.2 then 1 else -1

omit [Fintype α] in
theorem psi1_swap (k z : α × α) : psi1 k z.swap = eps k * psi1 k z := by
  obtain ⟨a, b⟩ := k
  obtain ⟨x, y⟩ := z
  simp only [psi1, eps, Prod.swap_prod_mk]
  by_cases hab : a ≤ b
  · simp only [hab, ite_true, one_mul]
    exact if_congr (by tauto) rfl rfl
  · simp only [hab, ite_false]
    split_ifs <;> first | (norm_num; done) | (exfalso; tauto)

omit [Fintype α] in
theorem psi1_eq_zero {k z : α × α} (h1 : ¬(z.1 = k.1 ∧ z.2 = k.2))
    (h2 : ¬(z.1 = k.2 ∧ z.2 = k.1)) : psi1 k z = 0 := by
  unfold psi1; simp [h1, h2]

/-- Normalization weight: `1 / ‖psi1 k‖²`. -/
def wt (k : α × α) : ℚ := if k.1 = k.2 then 1 else 1 / 2

/-- **Resolution of the identity at one position.** -/
theorem sum_psi1_mul_psi1 (z z' : α × α) :
    ∑ k, psi1 k z * psi1 k z' * wt k = if z = z' then 1 else 0 := by
  obtain ⟨x, y⟩ := z
  obtain ⟨x', y'⟩ := z'
  rw [← Finset.sum_subset (subset_univ {(x, y), (y, x)})]
  swap
  · intro k _ hk
    simp only [mem_insert, mem_singleton, not_or] at hk
    rw [psi1_eq_zero, zero_mul, zero_mul]
    · rintro ⟨h1, h2⟩; exact hk.1 (Prod.ext h1.symm h2.symm)
    · rintro ⟨h1, h2⟩; exact hk.2 (Prod.ext h2.symm h1.symm)
  rcases lt_trichotomy x y with hxy | rfl | hxy
  · rw [sum_pair (by simp [hxy.ne])]
    simp only [psi1, wt, hxy.le, not_le.mpr hxy, hxy.ne, hxy.ne', ite_true, ite_false, Prod.mk.injEq]
    by_cases h1 : x' = x <;> by_cases h2 : y' = y <;> by_cases h3 : x' = y <;>
      by_cases h4 : y' = x <;> simp_all <;> grind
  · simp only [mem_singleton, insert_eq_of_mem, sum_singleton]
    simp only [psi1, wt, le_refl, ite_true, Prod.mk.injEq, and_self, or_self, mul_one, one_mul]
    by_cases h1 : x' = x <;> by_cases h2 : y' = x <;> simp_all <;> grind
  · rw [sum_pair (by simp [hxy.ne'])]
    simp only [psi1, wt, hxy.le, not_le.mpr hxy, hxy.ne, hxy.ne', ite_true, ite_false, Prod.mk.injEq]
    by_cases h1 : x' = x <;> by_cases h2 : y' = y <;> by_cases h3 : x' = y <;>
      by_cases h4 : y' = x <;> simp_all <;> grind

/-- Product basis vector. -/
def psi (κ : Label α Q) (u : Label α Q) : ℚ := ∏ s, psi1 (κ s) (u s)

/-- Product weight. -/
def psiWt (κ : Label α Q) : ℚ := ∏ s, wt (κ s)

/-- **Resolution of the identity.** -/
theorem sum_psi_mul_psi (u u' : Label α Q) :
    ∑ κ, psi κ u * psi κ u' * psiWt κ = if u = u' then 1 else 0 := by
  have : ∀ κ : Label α Q, psi κ u * psi κ u' * psiWt κ =
      ∏ s, (psi1 (κ s) (u s) * psi1 (κ s) (u' s) * wt (κ s)) := fun κ => by
    simp only [psi, psiWt, Finset.prod_mul_distrib]
  simp only [this]
  rw [← Fintype.prod_sum (fun s k => psi1 k (u s) * psi1 k (u' s) * wt k)]
  simp only [sum_psi1_mul_psi1, Finset.prod_boole, mem_univ, true_implies, funext_iff]

theorem exchMatrix_mulVec_psi (S : Finset (Fin Q)) (κ : Label α Q) :
    exchMatrix S *ᵥ psi κ = (∏ s ∈ S, eps (κ s)) • psi κ := by
  funext u
  rw [exchMatrix_mulVec, Pi.smul_apply, smul_eq_mul, psi, psi, ← Finset.prod_mul_prod_compl S,
    ← Finset.prod_mul_prod_compl S (fun s => psi1 (κ s) (u s))]
  have h1 : ∏ s ∈ S, psi1 (κ s) (exch S u s) = ∏ s ∈ S, (eps (κ s) * psi1 (κ s) (u s)) :=
    Finset.prod_congr rfl fun s hs => by simp [exch, hs, psi1_swap]
  have h2 : ∏ s ∈ Sᶜ, psi1 (κ s) (exch S u s) = ∏ s ∈ Sᶜ, psi1 (κ s) (u s) :=
    Finset.prod_congr rfl fun s hs => by simp [exch, Finset.mem_compl.mp hs]
  rw [h1, h2, Finset.prod_mul_distrib]
  ring

omit [Fintype α] [DecidableEq α] [LinearOrder α] in
theorem exch_empty (u : Label α Q) : exch ∅ u = u := by
  funext s; simp [exch]

omit [LinearOrder α] in
theorem exchMatrix_empty : (exchMatrix ∅ : Matrix (Label α Q) (Label α Q) ℚ) = 1 := by
  ext u y
  simp [exchMatrix, exch_empty, one_apply, eq_comm]

/-- Positions where `psi1 (κ s)` is odd under the swap. -/
def antiCount (κ : Label α Q) : ℕ := #{s | (κ s).2 < (κ s).1}

theorem W0_mulVec_psi (κ : Label α Q) : W0 *ᵥ psi κ = (antiCount κ : ℚ) • psi κ := by
  rw [W0, smul_mulVec, sum_mulVec]
  simp only [sub_mulVec, one_mulVec, exchMatrix_mulVec_psi, prod_singleton]
  have : ∀ s : Fin Q, psi κ - eps (κ s) • psi κ =
      (if (κ s).2 < (κ s).1 then (2 : ℚ) else 0) • psi κ := fun s => by
    unfold eps
    by_cases h : (κ s).1 ≤ (κ s).2
    · simp [h, not_lt.mpr h]
    · simp only [h, ite_false, not_le.mp h, ite_true]
      funext u; simp; ring
  simp only [this, ← Finset.sum_smul, smul_smul, antiCount, Finset.sum_ite, sum_const_zero,
    add_zero, sum_const, nsmul_eq_mul]
  congr 1
  ring

theorem V0_mulVec_psi (κ : Label α Q) :
    exchMatrix univ *ᵥ psi κ = ((-1 : ℚ) ^ antiCount κ) • psi κ := by
  rw [exchMatrix_mulVec_psi]
  congr 1
  simp only [eps, antiCount, ← not_le]
  rw [Finset.prod_ite, prod_const_one, one_mul, prod_const]

theorem aeval_mulVec_eigen {n : Type*} [Fintype n] [DecidableEq n] (W : Matrix n n ℚ)
    (v : n → ℚ) (c : ℚ) (h : W *ᵥ v = c • v) (p : Polynomial ℚ) :
    Polynomial.aeval W p *ᵥ v = p.eval c • v := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, add_mulVec, hp, hq, Polynomial.eval_add, add_smul]
  | monomial k a =>
    have hk : ∀ k : ℕ, (W ^ k) *ᵥ v = c ^ k • v := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        rw [pow_succ, ← mulVec_mulVec, h, mulVec_smul, ih, smul_smul, pow_succ, mul_comm]
    rw [Polynomial.aeval_monomial, Polynomial.eval_monomial, Algebra.algebraMap_eq_smul_one,
      smul_mul_assoc, one_mul, smul_mulVec, hk, smul_smul]

/-- `M₀ = V₀ f(W₀)`. -/
noncomputable def M0 (f : Polynomial ℚ) : Matrix (Label α Q) (Label α Q) ℚ :=
  exchMatrix univ * Polynomial.aeval W0 f

theorem M0_mulVec_psi (f : Polynomial ℚ) (κ : Label α Q) :
    M0 f *ᵥ psi κ = ((-1 : ℚ) ^ antiCount κ * f.eval (antiCount κ : ℚ)) • psi κ := by
  rw [M0, ← mulVec_mulVec, aeval_mulVec_eigen _ _ _ (W0_mulVec_psi κ), mulVec_smul,
    V0_mulVec_psi, smul_smul, mul_comm]

/-- **Lemma 4.1 (kernel).** If `f(j) = (−1)^j` for `j ∈ I`, then `M₀` fixes every `ξ` orthogonal to
the basis vectors `psi κ` with `antiCount κ ∉ I`. -/
theorem M0_mulVec_of_orthogonal (f : Polynomial ℚ) (I : Finset ℕ)
    (hf : ∀ j ∈ I, f.eval (j : ℚ) = (-1) ^ j) (ξ : Label α Q → ℚ)
    (hξ : ∀ κ, antiCount κ ∉ I → psi κ ⬝ᵥ ξ = 0) : M0 f *ᵥ ξ = ξ := by
  have hexp : ξ = ∑ κ, (psiWt κ * (psi κ ⬝ᵥ ξ)) • psi κ := by
    funext u
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, dotProduct, Finset.mul_sum,
      Finset.sum_mul]
    rw [Finset.sum_comm]
    have := fun u' => sum_psi_mul_psi (α := α) (Q := Q) u u'
    simp_rw [show ∀ κ u', psiWt κ * (psi κ u' * ξ u') * psi κ u =
      ξ u' * (psi κ u * psi κ u' * psiWt κ) from fun _ _ => by ring, ← Finset.mul_sum, this]
    simp
  rw [hexp, mulVec_sum]
  refine Finset.sum_congr rfl fun κ _ => ?_
  rw [mulVec_smul, M0_mulVec_psi]
  by_cases hκ : antiCount κ ∈ I
  · rw [hf _ hκ, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_smul]
  · rw [hξ κ hκ, mul_zero, zero_smul, zero_smul]

/-! ### Lemma 4.2 -/

/-- Matrices whose nonzero entries `(u, y)` have at most `k` positions with `a_y s ≠ d_u s`. -/
def FewMismatches (k : ℕ) (M : Matrix (Label α Q) (Label α Q) ℚ) : Prop :=
  ∀ u y, M u y ≠ 0 → #{s | (y s).1 ≠ (u s).2} ≤ k

/-- Combinations of exchange matrices with at most `k` exchanged positions. -/
def lowSpan (k : ℕ) : Submodule ℚ (Matrix (Label α Q) (Label α Q) ℚ) :=
  Submodule.span ℚ {M | ∃ S : Finset (Fin Q), #S ≤ k ∧ M = exchMatrix S}

theorem lowSpan_mono {k l : ℕ} (h : k ≤ l) : (lowSpan k : Submodule ℚ
    (Matrix (Label α Q) (Label α Q) ℚ)) ≤ lowSpan l :=
  Submodule.span_mono fun _ ⟨S, hS, e⟩ => ⟨S, hS.trans h, e⟩

theorem mul_exchMatrix_mem_lowSpan {k : ℕ} {M : Matrix (Label α Q) (Label α Q) ℚ}
    (hM : M ∈ lowSpan k) (s : Fin Q) : M * exchMatrix {s} ∈ lowSpan (k + 1) := by
  induction hM using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨S, hS, rfl⟩ := hx
    rw [exchMatrix_mul]
    refine Submodule.subset_span ⟨_, ?_, rfl⟩
    exact (card_le_card symmDiff_le_sup).trans ((card_union_le _ _).trans (by simp; omega))
  | zero => simp
  | add x y _ _ hx hy => rw [add_mul]; exact add_mem hx hy
  | smul c x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ _ hx

theorem mul_W0_mem_lowSpan {k : ℕ} {M : Matrix (Label α Q) (Label α Q) ℚ}
    (hM : M ∈ lowSpan k) : M * W0 ∈ lowSpan (k + 1) := by
  rw [W0, mul_smul_comm, Finset.mul_sum]
  refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun s _ => ?_)
  rw [mul_sub, mul_one]
  exact sub_mem (lowSpan_mono (Nat.le_succ k) hM) (mul_exchMatrix_mem_lowSpan hM s)

theorem aeval_W0_mem_lowSpan (f : Polynomial ℚ) : Polynomial.aeval W0 f ∈
    (lowSpan f.natDegree : Submodule ℚ (Matrix (Label α Q) (Label α Q) ℚ)) := by
  have hpow : ∀ m : ℕ, (W0 : Matrix (Label α Q) (Label α Q) ℚ) ^ m ∈ lowSpan m := by
    intro m
    induction m with
    | zero => exact Submodule.subset_span ⟨∅, by simp, by rw [pow_zero, exchMatrix_empty]⟩
    | succ m ih => rw [pow_succ]; exact mul_W0_mem_lowSpan ih
  rw [Polynomial.aeval_eq_sum_range]
  refine Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ ?_
  exact lowSpan_mono (Nat.lt_succ_iff.mp (mem_range.mp hi)) (hpow i)

theorem fewMismatches_V0_mul {k : ℕ} {M : Matrix (Label α Q) (Label α Q) ℚ}
    (hM : M ∈ lowSpan k) : FewMismatches k (exchMatrix univ * M) := by
  induction hM using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨S, hS, rfl⟩ := hx
    rw [exchMatrix_mul]
    intro u y h
    simp only [exchMatrix, of_apply, ne_eq, ite_eq_right_iff, one_ne_zero, imp_false,
      not_not] at h
    subst h
    refine (card_le_card fun s hs => ?_).trans hS
    simp only [mem_filter, mem_univ, true_and, exch, Finset.mem_symmDiff, mem_univ] at hs
    by_contra hsS
    simp [hsS] at hs
  | zero => intro u y h; simp at h
  | add x y _ _ hx hy =>
    intro u v h
    rw [mul_add, Matrix.add_apply] at h
    by_cases hxu : (exchMatrix univ * x : Matrix (Label α Q) (Label α Q) ℚ) u v = 0
    · exact hy u v (by rwa [hxu, zero_add] at h)
    · exact hx u v hxu
  | smul c x _ hx =>
    intro u v h
    rw [mul_smul_comm, Matrix.smul_apply, smul_eq_mul] at h
    exact hx u v (right_ne_zero_of_mul h)

/-- **Lemma 4.2.** -/
theorem M0_fewMismatches (f : Polynomial ℚ) : FewMismatches f.natDegree (M0 f : Matrix
    (Label α Q) (Label α Q) ℚ) :=
  fewMismatches_V0_mul (aeval_W0_mem_lowSpan f)

/-! ### The interpolating polynomial (4.7) -/

open Polynomial in
/-- `f_I(z) = (−1)^A₀ Σ_{j<R} (−2)^j (z − A₀ choose j)`. -/
noncomputable def fI (A0 R : ℕ) : ℚ[X] :=
  C ((-1 : ℚ) ^ A0) *
    ∑ j ∈ range R, C ((-2 : ℚ) ^ j / j.factorial) * (descPochhammer ℚ j).comp (X - C (A0 : ℚ))

open Polynomial in
theorem natDegree_fI_le (A0 R : ℕ) : (fI A0 R).natDegree ≤ R - 1 := by
  unfold fI
  refine (natDegree_C_mul_le _ _).trans (natDegree_sum_le_of_forall_le _ _ fun j hj => ?_)
  refine (natDegree_C_mul_le _ _).trans ((natDegree_comp_le).trans ?_)
  rw [descPochhammer_natDegree, natDegree_X_sub_C, mul_one]
  have := mem_range.mp hj; omega

open Polynomial in
theorem fI_eval (A0 R q : ℕ) (hq : q < R) : (fI A0 R).eval ((A0 + q : ℕ) : ℚ) = (-1) ^ (A0 + q) := by
  unfold fI
  simp only [eval_mul, eval_C, eval_finsetSum, eval_comp, eval_sub, eval_X, Nat.cast_add,
    add_sub_cancel_left, descPochhammer_eval_eq_descFactorial, Nat.descFactorial_eq_factorial_mul_choose]
  have h : ∑ j ∈ range R, (-2 : ℚ) ^ j / j.factorial * ((j.factorial * q.choose j : ℕ) : ℚ) =
      ∑ j ∈ range (q + 1), (-2 : ℚ) ^ j * 1 ^ (q - j) * q.choose j := by
    rw [← Finset.sum_subset (range_subset_range.mpr (by omega : q + 1 ≤ R))]
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [one_pow, mul_one]
      push_cast
      field_simp
    · intro j _ hj
      rw [Nat.choose_eq_zero_of_lt (by simpa using hj), mul_zero, Nat.cast_zero, mul_zero]
  rw [h, ← add_pow, pow_add]
  norm_num

/-! ### Entries of the measurement rows -/

omit [Fintype α] in
theorem psi1_mem (k z : α × α) : psi1 k z = 0 ∨ psi1 k z = 1 ∨ psi1 k z = -1 := by
  unfold psi1
  split_ifs <;> first | (left; norm_num; done) | (right; left; norm_num; done) |
    (right; right; norm_num; done) | (exfalso; tauto)

theorem psi_mem (κ u : Label α Q) : psi κ u = 0 ∨ psi κ u = 1 ∨ psi κ u = -1 := by
  unfold psi
  induction (univ : Finset (Fin Q)) using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
    rw [prod_insert ha]
    rcases psi1_mem (κ a) (u a) with h | h | h <;> rcases ih with h' | h' | h' <;>
      simp [h, h']

/-! ### Lemma 4.3: the polynomial rows -/

/-- The evaluation point for position `s`: `s + 1`. -/
def node (s : Fin Q) : ℚ := (s : ℚ) + 1

/-- Positions where `a_y s ≠ d_u s`. -/
def mismatch (u y : Label α Q) : Finset (Fin Q) := {s | (y s).1 ≠ (u s).2}

open Polynomial in
/-- `φ_{u,y}(T) = Π_{s ∈ E_{u,y}} (1 − T / s)`, with nodes `1, …, Q`. -/
noncomputable def phi (u y : Label α Q) : ℚ[X] := ∏ s ∈ mismatch u y, (1 - C (node s)⁻¹ * X)

open Polynomial in
/-- The row (4.10): `P_u(T) = δ_u (I − M₀) + Σ_y M₀[u, y] φ_{u,y}(T) δ_y`. -/
noncomputable def row (f : ℚ[X]) (u y : Label α Q) : ℚ[X] :=
  C ((1 - M0 f) u y) + C (M0 f u y) * phi u y

open Polynomial in
theorem natDegree_row_le (f : ℚ[X]) (u y : Label α Q) : (row f u y).natDegree ≤ f.natDegree := by
  unfold row
  by_cases h : M0 f u y = 0
  · simp [h]
  refine (natDegree_add_le _ _).trans (max_le (by simp) ((natDegree_C_mul_le _ _).trans ?_))
  refine (natDegree_prod_le _ _).trans ((Finset.sum_le_card_nsmul _ _ 1 fun s _ => ?_).trans ?_)
  · exact (natDegree_sub_le _ _).trans (max_le (by simp)
      ((natDegree_C_mul_le _ _).trans natDegree_X_le))
  · rw [smul_eq_mul, mul_one]
    exact M0_fewMismatches f u y h

open Polynomial in
theorem row_eval_zero (f : ℚ[X]) (u y : Label α Q) :
    (row f u y).eval 0 = if y = u then 1 else 0 := by
  have hphi : (phi u y).eval 0 = 1 := by simp [phi, eval_prod]
  rw [row, eval_add, eval_C, eval_mul, eval_C, hphi, mul_one, Matrix.sub_apply, sub_add_cancel,
    Matrix.one_apply]
  simp [eq_comm]

theorem phi_eval_node {u y : Label α Q} {t : Fin Q} (ht : (y t).1 ≠ (u t).2) :
    (phi u y).eval (node t) = 0 := by
  rw [phi, Polynomial.eval_prod]
  refine Finset.prod_eq_zero (i := t) (by simp [mismatch, ht]) ?_
  have : node t ≠ 0 := by unfold node; positivity
  simp [this]

/-- **Lemma 4.3 (separation).** At the node `t`, the row of `u` vanishes on every `ξ` in the
kernel of the measurements that vanishes on the coordinates `y` with `a_y t = d_u t`. -/
theorem sum_row_eval_mul_eq_zero (f : Polynomial ℚ) (I : Finset ℕ)
    (hf : ∀ j ∈ I, f.eval (j : ℚ) = (-1) ^ j) (ξ : Label α Q → ℚ)
    (hξ : ∀ κ, antiCount κ ∉ I → psi κ ⬝ᵥ ξ = 0) (u : Label α Q) (t : Fin Q)
    (hsupp : ∀ y, (y t).1 = (u t).2 → ξ y = 0) :
    ∑ y, (row f u y).eval (node t) * ξ y = 0 := by
  have hfix := M0_mulVec_of_orthogonal f I hf ξ hξ
  have h1 : ∑ y, (1 - M0 f) u y * ξ y = 0 := by
    have : (1 - M0 f) *ᵥ ξ = 0 := by rw [sub_mulVec, one_mulVec, hfix, sub_self]
    simpa [mulVec, dotProduct] using congrFun this u
  have h2 : ∑ y, M0 f u y * (phi u y).eval (node t) * ξ y = 0 :=
    Finset.sum_eq_zero fun y _ => by
      by_cases hy : (y t).1 = (u t).2
      · rw [hsupp y hy, mul_zero]
      · rw [phi_eval_node hy, mul_zero, zero_mul]
  simp only [row, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul, add_mul,
    Finset.sum_add_distrib, h1, h2, zero_add]

/-! ### Counting rows -/

variable (α) in
/-- `m₋`: pairs `(a, b)` with `b < a`. -/
def oddPairs : ℕ := #{k : α × α | k.2 < k.1}

variable (α) in
/-- `m₊`: pairs `(a, b)` with `a ≤ b`. -/
def evenPairs : ℕ := #{k : α × α | k.1 ≤ k.2}

open Polynomial in
theorem sum_X_pow_antiCount :
    ∑ κ : Label α Q, (X : ℕ[X]) ^ antiCount κ = (C (evenPairs α) + C (oddPairs α) * X) ^ Q := by
  have h1 : ∀ κ : Label α Q, (X : ℕ[X]) ^ antiCount κ =
      ∏ s, X ^ (if (κ s).2 < (κ s).1 then 1 else 0) := fun κ => by
    rw [Finset.prod_pow_eq_pow_sum, antiCount, Finset.card_filter]
  simp only [h1]
  set g : α × α → ℕ[X] := fun k => X ^ (if k.2 < k.1 then 1 else 0) with hg
  rw [show (∑ x : Label α Q, ∏ s, g (x s)) = ∏ _s : Fin Q, ∑ k, g k from
    (Fintype.prod_sum fun _ k => g k).symm, prod_const, card_univ, Fintype.card_fin, hg]
  congr 1
  simp only [pow_ite, pow_one, pow_zero]
  rw [Finset.sum_ite, evenPairs, oddPairs, add_comm]
  simp only [sum_const, nsmul_eq_mul, mul_one, not_lt]
  rw [← C_eq_natCast, ← C_eq_natCast, Nat.cast_id, Nat.cast_id]

open Polynomial in
theorem card_antiCount_eq (j : ℕ) :
    #{κ : Label α Q | antiCount κ = j} = Q.choose j * oddPairs α ^ j * evenPairs α ^ (Q - j) := by
  have h := congrArg (coeff · j) (sum_X_pow_antiCount (α := α) (Q := Q))
  simp only [finsetSum_coeff, coeff_X_pow] at h
  rw [Finset.card_filter]
  simp_rw [eq_comm (a := antiCount _)] at h ⊢
  rw [h, add_comm, add_pow, finsetSum_coeff]
  have : ∀ i ∈ range (Q + 1), ((C (oddPairs α) * X) ^ i * C (evenPairs α) ^ (Q - i) *
      (Q.choose i : ℕ[X])).coeff j =
      if j = i then Q.choose i * oddPairs α ^ i * evenPairs α ^ (Q - i) else 0 := fun i _ => by
    rw [mul_pow, ← C_pow, ← C_pow, ← C_eq_natCast, Nat.cast_id,
      show C (oddPairs α ^ i) * X ^ i * C (evenPairs α ^ (Q - i)) * C (Q.choose i) =
        C (Q.choose i * oddPairs α ^ i * evenPairs α ^ (Q - i)) * X ^ i by
          simp only [map_mul]; ring, coeff_C_mul_X_pow]
  rw [Finset.sum_congr rfl this, Finset.sum_ite_eq]
  split_ifs with hj
  · rfl
  · rw [Nat.choose_eq_zero_of_lt (by simpa using hj), zero_mul, zero_mul]

end Scratch1226X
