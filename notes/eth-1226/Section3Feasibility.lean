import Mathlib

/-! Scratch feasibility prototype for #1226, manuscript §3 (not for the library). -/

open Polynomial Finset Function

namespace Scratch1226

/-! ### Hermite uniqueness (§3.4, p. 24; Appendix B.3) -/

/-- If the first `J` Taylor coefficients of `p` vanish at `Q` points whose pairwise differences are
units, and `natDegree p < Q * J`, then `p = 0`. Works over any commutative ring, in particular a
`ℚ`-algebra with integer points. -/
theorem eq_zero_of_taylor_coeff_eq_zero {A : Type*} [CommRing A] {Q J : ℕ} (t : Fin Q → A)
    (ht : ∀ i j, i ≠ j → IsUnit (t i - t j)) (p : A[X]) (hp : p.natDegree < Q * J)
    (hT : ∀ i, ∀ d < J, (taylor (t i) p).coeff d = 0) : p = 0 := by
  nontriviality A
  by_contra h0
  have hdvd : ∀ i ∈ (univ : Finset (Fin Q)), (X - C (t i)) ^ J ∣ p := fun i _ => by
    rw [X_sub_C_pow_dvd_iff, ← taylor_apply, X_pow_dvd_iff]
    exact hT i
  have hcop : ((univ : Finset (Fin Q)) : Set (Fin Q)).Pairwise
      (IsCoprime on fun i => (X - C (t i)) ^ J) := fun i _ j _ hij =>
    (isCoprime_X_sub_C_of_isUnit_sub (ht i j hij)).pow
  have hprod := Finset.prod_dvd_of_coprime hcop hdvd
  have hmon : (∏ i : Fin Q, (X - C (t i)) ^ J).Monic :=
    monic_prod_of_monic _ _ fun i _ => (monic_X_sub_C _).pow J
  refine hmon.not_dvd_of_natDegree_lt h0 ?_ hprod
  rw [natDegree_prod_of_monic _ _ fun i _ => (monic_X_sub_C _).pow J]
  simpa only [(monic_X_sub_C _).natDegree_pow, natDegree_X_sub_C, mul_one, one_mul, sum_const, card_univ,
    Fintype.card_fin, smul_eq_mul, mul_comm J] using hp

/-! ### Lemma 3.3 (p. 24): Taylor data from fixed Boolean substitutions -/

variable {σ A : Type*} [CommRing A] [DecidableEq σ]

/-- The alternating sum over an interval `[a, b]` of the Boolean lattice. -/
theorem sum_interval_neg_one_pow {a b : Finset σ} (hab : a ⊆ b) :
    ∑ x ∈ b.powerset with a ⊆ x, (-1 : A) ^ (#x - #a) = if a = b then 1 else 0 := by
  have h : ∑ x ∈ b.powerset with a ⊆ x, (-1 : A) ^ (#x - #a) =
      ∑ w ∈ (b \ a).powerset, (-1 : A) ^ #w := by
    refine Finset.sum_nbij' (fun x => x \ a) (fun w => w ∪ a) ?_ ?_ ?_ ?_ ?_
    · intro x hx
      simp only [mem_filter, mem_powerset] at hx ⊢
      exact sdiff_subset_sdiff hx.1 le_rfl
    · intro w hw
      simp only [mem_filter, mem_powerset] at hw ⊢
      exact ⟨union_subset (hw.trans sdiff_subset) hab, subset_union_right⟩
    · intro x hx
      simp only [mem_filter, mem_powerset] at hx
      exact sdiff_union_of_subset hx.2
    · intro w hw
      simp only [mem_powerset] at hw
      exact union_sdiff_cancel_right (disjoint_of_subset_left hw disjoint_sdiff_self_left)
    · intro x hx
      simp only [mem_filter, mem_powerset] at hx
      rw [card_sdiff_of_subset hx.2]
  rw [h]
  have hz := congrArg (Int.cast : ℤ → A) (Finset.sum_powerset_neg_one_pow_card (x := b \ a))
  push_cast at hz
  rw [hz]
  simp only [sdiff_eq_empty_iff_subset]
  exact if_congr ⟨fun h => h.antisymm' hab, fun h => h ▸ le_rfl⟩ rfl rfl

/-- Möbius coefficient of a set function. -/
def mobius (f : Finset σ → A) (E : Finset σ) : A :=
  ∑ U ∈ E.powerset, (-1) ^ (#E - #U) * f U

/-- The Möbius coefficients of the indicator of the up-set of `S`. -/
theorem mobius_ite_subset (S E : Finset σ) :
    mobius (A := A) (fun U => if S ⊆ U then 1 else 0) E = if S = E then 1 else 0 := by
  unfold mobius
  simp only [mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  by_cases hSE : S ⊆ E
  · have h : ∀ U ∈ E.powerset.filter (fun U => S ⊆ U),
        (-1 : A) ^ (#E - #U) = (-1) ^ (#E - #S) * (-1) ^ (#U - #S) := by
      intro U hU
      simp only [mem_filter, mem_powerset] at hU
      have h₁ := card_le_card hU.1
      have h₂ := card_le_card hU.2
      rw [← pow_add, show #E - #S + (#U - #S) = (#E - #U) + 2 * (#U - #S) by omega, pow_add,
        pow_mul, neg_one_sq, one_pow, mul_one]
    rw [Finset.sum_congr rfl h, ← Finset.mul_sum, sum_interval_neg_one_pow hSE]
    split_ifs with hS
    · subst hS; simp
    · simp
  · have hne : S ≠ E := fun h => hSE (h ▸ subset_refl S)
    simp only [hne, ↓reduceIte]
    refine Finset.sum_eq_zero ?_
    intro U hU
    simp only [mem_filter, mem_powerset] at hU
    exact absurd (hU.2.trans hU.1) hSE

/-- **Möbius inversion on subsets.** -/
theorem sum_mobius (f : Finset σ → A) (S : Finset σ) :
    ∑ E ∈ S.powerset, mobius f E = f S := by
  unfold mobius
  rw [Finset.sum_comm' (t' := S.powerset) (s' := fun U => S.powerset.filter (U ⊆ ·))]
  · rw [Finset.sum_eq_single S]
    · rw [← Finset.sum_mul, sum_interval_neg_one_pow (subset_refl S)]
      simp
    · intro U hU hUS
      rw [← Finset.sum_mul]
      have hU' := mem_powerset.mp hU
      rw [show (∑ E ∈ S.powerset with U ⊆ E, (-1 : A) ^ (#E - #U)) = 0 by
        rw [sum_interval_neg_one_pow hU']; simp [hUS], zero_mul]
    · intro h; exact absurd (mem_powerset.mpr le_rfl) h
  · intro E U
    simp only [mem_powerset, mem_filter]
    constructor
    · rintro ⟨h₁, h₂⟩; exact ⟨⟨h₁, h₂⟩, h₂.trans h₁⟩
    · rintro ⟨⟨h₁, h₂⟩, -⟩; exact ⟨h₁, h₂⟩

/-- Indicator vector of a finite set, as a point of `σ → A`. -/
def ind (U : Finset σ) : σ → A := fun i => if i ∈ U then 1 else 0

theorem prod_pow_ind (d : σ →₀ ℕ) (U : Finset σ) :
    ∏ i ∈ d.support, (ind (A := A) U i) ^ d i = if d.support ⊆ U then 1 else 0 := by
  split_ifs with h
  · refine Finset.prod_eq_one fun i hi => ?_
    simp [ind, h hi]
  · obtain ⟨i, hi, hiU⟩ := Finset.not_subset.mp h
    refine Finset.prod_eq_zero hi ?_
    simp [ind, hiU, zero_pow (Finsupp.mem_support_iff.mp hi)]

omit [DecidableEq σ] in
theorem card_support_le_sum (d : σ →₀ ℕ) : #d.support ≤ d.sum fun _ e => e := by
  rw [Finsupp.sum, card_eq_sum_ones]
  exact Finset.sum_le_sum fun i hi => Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi)

/-- The degree bound kills Möbius coefficients of a polynomial on the cube above its degree. -/
theorem mobius_eval_ind_eq_zero (p : MvPolynomial σ A) {E : Finset σ}
    (hE : p.totalDegree < #E) : mobius (fun U => MvPolynomial.eval (ind U) p) E = 0 := by
  unfold mobius
  simp only [MvPolynomial.eval_eq, prod_pow_ind, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun d hd => ?_
  have := mobius_ite_subset (A := A) d.support E
  unfold mobius at this
  have hne : d.support ≠ E := fun h => by
    have := (card_support_le_sum d).trans (MvPolynomial.le_totalDegree hd)
    rw [h] at this; omega
  simp only [hne, ↓reduceIte] at this
  calc ∑ U ∈ E.powerset, (-1 : A) ^ (#E - #U) * (p.coeff d * if d.support ⊆ U then 1 else 0)
      = p.coeff d * ∑ U ∈ E.powerset, (-1) ^ (#E - #U) * (if d.support ⊆ U then 1 else 0) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => mul_left_comm _ _ _
    _ = 0 := by rw [this, mul_zero]

/-- **Lemma 3.3**, pointwise form: on a Boolean point (the indicator of `S`), a polynomial of
degree at most `q` is recovered from substitutions `1_U` with `U ⊆ E ⊆ S`, `|E| ≤ q`. -/
theorem eval_ind_eq_sum (p : MvPolynomial σ A) {q : ℕ} (hp : p.totalDegree ≤ q)
    (S : Finset σ) :
    MvPolynomial.eval (ind S) p =
      ∑ E ∈ S.powerset with #E ≤ q, mobius (fun U => MvPolynomial.eval (ind U) p) E := by
  rw [← sum_mobius (fun U => MvPolynomial.eval (ind U) p) S, Finset.sum_filter]
  refine Finset.sum_congr rfl fun E _ => ?_
  split_ifs with h
  · rfl
  · exact mobius_eval_ind_eq_zero p (by omega)

/-- **Lemma 3.3** (summed form, (3.10)). Points of the cube are finite sets `S ⊆ univ`. -/
theorem sum_eval_ind_eq [Fintype σ] (p : Finset σ → MvPolynomial σ A) {q : ℕ}
    (hp : ∀ S, (p S).totalDegree ≤ q) :
    ∑ S : Finset σ, MvPolynomial.eval (ind S) (p S) =
      ∑ E : Finset σ with #E ≤ q, ∑ U ∈ E.powerset, (-1) ^ (#E - #U) *
        ∑ S : Finset σ with E ⊆ S, MvPolynomial.eval (ind U) (p S) := by
  simp only [fun S => eval_ind_eq_sum (p S) (hp S) S, mobius]
  rw [Finset.sum_comm' (t' := univ.filter (#· ≤ q)) (s' := fun E => univ.filter (E ⊆ ·))]
  · refine Finset.sum_congr rfl fun E _ => ?_
    simp only [Finset.mul_sum]
    exact Finset.sum_comm
  · intro S E
    simp only [mem_univ, mem_filter, mem_powerset, true_and]

/-! ### Separation identity (proof of Lemma 3.2, pp. 22–23), abstract form -/

/-- Fixing the measurements separates the sum: if each factor `B g` reads only its own group's
assignment `x g` and the measurement tuple, then the sum over all assignments of the product is the
sum over measurement tuples of the product of per-group sums. -/
theorem sum_prod_eq_sum_prod_sum {ι : Type*} [Fintype ι] [DecidableEq ι] {X Y : ι → Type*}
    [∀ g, Fintype (X g)] [∀ g, Fintype (Y g)] [∀ g, DecidableEq (Y g)]
    (M : ∀ g, X g → Y g) (B : ∀ g, X g → (∀ h, Y h) → A) :
    ∑ x : ∀ g, X g, ∏ g, B g (x g) (fun h => M h (x h)) =
      ∑ y : ∀ h, Y h, ∏ g, ∑ u : X g with M g u = y g, B g u y := by
  rw [← Finset.sum_fiberwise univ (fun x : ∀ g, X g => fun h => M h (x h))]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.prod_univ_sum]
  have hfib : (univ.filter fun x : ∀ g, X g => (fun h => M h (x h)) = y) =
      Fintype.piFinset fun g => univ.filter fun u => M g u = y g := by
    ext x; simp [funext_iff]
  rw [hfib]
  refine Finset.sum_congr rfl fun x hx => Finset.prod_congr rfl fun g _ => ?_
  have hx' : (fun h => M h (x h)) = y := funext fun h => by
    simpa using Fintype.mem_piFinset.mp hx h
  rw [hx']

end Scratch1226
