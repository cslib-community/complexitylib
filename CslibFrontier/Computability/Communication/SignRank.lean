/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Communication.Functions
public import CslibFrontier.Computability.Communication.Rank
import CslibFrontier.Foundations.LinearAlgebra.Matrix.Rank
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Matrix.Mul

/-!
# Sign-rank

A real matrix `A` *sign-represents* a Boolean function `f : X → Y → Bool` when each entry of `A` is
nonzero with the sign of the corresponding entry of the sign matrix `signMatrix ℝ f`: negative
where `f` is true and positive where `f` is false (`SignRepresents`). The *sign-rank* of `f` is
the least rank of such a matrix (`signRank`) [Paturi and Simon][PaturiSimon1986]
[Sherstov and Wu, §2.8][SherstovWu2019]. It is invariant under negating `f` (`signRank_not`) and
exchanging the players (`signRank_swap`), does not increase on submatrices
(`signRank_comap_le`), and is at most the rank of the sign matrix (`signRank_le_rank_signMatrix`).
A sign-representation of least rank factors through `signRank f` dimensions
(`exists_mul_signRepresents`), and by scaling and rounding every factorization can be replaced by
an integer one (`exists_int_mul_signRepresents`).

The sign-rank can be much smaller than the rank. The communication matrix of equality on `n`
inputs is the identity, of rank `n`, but its sign-rank is at most three: for an injective
numbering `e` of the inputs, the matrix `(e x - e y) ^ 2 - 1 / 4` sign-represents equality and
has rank at most three (`signRank_equality_le_three`). With three or more inputs it is at least
two (`two_le_signRank_equality`); for four or more it is exactly three
[Alon, Moran and Yehudayoff, Claim 3][AlonMoranYehudayoff2016], which is not formalized here.

The sign-rank characterizes unbounded-error communication; see
`CslibFrontier.Computability.Communication.PaturiSimon`.

## Main definitions

* `Cslib.Communication.SignRepresents`: a real matrix sign-represents a Boolean function.
* `Cslib.Communication.signRank`: the sign-rank of a Boolean function.

## Main results

* `Cslib.Communication.signRank_le_rank`, `Cslib.Communication.signRank_le_iff`: sign-rank in terms
  of sign-representations.
* `Cslib.Communication.signRank_le_rank_signMatrix`,
  `Cslib.Communication.signRank_le_rank_communicationMatrix_add_one`: sign-rank is at most rank.
* `Cslib.Communication.signRank_comap_le`: monotonicity under submatrices.
* `Cslib.Communication.exists_mul_signRepresents`,
  `Cslib.Communication.exists_int_mul_signRepresents`: real and integer factorizations.
* `Cslib.Communication.signRank_equality_le_three`, `Cslib.Communication.two_le_signRank_equality`:
  bounds for equality.

## References

* [R. Paturi and J. Simon, *Probabilistic communication complexity*][PaturiSimon1986]
* [A. A. Sherstov and P. Wu, *Near-optimal lower bounds on the threshold degree and sign-rank of
  AC⁰*][SherstovWu2019]
* [N. Alon, S. Moran and A. Yehudayoff, *Sign rank versus VC dimension*][AlonMoranYehudayoff2016]
-/

open Finset Matrix Filter Topology

public section

namespace Cslib.Communication

variable {X Y X' Y' : Type*}

/-- A real matrix `A` *sign-represents* a Boolean function `f` when each of its entries has the
sign of the corresponding entry of the sign matrix of `f`: negative where `f` is true and positive
where `f` is false. In particular every entry is nonzero. -/
@[expose] def SignRepresents (A : Matrix X Y ℝ) (f : X → Y → Bool) : Prop :=
  ∀ x y, 0 < signMatrix ℝ f x y * A x y

namespace SignRepresents

variable {A : Matrix X Y ℝ} {f : X → Y → Bool}

/-- Sign-representation entry by entry. -/
theorem iff_lt : SignRepresents A f ↔ ∀ x y, if f x y then A x y < 0 else 0 < A x y := by
  refine forall₂_congr fun x y => ?_
  by_cases h : f x y <;> simp [h]

theorem neg_of_true (hA : SignRepresents A f) {x : X} {y : Y} (h : f x y = true) : A x y < 0 := by
  simpa [h] using iff_lt.mp hA x y

theorem pos_of_false (hA : SignRepresents A f) {x : X} {y : Y} (h : f x y = false) :
    0 < A x y := by
  simpa [h] using iff_lt.mp hA x y

theorem ne_zero (hA : SignRepresents A f) (x : X) (y : Y) : A x y ≠ 0 := by
  cases h : f x y
  · exact (hA.pos_of_false h).ne'
  · exact (hA.neg_of_true h).ne

/-- Scaling by a positive constant preserves sign-representation. -/
theorem smul (hA : SignRepresents A f) {c : ℝ} (hc : 0 < c) : SignRepresents (c • A) f :=
  fun x y => by simpa [mul_left_comm] using mul_pos hc (hA x y)

/-- Negating a matrix sign-represents the negated function. -/
theorem neg (hA : SignRepresents A f) : SignRepresents (-A) fun x y => !f x y := by
  intro x y
  have := hA x y
  cases h : f x y <;> simp_all

/-- Transposing a matrix sign-represents the function with its arguments exchanged. -/
theorem transpose (hA : SignRepresents A f) : SignRepresents Aᵀ fun y x => f x y :=
  fun y x => hA x y

/-- Submatrices sign-represent the restricted function. -/
theorem submatrix (hA : SignRepresents A f) (a : X' → X) (b : Y' → Y) :
    SignRepresents (A.submatrix a b) fun x y => f (a x) (b y) :=
  fun x y => hA (a x) (b y)

end SignRepresents

/-- The sign matrix of `f` sign-represents `f`. -/
theorem signRepresents_signMatrix (f : X → Y → Bool) : SignRepresents (signMatrix ℝ f) f := by
  intro x y
  by_cases h : f x y <;> simp [h]

variable [Fintype Y]

/-- The *sign-rank* of a Boolean function `f`: the least rank of a real matrix that
sign-represents `f` [Sherstov and Wu, §2.8][SherstovWu2019]. The sign matrix itself is such a
matrix, so the infimum is attained (`exists_signRepresents_rank_eq`). -/
noncomputable def signRank (f : X → Y → Bool) : ℕ :=
  sInf {r | ∃ A : Matrix X Y ℝ, SignRepresents A f ∧ A.rank = r}

variable {f : X → Y → Bool}

theorem signRank_le_rank {A : Matrix X Y ℝ} (hA : SignRepresents A f) : signRank f ≤ A.rank :=
  Nat.sInf_le ⟨A, hA, rfl⟩

/-- Some sign-representation has rank exactly the sign-rank. -/
theorem exists_signRepresents_rank_eq (f : X → Y → Bool) :
    ∃ A : Matrix X Y ℝ, SignRepresents A f ∧ A.rank = signRank f :=
  Nat.sInf_mem (s := {r | ∃ A : Matrix X Y ℝ, SignRepresents A f ∧ A.rank = r})
    ⟨_, signMatrix ℝ f, signRepresents_signMatrix f, rfl⟩

theorem signRank_le_iff {r : ℕ} :
    signRank f ≤ r ↔ ∃ A : Matrix X Y ℝ, SignRepresents A f ∧ A.rank ≤ r := by
  refine ⟨fun h => ?_, fun ⟨A, hA, hr⟩ => (signRank_le_rank hA).trans hr⟩
  obtain ⟨A, hA, hr⟩ := exists_signRepresents_rank_eq f
  exact ⟨A, hA, hr ▸ h⟩

theorem le_signRank_iff {r : ℕ} :
    r ≤ signRank f ↔ ∀ A : Matrix X Y ℝ, SignRepresents A f → r ≤ A.rank := by
  refine ⟨fun h A hA => h.trans (signRank_le_rank hA), fun h => ?_⟩
  obtain ⟨A, hA, hr⟩ := exists_signRepresents_rank_eq f
  exact hr ▸ h A hA

/-- A sign-representation by a product through `k` dimensions bounds the sign-rank by `k`. -/
theorem signRank_le_card_of_mul {ι : Type*} [Fintype ι] {U : Matrix X ι ℝ} {V : Matrix ι Y ℝ}
    (h : SignRepresents (U * V) f) : signRank f ≤ Fintype.card ι :=
  (signRank_le_rank h).trans ((Matrix.rank_mul_le_left U V).trans (Matrix.rank_le_card_width U))

/-- **Sign-rank factorization**: `f` is sign-represented by a product through `signRank f`
dimensions. -/
theorem exists_mul_signRepresents (f : X → Y → Bool) :
    ∃ (U : Matrix X (Fin (signRank f)) ℝ) (V : Matrix (Fin (signRank f)) Y ℝ),
      SignRepresents (U * V) f := by
  obtain ⟨A, hA, hr⟩ := exists_signRepresents_rank_eq f
  obtain ⟨C, D, hCD⟩ := Matrix.exists_eq_mul_rank A
  let e : Fin (signRank f) ≃ Fin A.rank := finCongr hr.symm
  refine ⟨C.submatrix id e, D.submatrix e id, ?_⟩
  rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_id_id, ← hCD]
  exact hA

/-- The sign-rank is at most the rank of the sign matrix. -/
theorem signRank_le_rank_signMatrix (f : X → Y → Bool) :
    signRank f ≤ (signMatrix ℝ f).rank :=
  signRank_le_rank (signRepresents_signMatrix f)

/-- The sign-rank is at most the rank of the communication matrix plus one. -/
theorem signRank_le_rank_communicationMatrix_add_one (f : X → Y → Bool) :
    signRank f ≤ (communicationMatrix ℝ f).rank + 1 :=
  (signRank_le_rank_signMatrix f).trans (rank_signMatrix_le f)

/-- The sign-rank is at most the number of columns. -/
theorem signRank_le_card_right (f : X → Y → Bool) : signRank f ≤ Fintype.card Y :=
  (signRank_le_rank_signMatrix f).trans (Matrix.rank_le_card_width _)

/-- The sign-rank is at most the number of rows. -/
theorem signRank_le_card_left [Fintype X] (f : X → Y → Bool) : signRank f ≤ Fintype.card X :=
  (signRank_le_rank_signMatrix f).trans (Matrix.rank_le_card_height _)

/-- **Monotonicity under submatrices**: restricting (or repeating) rows and columns does not
increase the sign-rank. -/
theorem signRank_comap_le [Fintype Y'] (f : X → Y → Bool) (a : X' → X) (b : Y' → Y) :
    signRank (fun x y => f (a x) (b y)) ≤ signRank f := by
  obtain ⟨A, hA, hr⟩ := exists_signRepresents_rank_eq f
  exact (signRank_le_rank (hA.submatrix a b)).trans (hr ▸ Matrix.rank_submatrix_le A a b)

/-- Negating a function does not change its sign-rank. -/
@[simp] theorem signRank_not (f : X → Y → Bool) : signRank (fun x y => !f x y) = signRank f := by
  have key (g : X → Y → Bool) : signRank (fun x y => !g x y) ≤ signRank g := by
    obtain ⟨A, hA, hr⟩ := exists_signRepresents_rank_eq g
    exact (signRank_le_rank hA.neg).trans (by rw [Matrix.rank_neg, hr])
  refine le_antisymm (key f) ?_
  simpa using key fun x y => !f x y

private theorem signRank_swap_le [Fintype X] (f : X → Y → Bool) :
    signRank (fun y x => f x y) ≤ signRank f := by
  obtain ⟨A, hA, hr⟩ := exists_signRepresents_rank_eq f
  exact (signRank_le_rank hA.transpose).trans (by rw [Matrix.rank_transpose, hr])

/-- Exchanging the arguments does not change the sign-rank. -/
theorem signRank_swap [Fintype X] (f : X → Y → Bool) :
    signRank (fun y x => f x y) = signRank f :=
  le_antisymm (signRank_swap_le f) (signRank_swap_le fun y x => f x y)

/-- A matrix of rank zero is zero. -/
private theorem eq_zero_of_rank_eq_zero {A : Matrix X Y ℝ} (h : A.rank = 0) (x : X) (y : Y) :
    A x y = 0 := by
  obtain ⟨C, D, hCD⟩ := Matrix.exists_eq_mul_rank A
  have : IsEmpty (Fin A.rank) := by rw [h]; infer_instance
  rw [hCD, Matrix.mul_apply, Finset.univ_eq_empty, Finset.sum_empty]

/-- When both players have inputs, the sign-rank is positive: the zero matrix sign-represents
nothing. -/
theorem signRank_pos [Nonempty X] [Nonempty Y] (f : X → Y → Bool) : 0 < signRank f := by
  obtain ⟨x⟩ := ‹Nonempty X›
  obtain ⟨y⟩ := ‹Nonempty Y›
  refine le_signRank_iff.mpr fun A hA => Nat.pos_of_ne_zero fun h => ?_
  exact hA.ne_zero x y (eq_zero_of_rank_eq_zero h x y)

/-- If `f` has sign-rank at most one, it is sign-represented by a product `u x * v y`. -/
theorem exists_mul_of_signRank_le_one [Nonempty X] [Nonempty Y] (h : signRank f ≤ 1) :
    ∃ (u : X → ℝ) (v : Y → ℝ), ∀ x y, 0 < signMatrix ℝ f x y * (u x * v y) := by
  have h1 : signRank f = 1 := le_antisymm h (signRank_pos f)
  obtain ⟨U, V, hUV⟩ := exists_mul_signRepresents f
  have : Unique (Fin (signRank f)) := by rw [h1]; infer_instance
  refine ⟨fun x => U x default, fun y => V default y, fun x y => ?_⟩
  simpa [SignRepresents, Matrix.mul_apply] using hUV x y

/-! ### Integer sign-representations -/

/-- `⌊N z⌋ / N → z` as `N → ∞`. -/
private theorem tendsto_floor_mul_div (z : ℝ) :
    Tendsto (fun N : ℕ => (⌊(N : ℝ) * z⌋ : ℝ) / N) atTop (𝓝 z) := by
  have h1 : Tendsto (fun N : ℕ => z - 1 / (N : ℝ)) atTop (𝓝 z) := by
    have := (tendsto_const_nhds (x := z) (f := (atTop : Filter ℕ))).sub
      tendsto_one_div_atTop_nhds_zero_nat
    rwa [sub_zero] at this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' h1 tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with N hN
    have hN' : (0 : ℝ) < N := by exact_mod_cast hN
    rw [le_div_iff₀ hN', sub_mul, one_div, inv_mul_cancel₀ hN'.ne']
    linarith [Int.sub_one_lt_floor ((N : ℝ) * z)]
  · filter_upwards [eventually_gt_atTop 0] with N hN
    have hN' : (0 : ℝ) < N := by exact_mod_cast hN
    rw [div_le_iff₀ hN']
    linarith [Int.floor_le ((N : ℝ) * z)]

omit [Fintype Y] in
/-- **Integer sign-representations.** If a product `U * V` of real matrices through `ι`
sign-represents `f` on finite sets of inputs, so does a product of integer matrices through the
same `ι`: for large `N`, the matrices `⌊N U⌋` and `⌊N V⌋` have a product within `o(N ^ 2)` of
`N ^ 2 (U * V)`, whose entries are bounded away from zero. -/
theorem exists_int_mul_signRepresents [Finite X] [Finite Y] {ι : Type*} [Fintype ι]
    {U : Matrix X ι ℝ} {V : Matrix ι Y ℝ} (h : SignRepresents (U * V) f) :
    ∃ (U' : Matrix X ι ℤ) (V' : Matrix ι Y ℤ), SignRepresents ((U' * V').map (↑)) f := by
  have hlim : ∀ x y, Tendsto (fun N : ℕ => signMatrix ℝ f x y *
      ∑ i, (⌊(N : ℝ) * U x i⌋ : ℝ) / N * ((⌊(N : ℝ) * V i y⌋ : ℝ) / N)) atTop
      (𝓝 (signMatrix ℝ f x y * (U * V) x y)) := fun x y =>
    tendsto_const_nhds.mul (tendsto_finsetSum _ fun i _ =>
      (tendsto_floor_mul_div _).mul (tendsto_floor_mul_div _))
  have hev : ∀ᶠ N : ℕ in atTop, ∀ x y, 0 < signMatrix ℝ f x y *
      ∑ i, (⌊(N : ℝ) * U x i⌋ : ℝ) / N * ((⌊(N : ℝ) * V i y⌋ : ℝ) / N) := by
    simp only [eventually_all]
    exact fun x y => (hlim x y).eventually (lt_mem_nhds (h x y))
  obtain ⟨N, hN⟩ := hev.exists
  refine ⟨Matrix.of fun x i => ⌊(N : ℝ) * U x i⌋, Matrix.of fun i y => ⌊(N : ℝ) * V i y⌋,
    fun x y => ?_⟩
  have hxy := hN x y
  have heq : ∑ i, (⌊(N : ℝ) * U x i⌋ : ℝ) / N * ((⌊(N : ℝ) * V i y⌋ : ℝ) / N) =
      (∑ i, (⌊(N : ℝ) * U x i⌋ : ℝ) * ⌊(N : ℝ) * V i y⌋) / (N : ℝ) ^ 2 := by
    rw [sum_div]
    exact sum_congr rfl fun i _ => by ring
  rw [heq, mul_div_assoc'] at hxy
  rcases div_pos_iff.mp hxy with ⟨h1, _⟩ | ⟨_, h2⟩
  · simpa [Matrix.mul_apply] using h1
  · exact absurd h2 (not_lt.mpr (sq_nonneg _))

/-! ### Equality -/

/-- **Equality has sign-rank at most three**: for an injective numbering `e` of the inputs, the
matrix `(e x - e y) ^ 2 - 1 / 4` sign-represents equality and has rank at most three. -/
theorem signRank_equality_le_three [DecidableEq Y] : signRank (equality (X := Y)) ≤ 3 := by
  classical
  let e : Y → ℝ := fun y => (Fintype.equivFin Y y : ℕ)
  have he : ∀ x y, x ≠ y → 1 ≤ (e x - e y) ^ 2 := by
    intro x y hxy
    have hne : (Fintype.equivFin Y x : ℕ) ≠ Fintype.equivFin Y y := fun h =>
      hxy ((Fintype.equivFin Y).injective (Fin.ext h))
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · have : e x + 1 ≤ e y := by simp only [e]; exact_mod_cast h
      nlinarith
    · have : e y + 1 ≤ e x := by simp only [e]; exact_mod_cast h
      nlinarith
  let U : Matrix Y (Fin 3) ℝ := Matrix.of fun x i => ![e x ^ 2 - 1 / 4, e x, 1] i
  let V : Matrix (Fin 3) Y ℝ := Matrix.of fun i y => ![1, -2 * e y, e y ^ 2] i
  have hUV : ∀ x y, (U * V) x y = (e x - e y) ^ 2 - 1 / 4 := by
    intro x y
    simp only [Matrix.mul_apply, Fin.sum_univ_three, U, V, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons]
    ring
  have h : SignRepresents (U * V) equality := by
    refine SignRepresents.iff_lt.mpr fun x y => ?_
    rw [hUV]
    by_cases hxy : x = y
    · subst hxy; simp [equality]
    · have := he x y hxy
      simp only [equality, hxy, decide_false, Bool.false_eq_true, ite_false]
      linarith
  simpa using signRank_le_card_of_mul h

/-- On three or more inputs, equality has sign-rank at least two: a product `u x * v y` takes the
same sign on two rows `x₁ ≠ x₂` with `u x₁`, `u x₂` of the same sign, but equality separates them
in column `x₁`. -/
theorem two_le_signRank_equality [DecidableEq Y] (hY : 2 < Fintype.card Y) :
    2 ≤ signRank (equality (X := Y)) := by
  by_contra! hlt
  obtain ⟨a, b, c, hab, hac, hbc⟩ := Fintype.two_lt_card_iff.mp hY
  have : Nonempty Y := ⟨a⟩
  obtain ⟨u, v, h⟩ := exists_mul_of_signRank_le_one (f := equality (X := Y)) (by omega)
  have hu : ∀ x, u x ≠ 0 := fun x hx => by simpa [hx] using h x x
  -- Two distinct rows `x₁ ≠ x₂` have `u x₁ * u x₂ < 0`: column `x₁` separates them.
  have key : ∀ x₁ x₂, x₁ ≠ x₂ → u x₁ * u x₂ < 0 := by
    intro x₁ x₂ hne
    have h₁ : u x₁ * v x₁ < 0 := by simpa [equality] using h x₁ x₁
    have h₂ : 0 < u x₂ * v x₁ := by simpa [equality, Ne.symm hne] using h x₂ x₁
    refine lt_of_le_of_ne (not_lt.mp fun hpos => ?_) (mul_ne_zero (hu x₁) (hu x₂))
    have e : (u x₁ * v x₁) * (u x₂ * v x₁) = (u x₁ * u x₂) * v x₁ ^ 2 := by ring
    linarith [mul_neg_of_neg_of_pos h₁ h₂, mul_nonneg hpos.le (sq_nonneg (v x₁))]
  have e : (u a * u b) * (u a * u c) * (u b * u c) = (u a * u b * u c) ^ 2 := by ring
  linarith [mul_neg_of_pos_of_neg (mul_pos_of_neg_of_neg (key a b hab) (key a c hac))
    (key b c hbc), sq_nonneg (u a * u b * u c)]

end Cslib.Communication

end
