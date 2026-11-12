/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.AuxiliaryFormula
public import CslibFrontier.Probability.Product
import CslibFrontier.Probability.Product.Resample
import CslibFrontier.Probability.PMF
import Mathlib.Tactic

/-!
# Predicting `g` from a protocol for a dense restriction

[ChukhinKulikovMihajlinSmal2026], Lemma 6.2 (printed pp. 13–15; PDF pp. 14–16). Let `ν` be a
distribution on `{0, 1}ⁿ`, and let `ρ` be the density of a set `X` of `m`-row matrices under the
product `νᵐ` (`density`). If `R_g(X)` has a protocol of depth `d`, then some formula of
`binaryCost` depth at most `d + 1` predicts `g` under `ν` (`accuracy`) with accuracy at least
`1/2 + (2ᵐ ρ - 1) / (2 (2ᵐ - 1))` (`exists_accuracy_ge`).

The proof follows the source. Take the formula `φ(Z, p)` of Lemma 6.1 (`exists_auxFormula`). For
a set `U` of row-value vectors, given by its indicator, `Φ_U(Z) = φ(Z, 1_U) ∧ ¬φ(Z, 1_{Uᶜ})`
equals `1[gᵐ(Z) ∈ U]` on `X`. Monotonicity in the auxiliary variables gives
`Φ_U + Φ_V ≤ Φ_{U ∪ V}` for disjoint `U`, `V` everywhere. Let `C_r(Z)` be the vectors that agree
with `g` on the first `r` rows of `Z`, and `M_r = E[Φ_{C_r(Z)}(Z)]`. Fixing all rows but row `r`
(`Probability.PMF.sum_pi_mul_update`), the formulas `h_b` that claim the correct first `r` values
and `b` on row `r` mix into a predictor of accuracy `1/2 + E[h_{g(x)}] - E[h₀ + h₁]/2`. So if
every formula of depth `d + 1` has accuracy at most `1/2 + α`, then `M_{r+1} ≤ M_r / 2 + α`.
Iterating from `M₀ ≤ 1` up to `M_m ≥ ρ` gives `ρ ≤ 2⁻ᵐ + 2α(1 - 2⁻ᵐ)`
(`density_le_of_forall_accuracy_le`). The best formula exists, because only finitely many
functions are computed, and taking `α` to be its advantage proves the lemma.

Formulas have `binaryCost` depth, so negations are free, as the source's "negation can be pushed
to the input literals and constants" requires.

## Main definitions

* `Cslib.Circuits.Boolean.accuracy`: `Pr_{x ∼ ν}[h(x) = g(x)]`.
* `Cslib.Circuits.Boolean.density`: `Pr_{Z ∼ νᵐ}[Z ∈ X]`.

## Main results

* `Cslib.Circuits.Boolean.density_le_of_forall_accuracy_le`: the iterated recursion.
* `Cslib.Circuits.Boolean.exists_accuracy_ge`: Lemma 6.2.

## References

* [N. Chukhin, A. S. Kulikov, I. Mihajlin and A. V. Smal, *Solving One of Many Instances is
  Almost as Hard as Solving One*][ChukhinKulikovMihajlinSmal2026]
-/

public section

namespace Cslib.Circuits.Boolean

open Cslib.Communication Cslib.BitString Formula Cslib.Probability.PMF

variable {m n : ℕ}

/-- A Boolean value as a real number. -/
private def ind (b : Bool) : ℝ := if b then 1 else 0

private theorem ind_nonneg (b : Bool) : 0 ≤ ind b := by cases b <;> simp [ind]

private theorem ind_le_one (b : Bool) : ind b ≤ 1 := by cases b <;> simp [ind]

/-- The accuracy `Pr_{x ∼ ν}[h(x) = g(x)]` of a formula `h` predicting `g` under `ν`. -/
@[expose] noncomputable def accuracy (ν : PMF (BitString n)) (g : BitString n → Bool)
    (h : Formula signature n) : ℝ :=
  ∑ x, (ν x).toReal * if h.eval interpretation x = g x then 1 else 0

/-- The density `Pr_{Z ∼ νᵐ}[Z ∈ X]` of a set of matrices under the product of `ν` over rows. -/
@[expose] noncomputable def density (ν : PMF (BitString n)) (X : Set (Fin m → BitString n)) : ℝ :=
  open Classical in ∑ Z, ((pi fun _ : Fin m => ν) Z).toReal * if Z ∈ X then 1 else 0

/-- `φ` with row `i` of the matrix read from the input, the other rows fixed to those of `Z`, and
the auxiliary variables fixed to `q`. -/
private noncomputable def specialize (φ : Formula signature (m * n + 2 ^ m))
    (Z : Fin m → BitString n) (i : Fin m) (q : BitString m → Bool) : Formula signature n :=
  φ.bind fun v => Fin.addCases
    (fun a => if (finProdFinEquiv.symm a).1 = i then .input (finProdFinEquiv.symm a).2
      else .const (Z (finProdFinEquiv.symm a).1 (finProdFinEquiv.symm a).2))
    (fun c => .const (q ((equivFin m).symm c))) v

private theorem eval_specialize (φ : Formula signature (m * n + 2 ^ m))
    (Z : Fin m → BitString n) (i : Fin m) (q : BitString m → Bool) (x : BitString n) :
    (specialize φ Z i q).eval interpretation x =
      φ.eval interpretation (auxInput (Function.update Z i x) q) := by
  rw [specialize, eval_bind]
  congr 1
  funext v
  refine Fin.addCases (fun a => ?_) (fun c => ?_) v
  · obtain ⟨⟨k, j⟩, rfl⟩ := finProdFinEquiv.surjective a
    simp only [Fin.addCases_left, Equiv.symm_apply_apply]
    change _ = auxInput _ q (matrixVar k j)
    rw [auxInput_matrixVar]
    by_cases hk : k = i
    · subst hk
      simp
    · simp [hk]
  · simp [auxInput]

private theorem depthWith_specialize_le (φ : Formula signature (m * n + 2 ^ m))
    (Z : Fin m → BitString n) (i : Fin m) (q : BitString m → Bool) :
    (specialize φ Z i q).depthWith binaryCost ≤ φ.depthWith binaryCost := by
  rw [specialize]
  simpa using depthWith_bind_le (c := 0) (fun v => by
    refine Fin.addCases (fun a => ?_) (fun c => ?_) v
    · simp only [Fin.addCases_left]
      split_ifs <;> simp
    · simp) φ

/-- The source's `Φ_U(Z) = φ(Z, 1_U) ∧ ¬φ(Z, 1_{Uᶜ})`, for `U` given by its indicator `q`. -/
private def Phi (φ : Formula signature (m * n + 2 ^ m)) (q : BitString m → Bool)
    (Z : Fin m → BitString n) : Bool :=
  φ.eval interpretation (auxInput Z q) && !φ.eval interpretation (auxInput Z fun c => !q c)

variable {g : BitString n → Bool} {φ : Formula signature (m * n + 2 ^ m)}

/-- On `X`, `Φ_U(Z) = 1[gᵐ(Z) ∈ U]`. -/
private theorem Phi_of_mem {X : Set (Fin m → BitString n)}
    (hφ : ∀ Z ∈ X, ∀ q : BitString m → Bool,
      φ.eval interpretation (auxInput Z q) = q (rowValues g Z))
    {Z : Fin m → BitString n} (hZ : Z ∈ X) (q : BitString m → Bool) :
    Phi φ q Z = q (rowValues g Z) := by
  simp [Phi, hφ Z hZ]

/-- For disjoint `U` and `V`, `Φ_U + Φ_V ≤ Φ_{U ∪ V}`, by monotonicity in the auxiliary
variables. -/
private theorem ind_Phi_add_le
    (hmono : ∀ Z, Monotone fun q : BitString m → Bool => φ.eval interpretation (auxInput Z q))
    (Z : Fin m → BitString n) {q₀ q₁ : BitString m → Bool}
    (hdisj : ∀ c, q₀ c = true → q₁ c = false) :
    ind (Phi φ q₀ Z) + ind (Phi φ q₁ Z) ≤ ind (Phi φ (fun c => q₀ c || q₁ c) Z) := by
  have hle {q q' : BitString m → Bool} (h : ∀ c, q c = true → q' c = true) :
      φ.eval interpretation (auxInput Z q) ≤ φ.eval interpretation (auxInput Z q') :=
    hmono Z fun c => by
      have := h c
      revert this
      cases q c <;> cases q' c <;> simp
  have h₁ := hle (q := q₀) (q' := fun c => q₀ c || q₁ c) fun c h => by simp [h]
  have h₂ := hle (q := q₁) (q' := fun c => q₀ c || q₁ c) fun c h => by simp [h]
  have h₃ := hle (q := fun c => !(q₀ c || q₁ c)) (q' := fun c => !q₀ c) fun c h => by
    simpa using (Bool.or_eq_false_iff.1 (by simpa using h)).1
  have h₄ := hle (q := fun c => !(q₀ c || q₁ c)) (q' := fun c => !q₁ c) fun c h => by
    simpa using (Bool.or_eq_false_iff.1 (by simpa using h)).2
  have h₅ := hle (q := q₀) (q' := fun c => !q₁ c) fun c h => by simp [hdisj c h]
  simp only [Phi]
  revert h₁ h₂ h₃ h₄ h₅
  generalize φ.eval interpretation (auxInput Z q₀) = a₀
  generalize φ.eval interpretation (auxInput Z q₁) = a₁
  generalize φ.eval interpretation (auxInput Z fun c => !q₀ c) = b₀
  generalize φ.eval interpretation (auxInput Z fun c => !q₁ c) = b₁
  generalize φ.eval interpretation (auxInput Z fun c => q₀ c || q₁ c) = a
  generalize φ.eval interpretation (auxInput Z fun c => !(q₀ c || q₁ c)) = b
  cases a₀ <;> cases a₁ <;> cases b₀ <;> cases b₁ <;> cases a <;> cases b <;> simp [ind]

/-- The vectors `c` agreeing with `g` on the first `r` rows of `Z`: the source's `C_r(Z)`. -/
private def agreeRows (g : BitString n → Bool) (r : ℕ) (Z : Fin m → BitString n) :
    BitString m → Bool :=
  fun c => decide (∀ j : Fin m, j.val < r → c j = g (Z j))

/-- The real expectation of `F` over `Z ∼ νᵐ`. -/
private noncomputable def expect (ν : PMF (BitString n)) (F : (Fin m → BitString n) → ℝ) : ℝ :=
  ∑ Z, ((pi fun _ : Fin m => ν) Z).toReal * F Z

/-- The source's `M_r = E_Z[Φ_{C_r(Z)}(Z)]`. -/
private noncomputable def Mr (ν : PMF (BitString n)) (g : BitString n → Bool)
    (φ : Formula signature (m * n + 2 ^ m)) (r : ℕ) : ℝ :=
  expect ν fun Z => ind (Phi φ (agreeRows g r Z) Z)

/-- The pointwise identity behind the mixed predictor: if `h₀` and `h₁` are not both true, then
`1[h₁ = b] + 1[¬h₀ = b] = 1 + 2 · h_b - h₀ - h₁`. -/
private theorem ind_eq_add_ind_not_eq (a₀ a₁ b : Bool) (h : ¬ (a₀ = true ∧ a₁ = true)) :
    ((if a₁ = b then 1 else 0) + if (!a₀) = b then 1 else 0 : ℝ) =
      1 + 2 * ind (if b then a₁ else a₀) - ind a₀ - ind a₁ := by
  cases a₀ <;> cases a₁ <;> cases b <;> simp_all [ind] <;> norm_num

/-- **One step of the recursion** (proof of [ChukhinKulikovMihajlinSmal2026], Lemma 6.2):
if every formula of depth at most `D + 1` predicts `g` under `ν` with accuracy at most
`1/2 + α`, then `M_{r+1} ≤ M_r / 2 + α`. Fix all rows but row `r`. The formulas `h_b`, which say
that `φ` claims the correct values on the first `r` rows and `b` on row `r`, mix into a predictor
of accuracy `1/2 + E[h_{g(x)}] - E[h₀ + h₁]/2`. -/
private theorem Mr_succ_le (ν : PMF (BitString n)) {D : ℕ} (hD : φ.depthWith binaryCost ≤ D)
    (hmono : ∀ Z, Monotone fun q : BitString m → Bool => φ.eval interpretation (auxInput Z q))
    {α : ℝ} (hα : ∀ h : Formula signature n, h.depthWith binaryCost ≤ D + 1 →
      accuracy ν g h ≤ 1 / 2 + α) {r : ℕ} (hr : r < m) :
    Mr ν g φ (r + 1) ≤ Mr ν g φ r / 2 + α := by
  set i : Fin m := ⟨r, hr⟩
  unfold Mr expect
  rw [sum_pi_mul_update (fun _ => ν) i (F := fun Z => ind (Phi φ (agreeRows g (r + 1) Z) Z)),
    sum_pi_mul_update (fun _ => ν) i (F := fun Z => ind (Phi φ (agreeRows g r Z) Z))]
  have hw0 (Z : Fin m → BitString n) : 0 ≤ ((pi fun _ : Fin m => ν) Z).toReal :=
    ENNReal.toReal_nonneg
  have hw1 : ∑ Z, ((pi fun _ : Fin m => ν) Z).toReal = 1 := sum_toReal _
  -- The bound for each fixing of the other rows.
  have hpt (Z : Fin m → BitString n) :
      ∑ x, (ν x).toReal * ind (Phi φ (agreeRows g (r + 1) (Function.update Z i x))
          (Function.update Z i x)) ≤
        (∑ x, (ν x).toReal * ind (Phi φ (agreeRows g r (Function.update Z i x))
          (Function.update Z i x))) / 2 + α := by
    set C := agreeRows g r Z
    have hC (x : BitString n) : agreeRows g r (Function.update Z i x) = C := by
      funext c
      change decide (∀ j : Fin m, j.val < r → c j = g (Function.update Z i x j)) =
        decide (∀ j : Fin m, j.val < r → c j = g (Z j))
      refine decide_eq_decide.2 (forall_congr' fun j => imp_congr_right fun hj => ?_)
      rw [Function.update_of_ne (Fin.ne_of_val_ne (by change j.val ≠ r; omega))]
    let q (b : Bool) : BitString m → Bool := fun c => C c && (c i == b)
    have hC' (x : BitString n) :
        agreeRows g (r + 1) (Function.update Z i x) = q (g x) := by
      funext c
      change decide (∀ j : Fin m, j.val < r + 1 → c j = g (Function.update Z i x j)) =
        (decide (∀ j : Fin m, j.val < r → c j = g (Z j)) && (c i == g x))
      rw [Bool.eq_iff_iff]
      simp only [decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq]
      constructor
      · intro h
        refine ⟨fun j hj => ?_, by simpa using h i (by simp [i])⟩
        have hne : j ≠ i := Fin.ne_of_val_ne (by change j.val ≠ r; omega)
        have := h j (by omega)
        rwa [Function.update_of_ne hne] at this
      · rintro ⟨h, hi⟩ j hj
        by_cases hji : j = i
        · subst hji
          simpa using hi
        · rw [Function.update_of_ne hji]
          refine h j ?_
          have : j.val ≠ r := fun h' => hji (Fin.ext h')
          omega
    have hq : (fun c => q false c || q true c) = C := by
      funext c
      simp only [q]
      cases C c <;> cases c i <;> rfl
    have hdisj (c : BitString m) : q false c = true → q true c = false := by
      simp only [q]
      cases C c <;> cases c i <;> simp
    -- The formulas `h_b` and their accuracies.
    let hb (b : Bool) : Formula signature n :=
      (specialize φ Z i (q b)).and (specialize φ Z i fun c => !q b c).not
    have heval (b : Bool) (x : BitString n) :
        (hb b).eval interpretation x = Phi φ (q b) (Function.update Z i x) := by
      simp [hb, eval_specialize, Phi]
    have hdepth (b : Bool) : (hb b).depthWith binaryCost ≤ D + 1 := by
      simp only [hb, depthWith_and, depthWith_not, binaryCost_and, binaryCost_not, add_zero]
      have := depthWith_specialize_le φ Z i (q b)
      have := depthWith_specialize_le φ Z i fun c => !q b c
      omega
    have hacc := add_le_add (hα _ (hdepth true))
      (hα (hb false).not (by simpa using hdepth false))
    simp only [accuracy, eval_not, heval, ← Finset.sum_add_distrib, ← mul_add] at hacc
    have hsplit (x : BitString n) := ind_Phi_add_le hmono (Function.update Z i x) hdisj
    rw [hq] at hsplit
    have hnot (x : BitString n) : ¬ (Phi φ (q false) (Function.update Z i x) = true ∧
        Phi φ (q true) (Function.update Z i x) = true) := fun ⟨h₀, h₁⟩ => by
      have := hsplit x
      rw [h₀, h₁] at this
      have := ind_le_one (Phi φ C (Function.update Z i x))
      simp [ind] at *
      linarith
    simp only [fun x => ind_eq_add_ind_not_eq _ _ (g x) (hnot x)] at hacc
    simp only [hC, hC']
    have hgq (x : BitString n) : Phi φ (q (g x)) (Function.update Z i x) =
        if g x then Phi φ (q true) (Function.update Z i x)
        else Phi φ (q false) (Function.update Z i x) := by
      cases g x <;> rfl
    simp only [hgq]
    have hsum : ∑ x, (ν x).toReal = 1 := sum_toReal ν
    set w : BitString n → ℝ := fun x => (ν x).toReal
    set A : BitString n → ℝ := fun x => ind (Phi φ (q true) (Function.update Z i x))
    set B : BitString n → ℝ := fun x => ind (Phi φ (q false) (Function.update Z i x))
    set P : BitString n → ℝ := fun x => ind (Phi φ C (Function.update Z i x))
    set G : BitString n → ℝ := fun x => ind (if g x then Phi φ (q true) (Function.update Z i x)
      else Phi φ (q false) (Function.update Z i x))
    have h1 : ∑ x, w x * (1 + 2 * G x - B x - A x) =
        ∑ x, w x + 2 * ∑ x, w x * G x - ∑ x, w x * (B x + A x) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun x _ => by ring
    have h2 : ∑ x, w x * (B x + A x) ≤ ∑ x, w x * P x :=
      Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (by linarith [hsplit x])
        ENNReal.toReal_nonneg
    change ∑ x, w x * G x ≤ (∑ x, w x * P x) / 2 + α
    change ∑ x, w x * (1 + 2 * G x - B x - A x) ≤ 1 / 2 + α + (1 / 2 + α) at hacc
    linarith
  calc ∑ Z, ((pi fun _ : Fin m => ν) Z).toReal * ∑ x, (ν x).toReal *
        ind (Phi φ (agreeRows g (r + 1) (Function.update Z i x)) (Function.update Z i x))
      ≤ ∑ Z, ((pi fun _ : Fin m => ν) Z).toReal * ((∑ x, (ν x).toReal *
        ind (Phi φ (agreeRows g r (Function.update Z i x)) (Function.update Z i x))) / 2 + α) :=
        Finset.sum_le_sum fun Z _ => mul_le_mul_of_nonneg_left (hpt Z) (hw0 Z)
    _ = (∑ Z, ((pi fun _ : Fin m => ν) Z).toReal * ∑ x, (ν x).toReal *
        ind (Phi φ (agreeRows g r (Function.update Z i x)) (Function.update Z i x))) / 2 + α := by
        simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hw1, one_mul,
          Finset.sum_div, mul_div_assoc]

/-- **The density bound behind Lemma 6.2.** If `R_g(X)` has a protocol of depth `d` and every
formula of depth at most `d + 1` predicts `g` under `ν` with accuracy at most `1/2 + α`, then
`Pr_{νᵐ}[X] ≤ 2⁻ᵐ + 2α(1 - 2⁻ᵐ)`. -/
theorem density_le_of_forall_accuracy_le (ν : PMF (BitString n)) {X : Set (Fin m → BitString n)}
    {p : Protocol (Fin m → BitString n) (Fin m → BitString n) (Option (Fin m × Fin n))}
    (hp : p.Solves (composeKW g) X X) {α : ℝ}
    (hα : ∀ h : Formula signature n, h.depthWith binaryCost ≤ p.depth + 1 →
      accuracy ν g h ≤ 1 / 2 + α) :
    density ν X ≤ (1 / 2) ^ m + 2 * α * (1 - (1 / 2) ^ m) := by
  classical
  obtain ⟨φ, hD, hmono, hφ⟩ := exists_auxFormula hp
  have hw0 (Z : Fin m → BitString n) : 0 ≤ ((pi fun _ : Fin m => ν) Z).toReal :=
    ENNReal.toReal_nonneg
  have hw1 : ∑ Z, ((pi fun _ : Fin m => ν) Z).toReal = 1 := sum_toReal _
  -- `M_r ≤ 2⁻ʳ + 2α(1 - 2⁻ʳ)` for `r ≤ m`.
  have hiter : ∀ r ≤ m, Mr ν g φ r ≤ (1 / 2) ^ r + 2 * α * (1 - (1 / 2) ^ r) := by
    intro r
    induction r with
    | zero =>
      intro _
      have : Mr ν g φ 0 ≤ ∑ Z, ((pi fun _ : Fin m => ν) Z).toReal := by
        unfold Mr expect
        exact Finset.sum_le_sum fun Z _ => mul_le_of_le_one_right (hw0 Z) (ind_le_one _)
      rw [hw1] at this
      simpa using this
    | succ r ih =>
      intro hr
      have h := Mr_succ_le ν hD hmono hα (r := r) (by omega)
      have := ih (by omega)
      rw [pow_succ]
      linarith
  refine le_trans ?_ (hiter m le_rfl)
  refine Finset.sum_le_sum fun Z _ => mul_le_mul_of_nonneg_left ?_ (hw0 Z)
  split_ifs with hZ
  · change 1 ≤ ind (Phi φ (agreeRows g m Z) Z)
    rw [Phi_of_mem hφ hZ]
    simp [agreeRows, rowValues, ind]
  · exact ind_nonneg _

/-- **[ChukhinKulikovMihajlinSmal2026], Lemma 6.2.** Let `m ≥ 1`, let `ν` be a distribution on
`{0, 1}ⁿ`, and let `ρ` be the density of `X` under `νᵐ`. If `R_g(X)` has a protocol of depth `d`,
then some formula `h` of `binaryCost` depth at most `d + 1` predicts `g` under `ν` with accuracy
at least `1/2 + (2ᵐ ρ - 1) / (2 (2ᵐ - 1))`. The source also assumes `ρ ≥ 2⁻ᵐ`, which only makes
the bound at least `1/2`; it is not needed here. -/
theorem exists_accuracy_ge (ν : PMF (BitString n)) {X : Set (Fin m → BitString n)}
    {p : Protocol (Fin m → BitString n) (Fin m → BitString n) (Option (Fin m × Fin n))}
    (hp : p.Solves (composeKW g) X X) (hm : 1 ≤ m) :
    ∃ h : Formula signature n, h.depthWith binaryCost ≤ p.depth + 1 ∧
      1 / 2 + (2 ^ m * density ν X - 1) / (2 * (2 ^ m - 1)) ≤ accuracy ν g h := by
  classical
  -- The best accuracy is attained: only finitely many functions are computed.
  set S : Finset (BitString n → Bool) := Finset.univ.filter fun f =>
    ∃ h : Formula signature n, h.depthWith binaryCost ≤ p.depth + 1 ∧
      h.eval interpretation = f
  set acc : (BitString n → Bool) → ℝ := fun f =>
    ∑ x, (ν x).toReal * if f x = g x then 1 else 0
  have hS : S.Nonempty := ⟨_, Finset.mem_filter.2 ⟨Finset.mem_univ _,
    Formula.const false, by simp, rfl⟩⟩
  obtain ⟨f, hfS, hmax⟩ := S.exists_max_image acc hS
  obtain ⟨h, hd, rfl⟩ := (Finset.mem_filter.1 hfS).2
  refine ⟨h, hd, ?_⟩
  have hle := density_le_of_forall_accuracy_le ν hp (α := accuracy ν g h - 1 / 2)
    fun h' hd' => by
      have := hmax _ (Finset.mem_filter.2 ⟨Finset.mem_univ _, h', hd', rfl⟩)
      simp only [accuracy, acc] at this ⊢
      linarith
  have hP : (2 : ℝ) ≤ 2 ^ m := by
    calc (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ m := pow_le_pow_right₀ (by norm_num) hm
  have hhalf : ((1 : ℝ) / 2) ^ m = 1 / 2 ^ m := by rw [div_pow, one_pow]
  rw [hhalf] at hle
  have hpos : (0 : ℝ) < 2 * (2 ^ m - 1) := by linarith
  have hP0 : (0 : ℝ) < 2 ^ m := by linarith
  have := mul_le_mul_of_nonneg_left hle hP0.le
  have e : (2 : ℝ) ^ m * (1 / 2 ^ m + 2 * (accuracy ν g h - 1 / 2) * (1 - 1 / 2 ^ m)) =
      1 + 2 * (accuracy ν g h - 1 / 2) * (2 ^ m - 1) := by
    field_simp
  rw [e] at this
  have key : (2 ^ m * density ν X - 1) / (2 * (2 ^ m - 1)) ≤ accuracy ν g h - 1 / 2 := by
    rw [div_le_iff₀ hpos]
    nlinarith
  linarith

end Cslib.Circuits.Boolean
