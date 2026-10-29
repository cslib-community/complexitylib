/-
Copyright (c) 2026 Anton Kovsharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anton Kovsharov
-/

import Complexity.Foundations.Data.MvPolynomial.AffineTaylor
import Mathlib.Algebra.Field.ZMod
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Concrete tests for affine Taylor substitutions and restricted-subset jets

Nonvacuous checks exercising `Cslib.AffineTaylor` across:
- nonzero nodes (`t ≠ 0`) and nonconstant quadratic replacement rows;
- multiple factors with dependent variable types `κ : Bool → Type` and mixed signs;
- genuine baseline dependence on `x` (and a negative control showing `G_{1_U}` fails);
- common-`q` jet bounds (`j < q`, `j = q`, `q = 0`) and failure when `j > q`;
- empty factor sets (`s = ∅`) and empty coordinate types (`Fin 0`);
- characteristic-2 (`ZMod 2`) cross-term cancellation and trivial rings (`ZMod 1`).
-/

open scoped BigOperators
open Finset Cslib.BitString Cslib.AffineTaylor

namespace AffineTaylorTests

private theorem cube_two_sum {M : Type*} [AddCommMonoid M]
    (s : Finset (Fin 2 → Bool)) (f : (Fin 2 → Bool) → M) (hs : ∀ x, x ∈ s) :
    (∑ x ∈ s, f x) =
      f ![false, false] + f ![false, true] + f ![true, false] + f ![true, true] := by
  have hsuniv : s = univ := Finset.eq_univ_iff_forall.mpr hs
  rw [hsuniv, ← (finTwoArrowEquiv Bool).symm.sum_comp f]
  change (∑ b : Bool × Bool, f ![b.1, b.2]) = _
  simp only [Fintype.sum_prod_type, Fintype.sum_bool]
  ac_rfl

private theorem cube_one_sum {M : Type*} [AddCommMonoid M]
    (s : Finset (Fin 1 → Bool)) (f : (Fin 1 → Bool) → M) (hs : ∀ x, x ∈ s) :
    (∑ x ∈ s, f x) = f (fun _ => false) + f (fun _ => true) := by
  have hsuniv : s = univ := Finset.eq_univ_iff_forall.mpr hs
  rw [hsuniv, ← (Equiv.funUnique (Fin 1) Bool).symm.sum_comp f]
  change (∑ b : Bool, f (fun _ => b)) = _
  simp only [Fintype.sum_bool]
  exact add_comm _ _

open Classical in
private noncomputable def restrictedJet {ι F A : Type*} [Fintype ι] [CommRing A] {κ : F → Type*}
    (s : Finset F) (Φ : ∀ f, MvPolynomial (κ f) A) (P : ∀ f, κ f → ι → Polynomial A)
    (t : A) (q j : ℕ) : A :=
  ∑ E ∈ (univ : Finset ι).powerset.filter (fun E => #E ≤ q),
    ∑ U ∈ E.powerset, (-1 : A) ^ (#E - #U) *
      ∑ x ∈ (univ : Finset (ι → Bool)).filter (fun x => ∀ i ∈ E, x i = true),
        MvPolynomial.eval (fun i => bitVal A (decide (i ∈ U)))
          ((factorProduct s Φ P t x).coeff j)

/-! ### 1. Scalar Taylor corrections at nonzero node -/

-- Nonconstant quadratic polynomial at nonzero node t = 2: constant term vanishes and X divides it.
example :
    (Polynomial.taylor (2 : ℤ) (3 - 2 * Polynomial.X + Polynomial.X ^ 2) -
      Polynomial.C ((3 - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ).eval 2)).coeff 0 = 0 ∧
    (Polynomial.X ∣ Polynomial.taylor (2 : ℤ) (3 - 2 * Polynomial.X + Polynomial.X ^ 2) -
      Polynomial.C ((3 - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ).eval 2)) ∧
    Polynomial.taylor (2 : ℤ) (3 - 2 * Polynomial.X + Polynomial.X ^ 2) -
      Polynomial.C ((3 - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ).eval 2) =
        2 * Polynomial.X + Polynomial.X ^ 2 := by
  refine ⟨coeff_zero_taylor_sub_C_eval 2 _, X_dvd_taylor_sub_C_eval 2 _, ?_⟩
  simp only [map_add, map_sub, Polynomial.taylor_mul, Polynomial.taylor_X_pow, Polynomial.taylor_X]
  have h3 : Polynomial.taylor (2 : ℤ) (3 : Polynomial ℤ) = 3 := Polynomial.taylor_C 2 3
  have h2 : Polynomial.taylor (2 : ℤ) (2 : Polynomial ℤ) = 2 := Polynomial.taylor_C 2 2
  have hev : (3 - 2 * Polynomial.X + Polynomial.X ^ 2 : Polynomial ℤ).eval 2 = 3 := by
    simp [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul]
  rw [h3, h2, hev]
  change (3 : Polynomial ℤ) - 2 * (Polynomial.X + 2) + (Polynomial.X + 2) ^ 2 - 3 = _
  ring

/-! ### 2. Multi-factor, dependent-variable, mixed-sign, nonzero-node system -/

private abbrev depVars : Bool → Type
  | true => Fin 2
  | false => Fin 1

private noncomputable def twoFactors : (b : Bool) → MvPolynomial (depVars b) ℤ
  | true => MvPolynomial.X 0 - 2 * MvPolynomial.X 1
  | false => 1 - MvPolynomial.X 0

private noncomputable def twoRows : (b : Bool) → depVars b → Fin 2 → Polynomial ℤ
  | true => ![![1 + Polynomial.X ^ 2, -Polynomial.X], ![2 * Polynomial.X, 1 - Polynomial.X]]
  | false => ![![Polynomial.X, 2 + Polynomial.X]]

private theorem replacedSum_twoFactors :
    replacedSum ({true, false} : Finset Bool) twoFactors twoRows =
      4 + Polynomial.X + 9 * Polynomial.X ^ 2 - 3 * Polynomial.X ^ 3 := by
  unfold replacedSum
  rw [cube_two_sum]
  · simp only [Finset.prod_pair (by decide : true ≠ false)]
    dsimp only [twoFactors, twoRows]
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      bitVal_false, bitVal_true, map_zero, map_one, mul_zero, mul_one, add_zero, zero_add,
      map_sub, map_mul, map_ofNat, MvPolynomial.aeval_X]
    ring
  · intro x
    simp

private theorem taylor_two_replacedSum_twoFactors :
    Polynomial.taylor (2 : ℤ) (replacedSum ({true, false} : Finset Bool) twoFactors twoRows) =
      18 + Polynomial.X - 9 * Polynomial.X ^ 2 - 3 * Polynomial.X ^ 3 := by
  rw [replacedSum_twoFactors]
  simp only [map_sub, map_add, Polynomial.taylor_mul, Polynomial.taylor_X_pow, Polynomial.taylor_X]
  have h4 : Polynomial.taylor (2 : ℤ) (4 : Polynomial ℤ) = 4 := Polynomial.taylor_C 2 4
  have h9 : Polynomial.taylor (2 : ℤ) (9 : Polynomial ℤ) = 9 := Polynomial.taylor_C 2 9
  have h3 : Polynomial.taylor (2 : ℤ) (3 : Polynomial ℤ) = 3 := Polynomial.taylor_C 2 3
  rw [h4, h9, h3]
  change (4 : Polynomial ℤ) + (Polynomial.X + 2) + 9 * (Polynomial.X + 2) ^ 2 -
      3 * (Polynomial.X + 2) ^ 3 = _
  ring

-- Common q = 2 bound covers j = 0 < q, j = 1 < q, and j = 2 = q at nonzero node t = 2,
-- and boundary q = 0 at j = 0 still captures full x-dependent baselines.
example :
    restrictedJet ({true, false} : Finset Bool) twoFactors twoRows 2 2 0 = 18 ∧
    restrictedJet ({true, false} : Finset Bool) twoFactors twoRows 2 2 1 = 1 ∧
    restrictedJet ({true, false} : Finset Bool) twoFactors twoRows 2 2 2 = -9 ∧
    restrictedJet ({true, false} : Finset Bool) twoFactors twoRows 2 0 0 = 18 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [restrictedJet, ← coeff_taylor_replacedSum_eq_restricted_subsets _ _ _ 2 (by decide : 0 ≤ 2),
      taylor_two_replacedSum_twoFactors]
    simp [Polynomial.coeff_X]
  · rw [restrictedJet, ← coeff_taylor_replacedSum_eq_restricted_subsets _ _ _ 2 (by decide : 1 ≤ 2),
      taylor_two_replacedSum_twoFactors]
    simp [Polynomial.coeff_X]
  · rw [restrictedJet, ← coeff_taylor_replacedSum_eq_restricted_subsets _ _ _ 2 (by decide : 2 ≤ 2),
      taylor_two_replacedSum_twoFactors]
    simp [Polynomial.coeff_X]
  · rw [restrictedJet, ← coeff_taylor_replacedSum_eq_restricted_subsets _ _ _ 2 (by decide : 0 ≤ 0),
      taylor_two_replacedSum_twoFactors]
    simp [Polynomial.coeff_X]

-- Genuine x-dependence of G_x: at X = 0, [z^0] G_x differs across assignments x (1 vs -3).
example :
    MvPolynomial.eval 0 ((factorProduct ({true, false} : Finset Bool)
      twoFactors twoRows 2 ![false, false]).coeff 0) ≠
    MvPolynomial.eval 0 ((factorProduct ({true, false} : Finset Bool)
      twoFactors twoRows 2 ![true, false]).coeff 0) := by
  simp only [eval_coeff_factorProduct, Finset.prod_pair (by decide : true ≠ false),
    map_eval_affineFactor, map_eval_affineInput]
  dsimp only [twoFactors, twoRows]
  simp [Fin.sum_univ_two, bitVal]

-- Negative control (j > q): truncating subsets to #E ≤ 0 loses the j = 1 jet coefficient (0 ≠ 1).
example : restrictedJet ({true, false} : Finset Bool) twoFactors twoRows 2 0 1 ≠
    (Polynomial.taylor 2
      (replacedSum ({true, false} : Finset Bool) twoFactors twoRows)).coeff 1 := by
  have hpow : (univ : Finset (Fin 2)).powerset.filter (fun E => #E ≤ 0) = {∅} := by
    ext E
    simp only [mem_filter, mem_powerset, subset_univ, true_and, Nat.le_zero, card_eq_zero,
      mem_singleton]
  rw [taylor_two_replacedSum_twoFactors]
  have hrhs : (18 + Polynomial.X - 9 * Polynomial.X ^ 2 - 3 * Polynomial.X ^ 3 :
      Polynomial ℤ).coeff 1 = 1 := by simp [Polynomial.coeff_X]
  rw [hrhs]
  unfold restrictedJet
  rw [hpow, sum_singleton, powerset_empty, sum_singleton]
  rw [cube_two_sum _ _ (fun x => by simp)]
  simp only [card_empty, tsub_zero, pow_zero, one_mul, eval_coeff_factorProduct, notMem_empty,
    decide_false, bitVal_false, Finset.prod_pair (by decide : true ≠ false),
    map_eval_affineFactor, map_eval_affineInput, map_zero, zero_mul]
  dsimp only [twoFactors, twoRows]
  simp [Fin.sum_univ_two, bitVal]
  norm_num

-- Baseline x-dependence control: replacing G_x by G_{1_U} at q = 0, j = 0 fails (0 ≠ 18).
example :
    (∑ E ∈ (univ : Finset (Fin 2)).powerset.filter (fun E => #E ≤ 0),
      ∑ U ∈ E.powerset, (-1 : ℤ) ^ (#E - #U) *
        ∑ _x ∈ (univ : Finset (Fin 2 → Bool)).filter (fun x => ∀ i ∈ E, x i = true),
          MvPolynomial.eval (fun i => bitVal ℤ (decide (i ∈ U)))
            ((factorProduct ({true, false} : Finset Bool) twoFactors twoRows 2
              (fun i => decide (i ∈ U))).coeff 0)) = 0 := by
  have hpow : (univ : Finset (Fin 2)).powerset.filter (fun E => #E ≤ 0) = {∅} := by
    ext E
    simp only [mem_filter, mem_powerset, subset_univ, true_and, Nat.le_zero, card_eq_zero,
      mem_singleton]
  rw [hpow, sum_singleton, powerset_empty, sum_singleton]
  rw [cube_two_sum _ _ (fun x => by simp)]
  simp only [card_empty, tsub_zero, pow_zero, one_mul, notMem_empty, decide_false, bitVal_false,
    eval_coeff_factorProduct, Finset.prod_pair (by decide : true ≠ false), map_eval_affineFactor,
    map_eval_affineInput, mul_zero, map_zero, zero_mul]
  dsimp only [twoFactors, twoRows]
  simp

/-! ### 3. Empty factor sets and empty coordinate types -/

-- Empty factor set on 2 coordinates gives constant polynomial 4, so [z^0] = 4 and [z^1] = 0.
example :
    restrictedJet (∅ : Finset Bool) twoFactors twoRows 5 0 0 = 4 ∧
    restrictedJet (∅ : Finset Bool) twoFactors twoRows 5 1 1 = 0 := by
  refine ⟨?_, ?_⟩
  · rw [restrictedJet, ← coeff_taylor_replacedSum_eq_restricted_subsets _ _ _ 5 (by decide : 0 ≤ 0),
      replacedSum_empty]
    norm_num
  · rw [restrictedJet, ← coeff_taylor_replacedSum_eq_restricted_subsets _ _ _ 5 (by decide : 1 ≤ 1),
      replacedSum_empty]
    norm_num [Polynomial.coeff_one]

-- Empty coordinate type (Fin 0) and empty factor-variable type (Fin 0) at nonzero node t = 3.
example : restrictedJet (ι := Fin 0) ({()} : Finset Unit)
    (fun _ => MvPolynomial.C (-7 : ℤ))
    (fun _ (v : Fin 0) => Fin.elim0 v) 3 0 0 = -7 := by
  rw [restrictedJet, ← coeff_taylor_replacedSum_eq_restricted_subsets _ _ _ 3 (by decide : 0 ≤ 0),
    Polynomial.taylor_coeff_zero, eval_replacedSum]
  have hsum0 : ∀ (s : Finset (Fin 0 → Bool)) (g : (Fin 0 → Bool) → ℤ),
      (∀ x, x ∈ s) → (∑ x ∈ s, g x) = g Fin.elim0 := by
    intro s g hs
    have hs' : s = {Fin.elim0} := by
      ext x
      simp only [hs x, mem_singleton, true_iff]
      funext i
      exact Fin.elim0 i
    rw [hs', sum_singleton]
  rw [hsum0]
  · simp only [prod_singleton, MvPolynomial.eval_C]
  · exact Finset.mem_univ

/-! ### 4. Characteristic 2 (ZMod 2) cancellation and trivial ring (ZMod 1) -/

-- Over ZMod 2 on Fin 1 → Bool with Φ(Y) = Y^2 and row P(T) = T, H(T) = T^2.
-- At nonzero node t = 1, H(1 + z) = (1 + z)^2 = 1 + z^2: order-1 cross term cancels mod 2,
-- while order-2 Hasse coefficient equals 1 without division by 2!.
private noncomputable def charTwoFactor : Unit → MvPolynomial Unit (ZMod 2) :=
  fun _ => (MvPolynomial.X ()) ^ 2

private noncomputable def charTwoRow : Unit → Unit → Fin 1 → Polynomial (ZMod 2) :=
  fun _ _ _ => Polynomial.X

private theorem taylor_one_charTwo :
    Polynomial.taylor (1 : ZMod 2)
      (replacedSum ({()} : Finset Unit) charTwoFactor charTwoRow) =
        1 + Polynomial.X ^ 2 := by
  have hsum : replacedSum ({()} : Finset Unit) charTwoFactor charTwoRow = Polynomial.X ^ 2 := by
    unfold replacedSum
    rw [cube_one_sum]
    · simp only [prod_singleton, charTwoFactor, charTwoRow, Fintype.sum_unique, bitVal_false,
        bitVal_true, map_zero, map_one, mul_zero, mul_one, map_pow, MvPolynomial.aeval_X]
      ring
    · intro x
      simp
  have htwo : (2 : Polynomial (ZMod 2)) = 0 := by
    simpa only [map_ofNat, map_zero] using
      congrArg Polynomial.C (show (2 : ZMod 2) = 0 by decide)
  rw [hsum, Polynomial.taylor_X_pow, map_one]
  calc
    (Polynomial.X + 1 : Polynomial (ZMod 2)) ^ 2 =
        1 + 2 * Polynomial.X + Polynomial.X ^ 2 := by ring
    _ = 1 + Polynomial.X ^ 2 := by rw [htwo, zero_mul, add_zero]

example :
    restrictedJet ({()} : Finset Unit) charTwoFactor charTwoRow 1 2 1 = 0 ∧
    restrictedJet ({()} : Finset Unit) charTwoFactor charTwoRow 1 2 2 = 1 ∧
    restrictedJet ({()} : Finset Unit)
      (fun _ => (MvPolynomial.X () : MvPolynomial Unit (ZMod 1)))
      (fun _ _ (_ : Fin 1) => Polynomial.X) 0 1 1 = 0 := by
  refine ⟨?_, ?_, Subsingleton.elim _ _⟩
  · rw [restrictedJet, ← coeff_taylor_replacedSum_eq_restricted_subsets _ _ _ 1 (by decide : 1 ≤ 2),
      taylor_one_charTwo]
    simp [Polynomial.coeff_one]
  · rw [restrictedJet, ← coeff_taylor_replacedSum_eq_restricted_subsets _ _ _ 1 (by decide : 2 ≤ 2),
      taylor_one_charTwo]
    simp [Polynomial.coeff_one]

end AffineTaylorTests
