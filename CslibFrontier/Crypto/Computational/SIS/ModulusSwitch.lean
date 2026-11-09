/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.SIS.ModuleEncryption
public import CslibFrontier.Foundations.Data.ZMod.ModulusSwitch

/-!
# Rounded modulus switching for Module-LWE ciphertext phases

The existing ciphertext type is converted coefficientwise using `ZMod.modulusSwitch`. Its
canonical centered lifts may be replaced by arbitrary integer representatives. An explicit
carry polynomial accounts for wraparound at the source modulus. The switched phase has an
integer representative differing from the rationally scaled original phase by at most half of
one plus the full coefficient
`ℓ₁` norm of the integer secret.

This is original supporting nearest-integer algebra. It is not the parity-preserving switching
variant: half-integer ties round toward positive infinity. No Boolean decoding preservation,
security reduction, sampling law, or native runtime bound is claimed.

## Main definitions

* `moduleLWEModulusSwitch`: coefficientwise conversion of the existing ciphertext type.

## Main results

* `exists_moduleLWEModulusSwitch_phase_of_lifts`: phase identity and rounding-error bounds
  from arbitrary integer lifts and an explicit carry equation.
* `exists_moduleLWEModulusSwitch_phase_of_intCast`: the bound from any integer phase representative.
* `exists_moduleLWEModulusSwitch_phase`: the bound for the canonical original phase,
  constructing the carry polynomial automatically.
-/

public section

namespace Cslib.Crypto

/-- Convert both components of a Module-LWE ciphertext by canonical nearest-integer scaling. -/
@[expose] def moduleLWEModulusSwitch {k n q : ℕ} (p : ℕ)
    (ct : ModuleLWECiphertext k n q) : ModuleLWECiphertext k n p :=
  (fun j i => ZMod.modulusSwitch p (ct.1 j i), fun i => ZMod.modulusSwitch p (ct.2 i))

private theorem innerPoly_scale_left {k n : ℕ} (c : ℚ)
    (a b : Fin k → Fin n → ℚ) (i : Fin n) :
    innerPoly (fun j l => c * a j l) b i = c * innerPoly a b i := by
  simp only [innerPoly, Finset.sum_apply, negacyclicMul, Matrix.mulVec, dotProduct,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro l _
  simp only [rotMatrix, Matrix.of_apply]
  split_ifs <;> ring

private theorem abs_innerPoly_le_half_sum {k n : ℕ}
    (a b : Fin k → Fin n → ℚ) (ha : ∀ j l, |a j l| ≤ 1 / 2) (i : Fin n) :
    |innerPoly a b i| ≤ (∑ j, ∑ l, |b j l|) / 2 := by
  calc
    |innerPoly a b i| = |∑ j, ∑ l, rotMatrix (a j) i l * b j l| := by
      simp only [innerPoly, Finset.sum_apply, negacyclicMul, Matrix.mulVec, dotProduct]
    _ ≤ ∑ j, |∑ l, rotMatrix (a j) i l * b j l| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, ∑ l, |rotMatrix (a j) i l * b j l| :=
      Finset.sum_le_sum fun j _ => Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, ∑ l, (1 / 2 : ℚ) * |b j l| := by
      apply Finset.sum_le_sum
      intro j _
      apply Finset.sum_le_sum
      intro l _
      rw [abs_mul]
      apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
      simp only [rotMatrix, Matrix.of_apply]
      split_ifs
      · exact ha j _
      · simpa only [abs_neg] using ha j _
    _ = (∑ j, ∑ l, |b j l|) / 2 := by
      simp only [← Finset.mul_sum]
      ring

/-- A switched phase has an integer representative close to the scaled original phase.

The secret at both moduli is the cast of the same integer vector `s`. The carry equation is
an integer equation, not an assumption about rounded values or the desired error bound.
Both moduli are positive; no relative-size, primality or nontriviality assumption is needed. -/
theorem exists_moduleLWEModulusSwitch_phase_of_lifts {k n q p : ℕ}
    (hq : 0 < q) (hp : 0 < p) (ct : ModuleLWECiphertext k n q)
    (u s : Fin k → Fin n → ℤ) (v e w : Fin n → ℤ)
    (hu : (fun j i => (u j i : ZMod q)) = ct.1)
    (hv : (fun i => (v i : ZMod q)) = ct.2)
    (hphase : v - innerPoly u s = fun i => e i + q * w i) :
    ∃ e' : Fin n → ℤ,
      (moduleLWEModulusSwitch p ct).2 -
          innerPoly (moduleLWEModulusSwitch p ct).1 (fun j i => (s j i : ZMod p)) =
        (fun i => (e' i : ZMod p)) ∧
      (∀ i, |(e' i : ℚ) - (p : ℚ) / q * e i| ≤
        (1 + ∑ j, ∑ l, |(s j l : ℚ)|) / 2) ∧
      (∀ i, |(e' i : ℚ)| ≤ (p : ℚ) / q * |(e i : ℚ)| +
        (1 + ∑ j, ∑ l, |(s j l : ℚ)|) / 2) := by
  let c : ℚ := (p : ℚ) / q
  let ur : Fin k → Fin n → ℤ := fun j i => round (c * u j i)
  let vr : Fin n → ℤ := fun i => round (c * v i)
  let e' : Fin n → ℤ := fun i => vr i - innerPoly ur s i - p * w i
  let a : Fin k → Fin n → ℚ := fun j i => (u j i : ℚ)
  let b : Fin k → Fin n → ℚ := fun j i => (s j i : ℚ)
  let ar : Fin k → Fin n → ℚ := fun j i => (ur j i : ℚ)
  let δ : Fin k → Fin n → ℚ := ar - fun j i => c * a j i
  have hcast (x : Fin k → Fin n → ℤ) (i : Fin n) :
      ((innerPoly x s i : ℤ) : ℚ) = innerPoly (fun j l => (x j l : ℚ)) b i :=
    congrFun (map_innerPoly (Int.castRingHom ℚ) x s) i
  have herr (i : Fin n) :
      (e' i : ℚ) - c * e i = ((vr i : ℚ) - c * v i) - innerPoly δ b i := by
    have hi := congrArg (fun x : ℤ => (x : ℚ)) (congrFun hphase i)
    simp only [Pi.sub_apply, Int.cast_sub, Int.cast_add, Int.cast_mul, Int.cast_natCast] at hi
    rw [hcast] at hi
    have hq' : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne'
    have hc : c * q = (p : ℚ) := div_mul_cancel₀ _ hq'
    dsimp only [e', δ]
    rw [innerPoly_sub_left]
    simp only [Pi.sub_apply, Int.cast_sub, Int.cast_mul, Int.cast_natCast]
    rw [hcast, innerPoly_scale_left]
    dsimp only [a, ar] at *
    linear_combination c * hi + (w i : ℚ) * hc
  have hδ : ∀ j l, |δ j l| ≤ 1 / 2 := by
    intro j l
    dsimp only [δ, ar, ur, a, Pi.sub_apply]
    rw [abs_sub_comm]
    exact abs_sub_round _
  have hnear (i : Fin n) : |(e' i : ℚ) - c * e i| ≤
      (1 + ∑ j, ∑ l, |(s j l : ℚ)|) / 2 := by
    rw [herr]
    calc
      |(vr i : ℚ) - c * v i - innerPoly δ b i| ≤
          |(vr i : ℚ) - c * v i| + |innerPoly δ b i| := abs_sub _ _
      _ ≤ 1 / 2 + (∑ j, ∑ l, |(s j l : ℚ)|) / 2 := by
        apply add_le_add
        · rw [abs_sub_comm]
          exact abs_sub_round _
        · exact abs_innerPoly_le_half_sum δ b hδ i
      _ = _ := by ring
  refine ⟨e', ?_, hnear, ?_⟩
  · funext i
    have hs := congrFun (map_innerPoly (Int.castRingHom (ZMod p)) ur s) i
    simp only [moduleLWEModulusSwitch, ← hu, ← hv, ZMod.modulusSwitch_intCast hq.ne',
      Pi.sub_apply]
    dsimp only [e', vr, ur, c] at hs ⊢
    simp only [Int.cast_sub, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, zero_mul,
      sub_zero]
    exact congrArg (fun x : ZMod p => (round ((p : ℚ) / q * v i) : ℤ) - x) hs.symm
  · intro i
    have hc : 0 ≤ c := div_nonneg (by positivity) (by positivity)
    calc
      |(e' i : ℚ)| = |((e' i : ℚ) - c * e i) + c * e i| := by ring_nf
      _ ≤ |(e' i : ℚ) - c * e i| + |c * e i| := abs_add_le _ _
      _ ≤ (1 + ∑ j, ∑ l, |(s j l : ℚ)|) / 2 + c * |(e i : ℚ)| := by
        rw [abs_mul, abs_of_nonneg hc]
        exact add_le_add (hnear i) le_rfl
      _ = _ := by ring

/-- The phase bound for any supplied integer representative of the original phase.
Carries are constructed from the modular phase identity, including representatives outside
the centered interval. This lets plaintext/error decompositions reuse the same rounding bound. -/
theorem exists_moduleLWEModulusSwitch_phase_of_intCast {k n q p : ℕ}
    (hq : 0 < q) (hp : 0 < p) (ct : ModuleLWECiphertext k n q)
    (s : Fin k → Fin n → ℤ) (e : Fin n → ℤ)
    (he : (fun i => (e i : ZMod q)) =
      ct.2 - innerPoly ct.1 (fun j l => (s j l : ZMod q))) :
    ∃ e' : Fin n → ℤ,
      (moduleLWEModulusSwitch p ct).2 -
          innerPoly (moduleLWEModulusSwitch p ct).1 (fun j i => (s j i : ZMod p)) =
        (fun i => (e' i : ZMod p)) ∧
      (∀ i, |(e' i : ℚ) - (p : ℚ) / q * e i| ≤
        (1 + ∑ j, ∑ l, |(s j l : ℚ)|) / 2) ∧
      (∀ i, |(e' i : ℚ)| ≤ (p : ℚ) / q * |(e i : ℚ)| +
        (1 + ∑ j, ∑ l, |(s j l : ℚ)|) / 2) := by
  let u : Fin k → Fin n → ℤ := fun j i => (ct.1 j i).valMinAbs
  let v : Fin n → ℤ := fun i => (ct.2 i).valMinAbs
  have hu : (fun j i => (u j i : ZMod q)) = ct.1 := by
    funext j i
    exact ZMod.coe_valMinAbs _
  have hv : (fun i => (v i : ZMod q)) = ct.2 := by
    funext i
    exact ZMod.coe_valMinAbs _
  have hdvd (i : Fin n) : (q : ℤ) ∣ v i - innerPoly u s i - e i := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mp
    have hm := congrFun (map_innerPoly (Int.castRingHom (ZMod q)) u s) i
    change ((innerPoly u s i : ℤ) : ZMod q) =
      innerPoly (fun j l => (u j l : ZMod q)) (fun j l => (s j l : ZMod q)) i at hm
    rw [hu] at hm
    rw [Int.cast_sub, Int.cast_sub, hm, congrFun hv i]
    exact sub_eq_zero.mpr (congrFun he i).symm
  choose w hw using hdvd
  have hphase : v - innerPoly u s = fun i => e i + q * w i := by
    funext i
    have hi := hw i
    dsimp only [Pi.sub_apply]
    linarith
  exact exists_moduleLWEModulusSwitch_phase_of_lifts hq hp ct u s v e w hu hv hphase

/-- The actual switched ciphertext phase is close to the scaled canonical original phase.
Integer carries exist automatically; no no-wrap assumption is needed. The secret at the new
modulus is obtained from the same integer secret `s`, not by rounding the secret. -/
theorem exists_moduleLWEModulusSwitch_phase {k n q p : ℕ}
    (hq : 0 < q) (hp : 0 < p) (ct : ModuleLWECiphertext k n q)
    (s : Fin k → Fin n → ℤ) :
    ∃ e' : Fin n → ℤ,
      (moduleLWEModulusSwitch p ct).2 -
          innerPoly (moduleLWEModulusSwitch p ct).1 (fun j i => (s j i : ZMod p)) =
        (fun i => (e' i : ZMod p)) ∧
      (∀ i, |(e' i : ℚ) - (p : ℚ) / q *
          ((ct.2 - innerPoly ct.1 (fun j l => (s j l : ZMod q))) i).valMinAbs| ≤
        (1 + ∑ j, ∑ l, |(s j l : ℚ)|) / 2) ∧
      (∀ i, |(e' i : ℚ)| ≤ (p : ℚ) / q *
          |(((ct.2 - innerPoly ct.1 (fun j l => (s j l : ZMod q))) i).valMinAbs : ℚ)| +
        (1 + ∑ j, ∑ l, |(s j l : ℚ)|) / 2) := by
  apply exists_moduleLWEModulusSwitch_phase_of_intCast hq hp ct s
  funext i
  exact ZMod.coe_valMinAbs _

end Cslib.Crypto
