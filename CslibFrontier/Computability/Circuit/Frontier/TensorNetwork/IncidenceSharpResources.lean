/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.IncidenceOriginalCounter
public import CslibFrontier.Foundations.Data.Nat.LogLogSqrtLogReal

/-!
# Absorb actual incidence-array traversal into the sharper counting exponent

The actual native stream already charges construction, entry extraction, contraction and scalar
readback. Here its complete degree-array multiplier is absorbed into the single-iterated-log
integer scale. No output-size-to-runtime inference or faster solver hypothesis is used.
This is the admissible sparse-branch solver, not yet high-incidence/parity/sparsification
composition or the complete source Theorem 7.1.

## Main results

* `Cslib.Circuits.Frontier.IncidenceNetwork.exists_countOriginal_sharp_certificate`: actual
  array/contraction time and polynomial space in the rounded scale.
* `Cslib.Circuits.Frontier.IncidenceNetwork.exists_countOriginal_real_sharp_certificate`: the
  real base-two source exponent with all rounding costs charged.

## References

* [OpenAI2026ETH], Appendix D.3, Lemma D.2, PDF pp.55–57, degree-array and contraction bounds.
* [ChenJiangZhu2027], Lemma 3.2 (p.11), Proposition 4.2 (p.14), Theorem 7.1 (pp.23–24).
-/

public section

namespace Cslib.Circuits.Frontier.IncidenceNetwork

open Cslib.GenericRAM Cslib.Complexity Turing.MultiTapeTM Filter

private theorem eventually_degreeCount_le (k c : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ sys : List (List (List ℕ)), sys.length ≤ c * n →
      degreeCount k (n, sys) + 1 ≤ 2 ^ (4 * Nat.logLogSqrtLogScale n + 1) := by
  filter_upwards [Nat.eventually_sqrt_mul_clog_le_logLogSqrtLogScale
    (Nat.clog 2 (k * (c + 2) + 1)), eventually_ge_atTop 4] with n hn hn4 sys hs
  have h := degreeCount_le k (by omega : 1 ≤ n) hs
  have he : 4 * n.sqrt * (Nat.clog 2 (k * (c + 2) + 1) + Nat.clog 2 n) ≤
      4 * Nat.logLogSqrtLogScale n := by nlinarith
  have hd := h.trans (Nat.pow_le_pow_right (by decide : 0 < 2) he)
  calc degreeCount k (n, sys) + 1 ≤
      2 ^ (4 * Nat.logLogSqrtLogScale n) + 2 ^ (4 * Nat.logLogSqrtLogScale n) :=
        Nat.add_le_add hd Nat.one_le_two_pow
    _ = _ := by rw [pow_succ]; omega

private theorem factor_le (A : ℕ) {n : ℕ} (hn : 4 ≤ n) {D : ℕ}
    (hD : D ≤ 2 ^ (4 * Nat.logLogSqrtLogScale n + 1)) (L : ℕ) :
    D * (A * (L + 1) ^ A * 2 ^ (A * sizeParam n / Nat.sqrt (Nat.log 2 (sizeParam n)))) ≤
      A * (L + 1) ^ A * 2 ^ ((2 * A + 5) * Nat.logLogSqrtLogScale n) := by
  let E := Nat.logLogSqrtLogScale n
  have hE : 1 ≤ E := Nat.one_le_logLogSqrtLogScale hn
  have hexp : A * sizeParam n / Nat.sqrt (Nat.log 2 (sizeParam n)) ≤ A * E + A :=
    Nat.mul_padded_div_sqrt_log_two_le A hn
  calc _ ≤ 2 ^ (4 * E + 1) * (A * (L + 1) ^ A * 2 ^ (A * E + A)) :=
        Nat.mul_le_mul hD (Nat.mul_le_mul_left _
          (Nat.pow_le_pow_right (by decide : 0 < 2) hexp))
    _ = A * (L + 1) ^ A * 2 ^ (4 * E + 1 + (A * E + A)) := by rw [pow_add]; ring
    _ ≤ _ := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide : 0 < 2)
      (by nlinarith [Nat.mul_le_mul_left (A + 1) hE]))

/-- The actual native original-input solver has a single-iterated-log exponent after charging
and absorbing every degree array. Space stays polynomial in the full original encoding. The
threshold and constants depend only on fixed k,c. The following theorem supplies the real-log
comparison; high-incidence/parity/sparsification compositions have their own statements. -/
theorem exists_countOriginal_sharp_certificate (k c : ℕ) (hk : 1 ≤ k) :
    ∃ (cs : NativeCertificate (countOriginal k) encArrayInput encNat) (A n₀ : ℕ),
      ∀ n, n₀ ≤ n → ∀ sys,
        SubexponentialSAT.IncidenceBranching.IsSparseBranch k c n sys →
        let L := (encArrayInput (n, sys)).length
        cs.time (n, sys) ≤ A * (L + 1) ^ A * 2 ^ (A * Nat.logLogSqrtLogScale n) ∧
          cs.space (n, sys) ≤ A * (L + 1) ^ A := by
  obtain ⟨cs, A, n₀, P, hP, _, hcs⟩ := exists_countOriginal_certificate k c hk
  obtain ⟨C, d, hCd⟩ := Cslib.polynomiallyBounded_iff_le.mp hP
  obtain ⟨n₁, hn₁⟩ := eventually_atTop.mp (eventually_degreeCount_le k c)
  let B := 2 * A + C + d + 6
  refine ⟨cs, B, max (max n₀ n₁) 4, fun n hn sys hs => ?_⟩
  have hn₀ : n₀ ≤ n := (le_max_left _ _).trans ((le_max_left _ _).trans hn)
  have hn₁' : n₁ ≤ n := (le_max_right _ _).trans ((le_max_left _ _).trans hn)
  have hn4 : 4 ≤ n := (le_max_right _ _).trans hn
  obtain ⟨ht, hspace⟩ := hcs n hn₀ sys hs
  let L := (encArrayInput (n, sys)).length
  let E := Nat.logLogSqrtLogScale n
  have hD := hn₁ n hn₁' sys hs.length_le
  have hf := factor_le A hn4 hD L
  have hA : A ≤ B := by dsimp only [B]; omega
  have hd : d ≤ B := by dsimp only [B]; omega
  have he : 2 * A + 5 ≤ B := by dsimp only [B]; omega
  have hCA : C + A ≤ B := by dsimp only [B]; omega
  have hp : P L ≤ C * (L + 1) ^ B :=
    (hCd L).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) hd))
  have hpT : P L ≤ C * (L + 1) ^ B * 2 ^ (B * E) :=
    hp.trans (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _))
  have hfT : A * (L + 1) ^ A * 2 ^ ((2 * A + 5) * E) ≤
      A * (L + 1) ^ B * 2 ^ (B * E) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) hA))
      (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ he))
  constructor
  · calc cs.time (n, sys) ≤ P L + A * (L + 1) ^ A * 2 ^ ((2 * A + 5) * E) :=
          ht.trans (Nat.add_le_add_left hf _)
      _ ≤ C * (L + 1) ^ B * 2 ^ (B * E) + A * (L + 1) ^ B * 2 ^ (B * E) :=
          Nat.add_le_add hpT hfT
      _ = (C + A) * (L + 1) ^ B * 2 ^ (B * E) := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hCA)
  · calc cs.space (n, sys) ≤ P L + A * (L + 1) ^ A := hspace
      _ ≤ C * (L + 1) ^ B + A * (L + 1) ^ B :=
          Nat.add_le_add hp (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) hA))
      _ = (C + A) * (L + 1) ^ B := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ hCA

/-- Actual binary time in the real base-two source scale, with all rounding and array costs
proved above. This is the sparse branch solver; it does not assume the complete CNF counter. -/
theorem exists_countOriginal_real_sharp_certificate (k c : ℕ) (hk : 1 ≤ k) :
    ∃ (cs : NativeCertificate (countOriginal k) encArrayInput encNat) (A n₀ : ℕ),
      ∀ n, n₀ ≤ n → ∀ sys,
        SubexponentialSAT.IncidenceBranching.IsSparseBranch k c n sys →
        let L := (encArrayInput (n, sys)).length
        (cs.time (n, sys) : ℝ) ≤ (A : ℝ) * (L + 1 : ℕ) ^ A *
          (2 : ℝ) ^ (((6 * A : ℕ) : ℝ) * Real.logLogSqrtLogScale n) ∧
          cs.space (n, sys) ≤ A * (L + 1) ^ A := by
  obtain ⟨cs, A, n₀, hcs⟩ := exists_countOriginal_sharp_certificate k c hk
  refine ⟨cs, A, max n₀ 16, fun n hn sys hs => ?_⟩
  obtain ⟨ht, hspace⟩ := hcs n ((le_max_left _ _).trans hn) sys hs
  refine ⟨?_, hspace⟩
  have htR : (cs.time (n, sys) : ℝ) ≤ (A : ℝ) *
      ((encArrayInput (n, sys)).length + 1 : ℕ) ^ A *
      (2 : ℝ) ^ (A * Nat.logLogSqrtLogScale n) := by exact_mod_cast ht
  refine htR.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  exact Nat.two_pow_mul_logLogSqrtLogScale_le A ((le_max_right _ _).trans hn)

end Cslib.Circuits.Frontier.IncidenceNetwork
