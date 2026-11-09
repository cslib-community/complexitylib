/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.FineGrained.WeightedComparisonDistribution

/-!
# Real-exponent and source-parameter weighted counting

[ChenJiangZhu2027], Lemma A.1 and Corollary A.2 (PDF pp.28–29), fix a real
weight exponent and a source parameter p with p ≤ n and n plus predicate count O(p).
Enlarging the fixed exponent to its natural ceiling preserves every admissible coefficient.
The actual counters below use that ceiling, not an advised circuit, count or runtime.
The source exponent is the unshifted η(p); its bound holds beyond the explicit fixed
threshold max(16,K), as required for the asymptotic statement. Exact counts include n = 0.

## Main results

* `weight_bound_of_parameter`: real source promises imply the implemented natural promise.
* `exists_count_source_certificate`: actual correlated tests, original count and sharp resources.
* `exists_distribution_source_certificate`: actual complete ordered joint output and resources.
-/

public section

namespace Cslib.Circuits.Boolean.WeightedSum

open Turing.MultiTapeTM Cslib.GenericRAM Cslib.Complexity Logic.PL

/-- Cofinal enlargement of the fixed real source exponent, without converting coefficients
or targets to unary. Empty declarations require no special coefficient assumption. -/
theorem weight_bound_of_parameter {p n r : ℕ} (c : ℝ) (hc : 0 ≤ c) (hpn : p ≤ n)
    (weights : Fin r → Fin n → ℕ) (hw : ∀ j i, (weights j i : ℝ) ≤ (p : ℝ) ^ c) :
    ∀ j i, weights j i ≤ n ^ ⌈c⌉₊ := by
  intro j i
  have hi := i.isLt
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hpnR : (p : ℝ) ≤ n := by exact_mod_cast hpn
  have h : (weights j i : ℝ) ≤ (n : ℝ) ^ c :=
    (hw j i).trans (Real.rpow_le_rpow (Nat.cast_nonneg p) hpnR hc)
  have hh := h.trans (Real.rpow_le_rpow_of_exponent_le hn (Nat.le_ceil c))
  rw [Real.rpow_natCast] at hh
  exact_mod_cast hh

private theorem source_clock_le {T L C e A z p K : ℕ}
    (ht : T ≤ C * (L + 1) ^ e * 2 ^ (A * Nat.logLogSqrtLogScale z))
    (hz : z ≤ K * p) (hp : max 16 K ≤ p) :
    (T : ℝ) ≤ (C : ℝ) * (L + 1 : ℕ) ^ e *
      (2 : ℝ) ^ ((A * (120 * K) : ℕ) * Real.logLogSqrtLogScale p) := by
  have hR : (T : ℝ) ≤ (C : ℝ) * (L + 1 : ℕ) ^ e *
      (2 : ℝ) ^ (A * Nat.logLogSqrtLogScale z) := by exact_mod_cast ht
  have hx := mul_le_mul_of_nonneg_left
    (Nat.cast_logLogSqrtLogScale_le_of_le_mul K hz hp) (Nat.cast_nonneg A)
  rw [← Real.rpow_natCast (2 : ℝ) (A * Nat.logLogSqrtLogScale z)] at hR
  apply hR.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  simpa only [Nat.cast_mul, Nat.cast_ofNat, mul_assoc] using hx

open Classical in
/-- Corollary A.2 for any fixed real c ≥ 0: the actual original-input counter and native
resources, preserving every original predicate and annotation multiplicity. Source encodings
with p ≤ n and n + h ≤ Kp have time L^O(1) 2^O(η(p)) and global polynomial workspace. -/
theorem exists_count_source_certificate {r : ℕ} (op : Fin r → Comparison)
    (b d : ℕ) (c : ℝ) (hc : 0 ≤ c) (K : ℕ) :
    ∃ count : WithBase.Input → ℕ,
      ∃ cs : NativeCertificate count WithBase.encInput encNat, ∃ C e A : ℕ,
        (∀ x, cs.space x ≤ C * ((WithBase.encInput x).length + 1) ^ e) ∧
        ∀ {n p : ℕ} (B : CNF (Fin n)) (P : List (DNF (Fin n)))
          (weights : Fin r → Fin n → ℕ) (positive : Fin r → Fin n → Bool) (target : Fin r → ℤ)
          (_hpn : p ≤ n) (_hw : ∀ j i, (weights j i : ℝ) ≤ (p : ℝ) ^ c)
          (_hb : ∀ clause ∈ B, clause.length ≤ b) (_hp : ∀ q ∈ P, ∀ t ∈ q, t.length ≤ d),
          count (WithBase.ofData B P weights positive target) =
            Fintype.card {x : Fin n → Bool //
              (∀ j, (op j).Holds (value (weights j) (positive j) x) (target j)) ∧
                B.eval x = true ∧ ∀ q ∈ P, DNF.eval x q = true} ∧
          (n + P.length ≤ K * p → max 16 K ≤ p →
            (cs.time (WithBase.ofData B P weights positive target) : ℝ) ≤
              (C : ℝ) * ((WithBase.encInput
                (WithBase.ofData B P weights positive target)).length + 1 : ℕ) ^ e *
                (2 : ℝ) ^ ((A : ℝ) * Real.logLogSqrtLogScale p)) := by
  obtain ⟨count, cs, C, e, A, hs, h⟩ := WithBase.exists_count_sharp_certificate op b d ⌈c⌉₊
  refine ⟨count, cs, C, e, A * (120 * K), hs, ?_⟩
  intro n p B P weights positive target hpn hw hb hp
  have ht := h B P weights positive target (weight_bound_of_parameter c hc hpn weights hw) hb hp
  exact ⟨ht.1, fun hz hn => source_clock_le ht.2 hz hn⟩

open Classical in
/-- Actual complete joint distribution under the real source weight promise. Every tagged bin
(including zero counts) is retained in the fixed-dimensional grid's first-slowest order.
The full output and all calls share one sharp source clock and polynomial peak workspace. -/
theorem exists_distribution_source_certificate (r b d : ℕ) (c : ℝ) (hc : 0 ≤ c) (K : ℕ) :
    ∃ distribution : Distribution.Input → List Distribution.Entry,
      ∃ cs : NativeCertificate distribution Distribution.encInput
        (encList Distribution.encEntry), ∃ C e A : ℕ,
        (∀ x, cs.space x ≤ C * ((Distribution.encInput x).length + 1) ^ e) ∧
        ∀ {n p : ℕ} (B : CNF (Fin n)) (P : List (DNF (Fin n)))
          (weights : Fin r → Fin n → ℕ) (positive : Fin r → Fin n → Bool)
          (_hpn : p ≤ n) (_hw : ∀ j i, (weights j i : ℝ) ≤ (p : ℝ) ^ c)
          (_hb : ∀ clause ∈ B, clause.length ≤ b) (_hp : ∀ q ∈ P, ∀ t ∈ q, t.length ≤ d),
          distribution (Distribution.ofData B P weights positive) =
            (DegreePartition.SizeVectors.vectors r (n ^ (⌈c⌉₊ + 1))).map
              (fun v => (v, Distribution.countForVector B P weights positive v)) ∧
          (n + P.length ≤ K * p → max 16 K ≤ p →
            (cs.time (Distribution.ofData B P weights positive) : ℝ) ≤
              (C : ℝ) * ((Distribution.encInput
                (Distribution.ofData B P weights positive)).length + 1 : ℕ) ^ e *
                (2 : ℝ) ^ ((A : ℝ) * Real.logLogSqrtLogScale p)) := by
  obtain ⟨dist, cs, C, e, A, hs, h⟩ :=
    Distribution.exists_distribution_sharp_certificate r b d ⌈c⌉₊
  refine ⟨dist, cs, C, e, A * (120 * K), hs, ?_⟩
  intro n p B P weights positive hpn hw hb hp
  have ht := h B P weights positive (weight_bound_of_parameter c hc hpn weights hw) hb hp
  exact ⟨ht.1, fun hz hn => source_clock_le ht.2 hz hn⟩

end Cslib.Circuits.Boolean.WeightedSum
