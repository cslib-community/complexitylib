/-
Copyright (c) 2026 Anton Kovsharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anton Kovsharov
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.PolyTime.BooleanAnalysis.BoundedIncidenceSemantics
public import CslibFrontier.Computability.PolyTime.BooleanAnalysis.BoundedIncidenceStepCert
public import CslibFrontier.Computability.PolyTime.CNF.BranchedSparseCNFCounter
import CslibFrontier.Tactic.EncLen
import all CslibFrontier.Computability.PolyTime.BooleanAnalysis.BoundedIncidenceStepCert
import all CslibFrontier.Computability.PolyTime.CNF.BranchedSparseCNFCounter
import CslibFrontier.Computability.Complexity.FineGrained.SparseBranchAsymptotics
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Fold
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List.Size
import CslibFrontier.Foundations.Data.List.Fold
import Mathlib.Data.List.GetD
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Native Resource Bounds for the Bounded-Incidence Branch Evaluator (Proposition 5.3)

This file establishes the native multi-tape Turing machine resource certificate, global polynomial
workspace bound across all raw `BranchEvalInput` tuples, and subexponential
$O^*(2^{O(\mathrm{interpolationScale}(n'))})$ runtime bound for the Proposition 5.3
bounded-incidence, bounded-width $\mathbb{F}_2$ polynomial-system branch evaluator
`evalBoundedIncidenceBranch` of [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH]
(§§3.4–3.5, §4.7, §§5.3–5.5, Proposition 5.3, and Appendix B.2–B.3, pp. 24–26, 34–35, 37–39,
48–50).

## Main definitions

* `Cslib.Complexity.SubexponentialSAT.SparsePolyCounter.boundedIncidenceBranchCertificate`:
  uniform `NativeCertificate` for `evalBoundedIncidenceBranch` on `encBranchEvalInput`.

## Main results

* `SparsePolyCounter.auxDim_lt_self_of_two_le`: `ReplacementParams.auxDim n' < n'` for `2 ≤ n'`.
* `SparsePolyCounter.polyBounded_boundedIncidenceBranchCertificate_space`: global `PolyBounded`
  workspace bound across all raw `BranchEvalInput` tuples.
* `SparsePolyCounter.exists_boundedIncidenceBranchCertificate_time_bound`: subexponential
  $O^*(2^{O(\mathrm{interpolationScale}(n'))})$ branch runtime bound on
  `prepareBranchEvalInput (n', sys')` under polylogarithmic factor incidence and scope width
  (Proposition 5.3, pp. 37–39).
* `SparsePolyCounter.branchPolylogTimeBound_boundedIncidenceBranchCertificate`: discharges
  `Cslib.Complexity.BranchedSparseCNFCounter.BranchPolylogTimeBound` for
  `boundedIncidenceBranchCertificate`.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], §§3.4–3.5, §4.7, §§5.3–5.5,
  Proposition 5.3, Appendix B.2–B.3.
-/

namespace Cslib.Complexity.SubexponentialSAT.SparsePolyCounter

open Finset Cslib Cslib.BitString Cslib.CommonCountingAccum Cslib.Complexity Cslib.GenericRAM
open Cslib.LinearAlgebra Turing.MultiTapeTM ComputableInPolyTime

local notation "PolyT" => ComputableInPolyTime
local notation "Cert" => NativeCertificate

/-! ### 1. Asymptotic Branch Step-Count Transfer to `interpolationScale` -/

/-- For `2 ≤ n'`, the Section 4.7 auxiliary dimension `auxDim n' = r ^ (2 * Q)` is strictly bounded
by `n'` itself (since `D ≤ 2 ^ (λ / 128) ≤ 2 ^ (λ - 1) < n'`). -/
public theorem auxDim_lt_self_of_two_le {n' : ℕ} (hn' : 2 ≤ n') :
    ReplacementParams.auxDim n' < n' := by
  have hlam1 : 1 ≤ Nat.clog 2 n' := (Nat.lt_clog_iff_pow_lt Nat.one_lt_two).mpr (by omega)
  have hpow_lt : 2 ^ (Nat.clog 2 n' - 1) < n' := (Nat.lt_clog_iff_pow_lt Nat.one_lt_two).mp
    (by omega)
  exact (ReplacementParams.auxDim_le_two_pow n').trans_lt
    ((Nat.pow_le_pow_right Nat.zero_lt_two (by omega)).trans_lt hpow_lt)

private theorem numGroups_pow_numNodes_le_self {n' : ℕ} (hn' : 2 ≤ n')
    (hr : 1 ≤ ReplacementParams.numGroups n') :
    ReplacementParams.numGroups n' ^ ReplacementParams.numNodes n' ≤ n' := by
  refine (?_ : _ ≤ ReplacementParams.auxDim n').trans (auxDim_lt_self_of_two_le hn').le
  unfold ReplacementParams.auxDim; exact Nat.pow_le_pow_right hr (by omega)

private theorem chooseBeta_le_succ_of_le_mul_clog_pow {n' b w β C_inc : ℕ}
    (hn4 : 4 ≤ n') (hnC : 2 ^ C_inc ≤ n')
    (hb : b ≤ C_inc * Nat.clog 2 n' ^ β) (hw : w ≤ C_inc * Nat.clog 2 n' ^ β) :
    1 ≤ ParameterCheck.chooseBeta (Nat.clog 2 n') b w ∧
      ParameterCheck.chooseBeta (Nat.clog 2 n') b w ≤ β + 1 := by
  set lam := Nat.clog 2 n'
  have hlam2 : 2 ≤ lam :=
    (Nat.clog_pow 2 2 Nat.one_lt_two).symm.trans_le (Nat.clog_mono_right 2 hn4)
  have hC : C_inc ≤ lam := (Nat.clog_pow 2 C_inc Nat.one_lt_two).symm.trans_le
    (Nat.clog_mono_right 2 hnC)
  have hb' : b ≤ lam ^ (β + 1) := by rw [pow_succ']; exact hb.trans (Nat.mul_le_mul_right _ hC)
  have hw' : w ≤ lam ^ (β + 1) := by rw [pow_succ']; exact hw.trans (Nat.mul_le_mul_right _ hC)
  obtain ⟨h1, _, _, hmin⟩ := ParameterCheck.chooseBeta_spec (b := b) (w := w) hlam2
  exact ⟨h1, by_contra fun hgt => hmin (β + 1) (Nat.succ_pos β) (Nat.lt_of_not_ge hgt) ⟨hb', hw'⟩⟩

private theorem step_prefactor_le {rQ Q r S M G L : ℕ} (hrQ : rQ ≤ L) (hQ : Q ≤ L) (hr2 : 2 ≤ r)
    (hrL : r ≤ L) (hS : 1 ≤ S) (hM : 1 ≤ M) (hG : 1 ≤ G) :
    (rQ + 1) + (Q + 1) * (S + 1) * (M + 1) * (r * (G + 1) + 1) ≤
      64 * (L + 1) ^ 3 * (S * M * G) := by
  have hE : 1 ≤ S * M * G := Nat.mul_pos (Nat.mul_pos hS hM) hG
  have hGp1 : r * (G + 1) + 1 ≤ 4 * (L + 1) * G :=
    ((Nat.add_le_add (Nat.mul_le_mul_left r (by omega : G + 1 ≤ 2 * G))
      (Nat.mul_pos (by omega : 0 < 2 * r) hG)).trans_eq (by ring)).trans
      (Nat.mul_le_mul_right G (Nat.mul_le_mul_left 4 (by omega)))
  have hprod4 : (Q + 1) * (S + 1) * (M + 1) * (r * (G + 1) + 1) ≤ 16 * (L + 1) ^ 2 * (S * M * G) :=
    (Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (by omega : Q + 1 ≤ L + 1)
      (by omega : S + 1 ≤ 2 * S)) (by omega : M + 1 ≤ 2 * M)) hGp1).trans_eq (by ring)
  have hL3 : L + 1 ≤ (L + 1) ^ 3 := by
    simpa only [pow_one] using Nat.pow_le_pow_right (Nat.succ_pos L) (by decide : 1 ≤ 3)
  have hL23 : (L + 1) ^ 2 ≤ (L + 1) ^ 3 := Nat.pow_le_pow_right (Nat.succ_pos L) (by decide : 2 ≤ 3)
  have hrQ_le := (Nat.succ_le_succ hrQ).trans (hL3.trans (Nat.le_mul_of_pos_right _ hE))
  exact ((Nat.add_le_add hrQ_le (hprod4.trans
    (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 16 hL23)))).trans_eq (by ring)).trans
    (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by decide : 17 ≤ 64)))

/-- Core subexponential step-count bound for Proposition 5.3: under `checkBranchFeasible`,
polylogarithmic `(b, w)` bounds, linear equation count `sys'.length ≤ C_inc * n'`, and degree
`sysMaxDegree sys' ≤ k_deg`, any parametric loop-product bound is dominated above
`max 16384 (2 ^ C_inc)` by a fixed polynomial in
`(encPair encUnary encSparseSystem (n', sys')).length`
times `2 ^ (A_br * interpolationScale n')`. -/
private theorem nat_pow_le_exp_of_le {b e : ℕ} {r u : ℝ}
    (hb : 1 ≤ (b : ℝ)) (he : (e : ℝ) ≤ r) (hu : Real.log b * r ≤ u) :
    ((b ^ e : ℕ) : ℝ) ≤ Real.exp u :=
  calc ((b ^ e : ℕ) : ℝ)
      = (b : ℝ) ^ (e : ℝ) := by rw [Nat.cast_pow, Real.rpow_natCast]
    _ ≤ (b : ℝ) ^ r := Real.rpow_le_rpow_of_exponent_le hb he
    _ = Real.exp (Real.log b * r) := Real.rpow_def_of_pos (zero_lt_one.trans_le hb) _
    _ ≤ Real.exp u := Real.exp_le_exp.mpr hu

private theorem parametric_branch_step_bound {N₀_branch k_deg β C_inc C_p d_p : ℕ}
    {T : ℕ × List (List (List ℕ)) → ℕ}
    (hT : ∀ n' sys', checkBranchFeasible N₀_branch (n', sys') = true → 16384 ≤ n' →
      let β' := ParameterCheck.chooseBeta (Nat.clog 2 n')
        (branchMaxFactorIncidence n' sys') (branchMaxFactorWidth n' sys')
      let r := ReplacementParams.numGroups n'; let Q := ReplacementParams.numNodes n'
      let R := ReplacementParams.rowBound β' n'
      let q := (sysMaxDegree sys' * (R - 1)) * (sys'.length + 2 * n') / max 1 Q
      ∃ c_meas d_max : ℕ, (c_meas : ℝ) ≤ 2 * ReplacementParams.tau n' * (n' : ℝ) ∧
        d_max ≤ 2 * n' / r ∧ T (n', sys') ≤ ((r ^ Q + 1) + (Q + 1) *
          (SubsetPairFold.subsetPairCount n' q + 1) * ((2 * r ^ (2 * Q) + 1) ^ c_meas + 1) *
            (r * (2 ^ d_max + 1) + 1)) *
          (C_p * ((encPair encUnary encSparseSystem (n', sys')).length + 1) ^ d_p)) :
    let c_deg := k_deg * (C_inc + 2); let A_br := 65792 * (c_deg + 4) * (β + 4)
    ∀ n' : ℕ, ∀ sys' : List (List (List ℕ)),
      checkBranchFeasible N₀_branch (n', sys') = true → max 16384 (2 ^ C_inc) ≤ n' →
      sysMaxDegree sys' ≤ k_deg → sys'.length ≤ C_inc * n' →
      branchMaxFactorIncidence n' sys' ≤ C_inc * Nat.clog 2 n' ^ β →
      branchMaxFactorWidth n' sys' ≤ C_inc * Nat.clog 2 n' ^ β →
      (T (n', sys') : ℝ) ≤
        ((64 * C_p : ℕ) : ℝ) *
            ((encPair encUnary encSparseSystem (n', sys')).length + 1 : ℝ) ^ (d_p + 3) *
          (2 : ℝ) ^ ((A_br : ℝ) * interpolationScale n') := by
  intro c_deg A_br n' sys' hfeas hn' hdeg hlen hb hw
  have hn16384 : 16384 ≤ n' := (le_max_left _ _).trans hn'
  have hnC : 2 ^ C_inc ≤ n' := (le_max_right _ _).trans hn'
  obtain ⟨_, _, _, hF⟩ := feasible_of_checkBranchFeasible hfeas
  set b := branchMaxFactorIncidence n' sys'; set w := branchMaxFactorWidth n' sys'
  set β' := ParameterCheck.chooseBeta (Nat.clog 2 n') b w
  set r := ReplacementParams.numGroups n'; set Q := ReplacementParams.numNodes n'
  set R := ReplacementParams.rowBound β' n'
  set q := (sysMaxDegree sys' * (R - 1)) * (sys'.length + 2 * n') / max 1 Q
  obtain ⟨_, hβ'_le⟩ := chooseBeta_le_succ_of_le_mul_clog_pow (by omega) hnC hb hw
  obtain ⟨c_meas, d_max, hc_meas, hd_max, hT_le⟩ := hT n' sys' hfeas hn16384
  have hr2 : 2 ≤ r := hF.two_le_numGroups; have hR32 : 32 ≤ R := hF.thirtyTwo_le_rowBound
  have hRQ6 : 6 * R ≤ Q := hF.six_mul_rowBound_le_numNodes; have hQ_pos : 1 ≤ Q := by omega
  have hvar_bal : 2 * Q * r ^ 2 ≤ n' := hF.var_balance
  have hQ_le_n : Q ≤ n' := (by omega : Q ≤ 2 * Q * 1).trans
    ((Nat.mul_le_mul_left _ (Nat.one_le_pow 2 r (by omega))).trans hvar_bal)
  have hr_le_n : r ≤ n' := by
    have hr_sq : r ≤ r ^ 2 := by
      simpa only [pow_one] using Nat.pow_le_pow_right (by omega) (by decide : 1 ≤ 2)
    exact (one_mul r).symm.le.trans ((Nat.mul_le_mul (by omega) hr_sq).trans hvar_bal)
  have hrQ_le_n : r ^ Q ≤ n' := numGroups_pow_numNodes_le_self (by omega) (by omega)
  have hn_le_enc : n' ≤ (encPair encUnary encSparseSystem (n', sys')).length := by enc_len
  generalize hL_eq : (encPair encUnary encSparseSystem (n', sys')).length = L at hn_le_enc hT_le ⊢
  set S_sp := Cslib.subsetPairCount n' q; set D := ReplacementParams.auxDim n'
  have hS_eq : SubsetPairFold.subsetPairCount n' q = S_sp := SubsetPairFold.subsetPairCount_eq n' q
  have hS_pos : 1 ≤ S_sp := hS_eq ▸ SubsetPairFold.subsetPairCount_pos n' q
  have hM_pos : 1 ≤ (2 * D + 1) ^ c_meas := Nat.one_le_pow _ _ (by omega)
  set E_nat := S_sp * (2 * D + 1) ^ c_meas * 2 ^ d_max
  have hstep_nat : (r ^ Q + 1) + (Q + 1) * (SubsetPairFold.subsetPairCount n' q + 1) *
      ((2 * r ^ (2 * Q) + 1) ^ c_meas + 1) * (r * (2 ^ d_max + 1) + 1) ≤
      64 * (L + 1) ^ 3 * E_nat := by
    rw [hS_eq, (rfl : r ^ (2 * Q) = D)]
    exact step_prefactor_le (hrQ_le_n.trans hn_le_enc) (hQ_le_n.trans hn_le_enc) hr2
      (hr_le_n.trans hn_le_enc) hS_pos hM_pos Nat.one_le_two_pow
  have hq_real : (q : ℝ) ≤ (c_deg : ℝ) * (n' : ℝ) * ((R : ℝ) / Q) := by
    have hmaxQ : max 1 Q = Q := Nat.max_eq_right hQ_pos
    have hnum : (sysMaxDegree sys' * (R - 1)) * (sys'.length + 2 * n') ≤ c_deg * n' * R :=
      (Nat.mul_le_mul (Nat.mul_le_mul hdeg (Nat.sub_le R 1))
        (by rw [Nat.add_mul]; omega : sys'.length + 2 * n' ≤ (C_inc + 2) * n')).trans_eq
        (by dsimp only [c_deg]; ring)
    have hq_le : q ≤ (c_deg * n' * R) / Q := by
      rw [show q = (sysMaxDegree sys' * (R - 1)) * (sys'.length + 2 * n') / Q by rw [← hmaxQ]]
      exact Nat.div_le_div_right hnum
    exact ((Nat.cast_le.mpr hq_le).trans Nat.cast_div_le).trans_eq (by push_cast; ring)
  have hS_exp := Cslib.ReplacementCounting.subsetPairCount_le_exp_mul_log_ratio
    (by omega : 1 ≤ R) (by omega : R ≤ Q) hq_real
  have h2le_cdeg : (2 : ℝ) ≤ (c_deg : ℝ) + 4 :=
    (zero_add (2 : ℝ)).symm.le.trans (add_le_add (Nat.cast_nonneg c_deg) (by norm_num))
  have hM_exp : (((2 * D + 1) ^ c_meas : ℕ) : ℝ) ≤
      Real.exp (((c_deg : ℝ) + 4) * (n' : ℝ) *
        (ReplacementParams.tau n' * Real.log (2 * (D : ℝ) + 1))) := by
    have hlog_nn : 0 ≤ Real.log ((2 * D + 1 : ℕ) : ℝ) := Real.log_nonneg (by push_cast; linarith)
    have htau_nn : 0 ≤ ReplacementParams.tau n' := hF.tau_pos.le
    refine nat_pow_le_exp_of_le (by push_cast; linarith) hc_meas ?_
    calc Real.log ↑(2 * D + 1) * (2 * ReplacementParams.tau n' * ↑n')
        = 2 * (↑n' * (ReplacementParams.tau n' * Real.log ↑(2 * D + 1))) := by ring
      _ ≤ ((c_deg : ℝ) + 4) * (↑n' * (ReplacementParams.tau n' * Real.log ↑(2 * D + 1))) :=
          mul_le_mul_of_nonneg_right h2le_cdeg
            (mul_nonneg (Nat.cast_nonneg n') (mul_nonneg htau_nn hlog_nn))
      _ = ((c_deg : ℝ) + 4) * (n' : ℝ) *
            (ReplacementParams.tau n' * Real.log (2 * (D : ℝ) + 1)) := by push_cast; ring
  have hG_exp : ((2 ^ d_max : ℕ) : ℝ) ≤
      Real.exp (((c_deg : ℝ) + 4) * (n' : ℝ) * (1 / (r : ℝ))) := by
    have hr_pos : (0 : ℝ) < r := Nat.cast_pos.mpr (by omega)
    have hd_real : (d_max : ℝ) ≤ 2 * (n' : ℝ) / r :=
      ((Nat.cast_le.mpr hd_max).trans (Nat.cast_div_le (α := ℝ))).trans_eq (by push_cast; ring)
    refine nat_pow_le_exp_of_le (by norm_num) hd_real ?_
    have h2le : 2 * Real.log 2 ≤ (c_deg : ℝ) + 4 :=
      (mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos zero_lt_two) zero_le_two).trans
        ((by norm_num : (2 : ℝ) * (2 - 1) ≤ 2).trans h2le_cdeg)
    calc Real.log ↑2 * (2 * (n' : ℝ) / r)
        = (2 * Real.log 2) * ((n' : ℝ) * (1 / (r : ℝ))) := by ring
      _ ≤ ((c_deg : ℝ) + 4) * ((n' : ℝ) * (1 / (r : ℝ))) :=
          mul_le_mul_of_nonneg_right h2le (by positivity)
      _ = ((c_deg : ℝ) + 4) * (n' : ℝ) * (1 / (r : ℝ)) := by ring
  have hE_exp : (E_nat : ℝ) ≤
      Real.exp (((c_deg : ℝ) + 4) * (n' : ℝ) * ReplacementParams.rowCost β' n') := by
    have hcast : (E_nat : ℝ) =
        (S_sp : ℝ) * (((2 * D + 1) ^ c_meas : ℕ) : ℝ) * ((2 ^ d_max : ℕ) : ℝ) := by
      simp only [E_nat, Nat.cast_mul]
    rw [hcast, ← ReplacementParams.threeTermExponent_eq_rowCost β' n']
    refine (mul_le_mul (mul_le_mul hS_exp hM_exp (by positivity) (by positivity))
      hG_exp (by positivity) (by positivity)).trans_eq ?_
    rw [← Real.exp_add, ← Real.exp_add]; apply congrArg Real.exp
    unfold Cslib.ReplacementCounting.threeTermExponent; ring
  have hscale_nn : 0 ≤ interpolationScale n' :=
    (by positivity : (0 : ℝ) ≤ 2 * (Q : ℝ) * (r : ℝ)).trans
    (ReplacementParams.two_mul_numNodes_mul_numGroups_le_interpolationScale hn16384 le_rfl)
  have hrc := hF.mul_rowCost_le_interpolationScale hn16384 (by omega) le_rfl
  have hexp_bound : ((c_deg : ℝ) + 4) * (n' : ℝ) * ReplacementParams.rowCost β' n' ≤
      (32896 * (c_deg + 4) * (β + 4) : ℕ) * interpolationScale n' := by
    have hβ_le : 32896 * ((β' : ℝ) + 3) * interpolationScale n' ≤
        32896 * ((β : ℝ) + 4) * interpolationScale n' :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (by exact_mod_cast (by omega : β' + 3 ≤ β + 4)) (by positivity)) hscale_nn
    rw [mul_assoc]; exact (mul_le_mul_of_nonneg_left (hrc.trans hβ_le)
      (by positivity)).trans_eq (by push_cast; ring)
  have hE_pow2 : (E_nat : ℝ) ≤ (2 : ℝ) ^ ((A_br : ℝ) * interpolationScale n') := by
    have hexp_nn : 0 ≤ ((32896 * (c_deg + 4) * (β + 4) : ℕ) : ℝ) * interpolationScale n' :=
      mul_nonneg (Nat.cast_nonneg _) hscale_nn
    exact (hE_exp.trans (Real.exp_le_exp.mpr hexp_bound)).trans
      ((exp_le_two_rpow_two_mul hexp_nn).trans_eq
        (congrArg ((2 : ℝ) ^ ·) (by simp only [A_br]; push_cast; ring)))
  have hT_nat : T (n', sys') ≤ (64 * C_p * (L + 1) ^ (d_p + 3)) * E_nat :=
    (hT_le.trans (Nat.mul_le_mul_right _ hstep_nat)).trans_eq (by ring)
  calc (T (n', sys') : ℝ)
      ≤ (((64 * C_p * (L + 1) ^ (d_p + 3)) * E_nat : ℕ) : ℝ) := Nat.cast_le.mpr hT_nat
    _ = ((64 * C_p : ℕ) : ℝ) * (L + 1 : ℝ) ^ (d_p + 3) * (E_nat : ℝ) := by push_cast; ring
    _ ≤ ((64 * C_p : ℕ) : ℝ) * (L + 1 : ℝ) ^ (d_p + 3) *
          (2 : ℝ) ^ ((A_br : ℝ) * interpolationScale n') :=
        mul_le_mul_of_nonneg_left hE_pow2 (by positivity)

/-! ### 2. Outer Loop Certificates and Global Polynomial Workspace -/

section LoopCertificates

private theorem poly_apply_le {α : Type} {f Lfn : α → ℕ} {c d L : ℕ}
    (hf : ∀ a, f a ≤ c * (Lfn a + 1) ^ d) {a : α} (hla : Lfn a ≤ L) :
    f a ≤ c * (L + 1) ^ d :=
  (hf a).trans (Nat.mul_le_mul_left c (Nat.pow_le_pow_left (Nat.add_le_add_right hla 1) d))

private theorem hasPolySpace_branch {α β : Type} {eα : α ↪ List Bool} {eβ : β ↪ List Bool}
    {p : α → Bool} {t e : α → β}
    {cp : Cert p eα encBool} {ct : Cert t eα eβ} {ce : Cert e eα eβ}
    (hcp : HasPolySpace cp) (hct : HasPolySpace ct) (hce : HasPolySpace ce) :
    HasPolySpace (NativeCertificate.branch cp ct ce) :=
  (hcp.add (hct.add hce)).mono fun a => by
    simp only [NativeCertificate.branch_space]; split_ifs <;> omega

private theorem polyBounded_option_elim {α β : Type}
    {eα : α ↪ List Bool} {eβ : β ↪ List Bool}
    {f : α → Option β} {gNone : α → ℕ} {gSome : α × β → ℕ}
    (hf_len : PolyBounded (fun a => (eα a).length) (fun a => (encOption eβ (f a)).length))
    (hgNone : PolyBounded (fun a => (eα a).length) gNone)
    (hgSome : PolyBounded (fun p => (encPair eα eβ p).length) gSome) :
    PolyBounded (fun a => (eα a).length)
      (fun a => (f a).elim (gNone a) (fun b => gSome (a, b))) := by
  have hlenIY : PolyBounded (fun a => (eα a).length)
      (fun a => 2 * (eα a).length + 2 * (encOption eβ (f a)).length + 1) :=
    (((PolyBounded.const 2).mul .self).add ((PolyBounded.const 2).mul hf_len)).add (.const 1)
  obtain ⟨c, d, hcd⟩ := hgSome.exists_le
  refine (hgNone.add (NativeCertificate.polyBounded_pow_of_polyBounded hlenIY c d)).mono
    fun a => ?_
  cases h : f a with
  | none => exact Nat.le_add_right _ _
  | some b =>
    have hiy : (encPair eα eβ (a, b)).length ≤
        2 * (eα a).length + 2 * (encOption eβ (some b)).length + 1 := by enc_len
    exact (poly_apply_le hcd hiy).trans (Nat.le_add_left _ (gNone a))

private theorem computableInPolyTime_ctxAddJet
    {α Ctx : Type} {eα : α ↪ List Bool} {eCtx : Ctx ↪ List Bool}
    {J ℓ : Ctx → ℕ} (hJ : PolyT J eCtx encUnary) (hℓ : PolyT ℓ eCtx encUnary) :
    PolyT (fun q : (α × (Ctx × JetRows)) × JetRows =>
      (q.1.2.1, addJet (J q.1.2.1) (ℓ q.1.2.1) q.1.2.2 q.2))
      (encPair (encPair eα (encPair eCtx encJet)) encJet) (encPair eCtx encJet) := by
  have hq1 := fst (encPair eα (encPair eCtx encJet)) encJet
  have hq2 := snd (encPair eα (encPair eCtx encJet)) encJet
  have hctx := hq1.snd'.fst'
  exact hctx.prod (computableInPolyTime_addJet (hJ.comp hctx) (hℓ.comp hctx) hq1.snd'.snd' hq2)

private theorem jetFoldl_bound_mono {J ℓ N M bN : ℕ} (hN : N.size ≤ bN) :
    J * (2 * (ℓ * (2 * (N.size + (2 ^ M).size) + 3)) + 1) ≤
      J * (2 * (ℓ * (2 * (bN + (M + 1)) + 3)) + 1) := by
  have hM : (2 ^ M).size ≤ M + 1 := by rw [Nat.size_pow]
  exact Nat.mul_le_mul_left _ (Nat.add_le_add_right (Nat.mul_le_mul_left 2
    (Nat.mul_le_mul_left _ (Nat.add_le_add_right (Nat.mul_le_mul_left 2
      (Nat.add_le_add hN hM)) 3))) 1)

private theorem mul_inner_add_absorb {A B p q ov r : ℕ}
    (hA : 1 ≤ A) (hB : 1 ≤ B) (hr : p + q + ov ≤ r) :
    A * (B * p + q) + ov ≤ A * B * r := by
  have hAB : 1 ≤ A * B := Nat.mul_pos hA hB
  calc A * (B * p + q) + ov
      ≤ A * (B * (p + q)) + A * B * ov :=
        Nat.add_le_add (Nat.mul_le_mul_left A (absorb_step_add B p q hB))
          (Nat.le_mul_of_pos_left ov hAB)
    _ = A * B * (p + q + ov) := by ring
    _ ≤ A * B * r := Nat.mul_le_mul_left _ hr

private def evalSignedMeasJet (dc : SubsetPairFold.DecodedPair × SubsetStepCtx) : JetRows :=
  let measCtx : MeasStepCtx :=
    (dc.2.1, dc.2.2.2.1, dc.2.2.2.2.1, dc.2.2.2.2.2.1, (dc.1.1, dc.1.2.1), dc.2.2.2.2.2.2)
  let measJet := (MeasurementFold.run measurementStepBody dc.2.2.1
    (measCtx, zeroJet dc.2.jetOrder dc.2.precision)).2.2.2
  if dc.1.2.2 then smulJet dc.2.jetOrder dc.2.precision (-1) measJet else measJet

private theorem subsetPairStepBody_eq
    (inp : SubsetPairFold.DecodedPair × (SubsetStepCtx × JetRows)) :
    subsetPairStepBody inp = (inp.2.1, addJet inp.2.1.jetOrder inp.2.1.precision inp.2.2
      (evalSignedMeasJet (inp.1, inp.2.1))) := rfl

private theorem exists_computableInO_signedMeasJet :
    ∃ P : SubsetPairFold.DecodedPair × SubsetStepCtx → ℕ,
      PolyBounded (fun dc => (encPair SubsetPairFold.encDecodedPair encSubsetStepCtx dc).length) P ∧
      ComputableInO evalSignedMeasJet
        (encPair SubsetPairFold.encDecodedPair encSubsetStepCtx) encJet
        (fun dc => ((2 * dc.2.2.1.2 + 1) ^ dc.2.2.1.1 + 1) *
          (dc.2.numGroups * (2 ^ maxGroupDim dc.2.numVars dc.2.numGroups dc.2.varGroups + 1) + 1) *
            P dc)
        P := by
  obtain ⟨P₁, hP₁_pb, hPay⟩ := exists_computableInO_measPayload
  let eWC : List ℤ × MeasStepCtx ↪ List Bool := encPair (encList encIntBin) encMeasStepCtx
  let cPay : Cert evalMeasPayload eWC (encOption encJet) := ⟨_, P₁, hPay⟩
  let eAcc : MeasStepCtx × JetRows ↪ List Bool := encPair encMeasStepCtx encJet
  let eMIn : ((ℕ × ℕ) × List ℤ) × (MeasStepCtx × JetRows) ↪ List Bool :=
    encPair (encPair (encPair encUnary encNat) (encList encIntBin)) eAcc
  have hprojWC : PolyT
      (fun inp : ((ℕ × ℕ) × List ℤ) × (MeasStepCtx × JetRows) => (inp.1.2, inp.2.1)) eMIn eWC :=
    (fst _ eAcc).snd'.prod (snd _ eAcc).fst'
  have haddM : PolyT
      (fun q : (((ℕ × ℕ) × List ℤ) × (MeasStepCtx × JetRows)) × JetRows =>
        (q.1.2.1, addJet q.1.2.1.jetOrder q.1.2.1.precision q.1.2.2 q.2))
      (encPair eMIn encJet) eAcc :=
    computableInPolyTime_ctxAddJet (J := MeasStepCtx.jetOrder) (ℓ := MeasStepCtx.precision)
      (by unfold encMeasStepCtx; exact (snd _ _).fst'.fst')
      (by unfold encMeasStepCtx; exact (snd _ _).fst'.snd'.fst')
  let cProjWC := NativeCertificate.ofPolyTime hprojWC
  let cAddM := NativeCertificate.ofPolyTime haddM
  have hcProjWC : cProjWC.IsPolynomial := NativeCertificate.ofPolyTime_isPolynomial hprojWC
  have hcAddM : cAddM.IsPolynomial := NativeCertificate.ofPolyTime_isPolynomial haddM
  clear_value cProjWC cAddM
  let cNoM := NativeCertificate.snd
    (NativeCertificate.linear (ei := eMIn) (ComputableInO.of_eq fun _ => rfl))
  let cValM := cPay.comp cProjWC; let cbM₀ := NativeCertificate.option cValM cNoM cAddM
  have hcValM_sp : HasPolySpace cValM := hasPolySpace_comp hP₁_pb hcProjWC.2
  have hcNoM_sp : PolyBounded (fun inp => (eMIn inp).length) cNoM.space :=
    ((PolyBounded.const 2).mul .self).mono fun inp => by
      dsimp only [cNoM]; simp only [NativeCertificate.snd_space, NativeCertificate.linear_space]
      omega
  have hcNoM_t : PolyBounded (fun inp => (eMIn inp).length) cNoM.time :=
    ((PolyBounded.const 2).mul .self).mono fun inp => by
      dsimp only [cNoM]; simp only [NativeCertificate.snd_time, NativeCertificate.linear_time]
      omega
  have hcbM_sp : HasPolySpace cbM₀ :=
    (((((PolyBounded.const 2).mul hcValM_sp).add .self).add
      (polyBounded_option_elim (polyBounded_length_of_hasPolySpace hcValM_sp) hcNoM_sp
        hcAddM.2))).mono fun inp => by
      simp only [cbM₀, cValM, NativeCertificate.option_space, Function.comp_apply]; exact le_rfl
  let cbM : Cert measurementStepBody eMIn eAcc :=
    ⟨cbM₀.time, cbM₀.space,
      cbM₀.computes.of_enc_eq fun inp => congrArg eAcc (measurementStepBody_eq inp)⟩
  let cVisit := MeasurementFold.visitCertificate cbM
  have hcPrep := NativeCertificate.ofPolyTime_isPolynomial
    (MeasurementFold.prepare_polyTime (encB := eAcc))
  have hcVisit_sp : HasPolySpace cVisit :=
    hasPolySpace_prod .self (hasPolySpace_comp hcbM_sp hcPrep.2)
  have hovM_pb : PolyBounded (fun inp => (eMIn inp).length)
      (fun inp => 2 * cProjWC.time inp + (eMIn inp).length +
        (evalMeasPayload (inp.1.2, inp.2.1)).elim (cNoM.time inp)
          (fun b => cAddM.time (inp, b))) :=
    (((PolyBounded.const 2).mul hcProjWC.1).add .self).add
      (polyBounded_option_elim (polyBounded_length_of_hasPolySpace hcValM_sp) hcNoM_t hcAddM.1)
  let eSt := encPair encNat (encPair (encPair encUnary encNat) eAcc)
  have hovV_pb := (PolyBounded.self.add hcPrep.1).add
    (hovM_pb.comp (MeasurementFold.prepare_polyTime (encB := eAcc)).polyBounded_length)
  obtain ⟨cv, dv, hv_le⟩ := hovV_pb.exists_le
  let eDC := encPair SubsetPairFold.encDecodedPair encSubsetStepCtx
  let mkMCtx (dc : SubsetPairFold.DecodedPair × SubsetStepCtx) : MeasStepCtx :=
    (dc.2.1, dc.2.2.2.1, dc.2.2.2.2.1, dc.2.2.2.2.2.1, (dc.1.1, dc.1.2.1), dc.2.2.2.2.2.2)
  have hmkMCtx : PolyT mkMCtx eDC encMeasStepCtx := by
    have hdc1 := fst SubsetPairFold.encDecodedPair encSubsetStepCtx
    have hdc2 := snd SubsetPairFold.encDecodedPair encSubsetStepCtx
    unfold SubsetPairFold.encDecodedPair encSubsetStepCtx at hdc1 hdc2
    dsimp only [eDC]; unfold encMeasStepCtx mkMCtx
    exact hdc2.fst'.prod (hdc2.snd'.snd'.fst'.prod (hdc2.snd'.snd'.snd'.fst'.prod
      (hdc2.snd'.snd'.snd'.snd'.fst'.prod ((hdc1.fst'.prod hdc1.snd'.fst').prod
        hdc2.snd'.snd'.snd'.snd'.snd'))))
  have hparDC : PolyT (fun dc : _ × SubsetStepCtx => dc.2.2.1) eDC
      (encPair encUnary encNat) := by
    unfold eDC encSubsetStepCtx; exact (snd _ _).snd'.fst'
  have hJ_dc : PolyT (fun dc : _ × SubsetStepCtx => dc.2.jetOrder) eDC encUnary := by
    unfold eDC encSubsetStepCtx; exact (snd _ _).snd'.snd'.fst'.fst'
  have hℓ_dc : PolyT (fun dc : _ × SubsetStepCtx => dc.2.precision) eDC encUnary := by
    unfold eDC encSubsetStepCtx; exact (snd _ _).snd'.snd'.fst'.snd'.fst'
  have hinitDC := hparDC.prod (hmkMCtx.prod (computableInPolyTime_zeroJet hJ_dc hℓ_dc))
  have hc_pb := ((fst encUnary encNat).comp hparDC).polyBounded
  have hDsz_pb : PolyBounded (fun dc => (eDC dc).length) (fun dc => (dc.2.2.1.2).size) :=
    (((snd encUnary encNat).comp hparDC).polyBounded_length).mono
      fun dc => by simp only [Function.comp_apply, encNat_apply, Nat.size_eq_bits_len]; exact le_rfl
  let L_wc (dc : SubsetPairFold.DecodedPair × SubsetStepCtx) :=
    2 * (dc.2.2.1.1 * (2 * ((dc.2.2.1.2).size + 1) + 1)) +
      2 * (encMeasStepCtx (mkMCtx dc)).length + 1
  have hLwc_pb : PolyBounded (fun dc => (eDC dc).length) L_wc :=
    (((PolyBounded.const 2).mul (hc_pb.mul (((PolyBounded.const 2).mul
      (hDsz_pb.add (.const 1))).add (.const 1)))).add
      ((PolyBounded.const 2).mul hmkMCtx.polyBounded_length)).add (.const 1)
  obtain ⟨cp1, dp1, hp1_le⟩ := hP₁_pb.exists_le
  obtain ⟨co1, do1, ho1_le⟩ := (polyBounded_length_of_hasPolySpace (c := cPay) hP₁_pb).exists_le
  let P_pay (dc : SubsetPairFold.DecodedPair × SubsetStepCtx) := cp1 * (L_wc dc + 1) ^ dp1
  have hPpay_pb := NativeCertificate.polyBounded_pow_of_polyBounded hLwc_pb cp1 dp1
  let L_opt (dc : SubsetPairFold.DecodedPair × SubsetStepCtx) := co1 * (L_wc dc + 1) ^ do1
  have hLopt_pb := NativeCertificate.polyBounded_pow_of_polyBounded hLwc_pb co1 do1
  let B_jet (dc : SubsetPairFold.DecodedPair × SubsetStepCtx) :=
    dc.2.jetOrder * (2 * (dc.2.precision *
    (2 * ((dc.2.2.1.1 * ((dc.2.2.1.2).size + 1) + 1) + (L_opt dc + 1)) + 3)) + 1)
  have hBjet_pb : PolyBounded (fun dc => (eDC dc).length) B_jet :=
    hJ_dc.polyBounded.mul (((PolyBounded.const 2).mul (hℓ_dc.polyBounded.mul
      (((PolyBounded.const 2).mul (((hc_pb.mul (hDsz_pb.add (.const 1))).add (.const 1)).add
        (hLopt_pb.add (.const 1)))).add (.const 3)))).add (.const 1))
  let B_outer (dc : SubsetPairFold.DecodedPair × SubsetStepCtx) :=
    2 * (encPair encUnary encNat dc.2.2.1).length +
      2 * (2 * (encMeasStepCtx (mkMCtx dc)).length + 2 * B_jet dc + 1) + 1
  have hBout_pb : PolyBounded (fun dc => (eDC dc).length) B_outer :=
    (((PolyBounded.const 2).mul hparDC.polyBounded_length).add ((PolyBounded.const 2).mul
      ((((PolyBounded.const 2).mul hmkMCtx.polyBounded_length).add
        ((PolyBounded.const 2).mul hBjet_pb)).add (.const 1)))).add (.const 1)
  have hrun_eq (dc : SubsetPairFold.DecodedPair × SubsetStepCtx) (j : ℕ) :
      (IndexFold.run (MeasurementFold.visit measurementStepBody) j
        (dc.2.2.1, (mkMCtx dc, zeroJet dc.2.jetOrder dc.2.precision))).2 =
      (dc.2.2.1, (mkMCtx dc, (List.range j).foldl
        (fun acc i => (evalMeasPayload
          (Cslib.Radix.measurementValues dc.2.2.1.1 dc.2.2.1.2 i, mkMCtx dc)).elim acc
          (fun y => addJet dc.2.jetOrder dc.2.precision acc y))
        (zeroJet dc.2.jetOrder dc.2.precision))) := by
    refine Prod.ext (MeasurementFold.prefix_parameters _ _ _ _) ?_
    rw [show (IndexFold.run (MeasurementFold.visit measurementStepBody) j
        (dc.2.2.1, (mkMCtx dc, zeroJet dc.2.jetOrder dc.2.precision))).2.2 =
        (MeasurementFold.runPrefix measurementStepBody dc.2.2.1 j
          (mkMCtx dc, zeroJet dc.2.jetOrder dc.2.precision)).2.2 from rfl,
      MeasurementFold.prefix_accumulator]
    simp only [measurementStepBody_eq]
    have hfn : (fun (acc : MeasStepCtx × JetRows) (i : ℕ) =>
        (evalMeasPayload (Cslib.Radix.measurementValues dc.2.2.1.1 dc.2.2.1.2 i, acc.1)).elim acc
          fun y => (acc.1, addJet acc.1.2.1.1 acc.1.2.1.2.1 acc.2 y)) =
      fun pa i => (pa.1,
        (evalMeasPayload (Cslib.Radix.measurementValues dc.2.2.1.1 dc.2.2.1.2 i, pa.1)).elim pa.2
          fun y => addJet pa.1.2.1.1 pa.1.2.1.2.1 pa.2 y) := by
      funext pa i; cases evalMeasPayload _ <;> rfl
    rw [hfn]; exact List.foldl_keep_fst
      (fun (m : MeasStepCtx) (acc : JetRows) (i : ℕ) =>
        (evalMeasPayload (Cslib.Radix.measurementValues dc.2.2.1.1 dc.2.2.1.2 i, m)).elim acc
          (fun y => addJet m.2.1.1 m.2.1.2.1 acc y))
      (mkMCtx dc) (List.range j) (zeroJet dc.2.jetOrder dc.2.precision)
  have hB : ∀ dc j, j ≤ MeasurementFold.count dc.2.2.1 →
      (encPair (encPair encUnary encNat) eAcc
        (IndexFold.run (MeasurementFold.visit measurementStepBody) j
          (dc.2.2.1, (mkMCtx dc, zeroJet dc.2.jetOrder dc.2.precision))).2).length ≤
        B_outer dc := by
    intro dc j hj; rw [hrun_eq dc j]
    have hf_le := length_encJetRows_foldl_optAddJet_le (J := dc.2.jetOrder) (ℓ := dc.2.precision)
      (N := MeasurementFold.count dc.2.2.1) (M := 2 ^ L_opt dc)
      (f := fun i => evalMeasPayload
        (Cslib.Radix.measurementValues dc.2.2.1.1 dc.2.2.1.2 i, mkMCtx dc))
      hj fun i _ y hy j' _ u' _ => by
        have hw_len := MeasurementFold.length_values_le dc.2.2.1.1 dc.2.2.1.2 i
        have hwc_len : (eWC (Cslib.Radix.measurementValues dc.2.2.1.1 dc.2.2.1.2 i,
            mkMCtx dc)).length ≤ L_wc dc := by enc_len [eWC, L_wc]
        have hopt_len : (encOption encJet (some y)).length ≤ L_opt dc := by
          rw [← hy]; exact poly_apply_le ho1_le hwc_len
        have hy_len : (encJet y).length ≤ L_opt dc := by
          simp only [encOption_some, List.length_cons] at hopt_len; omega
        exact (Nat.size_le.mp ((CommonCountingAccum.size_natAbs_rowEntry_le_length_encJetRows y j'
          u').trans hy_len)).le
    have hN_sz : (MeasurementFold.count dc.2.2.1).size ≤
        dc.2.2.1.1 * ((dc.2.2.1.2).size + 1) + 1 := by
      rw [← Nat.size_eq_bits_len, ← encNat_apply]; exact MeasurementFold.length_count_le _ _
    have hjet_le : (encJet ((List.range j).foldl
        (fun acc i => (evalMeasPayload
          (Cslib.Radix.measurementValues dc.2.2.1.1 dc.2.2.1.2 i, mkMCtx dc)).elim acc
          (fun y => addJet dc.2.jetOrder dc.2.precision acc y))
        (zeroJet dc.2.jetOrder dc.2.precision))).length ≤ B_jet dc :=
      hf_le.trans (jetFoldl_bound_mono hN_sz)
    dsimp only [eAcc]
    rw [length_encPair (enc₁ := encPair encUnary encNat), length_encPair (enc₁ := encMeasStepCtx)]
    refine le_trans (Nat.add_le_add_left (Nat.add_le_add_left hjet_le _) _) ?_
    dsimp only [B_outer]; omega
  let cCnt := MeasurementFold.clock.comp (.ofPolyTime hparDC)
  have hcCnt := NativeCertificate.comp_isPolynomial _ _ MeasurementFold.clock_isPolynomial
    (NativeCertificate.ofPolyTime_isPolynomial hparDC)
  let S_st (dc : SubsetPairFold.DecodedPair × SubsetStepCtx) :=
    2 * (encNat (MeasurementFold.count dc.2.2.1)).length + 1 + B_outer dc
  have hSst_pb := (((PolyBounded.const 2).mul (cCnt.polyTime hcCnt).polyBounded_length).add
    (.const 1)).add hBout_pb
  let P_cb (dc : SubsetPairFold.DecodedPair × SubsetStepCtx) := cv * (S_st dc + 1) ^ dv
  have hPcb_pb := NativeCertificate.polyBounded_pow_of_polyBounded hSst_pb cv dv
  obtain ⟨P_loop, hPloop_pb, hloop⟩ := computableInO_snd_indexFold cCnt (.ofPolyTime hinitDC)
    cVisit hcCnt (NativeCertificate.ofPolyTime_isPolynomial hinitDC) hcVisit_sp hBout_pb hB
    (fun dc =>
      (dc.2.numGroups * (2 ^ maxGroupDim dc.2.numVars dc.2.numGroups dc.2.varGroups + 1) + 1) *
        (2 * P_pay dc)) P_cb hPcb_pb fun dc j hj hst_len => by
      set st := IndexFold.run (MeasurementFold.visit measurementStepBody) j
        (dc.2.2.1, (mkMCtx dc, zeroJet dc.2.jetOrder dc.2.precision))
      have hov := poly_apply_le hv_le hst_len
      have hw_len := MeasurementFold.length_values_le dc.2.2.1.1 dc.2.2.1.2 j
      have hwc_eq : (Cslib.Radix.measurementValues st.2.1.1 st.2.1.2 st.1, st.2.2.1) =
          (Cslib.Radix.measurementValues dc.2.2.1.1 dc.2.2.1.2 j, mkMCtx dc) := by
        rw [IndexFold.run_index, hrun_eq dc j]
      have hwc_len : (eWC (Cslib.Radix.measurementValues dc.2.2.1.1 dc.2.2.1.2 j,
          mkMCtx dc)).length ≤ L_wc dc := by enc_len [eWC, L_wc]
      have hpay_t : 2 * cPay.time (Cslib.Radix.measurementValues st.2.1.1 st.2.1.2 st.1, st.2.2.1) ≤
          (dc.2.numGroups * (2 ^ maxGroupDim dc.2.numVars dc.2.numGroups dc.2.varGroups + 1) + 1) *
            (2 * P_pay dc) := by
        rw [hwc_eq]
        exact (Nat.mul_le_mul_left 2
          (Nat.mul_le_mul_left _ (poly_apply_le hp1_le hwc_len))).trans_eq (by ring)
      dsimp only [cVisit, MeasurementFold.visitCertificate, cbM, cbM₀, cValM, eSt] at hov ⊢
      simp only [NativeCertificate.prod_time, NativeCertificate.comp_time,
        NativeCertificate.linear_time, NativeCertificate.option_time, Function.comp_apply] at hov ⊢
      exact le_trans (le_of_eq (by ring)) (Nat.add_le_add hpay_t hov)
  let cMeasJet := NativeCertificate.snd (NativeCertificate.snd
    (⟨_, _, hloop⟩ : Cert _ eDC (encPair (encPair encUnary encNat) eAcc)))
  have hsign : PolyT
      (fun p : (SubsetPairFold.DecodedPair × SubsetStepCtx) × JetRows =>
        if p.1.1.2.2 then smulJet p.1.2.jetOrder p.1.2.precision (-1) p.2 else p.2)
      (encPair eDC encJet) encJet := by
    have hp1 := fst eDC encJet; have hp2 := snd eDC encJet
    have hodd : PolyT (fun p : _ × JetRows => p.1.1.2.2) (encPair eDC encJet) encBool := by
      unfold eDC SubsetPairFold.encDecodedPair; exact hp1.fst'.snd'.snd'
    exact hodd.ite' (computableInPolyTime_smulJet (hJ_dc.comp hp1)
      (hℓ_dc.comp hp1) (const (-1)) hp2) hp2
  let cSign := NativeCertificate.ofPolyTime hsign
  have hcSign : cSign.IsPolynomial := NativeCertificate.ofPolyTime_isPolynomial hsign
  clear_value cSign
  let cIdDC := NativeCertificate.linear (ei := eDC) (ComputableInO.of_eq fun _ => rfl)
  let cFinal := cSign.comp (cIdDC.prod cMeasJet)
  have hspDCM : HasPolySpace (cIdDC.prod cMeasJet) := hasPolySpace_prod .self hPloop_pb
  let measFn (dc : SubsetPairFold.DecodedPair × SubsetStepCtx) : JetRows :=
    (MeasurementFold.run measurementStepBody dc.2.2.1
      (mkMCtx dc, zeroJet dc.2.jetOrder dc.2.precision)).2.2.2
  let P_out (dc : SubsetPairFold.DecodedPair × SubsetStepCtx) :=
    2 * P_pay dc + P_loop dc + (eDC dc).length + cSign.time (dc, measFn dc) + cFinal.space dc
  have hPout_pb : PolyBounded (fun dc => (eDC dc).length) P_out :=
    (((((PolyBounded.const 2).mul hPpay_pb).add hPloop_pb).add .self).add
      (hcSign.1.comp (polyBounded_length_of_hasPolySpace hspDCM))).add
      (hasPolySpace_comp hcSign.2 hspDCM)
  clear_value L_wc P_pay L_opt B_jet B_outer S_st P_cb cVisit cCnt
  refine ⟨P_out, hPout_pb, (cFinal.computes.of_enc_eq fun _ => rfl).mono_le (fun dc => ?_)
    fun dc => Nat.le_add_left _ _⟩
  set M_cnt := (2 * dc.2.2.1.2 + 1) ^ dc.2.2.1.1 + 1
  set G_cnt := dc.2.numGroups * (2 ^ maxGroupDim dc.2.numVars dc.2.numGroups dc.2.varGroups + 1) + 1
  have hcnt_eq : MeasurementFold.count dc.2.2.1 + 1 = M_cnt := rfl
  let ovDC := (eDC dc).length + cSign.time (dc, measFn dc)
  have hstep := mul_inner_add_absorb (A := M_cnt) (B := G_cnt) (Nat.succ_pos _) (Nat.succ_pos _)
    (by dsimp only [ovDC, P_out]; omega : 2 * P_pay dc + P_loop dc + ovDC ≤ P_out dc)
  dsimp only [cFinal, cIdDC, cMeasJet]
  simp only [NativeCertificate.comp_time, NativeCertificate.prod_time, NativeCertificate.snd_time,
    NativeCertificate.linear_time, Function.comp_apply, hcnt_eq]
  change (eDC dc).length + M_cnt * (G_cnt * (2 * P_pay dc) + P_loop dc) +
      cSign.time (dc, measFn dc) ≤ M_cnt * G_cnt * P_out dc
  exact (by dsimp only [ovDC]; omega : _ ≤
    M_cnt * (G_cnt * (2 * P_pay dc) + P_loop dc) + ovDC).trans hstep

private theorem exists_computableInO_nodeJet :
    ∃ P : ℕ × SubsetStepCtx → ℕ,
      PolyBounded (fun qs => (encPair encUnary encSubsetStepCtx qs).length) P ∧
      ComputableInO
        (fun qs : ℕ × SubsetStepCtx =>
          (SubsetPairFold.run subsetPairStepBody qs.2.numVars qs.1
            (qs.2, zeroJet qs.2.jetOrder qs.2.precision)).2)
        (encPair encUnary encSubsetStepCtx) encJet
        (fun qs => (SubsetPairFold.subsetPairCount qs.2.numVars qs.1 + 1) *
          ((2 * qs.2.2.1.2 + 1) ^ qs.2.2.1.1 + 1) *
          (qs.2.numGroups * (2 ^ maxGroupDim qs.2.numVars qs.2.numGroups qs.2.varGroups + 1) + 1) *
            P qs)
        P := by
  obtain ⟨P₂, hP₂_pb, hSignM⟩ := exists_computableInO_signedMeasJet
  let eDC := encPair SubsetPairFold.encDecodedPair encSubsetStepCtx
  let cSignM : Cert evalSignedMeasJet eDC encJet := ⟨_, P₂, hSignM⟩
  let eSubAcc := encPair encSubsetStepCtx encJet
  let eSubIn := encPair SubsetPairFold.encDecodedPair eSubAcc
  have hprojDC : PolyT
      (fun inp : SubsetPairFold.DecodedPair × (SubsetStepCtx × JetRows) => (inp.1, inp.2.1))
      eSubIn eDC := (fst _ eSubAcc).prod (snd _ eSubAcc).fst'
  have haddSub : PolyT
      (fun q : (SubsetPairFold.DecodedPair × (SubsetStepCtx × JetRows)) × JetRows =>
        (q.1.2.1, addJet q.1.2.1.jetOrder q.1.2.1.precision q.1.2.2 q.2))
      (encPair eSubIn encJet) eSubAcc :=
    computableInPolyTime_ctxAddJet (J := SubsetStepCtx.jetOrder) (ℓ := SubsetStepCtx.precision)
      (by unfold encSubsetStepCtx; exact (snd _ _).snd'.fst'.fst')
      (by unfold encSubsetStepCtx; exact (snd _ _).snd'.fst'.snd'.fst')
  let cProjDC := NativeCertificate.ofPolyTime hprojDC
  let cAddSub := NativeCertificate.ofPolyTime haddSub
  have hcProjDC : cProjDC.IsPolynomial := NativeCertificate.ofPolyTime_isPolynomial hprojDC
  have hcAddSub : cAddSub.IsPolynomial := NativeCertificate.ofPolyTime_isPolynomial haddSub
  clear_value cProjDC cAddSub
  let cIdSub := NativeCertificate.linear (ei := eSubIn) (ComputableInO.of_eq fun _ => rfl)
  let cbSub₀ := cAddSub.comp (cIdSub.prod (cSignM.comp cProjDC))
  let cbSub : Cert subsetPairStepBody eSubIn eSubAcc :=
    ⟨cbSub₀.time, cbSub₀.space,
      cbSub₀.computes.of_enc_eq fun inp => congrArg eSubAcc (subsetPairStepBody_eq inp)⟩
  have hspSubP : HasPolySpace (cIdSub.prod (cSignM.comp cProjDC)) :=
    hasPolySpace_prod .self (hasPolySpace_comp hP₂_pb hcProjDC.2)
  obtain ⟨co, do_, ho_le⟩ := ((PolyBounded.self.add hcProjDC.1).add
    (hcAddSub.1.comp (polyBounded_length_of_hasPolySpace hspSubP))).exists_le
  obtain ⟨cs, ds, hs_le⟩ := (hasPolySpace_comp hcAddSub.2 hspSubP).exists_le
  let eQS := encPair encUnary encSubsetStepCtx
  have hn_qs : PolyT (fun qs : ℕ × SubsetStepCtx => qs.2.numVars) eQS encUnary := by
    unfold eQS encSubsetStepCtx; exact (snd encUnary _).fst'.fst'
  have hq_qs : PolyT (fun qs : ℕ × SubsetStepCtx => qs.1) eQS encUnary :=
    fst encUnary encSubsetStepCtx
  have hJ_qs : PolyT (fun qs : ℕ × SubsetStepCtx => qs.2.jetOrder) eQS encUnary := by
    unfold eQS encSubsetStepCtx; exact (snd encUnary _).snd'.snd'.fst'.fst'
  have hℓ_qs : PolyT (fun qs : ℕ × SubsetStepCtx => qs.2.precision) eQS encUnary := by
    unfold eQS encSubsetStepCtx; exact (snd encUnary _).snd'.snd'.fst'.snd'.fst'
  have hinitQS := (snd encUnary encSubsetStepCtx).prod (computableInPolyTime_zeroJet hJ_qs hℓ_qs)
  have hn_pb := hn_qs.polyBounded
  have hctx_pb := (snd encUnary encSubsetStepCtx).polyBounded_length
  let L_dc (qs : ℕ × SubsetStepCtx) :=
    2 * (6 * qs.2.numVars + 7) + 2 * (encSubsetStepCtx qs.2).length + 1
  have hLdc_pb : PolyBounded (fun qs => (eQS qs).length) L_dc :=
    (((PolyBounded.const 2).mul (((PolyBounded.const 6).mul hn_pb).add (.const 7))).add
      ((PolyBounded.const 2).mul hctx_pb)).add (.const 1)
  obtain ⟨M_entry, hM_pb, hM_le⟩ := exists_natAbs_rowEntry_le_two_pow
    (polyBounded_length_of_hasPolySpace (c := cSignM) hP₂_pb) hLdc_pb
  obtain ⟨cp2, dp2, hp2_le⟩ := hP₂_pb.exists_le
  let P_sm (qs : ℕ × SubsetStepCtx) := cp2 * (L_dc qs + 1) ^ dp2
  have hPsm_pb := NativeCertificate.polyBounded_pow_of_polyBounded hLdc_pb cp2 dp2
  let B_jet (qs : ℕ × SubsetStepCtx) :=
    qs.2.jetOrder *
      (2 * (qs.2.precision * (2 * ((2 * qs.2.numVars + 1) + (M_entry qs + 1)) + 3)) + 1)
  have hBjet_pb : PolyBounded (fun qs => (eQS qs).length) B_jet :=
    hJ_qs.polyBounded.mul (((PolyBounded.const 2).mul (hℓ_qs.polyBounded.mul
      (((PolyBounded.const 2).mul ((((PolyBounded.const 2).mul hn_pb).add (.const 1)).add
        (hM_pb.add (.const 1)))).add (.const 3)))).add (.const 1))
  let B_sub (qs : ℕ × SubsetStepCtx) := 2 * (encSubsetStepCtx qs.2).length + 2 * B_jet qs + 1
  have hBsub_pb : PolyBounded (fun qs => (eQS qs).length) B_sub :=
    (((PolyBounded.const 2).mul hctx_pb).add ((PolyBounded.const 2).mul hBjet_pb)).add (.const 1)
  have hdp_len (n q i : ℕ) :
      (SubsetPairFold.encDecodedPair (SubsetPairFold.unrankSubsetPair n q i)).length ≤
        6 * n + 7 := by
    unfold SubsetPairFold.encDecodedPair
    enc_len [SubsetPairFold.length_fst_unrankSubsetPair, SubsetPairFold.length_snd_unrankSubsetPair]
  have hB : ∀ qs j, j ≤ SubsetPairFold.subsetPairCount qs.2.numVars qs.1 →
      (eSubAcc (SubsetPairFold.runPrefix subsetPairStepBody qs.2.numVars qs.1 j
        (qs.2, zeroJet qs.2.jetOrder qs.2.precision)).2.2).length ≤ B_sub qs := by
    intro qs j hj; rw [SubsetPairFold.runPrefix_acc]; simp only [subsetPairStepBody_eq]
    rw [List.foldl_keep_fst (fun (s : SubsetStepCtx) (acc : JetRows) (i : ℕ) =>
      addJet s.jetOrder s.precision acc
        (evalSignedMeasJet (SubsetPairFold.unrankSubsetPair qs.2.numVars qs.1 i, s)))]
    have hf_le := length_encJetRows_foldl_optAddJet_le (J := qs.2.jetOrder) (ℓ := qs.2.precision)
      (N := SubsetPairFold.subsetPairCount qs.2.numVars qs.1) (M := 2 ^ M_entry qs)
      (f := fun i =>
        some (evalSignedMeasJet (SubsetPairFold.unrankSubsetPair qs.2.numVars qs.1 i, qs.2)))
      hj fun i _ y hy j' _ u' _ => by
        cases hy; refine hM_le qs _ ?_ j' u'
        have hdp := hdp_len qs.2.numVars qs.1 i
        dsimp only [eDC, L_dc]; rw [length_encPair]; dsimp only; omega
    have hN_sz :
        (SubsetPairFold.subsetPairCount qs.2.numVars qs.1).size ≤ 2 * qs.2.numVars + 1 := by
      rw [← Nat.size_eq_bits_len, ← encNat_apply]
      exact SubsetPairFold.length_encNat_subsetPairCount_le _ _
    have hjet_le := hf_le.trans (jetFoldl_bound_mono hN_sz)
    simp only [Option.elim_some] at hjet_le
    dsimp only [eSubAcc, B_sub, B_jet] at hjet_le ⊢; enc_len
  let L_sub (qs : ℕ × SubsetStepCtx) := 2 * (6 * qs.2.numVars + 7) + 2 * B_sub qs + 1
  have hLsub_pb : PolyBounded (fun qs => (eQS qs).length) L_sub :=
    (((PolyBounded.const 2).mul (((PolyBounded.const 6).mul hn_pb).add (.const 7))).add
      ((PolyBounded.const 2).mul hBsub_pb)).add (.const 1)
  let Q_sub (qs : ℕ × SubsetStepCtx) := cs * (L_sub qs + 1) ^ ds
  have hQsub_pb := NativeCertificate.polyBounded_pow_of_polyBounded hLsub_pb cs ds
  let Ov_sub (qs : ℕ × SubsetStepCtx) := co * (L_sub qs + 1) ^ do_
  have hOvsub_pb := NativeCertificate.polyBounded_pow_of_polyBounded hLsub_pb co do_
  let cn := NativeCertificate.ofPolyTime hn_qs
  let cq := NativeCertificate.ofPolyTime hq_qs
  let ci := NativeCertificate.ofPolyTime hinitQS
  have hcn : cn.IsPolynomial := NativeCertificate.ofPolyTime_isPolynomial hn_qs
  have hcq : cq.IsPolynomial := NativeCertificate.ofPolyTime_isPolynomial hq_qs
  have hci : ci.IsPolynomial := NativeCertificate.ofPolyTime_isPolynomial hinitQS
  clear_value cn cq ci
  let R_sub (qs : ℕ × SubsetStepCtx) := ((2 * qs.2.2.1.2 + 1) ^ qs.2.2.1.1 + 1) *
    (qs.2.numGroups * (2 ^ maxGroupDim qs.2.numVars qs.2.numGroups qs.2.varGroups + 1) + 1) *
    P_sm qs + Ov_sub qs
  have hinp_len : ∀ qs j, j ≤ SubsetPairFold.subsetPairCount qs.2.numVars qs.1 →
      (eSubIn (SubsetPairFold.unrankSubsetPair qs.2.numVars qs.1 j,
        (SubsetPairFold.runPrefix subsetPairStepBody qs.2.numVars qs.1 j
          (qs.2, zeroJet qs.2.jetOrder qs.2.precision)).2.2)).length ≤ L_sub qs :=
    fun qs j hj => by
      have hdp := hdp_len qs.2.numVars qs.1 j; have hb := hB qs j hj
      dsimp only [eSubIn, L_sub]; rw [length_encPair]; dsimp only; omega
  have hsp_run := SubsetPairFold.computableInO cn cq ci cbSub R_sub Q_sub B_sub
    (fun qs j hj => by
      set inp := (SubsetPairFold.unrankSubsetPair qs.2.numVars qs.1 j,
        (SubsetPairFold.runPrefix subsetPairStepBody qs.2.numVars qs.1 j
          (qs.2, zeroJet qs.2.jetOrder qs.2.precision)).2.2)
      have hov := poly_apply_le ho_le (hinp_len qs j hj)
      have hfst_eq : inp.2.1 = qs.2 := by
        dsimp only [inp]; rw [SubsetPairFold.runPrefix_acc]; simp only [subsetPairStepBody_eq]
        rw [List.foldl_keep_fst (fun (s : SubsetStepCtx) (acc : JetRows) (i : ℕ) =>
          addJet s.jetOrder s.precision acc
            (evalSignedMeasJet (SubsetPairFold.unrankSubsetPair qs.2.numVars qs.1 i, s)))]
      have hdc_len : (eDC (inp.1, inp.2.1)).length ≤ L_dc qs := by
        have hdp := hdp_len qs.2.numVars qs.1 j
        rw [hfst_eq]; dsimp only [eDC, inp, L_dc]; rw [length_encPair]; dsimp only; omega
      have hsm_t : cSignM.time (inp.1, inp.2.1) ≤ ((2 * qs.2.2.1.2 + 1) ^ qs.2.2.1.1 + 1) *
          (qs.2.numGroups * (2 ^ maxGroupDim qs.2.numVars qs.2.numGroups qs.2.varGroups + 1) + 1) *
            P_sm qs := by
        dsimp only [cSignM, eDC] at hdc_len ⊢; rw [hfst_eq] at hdc_len ⊢
        exact Nat.mul_le_mul_left _ (poly_apply_le hp2_le hdc_len)
      dsimp only [cbSub, cbSub₀, cIdSub, R_sub, Ov_sub, eSubIn, inp] at hov hsm_t ⊢
      simp only [NativeCertificate.comp_time, NativeCertificate.prod_time,
        NativeCertificate.linear_time, Function.comp_apply] at hov hsm_t ⊢
      omega)
    (fun qs j hj => poly_apply_le hs_le (hinp_len qs j hj))
    hB
  have hS_pb :=
    SubsetPairFold.polyBounded_space_of_polyBounded cn cq ci hcn hcq hci hBsub_pb hQsub_pb
  let cSubRun : Cert _ eQS eSubAcc := ⟨_, _, hsp_run⟩
  let hd_ov (qs : ℕ × SubsetStepCtx) := SubsetPairFold.decodeOverhead (qs.2.numVars + qs.1)
  have hhd_pb : PolyBounded (fun qs => (eQS qs).length) hd_ov := hS_pb.mono fun qs => by
    dsimp only [hd_ov]; omega
  let P_out (qs : ℕ × SubsetStepCtx) := P_sm qs + Ov_sub qs + hd_ov qs + B_sub qs +
    ((eQS qs).length + cn.time qs + cq.time qs + ci.time qs + hd_ov qs) +
    (NativeCertificate.snd cSubRun).space qs
  have hPout_pb : PolyBounded (fun qs => (eQS qs).length) P_out :=
    (((((hPsm_pb.add hOvsub_pb).add hhd_pb).add hBsub_pb).add
      ((((PolyBounded.self.add hcn.1).add hcq.1).add hci.1).add hhd_pb)).add hS_pb)
  clear_value L_dc P_sm B_jet B_sub L_sub Q_sub Ov_sub
  refine ⟨P_out, hPout_pb, (NativeCertificate.snd cSubRun).computes.mono_le (fun qs => ?_)
    fun qs => Nat.le_add_left _ _⟩
  set S_cnt := SubsetPairFold.subsetPairCount qs.2.numVars qs.1 + 1
  set M_cnt := (2 * qs.2.2.1.2 + 1) ^ qs.2.2.1.1 + 1
  set G_cnt := qs.2.numGroups * (2 ^ maxGroupDim qs.2.numVars qs.2.numGroups qs.2.varGroups + 1) + 1
  have hMG : 1 ≤ M_cnt * G_cnt := Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _)
  have hstep := mul_inner_add_absorb (A := S_cnt) (B := M_cnt * G_cnt)
    (p := P_sm qs) (q := hd_ov qs + B_sub qs + Ov_sub qs)
    (ov := (eQS qs).length + cn.time qs + cq.time qs + ci.time qs + hd_ov qs)
    (r := P_out qs) (Nat.succ_pos _) hMG (by dsimp only [P_out]; omega)
  dsimp only [NativeCertificate.snd_time, cSubRun, R_sub, hd_ov] at hstep ⊢
  refine (le_of_eq ?_).trans (hstep.trans_eq (by dsimp only [S_cnt, M_cnt, G_cnt]; ring))
  dsimp only [S_cnt, M_cnt, G_cnt]; ring

private def branchQ_u (inp : BranchEvalInput) : ℕ := min inp.numVars inp.numNodes
private def branchR_u (inp : BranchEvalInput) : ℕ := min inp.numVars inp.rowBound
private def branchr_u (inp : BranchEvalInput) : ℕ := min inp.numVars inp.numGroups
private def branchA₀_u (inp : BranchEvalInput) : ℕ := min (inp.numVars + 1) inp.intervalStart
private def branchD_cap (inp : BranchEvalInput) : ℕ :=
  min inp.numVars (branchr_u inp ^ (2 * branchQ_u inp))
private def branchTruncQ (inp : BranchEvalInput) : ℕ :=
  (inp.maxDegree * (branchR_u inp - 1)) * (inp.equations.length + 2 * inp.numVars) /
    max 1 (branchQ_u inp)
private def branchAugScopes (inp : BranchEvalInput) : List (List ℕ) :=
  withNeutralScopesList (inp.equations.map equationVars) inp.numVars

private theorem computableInPolyTime_branchClamped :
    PolyT BranchEvalInput.numVars encBranchEvalInput encUnary ∧
    PolyT BranchEvalInput.maxDegree encBranchEvalInput encUnary ∧
    PolyT BranchEvalInput.equations encBranchEvalInput encSparseSystem ∧
    PolyT branchQ_u encBranchEvalInput encUnary ∧
    PolyT branchR_u encBranchEvalInput encUnary ∧
    PolyT branchr_u encBranchEvalInput encUnary ∧
    PolyT branchA₀_u encBranchEvalInput encUnary ∧
    PolyT branchD_cap encBranchEvalInput encUnary ∧
    PolyT branchTruncQ encBranchEvalInput encUnary ∧
    PolyT branchAugScopes encBranchEvalInput (encList (encList encNat)) := by
  have hn' := BranchEvalInput.computableInPolyTime_numVars
  have hk' := BranchEvalInput.computableInPolyTime_maxDegree
  have heqs := BranchEvalInput.computableInPolyTime_equations
  have hr := BranchEvalInput.computableInPolyTime_numGroups
  have hQ := BranchEvalInput.computableInPolyTime_numNodes
  have hR := BranchEvalInput.computableInPolyTime_rowBound
  have hA₀ := BranchEvalInput.computableInPolyTime_intervalStart
  have hQu : PolyT branchQ_u encBranchEvalInput encUnary := binary_min_unary' hn' hQ
  have hRu : PolyT branchR_u encBranchEvalInput encUnary := binary_min_unary' hn' hR
  have hru : PolyT branchr_u encBranchEvalInput encUnary := binary_min_unary' hn' hr
  have hA₀u : PolyT branchA₀_u encBranchEvalInput encUnary :=
    binary_min_unary' (unary_add.comp (hn'.prod (const 1))) hA₀
  have hpow : PolyT (fun inp : BranchEvalInput => branchr_u inp ^ (2 * branchQ_u inp))
      encBranchEvalInput encNat :=
    (binary_pow.comp
      ((unary_to_binary.comp hru).prod (unary_add.comp (hQu.prod hQu)))).of_enc_eq
      fun inp => congrArg encNat (congrArg (branchr_u inp ^ ·)
        (by dsimp only [Function.comp_apply]; omega))
  have hDcap : PolyT branchD_cap encBranchEvalInput encUnary := binary_min_unary' hn' hpow
  have hnum := unary_mul.comp
    ((unary_mul.comp (hk'.prod (unary_sub.comp (hRu.prod (const 1))))).prod
    (unary_add.comp (((length_list (encList (encList encNat))).comp heqs).prod
      (unary_add.comp (hn'.prod hn')))))
  have hdiv := binary_div.comp ((unary_to_binary.comp hnum).prod
    (unary_to_binary.comp (bi_unary_max.comp ((const 1).prod hQu))))
  have hq : PolyT branchTruncQ encBranchEvalInput encUnary := by
    refine (binary_min_unary' hnum hdiv).of_enc_eq fun inp => congrArg encUnary ?_
    dsimp only [Function.comp_apply, branchTruncQ]
    rw [show inp.numVars + inp.numVars = 2 * inp.numVars by omega]
    exact (Nat.min_eq_right (Nat.div_le_self _ _)).symm
  exact ⟨hn', hk', heqs, hQu, hRu, hru, hA₀u, hDcap, hq,
    computableInPolyTime_withNeutralScopesListWithInput
      (bi_mapWithId (computableInPolyTime_equationVars.comp
        (snd encBranchEvalInput (encList (encList encNat))))
        heqs) hn'⟩

private def prepScheduleParams (inp : BranchEvalInput) : BalancedSchedules.ScheduleParams :=
  let aug := branchAugScopes inp
  ((inp.numVars, aug.length, branchQ_u inp), (branchr_u inp, inp.factorIncidence + inp.factorWidth),
    scopeIncidencesList inp.numVars aug)

private def mkDesignFromScheds (p : BranchEvalInput × (List (List ℕ) × List (List ℕ))) :
    BranchEvalInput × ReplacementDesignData :=
  (p.1, buildReplacementDesignData p.1.1.1 (branchD_cap p.1) (branchQ_u p.1) (branchr_u p.1)
    (branchA₀_u p.1) (branchR_u p.1) (branchAugScopes p.1) p.2.1 p.2.2)

private def mkDesignPair (inp : BranchEvalInput) : BranchEvalInput × ReplacementDesignData :=
  let p := prepScheduleParams inp
  mkDesignFromScheds (inp,
    BalancedSchedules.constructBalancedSchedules p.1.1 p.1.2.1 p.1.2.2 p.2.1.1 p.2.1.2 p.2.2)

private theorem exists_computableInO_mkDesignPair :
    ∃ P : BranchEvalInput → ℕ, PolyBounded (fun inp => (encBranchEvalInput inp).length) P ∧
      ComputableInO mkDesignPair encBranchEvalInput
        (encPair encBranchEvalInput encReplacementDesignData)
        (fun inp => (branchr_u inp ^ branchQ_u inp + 1) * P inp) P := by
  obtain ⟨hn', _, _, hQu, hRu, hru, hA₀u, hDcap, _, haug⟩ := computableInPolyTime_branchClamped
  have hprep : PolyT prepScheduleParams encBranchEvalInput
      BalancedSchedules.encScheduleParams := by
    unfold BalancedSchedules.encScheduleParams prepScheduleParams
    exact (hn'.prod (((length_list (encList encNat)).comp haug).prod hQu)).prod
      (((unary_to_binary.comp hru).prod
        (binary_add' BranchEvalInput.computableInPolyTime_factorIncidence
          BranchEvalInput.computableInPolyTime_factorWidth)).prod
        (computableInPolyTime_scopeIncidencesList hn' haug))
  let eSchOut := encPair (encList (encList encNat)) (encList (encList encNat))
  have hbuild : PolyT mkDesignFromScheds (encPair encBranchEvalInput eSchOut)
      (encPair encBranchEvalInput encReplacementDesignData) := by
    have hp1 : PolyT Prod.fst (encPair encBranchEvalInput eSchOut) encBranchEvalInput :=
      fst encBranchEvalInput eSchOut
    have hp2' := snd encBranchEvalInput eSchOut
    exact hp1.prod (computableInPolyTime_buildReplacementDesignData
      (hn'.comp hp1) (hDcap.comp hp1) (hQu.comp hp1) (hru.comp hp1) (hA₀u.comp hp1)
      (hRu.comp hp1) (haug.comp hp1) hp2'.fst' hp2'.snd')
  let cSched := BalancedSchedules.constructBalancedSchedulesCertificate
  obtain ⟨poly, hpoly, _, hB⟩ := BalancedSchedules.constructBalancedSchedulesCertificate_bounds
  have hcSched_sp : HasPolySpace cSched := (PolyBounded.of_polynomiallyBounded _ hpoly).mono
    fun p => (hB p).2
  let cPrep := NativeCertificate.ofPolyTime hprep
  let cId := NativeCertificate.linear (ei := encBranchEvalInput) (ComputableInO.of_eq fun _ => rfl)
  let cBuild := NativeCertificate.ofPolyTime hbuild
  have hcPrep : cPrep.IsPolynomial := NativeCertificate.ofPolyTime_isPolynomial hprep
  have hcBuild : cBuild.IsPolynomial := NativeCertificate.ofPolyTime_isPolynomial hbuild
  clear_value cPrep cBuild
  let cStg1 := cBuild.comp (cId.prod (cSched.comp cPrep))
  have hspMid : HasPolySpace (cId.prod (cSched.comp cPrep)) :=
    hasPolySpace_prod .self (hasPolySpace_comp hcSched_sp hcPrep.2)
  have hcStg1_sp : HasPolySpace cStg1 := hasPolySpace_comp hcBuild.2 hspMid
  have hpoly_pb : PolyBounded (fun inp => (encBranchEvalInput inp).length)
      (fun inp => poly (BalancedSchedules.encScheduleParams (prepScheduleParams inp)).length) :=
    (PolyBounded.of_polynomiallyBounded _ hpoly).comp hprep.polyBounded_length
  let ov1 (inp : BranchEvalInput) : ℕ := (encBranchEvalInput inp).length + cPrep.time inp +
    cBuild.time (inp, let p := prepScheduleParams inp
      BalancedSchedules.constructBalancedSchedules p.1.1 p.1.2.1 p.1.2.2 p.2.1.1 p.2.1.2 p.2.2)
  let P_out (inp : BranchEvalInput) : ℕ :=
    poly (BalancedSchedules.encScheduleParams (prepScheduleParams inp)).length +
      ov1 inp + cStg1.space inp
  have hPout_pb : PolyBounded (fun inp => (encBranchEvalInput inp).length) P_out :=
    (hpoly_pb.add (((PolyBounded.self.add hcPrep.1).add
      (hcBuild.1.comp (polyBounded_length_of_hasPolySpace hspMid))))).add hcStg1_sp
  refine ⟨P_out, hPout_pb, (cStg1.computes.of_enc_eq fun _ => rfl).mono_le (fun inp => ?_)
    fun inp => Nat.le_add_left _ _⟩
  have hsched_t := (hB (prepScheduleParams inp)).1
  have habs := absorb_step_add (branchr_u inp ^ branchQ_u inp + 1)
    (poly (BalancedSchedules.encScheduleParams (prepScheduleParams inp)).length) (ov1 inp)
    (Nat.succ_pos _)
  refine le_trans ?_ (Nat.mul_le_mul_left _ (show
    poly (BalancedSchedules.encScheduleParams (prepScheduleParams inp)).length + ov1 inp ≤ P_out inp
    by dsimp only [P_out]; omega))
  dsimp only [cStg1, cId, cSched, ov1] at hsched_t habs ⊢
  simp only [NativeCertificate.comp_time, NativeCertificate.prod_time,
    NativeCertificate.linear_time, Function.comp_apply] at habs ⊢
  dsimp only [prepScheduleParams] at hsched_t habs ⊢; omega

private def mkNodeSubIn (p : ((BranchEvalInput × ReplacementDesignData) ×
    List (List (List (List ℤ)))) × ℕ) : ℕ × SubsetStepCtx :=
  let inp := p.1.1.1; let data := p.1.1.2; let eqRowTables := p.1.2; let t := p.2
  let n' := inp.numVars; let k' := inp.maxDegree; let eqs' := inp.equations
  let r_u := branchr_u inp; let D_cap := branchD_cap inp; let q := branchTruncQ inp
  let m_rows := data.measurementMatrix.length
  let c_meas := min (4 * (n' + 1) * (eqs'.length * n' + n' + 1)) (r_u * m_rows)
  let grpEqLists := (List.range r_u).map fun g =>
    groupEquationsAt eqs' data.factorGroups eqRowTables t g
  (q, ((n', r_u, m_rows), (c_meas, D_cap), (q + 1, n' + 1, k'), ((t : ℤ) + 1, data.denom),
    (data.varGroups.getD t [], data.groupMeasurementMatrices.getD t []), grpEqLists))

private def finalizeDesignStage
    (p : (BranchEvalInput × ReplacementDesignData) × List JetRows) : ℕ :=
  let inp := p.1.1; let data := p.1.2; let n' := inp.numVars; let ℓ := n' + 1
  let nodes : List ℤ := (List.range (branchQ_u inp)).map fun (t : ℕ) => ((t : ℤ) + 1)
  let Ω : ℤ := ((data.denom ^ inp.maxDegree) ^ (2 * ℓ - 1)) ^ inp.equations.length
  let recCount :=
    CommonCountingAccum.recoverOuterJetSumModPowTwo nodes (branchTruncQ inp + 1) ℓ Ω p.2
  min (2 ^ n') recCount.toNat

private def evalDesignStageCore (idPair : BranchEvalInput × ReplacementDesignData) : ℕ :=
  let eqRowTables := buildEqRowTables idPair.1.numVars idPair.1.equations idPair.2
  let nodeJets := (List.range (branchQ_u idPair.1)).map fun t =>
    let qs := mkNodeSubIn ((idPair, eqRowTables), t)
    (SubsetPairFold.run subsetPairStepBody qs.2.numVars qs.1
      (qs.2, zeroJet qs.2.jetOrder qs.2.precision)).2
  finalizeDesignStage (idPair, nodeJets)

private def evalDesignStage (idPair : BranchEvalInput × ReplacementDesignData) : ℕ :=
  if validDesignShape idPair.1.numVars (branchr_u idPair.1) idPair.1.equations.length idPair.2 then
    evalDesignStageCore idPair
  else 0

private theorem exists_boundedIncidenceBranch_cert :
    ∃ c : Cert evalBoundedIncidenceBranch encBranchEvalInput encNat,
      PolyBounded (fun x => (encBranchEvalInput x).length) c.space ∧
      ∃ P : BranchEvalInput → ℕ, PolyBounded (fun x => (encBranchEvalInput x).length) P ∧
        ∀ inp : BranchEvalInput,
          let n' := inp.numVars; let Q_u := branchQ_u inp; let r_u := branchr_u inp
          let D_cap := branchD_cap inp; let q := branchTruncQ inp
          let data := (mkDesignPair inp).2; let m_rows := data.measurementMatrix.length
          let c_meas := min (4 * (n' + 1) * (inp.equations.length * n' + n' + 1)) (r_u * m_rows)
          let d_max := maxAllGroupDim n' Q_u r_u data.varGroups
          c.time inp ≤ ((r_u ^ Q_u + 1) + (Q_u + 1) * (SubsetPairFold.subsetPairCount n' q + 1) *
            ((2 * D_cap + 1) ^ c_meas + 1) * (r_u * (2 ^ d_max + 1) + 1)) * P inp := by
  obtain ⟨hn', hk', heqs, hQu, _, hru, _, hDcap, hq, _⟩ := computableInPolyTime_branchClamped
  let eID := encPair encBranchEvalInput encReplacementDesignData
  let eTabs := encList (encList (encList (encList encIntBin))); let eCtx := encPair eID eTabs
  have hid_inp : PolyT Prod.fst eID encBranchEvalInput :=
    fst encBranchEvalInput encReplacementDesignData
  have hid_data : PolyT Prod.snd eID encReplacementDesignData :=
    snd encBranchEvalInput encReplacementDesignData
  have hctx_build : PolyT (fun idPair : BranchEvalInput × ReplacementDesignData =>
      (idPair, buildEqRowTables idPair.1.numVars idPair.1.equations idPair.2)) eID eCtx :=
    id'.prod (computableInPolyTime_buildEqRowTables (hn'.comp hid_inp) (heqs.comp hid_inp) hid_data)
  have hmkNode : PolyT mkNodeSubIn (encPair eCtx encUnary)
      (encPair encUnary encSubsetStepCtx) := by
    let eIn := encPair eCtx encUnary; have hc := fst eCtx encUnary
    have ht := snd eCtx encUnary
    have hinp := hc.fst'.fst'; have hdat := hc.fst'.snd'; have htab := hc.snd'
    have hn_p := hn'.comp hinp; have hk_p := hk'.comp hinp; have heqs_p := heqs.comp hinp
    have hru_p := hru.comp hinp; have hDcap_p := hDcap.comp hinp; have hq_p := hq.comp hinp
    have hJ_p := unary_add.comp (hq_p.prod (const 1))
    have hℓ_p := unary_add.comp (hn_p.prod (const 1))
    have hm_rows :=
      (length_list (encList encIntBin)).comp (computableInPolyTime_measurementMatrix hdat)
    have hmeq_p := (length_list (encList (encList encNat))).comp heqs_p
    have hc_cap := unary_mul.comp ((unary_mul.comp ((const 4).prod hℓ_p)).prod
      (unary_add.comp ((unary_add.comp ((unary_mul.comp (hmeq_p.prod hn_p)).prod
        hn_p)).prod (const 1))))
    have hc_meas := bi_unary_min.comp (hc_cap.prod (unary_mul.comp (hru_p.prod hm_rows)))
    have hnode := bi_intBin_add' (intBin_natCast.comp (unary_to_binary.comp ht)) (const 1)
    have hvgt := (listGetD (encA := encList (encList encNat)) []).comp
      ((computableInPolyTime_varGroups hdat).prod ht)
    have hgmt := (listGetD (encA := encList (encList (encList encIntBin))) []).comp
      ((computableInPolyTime_groupMeasurementMatrices hdat).prod ht)
    have hp0 := fst eIn encUnary
    let grpEqAtFn (x : ((BranchEvalInput × ReplacementDesignData) ×
        List (List (List (List ℤ)))) × ℕ) (g : ℕ) :=
      groupEquationsAt x.1.1.1.equations x.1.1.2.factorGroups x.1.2 x.2 g
    have hge : PolyT (fun q => grpEqAtFn q.1 q.2)
        (encPair eIn encUnary) (encList encGroupEqEntry) :=
      computableInPolyTime_groupEquationsAt (heqs_p.comp hp0)
        ((computableInPolyTime_factorGroups hdat).comp hp0)
        (htab.comp hp0) (ht.comp hp0) (snd eIn encUnary)
    have hgrpEqs := mapWithInput (range.comp hru_p) hge
    unfold mkNodeSubIn encSubsetStepCtx
    exact hq_p.prod (((hn_p.prod (hru_p.prod hm_rows)).prod
      ((hc_meas.prod (unary_to_binary.comp hDcap_p)).prod
        ((hJ_p.prod (hℓ_p.prod hk_p)).prod
          ((hnode.prod (computableInPolyTime_denom hdat)).prod
            ((hvgt.prod hgmt).prod hgrpEqs))))))
  have hfin : PolyT finalizeDesignStage (encPair eID (encList encJet)) encNat := by
    let eF := encPair eID (encList encJet)
    have hp1 := hid_inp.comp (fst eID (encList encJet))
    have hdat := hid_data.comp (fst eID (encList encJet))
    have hnj := snd eID (encList encJet)
    have hn_f := hn'.comp hp1; have hk_f := hk'.comp hp1
    have heqs_f := heqs.comp hp1; have hQu_f := hQu.comp hp1; have hq_f := hq.comp hp1
    have hℓ_f := unary_add.comp (hn_f.prod (const 1))
    have hJ_f := unary_add.comp (hq_f.prod (const 1))
    have h2ℓ_sub1 := unary_sub.comp ((unary_mul.comp ((const 2).prod hℓ_f)).prod (const 1))
    have hmeq_f := (length_list (encList (encList encNat))).comp heqs_f
    have hnode_fn : PolyT (fun q : (_ × List JetRows) × ℕ => ((q.2 : ℤ) + 1))
        (encPair eF encUnary) encIntBin :=
      bi_intBin_add' (intBin_natCast.comp (unary_to_binary.comp (snd eF encUnary))) (const 1)
    have hnodes : PolyT
        (fun p : (BranchEvalInput × ReplacementDesignData) × List JetRows =>
          (List.range (branchQ_u p.1.1)).map fun (t : ℕ) => ((t : ℤ) + 1)) eF (encList encIntBin) :=
      mapWithInput (range.comp hQu_f) hnode_fn
    have hΩ := intBin_pow' (intBin_pow' (intBin_pow'
      (computableInPolyTime_denom hdat) hk_f) h2ℓ_sub1) hmeq_f
    have hrec_nat := intBin_toNat.comp
      (CommonCountingAccum.computableInPolyTime_recoverOuterJetSumModPowTwo
        hnodes hJ_f hℓ_f hΩ hnj)
    have h2pow := binary_two_pow.comp hn_f
    refine ((binary_le' h2pow hrec_nat).ite' h2pow hrec_nat).of_enc_eq fun p =>
      congrArg encNat ?_
    simp only [finalizeDesignStage, Nat.min_def, decide_eq_true_eq, Function.comp_apply]
  obtain ⟨P_nj, hPnj_pb, hNJ⟩ := exists_computableInO_nodeJet
  let cNJ : Cert _ (encPair encUnary encSubsetStepCtx) encJet := ⟨_, P_nj, hNJ⟩
  let cMkNode := NativeCertificate.ofPolyTime hmkNode
  have hcMkNode : cMkNode.IsPolynomial := NativeCertificate.ofPolyTime_isPolynomial hmkNode
  clear_value cMkNode
  let cNodeOne := cNJ.comp cMkNode
  have hcNodeOne_sp : HasPolySpace cNodeOne := hasPolySpace_comp hPnj_pb hcMkNode.2
  obtain ⟨cn1, dn1, hn1_le⟩ := (hcMkNode.1.add (hPnj_pb.comp hmkNode.polyBounded_length)).exists_le
  let hQu_id := hQu.comp hid_inp
  let Pn_iter (idPair : BranchEvalInput × ReplacementDesignData) : ℕ :=
    cn1 * (2 * (eCtx (idPair,
      buildEqRowTables idPair.1.numVars idPair.1.equations idPair.2)).length +
      2 * branchQ_u idPair.1 + 1 + 1) ^ dn1
  have hPn_iter_pb := NativeCertificate.polyBounded_pow_of_polyBounded
    ((((PolyBounded.const 2).mul hctx_build.polyBounded_length).add
      ((PolyBounded.const 2).mul hQu_id.polyBounded)).add (.const 1)) cn1 dn1
  let K_inner (idPair : BranchEvalInput × ReplacementDesignData) : ℕ :=
    let n' := idPair.1.numVars; let Q_u := branchQ_u idPair.1; let r_u := branchr_u idPair.1
    let c_meas := min (4 * (n' + 1) * (idPair.1.equations.length * n' + n' + 1))
      (r_u * idPair.2.measurementMatrix.length)
    (SubsetPairFold.subsetPairCount n' (branchTruncQ idPair.1) + 1) *
      ((2 * branchD_cap idPair.1 + 1) ^ c_meas + 1) *
      (r_u * (2 ^ maxAllGroupDim n' Q_u r_u idPair.2.varGroups + 1) + 1)
  obtain ⟨Pm_nodes, hPmn_pb, hcomp_nodes⟩ := exists_computableInO_mapRange hQu_id hctx_build
    hcNodeOne_sp cNodeOne.computes (fun idPair => K_inner idPair * Pn_iter idPair)
    fun idPair t ht => by
      have ht' : t < branchQ_u idPair.1 := ht
      have hlen : (encPair eCtx encUnary
          ((idPair, buildEqRowTables idPair.1.numVars idPair.1.equations idPair.2), t)).length ≤
          2 * (eCtx (idPair,
            buildEqRowTables idPair.1.numVars idPair.1.equations idPair.2)).length +
            2 * branchQ_u idPair.1 + 1 := by enc_len
      have hov := poly_apply_le hn1_le hlen
      have hpow_le := Nat.pow_le_pow_right Nat.zero_lt_two (maxGroupDim_le_maxAllGroupDim
        (n' := idPair.1.numVars) (r_u := branchr_u idPair.1) (varGroups := idPair.2.varGroups) ht')
      have hK_pos : 1 ≤ K_inner idPair :=
        Nat.mul_pos (Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _)) (Nat.succ_pos _)
      set K_t := (SubsetPairFold.subsetPairCount idPair.1.numVars (branchTruncQ idPair.1) + 1) *
        ((2 * branchD_cap idPair.1 + 1) ^ min (4 * (idPair.1.numVars + 1) *
          (idPair.1.equations.length * idPair.1.numVars + idPair.1.numVars + 1))
          (branchr_u idPair.1 * idPair.2.measurementMatrix.length) + 1) *
        (branchr_u idPair.1 * (2 ^ maxGroupDim idPair.1.numVars (branchr_u idPair.1)
          (idPair.2.varGroups.getD t []) + 1) + 1)
      have hKt_le : K_t ≤ K_inner idPair := Nat.mul_le_mul_left _
        (Nat.succ_le_succ (Nat.mul_le_mul_left _ (Nat.succ_le_succ hpow_le)))
      change cMkNode.time _ + K_t * P_nj _ ≤ K_inner idPair * Pn_iter idPair
      exact ((Nat.add_comm _ _).le.trans
        (Nat.add_le_add_right (Nat.mul_le_mul_right _ hKt_le) _)).trans
        ((absorb_step_add _ _ _ hK_pos).trans
          (Nat.mul_le_mul_left _ (by dsimp only [Pn_iter] at hov ⊢; omega)))
  let cMapNodes : Cert _ eID (encList encJet) := ⟨_, Pm_nodes, hcomp_nodes⟩
  obtain ⟨P_stg1, hPstg1_pb, hStg1⟩ := exists_computableInO_mkDesignPair
  change ComputableInO mkDesignPair encBranchEvalInput eID _ _ at hStg1
  let cStg1 : Cert mkDesignPair encBranchEvalInput eID := ⟨_, P_stg1, hStg1⟩
  let cFin := NativeCertificate.ofPolyTime hfin
  have hcFin : cFin.IsPolynomial := NativeCertificate.ofPolyTime_isPolynomial hfin
  have hshape_id := computableInPolyTime_validDesignShape (hn'.comp hid_inp) (hru.comp hid_inp)
    ((length_list (encList (encList encNat))).comp (heqs.comp hid_inp)) hid_data
  let cGuard2 := NativeCertificate.ofPolyTime hshape_id
  have hcGuard2 : cGuard2.IsPolynomial := NativeCertificate.ofPolyTime_isPolynomial hshape_id
  clear_value cFin cGuard2 eID
  let cIdID := NativeCertificate.linear (ei := eID) (ComputableInO.of_eq fun _ => rfl)
  let cCore := cFin.comp (cIdID.prod cMapNodes)
  have hspIDN : HasPolySpace (cIdID.prod cMapNodes) := hasPolySpace_prod .self hPmn_pb
  have hcCore_sp : HasPolySpace cCore := hasPolySpace_comp hcFin.2 hspIDN
  let cZeroID := NativeCertificate.const (ei := eID) (em := encNat) 0
  let cStg2 := NativeCertificate.branch cGuard2 cCore cZeroID
  have hcStg2_sp : HasPolySpace cStg2 :=
    hasPolySpace_branch hcGuard2.2 hcCore_sp (NativeCertificate.const_isPolynomial 0).2
  let fnOut (idPair : BranchEvalInput × ReplacementDesignData) :=
    (idPair, (List.range (branchQ_u idPair.1)).map fun t =>
      let qs := mkNodeSubIn
        ((idPair, buildEqRowTables idPair.1.numVars idPair.1.equations idPair.2), t)
      (SubsetPairFold.run subsetPairStepBody qs.2.numVars qs.1
        (qs.2, zeroJet qs.2.jetOrder qs.2.precision)).2)
  let P_stg2 (idPair : BranchEvalInput × ReplacementDesignData) : ℕ :=
    Pn_iter idPair + Pm_nodes idPair +
      (cGuard2.time idPair + (eID idPair).length + cFin.time (fnOut idPair))
  have hPstg2_pb : PolyBounded (fun idPair => (eID idPair).length) P_stg2 :=
    (hPn_iter_pb.add hPmn_pb).add
      ((hcGuard2.1.add .self).add (hcFin.1.comp (polyBounded_length_of_hasPolySpace hspIDN)))
  have hStg2_time (idPair : BranchEvalInput × ReplacementDesignData) :
      cStg2.time idPair ≤ (branchQ_u idPair.1 + 1) * K_inner idPair * P_stg2 idPair := by
    have hK_pos : 1 ≤ K_inner idPair :=
      Nat.mul_pos (Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _)) (Nat.succ_pos _)
    dsimp only [cStg2, cCore, cIdID, cMapNodes, cZeroID]
    simp only [NativeCertificate.branch_time, NativeCertificate.comp_time,
      NativeCertificate.prod_time, NativeCertificate.linear_time, NativeCertificate.const_time,
      Function.comp_apply]
    split_ifs
    · let ovS := cGuard2.time idPair + (eID idPair).length + cFin.time (fnOut idPair)
      have hstep := mul_inner_add_absorb (A := branchQ_u idPair.1 + 1) (B := K_inner idPair)
        (Nat.succ_pos (branchQ_u idPair.1)) hK_pos
        (by dsimp only [P_stg2, ovS]; omega :
          Pn_iter idPair + Pm_nodes idPair + ovS ≤ P_stg2 idPair)
      change cGuard2.time idPair + ((eID idPair).length +
        (branchQ_u idPair.1 + 1) * (K_inner idPair * Pn_iter idPair + Pm_nodes idPair) +
        cFin.time (fnOut idPair)) ≤ _
      exact (by dsimp only [ovS]; omega : _ ≤ (branchQ_u idPair.1 + 1) *
        (K_inner idPair * Pn_iter idPair + Pm_nodes idPair) + ovS).trans hstep
    · exact (Nat.le_mul_of_pos_left (cGuard2.time idPair + (eID idPair).length)
        (Nat.mul_pos (Nat.succ_pos _) hK_pos)).trans
        (Nat.mul_le_mul_left _ (by dsimp only [P_stg2]; omega))
  let cGuard1 := NativeCertificate.ofPolyTime computableInPolyTime_validBranchEvalParams
  have hcGuard1 : cGuard1.IsPolynomial :=
    NativeCertificate.ofPolyTime_isPolynomial computableInPolyTime_validBranchEvalParams
  clear_value cGuard1
  let cZeroInp := NativeCertificate.const (ei := encBranchEvalInput) (em := encNat) 0
  let cFull₀ := NativeCertificate.branch cGuard1 (cStg2.comp cStg1) cZeroInp
  have heval_eq : (fun inp => if validBranchEvalParams inp then evalDesignStage (mkDesignPair inp)
      else 0) = evalBoundedIncidenceBranch := by
    funext inp
    unfold evalBoundedIncidenceBranch evalDesignStage evalDesignStageCore mkDesignPair
      mkDesignFromScheds prepScheduleParams mkNodeSubIn finalizeDesignStage branchAugScopes
      branchD_cap branchTruncQ branchQ_u branchR_u branchr_u branchA₀_u
    dsimp only; cases validBranchEvalParams inp; · rfl
    · cases validDesignShape _ _ _ _ <;> rfl
  let cFull : Cert evalBoundedIncidenceBranch encBranchEvalInput encNat :=
    ⟨cFull₀.time, cFull₀.space, cFull₀.computes.of_enc_eq fun inp =>
      congrArg encNat (congrFun heval_eq inp).symm⟩
  have hsp12 : HasPolySpace (cStg2.comp cStg1) := hasPolySpace_comp hcStg2_sp hPstg1_pb
  have hcFull_sp : PolyBounded (fun inp => (encBranchEvalInput inp).length) cFull.space :=
    hasPolySpace_branch hcGuard1.2 hsp12 (NativeCertificate.const_isPolynomial 0).2
  let P_all (inp : BranchEvalInput) : ℕ :=
    cGuard1.time inp + (encBranchEvalInput inp).length + P_stg1 inp + P_stg2 (mkDesignPair inp)
  have hPall_pb : PolyBounded (fun inp => (encBranchEvalInput inp).length) P_all :=
    ((hcGuard1.1.add .self).add hPstg1_pb).add
      (hPstg2_pb.comp (polyBounded_length_of_hasPolySpace (c := cStg1) hPstg1_pb))
  refine ⟨cFull, hcFull_sp, P_all, hPall_pb, fun inp => ?_⟩
  have hmk1 : (mkDesignPair inp).1 = inp := rfl
  set K0 := K_inner (mkDesignPair inp); set A_cnt := branchr_u inp ^ branchQ_u inp + 1
  set B_cnt := (branchQ_u inp + 1) * K0
  have hAB_pos : 1 ≤ A_cnt + B_cnt := Nat.add_pos_left (Nat.succ_pos _) _
  have h2 : cStg2.time (mkDesignPair inp) ≤ B_cnt * P_stg2 (mkDesignPair inp) := by
    have h := hStg2_time (mkDesignPair inp); rw [hmk1] at h; exact h
  have hov := Nat.le_mul_of_pos_left (cGuard1.time inp + (encBranchEvalInput inp).length) hAB_pos
  have hmain : cFull.time inp ≤ (A_cnt + B_cnt) * P_all inp := by
    have h1 : cStg1.time inp = A_cnt * P_stg1 inp := rfl
    dsimp only [cFull, cFull₀, cZeroInp]
    simp only [NativeCertificate.branch_time, NativeCertificate.comp_time,
      NativeCertificate.const_time]
    split_ifs
    · rw [h1, ← Nat.add_assoc]
      have h0 := (Nat.le_add_right (cGuard1.time inp) (encBranchEvalInput inp).length).trans hov
      have h1' := Nat.mul_le_mul_right (P_stg1 inp) (Nat.le_add_right A_cnt B_cnt)
      have h2' := h2.trans (Nat.mul_le_mul_right _ (Nat.le_add_left B_cnt A_cnt))
      exact (Nat.add_le_add (Nat.add_le_add h0 h1') h2').trans_eq (by dsimp only [P_all]; ring)
    · exact hov.trans (Nat.mul_le_mul_left _ (by dsimp only [P_all]; omega))
  refine hmain.trans_eq ?_; dsimp only [A_cnt, B_cnt, K0, K_inner]; rw [hmk1]; ac_rfl

end LoopCertificates

/-! ### 3. Public Branch Certificate, Polynomial Workspace, and Subexponential Runtime Bound -/

/-- **Proposition 5.3 native branch certificate**: uniform multi-tape Turing machine resource
certificate for `evalBoundedIncidenceBranch` on `encBranchEvalInput`
([OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], §§5.3–5.5, Proposition 5.3,
pp. 37–39). -/
public noncomputable def boundedIncidenceBranchCertificate :
    NativeCertificate evalBoundedIncidenceBranch encBranchEvalInput encNat :=
  exists_boundedIncidenceBranch_cert.choose

/-- **Global polynomial workspace bound**: `boundedIncidenceBranchCertificate.space` is
polynomially bounded in `(encBranchEvalInput x).length` across **all** raw `BranchEvalInput`
tuples `x` (including malformed or unfeasible inputs). -/
public theorem polyBounded_boundedIncidenceBranchCertificate_space :
    PolyBounded (fun x => (encBranchEvalInput x).length)
      boundedIncidenceBranchCertificate.space :=
  exists_boundedIncidenceBranch_cert.choose_spec.1

/-- **Proposition 5.3 subexponential branch runtime bound**: for every degree bound `k_deg`,
polylogarithmic exponent `β`, and constant `C_inc`, above `N₀_br`, every feasible reduced branch
`(n', sys')` with `sysMaxDegree sys' ≤ k_deg`, `sys'.length ≤ C_inc * n'`, and neutral-augmented
factor incidence and scope width at most `C_inc * (Nat.clog 2 n') ^ β` runs in
`O^*(2^{O(interpolationScale n')})` native TM steps. -/
public theorem exists_boundedIncidenceBranchCertificate_time_bound
    (N₀_branch k_deg β C_inc : ℕ) :
    ∃ N₀_br C_br d_br A_br : ℕ,
      ∀ n' : ℕ, ∀ sys' : List (List (List ℕ)),
        checkBranchFeasible N₀_branch (n', sys') = true → N₀_br ≤ n' →
        sysMaxDegree sys' ≤ k_deg → sys'.length ≤ C_inc * n' →
        branchMaxFactorIncidence n' sys' ≤ C_inc * Nat.clog 2 n' ^ β →
        branchMaxFactorWidth n' sys' ≤ C_inc * Nat.clog 2 n' ^ β →
        (boundedIncidenceBranchCertificate.time (prepareBranchEvalInput (n', sys')) : ℝ) ≤
          (C_br : ℝ) * ((encPair encUnary encSparseSystem (n', sys')).length + 1 : ℝ) ^ d_br *
            (2 : ℝ) ^ ((A_br : ℝ) * interpolationScale n') := by
  obtain ⟨P, hP_pb, htime⟩ := exists_boundedIncidenceBranch_cert.choose_spec.2
  obtain ⟨C_p, d_p, hCp⟩ :=
    (hP_pb.comp computableInPolyTime_prepareBranchEvalInput.polyBounded_length).exists_le
  refine ⟨max 16384 (2 ^ C_inc), 64 * C_p, d_p + 3,
    65792 * (k_deg * (C_inc + 2) + 4) * (β + 4), ?_⟩
  exact parametric_branch_step_bound (N₀_branch := N₀_branch) (k_deg := k_deg) (β := β)
    (C_inc := C_inc) (C_p := C_p) (d_p := d_p)
    (T := fun ns => boundedIncidenceBranchCertificate.time (prepareBranchEvalInput ns))
    fun n' sys' hfeas _ => by
    intro β' r Q R q
    have hex := exists_refines_prepare_of_feasible hfeas
    dsimp only [prepareBranchEvalInput, ParameterCheck.computeScheduleParams] at hex
    obtain ⟨hQn, hRn, hrn, _, haux, _, D, href, hmeas_len, _⟩ := hex
    let inp := prepareBranchEvalInput (n', sys')
    let A₀ := ReplacementParams.intervalStart β' n'
    have hQu_eq : branchQ_u inp = Q := Nat.min_eq_right hQn
    have hRu_eq : branchR_u inp = R := Nat.min_eq_right hRn
    have hru_eq : branchr_u inp = r := Nat.min_eq_right hrn
    have hDcap_eq : branchD_cap inp = r ^ (2 * Q) := by
      simp only [branchD_cap, hru_eq, hQu_eq]; exact Nat.min_eq_right haux
    have hq_eq : branchTruncQ inp =
        (sysMaxDegree sys' * (R - 1)) * (sys'.length + 2 * n') / max 1 Q := by
      simp only [branchTruncQ, hRu_eq, hQu_eq]; rfl
    let data := (mkDesignPair inp).2; let m_rows := data.measurementMatrix.length
    let c_meas := min (4 * (n' + 1) * (sys'.length * n' + n' + 1)) (r * m_rows)
    let d_max := maxAllGroupDim n' Q r data.varGroups
    refine ⟨c_meas, d_max, ?_, ?_, ?_⟩
    · have hc_le : c_meas ≤ r * (D.h * #(measurementIndices Q r A₀ R)) :=
        (Nat.min_le_right _ _).trans (le_of_eq (congrArg (r * ·) hmeas_len))
      have hrat_r : (((r * (D.h * #(measurementIndices Q r A₀ R)) : ℕ) : ℚ) : ℝ) ≤
          ((2 * ReplacementParams.tauRat n' * (n' : ℚ) : ℚ) : ℝ) :=
        Rat.cast_le.mpr D.total_measurement_rows_le
      simp only [Rat.cast_natCast, Rat.cast_mul, Rat.cast_ofNat,
        ReplacementParams.cast_tauRat] at hrat_r
      exact (Nat.cast_le.mpr hc_le).trans hrat_r
    · unfold d_max maxAllGroupDim
      refine (List.max_le_iff (l := _ :: _) (List.cons_ne_nil _ _)).mpr ?_
      simp only [List.mem_cons, forall_eq_or_imp]
      refine ⟨Nat.zero_le _, fun x hx => ?_⟩
      obtain ⟨t, ht_mem, rfl⟩ := List.mem_map.mp hx; have ht : t < Q := List.mem_range.mp ht_mem
      unfold maxGroupDim
      refine (List.max_le_iff (l := _ :: _) (List.cons_ne_nil _ _)).mpr ?_
      simp only [List.mem_cons, forall_eq_or_imp]
      refine ⟨Nat.zero_le _, fun y hy => ?_⟩
      obtain ⟨g, hg_mem, rfl⟩ := List.mem_map.mp hy; have hg : g < r := List.mem_range.mp hg_mem
      exact (Nat.min_le_right _ _).trans (href.2.2.1 ⟨t, ht⟩ ⟨g, hg⟩).2.1
    · have ht := htime inp; have hp := hCp (n', sys')
      change boundedIncidenceBranchCertificate.time inp ≤ _
      dsimp only [boundedIncidenceBranchCertificate]; rw [hQu_eq, hru_eq, hDcap_eq, hq_eq] at ht
      exact ht.trans (Nat.mul_le_mul_left _ hp)

/-- **Instantiation of `BranchPolylogTimeBound`**: `boundedIncidenceBranchCertificate` satisfies
`Cslib.Complexity.BranchedSparseCNFCounter.BranchPolylogTimeBound` for every `N₀_branch`. -/
public theorem branchPolylogTimeBound_boundedIncidenceBranchCertificate (N₀_branch : ℕ) :
    Cslib.Complexity.BranchedSparseCNFCounter.BranchPolylogTimeBound N₀_branch
      boundedIncidenceBranchCertificate :=
  fun k_deg β C_inc => exists_boundedIncidenceBranchCertificate_time_bound N₀_branch k_deg β C_inc

end Cslib.Complexity.SubexponentialSAT.SparsePolyCounter
