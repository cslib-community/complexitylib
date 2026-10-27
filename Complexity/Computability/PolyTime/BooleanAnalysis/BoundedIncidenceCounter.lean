/-
Copyright (c) 2026 Anton Kovsharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anton Kovsharov
-/
module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.PolyTime.BooleanAnalysis.BoundedIncidenceSemantics
public import Complexity.Computability.PolyTime.BooleanAnalysis.BoundedIncidenceStepCert
import all Complexity.Computability.PolyTime.BooleanAnalysis.BoundedIncidenceStepCert
import Complexity.Computability.Complexity.FineGrained.SparseBranchAsymptotics
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.Plain
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolySpace.Plain
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Fold
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.List.Size
import Mathlib.Data.List.GetD
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Native Resource Bounds and Unconditional Counter for Bounded-Incidence Polynomial Systems

This file establishes the native resource certificates and subexponential runtime bounds for the
bounded-incidence, bounded-width $\mathbb{F}_2$ polynomial-system branch evaluator of
[OpenAI2026ETH], §§3.4–3.5, §4.7, §§5.4–5.5, Proposition 5.3, and instantiates the unconditional
sparse polynomial-system and context-parity counters toward Theorem 2.2.

## Main definitions

* `boundedIncidenceBranchCertificate`: native multi-tape TM resource certificate for
  `evalBoundedIncidenceBranch`.
* `unconditionalSparsePolyCounter`: unconditional $\mathbb{F}_2$ sparse polynomial-system root
  counter instantiated with `evalBoundedIncidenceBranch`.
* `unconditionalContextParityCounter`: unconditional context-parity counter instantiated with
  `evalBoundedIncidenceBranch`.

## Main results

* `polyBounded_boundedIncidenceBranchCertificate_space`: global polynomial workspace bound for
  `boundedIncidenceBranchCertificate`.
* `branchPolylogTimeBound_boundedIncidenceBranchCertificate`: subexponential
  $O^*(2^{O(\mathrm{interpolationScale}(n'))})$ branch runtime bound under polylogarithmic factor
  incidence and scope width (Proposition 5.3, pp. 37–38).
* `unconditionalSparsePolyCounter_eq_rootCount`: unconditional exactness of
  `unconditionalSparsePolyCounter`.

## References

* [OpenAI2026ETH], §§3.4–3.5, §4.7, §§5.4–5.5, Proposition 5.3, Theorem 2.2.
-/

namespace Cslib.Complexity.SubexponentialSAT.SparsePolyCounter

open Finset Cslib Cslib.BitString Cslib.Complexity Cslib.GenericRAM Cslib.LinearAlgebra
open Turing.MultiTapeTM

local notation "encSys" => encList (encList (encList encNat))

/-! ### 1. Asymptotic Branch Step-Count Transfer to `interpolationScale` -/

/-- For `2 ≤ n'`, the Section 4.7 auxiliary dimension `auxDim n' = r ^ (2 * Q)` is strictly bounded
by `n'` itself (since `D ≤ 2 ^ (λ / 128) ≤ 2 ^ (λ - 1) < n'`). -/
public theorem auxDim_lt_self_of_two_le {n' : ℕ} (hn' : 2 ≤ n') :
    ReplacementParams.auxDim n' < n' := by
  have hlam1 : 1 ≤ Nat.clog 2 n' :=
    (Nat.lt_clog_iff_pow_lt Nat.one_lt_two).mpr (by omega : 2 ^ 0 < n')
  have hdiv : Nat.clog 2 n' / 128 ≤ Nat.clog 2 n' - 1 := by omega
  have hpow_lt : 2 ^ (Nat.clog 2 n' - 1) < n' :=
    (Nat.lt_clog_iff_pow_lt Nat.one_lt_two).mp (by omega)
  exact (ReplacementParams.auxDim_le_two_pow n').trans_lt
    ((Nat.pow_le_pow_right Nat.zero_lt_two hdiv).trans_lt hpow_lt)

/-- For `2 ≤ n'`, `numGroups n' ^ numNodes n' ≤ n'`. -/
private theorem numGroups_pow_numNodes_le_self {n' : ℕ} (hn' : 2 ≤ n')
    (hr : 1 ≤ ReplacementParams.numGroups n') :
    ReplacementParams.numGroups n' ^ ReplacementParams.numNodes n' ≤ n' := by
  have hle : ReplacementParams.numGroups n' ^ ReplacementParams.numNodes n' ≤
      ReplacementParams.auxDim n' := by
    unfold ReplacementParams.auxDim
    exact Nat.pow_le_pow_right hr (by omega)
  exact hle.trans (auxDim_lt_self_of_two_le hn').le

/-- Uniform upper bound `chooseBeta (clog 2 n') b w ≤ β + 1` whenever `n' ≥ max 4 (2 ^ C_inc)`
and `b, w ≤ C_inc * (clog 2 n') ^ β`. -/
private theorem chooseBeta_le_succ_of_le_mul_clog_pow {n' b w β C_inc : ℕ}
    (hn4 : 4 ≤ n') (hnC : 2 ^ C_inc ≤ n')
    (hb : b ≤ C_inc * Nat.clog 2 n' ^ β) (hw : w ≤ C_inc * Nat.clog 2 n' ^ β) :
    1 ≤ ParameterCheck.chooseBeta (Nat.clog 2 n') b w ∧
      ParameterCheck.chooseBeta (Nat.clog 2 n') b w ≤ β + 1 := by
  set lam := Nat.clog 2 n'
  have hlam2 : 2 ≤ lam :=
    (show 2 = Nat.clog 2 (2 ^ 2) from (Nat.clog_pow 2 2 Nat.one_lt_two).symm).trans_le
      (Nat.clog_mono_right 2 hn4)
  have hC_le : C_inc ≤ lam :=
    (Nat.clog_pow 2 C_inc Nat.one_lt_two).symm.trans_le (Nat.clog_mono_right 2 hnC)
  have hb' : b ≤ lam ^ (β + 1) := by
    rw [pow_succ']
    exact hb.trans (Nat.mul_le_mul_right (lam ^ β) hC_le)
  have hw' : w ≤ lam ^ (β + 1) := by
    rw [pow_succ']
    exact hw.trans (Nat.mul_le_mul_right (lam ^ β) hC_le)
  obtain ⟨h1, _, _, hmin⟩ := ParameterCheck.chooseBeta_spec (b := b) (w := w) hlam2
  refine ⟨h1, ?_⟩
  by_contra hgt
  exact hmin (β + 1) (Nat.succ_pos β) (Nat.lt_of_not_ge hgt) ⟨hb', hw'⟩

private theorem exp_le_two_rpow_two_mul {x : ℝ} (hx : 0 ≤ x) :
    Real.exp x ≤ (2 : ℝ) ^ (2 * x) := by
  rw [Real.rpow_def_of_pos two_pos, Real.exp_le_exp]
  have hlog2 : (1 : ℝ) - 2⁻¹ ≤ Real.log 2 := Real.one_sub_inv_le_log_of_pos zero_lt_two
  have h1 : 1 ≤ 2 * Real.log 2 := by linarith
  calc x = 1 * x := (one_mul x).symm
    _ ≤ (2 * Real.log 2) * x := mul_le_mul_of_nonneg_right h1 hx
    _ = Real.log 2 * (2 * x) := by ring

private theorem step_prefactor_le {rQ Q r S M G L : ℕ}
    (hrQ : rQ ≤ L) (hQ : Q ≤ L) (hr2 : 2 ≤ r) (hrL : r ≤ L)
    (hS : 1 ≤ S) (hM : 1 ≤ M) (hG : 1 ≤ G) :
    (rQ + 1) + (Q + 1) * (S + 1) * (M + 1) * (r * (G + 1) + 1) ≤
      64 * (L + 1) ^ 3 * (S * M * G) := by
  have hE : 1 ≤ S * M * G := Nat.mul_pos (Nat.mul_pos hS hM) hG
  have hQ1 : Q + 1 ≤ L + 1 := Nat.succ_le_succ hQ
  have hSp1 : S + 1 ≤ 2 * S := by omega
  have hMp1 : M + 1 ≤ 2 * M := by omega
  have hGp1 : r * (G + 1) + 1 ≤ 4 * (L + 1) * G := by
    have hrG : r ≤ r * G := Nat.le_mul_of_pos_right r hG
    have h1G : 1 ≤ r * G := by omega
    calc r * (G + 1) + 1 = r * G + r + 1 := by ring
      _ ≤ r * G + r * G + r * G + r * G := by omega
      _ = 4 * r * G := by ring
      _ ≤ 4 * (L + 1) * G := Nat.mul_le_mul_right G (Nat.mul_le_mul_left 4 (by omega))
  have hprod4 : (Q + 1) * (S + 1) * (M + 1) * (r * (G + 1) + 1) ≤ 16 * (L + 1) ^ 2 * (S * M * G) :=
    calc (Q + 1) * (S + 1) * (M + 1) * (r * (G + 1) + 1)
        ≤ (L + 1) * (2 * S) * (2 * M) * (4 * (L + 1) * G) :=
          Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul hQ1 hSp1) hMp1) hGp1
      _ = 16 * (L + 1) ^ 2 * (S * M * G) := by ring
  have hL1_pos : 1 ≤ L + 1 := Nat.succ_pos L
  have hL3 : L + 1 ≤ (L + 1) ^ 3 := by
    simpa only [pow_one] using Nat.pow_le_pow_right hL1_pos (by decide : 1 ≤ 3)
  have hL23 : (L + 1) ^ 2 ≤ (L + 1) ^ 3 :=
    Nat.pow_le_pow_right hL1_pos (by decide : 2 ≤ 3)
  have hrQ_le : rQ + 1 ≤ (L + 1) ^ 3 * (S * M * G) :=
    (Nat.succ_le_succ hrQ).trans (hL3.trans (Nat.le_mul_of_pos_right _ hE))
  have hp4_le : 16 * (L + 1) ^ 2 * (S * M * G) ≤ 16 * (L + 1) ^ 3 * (S * M * G) :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 16 hL23)
  calc (rQ + 1) + (Q + 1) * (S + 1) * (M + 1) * (r * (G + 1) + 1)
      ≤ (L + 1) ^ 3 * (S * M * G) + 16 * (L + 1) ^ 3 * (S * M * G) :=
        Nat.add_le_add hrQ_le (hprod4.trans hp4_le)
    _ = 17 * ((L + 1) ^ 3 * (S * M * G)) := by ring
    _ ≤ 64 * ((L + 1) ^ 3 * (S * M * G)) := Nat.mul_le_mul_right _ (by decide)
    _ = 64 * (L + 1) ^ 3 * (S * M * G) := by ring

/-- Core subexponential step-count bound for Proposition 5.3: under `checkBranchFeasible`,
polylogarithmic `(b, w)` bounds, linear equation count `sys'.length ≤ C_inc * n'`, and degree
`sysMaxDegree sys' ≤ k_deg`, any parametric loop-product bound is dominated above
`max 16384 (2 ^ C_inc)` by a fixed polynomial in `(encPair encUnary encSys (n', sys')).length`
times `2 ^ (A_br * interpolationScale n')`. -/
private theorem parametric_branch_step_bound {N₀_branch k_deg β C_inc C_p d_p : ℕ}
    {T : ℕ × List (List (List ℕ)) → ℕ}
    (hT : ∀ n' sys',
      checkBranchFeasible N₀_branch (n', sys') = true →
      16384 ≤ n' →
      let b := branchMaxFactorIncidence n' sys'
      let w := branchMaxFactorWidth n' sys'
      let β' := ParameterCheck.chooseBeta (Nat.clog 2 n') b w
      let r := ReplacementParams.numGroups n'
      let Q := ReplacementParams.numNodes n'
      let R := ReplacementParams.rowBound β' n'
      let q := (sysMaxDegree sys' * (R - 1)) * (sys'.length + 2 * n') / max 1 Q
      ∃ c_meas d_max : ℕ,
        (c_meas : ℝ) ≤ 2 * ReplacementParams.tau n' * (n' : ℝ) ∧
        d_max ≤ 2 * n' / r ∧
        T (n', sys') ≤
          ((r ^ Q + 1) +
            (Q + 1) * (SubsetPairFold.subsetPairCount n' q + 1) *
              ((2 * r ^ (2 * Q) + 1) ^ c_meas + 1) * (r * (2 ^ d_max + 1) + 1)) *
            (C_p * ((encPair encUnary encSys (n', sys')).length + 1) ^ d_p)) :
    let c_deg := k_deg * (C_inc + 2)
    let A_br := 65792 * (c_deg + 4) * (β + 4)
    ∀ n' : ℕ, ∀ sys' : List (List (List ℕ)),
      checkBranchFeasible N₀_branch (n', sys') = true →
      max 16384 (2 ^ C_inc) ≤ n' →
      sysMaxDegree sys' ≤ k_deg →
      sys'.length ≤ C_inc * n' →
      branchMaxFactorIncidence n' sys' ≤ C_inc * Nat.clog 2 n' ^ β →
      branchMaxFactorWidth n' sys' ≤ C_inc * Nat.clog 2 n' ^ β →
      (T (n', sys') : ℝ) ≤
        ((64 * C_p : ℕ) : ℝ) * ((encPair encUnary encSys (n', sys')).length + 1 : ℝ) ^ (d_p + 3) *
          (2 : ℝ) ^ ((A_br : ℝ) * interpolationScale n') := by
  intro c_deg A_br n' sys' hfeas hn' hdeg hlen hb hw
  have hn16384 : 16384 ≤ n' := (le_max_left _ _).trans hn'
  have hnC : 2 ^ C_inc ≤ n' := (le_max_right _ _).trans hn'
  obtain ⟨_, _, _, hF⟩ := feasible_of_checkBranchFeasible hfeas
  set b := branchMaxFactorIncidence n' sys'
  set w := branchMaxFactorWidth n' sys'
  set β' := ParameterCheck.chooseBeta (Nat.clog 2 n') b w
  set r := ReplacementParams.numGroups n'
  set Q := ReplacementParams.numNodes n'
  set R := ReplacementParams.rowBound β' n'
  set q := (sysMaxDegree sys' * (R - 1)) * (sys'.length + 2 * n') / max 1 Q
  obtain ⟨_, hβ'_le⟩ := chooseBeta_le_succ_of_le_mul_clog_pow (by omega) hnC hb hw
  obtain ⟨c_meas, d_max, hc_meas, hd_max, hT_le⟩ := hT n' sys' hfeas hn16384
  have hr2 : 2 ≤ r := hF.two_le_numGroups
  have hR32 : 32 ≤ R := hF.thirtyTwo_le_rowBound
  have hRQ6 : 6 * R ≤ Q := hF.six_mul_rowBound_le_numNodes
  have hQ_pos : 1 ≤ Q := by omega
  have hvar_bal : 2 * Q * r ^ 2 ≤ n' := hF.var_balance
  have hQ_le_n : Q ≤ n' := by
    have hr_sq : 1 ≤ r ^ 2 := Nat.one_le_pow 2 r (by omega)
    calc Q ≤ 2 * Q * 1 := by omega
      _ ≤ 2 * Q * r ^ 2 := Nat.mul_le_mul_left (2 * Q) hr_sq
      _ ≤ n' := hvar_bal
  have hr_le_n : r ≤ n' := by
    have hr_sq : r ≤ r ^ 2 := by
      simpa only [pow_one] using Nat.pow_le_pow_right (by omega) (by decide : 1 ≤ 2)
    calc r = 1 * r := (one_mul r).symm
      _ ≤ (2 * Q) * r ^ 2 := Nat.mul_le_mul (by omega) hr_sq
      _ ≤ n' := hvar_bal
  have hrQ_le_n : r ^ Q ≤ n' := numGroups_pow_numNodes_le_self (by omega) (by omega)
  have hn_le_enc : n' ≤ (encPair encUnary encSys (n', sys')).length := by
    simp only [length_encPair, encUnary_apply, List.length_replicate]
    omega
  generalize hL_eq : (encPair encUnary encSys (n', sys')).length = L at hn_le_enc hT_le ⊢
  have hn_le_L : n' ≤ L := hn_le_enc
  -- Nat inequality reducing outer prefactors into `64 * (L + 1) ^ 3`
  set S_sp := Cslib.subsetPairCount n' q
  set D := ReplacementParams.auxDim n'
  have hD_eq : r ^ (2 * Q) = D := rfl
  have hS_eq : SubsetPairFold.subsetPairCount n' q = S_sp := SubsetPairFold.subsetPairCount_eq n' q
  have hS_pos : 1 ≤ S_sp := hS_eq ▸ SubsetPairFold.subsetPairCount_pos n' q
  have hM_pos : 1 ≤ (2 * D + 1) ^ c_meas := Nat.one_le_pow _ _ (by omega)
  have hG_pos : 1 ≤ 2 ^ d_max := Nat.one_le_two_pow
  set E_nat := S_sp * (2 * D + 1) ^ c_meas * 2 ^ d_max
  have hstep_nat :
      (r ^ Q + 1) + (Q + 1) * (SubsetPairFold.subsetPairCount n' q + 1) *
          ((2 * r ^ (2 * Q) + 1) ^ c_meas + 1) * (r * (2 ^ d_max + 1) + 1) ≤
        64 * (L + 1) ^ 3 * E_nat := by
    rw [hS_eq, hD_eq]
    exact step_prefactor_le (hrQ_le_n.trans hn_le_L) (hQ_le_n.trans hn_le_L) hr2
      (hr_le_n.trans hn_le_L) hS_pos hM_pos hG_pos
  -- Bound `E_nat` in ℝ via the three-term counting exponent and `rowCost`
  have hq_real : (q : ℝ) ≤ (c_deg : ℝ) * (n' : ℝ) * ((R : ℝ) / Q) := by
    have hmaxQ : max 1 Q = Q := Nat.max_eq_right hQ_pos
    have hnum : (sysMaxDegree sys' * (R - 1)) * (sys'.length + 2 * n') ≤ c_deg * n' * R := by
      have h1 : sysMaxDegree sys' * (R - 1) ≤ k_deg * R :=
        Nat.mul_le_mul hdeg (Nat.sub_le R 1)
      have h2 : sys'.length + 2 * n' ≤ (C_inc + 2) * n' := by linarith
      calc (sysMaxDegree sys' * (R - 1)) * (sys'.length + 2 * n')
          ≤ (k_deg * R) * ((C_inc + 2) * n') := Nat.mul_le_mul h1 h2
        _ = c_deg * n' * R := by ring
    have hq_le : q ≤ (c_deg * n' * R) / Q := by
      rw [show q = (sysMaxDegree sys' * (R - 1)) * (sys'.length + 2 * n') / Q by rw [← hmaxQ]]
      exact Nat.div_le_div_right hnum
    calc (q : ℝ) ≤ ((c_deg * n' * R : ℕ) : ℝ) / Q :=
          (Nat.cast_le.mpr hq_le).trans Nat.cast_div_le
      _ = (c_deg : ℝ) * (n' : ℝ) * ((R : ℝ) / Q) := by push_cast; ring
  have hS_exp := Cslib.ReplacementCounting.subsetPairCount_le_exp_mul_log_ratio
    (by omega : 1 ≤ R) (by omega : R ≤ Q) hq_real
  have hM_exp : (((2 * D + 1) ^ c_meas : ℕ) : ℝ) ≤
      Real.exp (((c_deg : ℝ) + 4) * (n' : ℝ) *
        (ReplacementParams.tau n' * Real.log (2 * (D : ℝ) + 1))) := by
    have hbase1 : (1 : ℝ) ≤ 2 * (D : ℝ) + 1 := by linarith [(Nat.cast_nonneg D : (0 : ℝ) ≤ D)]
    have hbase_pos : (0 : ℝ) < 2 * (D : ℝ) + 1 := by positivity
    have hlog_nn : 0 ≤ Real.log (2 * (D : ℝ) + 1) := Real.log_nonneg hbase1
    have htau_nn : 0 ≤ ReplacementParams.tau n' := hF.tau_pos.le
    calc (((2 * D + 1) ^ c_meas : ℕ) : ℝ)
        = (2 * (D : ℝ) + 1) ^ (c_meas : ℝ) := by
          rw [Nat.cast_pow, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one,
            Real.rpow_natCast]
      _ ≤ (2 * (D : ℝ) + 1) ^ (2 * ReplacementParams.tau n' * (n' : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le hbase1 hc_meas
      _ = Real.exp (Real.log (2 * (D : ℝ) + 1) * (2 * ReplacementParams.tau n' * (n' : ℝ))) :=
          Real.rpow_def_of_pos hbase_pos _
      _ ≤ Real.exp (((c_deg : ℝ) + 4) * (n' : ℝ) *
            (ReplacementParams.tau n' * Real.log (2 * (D : ℝ) + 1))) := by
          refine Real.exp_le_exp.mpr ?_
          have hnn : 0 ≤ (n' : ℝ) * (ReplacementParams.tau n' * Real.log (2 * (D : ℝ) + 1)) := by
            positivity
          have h2le : (2 : ℝ) ≤ (c_deg : ℝ) + 4 := by
            have : (0 : ℝ) ≤ c_deg := Nat.cast_nonneg _
            linarith
          calc Real.log (2 * (D : ℝ) + 1) * (2 * ReplacementParams.tau n' * (n' : ℝ))
              = 2 * ((n' : ℝ) * (ReplacementParams.tau n' * Real.log (2 * (D : ℝ) + 1))) := by ring
            _ ≤ ((c_deg : ℝ) + 4) *
                  ((n' : ℝ) * (ReplacementParams.tau n' * Real.log (2 * (D : ℝ) + 1))) :=
                mul_le_mul_of_nonneg_right h2le hnn
            _ = ((c_deg : ℝ) + 4) * (n' : ℝ) *
                  (ReplacementParams.tau n' * Real.log (2 * (D : ℝ) + 1)) := by ring
  have hG_exp : ((2 ^ d_max : ℕ) : ℝ) ≤
      Real.exp (((c_deg : ℝ) + 4) * (n' : ℝ) * (1 / (r : ℝ))) := by
    have hr_pos : (0 : ℝ) < r := Nat.cast_pos.mpr (by omega)
    have hd_real : (d_max : ℝ) ≤ 2 * (n' : ℝ) / r := by
      calc (d_max : ℝ) ≤ ((2 * n' / r : ℕ) : ℝ) := Nat.cast_le.mpr hd_max
        _ ≤ (((2 * n' : ℕ) : ℝ)) / r := Nat.cast_div_le (α := ℝ)
        _ = 2 * (n' : ℝ) / r := by push_cast; ring
    have hlog2_le : Real.log 2 ≤ 1 := by
      linarith [Real.log_le_sub_one_of_pos zero_lt_two]
    calc ((2 ^ d_max : ℕ) : ℝ)
        = (2 : ℝ) ^ (d_max : ℝ) := by rw [Nat.cast_pow, Nat.cast_ofNat, Real.rpow_natCast]
      _ ≤ (2 : ℝ) ^ (2 * (n' : ℝ) / r) := Real.rpow_le_rpow_of_exponent_le one_le_two hd_real
      _ = Real.exp (Real.log 2 * (2 * (n' : ℝ) / r)) := Real.rpow_def_of_pos two_pos _
      _ ≤ Real.exp (((c_deg : ℝ) + 4) * (n' : ℝ) * (1 / (r : ℝ))) := by
          refine Real.exp_le_exp.mpr ?_
          have hnn : 0 ≤ (n' : ℝ) * (1 / (r : ℝ)) := by positivity
          have h2le : 2 * Real.log 2 ≤ (c_deg : ℝ) + 4 := by
            have : (0 : ℝ) ≤ c_deg := Nat.cast_nonneg _
            linarith
          calc Real.log 2 * (2 * (n' : ℝ) / r)
              = (2 * Real.log 2) * ((n' : ℝ) * (1 / (r : ℝ))) := by ring
            _ ≤ ((c_deg : ℝ) + 4) * ((n' : ℝ) * (1 / (r : ℝ))) :=
                mul_le_mul_of_nonneg_right h2le hnn
            _ = ((c_deg : ℝ) + 4) * (n' : ℝ) * (1 / (r : ℝ)) := by ring
  have hE_exp : (E_nat : ℝ) ≤
      Real.exp (((c_deg : ℝ) + 4) * (n' : ℝ) * ReplacementParams.rowCost β' n') := by
    have hcast : (E_nat : ℝ) =
        (S_sp : ℝ) * (((2 * D + 1) ^ c_meas : ℕ) : ℝ) * ((2 ^ d_max : ℕ) : ℝ) := by
      simp only [E_nat, Nat.cast_mul]
    rw [hcast, ← ReplacementParams.threeTermExponent_eq_rowCost β' n']
    calc (S_sp : ℝ) * (((2 * D + 1) ^ c_meas : ℕ) : ℝ) * ((2 ^ d_max : ℕ) : ℝ)
        ≤ Real.exp (((c_deg : ℝ) + 4) * (n' : ℝ) * ((R : ℝ) / Q * Real.log (2 * (Q : ℝ) / R))) *
            Real.exp (((c_deg : ℝ) + 4) * (n' : ℝ) *
              (ReplacementParams.tau n' * Real.log (2 * (D : ℝ) + 1))) *
            Real.exp (((c_deg : ℝ) + 4) * (n' : ℝ) * (1 / (r : ℝ))) := by
          refine mul_le_mul (mul_le_mul hS_exp hM_exp (by positivity) (by positivity))
            hG_exp (by positivity) (by positivity)
      _ = Real.exp (((c_deg : ℝ) + 4) * (n' : ℝ) *
            Cslib.ReplacementCounting.threeTermExponent r Q R D (ReplacementParams.tau n')) := by
          rw [← Real.exp_add, ← Real.exp_add]
          congr 1; unfold Cslib.ReplacementCounting.threeTermExponent; ring
  have hscale_nn : 0 ≤ interpolationScale n' := by
    have hpre := ReplacementParams.two_mul_numNodes_mul_numGroups_le_interpolationScale
      hn16384 le_rfl
    exact (by positivity : (0 : ℝ) ≤ 2 * (Q : ℝ) * (r : ℝ)).trans hpre
  have hrc := hF.mul_rowCost_le_interpolationScale hn16384 (by omega) le_rfl
  have hβ_real : (β' : ℝ) + 3 ≤ (β : ℝ) + 4 := by
    have : (β' : ℝ) ≤ (β : ℝ) + 1 := by exact_mod_cast hβ'_le
    linarith
  have hexp_bound :
      ((c_deg : ℝ) + 4) * (n' : ℝ) * ReplacementParams.rowCost β' n' ≤
        (32896 * (c_deg + 4) * (β + 4) : ℕ) * interpolationScale n' := by
    calc ((c_deg : ℝ) + 4) * (n' : ℝ) * ReplacementParams.rowCost β' n'
        = ((c_deg : ℝ) + 4) * ((n' : ℝ) * ReplacementParams.rowCost β' n') := mul_assoc _ _ _
      _ ≤ ((c_deg : ℝ) + 4) * (32896 * ((β' : ℝ) + 3) * interpolationScale n') :=
          mul_le_mul_of_nonneg_left hrc (by positivity)
      _ ≤ ((c_deg : ℝ) + 4) * (32896 * ((β : ℝ) + 4) * interpolationScale n') := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact mul_le_mul_of_nonneg_right (by linarith) hscale_nn
      _ = ((32896 * (c_deg + 4) * (β + 4) : ℕ) : ℝ) * interpolationScale n' := by
          push_cast; ring
  have hE_pow2 : (E_nat : ℝ) ≤ (2 : ℝ) ^ ((A_br : ℝ) * interpolationScale n') := by
    have hexp_nn : 0 ≤ ((32896 * (c_deg + 4) * (β + 4) : ℕ) : ℝ) * interpolationScale n' :=
      mul_nonneg (Nat.cast_nonneg _) hscale_nn
    calc (E_nat : ℝ)
        ≤ Real.exp (((c_deg : ℝ) + 4) * (n' : ℝ) * ReplacementParams.rowCost β' n') := hE_exp
      _ ≤ Real.exp (((32896 * (c_deg + 4) * (β + 4) : ℕ) : ℝ) * interpolationScale n') :=
          Real.exp_le_exp.mpr (by linarith)
      _ ≤ (2 : ℝ) ^ (2 * (((32896 * (c_deg + 4) * (β + 4) : ℕ) : ℝ) * interpolationScale n')) :=
          exp_le_two_rpow_two_mul hexp_nn
      _ = (2 : ℝ) ^ ((A_br : ℝ) * interpolationScale n') := by
          congr 1; simp only [A_br]; push_cast; ring
  have hT_nat :
      T (n', sys') ≤ (64 * C_p * (L + 1) ^ (d_p + 3)) * E_nat := by
    calc T (n', sys')
        ≤ (64 * (L + 1) ^ 3 * E_nat) * (C_p * (L + 1) ^ d_p) :=
          hT_le.trans (Nat.mul_le_mul_right _ hstep_nat)
      _ = (64 * C_p * (L + 1) ^ (d_p + 3)) * E_nat := by ring
  calc (T (n', sys') : ℝ)
      ≤ (((64 * C_p * (L + 1) ^ (d_p + 3)) * E_nat : ℕ) : ℝ) := Nat.cast_le.mpr hT_nat
    _ = ((64 * C_p : ℕ) : ℝ) * (L + 1 : ℝ) ^ (d_p + 3) * (E_nat : ℝ) := by
        push_cast; ring
    _ ≤ ((64 * C_p : ℕ) : ℝ) * (L + 1 : ℝ) ^ (d_p + 3) *
          (2 : ℝ) ^ ((A_br : ℝ) * interpolationScale n') :=
        mul_le_mul_of_nonneg_left hE_pow2 (by positivity)

/-! ### 2. Native Certificates and Global Polynomial Workspace -/

/-! ### 2. Signed Measurement-Jet and Node-Jet Certificates (`0` `sorry`s) -/

section LoopCertificates

open ComputableTidilyInPolyTime

private def evalSignedMeasJet (dc : SubsetPairFold.DecodedPair × SubsetStepCtx) : JetRows :=
  let measCtx : MeasStepCtx :=
    (dc.2.1, dc.2.2.2.1, dc.2.2.2.2.1, dc.2.2.2.2.2.1, (dc.1.1, dc.1.2.1), dc.2.2.2.2.2.2)
  let measJet := (MeasurementFold.run measurementStepBody dc.2.2.1
    (measCtx, zeroJet dc.2.2.2.1.1 dc.2.2.2.1.2.1)).2.2.2
  if dc.1.2.2 then smulJet dc.2.2.2.1.1 dc.2.2.2.1.2.1 (-1) measJet else measJet

private theorem subsetPairStepBody_eq
    (inp : SubsetPairFold.DecodedPair × (SubsetStepCtx × JetRows)) :
    subsetPairStepBody inp =
      (inp.2.1, addJet inp.2.1.2.2.1.1 inp.2.1.2.2.1.2.1 inp.2.2
        (evalSignedMeasJet (inp.1, inp.2.1))) := rfl

private theorem exists_computableInO_signedMeasJet :
    ∃ P : SubsetPairFold.DecodedPair × SubsetStepCtx → ℕ,
      PolyBounded (fun dc => (encPair SubsetPairFold.encDecodedPair encSubsetStepCtx dc).length) P ∧
      ComputableInO evalSignedMeasJet
        (encPair SubsetPairFold.encDecodedPair encSubsetStepCtx) encJet
        (fun dc => ((2 * dc.2.2.1.2 + 1) ^ dc.2.2.1.1 + 1) *
          (dc.2.1.2.1 * (2 ^ maxGroupDim dc.2.1.1 dc.2.1.2.1 dc.2.2.2.2.2.1.1 + 1) + 1) * P dc)
        P := by
  obtain ⟨P₁, hP₁_pb, hPay⟩ := exists_computableInO_measPayload
  let eWC := encPair (encList encIntBin) encMeasStepCtx
  let cPay : NativeCertificate evalMeasPayload eWC (encOption encJet) := ⟨_, P₁, hPay⟩
  let eAcc := encPair encMeasStepCtx encJet
  let eMIn := encPair (encPair (encPair encUnary encNat) (encList encIntBin)) eAcc
  have hprojWC : ComputableInPolyTime
      (fun inp : ((ℕ × ℕ) × List ℤ) × (MeasStepCtx × JetRows) => (inp.1.2, inp.2.1)) eMIn eWC :=
    .of_tidy (((fst _ eAcc).snd').prod ((snd _ eAcc).fst'))
  have haddM : ComputableInPolyTime
      (fun q : (((ℕ × ℕ) × List ℤ) × (MeasStepCtx × JetRows)) × JetRows =>
        (q.1.2.1, addJet q.1.2.1.2.1.1 q.1.2.1.2.1.2.1 q.1.2.2 q.2))
      (encPair eMIn encJet) eAcc := by
    have hq1 := fst eMIn encJet; have hq2 := snd eMIn encJet
    have hctx := hq1.snd'.fst'; have hacc := hq1.snd'.snd'
    have hJ : ComputableInPolyTime
        (fun q : (((ℕ × ℕ) × List ℤ) × (MeasStepCtx × JetRows)) × JetRows => q.1.2.1.2.1.1)
        (encPair eMIn encJet) encUnary := by
      unfold encMeasStepCtx at hctx; exact .of_tidy (hctx.snd'.fst'.fst')
    have hℓ : ComputableInPolyTime
        (fun q : (((ℕ × ℕ) × List ℤ) × (MeasStepCtx × JetRows)) × JetRows => q.1.2.1.2.1.2.1)
        (encPair eMIn encJet) encUnary := by
      unfold encMeasStepCtx at hctx; exact .of_tidy (hctx.snd'.fst'.snd'.fst')
    exact (ComputableInPolyTime.of_tidy hctx).prod
      (computableInPolyTime_addJet hJ hℓ (.of_tidy hacc) (.of_tidy hq2))
  let cProjWC := NativeCertificate.ofPolyTime hprojWC
  let cAddM := NativeCertificate.ofPolyTime haddM
  let cNoM := NativeCertificate.snd
    (NativeCertificate.linear (ei := eMIn) (ComputableInO.of_eq fun _ => rfl))
  let cValM := cPay.comp cProjWC
  let cbM₀ := NativeCertificate.option cValM cNoM cAddM
  have hcProjWC := NativeCertificate.ofPolyTime_isPolynomial hprojWC
  have hcAddM := NativeCertificate.ofPolyTime_isPolynomial haddM
  have hcValM_sp : HasPolySpace cValM := hasPolySpace_comp hP₁_pb hcProjWC.2
  have hlenPay_pb := polyBounded_length_of_hasPolySpace hcValM_sp
  have hcbM_sp : HasPolySpace cbM₀ := by
    have hmaxY : PolyBounded (fun inp => (eMIn inp).length)
        (fun inp => (evalMeasPayload (inp.1.2, inp.2.1)).elim (cNoM.space inp)
          (fun y => cAddM.space (inp, y))) := by
      obtain ⟨ca, da, ha⟩ := hcAddM.2.exists_le
      have hlenIY : PolyBounded (fun inp => (eMIn inp).length)
          (fun inp => 2 * (eMIn inp).length +
            2 * (encOption encJet (evalMeasPayload (inp.1.2, inp.2.1))).length + 1) :=
        (((PolyBounded.const 2).mul .self).add
          ((PolyBounded.const 2).mul hlenPay_pb)).add (.const 1)
      refine (PolyBounded.self.add
        (NativeCertificate.polyBounded_pow_of_polyBounded hlenIY ca da)).mono fun inp => ?_
      cases h : evalMeasPayload (inp.1.2, inp.2.1) with
      | none =>
        dsimp only [cNoM]
        simp only [Option.elim_none, NativeCertificate.snd_space, NativeCertificate.linear_space]
        omega
      | some y =>
        simp only [Option.elim_some]
        have hiy : (encPair eMIn encJet (inp, y)).length ≤
            2 * (eMIn inp).length + 2 * (encOption encJet (some y)).length + 1 := by
          simp only [length_encPair, encOption_some, List.length_cons]; omega
        have hbound := (ha (inp, y)).trans
          (Nat.mul_le_mul_left ca (Nat.pow_le_pow_left (Nat.add_le_add_right hiy 1) da))
        dsimp only [cAddM]; omega
    exact ((((PolyBounded.const 2).mul hcValM_sp).add .self).add hmaxY).mono fun inp => by
      simp only [cbM₀, cValM, NativeCertificate.option_space, Function.comp_apply]; exact le_rfl
  let cbM : NativeCertificate measurementStepBody eMIn eAcc :=
    ⟨cbM₀.time, cbM₀.space, cbM₀.computes.of_enc_eq fun inp =>
      congrArg eAcc (measurementStepBody_eq inp)⟩
  let cVisit := MeasurementFold.visitCertificate cbM
  have hcPrep := NativeCertificate.ofPolyTime_isPolynomial
    (MeasurementFold.prepare_polyTime (encB := eAcc))
  have hcVisit_sp : HasPolySpace cVisit :=
    hasPolySpace_prod .self (hasPolySpace_comp hcbM_sp hcPrep.2)
  have hovM_pb : PolyBounded (fun inp => (eMIn inp).length)
      (fun inp => 2 * cProjWC.time inp + (eMIn inp).length +
        (evalMeasPayload (inp.1.2, inp.2.1)).elim (cNoM.time inp)
          (fun y => cAddM.time (inp, y))) := by
    obtain ⟨ca, da, ha⟩ := hcAddM.1.exists_le
    have hlenIY : PolyBounded (fun inp => (eMIn inp).length)
        (fun inp => 2 * (eMIn inp).length +
          2 * (encOption encJet (evalMeasPayload (inp.1.2, inp.2.1))).length + 1) :=
      (((PolyBounded.const 2).mul .self).add
        ((PolyBounded.const 2).mul hlenPay_pb)).add (.const 1)
    refine ((((PolyBounded.const 2).mul hcProjWC.1).add .self).add
      (PolyBounded.self.add
        (NativeCertificate.polyBounded_pow_of_polyBounded hlenIY ca da))).mono fun inp => ?_
    cases h : evalMeasPayload (inp.1.2, inp.2.1) with
    | none =>
      dsimp only [cProjWC, cNoM]
      simp only [Option.elim_none, NativeCertificate.snd_time, NativeCertificate.linear_time]
      omega
    | some y =>
      simp only [Option.elim_some]
      have hiy : (encPair eMIn encJet (inp, y)).length ≤
          2 * (eMIn inp).length + 2 * (encOption encJet (some y)).length + 1 := by
        simp only [length_encPair, encOption_some, List.length_cons]; omega
      have hbound := (ha (inp, y)).trans
        (Nat.mul_le_mul_left ca (Nat.pow_le_pow_left (Nat.add_le_add_right hiy 1) da))
      dsimp only [cProjWC, cAddM]; omega
  let eSt := encPair encNat (encPair (encPair encUnary encNat) eAcc)
  have hovV_pb : PolyBounded (fun st => (eSt st).length)
      (fun st => (eSt st).length + (NativeCertificate.ofPolyTime
        (MeasurementFold.prepare_polyTime (encB := eAcc))).time st +
        (let inp := ((st.2.1, Cslib.Radix.measurementValues st.2.1.1 st.2.1.2 st.1), st.2.2)
         2 * cProjWC.time inp + (eMIn inp).length +
          (evalMeasPayload (inp.1.2, inp.2.1)).elim (cNoM.time inp)
            (fun y => cAddM.time (inp, y)))) :=
    ((PolyBounded.self.add hcPrep.1).add
      (hovM_pb.comp (MeasurementFold.prepare_polyTime (encB := eAcc)).polyBounded_length))
  obtain ⟨cv, dv, hv_le⟩ := hovV_pb.exists_le
  let eDC := encPair SubsetPairFold.encDecodedPair encSubsetStepCtx
  let mkMCtx (dc : SubsetPairFold.DecodedPair × SubsetStepCtx) : MeasStepCtx :=
    (dc.2.1, dc.2.2.2.1, dc.2.2.2.2.1, dc.2.2.2.2.2.1, (dc.1.1, dc.1.2.1), dc.2.2.2.2.2.2)
  have hmkMCtx : ComputableInPolyTime mkMCtx eDC encMeasStepCtx := by
    have hdc1 := fst SubsetPairFold.encDecodedPair encSubsetStepCtx
    have hdc2 := snd SubsetPairFold.encDecodedPair encSubsetStepCtx
    unfold SubsetPairFold.encDecodedPair encSubsetStepCtx at hdc1 hdc2
    dsimp only [eDC]; unfold encMeasStepCtx mkMCtx
    exact .of_tidy (hdc2.fst'.prod (hdc2.snd'.snd'.fst'.prod (hdc2.snd'.snd'.snd'.fst'.prod
      (hdc2.snd'.snd'.snd'.snd'.fst'.prod ((hdc1.fst'.prod hdc1.snd'.fst').prod
        hdc2.snd'.snd'.snd'.snd'.snd')))))
  have hparDC : ComputableInPolyTime
      (fun dc : SubsetPairFold.DecodedPair × SubsetStepCtx => dc.2.2.1) eDC
      (encPair encUnary encNat) := by
    unfold eDC encSubsetStepCtx; exact .of_tidy ((snd _ _).snd'.fst')
  have hJ_dc : ComputableInPolyTime
      (fun dc : SubsetPairFold.DecodedPair × SubsetStepCtx => dc.2.2.2.1.1) eDC encUnary := by
    unfold eDC encSubsetStepCtx; exact .of_tidy ((snd _ _).snd'.snd'.fst'.fst')
  have hℓ_dc : ComputableInPolyTime
      (fun dc : SubsetPairFold.DecodedPair × SubsetStepCtx => dc.2.2.2.1.2.1) eDC encUnary := by
    unfold eDC encSubsetStepCtx; exact .of_tidy ((snd _ _).snd'.snd'.fst'.snd'.fst')
  have hinitDC : ComputableInPolyTime
      (fun dc : SubsetPairFold.DecodedPair × SubsetStepCtx =>
        (dc.2.2.1, (mkMCtx dc, zeroJet dc.2.2.2.1.1 dc.2.2.2.1.2.1)))
      eDC (encPair (encPair encUnary encNat) eAcc) :=
    hparDC.prod (hmkMCtx.prod (computableInPolyTime_zeroJet hJ_dc hℓ_dc))
  have hc_pb : PolyBounded (fun dc => (eDC dc).length) (fun dc => dc.2.2.1.1) :=
    (ComputableInPolyTime.of_tidy ((fst encUnary encNat).comp hparDC.tidy)).tidy.polyBounded
  have hDsz_pb : PolyBounded (fun dc => (eDC dc).length) (fun dc => (dc.2.2.1.2).size) :=
    ((ComputableInPolyTime.of_tidy ((snd encUnary encNat).comp hparDC.tidy)).polyBounded_length).mono
      fun dc => by simp only [Function.comp_apply, encNat_apply, Nat.size_eq_bits_len]; exact le_rfl
  let L_wc : SubsetPairFold.DecodedPair × SubsetStepCtx → ℕ := fun dc =>
    2 * (dc.2.2.1.1 * (2 * ((dc.2.2.1.2).size + 1) + 1)) + 2 * (encMeasStepCtx (mkMCtx dc)).length + 1
  have hLwc_pb : PolyBounded (fun dc => (eDC dc).length) L_wc :=
    (((PolyBounded.const 2).mul
      (hc_pb.mul (((PolyBounded.const 2).mul (hDsz_pb.add (.const 1))).add (.const 1)))).add
      ((PolyBounded.const 2).mul hmkMCtx.polyBounded_length)).add (.const 1)
  obtain ⟨cp1, dp1, hp1_le⟩ := hP₁_pb.exists_le
  obtain ⟨co1, do1, ho1_le⟩ := (polyBounded_length_of_hasPolySpace (c := cPay) hP₁_pb).exists_le
  let P_pay : SubsetPairFold.DecodedPair × SubsetStepCtx → ℕ := fun dc => cp1 * (L_wc dc + 1) ^ dp1
  have hPpay_pb := NativeCertificate.polyBounded_pow_of_polyBounded hLwc_pb cp1 dp1
  let L_opt : SubsetPairFold.DecodedPair × SubsetStepCtx → ℕ := fun dc => co1 * (L_wc dc + 1) ^ do1
  have hLopt_pb := NativeCertificate.polyBounded_pow_of_polyBounded hLwc_pb co1 do1
  have hJ_pb := hJ_dc.tidy.polyBounded
  have hℓ_pb := hℓ_dc.tidy.polyBounded
  let B_jet : SubsetPairFold.DecodedPair × SubsetStepCtx → ℕ := fun dc =>
    dc.2.2.2.1.1 * (2 * (dc.2.2.2.1.2.1 *
      (2 * ((dc.2.2.1.1 * ((dc.2.2.1.2).size + 1) + 1) + (L_opt dc + 1)) + 3)) + 1)
  have hBjet_pb : PolyBounded (fun dc => (eDC dc).length) B_jet :=
    hJ_pb.mul (((PolyBounded.const 2).mul (hℓ_pb.mul
      (((PolyBounded.const 2).mul
        (((hc_pb.mul (hDsz_pb.add (.const 1))).add (.const 1)).add
          (hLopt_pb.add (.const 1)))).add (.const 3)))).add (.const 1))
  let B_outer : SubsetPairFold.DecodedPair × SubsetStepCtx → ℕ := fun dc =>
    2 * (encPair encUnary encNat dc.2.2.1).length +
      2 * (2 * (encMeasStepCtx (mkMCtx dc)).length + 2 * B_jet dc + 1) + 1
  have hBout_pb : PolyBounded (fun dc => (eDC dc).length) B_outer :=
    (((PolyBounded.const 2).mul hparDC.polyBounded_length).add
      ((PolyBounded.const 2).mul
        ((((PolyBounded.const 2).mul hmkMCtx.polyBounded_length).add
          ((PolyBounded.const 2).mul hBjet_pb)).add (.const 1)))).add (.const 1)
  have hrun_eq (dc : SubsetPairFold.DecodedPair × SubsetStepCtx) (j : ℕ) :
      (IndexFold.run (MeasurementFold.visit measurementStepBody) j
        (dc.2.2.1, (mkMCtx dc, zeroJet dc.2.2.2.1.1 dc.2.2.2.1.2.1))).2 =
      (dc.2.2.1, (mkMCtx dc, (List.range j).foldl
        (fun acc i => (evalMeasPayload
          (Cslib.Radix.measurementValues dc.2.2.1.1 dc.2.2.1.2 i, mkMCtx dc)).elim acc
          (fun y => addJet dc.2.2.2.1.1 dc.2.2.2.1.2.1 acc y))
        (zeroJet dc.2.2.2.1.1 dc.2.2.2.1.2.1))) := by
    refine Prod.ext (MeasurementFold.prefix_parameters _ _ _ _) ?_
    rw [show (IndexFold.run (MeasurementFold.visit measurementStepBody) j
        (dc.2.2.1, (mkMCtx dc, zeroJet dc.2.2.2.1.1 dc.2.2.2.1.2.1))).2.2 =
        (MeasurementFold.runPrefix measurementStepBody dc.2.2.1 j
          (mkMCtx dc, zeroJet dc.2.2.2.1.1 dc.2.2.2.1.2.1)).2.2 from rfl,
      MeasurementFold.prefix_accumulator]
    simp only [measurementStepBody_eq]
    have hk := foldl_keep_fst
      (fun (m : MeasStepCtx) (acc : JetRows) (i : ℕ) =>
        (evalMeasPayload (Cslib.Radix.measurementValues dc.2.2.1.1 dc.2.2.1.2 i, m)).elim acc
          (fun y => addJet m.2.1.1 m.2.1.2.1 acc y))
      (mkMCtx dc) (List.range j) (zeroJet dc.2.2.2.1.1 dc.2.2.2.1.2.1)
    have hfn : (fun (pa : MeasStepCtx × JetRows) (i : ℕ) =>
        (evalMeasPayload (Cslib.Radix.measurementValues dc.2.2.1.1 dc.2.2.1.2 i, pa.1)).elim pa
          (fun y => (pa.1, addJet pa.1.2.1.1 pa.1.2.1.2.1 pa.2 y))) =
        (fun (pa : MeasStepCtx × JetRows) (i : ℕ) =>
          (pa.1, (evalMeasPayload (Cslib.Radix.measurementValues dc.2.2.1.1 dc.2.2.1.2 i, pa.1)).elim
            pa.2 (fun y => addJet pa.1.2.1.1 pa.1.2.1.2.1 pa.2 y))) :=
      funext fun pa => funext fun i => by cases evalMeasPayload _ <;> rfl
    rw [hfn]; exact hk
  have hB : ∀ dc j, j ≤ MeasurementFold.count dc.2.2.1 →
      (encPair (encPair encUnary encNat) eAcc
        (IndexFold.run (MeasurementFold.visit measurementStepBody) j
          (dc.2.2.1, (mkMCtx dc, zeroJet dc.2.2.2.1.1 dc.2.2.2.1.2.1))).2).length ≤
        B_outer dc := by
    intro dc j hj
    rw [hrun_eq dc j]
    have hjet_le : (encJet ((List.range j).foldl
        (fun acc i => (evalMeasPayload
          (Cslib.Radix.measurementValues dc.2.2.1.1 dc.2.2.1.2 i, mkMCtx dc)).elim acc
          (fun y => addJet dc.2.2.2.1.1 dc.2.2.2.1.2.1 acc y))
        (zeroJet dc.2.2.2.1.1 dc.2.2.2.1.2.1))).length ≤ B_jet dc := by
      have hf_le := length_encJetRows_foldl_optAddJet_le (N := MeasurementFold.count dc.2.2.1)
        (M := 2 ^ L_opt dc) hj fun i _ y hy j' _ u' _ => by
          have hw_len := MeasurementFold.length_values_le dc.2.2.1.1 dc.2.2.1.2 i
          have hwc_len : (eWC (Cslib.Radix.measurementValues dc.2.2.1.1 dc.2.2.1.2 i,
              mkMCtx dc)).length ≤ L_wc dc := by
            simp only [eWC, length_encPair, L_wc]; omega
          have hopt_len : (encOption encJet (some y)).length ≤ L_opt dc := by
            rw [← hy]
            exact (ho1_le _).trans (Nat.mul_le_mul_left co1
              (Nat.pow_le_pow_left (Nat.add_le_add_right hwc_len 1) do1))
          have hy_len : (encJet y).length ≤ L_opt dc := by
            simp only [encOption_some, List.length_cons] at hopt_len; omega
          exact (Nat.size_le.mp
            ((CommonCountingAccum.size_natAbs_rowEntry_le_length_encJetRows y j' u').trans
              hy_len)).le
      have hN_sz : (MeasurementFold.count dc.2.2.1).size ≤
          dc.2.2.1.1 * ((dc.2.2.1.2).size + 1) + 1 := by
        rw [Nat.size_eq_bits_len]; exact MeasurementFold.length_count_le _ _
      have hM_sz : (2 ^ L_opt dc).size ≤ L_opt dc + 1 := by
        rw [Nat.size_pow]; omega
      exact hf_le.trans (Nat.mul_le_mul_left _ (Nat.add_le_add_right (Nat.mul_le_mul_left 2
        (Nat.mul_le_mul_left _ (Nat.add_le_add_right (Nat.mul_le_mul_left 2
          (Nat.add_le_add hN_sz hM_sz)) 3))) 1))
    dsimp only [B_outer, eAcc]; rw [length_encPair, length_encPair]; dsimp only; omega
  let cCnt := MeasurementFold.clock.comp (.ofPolyTime hparDC)
  have hcCnt := NativeCertificate.comp_isPolynomial _ _ MeasurementFold.clock_isPolynomial
    (NativeCertificate.ofPolyTime_isPolynomial hparDC)
  let S_st : SubsetPairFold.DecodedPair × SubsetStepCtx → ℕ := fun dc =>
    2 * (encNat (MeasurementFold.count dc.2.2.1)).length + 1 + B_outer dc
  have hSst_pb := (((PolyBounded.const 2).mul (cCnt.polyTime hcCnt).polyBounded_length).add
    (.const 1)).add hBout_pb
  let P_cb : SubsetPairFold.DecodedPair × SubsetStepCtx → ℕ := fun dc => cv * (S_st dc + 1) ^ dv
  have hPcb_pb := NativeCertificate.polyBounded_pow_of_polyBounded hSst_pb cv dv
  obtain ⟨P_loop, hPloop_pb, hloop⟩ := computableInO_snd_indexFold cCnt (.ofPolyTime hinitDC)
    cVisit hcCnt (NativeCertificate.ofPolyTime_isPolynomial hinitDC) hcVisit_sp hBout_pb hB
    (fun dc => (dc.2.1.2.1 * (2 ^ maxGroupDim dc.2.1.1 dc.2.1.2.1 dc.2.2.2.2.2.1.1 + 1) + 1) *
      (2 * P_pay dc))
    P_cb hPcb_pb fun dc j hj hst_len => by
      set st := IndexFold.run (MeasurementFold.visit measurementStepBody) j
        (dc.2.2.1, (mkMCtx dc, zeroJet dc.2.2.2.1.1 dc.2.2.2.1.2.1))
      have hov := (hv_le st).trans
        (Nat.mul_le_mul_left cv (Nat.pow_le_pow_left (Nat.add_le_add_right hst_len 1) dv))
      have hst_idx : st.1 = j := IndexFold.run_index _ _ _
      have hst_2 : st.2 = _ := hrun_eq dc j
      have hw_len := MeasurementFold.length_values_le dc.2.2.1.1 dc.2.2.1.2 j
      have hwc_eq : (Cslib.Radix.measurementValues st.2.1.1 st.2.1.2 st.1, st.2.2.1) =
          (Cslib.Radix.measurementValues dc.2.2.1.1 dc.2.2.1.2 j, mkMCtx dc) := by
        rw [hst_idx, hst_2]
      have hwc_len : (eWC (Cslib.Radix.measurementValues dc.2.2.1.1 dc.2.2.1.2 j,
          mkMCtx dc)).length ≤ L_wc dc := by
        simp only [eWC, length_encPair, L_wc]; omega
      have hpay_t : cPay.time (Cslib.Radix.measurementValues st.2.1.1 st.2.1.2 st.1, st.2.2.1) ≤
          (dc.2.1.2.1 * (2 ^ maxGroupDim dc.2.1.1 dc.2.1.2.1 dc.2.2.2.2.2.1.1 + 1) + 1) *
            P_pay dc := by
        rw [hwc_eq]
        exact Nat.mul_le_mul_left _ ((hp1_le _).trans
          (Nat.mul_le_mul_left cp1 (Nat.pow_le_pow_left (Nat.add_le_add_right hwc_len 1) dp1)))
      dsimp only [cVisit, MeasurementFold.visitCertificate, cbM, cbM₀, cValM, eSt] at hov ⊢
      simp only [NativeCertificate.prod_time, NativeCertificate.comp_time,
        NativeCertificate.linear_time, NativeCertificate.option_time, Function.comp_apply] at hov ⊢
      dsimp only [P_cb, S_st] at hov ⊢; linarith
  let cMeasJet := NativeCertificate.snd (NativeCertificate.snd
    (⟨_, _, hloop⟩ : NativeCertificate _ eDC (encPair (encPair encUnary encNat) eAcc)))
  have hsign : ComputableInPolyTime
      (fun p : (SubsetPairFold.DecodedPair × SubsetStepCtx) × JetRows =>
        if p.1.1.2.2 then smulJet p.1.2.2.2.1.1 p.1.2.2.2.1.2.1 (-1) p.2 else p.2)
      (encPair eDC encJet) encJet := by
    have hp1 := fst eDC encJet; have hp2 := snd eDC encJet
    have hodd : ComputableTidilyInPolyTime
        (fun p : (SubsetPairFold.DecodedPair × SubsetStepCtx) × JetRows => p.1.1.2.2)
        (encPair eDC encJet) encBool := by
      unfold eDC SubsetPairFold.encDecodedPair; exact hp1.fst'.snd'.snd'
    have hsm := computableInPolyTime_smulJet (hJ_dc.comp (.of_tidy hp1))
      (hℓ_dc.comp (.of_tidy hp1)) (.of_tidy (const (-1))) (.of_tidy hp2)
    exact .of_tidy (hodd.ite' hsm.tidy hp2)
  let cSign := NativeCertificate.ofPolyTime hsign
  let cIdDC := NativeCertificate.linear (ei := eDC) (ComputableInO.of_eq fun _ => rfl)
  let cFinal := cSign.comp (cIdDC.prod cMeasJet)
  have hcSign := NativeCertificate.ofPolyTime_isPolynomial hsign
  have hspDCM : HasPolySpace (cIdDC.prod cMeasJet) := hasPolySpace_prod .self hPloop_pb
  have hcFinal_sp : HasPolySpace cFinal := hasPolySpace_comp hcSign.2 hspDCM
  have hlenDCM_pb := polyBounded_length_of_hasPolySpace hspDCM
  let measFn (dc : SubsetPairFold.DecodedPair × SubsetStepCtx) : JetRows :=
    (MeasurementFold.run measurementStepBody dc.2.2.1
      (mkMCtx dc, zeroJet dc.2.2.2.1.1 dc.2.2.2.1.2.1)).2.2.2
  let P_out : SubsetPairFold.DecodedPair × SubsetStepCtx → ℕ := fun dc =>
    2 * P_pay dc + P_loop dc + (eDC dc).length + cSign.time (dc, measFn dc) + cFinal.space dc
  have hPout_pb : PolyBounded (fun dc => (eDC dc).length) P_out :=
    ((((((PolyBounded.const 2).mul hPpay_pb).add hPloop_pb).add .self).add
      (hcSign.1.comp hlenDCM_pb)).add hcFinal_sp)
  refine ⟨P_out, hPout_pb, (cFinal.computes.of_enc_eq fun _ => rfl).mono_le (fun dc => ?_)
    fun dc => by dsimp only [P_out]; omega⟩
  set M_cnt := (2 * dc.2.2.1.2 + 1) ^ dc.2.2.1.1 + 1
  set G_cnt := dc.2.1.2.1 * (2 ^ maxGroupDim dc.2.1.1 dc.2.1.2.1 dc.2.2.2.2.2.1.1 + 1) + 1
  have hMG : 1 ≤ M_cnt * G_cnt := Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _)
  have hcnt_eq : MeasurementFold.count dc.2.2.1 + 1 = M_cnt := rfl
  have hstep1 := Nat.mul_le_mul_left M_cnt
    (absorb_step_add G_cnt (2 * P_pay dc) (P_loop dc) (Nat.succ_pos _))
  rw [← Nat.mul_assoc] at hstep1
  have hov1 := Nat.le_mul_of_pos_left ((eDC dc).length + cSign.time (dc, measFn dc)) hMG
  dsimp only [cFinal, cIdDC, cMeasJet, P_out]
  simp only [NativeCertificate.comp_time, NativeCertificate.prod_time, NativeCertificate.snd_time,
    NativeCertificate.linear_time, Function.comp_apply, hcnt_eq]
  change (eDC dc).length + M_cnt * (G_cnt * (2 * P_pay dc) + P_loop dc) +
      cSign.time (dc, measFn dc) ≤
    M_cnt * G_cnt * (2 * P_pay dc + P_loop dc + (eDC dc).length +
      cSign.time (dc, measFn dc) + cFinal.space dc)
  have hsum := Nat.add_le_add hstep1 hov1
  calc (eDC dc).length + M_cnt * (G_cnt * (2 * P_pay dc) + P_loop dc) +
        cSign.time (dc, measFn dc)
      ≤ M_cnt * G_cnt * (2 * P_pay dc + P_loop dc) +
          M_cnt * G_cnt * ((eDC dc).length + cSign.time (dc, measFn dc)) := by linarith
    _ = M_cnt * G_cnt * (2 * P_pay dc + P_loop dc + (eDC dc).length +
          cSign.time (dc, measFn dc)) := by ring
    _ ≤ M_cnt * G_cnt * (2 * P_pay dc + P_loop dc + (eDC dc).length +
          cSign.time (dc, measFn dc) + cFinal.space dc) :=
        Nat.mul_le_mul_left _ (by omega)

private theorem exists_computableInO_nodeJet :
    ∃ P : ℕ × SubsetStepCtx → ℕ,
      PolyBounded (fun qs => (encPair encUnary encSubsetStepCtx qs).length) P ∧
      ComputableInO
        (fun qs : ℕ × SubsetStepCtx =>
          (SubsetPairFold.run subsetPairStepBody qs.2.1.1 qs.1
            (qs.2, zeroJet qs.2.2.2.1.1 qs.2.2.2.1.2.1)).2)
        (encPair encUnary encSubsetStepCtx) encJet
        (fun qs => (SubsetPairFold.subsetPairCount qs.2.1.1 qs.1 + 1) *
          ((2 * qs.2.2.1.2 + 1) ^ qs.2.2.1.1 + 1) *
          (qs.2.1.2.1 * (2 ^ maxGroupDim qs.2.1.1 qs.2.1.2.1 qs.2.2.2.2.2.1.1 + 1) + 1) * P qs)
        P := by
  obtain ⟨P₂, hP₂_pb, hSignM⟩ := exists_computableInO_signedMeasJet
  let eDC := encPair SubsetPairFold.encDecodedPair encSubsetStepCtx
  let cSignM : NativeCertificate evalSignedMeasJet eDC encJet := ⟨_, P₂, hSignM⟩
  let eSubAcc := encPair encSubsetStepCtx encJet
  let eSubIn := encPair SubsetPairFold.encDecodedPair eSubAcc
  have hprojDC : ComputableInPolyTime
      (fun inp : SubsetPairFold.DecodedPair × (SubsetStepCtx × JetRows) => (inp.1, inp.2.1))
      eSubIn eDC :=
    .of_tidy ((fst _ eSubAcc).prod ((snd _ eSubAcc).fst'))
  have haddSub : ComputableInPolyTime
      (fun q : (SubsetPairFold.DecodedPair × (SubsetStepCtx × JetRows)) × JetRows =>
        (q.1.2.1, addJet q.1.2.1.2.2.1.1 q.1.2.1.2.2.1.2.1 q.1.2.2 q.2))
      (encPair eSubIn encJet) eSubAcc := by
    have hq1 := fst eSubIn encJet; have hq2 := snd eSubIn encJet
    have hctx := hq1.snd'.fst'; have hacc := hq1.snd'.snd'
    have hJ : ComputableInPolyTime
        (fun q : (SubsetPairFold.DecodedPair × (SubsetStepCtx × JetRows)) × JetRows =>
          q.1.2.1.2.2.1.1) (encPair eSubIn encJet) encUnary := by
      unfold encSubsetStepCtx at hctx; exact .of_tidy (hctx.snd'.snd'.fst'.fst')
    have hℓ : ComputableInPolyTime
        (fun q : (SubsetPairFold.DecodedPair × (SubsetStepCtx × JetRows)) × JetRows =>
          q.1.2.1.2.2.1.2.1) (encPair eSubIn encJet) encUnary := by
      unfold encSubsetStepCtx at hctx; exact .of_tidy (hctx.snd'.snd'.fst'.snd'.fst')
    exact (ComputableInPolyTime.of_tidy hctx).prod
      (computableInPolyTime_addJet hJ hℓ (.of_tidy hacc) (.of_tidy hq2))
  let cProjDC := NativeCertificate.ofPolyTime hprojDC
  let cAddSub := NativeCertificate.ofPolyTime haddSub
  let cIdSub := NativeCertificate.linear (ei := eSubIn) (ComputableInO.of_eq fun _ => rfl)
  let cbSub₀ := cAddSub.comp (cIdSub.prod (cSignM.comp cProjDC))
  let cbSub : NativeCertificate subsetPairStepBody eSubIn eSubAcc :=
    ⟨cbSub₀.time, cbSub₀.space, cbSub₀.computes.of_enc_eq fun inp =>
      congrArg eSubAcc (subsetPairStepBody_eq inp)⟩
  have hcProjDC := NativeCertificate.ofPolyTime_isPolynomial hprojDC
  have hcAddSub := NativeCertificate.ofPolyTime_isPolynomial haddSub
  have hspSubP : HasPolySpace (cIdSub.prod (cSignM.comp cProjDC)) :=
    hasPolySpace_prod .self (hasPolySpace_comp hP₂_pb hcProjDC.2)
  have hcbSub_sp : HasPolySpace cbSub := hasPolySpace_comp hcAddSub.2 hspSubP
  have hovSub_pb : PolyBounded (fun inp => (eSubIn inp).length)
      (fun inp => (eSubIn inp).length + cProjDC.time inp +
        cAddSub.time (inp, evalSignedMeasJet (inp.1, inp.2.1))) :=
    ((PolyBounded.self.add hcProjDC.1).add
      (hcAddSub.1.comp (polyBounded_length_of_hasPolySpace hspSubP)))
  obtain ⟨co, do_, ho_le⟩ := hovSub_pb.exists_le
  obtain ⟨cs, ds, hs_le⟩ := hcbSub_sp.exists_le
  let eQS := encPair encUnary encSubsetStepCtx
  have hn_qs : ComputableInPolyTime (fun qs : ℕ × SubsetStepCtx => qs.2.1.1) eQS encUnary := by
    unfold eQS encSubsetStepCtx; exact .of_tidy ((snd encUnary _).fst'.fst')
  have hq_qs : ComputableInPolyTime (fun qs : ℕ × SubsetStepCtx => qs.1) eQS encUnary :=
    .of_tidy (fst encUnary encSubsetStepCtx)
  have hJ_qs : ComputableInPolyTime (fun qs : ℕ × SubsetStepCtx => qs.2.2.2.1.1) eQS encUnary := by
    unfold eQS encSubsetStepCtx; exact .of_tidy ((snd encUnary _).snd'.snd'.fst'.fst')
  have hℓ_qs : ComputableInPolyTime (fun qs : ℕ × SubsetStepCtx => qs.2.2.2.1.2.1) eQS
      encUnary := by
    unfold eQS encSubsetStepCtx; exact .of_tidy ((snd encUnary _).snd'.snd'.fst'.snd'.fst')
  have hinitQS : ComputableInPolyTime
      (fun qs : ℕ × SubsetStepCtx => (qs.2, zeroJet qs.2.2.2.1.1 qs.2.2.2.1.2.1)) eQS eSubAcc :=
    (ComputableInPolyTime.of_tidy (snd encUnary encSubsetStepCtx)).prod
      (computableInPolyTime_zeroJet hJ_qs hℓ_qs)
  have hn_pb := hn_qs.tidy.polyBounded
  have hctx_pb := (ComputableInPolyTime.of_tidy (snd encUnary encSubsetStepCtx)).polyBounded_length
  let L_dc : ℕ × SubsetStepCtx → ℕ := fun qs =>
    2 * (6 * qs.2.1.1 + 7) + 2 * (encSubsetStepCtx qs.2).length + 1
  have hLdc_pb : PolyBounded (fun qs => (eQS qs).length) L_dc :=
    (((PolyBounded.const 2).mul (((PolyBounded.const 6).mul hn_pb).add (.const 7))).add
      ((PolyBounded.const 2).mul hctx_pb)).add (.const 1)
  obtain ⟨M_entry, hM_pb, hM_le⟩ := exists_natAbs_rowEntry_le_two_pow
    (polyBounded_length_of_hasPolySpace (c := cSignM) hP₂_pb) hLdc_pb
  obtain ⟨cp2, dp2, hp2_le⟩ := hP₂_pb.exists_le
  let P_sm : ℕ × SubsetStepCtx → ℕ := fun qs => cp2 * (L_dc qs + 1) ^ dp2
  have hPsm_pb := NativeCertificate.polyBounded_pow_of_polyBounded hLdc_pb cp2 dp2
  have hJ_pb := hJ_qs.tidy.polyBounded
  have hℓ_pb := hℓ_qs.tidy.polyBounded
  let B_jet : ℕ × SubsetStepCtx → ℕ := fun qs =>
    qs.2.2.2.1.1 * (2 * (qs.2.2.2.1.2.1 *
      (2 * ((2 * qs.2.1.1 + 1) + (M_entry qs + 1)) + 3)) + 1)
  have hBjet_pb : PolyBounded (fun qs => (eQS qs).length) B_jet :=
    hJ_pb.mul (((PolyBounded.const 2).mul (hℓ_pb.mul
      (((PolyBounded.const 2).mul
        ((((PolyBounded.const 2).mul hn_pb).add (.const 1)).add
          (hM_pb.add (.const 1)))).add (.const 3)))).add (.const 1))
  let B_sub : ℕ × SubsetStepCtx → ℕ := fun qs =>
    2 * (encSubsetStepCtx qs.2).length + 2 * B_jet qs + 1
  have hBsub_pb : PolyBounded (fun qs => (eQS qs).length) B_sub :=
    (((PolyBounded.const 2).mul hctx_pb).add ((PolyBounded.const 2).mul hBjet_pb)).add (.const 1)
  have hdp_len (n q i : ℕ) :
      (SubsetPairFold.encDecodedPair (SubsetPairFold.unrankSubsetPair n q i)).length =
        6 * n + 7 := by
    unfold SubsetPairFold.encDecodedPair
    rw [length_encPair, length_encPair]
    dsimp only
    rw [encBits_apply, encBits_apply, encBool_apply, List.length_singleton,
      SubsetPairFold.length_fst_unrankSubsetPair, SubsetPairFold.length_snd_unrankSubsetPair]
    omega
  have hB : ∀ qs j, j ≤ SubsetPairFold.subsetPairCount qs.2.1.1 qs.1 →
      (eSubAcc (SubsetPairFold.runPrefix subsetPairStepBody qs.2.1.1 qs.1 j
        (qs.2, zeroJet qs.2.2.2.1.1 qs.2.2.2.1.2.1)).2.2).length ≤ B_sub qs := by
    intro qs j hj
    rw [SubsetPairFold.runPrefix_acc]
    simp only [subsetPairStepBody_eq]
    rw [foldl_keep_fst
      (fun (s : SubsetStepCtx) (acc : JetRows) (i : ℕ) =>
        addJet s.2.2.1.1 s.2.2.1.2.1 acc
          (evalSignedMeasJet (SubsetPairFold.unrankSubsetPair qs.2.1.1 qs.1 i, s)))]
    have hf_le := length_encJetRows_foldl_optAddJet_le
      (J := qs.2.2.2.1.1) (ℓ := qs.2.2.2.1.2.1)
      (N := SubsetPairFold.subsetPairCount qs.2.1.1 qs.1) (M := 2 ^ M_entry qs)
      (f := fun i => some (evalSignedMeasJet (SubsetPairFold.unrankSubsetPair qs.2.1.1 qs.1 i,
        qs.2))) hj fun i _ y hy j' _ u' _ => by
          cases hy
          refine hM_le qs _ ?_ j' u'
          dsimp only [eDC, L_dc]; rw [length_encPair]; dsimp only; rw [hdp_len]; omega
    have hN_sz : (SubsetPairFold.subsetPairCount qs.2.1.1 qs.1).size ≤ 2 * qs.2.1.1 + 1 := by
      rw [← Nat.size_eq_bits_len, ← encNat_apply]
      exact SubsetPairFold.length_encNat_subsetPairCount_le _ _
    have hM_sz : (2 ^ M_entry qs).size ≤ M_entry qs + 1 := by rw [Nat.size_pow]; omega
    have hjet_le := hf_le.trans (Nat.mul_le_mul_left _ (Nat.add_le_add_right
      (Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left _ (Nat.add_le_add_right
        (Nat.mul_le_mul_left 2 (Nat.add_le_add hN_sz hM_sz)) 3))) 1))
    dsimp only [Option.elim_some] at hjet_le
    dsimp only [eSubAcc, B_sub]; rw [length_encPair]; dsimp only; omega
  let L_sub : ℕ × SubsetStepCtx → ℕ := fun qs => 2 * (6 * qs.2.1.1 + 7) + 2 * B_sub qs + 1
  have hLsub_pb : PolyBounded (fun qs => (eQS qs).length) L_sub :=
    (((PolyBounded.const 2).mul (((PolyBounded.const 6).mul hn_pb).add (.const 7))).add
      ((PolyBounded.const 2).mul hBsub_pb)).add (.const 1)
  let Q_sub : ℕ × SubsetStepCtx → ℕ := fun qs => cs * (L_sub qs + 1) ^ ds
  have hQsub_pb := NativeCertificate.polyBounded_pow_of_polyBounded hLsub_pb cs ds
  let Ov_sub : ℕ × SubsetStepCtx → ℕ := fun qs => co * (L_sub qs + 1) ^ do_
  have hOvsub_pb := NativeCertificate.polyBounded_pow_of_polyBounded hLsub_pb co do_
  let cn := NativeCertificate.ofPolyTime hn_qs
  let cq := NativeCertificate.ofPolyTime hq_qs
  let ci := NativeCertificate.ofPolyTime hinitQS
  have hcn := NativeCertificate.ofPolyTime_isPolynomial hn_qs
  have hcq := NativeCertificate.ofPolyTime_isPolynomial hq_qs
  have hci := NativeCertificate.ofPolyTime_isPolynomial hinitQS
  let R_sub : ℕ × SubsetStepCtx → ℕ := fun qs =>
    ((2 * qs.2.2.1.2 + 1) ^ qs.2.2.1.1 + 1) *
      (qs.2.1.2.1 * (2 ^ maxGroupDim qs.2.1.1 qs.2.1.2.1 qs.2.2.2.2.2.1.1 + 1) + 1) *
      P_sm qs + Ov_sub qs
  have hsp_run := SubsetPairFold.computableInO cn cq ci cbSub R_sub Q_sub B_sub
    (fun qs j hj => by
      set inp := (SubsetPairFold.unrankSubsetPair qs.2.1.1 qs.1 j,
        (SubsetPairFold.runPrefix subsetPairStepBody qs.2.1.1 qs.1 j
          (qs.2, zeroJet qs.2.2.2.1.1 qs.2.2.2.1.2.1)).2.2)
      have hinp_len : (eSubIn inp).length ≤ L_sub qs := by
        have hb := hB qs j hj
        dsimp only [eSubIn, inp, L_sub]; rw [length_encPair]; dsimp only; rw [hdp_len]; omega
      have hov := (ho_le inp).trans
        (Nat.mul_le_mul_left co (Nat.pow_le_pow_left (Nat.add_le_add_right hinp_len 1) do_))
      have hfst_eq : inp.2.1 = qs.2 := by
        dsimp only [inp]; rw [SubsetPairFold.runPrefix_acc]
        simp only [subsetPairStepBody_eq]
        rw [foldl_keep_fst (fun (s : SubsetStepCtx) (acc : JetRows) (i : ℕ) =>
          addJet s.2.2.1.1 s.2.2.1.2.1 acc
            (evalSignedMeasJet (SubsetPairFold.unrankSubsetPair qs.2.1.1 qs.1 i, s)))]
      have hdc_len : (eDC (inp.1, inp.2.1)).length ≤ L_dc qs := by
        rw [hfst_eq]; dsimp only [eDC, inp, L_dc]; rw [length_encPair]; dsimp only; rw [hdp_len]; omega
      have hsm_t : cSignM.time (inp.1, inp.2.1) ≤
          ((2 * qs.2.2.1.2 + 1) ^ qs.2.2.1.1 + 1) *
            (qs.2.1.2.1 * (2 ^ maxGroupDim qs.2.1.1 qs.2.1.2.1 qs.2.2.2.2.2.1.1 + 1) + 1) *
            P_sm qs := by
        dsimp only [cSignM, eDC] at hdc_len ⊢; rw [hfst_eq] at hdc_len ⊢
        exact Nat.mul_le_mul_left _ ((hp2_le _).trans
          (Nat.mul_le_mul_left cp2 (Nat.pow_le_pow_left (Nat.add_le_add_right hdc_len 1) dp2)))
      dsimp only [cbSub, cbSub₀, cIdSub, R_sub, Ov_sub, eSubIn, inp] at hov hsm_t ⊢
      simp only [NativeCertificate.comp_time, NativeCertificate.prod_time,
        NativeCertificate.linear_time, Function.comp_apply] at hov hsm_t ⊢
      linarith)
    (fun qs j hj => by
      have hinp_len : (eSubIn (SubsetPairFold.unrankSubsetPair qs.2.1.1 qs.1 j,
          (SubsetPairFold.runPrefix subsetPairStepBody qs.2.1.1 qs.1 j
            (qs.2, zeroJet qs.2.2.2.1.1 qs.2.2.2.1.2.1)).2.2)).length ≤ L_sub qs := by
        have hb := hB qs j hj
        dsimp only [eSubIn, L_sub]; rw [length_encPair]; dsimp only; rw [hdp_len]; omega
      exact (hs_le _).trans
        (Nat.mul_le_mul_left cs (Nat.pow_le_pow_left (Nat.add_le_add_right hinp_len 1) ds)))
    hB
  have hS_pb := SubsetPairFold.polyBounded_space_of_polyBounded cn cq ci hcn hcq hci
    hBsub_pb hQsub_pb
  let cSubRun : NativeCertificate _ eQS eSubAcc := ⟨_, _, hsp_run⟩
  let hd_ov : ℕ × SubsetStepCtx → ℕ := fun qs =>
    SubsetPairFold.decodeOverhead (qs.2.1.1 + qs.1)
  have hhd_pb : PolyBounded (fun qs => (eQS qs).length) hd_ov := by
    refine PolyBounded.mono ?_ fun qs =>
      Nat.le_add_left (SubsetPairFold.decodeOverhead (qs.2.1.1 + qs.1)) _
    exact hS_pb
  let P_out : ℕ × SubsetStepCtx → ℕ := fun qs =>
    P_sm qs + Ov_sub qs + hd_ov qs + B_sub qs +
      ((eQS qs).length + cn.time qs + cq.time qs + ci.time qs + hd_ov qs) +
      (NativeCertificate.snd cSubRun).space qs
  have hPout_pb : PolyBounded (fun qs => (eQS qs).length) P_out :=
    (((((((hPsm_pb.add hOvsub_pb).add hhd_pb).add hBsub_pb).add
      ((((PolyBounded.self.add hcn.1).add hcq.1).add hci.1).add hhd_pb)).add hS_pb)))
  refine ⟨P_out, hPout_pb, (NativeCertificate.snd cSubRun).computes.mono_le (fun qs => ?_)
    fun qs => by dsimp only [P_out, NativeCertificate.snd_space, cSubRun]; omega⟩
  set S_cnt := SubsetPairFold.subsetPairCount qs.2.1.1 qs.1 + 1
  set M_cnt := (2 * qs.2.2.1.2 + 1) ^ qs.2.2.1.1 + 1
  set G_cnt := qs.2.1.2.1 * (2 ^ maxGroupDim qs.2.1.1 qs.2.1.2.1 qs.2.2.2.2.2.1.1 + 1) + 1
  have hMG : 1 ≤ M_cnt * G_cnt := Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _)
  have hSMG : 1 ≤ S_cnt * (M_cnt * G_cnt) := Nat.mul_pos (Nat.succ_pos _) hMG
  have hstep1 := Nat.mul_le_mul_left S_cnt
    (absorb_step_add (M_cnt * G_cnt) (P_sm qs) (hd_ov qs + B_sub qs + Ov_sub qs) hMG)
  have hov1 := Nat.le_mul_of_pos_left
    ((eQS qs).length + cn.time qs + cq.time qs + ci.time qs + hd_ov qs) hSMG
  dsimp only [NativeCertificate.snd_time, cSubRun, R_sub, hd_ov, P_out] at hov1 hstep1 ⊢
  calc (eQS qs).length + cn.time qs + cq.time qs + ci.time qs +
        SubsetPairFold.decodeOverhead (qs.2.1.1 + qs.1) +
        S_cnt * (SubsetPairFold.decodeOverhead (qs.2.1.1 + qs.1) + B_sub qs +
          (M_cnt * G_cnt * P_sm qs + Ov_sub qs))
      ≤ ((eQS qs).length + cn.time qs + cq.time qs + ci.time qs +
          SubsetPairFold.decodeOverhead (qs.2.1.1 + qs.1)) +
        S_cnt * ((M_cnt * G_cnt) * P_sm qs +
          (SubsetPairFold.decodeOverhead (qs.2.1.1 + qs.1) + B_sub qs + Ov_sub qs)) := by linarith
    _ ≤ S_cnt * (M_cnt * G_cnt) *
          ((eQS qs).length + cn.time qs + cq.time qs + ci.time qs +
            SubsetPairFold.decodeOverhead (qs.2.1.1 + qs.1)) +
        S_cnt * ((M_cnt * G_cnt) *
          (P_sm qs + (SubsetPairFold.decodeOverhead (qs.2.1.1 + qs.1) + B_sub qs + Ov_sub qs))) :=
        Nat.add_le_add hov1 hstep1
    _ = S_cnt * M_cnt * G_cnt *
          (P_sm qs + Ov_sub qs + SubsetPairFold.decodeOverhead (qs.2.1.1 + qs.1) + B_sub qs +
            ((eQS qs).length + cn.time qs + cq.time qs + ci.time qs +
              SubsetPairFold.decodeOverhead (qs.2.1.1 + qs.1))) := by ring
    _ ≤ S_cnt * M_cnt * G_cnt *
          (P_sm qs + Ov_sub qs + SubsetPairFold.decodeOverhead (qs.2.1.1 + qs.1) + B_sub qs +
            ((eQS qs).length + cn.time qs + cq.time qs + ci.time qs +
              SubsetPairFold.decodeOverhead (qs.2.1.1 + qs.1)) +
            (NativeCertificate.snd cSubRun).space qs) := Nat.mul_le_mul_left _ (by omega)

end LoopCertificates

end Cslib.Complexity.SubexponentialSAT.SparsePolyCounter
