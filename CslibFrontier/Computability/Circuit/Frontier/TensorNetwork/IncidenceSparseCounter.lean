/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.IncidenceSharpResources
public import CslibFrontier.Computability.PolyTime.BooleanAnalysis.IncidenceBranching
public import CslibFrontier.Computability.PolyTime.BooleanAnalysis.SparsePolyCounter

/-!
# Executable high-incidence branching with the sharper native solver

The guard checks canonical, declared, degree-bounded input in polynomial binary time and rejects
invalid inputs. This makes the solver globally bounded by `2^n`, without an assumed counter
contract. The actual streaming high-incidence machine then uses the already verified incidence
solver at every reduced branch. The older interpolation counter is not called; its module
supplies only existing polynomial validation routines.

Correctness holds for all sizes on canonical, declared, degree-bounded systems. The resource
bound is eventual for fixed k,c, at most c*n equations and at most clog₂(n)^c monomials per
equation. There is no input incidence/occurrence restriction: those variables are branched on.
The model is unary declared size and binary variable indices. This does not yet compose the
source general-density CNF parity queries, sharper sparsification schedule or weighted frontend.

## Main definitions

* `Cslib.Circuits.Frontier.IncidenceNetwork.countSparse`: actual high-incidence streaming counter.

## Main results

* `Cslib.Circuits.Frontier.IncidenceNetwork.countSparse_eq_rootCount`: original count correctness.
* `Cslib.Circuits.Frontier.IncidenceNetwork.exists_countSparse_real_sharp_certificate`: actual
  single-iterated-log source exponent and polynomial original-input space.

## References

* [OpenAI2026ETH], Appendix D.3, Lemma D.2, PDF pp.54–57, high-incidence branching, sequential
  contraction sums and exponent absorption.
* [ChenJiangZhu2027], Lemma 3.2 (p.11) and Theorem 7.1 (pp.23–24), broader open endpoints.
-/

public section

namespace Cslib.Circuits.Frontier.IncidenceNetwork

open Cslib.GenericRAM Cslib.Complexity Turing.MultiTapeTM ComputableInPolyTime
open SubexponentialSAT SubexponentialSAT.SparsePolyCounter

/-- Actual polynomial validation, without parameters supplied by a caller as advice. -/
@[expose] def validSystem (k : ℕ) (p : ArrayInput) : Bool :=
  checkVarsLt p.1 p.2 && checkCanonicalSystem p.2 && decide (sysMaxDegree p.2 ≤ k)

private theorem validSystem_iff (k : ℕ) (p : ArrayInput) : validSystem k p = true ↔
    (∀ eq ∈ p.2, IsCanonicalEquation eq) ∧
    (∀ eq ∈ p.2, ∀ m ∈ eq, ∀ v ∈ m, v < p.1) ∧
    (∀ eq ∈ p.2, ∀ m ∈ eq, m.length ≤ k) := by
  simp only [validSystem, Bool.and_eq_true, decide_eq_true_eq,
    checkVarsLt_eq_true_iff, checkCanonicalSystem_eq_true_iff, sysMaxDegree_le_iff]
  tauto

/-- Certified incidence solver on valid input, and zero on invalid encodings of a system. -/
@[expose] noncomputable def countChecked (k : ℕ) (p : ArrayInput) : ℕ :=
  if validSystem k p then countOriginal k p else 0

/-- The guard preserves every input in the semantic domain of the incidence solver. -/
theorem countChecked_eq_rootCount {k n : ℕ} {sys : List (List (List ℕ))}
    (hc : ∀ eq ∈ sys, IsCanonicalEquation eq)
    (hv : ∀ eq ∈ sys, ∀ m ∈ eq, ∀ v ∈ m, v < n)
    (hk : ∀ eq ∈ sys, ∀ m ∈ eq, m.length ≤ k) :
    countChecked k (n, sys) = HeavyBranchFold.rootCount n sys := by
  rw [countChecked, ite_eq_left ((validSystem_iff k (n, sys)).mpr ⟨hc, hv, hk⟩)]
  exact countOriginal_eq_rootCount hc hv hk

/-- A global output bound, derived from validation and correctness, for the actual branch caller. -/
theorem countChecked_le (k : ℕ) (p : ArrayInput) : countChecked k p ≤ 2 ^ p.1 := by
  by_cases h : validSystem k p = true
  · obtain ⟨hc, hv, hk⟩ := (validSystem_iff k p).mp h
    rw [show p = (p.1, p.2) from rfl, countChecked_eq_rootCount hc hv hk]
    exact HeavyBranchFold.rootCount_le_two_pow _ _
  · simp [countChecked, h]

private theorem validSystem_polytime (k : ℕ) :
    ComputableInPolyTime (validSystem k) encArrayInput encBool := by
  have hc := computableInPolyTime_checkCanonicalSystem.comp
    (snd encUnary (encList (encList (encList encNat))))
  have hd := computableInPolyTime_sysMaxDegree.comp
    (snd encUnary (encList (encList (encList encNat))))
  exact bool_and' (bool_and' computableInPolyTime_checkVarsLt hc)
    (binary_le' (unary_to_binary.comp hd) (const k))

private noncomputable def guardCertificate (k : ℕ) :
    NativeCertificate (validSystem k) encArrayInput encBool :=
  NativeCertificate.ofPolyTime (validSystem_polytime k)

private noncomputable def checkedCertificate (k : ℕ)
    (cs : NativeCertificate (countOriginal k) encArrayInput encNat) :
    NativeCertificate (countChecked k) encArrayInput encNat :=
  NativeCertificate.branch (guardCertificate k) cs (NativeCertificate.const 0)

private theorem exists_checked_certificate (k c : ℕ) (hk : 1 ≤ k) :
    ∃ (cs : NativeCertificate (countChecked k) encArrayInput encNat) (A B d n₀ : ℕ),
      ∀ n, n₀ ≤ n → ∀ sys, IncidenceBranching.IsSparseBranch k c n sys →
        let L := (encArrayInput (n, sys)).length
        cs.time (n, sys) ≤ B * (L + 1) ^ d +
          A * (L + 1) ^ A * 2 ^ (A * Nat.logLogSqrtLogScale n) ∧
        cs.space (n, sys) ≤ B * (L + 1) ^ d + A * (L + 1) ^ A := by
  obtain ⟨base, A, n₀, hb⟩ := exists_countOriginal_sharp_certificate k c hk
  have hg := NativeCertificate.ofPolyTime_isPolynomial (validSystem_polytime k)
  obtain ⟨B, d, hBd⟩ := (hg.1.add hg.2).exists_le
  refine ⟨checkedCertificate k base, A, B, d, n₀, fun n hn sys hs => ?_⟩
  obtain ⟨ht, hspace⟩ := hb n hn sys hs
  have hguard := (validSystem_iff k (n, sys)).mpr ⟨hs.canonical, hs.vars_lt, hs.degree_le⟩
  have hcost : (guardCertificate k).time (n, sys) + (guardCertificate k).space (n, sys) ≤
      B * ((encArrayInput (n, sys)).length + 1) ^ d := hBd (n, sys)
  change (guardCertificate k).time (n, sys) +
      (if validSystem k (n, sys) then base.time (n, sys) else _) ≤ _ ∧
    (guardCertificate k).space (n, sys) +
      (if validSystem k (n, sys) then base.space (n, sys) else _) ≤ _
  rw [hguard]
  simp only [↓reduceIte]
  constructor <;> omega

/-- Compute the source high-incidence variables and stream all their assignments, using the
actual checked incidence solver at every reduced branch. -/
@[expose] noncomputable def countSparse (k : ℕ) (p : ArrayInput) : ℕ :=
  IncidenceBranching.count (fun n sys => countChecked k (n, sys)) p.1 p.2

/-- Original-system exactness of the actual high-incidence composition, at every declared size.
No density, incidence bound, supplied branch solver or desired output is a premise. -/
theorem countSparse_eq_rootCount {k n : ℕ} {sys : List (List (List ℕ))}
    (hc : ∀ eq ∈ sys, IsCanonicalEquation eq)
    (hv : ∀ eq ∈ sys, ∀ m ∈ eq, ∀ v ∈ m, v < n)
    (hk : ∀ eq ∈ sys, ∀ m ∈ eq, m.length ≤ k) :
    countSparse k (n, sys) = HeavyBranchFold.rootCount n sys := by
  apply IncidenceBranching.count_eq_rootCount hv
  intro n' sys' hb
  obtain ⟨vals, _, hred⟩ := hb
  obtain ⟨_, _, _, _, hc', hv'⟩ := HeavyBranchFold.prepareBranch_reduced_canonical
    (HeavyBranchFold.nodup_heavyVarList _ _ _)
    (fun _ hs => HeavyBranchFold.lt_of_mem_heavyVarList hs) hc hv hred
  exact countChecked_eq_rootCount hc' hv' (HeavyBranchFold.prepareBranch_reduced_degree_le hk hred)

/-- Actual high-incidence branching retains the single-iterated-log exponent and polynomial
original-input space on sparse listed systems. All branch costs are obtained from the verified
native incidence machine and computed reductions, not supplied runtime bounds. -/
theorem exists_countSparse_sharp_certificate (k c : ℕ) (hk : 1 ≤ k) :
    ∃ (cs : NativeCertificate (countSparse k) encArrayInput encNat) (D n₀ : ℕ),
      ∀ n, n₀ ≤ n → ∀ sys, IncidenceBranching.IsSparseSystem k c n sys →
        let L := (encArrayInput (n, sys)).length
        cs.time (n, sys) ≤ D * (L + 1) ^ D * 2 ^ (D * Nat.logLogSqrtLogScale n) ∧
          cs.space (n, sys) ≤ D * (L + 1) ^ D := by
  obtain ⟨leaf, A, B, d, n₀, hleaf⟩ := exists_checked_certificate k (2 * c + 4) hk
  obtain ⟨K, hK⟩ := IncidenceBranching.exists_count_certificate
  obtain ⟨cs, hcs⟩ := hK (fun n sys => countChecked k (n, sys)) leaf
    (fun n sys => countChecked_le k (n, sys))
  let D := K + B + 6 * A + d + 3
  refine ⟨cs, D, max (max (2 * n₀) 5) (2 ^ ((c + 1) * k)), fun n hn sys hs => ?_⟩
  have hn₀ : 2 * n₀ ≤ n := (le_max_left _ _).trans ((le_max_left _ _).trans hn)
  have hn5 : 5 ≤ n := (le_max_right _ _).trans ((le_max_left _ _).trans hn)
  have hnPow : 2 ^ ((c + 1) * k) ≤ n := (le_max_right _ _).trans hn
  let L := (encArrayInput (n, sys)).length
  let E := Nat.logLogSqrtLogScale n
  let R := B * (L + 1) ^ d + A * (L + 1) ^ A * 2 ^ (5 * A * E)
  let Q := B * (L + 1) ^ d + A * (L + 1) ^ A
  have hRQ : ∀ n' sys', IncidenceBranching.IsReducedBranch n sys n' sys' →
      leaf.time (n', sys') ≤ R ∧ leaf.space (n', sys') ≤ Q := by
    intro n' sys' hb
    obtain ⟨hs', hn2⟩ := IncidenceBranching.isSparseBranch_of_isReducedBranch hs hn5 hnPow hb
    have hn' : n₀ ≤ n' := by omega
    have hn'le : n' ≤ n := by
      have he := (IncidenceBranching.IsReducedBranch.le_two_mul (by omega) hb).1
      rw [he]
      exact Nat.sub_le _ _
    have hlen := IncidenceBranching.IsReducedBranch.length_enc_le hb
    obtain ⟨ht, hspace⟩ := hleaf n' hn' sys' hs'
    have hη := Nat.logLogSqrtLogScale_le_of_le hn'le (by omega)
    have hpoly (a : ℕ) : ((encArrayInput (n', sys')).length + 1) ^ a ≤ (L + 1) ^ a :=
      Nat.pow_le_pow_left (Nat.add_le_add_right hlen 1) a
    have hlow : B * ((encArrayInput (n', sys')).length + 1) ^ d ≤ B * (L + 1) ^ d :=
      Nat.mul_le_mul_left _ (hpoly d)
    have hhigh : A * ((encArrayInput (n', sys')).length + 1) ^ A *
        2 ^ (A * Nat.logLogSqrtLogScale n') ≤ A * (L + 1) ^ A * 2 ^ (5 * A * E) := by
      apply Nat.mul_le_mul (Nat.mul_le_mul_left _ (hpoly A))
      apply Nat.pow_le_pow_right (by decide)
      nlinarith
    exact ⟨ht.trans (Nat.add_le_add hlow hhigh),
      hspace.trans (Nat.add_le_add hlow (Nat.mul_le_mul_left _ (hpoly A)))⟩
  obtain ⟨ht, hspace⟩ := hcs n sys R Q hRQ
  have hE : 1 ≤ E := Nat.one_le_logLogSqrtLogScale (by omega)
  have hS : (IncidenceBranching.branchVars n sys).length ≤ E :=
    (IncidenceBranching.length_branchVars_le_div_sqrt_log sys (by omega)).trans
      (Nat.div_sqrt_log_two_le_logLogSqrtLogScale (by omega))
  have hfactor : 2 ^ (IncidenceBranching.branchVars n sys).length + 1 ≤ 2 ^ (E + 1) := by
    calc _ ≤ 2 ^ E + 2 ^ E :=
        Nat.add_le_add (Nat.pow_le_pow_right (by decide) hS) Nat.one_le_two_pow
      _ = _ := by rw [pow_succ]; omega
  have hKD : K ≤ D := by dsimp only [D]; omega
  have hBD : d ≤ D := by dsimp only [D]; omega
  have hAD : A ≤ D := by dsimp only [D]; omega
  have hcoef : K + B + A ≤ D := by dsimp only [D]; omega
  have hexp : 5 * A + 2 ≤ D := by dsimp only [D]; omega
  have hpoly (a : ℕ) (ha : a ≤ D) : (L + 1) ^ a ≤ (L + 1) ^ D :=
    Nat.pow_le_pow_right (by omega) ha
  have hinside : K * (L + 1) ^ K + R ≤
      (K + B + A) * (L + 1) ^ D * 2 ^ (5 * A * E) := by
    have hp (b a : ℕ) (ha : a ≤ D) : b * (L + 1) ^ a ≤
        b * (L + 1) ^ D * 2 ^ (5 * A * E) :=
      (Nat.mul_le_mul_left b (hpoly a ha)).trans (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _))
    have hh := Nat.mul_le_mul_right (2 ^ (5 * A * E)) (Nat.mul_le_mul_left A (hpoly A hAD))
    dsimp only [R]
    nlinarith [hp K K hKD, hp B d hBD]
  constructor
  · calc cs.time (n, sys) ≤ 2 ^ (E + 1) *
          ((K + B + A) * (L + 1) ^ D * 2 ^ (5 * A * E)) :=
          ht.trans (Nat.mul_le_mul hfactor hinside)
      _ = (K + B + A) * (L + 1) ^ D * 2 ^ (E + 1 + 5 * A * E) := by rw [pow_add]; ring
      _ ≤ D * (L + 1) ^ D * 2 ^ (D * E) :=
          Nat.mul_le_mul (Nat.mul_le_mul_right _ hcoef)
            (Nat.pow_le_pow_right (by decide) (by nlinarith [Nat.mul_le_mul_right E hexp]))
  · calc cs.space (n, sys) ≤ K * (L + 1) ^ K + Q := hspace
      _ ≤ (K + B + A) * (L + 1) ^ D := by
          dsimp only [Q]
          nlinarith [Nat.mul_le_mul_left K (hpoly K hKD),
            Nat.mul_le_mul_left B (hpoly d hBD), Nat.mul_le_mul_left A (hpoly A hAD)]
      _ ≤ _ := Nat.mul_le_mul_right _ hcoef

/-- The actual high-incidence counter satisfies the real base-two source exponent on sparse
polynomial systems. No additional iterated logarithm or counter/runtime oracle is assumed. -/
theorem exists_countSparse_real_sharp_certificate (k c : ℕ) (hk : 1 ≤ k) :
    ∃ (cs : NativeCertificate (countSparse k) encArrayInput encNat) (D n₀ : ℕ),
      ∀ n, n₀ ≤ n → ∀ sys, IncidenceBranching.IsSparseSystem k c n sys →
        let L := (encArrayInput (n, sys)).length
        (cs.time (n, sys) : ℝ) ≤ (D : ℝ) * (L + 1 : ℕ) ^ D *
          (2 : ℝ) ^ (((6 * D : ℕ) : ℝ) * Real.logLogSqrtLogScale n) ∧
          cs.space (n, sys) ≤ D * (L + 1) ^ D := by
  obtain ⟨cs, D, n₀, hcs⟩ := exists_countSparse_sharp_certificate k c hk
  refine ⟨cs, D, max n₀ 16, fun n hn sys hs => ?_⟩
  obtain ⟨ht, hspace⟩ := hcs n ((le_max_left _ _).trans hn) sys hs
  refine ⟨?_, hspace⟩
  have htR : (cs.time (n, sys) : ℝ) ≤ (D : ℝ) *
      ((encArrayInput (n, sys)).length + 1 : ℕ) ^ D *
      (2 : ℝ) ^ (D * Nat.logLogSqrtLogScale n) := by exact_mod_cast ht
  exact htR.trans (mul_le_mul_of_nonneg_left
    (Nat.two_pow_mul_logLogSqrtLogScale_le D ((le_max_right _ _).trans hn)) (by positivity))

end Cslib.Circuits.Frontier.IncidenceNetwork
