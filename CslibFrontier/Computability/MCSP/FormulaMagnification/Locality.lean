/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.OracleFormula
public import CslibFrontier.Computability.MCSP.FormulaMagnification

/-!
# Locality of the Oliveira–Santhanam formula construction

Draft module docstring.
-/

public section

namespace Cslib.Circuits.Boolean

open MCSP

/-- The oracle language of the Oliveira–Santhanam construction: the encoded `SuccinctMCSP`
yes-instances. -/
abbrev succinctMCSPOracle : Language Bool :=
  SuccinctMCSP.enc '' SuccinctMCSP

/-- The oracle gate on `succinctWord n S s` answers whether the sampled instance is a
`SuccinctMCSP` yes-instance. -/
theorem eval_query_succinctWord_eq_true_iff (n : ℕ) (S : Finset (BitString n)) (s : ℕ)
    (T : BitString (2 ^ n)) :
    (OracleFormula.query (succinctWord n S s)).eval (oracleInterpretation succinctMCSPOracle) T =
        true ↔
      SuccinctMCSP.Instance.ofFunction ((MCSP.truthTable n).symm T) S s ∈ SuccinctMCSP := by
  rw [OracleFormula.eval_query_eq_true_iff]
  change evalWord (succinctWord n S s) T ∈ succinctMCSPOracle ↔ _
  rw [evalWord_succinctWord]
  exact SuccinctMCSP.enc.injective.mem_set_image

open Classical in
/-- Per-length local form of the Oliveira–Santhanam construction. -/
theorem exists_oracleFormula_separating_approxMCSP {s₁ s₂ k : ℕ → ℕ} {n : ℕ}
    (hk : 1 ≤ k n) (hs : s₁ n ≤ s₂ n) :
    ∃ E : OracleFormula (2 ^ n),
      E.leafSize ≤ 2 ^ n * approxMCSPQueryEncLength n (s₂ n) (k n) ∧
      E.queryCount ≤ 2 ^ n ∧
      E.maxQueryArity ≤ approxMCSPQueryEncLength n (s₂ n) (k n) ∧
      E.adaptivity ≤ 1 ∧
      (∀ T : BitString (2 ^ n), List.ofFn T ∈ GapMCSP.yesSet s₁ →
        E.eval (oracleInterpretation succinctMCSPOracle) T = true) ∧
      (∀ T : BitString (2 ^ n), List.ofFn T ∈ ApproxMCSP.noSet s₂ k →
        E.eval (oracleInterpretation succinctMCSPOracle) T = false) := by
  obtain ⟨ωs, hyes, hno⟩ := exists_seeds_approxMCSP (s₁ := s₁) hk hs
    (card_computableFunctions_le_two_pow n (s₂ n))
  set ℓ := approxMCSPQueryEncLength n (s₂ n) (k n)
  let w : Fin (2 ^ n) → List (Formula signature (2 ^ n)) := fun j =>
    succinctWord n (Finset.univ.image (ωs j)) (s₂ n)
  have hw : ∀ j, (w j).length ≤ ℓ := fun j => by
    simp only [w, length_succinctWord]
    refine ofFunctionEncLength_le_approxMCSPQueryEncLength ?_
    exact Finset.card_image_le.trans (by simp)
  let Es : List (OracleFormula (2 ^ n)) := List.ofFn fun j => OracleFormula.query (w j)
  refine ⟨OracleFormula.all Es, ?_, ?_, ?_, ?_, fun T hT => ?_, fun T hT => ?_⟩
  · rw [OracleFormula.leafSize_all]
    refine (List.sum_le_length_nsmul _ ℓ ?_).trans (by simp [Es])
    intro x hx
    obtain ⟨E, hE, rfl⟩ := List.mem_map.mp hx
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hE
    exact (OracleFormula.leafSize_query_le
      fun _ h => leafSize_le_one_of_mem_succinctWord h).trans (hw j)
  · simp [Es, Function.comp_def]
  · refine OracleFormula.maxQueryArity_all_le fun E hE => ?_
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hE
    simpa using hw j
  · refine OracleFormula.adaptivity_all_le fun E hE => ?_
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hE
    simp
  · rw [OracleFormula.eval_all, decide_eq_true_eq]
    intro E hE
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hE
    exact (eval_query_succinctWord_eq_true_iff _ _ _ T).mpr (hyes T hT j)
  · rw [OracleFormula.eval_all, decide_eq_false_iff_not, not_forall]
    obtain ⟨j, hj⟩ := hno T hT
    refine ⟨OracleFormula.query (w j), fun h => hj ?_⟩
    exact (eval_query_succinctWord_eq_true_iff _ _ _ T).mp (h (List.mem_ofFn.mpr ⟨j, rfl⟩))

/-- A truth-table word has power-of-two length. -/
theorem exists_length_eq_two_pow_of_mem_truthTableLanguage {C : ∀ n, Set (BooleanFunction n)}
    {w : List Bool} (hw : w ∈ truthTableLanguage C) : ∃ n, w.length = 2 ^ n := by
  obtain ⟨n, h, -⟩ := hw
  exact ⟨n, h⟩

/-- Class form of the local Oliveira–Santhanam construction. -/
theorem localFormulaClass_approxMCSP {s₁ s₂ k : ℕ → ℕ} (hk : ∀ n, 1 ≤ k n)
    (hs : ∀ n, s₁ n ≤ s₂ n) :
    LocalFormulaClass (fun m => m)
      (fun m => approxMCSPQueryEncLength (Nat.log 2 m) (s₂ (Nat.log 2 m)) (k (Nat.log 2 m)))
      (fun _ => 1)
      (fun m => m * approxMCSPQueryEncLength (Nat.log 2 m) (s₂ (Nat.log 2 m)) (k (Nat.log 2 m)))
      (GapMCSP.yesSet s₁) (ApproxMCSP.noSet s₂ k) := by
  refine ⟨succinctMCSPOracle, fun m => ?_⟩
  by_cases hm : ∃ n, m = 2 ^ n
  · obtain ⟨n, rfl⟩ := hm
    obtain ⟨E, hS, hq, hℓ, ha, hyes, hno⟩ :=
      exists_oracleFormula_separating_approxMCSP (s₁ := s₁) (hk n) (hs n)
    simp only [Nat.log_pow Nat.one_lt_two]
    exact ⟨E, hS, hq, hℓ, ha, fun x hx => hyes x hx, fun x hx => hno x hx⟩
  · refine ⟨OracleFormula.tt, by simp, by simp, by simp, by simp, fun x hx => ?_, fun x hx => ?_⟩
    · exact absurd (by simpa using exists_length_eq_two_pow_of_mem_truthTableLanguage hx) hm
    · exact absurd (by simpa using exists_length_eq_two_pow_of_mem_truthTableLanguage hx) hm

/-- An explicit polynomial bound on the fan-in of the oracle gates, `poly(s * k)`, when
`n ≤ s`. -/
theorem approxMCSPQueryEncLength_le {n s k : ℕ} (hn : n ≤ s) (hk : 1 ≤ k) :
    approxMCSPQueryEncLength n s k ≤ 98 * (k * (s + 1)) ^ 3 := by
  have hlog := computableFunctionsLogBound_le_poly n s
  have hlog' : computableFunctionsLogBound n s + 2 ≤ 7 * (s + 1) ^ 2 := by nlinarith
  have hk' : 1 ≤ k * (s + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
  unfold approxMCSPQueryEncLength SuccinctMCSP.ofFunctionEncLength
  have h1 : k * (computableFunctionsLogBound n s + 2) ≤ 7 * k * (s + 1) ^ 2 := by nlinarith
  have h2 : 8 * n + 10 ≤ 10 * (s + 1) := by omega
  have h3 : k * (computableFunctionsLogBound n s + 2) * (8 * n + 10) ≤
      70 * (k * (s + 1)) ^ 3 := by
    calc k * (computableFunctionsLogBound n s + 2) * (8 * n + 10)
        ≤ (7 * k * (s + 1) ^ 2) * (10 * (s + 1)) := Nat.mul_le_mul h1 h2
      _ = 70 * k * (s + 1) ^ 3 := by ring
      _ ≤ 70 * (k * (s + 1)) ^ 3 := by
        rw [mul_pow, ← mul_assoc]
        exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.le_self_pow (by decide) k))
  have h4 : 4 * n + 3 + s ≤ 28 * (k * (s + 1)) ^ 3 := by
    have : s + 1 ≤ k * (s + 1) := Nat.le_mul_of_pos_left _ hk
    have : k * (s + 1) ≤ (k * (s + 1)) ^ 3 := Nat.le_self_pow (by decide) _
    omega
  omega

end Cslib.Circuits.Boolean
