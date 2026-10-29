/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.ClauseSet.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Complexity.Logics.Propositional.ClauseSet.Sparsification.Bounds
import Complexity.Foundations.Data.Nat.Choose.Real

/-!
# The sparsification lemma

The sparsification lemma of Impagliazzo, Paturi and Zane [ImpagliazzoPaturiZane2001]: for every
width `k` and every `ε > 0` there is a constant `c` such that every formula in conjunctive normal
form of width `k` over `N` variables is the disjunction of at most `2 ^ (ε N)` formulas of width
`k` in which every variable occurs in at most `c` clauses, each accepting only inputs the original
accepts.

The proof follows Calabro, Impagliazzo and Paturi [CalabroImpagliazzoPaturi2006]. While some set
`H` of `h ≥ 1` literals is contained in at least `θ (c - h)` clauses of size `c > h`, branch on
whether `H` is satisfied: either add the clause `H`, or add every *petal* `C \ H`; choose `c`
smallest and then `h` largest, and remove clauses that strictly contain others. The clauses a step
introduces are new along its branch, and fewer than `2 θ (c - h)` new clauses of size `c`
containing a fixed clause of size `h` are present at once. With thresholds
`θ j = α (2 k α) ^ (2 j - 1)`, a branch has length at most `N k (2 k α) ^ (2 k)` and at most
`(k - 1) N / α` petal steps, so the number of leaves is a binomial tail, below `2 ^ (ε N)` once
`α` is large. The leaves have no heavy hearts, so every literal occurs in at most `∑_{c < k} θ c`
of their clauses.

## Main results

* `Cslib.Logic.PL.ClauseSet.Sparsification.exists_sum_choose_le`: the leaf count is below
  `2 ^ (ε N)` for a suitable parameter.
* `Cslib.Logic.PL.ClauseSet.sparsification`: the lemma for clause sets.
* `Cslib.Logic.PL.CNF.sparsification`: the lemma for formulas in conjunctive normal form.

## References

* [R. Impagliazzo, R. Paturi, F. Zane, *Which problems have strongly exponential
  complexity?*][ImpagliazzoPaturiZane2001]
* [C. Calabro, R. Impagliazzo, R. Paturi, *A duality between clause width and clause density for
  SAT*][CalabroImpagliazzoPaturi2006]
-/

@[expose] public section

universe u

namespace Cslib.Logic.PL

open Finset Filter

/-- **The leaves are few.** For every width `k ≥ 1` and every `ε > 0` there is a parameter `α ≥ 1`
for which the bound `∑_{j ≤ (k - 1) N / α} (N k X ^ (2 k) choose j)` on the number of leaves
(`ClauseSet.Sparsification.exists_leaves`) is at most `2 ^ (ε N)`, for every number `N` of
variables. -/
theorem ClauseSet.Sparsification.exists_sum_choose_le {k : ℕ} (hk : 1 ≤ k) {ε : ℝ} (hε : 0 < ε) :
    ∃ α : ℕ, 1 ≤ α ∧ ∀ N : ℕ,
      (∑ j ∈ range ((k - 1) * N / α + 1),
        (N * (k * Sparsification.base k α ^ (2 * k))).choose j : ℝ) ≤ 2 ^ (ε * N) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  -- the parameter `M` controls `exp (Λ / T)`
  obtain ⟨M, hM⟩ := exists_nat_gt (2 / (ε * Real.log 2))
  have hMpos : (0 : ℝ) < M := lt_trans (by positivity) hM
  have hM1 : 1 ≤ M := by exact_mod_cast hMpos
  have hMε : 1 / (M : ℝ) ≤ ε / 2 * Real.log 2 := by
    rw [div_le_iff₀ hMpos]
    have := (div_lt_iff₀ (by positivity : 0 < ε * Real.log 2)).mp hM
    nlinarith
  -- the parameter `α` controls `T ^ ρ`
  set r : ℝ := (2 : ℝ) ^ (ε / 2) with hr
  have hr1 : 1 < r := Real.one_lt_rpow (by norm_num) (by positivity)
  set C₀ : ℝ := ((M * k * (2 * k) ^ (2 * k) : ℕ) : ℝ) ^ (k - 1)
  obtain ⟨α, hα, hαbound⟩ :=
    Real.exists_one_le_and_mul_pow_le_pow C₀ (2 * k * (k - 1)) hr1
  refine ⟨α, hα, fun N => ?_⟩
  set X := Sparsification.base k α
  set Λ := N * (k * X ^ (2 * k))
  set ρ := (k - 1) * N / α
  set T := M * (k * X ^ (2 * k))
  have hX : 1 ≤ X := Sparsification.one_le_base hk hα
  have hT : 1 ≤ T := Nat.one_le_iff_ne_zero.mpr
    (Nat.mul_ne_zero (by omega) (Nat.mul_ne_zero (by omega) (pow_ne_zero _ (by omega))))
  have hTR1 : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hsum := sum_choose_le_exp_mul_pow Λ ρ (T : ℝ) hTR1
  -- `exp (Λ / T) ≤ 2 ^ (ε N / 2)`
  have hexp : Real.exp (Λ / T) ≤ (2 : ℝ) ^ (ε / 2 * N) := by
    have hΛT : (Λ : ℝ) / T = N / M := by
      have hKX : (0 : ℝ) < (k * X ^ (2 * k) : ℕ) := by
        exact_mod_cast Nat.mul_pos (by omega) (pow_pos (by omega) _)
      simp only [Λ, T, Nat.cast_mul] at hKX ⊢
      field_simp
    rw [hΛT, Real.rpow_def_of_pos (by norm_num)]
    refine Real.exp_le_exp.mpr ?_
    have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    calc (N : ℝ) / M = N * (1 / M) := by ring
      _ ≤ N * (ε / 2 * Real.log 2) := mul_le_mul_of_nonneg_left hMε hN
      _ = Real.log 2 * (ε / 2 * N) := by ring
  -- `T ^ ρ ≤ 2 ^ (ε N / 2)`
  have hTK : (T : ℝ) ^ (k - 1) ≤ r ^ α := by
    have hTeq : (T : ℝ) ^ (k - 1) = C₀ * (α : ℝ) ^ (2 * k * (k - 1)) := by
      simp only [T, X, Sparsification.base, C₀, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
      ring
    rw [hTeq]
    exact hαbound
  have hTρ : (T : ℝ) ^ ρ ≤ (2 : ℝ) ^ (ε / 2 * N) := by
    have hαρ : ρ * α ≤ (k - 1) * N := Nat.div_mul_le_self _ _
    have hpow : ((T : ℝ) ^ ρ) ^ α ≤ ((2 : ℝ) ^ (ε / 2 * N)) ^ α := by
      calc ((T : ℝ) ^ ρ) ^ α = (T : ℝ) ^ (ρ * α) := (pow_mul _ _ _).symm
        _ ≤ (T : ℝ) ^ ((k - 1) * N) := pow_le_pow_right₀ hTR1 hαρ
        _ = ((T : ℝ) ^ (k - 1)) ^ N := pow_mul _ _ _
        _ ≤ (r ^ α) ^ N := pow_le_pow_left₀ (by positivity) hTK N
        _ = ((2 : ℝ) ^ (ε / 2 * N)) ^ α := by
            rw [hr, ← pow_mul, ← Real.rpow_natCast, ← Real.rpow_natCast,
              ← Real.rpow_mul (by norm_num), ← Real.rpow_mul (by norm_num)]
            congr 1
            push_cast
            ring
    exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by omega)).mp hpow
  calc (∑ j ∈ range (ρ + 1), (Λ.choose j : ℝ))
      ≤ Real.exp (Λ / T) * (T : ℝ) ^ ρ := hsum
    _ ≤ (2 : ℝ) ^ (ε / 2 * N) * (2 : ℝ) ^ (ε / 2 * N) :=
        mul_le_mul hexp hTρ (by positivity) (by positivity)
    _ = 2 ^ (ε * N) := by
        rw [← Real.rpow_add (by norm_num)]
        ring_nf

/-- **The sparsification lemma** [Impagliazzo, Paturi and Zane][ImpagliazzoPaturiZane2001], **for
clause sets.** For every width `k` and every `ε > 0` there is a constant `c` such that every clause
set `φ` over `N` variables whose clauses have at most `k` literals has a family `Ψ` of at most
`2 ^ (ε N)` clause sets whose clauses have at most `k` literals, in each of which every variable
occurs in at most `c` clauses, each having only solutions of `φ`, and whose solutions together
cover those of `φ`. -/
theorem ClauseSet.sparsification (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ c : ℕ, ∀ (V : Type u) [Fintype V] [DecidableEq V] (φ : ClauseSet V),
      (∀ C ∈ φ, C.card ≤ k) →
      ∃ Ψ : Finset (ClauseSet V), (Ψ.card : ℝ) ≤ 2 ^ (ε * Fintype.card V) ∧
        (∀ ψ ∈ Ψ, (∀ C ∈ ψ, C.card ≤ k) ∧ (∀ v, ψ.occurrences v ≤ c) ∧
          ψ.solutions ⊆ φ.solutions) ∧
        φ.solutions ⊆ Ψ.biUnion ClauseSet.solutions := by
  set K := max k 1
  have hK : 1 ≤ K := le_max_right _ _
  obtain ⟨α, hα, hcount⟩ := Sparsification.exists_sum_choose_le hK hε
  have hθ := Sparsification.one_le_threshold hK hα
  refine ⟨2 * ∑ j ∈ range K, Sparsification.threshold K α j, fun V _ _ φ hφ => ?_⟩
  have hφK : ∀ C ∈ φ, C.card ≤ K := fun C hC => (hφ C hC).trans (le_max_left _ _)
  obtain ⟨Ψ, hcard, hleaves, hcover⟩ := Sparsification.exists_leaves hK hα φ hφK
  refine ⟨Ψ, (Nat.cast_le.mpr hcard).trans (by exact_mod_cast hcount (Fintype.card V)),
    fun ψ hψ => ?_, fun x hx => ?_⟩
  · obtain ⟨hsparse, hrefine, hsat⟩ := hleaves ψ hψ
    have hψK : ∀ C ∈ ψ, C.card ≤ K := fun C hC => by
      obtain ⟨D, hD, hCD⟩ := hrefine C hC
      exact (card_le_card hCD).trans (hφK D hD)
    refine ⟨fun C hC => ?_, Sparsification.occurrences_le_of_sparse hθ hsparse hψK, fun x hx => ?_⟩
    · obtain ⟨D, hD, hCD⟩ := hrefine C hC
      exact (card_le_card hCD).trans (hφ D hD)
    · exact mem_solutions.mpr (hsat x (mem_solutions.mp hx))
  · obtain ⟨ψ, hψ, hψx⟩ := hcover x (mem_solutions.mp hx)
    exact mem_biUnion.mpr ⟨ψ, hψ, mem_solutions.mpr hψx⟩

/-- **The sparsification lemma** [Impagliazzo, Paturi and Zane][ImpagliazzoPaturiZane2001]. For
every width `k` and every `ε > 0` there is a constant `c` such that every formula `φ` in
conjunctive normal form over `N` variables whose clauses have at most `k` literals is the
disjunction of at most `2 ^ (ε N)` such formulas, in each of which every variable occurs in at most
`c` clauses: each of them accepts only inputs that `φ` accepts, and every input that `φ` accepts is
accepted by one of them. -/
theorem CNF.sparsification (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ c : ℕ, ∀ (V : Type u) [Fintype V] [DecidableEq V] (φ : CNF V), (∀ cl ∈ φ, cl.length ≤ k) →
      ∃ Fs : List (CNF V), (Fs.length : ℝ) ≤ 2 ^ (ε * Fintype.card V) ∧
        (∀ F ∈ Fs, (∀ cl ∈ F, cl.length ≤ k) ∧ (∀ v, F.occurrences v ≤ c) ∧
          ∀ x, F.eval x = true → φ.eval x = true) ∧
        ∀ x, φ.eval x = true → ∃ F ∈ Fs, F.eval x = true := by
  obtain ⟨c, hc⟩ := ClauseSet.sparsification k hε
  refine ⟨c, fun V _ _ φ hφ => ?_⟩
  obtain ⟨Ψ, hcard, hleaves, hcover⟩ := hc V φ.toClauseSet fun C hC => by
    obtain ⟨cl, hcl, hle⟩ := CNF.exists_card_le_of_mem_toClauseSet hC
    exact hle.trans (hφ cl hcl)
  refine ⟨Ψ.toList.map ClauseSet.toCNF, by simpa using hcard, fun F hF => ?_, fun x hx => ?_⟩
  · obtain ⟨ψ, hψ, rfl⟩ := List.mem_map.mp hF
    obtain ⟨hwidth, hocc, hsol⟩ := hleaves ψ (Finset.mem_toList.mp hψ)
    refine ⟨fun cl hcl => ClauseSet.length_le_of_mem_toCNF hwidth hcl,
      fun v => (ClauseSet.occurrences_toCNF ψ v).trans_le (hocc v), fun x hx => ?_⟩
    rw [← CNF.sat_toClauseSet_iff, ← ClauseSet.mem_solutions]
    exact hsol (ClauseSet.mem_solutions.mpr ((ClauseSet.eval_toCNF_eq_true_iff ψ x).mp hx))
  · obtain ⟨ψ, hψ, hψx⟩ := Finset.mem_biUnion.mp
      (hcover (ClauseSet.mem_solutions.mpr ((CNF.sat_toClauseSet_iff φ x).mpr hx)))
    refine ⟨ψ.toCNF, List.mem_map.mpr ⟨ψ, Finset.mem_toList.mpr hψ, rfl⟩, ?_⟩
    exact (ClauseSet.eval_toCNF_eq_true_iff ψ x).mpr (ClauseSet.mem_solutions.mp hψx)

end Cslib.Logic.PL
