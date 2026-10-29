/-
Copyright (c) 2026 OpenAI, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.FineGrained.CountingScale
public import Complexity.Computability.Complexity.FineGrained.Reduction
public import Complexity.Logics.Propositional.CNF.ModelCount.DenseRelabel
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Bounds
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Internal.OCombinators

/-!
# From sublinear interpolation-scale counting to `satExponent k = 0`, `¬ETH`, and `¬SETH`

Bridges the sublinear exponent `Cslib.Complexity.SubexponentialSAT.interpolationScale` of
Section 6.4, Proposition 6.4 (pp. 43–44) [OpenAI2026ETH] and dense variable relabeling
(`Cslib.Logic.PL.CNF.denseRelabel`) to the fine-grained satisfiability endpoints
(`DecidableInSubexpTime (KSAT k) encCNF CNF.numVars`, `satExponent k = 0`, `¬ETH`, and `¬SETH`).

### Source relation and library adaptations

* **Proposition 6.4 (§6.4, pp. 43–44) vs. Theorem 1.1:** Proposition 6.4 states that for every fixed
  integer $k \ge 2$, there is a deterministic algorithm that, given a $k$-CNF formula $F$ on
  $n \ge 20$ variables with $m$ clauses, outputs the exact number of satisfying assignments of $F$
  in $\{0, 1\}^n$ in time $(n + m)^{O_k(1)} \cdot 2^{O_k(\rho(n))}$, where
  $\rho(n) = n (\log\log n)^2 / \sqrt{\log n}$ (formalized for all $n \in \mathbb{N}$ with the
  $+16$ domain shift as `interpolationScale n`), whereas Theorem 1.1 states the sharper
  single-$\log\log$ headline bound. This module uses Proposition 6.4's `interpolationScale`, which
  is already $o(n)$ (`isLittleO_interpolationScale`).
* **Library adaptations:** First-occurrence dense variable numbering
  (`CNF.denseRelabel φ = φ.relabel φ.distinctVars.idxOf`, mapping occurring variables onto
  `Finset.range φ.numVars` while preserving `φ.modelCount` as
  `φ.denseRelabel.modelCountOn (Finset.range φ.numVars)`) and the conditional complexity-class
  reduction wrappers below are library adaptations connecting a dense-variable model counter to
  `Cslib.Complexity`'s existing `KSAT`, `DecidableInSubexpTime`, `satExponent`, `ETH`, and `SETH`
  definitions. This module assumes such a dense counter as a hypothesis and does not construct it.

Specifically:
1. Any problem decidable in time `O(2 ^ (A₀ * interpolationScale (μ a)) * (|enc a| + 1) ^ d)` is
   `DecidableInSubexpTime` with respect to `μ` (`DecidableInSubexpTime.of_interpolationScale`,
   `DecidableInSubexpTime.of_computableInO_interpolationScale`).
2. Any model-counting routine `count : CNF ℕ → ℕ` that computes
   `ψ.modelCountOn (Finset.range ψ.numVars)` on dense width-`≤ k` formulas (`ψ.vars.toFinset =
   Finset.range ψ.numVars`) within time `O(2 ^ (A₀ * interpolationScale ψ.numVars) * (|ψ| + 1) ^ e)`
   yields `DecidableInSubexpTime (KSAT k) encCNF CNF.numVars` via polynomial-time dense relabeling
   and clause-width checking (`DecidableInSubexpTime.KSAT_of_dense_modelCount_interpolationScale`).
3. Subexponential-time decidability of `KSAT k` is equivalent to `satExponent k = 0`
   (`satExponent_eq_zero_iff_decidableInSubexpTime`), refutes `ETH` at `k = 3`
   (`not_ETH_of_decidableInSubexpTime`), and refutes `SETH` when established for all `k`
   (`not_SETH_of_forall_decidableInSubexpTime`).

## Main results

* `Cslib.Logic.PL.CNF.denseRelabel_mem_KSAT_iff`: dense relabeling preserves `KSAT k`.
* `Cslib.Complexity.DecidableInSubexpTime.of_interpolationScale`,
  `Cslib.Complexity.DecidableInSubexpTime.of_computableInO_interpolationScale`: subexponential
  time from `interpolationScale` runtime bounds.
* `Cslib.Complexity.DecidableInSubexpTime.KSAT_of_dense_modelCount_interpolationScale`:
  `DecidableInSubexpTime (KSAT k)` from a dense-variable model counter at `interpolationScale`.
* `Cslib.Complexity.satExponent_eq_zero_of_decidableInSubexpTime`,
  `Cslib.Complexity.satExponent_eq_zero_iff_decidableInSubexpTime`: `satExponent k = 0`.
* `Cslib.Complexity.not_ETH_of_decidableInSubexpTime`,
  `Cslib.Complexity.not_SETH_of_forall_decidableInSubexpTime`: refutation of `ETH` and `SETH`.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], Section 6.4,
  Proposition 6.4, pp. 43–44.
* [R. Impagliazzo, R. Paturi, *On the complexity of k-SAT*][ImpagliazzoPaturi2001]
-/

@[expose] public section

namespace Cslib.Logic.PL.CNF

open Cslib.Complexity

/-- Dense variable relabeling preserves membership in `KSAT k` for every `k` (including `k = 0, 1`,
empty formulas, and formulas with repeated literals or gaps in variable numbering). -/
@[simp]
theorem denseRelabel_mem_KSAT_iff {k : ℕ} {φ : CNF ℕ} :
    φ.denseRelabel ∈ KSAT k ↔ φ ∈ KSAT k := by
  simp only [KSAT, Set.mem_ofPred_eq, all_length_le_denseRelabel, satisfiable_denseRelabel]

end Cslib.Logic.PL.CNF

namespace Cslib.Complexity

open Cslib.Logic.PL Turing.MultiTapeTM SubexponentialSAT

/-! ### From `interpolationScale` bounds to `DecidableInSubexpTime` -/

/-- Any problem decidable in time `O(2 ^ (A₀ * interpolationScale (μ a)) * (|enc a| + 1) ^ d)` is
decidable in subexponential time in `μ`. -/
theorem DecidableInSubexpTime.of_interpolationScale {α : Type} {enc : α ↪ List Bool}
    {A : Set α} {μ : α → ℕ} {A₀ : ℝ} {d : ℕ}
    (h : DecidableInTimeO A enc (fun a =>
      (2 : ℝ) ^ (A₀ * interpolationScale (μ a)) * (((enc a).length : ℝ) + 1) ^ d)) :
    DecidableInSubexpTime A enc μ := by
  intro δ hδ
  obtain ⟨K, _, hK⟩ := exists_two_pow_mul_interpolationScale_le A₀ hδ
  refine ⟨d, h.mono ⌈K⌉₊ (fun a => ?_) fun a => by positivity⟩
  have hceil : K ≤ ⌈K⌉₊ := Nat.le_ceil K
  have h1 : (2 : ℝ) ^ (A₀ * interpolationScale (μ a)) ≤ ⌈K⌉₊ * (2 : ℝ) ^ (δ * μ a) :=
    (hK (μ a)).trans (mul_le_mul_of_nonneg_right hceil (by positivity))
  have h2 := mul_le_mul_of_nonneg_right h1
    (by positivity : (0 : ℝ) ≤ (((enc a).length : ℝ) + 1) ^ d)
  linarith

/-- If `f : α → Bool` decides `A` in `ComputableInO` time bounded by
`c * (2 ^ (A₀ * interpolationScale (μ a)) * (|enc a| + 1) ^ e) + c`, then `A` is decidable in
subexponential time in `μ`. -/
theorem DecidableInSubexpTime.of_computableInO_interpolationScale {α : Type} {enc : α ↪ List Bool}
    {A : Set α} {μ : α → ℕ} {f : α → Bool} {t : α → ℕ}
    (hf : ComputableInO f enc encBool t t) (hfA : ∀ a, a ∈ A ↔ f a = true)
    {A₀ : ℝ} {c e : ℕ}
    (ht : ∀ a, (t a : ℝ) ≤
      c * ((2 : ℝ) ^ (A₀ * interpolationScale (μ a)) * (((enc a).length : ℝ) + 1) ^ e) + c) :
    DecidableInSubexpTime A enc μ := by
  intro δ hδ
  obtain ⟨K, _, hK⟩ := exists_two_pow_mul_interpolationScale_le A₀ hδ
  refine DecidableInExpTime.of_computableInO hf hfA (c * ⌈K⌉₊ + c) e fun a => ?_
  refine (ht a).trans ?_
  have hceil : K ≤ ⌈K⌉₊ := Nat.le_ceil K
  have hX1 : (1 : ℝ) ≤ (2 : ℝ) ^ (δ * μ a) := Real.one_le_rpow (by norm_num) (by positivity)
  have hP1 : (1 : ℝ) ≤ (((enc a).length : ℝ) + 1) ^ e :=
    one_le_pow₀ (by linarith [(Nat.cast_nonneg (enc a).length : (0 : ℝ) ≤ _)])
  have hXP1 : (1 : ℝ) ≤ (2 : ℝ) ^ (δ * μ a) * (((enc a).length : ℝ) + 1) ^ e :=
    one_le_mul_of_one_le_of_one_le hX1 hP1
  have hcXP : (c : ℝ) ≤ (c : ℝ) * ((2 : ℝ) ^ (δ * μ a) * (((enc a).length : ℝ) + 1) ^ e) :=
    le_mul_of_one_le_right (Nat.cast_nonneg c) hXP1
  have h1 : (2 : ℝ) ^ (A₀ * interpolationScale (μ a)) ≤ ⌈K⌉₊ * (2 : ℝ) ^ (δ * μ a) :=
    (hK (μ a)).trans (mul_le_mul_of_nonneg_right hceil (by positivity))
  have h2 := mul_le_mul_of_nonneg_right h1
    (by positivity : (0 : ℝ) ≤ (((enc a).length : ℝ) + 1) ^ e)
  rw [mul_assoc] at h2
  have h3 := mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg c)
  push_cast
  linarith

/-! ### From dense-variable model counting to `DecidableInSubexpTime (KSAT k)` -/

private theorem computableInPolyTime_pos_nat :
    ComputableInPolyTime (fun n : ℕ => decide (0 < n)) encNat encBool :=
  ComputableInPolyTime.binary_lt.comp
    ((ComputableInPolyTime.const 0).prod ComputableInPolyTime.id')

/-- **From dense-variable model counting at `interpolationScale` to subexponential `k`-SAT.**
Suppose `count : CNF ℕ → ℕ` runs in time
`O(2 ^ (A₀ * interpolationScale ψ.numVars) * (|encCNF ψ| + 1) ^ e)` and computes the
declared-variable model count `ψ.modelCountOn (Finset.range ψ.numVars)` on every width-`≤ k`
formula `ψ` whose occurring variables are `Finset.range ψ.numVars`. Then `KSAT k` is decidable in
subexponential time in the number of occurring variables (`CNF.numVars`). -/
theorem DecidableInSubexpTime.KSAT_of_dense_modelCount_interpolationScale {k : ℕ}
    {count : CNF ℕ → ℕ} {t : CNF ℕ → ℕ}
    (hcount : ComputableInO count encCNF encNat t t)
    (hspec : ∀ ψ : CNF ℕ, (∀ c ∈ ψ, c.length ≤ k) →
      ψ.vars.toFinset = Finset.range ψ.numVars →
      count ψ = ψ.modelCountOn (Finset.range ψ.numVars))
    {A₀ : ℝ} {c e : ℕ}
    (ht : ∀ ψ : CNF ℕ, (t ψ : ℝ) ≤
      c * ((2 : ℝ) ^ (A₀ * interpolationScale ψ.numVars) * (((encCNF ψ).length : ℝ) + 1) ^ e) + c) :
    DecidableInSubexpTime (KSAT k) encCNF CNF.numVars := by
  obtain ⟨dpos, _, hpos⟩ := computableInPolyTime_pos_nat.exists_degree
  have hposO := hpos.inO
  obtain ⟨l, hl⟩ := hcount.length_le_time
  have hcomp : ComputableInO (fun ψ : CNF ℕ => decide (0 < count ψ)) encCNF encBool _ _ :=
    hposO.comp hcount
  let B : Set (CNF ℕ) := {ψ | decide (0 < count ψ) = true}
  have hB_subexp : DecidableInSubexpTime B encCNF CNF.numVars := by
    set A₁ : ℝ := max A₀ 0 * (dpos + 1)
    set E : ℕ := e * (dpos + 1)
    set C₀ : ℕ := (2 * c + 1) + (2 * l + 1) ^ dpos * (2 * c + 2) ^ dpos
    refine DecidableInSubexpTime.of_computableInO_interpolationScale hcomp (fun _ => Iff.rfl)
      (A₀ := A₁) (c := C₀) (e := E) fun ψ => ?_
    set L : ℝ := ((encCNF ψ).length : ℝ)
    set X₀ : ℝ := (2 : ℝ) ^ (max A₀ 0 * interpolationScale ψ.numVars)
    set P₀ : ℝ := (L + 1) ^ e
    have hX₀1 : 1 ≤ X₀ := Real.one_le_rpow (by norm_num)
      (mul_nonneg (le_max_right _ _) (interpolationScale_nonneg _))
    have hP₀1 : 1 ≤ P₀ :=
      one_le_pow₀ (by linarith [(Nat.cast_nonneg (encCNF ψ).length : (0 : ℝ) ≤ L)])
    have hXP1 : 1 ≤ X₀ * P₀ := one_le_mul_of_one_le_of_one_le hX₀1 hP₀1
    have hX_mono : (2 : ℝ) ^ (A₀ * interpolationScale ψ.numVars) ≤ X₀ :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num)
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (interpolationScale_nonneg _))
    have ht_le : (t ψ : ℝ) ≤ (2 * c + 1) * (X₀ * P₀) := by
      have h1 := ht ψ
      have h2 : (2 : ℝ) ^ (A₀ * interpolationScale ψ.numVars) * P₀ ≤ X₀ * P₀ :=
        mul_le_mul_of_nonneg_right hX_mono (by positivity)
      have h3 := mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg c)
      have h4 : (c : ℝ) ≤ c * (X₀ * P₀) := le_mul_of_one_le_right (Nat.cast_nonneg c) hXP1
      linarith
    have hlen_le : ((encNat (count ψ)).length : ℝ) + 1 ≤
        (2 * l + 1) * (2 * c + 2) * (X₀ * P₀) := by
      have h1 : ((encNat (count ψ)).length : ℝ) ≤ l * ((t ψ : ℝ) + 1) := by
        exact_mod_cast hl ψ
      have h2 : (t ψ : ℝ) + 1 ≤ (2 * c + 2) * (X₀ * P₀) := by linarith
      have h3 := mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg l)
      nlinarith
    have hpow_le : (((encNat (count ψ)).length : ℝ) + 1) ^ dpos ≤
        ((2 * l + 1) ^ dpos * (2 * c + 2) ^ dpos) * (X₀ * P₀) ^ dpos := by
      calc (((encNat (count ψ)).length : ℝ) + 1) ^ dpos
          ≤ ((2 * l + 1) * (2 * c + 2) * (X₀ * P₀)) ^ dpos :=
            pow_le_pow_left₀ (by positivity) hlen_le dpos
        _ = ((2 * l + 1) ^ dpos * (2 * c + 2) ^ dpos) * (X₀ * P₀) ^ dpos := by
            rw [mul_pow, mul_pow]
    have hXP_dpos : (X₀ * P₀) ^ dpos ≤ (X₀ * P₀) ^ (dpos + 1) :=
      pow_le_pow_right₀ hXP1 (Nat.le_succ dpos)
    have hXP_one : X₀ * P₀ ≤ (X₀ * P₀) ^ (dpos + 1) :=
      le_self_pow₀ hXP1 (Nat.succ_ne_zero dpos)
    have hXP_Rewrite : (X₀ * P₀) ^ (dpos + 1) =
        (2 : ℝ) ^ (A₁ * interpolationScale ψ.numVars) * (L + 1) ^ E := by
      rw [mul_pow]
      congr 1
      · simp only [X₀, A₁, ← Real.rpow_natCast]
        rw [← Real.rpow_mul (by norm_num)]
        congr 1
        push_cast
        ring
      · simp only [P₀, E, ← pow_mul]
    have htot : (t ψ : ℝ) + (((encNat (count ψ)).length : ℝ) + 1) ^ dpos ≤
        C₀ * ((X₀ * P₀) ^ (dpos + 1)) := by
      have ht_le' : (t ψ : ℝ) ≤ (c + 1 + c) * (X₀ * P₀) ^ (dpos + 1) := by
        have := mul_le_mul_of_nonneg_left hXP_one (by positivity : (0 : ℝ) ≤ 2 * c + 1)
        linarith
      have hpow_le' : (((encNat (count ψ)).length : ℝ) + 1) ^ dpos ≤
          ((2 * l + 1) ^ dpos * (2 * c + 2) ^ dpos) * (X₀ * P₀) ^ (dpos + 1) := by
        refine hpow_le.trans (mul_le_mul_of_nonneg_left hXP_dpos (by positivity))
      simp only [C₀]
      push_cast
      linarith
    push_cast at htot ⊢
    rw [← hXP_Rewrite]
    have hC₀ : (0 : ℝ) ≤ C₀ := Nat.cast_nonneg C₀
    linarith
  have hB'_subexp : DecidableInSubexpTime {φ : CNF ℕ | φ.denseRelabel ∈ B} encCNF CNF.numVars :=
    hB_subexp.of_reduction SAT.computableInPolyTime_denseRelabel (fun _ => Iff.rfl) (c := 1)
      fun φ => by rw [CNF.numVars_denseRelabel]; omega
  intro δ hδ
  have hKSAT_eq : KSAT k = {φ : CNF ℕ | (φ.all fun c => decide (c.length ≤ k)) = true} ∩
      {φ : CNF ℕ | φ.denseRelabel ∈ B} := by
    ext φ
    simp only [KSAT, B, Set.mem_inter_iff, Set.mem_ofPred_eq, List.all_eq_true, decide_eq_true_eq]
    refine and_congr_right fun hφ => ?_
    have hvars : φ.denseRelabel.vars.toFinset = Finset.range φ.denseRelabel.numVars := by
      rw [CNF.numVars_denseRelabel, CNF.vars_denseRelabel_toFinset]
    rw [hspec φ.denseRelabel ((CNF.all_length_le_denseRelabel φ).mpr hφ) hvars,
      CNF.numVars_denseRelabel, CNF.modelCountOn_denseRelabel, CNF.modelCount_pos_iff]
  rw [hKSAT_eq]
  exact (hB'_subexp δ hδ).inter (computableInPolyTime_all_length_le k) hδ.le

/-! ### Exponent and ETH/SETH consequences -/

/-- If `KSAT k` is decidable in subexponential time in the number of variables, then
`satExponent k = 0`. -/
theorem satExponent_eq_zero_of_decidableInSubexpTime {k : ℕ}
    (h : DecidableInSubexpTime (KSAT k) encCNF CNF.numVars) :
    satExponent k = 0 := by
  refine le_antisymm (le_of_not_gt fun hpos => ?_) (satExponent_nonneg k)
  exact not_decidableInExpTime_of_lt_satExponent (half_pos hpos).le (half_lt_self hpos)
    (h (satExponent k / 2) (half_pos hpos))

/-- `satExponent k = 0` if and only if `KSAT k` is decidable in subexponential time in the number
of variables. -/
theorem satExponent_eq_zero_iff_decidableInSubexpTime {k : ℕ} :
    satExponent k = 0 ↔ DecidableInSubexpTime (KSAT k) encCNF CNF.numVars := by
  refine ⟨fun h δ hδ => ?_, satExponent_eq_zero_of_decidableInSubexpTime⟩
  by_contra hndec
  have hle := le_satExponent_of_not_decidableInExpTime hndec
  linarith

/-- Subexponential-time decidability of 3-SAT refutes the Exponential Time Hypothesis (`¬ETH`). -/
theorem not_ETH_of_decidableInSubexpTime
    (h : DecidableInSubexpTime (KSAT 3) encCNF CNF.numVars) : ¬ETH := by
  rw [ETH_iff_satExponent_pos, satExponent_eq_zero_of_decidableInSubexpTime h]
  exact lt_irrefl 0

/-- Subexponential-time decidability of `k`-SAT for all `k` refutes the Strong Exponential Time
Hypothesis (`¬SETH`). -/
theorem not_SETH_of_forall_decidableInSubexpTime
    (h : ∀ k, DecidableInSubexpTime (KSAT k) encCNF CNF.numVars) : ¬SETH := by
  rintro hSETH
  obtain ⟨k, hk⟩ := hSETH (1 / 2) (by norm_num)
  have h12 : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
  rw [h12] at hk
  exact hk (h k (1 / 2) (by norm_num))

end Cslib.Complexity
