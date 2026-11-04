/-
Copyright (c) 2026 Anton Kovsharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anton Kovsharov
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.Complexity.FineGrained.BruteForce
public import Complexity.Computability.GenericRAM.Native.BooleanFold
public import Complexity.Computability.PolyTime.CNF.SparsePolyCompile
public import Complexity.Foundations.BooleanAnalysis.SparseEquations
public import Complexity.Logics.Propositional.CNF.ModelCount.Declared
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Fold
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Complexity.Foundations.Data.BitString.ZModTwo
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Streaming polynomial-space exhaustive counting and finite-threshold fallback absorption

This module formalizes the streaming polynomial-space $2^n$ exhaustive counting fallbacks and their
constant-factor time absorption from §5.5 (Proof of Theorem 2.2, p. 39) and §6.4 (Proof of
Proposition 6.4, pp. 43–44) of [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH]:

1. **Streaming sparse `𝔽₂` polynomial system counter (`countSystemExhaustive`)**: iterates over all
   `0 ≤ idx < 2 ^ n` via `Cslib.GenericRAM.BooleanFold.run` without materializing `enumList n`,
   retaining only `((n, sys), Z)` with `Z ≤ idx ≤ 2 ^ n`, and increments `Z` whenever
   `Cslib.Complexity.evalSystem` vanishes on `(lowBits n idx).getD v false` (defaulting variable
   indices `v ≥ n` to `false`). On canonical equations with variables `< n`, this equals
   `Cslib.BitString.commonZeroCount`.
2. **Streaming declared-variable `CNF` model counter (`countCNFExhaustive`)**: iterates over all
   `0 ≤ idx < 2 ^ n` via `Cslib.GenericRAM.BooleanFold.run`, evaluating `φ : CNF ℕ` on
   `(lowBits n idx).getD v false` (defaulting variables `v ≥ n` to `false`), and equals
   `CNF.modelCountOn φ (Finset.range n)` (hence `2 ^ (n - φ.numVars) * φ.modelCount` whenever every
   occurring variable of `φ` is `< n`).
3. **Finite-threshold guard-fallback combinator and constant absorption**: combines a polynomial
   guard `ok : α → Bool`, a fast certificate `c_fast`, and an exhaustive fallback certificate
   `c_exhaust` via `NativeCertificate.branch` (evaluating only the selected branch), preserves
   polynomial workspace, and absorbs the `O(poly(|x|) * 2 ^ μ(x))` fallback runtime into a pure
   additive polynomial `C * (|ei x| + 1) ^ d` (and into `C' * (|ei x| + 1) ^ e * 2 ^ E(x)` for any
   nonnegative exponent `E(x)`) whenever `ok x = false → μ x < N₀`.

## Main definitions

* `Cslib.GenericRAM.ExhaustiveCountFallback.countStep`,
  `Cslib.GenericRAM.ExhaustiveCountFallback.countPredicateCertificate`: streaming step body and
  generic `NativeCertificate` for counting `n`-bit words satisfying a polynomial-time predicate
  along `BooleanFold`.
* `Cslib.GenericRAM.ExhaustiveCountFallback.countSystemPrefix`,
  `Cslib.GenericRAM.ExhaustiveCountFallback.countSystemExhaustive`,
  `Cslib.GenericRAM.ExhaustiveCountFallback.equationToFinset`,
  `Cslib.GenericRAM.ExhaustiveCountFallback.countSystemExhaustiveCertificate`: streaming sparse
  `𝔽₂` system counter, prefix state, `Fin n` monomial-family projection, and `NativeCertificate`.
* `Cslib.GenericRAM.ExhaustiveCountFallback.countCNFPrefix`,
  `Cslib.GenericRAM.ExhaustiveCountFallback.countCNFExhaustive`,
  `Cslib.GenericRAM.ExhaustiveCountFallback.countCNFExhaustiveCertificate`: streaming
  declared-variable `CNF ℕ` model counter, prefix state, and `NativeCertificate`.
* `Cslib.GenericRAM.ExhaustiveCountFallback.guardedBranchOfPolyTime`,
  `Cslib.GenericRAM.ExhaustiveCountFallback.guardedTargetCertificate`,
  `Cslib.GenericRAM.ExhaustiveCountFallback.guardedTargetOfPolyTime`: native guard-fallback
  certificate constructors via `NativeCertificate.branch`.

## Main results

* `Cslib.GenericRAM.ExhaustiveCountFallback.countSystemPrefix_invariant`,
  `Cslib.GenericRAM.ExhaustiveCountFallback.countSystemExhaustive_eq_card_filter`,
  `Cslib.GenericRAM.ExhaustiveCountFallback.countSystemExhaustive_eq_commonZeroCount`,
  `Cslib.GenericRAM.ExhaustiveCountFallback.countSystemExhaustive_nil`,
  `Cslib.GenericRAM.ExhaustiveCountFallback.countSystemExhaustive_eq_zero_of_nil_mem`: prefix
  bounds, `BitString n` filter equality, and `commonZeroCount` bridge for `countSystemExhaustive`.
* `Cslib.GenericRAM.ExhaustiveCountFallback.computableInPolyTime_evalSystem_word`,
  `Cslib.GenericRAM.ExhaustiveCountFallback.polyBounded_countSystemExhaustive_space`,
  `Cslib.GenericRAM.ExhaustiveCountFallback.exists_countSystemExhaustive_time_le`,
  `Cslib.GenericRAM.ExhaustiveCountFallback.computableInO_countSystemExhaustive`: polynomial-space
  and `O(poly(|x|) * 2 ^ n)`-time bounds for `countSystemExhaustive`.
* `Cslib.GenericRAM.ExhaustiveCountFallback.countCNFPrefix_invariant`,
  `Cslib.GenericRAM.ExhaustiveCountFallback.countCNFExhaustive_eq_card_filter`,
  `Cslib.GenericRAM.ExhaustiveCountFallback.countCNFExhaustive_eq_modelCountOn_range`,
  `Cslib.GenericRAM.ExhaustiveCountFallback.countCNFExhaustive_eq_mul_modelCount`,
  `Cslib.GenericRAM.ExhaustiveCountFallback.countCNFExhaustive_nil`,
  `Cslib.GenericRAM.ExhaustiveCountFallback.countCNFExhaustive_eq_zero_of_nil_mem`: prefix bounds
  and `CNF.modelCountOn` / `CNF.modelCount` bridges for `countCNFExhaustive`.
* `Cslib.GenericRAM.ExhaustiveCountFallback.computableInPolyTime_evalCNF_word`,
  `Cslib.GenericRAM.ExhaustiveCountFallback.polyBounded_countCNFExhaustive_space`,
  `Cslib.GenericRAM.ExhaustiveCountFallback.exists_countCNFExhaustive_time_le`,
  `Cslib.GenericRAM.ExhaustiveCountFallback.computableInO_countCNFExhaustive`: polynomial-space and
  `O(poly(|x|) * 2 ^ n)`-time bounds for `countCNFExhaustive`.
* `Cslib.GenericRAM.ExhaustiveCountFallback.ite_eq_of_agrees`,
  `Cslib.GenericRAM.ExhaustiveCountFallback.polyBounded_branch_space`,
  `Cslib.GenericRAM.ExhaustiveCountFallback.exists_branch_time_le_of_finite_threshold`,
  `Cslib.GenericRAM.ExhaustiveCountFallback.computableInO_of_guarded_fallback`,
  `Cslib.GenericRAM.ExhaustiveCountFallback.exists_nat_exp_bound_of_guarded_fallback`,
  `Cslib.GenericRAM.ExhaustiveCountFallback.exists_real_exp_bound_of_guarded_fallback`: pointwise
  agreement, polynomial workspace preservation, and finite-threshold fallback absorption.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], §5.5 (pp. 38–39) and §6.4
  (pp. 43–44)
-/

@[expose] public section

namespace Cslib.GenericRAM.ExhaustiveCountFallback

open Cslib.BitString Cslib.Complexity Cslib.Logic.PL Turing.MultiTapeTM

local notation "encSys" => encList (encList (encList encNat))

/-! ### Streaming Boolean-Cube Predicate Counter Infrastructure -/

/-- One streaming `BooleanFold` callback step for counting `n`-bit words satisfying `pred`: retains
the captured input `s.2.1 = (n, payload)` and increments the binary counter `s.2.2` when
`pred payload word` holds on the current decoded `n`-bit word `s.1.2`. -/
def countStep {P : Type} (pred : P → List Bool → Bool)
    (s : (ℕ × List Bool) × ((ℕ × P) × ℕ)) : (ℕ × P) × ℕ :=
  (s.2.1, if pred s.2.1.2 s.1.2 then s.2.2 + 1 else s.2.2)

private theorem ofFn_getD_false {n : ℕ} (σ : BitString n) (v : ℕ) :
    (List.ofFn σ).getD v false = if h : v < n then σ ⟨v, h⟩ else false := by
  by_cases h : v < n
  · rw [dite_eq_left h, List.getD_eq_getElem _ _ (by simp only [List.length_ofFn]; exact h),
      List.getElem_ofFn]
  · rw [dite_eq_right h, List.getD_eq_default _ _ (by simp only [List.length_ofFn]; omega)]

section StreamingCore

variable {P : Type} {encP : P ↪ List Bool}

private theorem foldl_countStep (pred : P → List Bool → Bool) (x : ℕ × P) (words : List (List Bool))
    (z₀ : ℕ) :
    words.foldl (fun acc word => countStep pred ((x.1, word), acc)) (x, z₀) =
      (x, z₀ + words.countP (pred x.2)) := by
  induction words generalizing z₀ with
  | nil => simp only [List.foldl_nil, List.countP_nil, Nat.add_zero]
  | cons w ws ih =>
    rw [List.foldl_cons, List.countP_cons]
    change ws.foldl (fun acc word => countStep pred ((x.1, word), acc))
      (x, if pred x.2 w then z₀ + 1 else z₀) = _
    cases h : pred x.2 w
    · simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
      exact ih z₀
    · simp only [↓reduceIte]
      rw [ih (z₀ + 1)]
      exact Prod.ext rfl (by omega)

private theorem prefix_payload_eq (pred : P → List Bool → Bool) (x : ℕ × P) (j : ℕ) :
    (BooleanFold.runPrefix (countStep pred) x.1 j (x, 0)).2.2.1 = x := by
  rw [BooleanFold.prefix_accumulator,
    ← List.foldl_map (f := lowBits x.1) (g := fun acc word => countStep pred ((x.1, word), acc)),
    foldl_countStep]

private theorem prefix_count_eq (pred : P → List Bool → Bool) (x : ℕ × P) (j : ℕ) :
    (BooleanFold.runPrefix (countStep pred) x.1 j (x, 0)).2.2.2 =
      ((List.range j).map (lowBits x.1)).countP (pred x.2) := by
  rw [BooleanFold.prefix_accumulator,
    ← List.foldl_map (f := lowBits x.1) (g := fun acc word => countStep pred ((x.1, word), acc)),
    foldl_countStep, Nat.zero_add]

private theorem prefix_count_le_index (pred : P → List Bool → Bool) (x : ℕ × P) (j : ℕ) :
    (BooleanFold.runPrefix (countStep pred) x.1 j (x, 0)).2.2.2 ≤ j := by
  rw [prefix_count_eq]
  exact List.countP_le_length.trans (by simp only [List.length_map, List.length_range, le_rfl])

private theorem run_count_eq_card_filter (pred : P → List Bool → Bool) (x : ℕ × P) :
    (BooleanFold.run (countStep pred) x.1 (x, 0)).2.2.2 =
      (Finset.univ.filter fun σ : BitString x.1 => pred x.2 (List.ofFn σ) = true).card := by
  rw [BooleanFold.run_accumulator, foldl_countStep, Nat.zero_add, countP_enumList]

open ComputableInPolyTime in
/-- If evaluating `pred` on `(payload, word)` is polynomial-time, then one streaming `countStep`
callback is polynomial-time. -/
theorem computableInPolyTime_countStep {pred : P → List Bool → Bool}
    (hpred : ComputableInPolyTime (fun q : P × List Bool => pred q.1 q.2) (encPair encP encBits)
      encBool) :
    ComputableInPolyTime (countStep pred)
      (encPair (encPair encUnary encBits) (encPair (encPair encUnary encP) encNat))
      (encPair (encPair encUnary encP) encNat) := by
  have hacc := snd (encPair encUnary encBits) (encPair (encPair encUnary encP) encNat)
  have hx := (fst (encPair encUnary encP) encNat).comp hacc
  have hp := (snd encUnary encP).comp hx
  have hw := (snd encUnary encBits).comp
    (fst (encPair encUnary encBits) (encPair (encPair encUnary encP) encNat))
  have hz := (snd (encPair encUnary encP) encNat).comp hacc
  have htest := hpred.comp (hp.prod hw)
  have hinc := binary_add.comp (hz.prod (const 1))
  exact hx.prod (htest.ite' hinc hz)

/-- Generic `NativeCertificate` for counting `n`-bit assignments satisfying `pred` via
`BooleanFold.certificate` without materializing `enumList n`. -/
noncomputable def countPredicateCertificate {pred : P → List Bool → Bool}
    (hpred : ComputableInPolyTime (fun q : P × List Bool => pred q.1 q.2) (encPair encP encBits)
      encBool) :
    NativeCertificate (fun x : ℕ × P => (BooleanFold.run (countStep pred) x.1 (x, 0)).2.2.2)
      (encPair encUnary encP) encNat :=
  NativeCertificate.snd (NativeCertificate.snd (NativeCertificate.snd
    (BooleanFold.certificate
      (NativeCertificate.linear (ComputableInO.fst encUnary encP))
      ((NativeCertificate.linear (.of_eq fun _ => rfl)).prod (NativeCertificate.const 0))
      (NativeCertificate.ofPolyTime (computableInPolyTime_countStep hpred)))))

private theorem length_prefix_accumulator_le (pred : P → List Bool → Bool) (x : ℕ × P) {j : ℕ}
    (hj : j ≤ 2 ^ x.1) :
    (encPair (encPair encUnary encP) encNat
      (BooleanFold.runPrefix (countStep pred) x.1 j (x, 0)).2.2).length ≤
      3 * (encPair encUnary encP x).length + 2 := by
  have hx_le : x.1 ≤ (encPair encUnary encP x).length := by
    simp only [length_encPair, encUnary_apply, List.length_replicate]
    omega
  have hz_le : (BooleanFold.runPrefix (countStep pred) x.1 j (x, 0)).2.2.2 ≤ 2 ^ x.1 :=
    (prefix_count_le_index pred x j).trans hj
  have hlen_z :
      (encNat (BooleanFold.runPrefix (countStep pred) x.1 j (x, 0)).2.2.2).length ≤ x.1 + 1 := by
    have hm : (encNat (BooleanFold.runPrefix (countStep pred) x.1 j (x, 0)).2.2.2).length ≤
        (encNat (2 ^ x.1)).length := by
      simpa [Nat.size_eq_bits_len] using Nat.size_le_size hz_le
    rw [BooleanFold.length_clock] at hm
    exact hm
  rw [length_encPair, prefix_payload_eq]
  omega

private theorem countPredicateCertificate_bounds {pred : P → List Bool → Bool}
    (hpred : ComputableInPolyTime (fun q : P × List Bool => pred q.1 q.2) (encPair encP encBits)
      encBool) :
    PolyBounded (fun x : ℕ × P => (encPair encUnary encP x).length)
      (countPredicateCertificate hpred).space ∧
    ∃ P_ex Q_ex : ℕ × P → ℕ,
      PolyBounded (fun x : ℕ × P => (encPair encUnary encP x).length) P_ex ∧
      PolyBounded (fun x : ℕ × P => (encPair encUnary encP x).length) Q_ex ∧
      ∀ x : ℕ × P, (countPredicateCertificate hpred).time x ≤ (2 ^ x.1 + 1) * P_ex x + Q_ex x := by
  obtain ⟨hspace, T, hT, htime⟩ := BooleanFold.certificate_bounds
    (NativeCertificate.linear_isPolynomial _)
    (NativeCertificate.prod_isPolynomial _ _ (NativeCertificate.linear_isPolynomial _)
      (NativeCertificate.const_isPolynomial _))
    (NativeCertificate.ofPolyTime_isPolynomial (computableInPolyTime_countStep hpred))
    (((PolyBounded.const 3).mul .self).add (.const 2))
    fun x j hj => length_prefix_accumulator_le pred x hj
  exact ⟨hspace, T, fun _ => 0, hT, .const 0, fun x => htime x⟩

end StreamingCore

/-! ### 1. Streaming Sparse `𝔽₂` Polynomial System Counter (§5.5, pp. 38–39) -/

/-- Prefix state after visiting the first `j` assignments `0 ≤ idx < j` of the streaming sparse `𝔽₂`
system counter on `(n, sys)`. Variable indices `v ≥ n` default to `false` via `List.getD`. -/
def countSystemPrefix (x : ℕ × List (List (List ℕ))) (j : ℕ) :
    ℕ × (ℕ × ((ℕ × List (List (List ℕ))) × ℕ)) :=
  BooleanFold.runPrefix
    (countStep fun sys word => evalSystem sys (fun v => word.getD v false)) x.1 j (x, 0)

/-- **Streaming polynomial-space $2^n$ sparse `𝔽₂` polynomial system counter** (§5.5, p. 39):
iterates over `0 ≤ idx < 2 ^ n` via `BooleanFold.run` without materializing `enumList n`, keeping
live state `((n, sys), Z)` and incrementing `Z` whenever every equation in `sys` evaluates to
`false` (`0 ∈ 𝔽₂`) under `(lowBits n idx).getD v false` (variables `v ≥ n` default to `false`). -/
def countSystemExhaustive (x : ℕ × List (List (List ℕ))) : ℕ :=
  (BooleanFold.run
    (countStep fun sys word => evalSystem sys (fun v => word.getD v false)) x.1 (x, 0)).2.2.2

/-- Project a sparse equation `eq : List (List ℕ)` onto `Finset (Finset (Fin n))` by intersecting
each monomial with `{0, …, n - 1}`. -/
def equationToFinset (n : ℕ) (eq : List (List ℕ)) : Finset (Finset (Fin n)) :=
  (eq.map fun m => Finset.univ.filter fun j : Fin n => j.1 ∈ m).toFinset

/-- At every prefix `j`, the retained payload in `countSystemPrefix x j` equals `x = (n, sys)`. -/
@[simp] theorem countSystemPrefix_payload (x : ℕ × List (List (List ℕ))) (j : ℕ) :
    (countSystemPrefix x j).2.2.1 = x :=
  prefix_payload_eq _ x j

/-- At every prefix `j`, the running count `Z` equals the number of indices `idx < j` whose decoded
`n`-bit word satisfies `evalSystem`. -/
theorem countSystemPrefix_count_eq (x : ℕ × List (List (List ℕ))) (j : ℕ) :
    (countSystemPrefix x j).2.2.2 =
      ((List.range j).map (lowBits x.1)).countP
        (fun word => evalSystem x.2 (fun v => word.getD v false)) :=
  prefix_count_eq _ x j

/-- Unconditional prefix count bound `Z ≤ j` for `countSystemPrefix`. -/
theorem countSystemPrefix_le_index (x : ℕ × List (List (List ℕ))) (j : ℕ) :
    (countSystemPrefix x j).2.2.2 ≤ j :=
  prefix_count_le_index _ x j

/-- **Prefix invariant `Z ≤ j ≤ 2 ^ n`** for `countSystemPrefix` along the `2 ^ n` traversal. -/
theorem countSystemPrefix_invariant (x : ℕ × List (List (List ℕ))) {j : ℕ} (hj : j ≤ 2 ^ x.1) :
    (countSystemPrefix x j).2.2.2 ≤ j ∧ j ≤ 2 ^ x.1 :=
  ⟨countSystemPrefix_le_index x j, hj⟩

/-- `countSystemExhaustive (n, sys)` equals the cardinality of the `BitString n` assignments whose
decoded word `(List.ofFn σ).getD v false` satisfies `evalSystem sys`. -/
theorem countSystemExhaustive_eq_card_filter (n : ℕ) (sys : List (List (List ℕ))) :
    countSystemExhaustive (n, sys) =
      (Finset.univ.filter fun σ : BitString n =>
        evalSystem sys (fun v => (List.ofFn σ).getD v false) = true).card :=
  run_count_eq_card_filter _ (n, sys)

private theorem monomialSum_equationToFinset_eq_zero_iff {n : ℕ} {eq : List (List ℕ)}
    (heq : IsCanonicalEquation eq) (hvars : ∀ m ∈ eq, ∀ v ∈ m, v < n) (σ : BitString n) :
    monomialSum (ZMod 2) (equationToFinset n eq) σ = 0 ↔
      evalMonomialList eq (fun v => (List.ofFn σ).getD v false) = false := by
  let f : List ℕ → Finset (Fin n) := fun m => Finset.univ.filter fun j : Fin n => j.1 ∈ m
  have hnd_f : (eq.map f).Nodup := by
    refine heq.1.map_on fun m₁ hm₁ m₂ hm₂ h => (heq.2 m₁ hm₁).eq_of_toFinset_eq (heq.2 m₂ hm₂) ?_
    ext v
    simp only [List.mem_toFinset]
    constructor <;> intro hv
    · have hvn : v < n := hvars m₁ hm₁ v hv
      have hmem : (⟨v, hvn⟩ : Fin n) ∈ f m₁ :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩
      rw [h] at hmem
      exact (Finset.mem_filter.mp hmem).2
    · have hvn : v < n := hvars m₂ hm₂ v hv
      have hmem : (⟨v, hvn⟩ : Fin n) ∈ f m₂ :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩
      rw [← h] at hmem
      exact (Finset.mem_filter.mp hmem).2
  have hnd_s : (eq.map List.toFinset).Nodup :=
    heq.1.map_on fun m₁ hm₁ m₂ hm₂ h => (heq.2 m₁ hm₁).eq_of_toFinset_eq (heq.2 m₂ hm₂) h
  have hterm (m : List ℕ) (hm : m ∈ eq) :
      monomial (ZMod 2) (f m) σ =
        monomial (ZMod 2) m.toFinset (fun v => (List.ofFn σ).getD v false) := by
    rw [monomial_apply, monomial_apply]
    have hiff : (∀ j ∈ f m, σ j = true) ↔
        (∀ v ∈ m.toFinset, (List.ofFn σ).getD v false = true) := by
      constructor
      · intro hj v hv
        have hvm : v ∈ m := List.mem_toFinset.mp hv
        have hvn : v < n := hvars m hm v hvm
        rw [ofFn_getD_false, dite_eq_left hvn]
        exact hj ⟨v, hvn⟩ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvm⟩)
      · intro hv j hj
        have hjm : j.1 ∈ m := (Finset.mem_filter.mp hj).2
        have hget := hv j.1 (List.mem_toFinset.mpr hjm)
        rwa [ofFn_getD_false, dite_eq_left j.isLt] at hget
    by_cases h1 : ∀ j ∈ f m, σ j = true
    · rw [ite_eq_left h1, ite_eq_left (hiff.mp h1)]
    · rw [ite_eq_right h1, ite_eq_right (fun h2 => h1 (hiff.mpr h2))]
  have hsum : monomialSum (ZMod 2) (equationToFinset n eq) σ =
      bitVal (ZMod 2) (evalMonomialList eq (fun v => (List.ofFn σ).getD v false)) := by
    rw [monomialSum, equationToFinset, List.sum_toFinset _ hnd_f,
      bitVal_evalMonomialList_eq_sum_monomial heq, List.sum_toFinset _ hnd_s,
      List.map_map, List.map_map]
    exact congrArg List.sum (List.map_congr_left fun m hm => hterm m hm)
  rw [hsum]
  cases evalMonomialList eq (fun v => (List.ofFn σ).getD v false)
  · simp only [bitVal_false]
  · simp only [bitVal_true, one_ne_zero, Bool.true_eq_false]

/-- **Semantic bridge to `Cslib.BitString.commonZeroCount`**: when every equation in `sys` is
canonical (`IsCanonicalEquation`) and all occurring variable indices satisfy `v < n`,
`countSystemExhaustive (n, sys)` equals `commonZeroCount` of the projected `Fin n` equations. -/
theorem countSystemExhaustive_eq_commonZeroCount {n : ℕ} {sys : List (List (List ℕ))}
    (hsys : ∀ eq ∈ sys, IsCanonicalEquation eq ∧ ∀ m ∈ eq, ∀ v ∈ m, v < n) :
    countSystemExhaustive (n, sys) =
      commonZeroCount (Finset.univ : Finset (Fin sys.length))
        (fun i : Fin sys.length => equationToFinset n sys[i]) := by
  rw [countSystemExhaustive_eq_card_filter, commonZeroCount]
  congr 1
  ext σ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, evalSystem_eq_true_iff]
  unfold IsCommonZero
  constructor
  · intro h i _
    have hi := hsys sys[i] (List.getElem_mem i.isLt)
    exact (monomialSum_equationToFinset_eq_zero_iff hi.1 hi.2 σ).mpr
      (h sys[i] (List.getElem_mem i.isLt))
  · intro h eq heq
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem heq
    have hcanon := hsys sys[i] (List.getElem_mem hi)
    exact (monomialSum_equationToFinset_eq_zero_iff hcanon.1 hcanon.2 σ).mp
      (h ⟨i, hi⟩ (Finset.mem_univ _))

/-- An empty list of equations has `2 ^ n` common zeros (§5.5, p. 38). -/
@[simp] theorem countSystemExhaustive_nil (n : ℕ) :
    countSystemExhaustive (n, []) = 2 ^ n := by
  have hall : (Finset.univ.filter fun σ : BitString n =>
      evalSystem [] (fun v => (List.ofFn σ).getD v false) = true) = Finset.univ :=
    Finset.filter_eq_self.mpr fun _ _ => rfl
  rw [countSystemExhaustive_eq_card_filter, hall, Finset.card_univ, Cslib.BitString.card]

/-- A system containing the contradictory constant equation `[[]]` (`1 = 0`) has `0` common zeros
(§5.5, p. 38). -/
theorem countSystemExhaustive_eq_zero_of_nil_mem {n : ℕ} {sys : List (List (List ℕ))}
    (h : [[]] ∈ sys) :
    countSystemExhaustive (n, sys) = 0 := by
  rw [countSystemExhaustive_eq_card_filter, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  intro σ hσ
  have hsat := (Finset.mem_filter.mp hσ).2
  have heval := (evalSystem_eq_true_iff sys _).mp hsat [[]] h
  simp only [evalMonomialList_singleton, List.all_nil, Bool.true_eq_false] at heval

open ComputableInPolyTime in
/-- Evaluating a sparse `𝔽₂` polynomial system `sys` on `(word.getD v false)` is polynomial-time in
the pair encoding `(encList (encList (encList encNat)), encBits)`. -/
theorem computableInPolyTime_evalSystem_word :
    ComputableInPolyTime
      (fun p : List (List (List ℕ)) × List Bool => evalSystem p.1 (fun v => p.2.getD v false))
      (encPair encSys encBits) encBool := by
  have hmon : ComputableInPolyTime
      (fun q : List ℕ × List Bool => q.1.all (fun v => q.2.getD v false))
      (encPair (encList encNat) encBits) encBool :=
    allWithInput (fst (encList encNat) encBits)
      (listGetD_binary (encA := encBool) (encL := encBits) false
        ((snd (encList encNat) encBits).comp (fst _ _)) (snd _ _))
  have heq : ComputableInPolyTime
      (fun q : List (List ℕ) × List Bool => evalMonomialList q.1 (fun v => q.2.getD v false))
      (encPair (encList (encList encNat)) encBits) encBool := by
    refine foldlWith (encA := encList encNat) (encL := encList (encList encNat))
      (encB := encBool) (encP := encBits)
      (par := Prod.snd) (list := Prod.fst) (init := fun _ => false)
      (step := fun word acc m => xor acc (m.all (fun v => word.getD v false)))
      (snd _ _) (fst _ _) (const false) ?_ (B := fun _ => 1) (PolyBounded.const 1)
      (fun _ _ _ => by
        cases (((_ : List (List ℕ)).take _).foldl _ false) <;> decide)
    have hacc := (snd encBits encBool).comp (fst (encPair encBits encBool) (encList encNat))
    have hword := (fst encBits encBool).comp (fst (encPair encBits encBool) (encList encNat))
    have hm := snd (encPair encBits encBool) (encList encNat)
    exact (of_finite (fun r : Bool × Bool => xor r.1 r.2)).comp
      (hacc.prod (hmon.comp (hm.prod hword)))
  unfold evalSystem
  exact allWithInput (fst encSys encBits)
    (bool_not.comp (heq.comp
      ((snd (encPair encSys encBits) (encList (encList encNat))).prod
        ((snd encSys encBits).comp (fst (encPair encSys encBits) (encList (encList encNat)))))))

/-- Native resource certificate for `countSystemExhaustive` over `(encUnary, encSys) → encNat`. -/
noncomputable def countSystemExhaustiveCertificate :
    NativeCertificate countSystemExhaustive (encPair encUnary encSys) encNat :=
  countPredicateCertificate computableInPolyTime_evalSystem_word

/-- `countSystemExhaustiveCertificate` uses polynomial workspace in the encoded input length. -/
theorem polyBounded_countSystemExhaustive_space :
    PolyBounded (fun x : ℕ × List (List (List ℕ)) => (encPair encUnary encSys x).length)
      countSystemExhaustiveCertificate.space :=
  (countPredicateCertificate_bounds computableInPolyTime_evalSystem_word).1

/-- `countSystemExhaustiveCertificate` runs in `(2 ^ n + 1) * P_ex x + Q_ex x` steps for
polynomially bounded `P_ex, Q_ex`. -/
theorem exists_countSystemExhaustive_time_le :
    ∃ P_ex Q_ex : ℕ × List (List (List ℕ)) → ℕ,
      PolyBounded (fun x => (encPair encUnary encSys x).length) P_ex ∧
      PolyBounded (fun x => (encPair encUnary encSys x).length) Q_ex ∧
      ∀ x, countSystemExhaustiveCertificate.time x ≤ (2 ^ x.1 + 1) * P_ex x + Q_ex x :=
  (countPredicateCertificate_bounds computableInPolyTime_evalSystem_word).2

/-- `countSystemExhaustive` is computable in `O((|x| + 1) ^ d * 2 ^ n)` time and polynomial
workspace. -/
theorem computableInO_countSystemExhaustive :
    ∃ d : ℕ, ∃ S : ℕ × List (List (List ℕ)) → ℕ,
      PolyBounded (fun x => (encPair encUnary encSys x).length) S ∧
      ComputableInO countSystemExhaustive (encPair encUnary encSys) encNat
        (fun x => 2 ^ x.1 * ((encPair encUnary encSys x).length + 1) ^ d) S := by
  obtain ⟨P_ex, Q_ex, hP, hQ, hT⟩ := exists_countSystemExhaustive_time_le
  obtain ⟨c, d, hcd⟩ := exists_le_mul_two_pow_of_polyBounded hP hQ hT
  refine ⟨d, countSystemExhaustiveCertificate.space, polyBounded_countSystemExhaustive_space,
    countSystemExhaustiveCertificate.computes.mono (c + 1)
      (fun x => by
        calc countSystemExhaustiveCertificate.time x
            ≤ c * (2 ^ x.1 * ((encPair encUnary encSys x).length + 1) ^ d) := by
              rw [← Nat.mul_assoc]; exact hcd x
          _ ≤ (c + 1) * (2 ^ x.1 * ((encPair encUnary encSys x).length + 1) ^ d + 1) :=
              Nat.mul_le_mul (Nat.le_succ c) (Nat.le_succ _))
      (fun x => (Nat.le_succ _).trans (Nat.le_mul_of_pos_left _ (Nat.succ_pos c)))⟩

/-! ### 2. Streaming Declared-Variable `CNF` Model Counter (§6.4, pp. 43–44) -/

/-- Prefix state after visiting the first `j` assignments `0 ≤ idx < j` of the streaming
declared-variable `CNF ℕ` model counter on `(n, φ)`. Variable indices `v ≥ n` default to `false`
via `(lowBits n idx).getD v false`. -/
def countCNFPrefix (x : ℕ × CNF ℕ) (j : ℕ) : ℕ × (ℕ × ((ℕ × CNF ℕ) × ℕ)) :=
  BooleanFold.runPrefix
    (countStep fun φ word => φ.eval (fun v => word.getD v false)) x.1 j (x, 0)

/-- **Streaming polynomial-space $2^n$ declared-variable `CNF` model counter** (§6.4, pp. 43–44):
iterates over `0 ≤ idx < 2 ^ n` via `BooleanFold.run` without materializing `enumList n`, keeping
live state `((n, φ), Z)` and incrementing `Z` when `φ.eval (fun v => (lowBits n idx).getD v false)`
is `true`. Variable indices `v ≥ n` default to `false`; to interpret `countCNFExhaustive (n, φ)` as
the satisfying-assignment count on `n` declared variables, require `∀ v ∈ φ.vars, v < n`. -/
def countCNFExhaustive (x : ℕ × CNF ℕ) : ℕ :=
  (BooleanFold.run
    (countStep fun φ word => φ.eval (fun v => word.getD v false)) x.1 (x, 0)).2.2.2

/-- At every prefix `j`, the retained payload in `countCNFPrefix x j` equals `x = (n, φ)`. -/
@[simp] theorem countCNFPrefix_payload (x : ℕ × CNF ℕ) (j : ℕ) :
    (countCNFPrefix x j).2.2.1 = x :=
  prefix_payload_eq _ x j

/-- At every prefix `j`, the running count `Z` equals the number of indices `idx < j` whose decoded
`n`-bit word satisfies `φ`. -/
theorem countCNFPrefix_count_eq (x : ℕ × CNF ℕ) (j : ℕ) :
    (countCNFPrefix x j).2.2.2 =
      ((List.range j).map (lowBits x.1)).countP
        (fun word => x.2.eval (fun v => word.getD v false)) :=
  prefix_count_eq _ x j

/-- Unconditional prefix count bound `Z ≤ j` for `countCNFPrefix`. -/
theorem countCNFPrefix_le_index (x : ℕ × CNF ℕ) (j : ℕ) :
    (countCNFPrefix x j).2.2.2 ≤ j :=
  prefix_count_le_index _ x j

/-- **Prefix invariant `Z ≤ j ≤ 2 ^ n`** for `countCNFPrefix` along the `2 ^ n` traversal. -/
theorem countCNFPrefix_invariant (x : ℕ × CNF ℕ) {j : ℕ} (hj : j ≤ 2 ^ x.1) :
    (countCNFPrefix x j).2.2.2 ≤ j ∧ j ≤ 2 ^ x.1 :=
  ⟨countCNFPrefix_le_index x j, hj⟩

/-- `countCNFExhaustive (n, φ)` equals the cardinality of the `BitString n` assignments whose
decoded word `(List.ofFn σ).getD v false` satisfies `φ`. -/
theorem countCNFExhaustive_eq_card_filter (n : ℕ) (φ : CNF ℕ) :
    countCNFExhaustive (n, φ) =
      (Finset.univ.filter fun σ : BitString n =>
        φ.eval (fun v => (List.ofFn σ).getD v false) = true).card :=
  run_count_eq_card_filter _ (n, φ)

/-- **Exact agreement with `CNF.modelCountOn φ (Finset.range n)`**: both `countCNFExhaustive (n, φ)`
and `CNF.modelCountOn φ (Finset.range n)` range over `n`-bit assignments on `{0, …, n - 1}` and
extend variables `v ≥ n` by `false`. -/
theorem countCNFExhaustive_eq_modelCountOn_range (n : ℕ) (φ : CNF ℕ) :
    countCNFExhaustive (n, φ) = φ.modelCountOn (Finset.range n) := by
  rw [countCNFExhaustive_eq_card_filter, CNF.modelCountOn]
  refine Finset.card_bij
    (fun (σ : BitString n) _ (v : Finset.range n) => σ ⟨v.1, Finset.mem_range.mp v.2⟩)
    (fun σ hσ => ?_)
    (fun σ₁ _ σ₂ _ h => funext fun i => congrFun h ⟨i.1, Finset.mem_range.mpr i.isLt⟩)
    (fun τ hτ => ⟨fun i => τ ⟨i.1, Finset.mem_range.mpr i.isLt⟩, ?_, funext fun _ => rfl⟩)
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
    convert hσ using 2
    funext v
    rw [ofFn_getD_false]
    by_cases hv : v < n <;> simp only [hv, ↓reduceDIte, Finset.mem_range]
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hτ ⊢
    convert hτ using 2
    funext v
    rw [ofFn_getD_false]
    by_cases hv : v < n <;> simp only [hv, ↓reduceDIte, Finset.mem_range]

/-- When all occurring variables of `φ` satisfy `v < n`, `countCNFExhaustive (n, φ)` equals
`2 ^ (n - φ.numVars) * φ.modelCount`, doubling for each unused declared variable `< n`. -/
theorem countCNFExhaustive_eq_mul_modelCount {n : ℕ} {φ : CNF ℕ} (hvars : ∀ v ∈ φ.vars, v < n) :
    countCNFExhaustive (n, φ) = 2 ^ (n - φ.numVars) * φ.modelCount := by
  rw [countCNFExhaustive_eq_modelCountOn_range, CNF.modelCountOn_eq_mul_modelCount]
  · simp only [Finset.card_range]
  · intro v hv
    exact Finset.mem_range.mpr (hvars v (List.mem_toFinset.mp hv))

/-- An empty formula `[]` has `2 ^ n` satisfying assignments on `n` declared variables (§6.4,
p. 43), including `n = 0`. -/
@[simp] theorem countCNFExhaustive_nil (n : ℕ) :
    countCNFExhaustive (n, []) = 2 ^ n := by
  rw [countCNFExhaustive_eq_modelCountOn_range, CNF.modelCountOn_nil, Finset.card_range]

/-- A formula containing an empty clause `[]` has `0` satisfying assignments (§6.4, p. 43). -/
theorem countCNFExhaustive_eq_zero_of_nil_mem {n : ℕ} {φ : CNF ℕ} (h : [] ∈ φ) :
    countCNFExhaustive (n, φ) = 0 := by
  rw [countCNFExhaustive_eq_modelCountOn_range]
  exact CNF.modelCountOn_eq_zero_of_nil_mem h (Finset.range n)

@[local fun_prop]
private theorem computableInPolyTime_bitsGetD_binary {γ : Type} {encIn : γ ↪ List Bool}
    {w : γ → List Bool} {i : γ → ℕ}
    (hw : ComputableInPolyTime w encIn encBits)
    (hi : ComputableInPolyTime i encIn encNat) :
    ComputableInPolyTime (fun x => (w x).getD (i x) false) encIn encBool :=
  ComputableInPolyTime.listGetD_binary (encA := encBool) (encL := encBits) false hw hi

/-- Evaluating `φ : CNF ℕ` on `(word.getD v false)` is polynomial-time in `(encCNF, encBits)`. -/
theorem computableInPolyTime_evalCNF_word :
    ComputableInPolyTime (fun p : CNF ℕ × List Bool => p.1.eval (fun v => p.2.getD v false))
      (encPair encCNF encBits) encBool := by
  unfold encCNF
  fun_prop [CNF.eval, Clause.eval, Literal.eval]

/-- Native resource certificate for `countCNFExhaustive` over `(encUnary, encCNF) → encNat`. -/
noncomputable def countCNFExhaustiveCertificate :
    NativeCertificate countCNFExhaustive (encPair encUnary encCNF) encNat :=
  countPredicateCertificate computableInPolyTime_evalCNF_word

/-- `countCNFExhaustiveCertificate` uses polynomial workspace in the encoded input length. -/
theorem polyBounded_countCNFExhaustive_space :
    PolyBounded (fun x : ℕ × CNF ℕ => (encPair encUnary encCNF x).length)
      countCNFExhaustiveCertificate.space :=
  (countPredicateCertificate_bounds computableInPolyTime_evalCNF_word).1

/-- `countCNFExhaustiveCertificate` runs in `(2 ^ n + 1) * P_ex x + Q_ex x` steps for polynomially
bounded `P_ex, Q_ex`. -/
theorem exists_countCNFExhaustive_time_le :
    ∃ P_ex Q_ex : ℕ × CNF ℕ → ℕ,
      PolyBounded (fun x => (encPair encUnary encCNF x).length) P_ex ∧
      PolyBounded (fun x => (encPair encUnary encCNF x).length) Q_ex ∧
      ∀ x, countCNFExhaustiveCertificate.time x ≤ (2 ^ x.1 + 1) * P_ex x + Q_ex x :=
  (countPredicateCertificate_bounds computableInPolyTime_evalCNF_word).2

/-- `countCNFExhaustive` is computable in `O((|x| + 1) ^ d * 2 ^ n)` time and polynomial workspace.
-/
theorem computableInO_countCNFExhaustive :
    ∃ d : ℕ, ∃ S : ℕ × CNF ℕ → ℕ,
      PolyBounded (fun x => (encPair encUnary encCNF x).length) S ∧
      ComputableInO countCNFExhaustive (encPair encUnary encCNF) encNat
        (fun x => 2 ^ x.1 * ((encPair encUnary encCNF x).length + 1) ^ d) S := by
  obtain ⟨P_ex, Q_ex, hP, hQ, hT⟩ := exists_countCNFExhaustive_time_le
  obtain ⟨c, d, hcd⟩ := exists_le_mul_two_pow_of_polyBounded hP hQ hT
  refine ⟨d, countCNFExhaustiveCertificate.space, polyBounded_countCNFExhaustive_space,
    countCNFExhaustiveCertificate.computes.mono (c + 1)
      (fun x => by
        calc countCNFExhaustiveCertificate.time x
            ≤ c * (2 ^ x.1 * ((encPair encUnary encCNF x).length + 1) ^ d) := by
              rw [← Nat.mul_assoc]; exact hcd x
          _ ≤ (c + 1) * (2 ^ x.1 * ((encPair encUnary encCNF x).length + 1) ^ d + 1) :=
              Nat.mul_le_mul (Nat.le_succ c) (Nat.le_succ _))
      (fun x => (Nat.le_succ _).trans (Nat.le_mul_of_pos_left _ (Nat.succ_pos c)))⟩

/-! ### 3. Finite-Threshold Guard-Fallback Combinator & Constant Absorption (§5.5 & §6.4) -/

section GuardedFallback

variable {α β : Type} {ei : α ↪ List Bool} {eo : β ↪ List Bool}

/-- Pointwise agreement of `if ok x then f_fast x else f_exhaust x` with a target specification `f`
whenever `f_fast` agrees with `f` on `ok x = true` and `f_exhaust` agrees with `f` on
`ok x = false`. -/
theorem ite_eq_of_agrees {ok : α → Bool} {f_fast f_exhaust f : α → β}
    (hfast : ∀ x, ok x = true → f_fast x = f x)
    (hex : ∀ x, ok x = false → f_exhaust x = f x) (x : α) :
    (if ok x then f_fast x else f_exhaust x) = f x := by
  cases h : ok x
  · simpa only [Bool.false_eq_true, ↓reduceIte] using hex x h
  · simpa only [↓reduceIte] using hfast x h

/-- Build the selected-branch `NativeCertificate` for
`fun x => if ok x then f_fast x else f_exhaust x` from a `ComputableInPolyTime` guard `ok`,
evaluating only the selected branch. -/
noncomputable def guardedBranchOfPolyTime {ok : α → Bool} {f_fast f_exhaust : α → β}
    (hok : ComputableInPolyTime ok ei encBool)
    (c_fast : NativeCertificate f_fast ei eo)
    (c_exhaust : NativeCertificate f_exhaust ei eo) :
    NativeCertificate (fun x => if ok x then f_fast x else f_exhaust x) ei eo :=
  NativeCertificate.branch (NativeCertificate.ofPolyTime hok) c_fast c_exhaust

/-- Build a `NativeCertificate` directly for a target specification `f : α → β` via
`NativeCertificate.branch`, charging only `c_ok` and the selected branch. -/
def guardedTargetCertificate {ok : α → Bool} {f_fast f_exhaust f : α → β}
    (c_ok : NativeCertificate ok ei encBool)
    (c_fast : NativeCertificate f_fast ei eo)
    (c_exhaust : NativeCertificate f_exhaust ei eo)
    (hfast : ∀ x, ok x = true → f_fast x = f x)
    (hex : ∀ x, ok x = false → f_exhaust x = f x) :
    NativeCertificate f ei eo :=
  (NativeCertificate.branch c_ok c_fast c_exhaust).congr (ite_eq_of_agrees hfast hex)

@[simp] theorem guardedTargetCertificate_time {ok : α → Bool} {f_fast f_exhaust f : α → β}
    (c_ok : NativeCertificate ok ei encBool)
    (c_fast : NativeCertificate f_fast ei eo)
    (c_exhaust : NativeCertificate f_exhaust ei eo)
    (hfast : ∀ x, ok x = true → f_fast x = f x)
    (hex : ∀ x, ok x = false → f_exhaust x = f x) (x : α) :
    (guardedTargetCertificate c_ok c_fast c_exhaust hfast hex).time x =
      c_ok.time x + if ok x then c_fast.time x else c_exhaust.time x := rfl

@[simp] theorem guardedTargetCertificate_space {ok : α → Bool} {f_fast f_exhaust f : α → β}
    (c_ok : NativeCertificate ok ei encBool)
    (c_fast : NativeCertificate f_fast ei eo)
    (c_exhaust : NativeCertificate f_exhaust ei eo)
    (hfast : ∀ x, ok x = true → f_fast x = f x)
    (hex : ∀ x, ok x = false → f_exhaust x = f x) (x : α) :
    (guardedTargetCertificate c_ok c_fast c_exhaust hfast hex).space x =
      c_ok.space x + if ok x then c_fast.space x else c_exhaust.space x := rfl

/-- Build a `NativeCertificate` for target `f` from a `ComputableInPolyTime` guard `ok`, a fast
certificate `c_fast`, and an exhaustive fallback certificate `c_exhaust`. -/
noncomputable def guardedTargetOfPolyTime {ok : α → Bool} {f_fast f_exhaust f : α → β}
    (hok : ComputableInPolyTime ok ei encBool)
    (c_fast : NativeCertificate f_fast ei eo)
    (c_exhaust : NativeCertificate f_exhaust ei eo)
    (hfast : ∀ x, ok x = true → f_fast x = f x)
    (hex : ∀ x, ok x = false → f_exhaust x = f x) :
    NativeCertificate f ei eo :=
  guardedTargetCertificate (NativeCertificate.ofPolyTime hok) c_fast c_exhaust hfast hex

/-- **Polynomial workspace preservation**: `NativeCertificate.branch` has polynomial workspace
whenever the guard, fast branch, and exhaustive fallback each have polynomial workspace (without
assuming either branch runs in polynomial time). -/
theorem polyBounded_branch_space {ok : α → Bool} {f_fast f_exhaust : α → β}
    (c_ok : NativeCertificate ok ei encBool)
    (c_fast : NativeCertificate f_fast ei eo)
    (c_exhaust : NativeCertificate f_exhaust ei eo)
    (hok : PolyBounded (fun x => (ei x).length) c_ok.space)
    (hfast : PolyBounded (fun x => (ei x).length) c_fast.space)
    (hex : PolyBounded (fun x => (ei x).length) c_exhaust.space) :
    PolyBounded (fun x => (ei x).length)
      (NativeCertificate.branch c_ok c_fast c_exhaust).space := by
  refine (hok.add (hfast.add hex)).mono fun x => ?_
  simp only [NativeCertificate.branch_space]
  split_ifs <;> omega

/-- **Finite-threshold fallback time absorption on `NativeCertificate.branch`** (§5.5 p. 39,
§6.4 p. 44): if `ok x = false → μ x < N₀` for a constant threshold `N₀` and `c_exhaust.time x ≤
(2 ^ μ x + 1) * P_ex x + Q_ex x` with `PolyBounded` `P_ex, Q_ex`, then the guarded branch preserves
polynomial workspace and bounds total time by `(if ok x then c_fast.time x else 0) +
C * (|ei x| + 1) ^ d`. -/
theorem exists_branch_time_le_of_finite_threshold {ok : α → Bool} {f_fast f_exhaust : α → β}
    {μ P_ex Q_ex : α → ℕ} {N₀ : ℕ}
    (c_ok : NativeCertificate ok ei encBool)
    (c_fast : NativeCertificate f_fast ei eo)
    (c_exhaust : NativeCertificate f_exhaust ei eo)
    (hok : c_ok.IsPolynomial)
    (hs_fast : PolyBounded (fun x => (ei x).length) c_fast.space)
    (hs_ex : PolyBounded (fun x => (ei x).length) c_exhaust.space)
    (hthresh : ∀ x, ok x = false → μ x < N₀)
    (hP : PolyBounded (fun x => (ei x).length) P_ex)
    (hQ : PolyBounded (fun x => (ei x).length) Q_ex)
    (ht_ex : ∀ x, ok x = false → c_exhaust.time x ≤ (2 ^ μ x + 1) * P_ex x + Q_ex x) :
    PolyBounded (fun x => (ei x).length) (NativeCertificate.branch c_ok c_fast c_exhaust).space ∧
    ∃ C d : ℕ, ∀ x, (NativeCertificate.branch c_ok c_fast c_exhaust).time x ≤
      (if ok x then c_fast.time x else 0) + C * ((ei x).length + 1) ^ d := by
  refine ⟨polyBounded_branch_space c_ok c_fast c_exhaust hok.2 hs_fast hs_ex, ?_⟩
  have hpoly : PolyBounded (fun x => (ei x).length)
      (fun x => c_ok.time x + ((2 ^ N₀ + 1) * P_ex x + Q_ex x)) :=
    hok.1.add (((PolyBounded.const (2 ^ N₀ + 1)).mul hP).add hQ)
  obtain ⟨C, d, hCd⟩ := hpoly.exists_le
  refine ⟨C, d, fun x => ?_⟩
  simp only [NativeCertificate.branch_time]
  cases h : ok x
  · simp only [Bool.false_eq_true, ↓reduceIte, zero_add]
    have hpow : 2 ^ μ x ≤ 2 ^ N₀ :=
      Nat.pow_le_pow_right (by omega) (Nat.le_of_lt (hthresh x h))
    have hex_le : c_exhaust.time x ≤ (2 ^ N₀ + 1) * P_ex x + Q_ex x :=
      (ht_ex x h).trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ (by omega)) _)
    exact (Nat.add_le_add_left hex_le (c_ok.time x)).trans (hCd x)
  · simp only [↓reduceIte]
    have hok_le : c_ok.time x ≤ C * ((ei x).length + 1) ^ d :=
      (Nat.le_add_right (c_ok.time x) _).trans (hCd x)
    omega

/-- **Combined `ComputableInO` theorem under a `ComputableInPolyTime` guard**: when `ok x = false →
μ x < N₀`, the guarded machine computes `f` in polynomial workspace and time
`T_fast x + C * (|ei x| + 1) ^ d`. -/
theorem computableInO_of_guarded_fallback {ok : α → Bool} {f_fast f_exhaust f : α → β}
    {μ P_ex Q_ex T_fast : α → ℕ} {N₀ : ℕ}
    (hok : ComputableInPolyTime ok ei encBool)
    (c_fast : NativeCertificate f_fast ei eo)
    (c_exhaust : NativeCertificate f_exhaust ei eo)
    (hfast_eq : ∀ x, ok x = true → f_fast x = f x)
    (hex_eq : ∀ x, ok x = false → f_exhaust x = f x)
    (hs_fast : PolyBounded (fun x => (ei x).length) c_fast.space)
    (hs_ex : PolyBounded (fun x => (ei x).length) c_exhaust.space)
    (hthresh : ∀ x, ok x = false → μ x < N₀)
    (hP : PolyBounded (fun x => (ei x).length) P_ex)
    (hQ : PolyBounded (fun x => (ei x).length) Q_ex)
    (ht_fast : ∀ x, ok x = true → c_fast.time x ≤ T_fast x)
    (ht_ex : ∀ x, ok x = false → c_exhaust.time x ≤ (2 ^ μ x + 1) * P_ex x + Q_ex x) :
    ∃ C d : ℕ, ∃ S : α → ℕ,
      PolyBounded (fun x => (ei x).length) S ∧
      ComputableInO f ei eo (fun x => T_fast x + C * ((ei x).length + 1) ^ d) S := by
  let cert := guardedTargetOfPolyTime hok c_fast c_exhaust hfast_eq hex_eq
  obtain ⟨hS, C, d, hT⟩ := exists_branch_time_le_of_finite_threshold
    (NativeCertificate.ofPolyTime hok) c_fast c_exhaust
    (NativeCertificate.ofPolyTime_isPolynomial hok) hs_fast hs_ex hthresh hP hQ ht_ex
  refine ⟨C, d, cert.space, hS, cert.computes.mono_le (fun x => ?_) (fun _ => le_rfl)⟩
  have hx := hT x
  change (NativeCertificate.branch (NativeCertificate.ofPolyTime hok) c_fast c_exhaust).time x ≤ _
  cases h : ok x
  · simp only [h, Bool.false_eq_true, ↓reduceIte, zero_add] at hx
    omega
  · simp only [h, ↓reduceIte] at hx
    have hf := ht_fast x h
    omega

/-- **Natural-exponent constant absorption**: for any `E : α → ℕ`, if the fast branch satisfies
`ok x = true → c_fast.time x ≤ C_f * (|ei x| + 1) ^ d_f * 2 ^ E x` and `ok x = false → μ x < N₀`,
then the finite exhaustive-fallback cases are absorbed into `C' * (|ei x| + 1) ^ e * 2 ^ E x`. -/
theorem exists_nat_exp_bound_of_guarded_fallback {ok : α → Bool} {f_fast f_exhaust f : α → β}
    {μ P_ex Q_ex E : α → ℕ} {N₀ C_f d_f : ℕ}
    (hok : ComputableInPolyTime ok ei encBool)
    (c_fast : NativeCertificate f_fast ei eo)
    (c_exhaust : NativeCertificate f_exhaust ei eo)
    (hfast_eq : ∀ x, ok x = true → f_fast x = f x)
    (hex_eq : ∀ x, ok x = false → f_exhaust x = f x)
    (hs_fast : PolyBounded (fun x => (ei x).length) c_fast.space)
    (hs_ex : PolyBounded (fun x => (ei x).length) c_exhaust.space)
    (hthresh : ∀ x, ok x = false → μ x < N₀)
    (hP : PolyBounded (fun x => (ei x).length) P_ex)
    (hQ : PolyBounded (fun x => (ei x).length) Q_ex)
    (ht_fast : ∀ x, ok x = true → c_fast.time x ≤ C_f * ((ei x).length + 1) ^ d_f * 2 ^ E x)
    (ht_ex : ∀ x, ok x = false → c_exhaust.time x ≤ (2 ^ μ x + 1) * P_ex x + Q_ex x) :
    ∃ C' e : ℕ, ∃ S : α → ℕ,
      PolyBounded (fun x => (ei x).length) S ∧
      (∀ x, (guardedTargetOfPolyTime hok c_fast c_exhaust hfast_eq hex_eq).time x ≤
        C' * ((ei x).length + 1) ^ e * 2 ^ E x) ∧
      ComputableInO f ei eo (fun x => ((ei x).length + 1) ^ e * 2 ^ E x) S := by
  let cert := guardedTargetOfPolyTime hok c_fast c_exhaust hfast_eq hex_eq
  obtain ⟨hS, C, d, hT⟩ := exists_branch_time_le_of_finite_threshold
    (NativeCertificate.ofPolyTime hok) c_fast c_exhaust
    (NativeCertificate.ofPolyTime_isPolynomial hok) hs_fast hs_ex hthresh hP hQ ht_ex
  have hcert_le (x : α) : cert.time x ≤ (C_f + C) * ((ei x).length + 1) ^ (d_f + d) * 2 ^ E x := by
    have hx := hT x
    have hp1 : ((ei x).length + 1) ^ d_f ≤ ((ei x).length + 1) ^ (d_f + d) :=
      Nat.pow_le_pow_right (Nat.succ_pos _) (Nat.le_add_right _ _)
    have hp2 : ((ei x).length + 1) ^ d ≤ ((ei x).length + 1) ^ (d_f + d) :=
      Nat.pow_le_pow_right (Nat.succ_pos _) (Nat.le_add_left _ _)
    have htwo : 1 ≤ 2 ^ E x := Nat.one_le_two_pow
    have hC : C * ((ei x).length + 1) ^ d ≤ C * ((ei x).length + 1) ^ (d_f + d) * 2 ^ E x := by
      calc C * ((ei x).length + 1) ^ d
          ≤ C * ((ei x).length + 1) ^ (d_f + d) := Nat.mul_le_mul_left C hp2
        _ ≤ C * ((ei x).length + 1) ^ (d_f + d) * 2 ^ E x := Nat.le_mul_of_pos_right _ htwo
    change (NativeCertificate.branch (NativeCertificate.ofPolyTime hok) c_fast c_exhaust).time x ≤ _
    cases h : ok x
    · simp only [h, Bool.false_eq_true, ↓reduceIte, zero_add] at hx
      calc _ ≤ C * ((ei x).length + 1) ^ d := hx
        _ ≤ C * ((ei x).length + 1) ^ (d_f + d) * 2 ^ E x := hC
        _ ≤ (C_f + C) * ((ei x).length + 1) ^ (d_f + d) * 2 ^ E x :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.le_add_left C C_f))
    · simp only [h, ↓reduceIte] at hx
      have hf : c_fast.time x ≤ C_f * ((ei x).length + 1) ^ (d_f + d) * 2 ^ E x :=
        (ht_fast x h).trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left C_f hp1))
      calc _ ≤ c_fast.time x + C * ((ei x).length + 1) ^ d := hx
        _ ≤ C_f * ((ei x).length + 1) ^ (d_f + d) * 2 ^ E x +
              C * ((ei x).length + 1) ^ (d_f + d) * 2 ^ E x := Nat.add_le_add hf hC
        _ = (C_f + C) * ((ei x).length + 1) ^ (d_f + d) * 2 ^ E x := by ring
  refine ⟨C_f + C, d_f + d, cert.space, hS, hcert_le,
    cert.computes.mono (C_f + C + 1)
      (fun x => by
        calc cert.time x
            ≤ (C_f + C) * (((ei x).length + 1) ^ (d_f + d) * 2 ^ E x) := by
              rw [← Nat.mul_assoc]; exact hcert_le x
          _ ≤ (C_f + C + 1) * (((ei x).length + 1) ^ (d_f + d) * 2 ^ E x + 1) :=
              Nat.mul_le_mul (Nat.le_succ _) (Nat.le_succ _))
      (fun x => (Nat.le_succ _).trans (Nat.le_mul_of_pos_left _ (Nat.succ_pos _)))⟩

/-- **Real-exponent subexponential constant absorption** (§5.5 p. 39, §6.4 p. 44): for any
nonnegative real exponent `E : α → ℝ` (`∀ x, 0 ≤ E x`, including subexponential exponents such as
`A * ρ (μ x)`), if `ok x = true → (c_fast.time x : ℝ) ≤ C_f * (|ei x| + 1) ^ d_f * 2 ^ E x` and
`ok x = false → μ x < N₀`, then the combined guarded certificate has polynomial workspace, satisfies
`(cert.time x : ℝ) ≤ C' * (|ei x| + 1) ^ e * (2 : ℝ) ^ E x` for all `x`, and runs in
`ComputableInO` time `(|ei x| + 1) ^ e * ⌈(2 : ℝ) ^ E x⌉₊`. -/
theorem exists_real_exp_bound_of_guarded_fallback {ok : α → Bool} {f_fast f_exhaust f : α → β}
    {μ P_ex Q_ex : α → ℕ} {E : α → ℝ} {N₀ C_f d_f : ℕ}
    (hok : ComputableInPolyTime ok ei encBool)
    (c_fast : NativeCertificate f_fast ei eo)
    (c_exhaust : NativeCertificate f_exhaust ei eo)
    (hfast_eq : ∀ x, ok x = true → f_fast x = f x)
    (hex_eq : ∀ x, ok x = false → f_exhaust x = f x)
    (hs_fast : PolyBounded (fun x => (ei x).length) c_fast.space)
    (hs_ex : PolyBounded (fun x => (ei x).length) c_exhaust.space)
    (hthresh : ∀ x, ok x = false → μ x < N₀)
    (hP : PolyBounded (fun x => (ei x).length) P_ex)
    (hQ : PolyBounded (fun x => (ei x).length) Q_ex)
    (hE : ∀ x, 0 ≤ E x)
    (ht_fast : ∀ x, ok x = true →
      (c_fast.time x : ℝ) ≤ (C_f : ℝ) * ((ei x).length + 1 : ℝ) ^ d_f * (2 : ℝ) ^ E x)
    (ht_ex : ∀ x, ok x = false → c_exhaust.time x ≤ (2 ^ μ x + 1) * P_ex x + Q_ex x) :
    ∃ C' e : ℕ, ∃ S : α → ℕ,
      PolyBounded (fun x => (ei x).length) S ∧
      (∀ x, ((guardedTargetOfPolyTime hok c_fast c_exhaust hfast_eq hex_eq).time x : ℝ) ≤
        (C' : ℝ) * ((ei x).length + 1 : ℝ) ^ e * (2 : ℝ) ^ E x) ∧
      ComputableInO f ei eo (fun x => ((ei x).length + 1) ^ e * ⌈(2 : ℝ) ^ E x⌉₊) S := by
  let cert := guardedTargetOfPolyTime hok c_fast c_exhaust hfast_eq hex_eq
  obtain ⟨hS, C, d, hT⟩ := exists_branch_time_le_of_finite_threshold
    (NativeCertificate.ofPolyTime hok) c_fast c_exhaust
    (NativeCertificate.ofPolyTime_isPolynomial hok) hs_fast hs_ex hthresh hP hQ ht_ex
  have hreal (x : α) :
      (cert.time x : ℝ) ≤ ((C_f + C : ℕ) : ℝ) * ((ei x).length + 1 : ℝ) ^ (d_f + d) *
        (2 : ℝ) ^ E x := by
    have hx : (cert.time x : ℝ) ≤
        ((if ok x then c_fast.time x else 0 : ℕ) : ℝ) + (C : ℝ) * ((ei x).length + 1 : ℝ) ^ d := by
      exact_mod_cast hT x
    have hp1 : (((ei x).length + 1) ^ d_f : ℝ) ≤ ((ei x).length + 1 : ℝ) ^ (d_f + d) := by
      exact_mod_cast Nat.pow_le_pow_right (Nat.succ_pos _) (Nat.le_add_right d_f d)
    have hp2 : (((ei x).length + 1) ^ d : ℝ) ≤ ((ei x).length + 1 : ℝ) ^ (d_f + d) := by
      exact_mod_cast Nat.pow_le_pow_right (Nat.succ_pos _) (Nat.le_add_left d d_f)
    have htwo : (1 : ℝ) ≤ (2 : ℝ) ^ E x := Real.one_le_rpow (by norm_num) (hE x)
    have hpow_nonneg : (0 : ℝ) ≤ ((ei x).length + 1 : ℝ) ^ (d_f + d) := by positivity
    have hC : (C : ℝ) * ((ei x).length + 1 : ℝ) ^ d ≤
        (C : ℝ) * ((ei x).length + 1 : ℝ) ^ (d_f + d) * (2 : ℝ) ^ E x := by
      have h1 : (C : ℝ) * ((ei x).length + 1 : ℝ) ^ d ≤
          (C : ℝ) * ((ei x).length + 1 : ℝ) ^ (d_f + d) :=
        mul_le_mul_of_nonneg_left hp2 (Nat.cast_nonneg C)
      have h2 : (C : ℝ) * ((ei x).length + 1 : ℝ) ^ (d_f + d) * 1 ≤
          (C : ℝ) * ((ei x).length + 1 : ℝ) ^ (d_f + d) * (2 : ℝ) ^ E x :=
        mul_le_mul_of_nonneg_left htwo (mul_nonneg (Nat.cast_nonneg C) hpow_nonneg)
      linarith
    cases h : ok x
    · simp only [h, Bool.false_eq_true, ↓reduceIte, Nat.cast_zero, zero_add] at hx
      have hCF : (0 : ℝ) ≤ (C_f : ℝ) * ((ei x).length + 1 : ℝ) ^ (d_f + d) * (2 : ℝ) ^ E x := by
        positivity
      push_cast
      linarith
    · simp only [h, ↓reduceIte] at hx
      have hf : (c_fast.time x : ℝ) ≤
          (C_f : ℝ) * ((ei x).length + 1 : ℝ) ^ (d_f + d) * (2 : ℝ) ^ E x := by
        refine (ht_fast x h).trans ?_
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hp1 (Nat.cast_nonneg C_f)) (by positivity)
      push_cast
      linarith
  refine ⟨C_f + C, d_f + d, cert.space, hS, hreal,
    cert.computes.mono (C_f + C + 1) (fun x => ?_)
      (fun x => (Nat.le_succ _).trans (Nat.le_mul_of_pos_left _ (Nat.succ_pos _)))⟩
  have hceil : (2 : ℝ) ^ E x ≤ (⌈(2 : ℝ) ^ E x⌉₊ : ℝ) := Nat.le_ceil _
  have hnat_real : (cert.time x : ℝ) ≤
      (((C_f + C) * (((ei x).length + 1) ^ (d_f + d) * ⌈(2 : ℝ) ^ E x⌉₊) : ℕ) : ℝ) := by
    refine (hreal x).trans ?_
    push_cast
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_left hceil (by positivity)
  have hnat : cert.time x ≤ (C_f + C) * (((ei x).length + 1) ^ (d_f + d) * ⌈(2 : ℝ) ^ E x⌉₊) := by
    exact_mod_cast hnat_real
  exact hnat.trans (Nat.mul_le_mul (Nat.le_succ _) (Nat.le_succ _))

end GuardedFallback

end Cslib.GenericRAM.ExhaustiveCountFallback
