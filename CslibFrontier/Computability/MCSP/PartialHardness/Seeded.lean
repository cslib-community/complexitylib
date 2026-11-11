/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.Promise.Randomized
public import CslibFrontier.Computability.MCSP.PartialHardness.Evaluator
public import CslibFrontier.Computability.MCSP.PartialNP
public import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import CslibFrontier.Computability.Complexity.Problems.CMMSA.Size
import CslibFrontier.Computability.MCSP.PartialHardness.EvaluatorPolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Log
import CslibFrontier.Computability.PCP.Approximation.LabelCover.MinRep
import CslibFrontier.Foundations.Data.BitString.FunctionTables
import CslibFrontier.Foundations.Data.Nat.Log

/-!
# Seeding the CMMSA construction with random tables

The library's randomized reductions from `GapCMMSA` to partial MCSP (issue #4362, route B) and to
MINKT\* (issue #4447) read the functions of the variables of a CMMSA instance `I` from a random
string. This module provides the part they share. The reductions and their analysis are the
library's own; [Hirahara2022] fixes only the shape of the problems.

* **Scale.** `lamOf λ₀ I = λ₀ (|I| + 1)²`, for the length `|I|` of the encoding of `I`.
* **Seed.** Variable `v` reads its table from the block `[v B, v B + 2 ^ ℓ v)` of the random string,
  where `B = 2 ^ W` for the seed width `W` (`seededFunctions`, a `BitString.decodeTables`). Bits
  outside the blocks are ignored. The string has length `(seedLen λ₀).eval |I|`, a polynomial.
* **Pattern.** `seededPattern λ₀ Δ k I r` lists the entries of the CMMSA partial truth table
  under the seeded functions, and is polynomial-time in `(I, r)`
  (`computableInPolyTime_seededPattern`).
* **Randomized reduction.** `rpReducible_of_seeded` turns any map `out I f` of the instance and the
  functions into a randomized reduction from `X` to `Y`, given that `out I f` is polynomial-time
  under the seeded functions, lies in `Y.yes` for every `f` when `I ∈ X.yes`, and lies outside
  `Y.no` for at most a third of the `f` when `I ∈ X.no`. Each seeded function is equally likely
  (`BitString.mul_card_filter_decodeTables_mem_le`), so the count of functions becomes a count of
  random strings.
* **Parameters.** `exists_hard_params` gives `Δ`, an odd `k`, a bias `δ₀` and a gap `g` with the
  hypotheses of the soundness count for `P = 1`, and with `GapCMMSA Δ g 1` `NP`-hard.

`rpReducible_of_seeded` and `exists_hard_params` are library results, with no counterpart in
[Hirahara2022].

## Main definitions

* `Cslib.PartialMCSP.FromCMMSA.lamOf`: the scale `λ₀ (|I| + 1)²`.
* `Cslib.PartialMCSP.FromCMMSA.seedLen`: the length of the random string.
* `Cslib.PartialMCSP.FromCMMSA.seededFunctions`: the functions read from a random string.
* `Cslib.PartialMCSP.FromCMMSA.seededTables`: their explicit tables, read from the string.
* `Cslib.PartialMCSP.FromCMMSA.seededPattern`: the partial truth table under the seeded functions.

## Main results

* `Cslib.PartialMCSP.FromCMMSA.mul_sq_le_lamOf`, `one_le_lamOf`: bounds on the scale.
* `Cslib.PartialMCSP.FromCMMSA.computableInPolyTime_lamOf`, `computableInPolyTime_seededTables`,
  `computableInPolyTime_seededPattern`: the scale, the tables and the pattern are polynomial-time.
* `Cslib.PartialMCSP.FromCMMSA.isVarTable_seededTables`: the tables are those of the seeded
  functions; `tableN_seededTables`: evaluating them gives the pattern, and `seededPattern_eq_ofFn`
  lists its entries.
* `Cslib.PartialMCSP.FromCMMSA.seedLen_eval`: the length of the random string.
* `Cslib.PartialMCSP.FromCMMSA.two_pow_varLength_le_two_pow_seedWidth`,
  `length_weights_mul_le_seedLen`: every table fits in its block, and the blocks fit in the random
  string.
* `Cslib.PartialMCSP.FromCMMSA.rpReducible_of_seeded`: the generic randomized reduction.
* `Cslib.PartialMCSP.FromCMMSA.exists_hard_params`: the parameters.

## References

* [S. Hirahara, *NP-Hardness of Learning Programs and Partial MCSP*][Hirahara2022]
-/

public section

namespace Cslib.PartialMCSP.FromCMMSA

open Cslib.Complexity Cslib.Logic.PL Turing.MultiTapeTM Finset

/-! ### The scale and the seed -/

/-- The scale `λ₀ (|I| + 1)²`, for the length `|I|` of the encoding of `I`. -/
def lamOf (lam₀ : ℕ) (I : CMMSAInstance) : ℕ := lam₀ * ((CMMSAInstance.encoding I).length + 1) ^ 2

/-- The scale is at least `λ₀ (N + 1)²` for every `N` at most the length of the encoding. -/
theorem mul_sq_le_lamOf {lam₀ N : ℕ} {I : CMMSAInstance}
    (hN : N ≤ (CMMSAInstance.encoding I).length) :
    lam₀ * (N + 1) ^ 2 ≤ lamOf lam₀ I := by
  unfold lamOf
  gcongr

/-- The scale is positive when `λ₀` is. -/
theorem one_le_lamOf {lam₀ : ℕ} (h : 1 ≤ lam₀) (I : CMMSAInstance) : 1 ≤ lamOf lam₀ I :=
  le_trans (by simpa using h) (mul_sq_le_lamOf (lam₀ := lam₀) (N := 0) (Nat.zero_le _))

/-- The length of the random string: `2 (λ₀ + 1) (N + 1) ^ 4` for an encoding of length `N`. -/
noncomputable def seedLen (lam₀ : ℕ) : Polynomial ℕ :=
  Polynomial.C (2 * (lam₀ + 1)) * (Polynomial.X + 1) ^ 4

/-- The length of the random string for an encoding of length `N`. -/
theorem seedLen_eval (lam₀ N : ℕ) : (seedLen lam₀).eval N = 2 * (lam₀ + 1) * (N + 1) ^ 4 := by
  simp [seedLen]

/-- The functions of the variables read from a random string `r`: variable `v` reads its table, in
the order of `BitString.equivFin`, from the bits of `r` starting at `v 2 ^ W`. -/
def seededFunctions (lam₀ : ℕ) (I : CMMSAInstance) (r : List Bool) :
    VarFunctions I (lamOf lam₀ I) :=
  BitString.decodeTables (2 ^ seedWidth I (lamOf lam₀ I)) (fun v => varLength I (lamOf lam₀ I) v) r

/-- Every block holds the table of its variable. -/
theorem two_pow_varLength_le_two_pow_seedWidth {I : CMMSAInstance} {lam : ℕ}
    (v : Fin I.weights.length) : 2 ^ varLength I lam v ≤ 2 ^ seedWidth I lam :=
  Nat.pow_le_pow_right two_pos (varLength_le_seedWidth v.isLt)

/-- The blocks fit in the random string. -/
theorem length_weights_mul_le_seedLen (lam₀ : ℕ) (I : CMMSAInstance) :
    I.weights.length * 2 ^ seedWidth I (lamOf lam₀ I) ≤
      (seedLen lam₀).eval (CMMSAInstance.encoding I).length := by
  set N := (CMMSAInstance.encoding I).length
  have hn : I.weights.length ≤ N := CMMSAInstance.length_weights_le I
  have hw : maxWeight I ≤ N := maxWeight_le fun w hw => CMMSAInstance.le_of_mem_weights I hw
  have hB : 2 ^ seedWidth I (lamOf lam₀ I) ≤ 2 * (N * (lam₀ * (N + 1) ^ 2) + 1) := by
    rw [seedWidth_eq]
    refine (Nat.two_pow_clog_two_le _).trans ?_
    unfold lamOf
    gcongr
  rw [seedLen_eval]
  calc I.weights.length * 2 ^ seedWidth I (lamOf lam₀ I)
      ≤ N * (2 * (N * (lam₀ * (N + 1) ^ 2) + 1)) := Nat.mul_le_mul hn hB
    _ ≤ 2 * (lam₀ + 1) * (N + 1) ^ 4 := by
      have h1 : N ≤ N + 1 := Nat.le_succ N
      have h2 : N * (N * (lam₀ * (N + 1) ^ 2)) ≤
          (N + 1) * ((N + 1) * (lam₀ * (N + 1) ^ 2)) := by
        gcongr
      have h3 : N ≤ (N + 1) ^ 4 := h1.trans (Nat.le_self_pow (by norm_num) _)
      nlinarith

/-! ### The explicit tables -/

/-- The explicit tables of the seeded functions, read from the random string: entry `y` of
variable `v` is bit `v 2 ^ W + y`. -/
def seededTables (lam₀ : ℕ) (I : CMMSAInstance) (r : List Bool) : List (List Bool) :=
  (List.range I.weights.length).map fun v =>
    (List.range (2 ^ varLength I (lamOf lam₀ I) v)).map fun y =>
      r.getD (v * 2 ^ seedWidth I (lamOf lam₀ I) + y) false

/-- The explicit tables are the tables of the seeded functions. -/
theorem isVarTable_seededTables (lam₀ : ℕ) (I : CMMSAInstance) (r : List Bool) (v : ℕ) :
    IsVarTable I (lamOf lam₀ I) (seededFunctions lam₀ I r) (seededTables lam₀ I r) v := by
  intro y
  by_cases hv : v < I.weights.length
  · have hy := (BitString.equivFin _ y).isLt
    simp [seededTables, evalVar, hv, List.getD_eq_getElem?_getD, hy, seededFunctions,
      BitString.zeroExtend_self]
  · simp [seededTables, evalVar, hv, List.getD_eq_getElem?_getD]

variable {α : Type} {input : α ↪ List Bool}

/-- The scale is polynomial-time, in unary. -/
@[fun_prop]
theorem computableInPolyTime_lamOf (lam₀ : ℕ) {I : α → CMMSAInstance}
    (hI : ComputableInPolyTime I input CMMSAInstance.encoding) :
    ComputableInPolyTime (fun a => lamOf lam₀ (I a)) input encUnary :=
  ComputableInPolyTime.unary_mul' (ComputableInPolyTime.const lam₀)
    ((ComputableInPolyTime.unary_pow 2).comp (ComputableInPolyTime.unary_add'
      ((ComputableInPolyTime.encoding_length _).comp hI) (ComputableInPolyTime.const 1)))

/-- The explicit tables are polynomial-time in the instance and the random string. -/
@[fun_prop]
theorem computableInPolyTime_seededTables (lam₀ : ℕ) {I : α → CMMSAInstance}
    {r : α → List Bool} (hI : ComputableInPolyTime I input CMMSAInstance.encoding)
    (hr : ComputableInPolyTime r input encBits) :
    ComputableInPolyTime (fun a => seededTables lam₀ (I a) (r a)) input (encList encBits) := by
  have hL := computableInPolyTime_lamOf lam₀ hI
  have h₁ := ComputableInPolyTime.fst input encUnary
  have h₂ := ComputableInPolyTime.snd input encUnary
  have h₁₁ := ComputableInPolyTime.fst (encPair input encUnary) encUnary
  have hy := ComputableInPolyTime.snd (encPair input encUnary) encUnary
  -- the block size `2 ^ W`, from the triple `((a, v), y)`
  have hB := ComputableInPolyTime.unary_pow_clog_const (ComputableInPolyTime.unary_mul'
    (computableInPolyTime_maxWeight ((hI.comp h₁).comp h₁₁)) ((hL.comp h₁).comp h₁₁)) 2 2
  simp only [← seedWidth_eq] at hB
  -- the table length `2 ^ ℓ v`, from the pair `(a, v)`
  have hlen := ComputableInPolyTime.unary_pow_clog_const (ComputableInPolyTime.unary_mul'
    (ComputableInPolyTime.listGetD_binary 0 (CMMSAInstance.isPolyTime_weights (hI.comp h₁))
      (ComputableInPolyTime.unary_to_binary.comp h₂)) (hL.comp h₁)) 2 2
  unfold seededTables
  exact ComputableInPolyTime.mapWithInput (ComputableInPolyTime.unary_range'
      ((ComputableInPolyTime.length_list _).comp (CMMSAInstance.isPolyTime_weights hI)))
    (ComputableInPolyTime.mapToBitsWithInput (ComputableInPolyTime.unary_range' hlen)
      (ComputableInPolyTime.bitsGetDWithInput ((hr.comp h₁).comp h₁₁)
        (ComputableInPolyTime.unary_add' (ComputableInPolyTime.unary_mul' (h₂.comp h₁₁) hB) hy)
        false))

/-! ### The pattern -/

/-- The partial truth table of the CMMSA construction under the seeded functions. -/
def seededPattern (lam₀ Δ k : ℕ) (I : CMMSAInstance) (r : List Bool) : List (Option Bool) :=
  List.ofFn fun i =>
    entry (Δ := Δ) (k := k) (seededFunctions lam₀ I r) ((BitString.equivFin _).symm i)

/-- The pattern lists the entries under the seeded functions. -/
theorem seededPattern_eq_ofFn (lam₀ Δ k : ℕ) (I : CMMSAInstance) (r : List Bool) :
    seededPattern lam₀ Δ k I r = List.ofFn fun i =>
      entry (Δ := Δ) (k := k) (seededFunctions lam₀ I r) ((BitString.equivFin _).symm i) := by
  rw [seededPattern]

/-- The pattern is the explicit-table evaluation on the seeded tables. -/
theorem tableN_seededTables (lam₀ Δ k : ℕ) (I : CMMSAInstance) (r : List Bool) :
    tableN I Δ k (lamOf lam₀ I) (seededTables lam₀ I r) = seededPattern lam₀ Δ k I r :=
  tableN_eq_ofFn (isVarTable_seededTables lam₀ I r) 0

/-- **The pattern is polynomial-time** in the instance and the random string, for fixed `λ₀`, `Δ`
and `k`. -/
@[fun_prop]
theorem computableInPolyTime_seededPattern (lam₀ Δ k : ℕ) {I : α → CMMSAInstance}
    {r : α → List Bool} (hI : ComputableInPolyTime I input CMMSAInstance.encoding)
    (hr : ComputableInPolyTime r input encBits) :
    ComputableInPolyTime (fun a => seededPattern lam₀ Δ k (I a) (r a)) input
      PartialMCSP.encTable := by
  simp only [← tableN_seededTables]
  exact computableInPolyTime_tableN Δ k hI (computableInPolyTime_lamOf lam₀ hI)
    (computableInPolyTime_seededTables lam₀ hI hr)

/-! ### The randomized reduction -/

open Classical in
/-- **A seeded map is a randomized reduction.** Let `out I f` be computed from a CMMSA instance and
the functions of its variables at the scale `lamOf λ₀ I`. Suppose it is polynomial-time under the
seeded functions, lies in `Y.yes` for every `f` when `I ∈ X.yes`, and lies outside `Y.no` for at
most a third of the functions `f` when `I ∈ X.no`. Then `X` reduces to `Y` by a randomized
reduction with one-sided error. This is a library result (issue #4362, route B). -/
theorem rpReducible_of_seeded {β : Type} {encB : β ↪ List Bool}
    {X : PromiseProblem CMMSAInstance} {Y : PromiseProblem β} (lam₀ : ℕ)
    (out : (I : CMMSAInstance) → VarFunctions I (lamOf lam₀ I) → β)
    (hout : ComputableInPolyTime (fun p : CMMSAInstance × List Bool =>
      out p.1 (seededFunctions lam₀ p.1 p.2)) (encPair CMMSAInstance.encoding encBits) encB)
    (hyes : ∀ I ∈ X.yes, ∀ f, out I f ∈ Y.yes)
    (hno : ∀ I ∈ X.no,
      3 * #{f | out I f ∉ Y.no} ≤ Fintype.card (VarFunctions I (lamOf lam₀ I))) :
    PromiseProblem.RPReducible CMMSAInstance.encoding encB X Y := by
  refine PromiseProblem.rpReducible_iff_exists_seeded.mpr
    ⟨seedLen lam₀, _, hout, fun I hI r => hyes I hI _, fun I hI => ?_⟩
  set q := (seedLen lam₀).eval (CMMSAInstance.encoding I).length
  have hbad : 3 * #{r : Fin q → Bool | out I (seededFunctions lam₀ I (List.ofFn r)) ∉ Y.no} ≤
      2 ^ q := by
    have := BitString.mul_card_filter_decodeTables_mem_le
      (B := 2 ^ seedWidth I (lamOf lam₀ I)) (ℓ := fun v => varLength I (lamOf lam₀ I) v)
      (p := q) (a := 3) (b := 1) two_pow_varLength_le_two_pow_seedWidth
      (length_weights_mul_le_seedLen lam₀ I) (S := {f | out I f ∉ Y.no}) (by simpa using hno I hI)
    rw [one_mul] at this
    convert this using 3
    ext r
    rw [Finset.mem_filter, Finset.mem_filter]
    simp [seededFunctions]
  have hsplit : #{r : Fin q → Bool | out I (seededFunctions lam₀ I (List.ofFn r)) ∉ Y.no} +
      #{r : Fin q → Bool | out I (seededFunctions lam₀ I (List.ofFn r)) ∈ Y.no} = 2 ^ q := by
    rw [add_comm, card_filter_add_card_filter_not, card_univ, Fintype.card_fun, Fintype.card_bool,
      Fintype.card_fin]
  dsimp only
  omega

/-! ### The parameters -/

/-- **Parameters for the reductions.** There are a bound `Δ`, an odd `k`, a bias `δ₀` and a gap `g`
satisfying the hypotheses of the soundness count for `P = 1`, with room to spare
(`24 log 2 < g (log 2 - H(δ₀))`), such that `GapCMMSA Δ g 1` is `NP`-hard. Clients get only these
facts (the proof takes `δ₀ = 1/4`). This is a library result (issue #4362, route B). -/
theorem exists_hard_params : ∃ (Δ k : ℕ) (δ₀ g : ℝ), Odd k ∧ 0 ≤ δ₀ ∧ δ₀ ≤ 1 / 2 ∧
    (1 - 2 * δ₀) ^ k ≤ 1 / (2 * (Δ : ℝ) ^ 2) ∧
    24 * Real.log 2 < g * (Real.log 2 - Real.binEntropy δ₀) ∧
    PromiseProblem.NPHard CMMSAInstance.encoding (GapCMMSA Δ g 1) := by
  set γ := Real.log 2 - Real.binEntropy (1 / 4)
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hγ : 0 < γ := sub_pos.2 (Real.binEntropy_lt_log_two.2 (by norm_num))
  have hγ' : γ ≤ Real.log 2 :=
    sub_le_self _ (Real.binEntropy_nonneg (by norm_num) (by norm_num))
  have hg : 1 ≤ 25 * Real.log 2 / γ := by
    rw [le_div_iff₀ hγ]
    linarith
  obtain ⟨Δ₀, hΔ₀⟩ := exists_GapCMMSA_npHard hg
  refine ⟨Δ₀ + 1, 2 * (Δ₀ + 1) ^ 2 + 1, 1 / 4, 25 * Real.log 2 / γ, odd_two_mul_add_one _,
    by norm_num, by norm_num, ?_, ?_, hΔ₀.mono (GapCMMSA.yes_mono (Nat.le_succ Δ₀))
      (GapCMMSA.no_mono (Nat.le_succ Δ₀))⟩
  · have hnat : 2 * (Δ₀ + 1) ^ 2 ≤ 2 ^ (2 * (Δ₀ + 1) ^ 2 + 1) :=
      Nat.lt_two_pow_self.le.trans (Nat.pow_le_pow_right two_pos (Nat.le_succ _))
    have hreal : (2 * ((Δ₀ + 1 : ℕ) : ℝ) ^ 2) ≤ (2 : ℝ) ^ (2 * (Δ₀ + 1) ^ 2 + 1) := by
      exact_mod_cast hnat
    rw [show (1 : ℝ) - 2 * (1 / 4) = 1 / 2 by norm_num, one_div_pow]
    exact one_div_le_one_div_of_le (by positivity) hreal
  · rw [div_mul_cancel₀ _ hγ.ne']
    linarith

end Cslib.PartialMCSP.FromCMMSA
