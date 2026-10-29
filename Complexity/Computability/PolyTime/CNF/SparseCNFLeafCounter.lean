/-
Copyright (c) 2026 Anton Kovsharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anton Kovsharov
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.Complexity.Problems.SAT
public import Complexity.Computability.GenericRAM.Native.ExhaustiveCountFallback
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.List.Size
public import Complexity.Computability.PolyTime.BitString.InitialTestsSearch
public import Complexity.Computability.PolyTime.CNF.GreedyParityContext
public import Complexity.Computability.PolyTime.CNF.SparsePolyCompile
public import Complexity.Logics.Propositional.CNF.ModelCount.DenseRelabel
public import Complexity.Logics.Propositional.CNF.SparseParityCounter
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Mathlib.Data.List.GetD
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Native sparse `k`-CNF leaf model counter and occurring-support normalization

Implements the deterministic sparse `k`-CNF model-counting algorithm of Section 6.3 (equation
(6.4), printed p. 43) of [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH] on
native multi-tape Turing machines, parameterized over a sparse `𝔽₂` polynomial-system counter:
- **Encoded procedures**: `Cslib.Logic.PL.CNF.validDeclaredInput`, `hasEmptyClause`, and
  `entersSparseFastPath` are `ComputableInPolyTime` guards; `compiledRowCounter`,
  `sparseCNFFastPath`, `sparseCNFDeclaredCounter`, `Cslib.Logic.PL.CNF.normalizeDeclaredLeaf`, and
  `sparseCNFLeafCounter` are certified by `sparseCNFDeclaredCertificate`,
  `normalizeDeclaredLeafCertificate`, and `sparseCNFLeafCertificate`.
- **Unencoded specifications**: `IsCompiledSparseSystem`, `sparseCNFTimeBound`, and
  `ValidPolyTimeBound` state structural equation invariants and split runtime hypotheses.
- **Total fallbacks**: `sparseCNFDeclaredCounter` returns `0` when `validDeclaredInput = false`,
  `[] ∈ ψ`, or `N ≥ N₀ ∧ ψ.length > B * N`; `2 ^ N` on `ψ = []`; and `countCNFExhaustive (N, ψ)`
  (defaulting variables `≥ N` to `false`) when `N < N₀`. `normalizeDeclaredLeaf` shifts right by
  `N - ψ.distinctVars.length` to recover `ψ.modelCount` within `≤ 2 ^ ψ.numVars`.

## Main definitions

* `hasEmptyClause`, `entersSparseFastPath`, `IsCompiledSparseSystem`, `compiledRowCounter`
* `sparseCNFFastPath`, `sparseCNFDeclaredCounter`, `sparseCNFLeafCounter`
* `sparseCNFTimeBound`, `ValidPolyTimeBound`
* `sparseCNFDeclaredCertificate`, `normalizeDeclaredLeafCertificate`, `sparseCNFLeafCertificate`

## Main results

* `isCompiledSparseSystem_compileParitySystemBounded`,
  `commonZeroCount_compileParitySystemBounded_eq_numPassing`
* `sparseCNFDeclaredCounter_le_two_pow`, `sparseCNFDeclaredCounter_eq_modelCountOn`,
  `sparseCNFDeclaredCounter_exhaustive_eq_modelCountOn`
* `sparseCNFLeafCounter_le_two_pow_numVars`, `sparseCNFLeafCounter_eq_modelCount`,
  `sparseCNFLeafCounter_exhaustive_eq_modelCount`
* `polyBounded_sparseCNFDeclaredCertificate_space`, `exists_sparseCNFDeclaredCertificate_bounds`,
  `computableInO_sparseCNFDeclaredCounter`, `computableInO_normalizeDeclaredLeaf`,
  `polyBounded_sparseCNFLeafCertificate_space`, `exists_sparseCNFLeafCertificate_bounds`,
  `computableInO_sparseCNFLeafCounter`

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], §6.3, eq. (6.4), p. 43.
-/

@[expose] public section

namespace Cslib.Complexity.SparseCNFLeafCounter

open Finset Cslib.BitString Cslib.GenericRAM Cslib.GenericRAM.ExhaustiveCountFallback
open Cslib.Logic.PL Cslib.Logic.PL.CNF Cslib.Logic.PL.CNF.GreedyContext
open Cslib.Complexity.InitialTestsSearch Turing.MultiTapeTM

/-! ### 1. Guards, Compiled-System Invariant, and Core Definitions -/

/-- Boolean check for whether `ψ` contains an empty clause `[]`. -/
def hasEmptyClause (ψ : CNF ℕ) : Bool := ψ.any List.isEmpty

/-- Guard characterizing inputs `(N, B, ψ)` entering the Section 6.3 parity-test fast path. -/
def entersSparseFastPath (k N₀ N B : ℕ) (ψ : CNF ℕ) : Bool :=
  validDeclaredInput k N ψ && !ψ.isEmpty && !hasEmptyClause ψ &&
    !decide (N < N₀) && decide (ψ.length ≤ B * N)

/-- Sparsity, canonicality, degree, and variable-range invariant for compiled `𝔽₂` systems. -/
def IsCompiledSparseSystem (k N maxEqs maxTerms : ℕ) (sys : List (List (List ℕ))) : Prop :=
  sys.length ≤ maxEqs ∧ ∀ eq ∈ sys, IsCanonicalEquation eq ∧ eq.length ≤ maxTerms ∧
    ∀ mon ∈ eq, mon.length ≤ k ∧ ∀ v ∈ mon, v < N

/-- Evaluates `polyCounter (N, compileParitySystemBounded k ψ rows)` when `rows.length ≤ 6 * N`. -/
def compiledRowCounter (k : ℕ) (polyCounter : ℕ × List (List (List ℕ)) → ℕ)
    (q : (ℕ × CNF ℕ) × List (List Bool)) : ℕ :=
  if decide (q.2.length ≤ 6 * q.1.1) then
    polyCounter (q.1.1, compileParitySystemBounded k q.1.2 q.2)
  else 0

/-- Deterministic Section 6.3 fast path: initial Tanner rows via `initialTestsRows`, `3 * N` rounds
of `greedyParityRows`, and one final `compiledRowCounter` call capped at `2 ^ N`. -/
def sparseCNFFastPath (k N B : ℕ) (polyCounter : ℕ × List (List (List ℕ)) → ℕ) (ψ : CNF ℕ) : ℕ :=
  let m := ψ.length
  let finalRows := greedyParityRows (fun rows => compiledRowCounter k polyCounter ((N, ψ), rows))
    N m (greedyRowListLength B m) (initialTestsRows m B)
  min (2 ^ N) (compiledRowCounter k polyCounter ((N, ψ), finalRows))

/-- **Section 6.3 declared-range sparse `k`-CNF model counter.**
Returns `0` if invalid, `2 ^ N` on `[]`, `0` if `[] ∈ ψ`, `countCNFExhaustive (N, ψ)` if `N < N₀`,
`sparseCNFFastPath k N B polyCounter ψ` if `ψ.length ≤ B * N`, and `0` otherwise. -/
def sparseCNFDeclaredCounter {P : Type*} (NOf BOf : P → ℕ) (k N₀ : ℕ)
    (polyCounter : ℕ × List (List (List ℕ)) → ℕ) (x : P × CNF ℕ) : ℕ :=
  let N := NOf x.1; let B := BOf x.1; let ψ := x.2
  if validDeclaredInput k N ψ then
    if ψ.isEmpty then 2 ^ N
    else if hasEmptyClause ψ then 0
    else if decide (N < N₀) then countCNFExhaustive (N, ψ)
    else if decide (ψ.length ≤ B * N) then sparseCNFFastPath k N B polyCounter ψ
    else 0
  else 0

/-- Normalized Section 6.3 sparse `k`-CNF leaf provider.
Returns `ψ.modelCount` on valid sparse or below-threshold inputs, as well as empty formulas and
formulas containing an empty clause. The supplied `polyCounter` must be exact on the compiled sparse
systems required by `sparseCNFLeafCounter_eq_modelCount`. -/
def sparseCNFLeafCounter {P : Type*} (NOf BOf : P → ℕ) (k N₀ : ℕ)
    (polyCounter : ℕ × List (List (List ℕ)) → ℕ) (x : P × CNF ℕ) : ℕ :=
  normalizeDeclaredLeaf NOf (sparseCNFDeclaredCounter NOf BOf k N₀ polyCounter) x

/-! ### 2. Structural & Semantic Proofs for Guards, Compilation, and Greedy Search -/

theorem hasEmptyClause_eq_true_iff {ψ : CNF ℕ} : hasEmptyClause ψ = true ↔ [] ∈ ψ := by
  simp only [hasEmptyClause, List.any_eq_true, List.isEmpty_iff]
  exact ⟨fun ⟨_, hc, hnil⟩ => hnil ▸ hc, fun h => ⟨[], h, rfl⟩⟩

theorem entersSparseFastPath_eq_true_iff {k N₀ N B : ℕ} {ψ : CNF ℕ} :
    entersSparseFastPath k N₀ N B ψ = true ↔
      validDeclaredInput k N ψ = true ∧ ψ.isEmpty = false ∧ hasEmptyClause ψ = false ∧
        N₀ ≤ N ∧ ψ.length ≤ B * N := by
  simp only [entersSparseFastPath, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
    decide_eq_true_eq, not_lt, and_assoc]

private theorem pos_of_nonempty_nonnil_valid {k N : ℕ} {ψ : CNF ℕ}
    (hvalid : validDeclaredInput k N ψ = true) (hne : ψ.isEmpty = false)
    (hnil : hasEmptyClause ψ = false) : 1 ≤ N ∧ 1 ≤ ψ.length := by
  obtain ⟨_, hsub⟩ := validDeclaredInput_eq_true_iff.mp hvalid
  rcases ψ with _ | ⟨_ | ⟨l, ls⟩, cs⟩
  · simp at hne
  · exact False.elim (Bool.false_ne_true (hnil ▸ hasEmptyClause_eq_true_iff.mpr List.mem_cons_self))
  · have hlt := Finset.mem_range.mp (hsub (List.mem_toFinset.mpr
      (CNF.mem_vars.mpr ⟨l :: ls, List.mem_cons_self, l.2, List.mem_cons_self⟩)))
    exact ⟨by omega, by simp⟩

private theorem greedyRowListLength_pos {B m : ℕ} (hB : 1 ≤ B) : 1 ≤ greedyRowListLength B m := by
  unfold greedyRowListLength
  have := Nat.one_le_pow 2 B hB; have := Nat.one_le_pow 2 (Nat.log 2 m + 1) (Nat.succ_pos _)
  nlinarith

private theorem greedyRowListLength_le_initialRowWeightBound (B m : ℕ) :
    greedyRowListLength B m ≤ initialRowWeightBound B m := by
  unfold greedyRowListLength initialRowWeightBound
  have := Nat.pow_le_pow_right (Nat.succ_pos (Nat.log 2 m)) (by decide : 2 ≤ 3); nlinarith

/-- Every `compileParitySystemBounded k ψ rows` on a width-`≤ k` formula with variables `< N`,
`rows.length ≤ maxEqs`, and row Hamming weights `≤ W` satisfies `IsCompiledSparseSystem`. -/
theorem isCompiledSparseSystem_compileParitySystemBounded {k N maxEqs W : ℕ} {ψ : CNF ℕ}
    (hw : ∀ c ∈ ψ, c.length ≤ k) (hsub : ψ.vars.toFinset ⊆ Finset.range N)
    {rows : List (List Bool)} (hlen : rows.length ≤ maxEqs) (hwt : ∀ r ∈ rows, r.count true ≤ W) :
    IsCompiledSparseSystem k N maxEqs (W * 2 ^ k) (compileParitySystemBounded k ψ rows) := by
  rw [compileParitySystemBounded_eq_compileParitySystem hw]
  refine ⟨by simpa only [compileParitySystem, List.length_map] using hlen, fun eq heq => ?_⟩
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp heq
  refine ⟨isCanonicalEquation_compileParityRow ψ r,
    (length_compileParityRow_le hw r).trans (Nat.mul_le_mul_right _ (hwt r hr)),
    fun mon hmon => ⟨length_mem_compileParityRow_le hw r hmon, fun v hv => ?_⟩⟩
  exact Finset.mem_range.mp
    (hsub (List.mem_toFinset.mpr (mem_vars_of_mem_compileParityRow hmon hv)))

private def toFinCNF (N : ℕ) (hN : 1 ≤ N) (ψ : CNF ℕ) : CNF (Fin N) :=
  ψ.relabel fun v => ⟨v % N, Nat.mod_lt v hN⟩

private def extendFinAssign {N : ℕ} (σ : Fin N → Bool) (v : ℕ) : Bool :=
  (List.ofFn σ).getD v false

private theorem extendFinAssign_lt {N : ℕ} (σ : Fin N → Bool) {v : ℕ} (hlt : v < N) :
    extendFinAssign σ v = σ ⟨v, hlt⟩ := by
  rw [extendFinAssign, List.getD_eq_getElem _ _ (by simp [hlt]), List.getElem_ofFn]

private theorem eval_toFinCNF_eq {N : ℕ} (hN : 1 ≤ N) {ψ : CNF ℕ}
    (hsub : ψ.vars.toFinset ⊆ Finset.range N) (σ : Fin N → Bool) :
    (toFinCNF N hN ψ).eval σ = ψ.eval (extendFinAssign σ) := by
  rw [toFinCNF, CNF.eval_relabel]; refine CNF.eval_congr fun v hv => ?_
  have hlt := Finset.mem_range.mp (hsub (List.mem_toFinset.mpr hv))
  simp only [Function.comp_apply, Nat.mod_eq_of_lt hlt, extendFinAssign_lt σ hlt]

private theorem get_eval_toFinCNF_eq {N : ℕ} (hN : 1 ≤ N) {ψ : CNF ℕ}
    (hsub : ψ.vars.toFinset ⊆ Finset.range N) (σ : Fin N → Bool)
    (e : Fin (toFinCNF N hN ψ).length) :
    ((toFinCNF N hN ψ).get e).eval σ =
      (ψ.get ⟨e.1, by simpa only [toFinCNF, CNF.relabel, List.length_map] using e.2⟩).eval
        (extendFinAssign σ) := by
  have he_lt : e.1 < ψ.length := by simpa only [toFinCNF, CNF.relabel, List.length_map] using e.2
  change ((ψ.map (Clause.relabel fun v => ⟨v % N, Nat.mod_lt v hN⟩))[e.1]).eval σ =
    ψ[e.1].eval (extendFinAssign σ)
  rw [List.getElem_map, Clause.eval_relabel]; apply Bool.eq_iff_iff.mpr
  simp only [Clause.eval_eq_true_iff]
  refine exists_congr fun b => and_congr_right fun hb1 => ?_
  have hlt := Finset.mem_range.mp (hsub (List.mem_toFinset.mpr
    (CNF.mem_vars.mpr ⟨ψ[e.1], List.getElem_mem he_lt, b.2, hb1⟩)))
  simp only [Function.comp_apply, Nat.mod_eq_of_lt hlt, extendFinAssign_lt σ hlt]

private theorem passesTests_toFinCNF_iff {N : ℕ} (hN : 1 ≤ N) {ψ : CNF ℕ}
    (hsub : ψ.vars.toFinset ⊆ Finset.range N) (rows : List (List Bool)) (σ : Fin N → Bool) :
    PassesTests (toFinCNF N hN ψ).violations
        (rows.map (ofList (toFinCNF N hN ψ).length)) σ ↔
      PassesTests ψ.violations (rows.map fun r (e : Fin ψ.length) => r.getD e.1 false)
        (extendFinAssign σ) := by
  have hlen : (toFinCNF N hN ψ).length = ψ.length := by
    simp only [toFinCNF, CNF.relabel, List.length_map]
  simp only [PassesTests, List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  refine forall₂_congr fun r _ => ?_
  rw [show ofList (toFinCNF N hN ψ).length r ⬝ᵥ (toFinCNF N hN ψ).violations σ =
      (fun e : Fin ψ.length => r.getD e.1 false) ⬝ᵥ ψ.violations (extendFinAssign σ) from
    Fintype.sum_equiv (finCongr hlen) _ _ fun i => by
      simp only [finCongr_apply, Fin.val_cast, ofList, CNF.violations,
        get_eval_toFinCNF_eq hN hsub]; rfl]

private theorem card_sat_toFinCNF_eq_modelCountOn {N : ℕ} (hN : 1 ≤ N) {ψ : CNF ℕ}
    (hsub : ψ.vars.toFinset ⊆ Finset.range N) :
    #{σ : Fin N → Bool | (toFinCNF N hN ψ).eval σ = true} = ψ.modelCountOn (Finset.range N) := by
  let eqv : (Fin N → Bool) ≃ (↥(Finset.range N) → Bool) :=
    ⟨fun σ v => σ ⟨v.1, Finset.mem_range.mp v.2⟩,
      fun τ i => τ ⟨i.1, Finset.mem_range.mpr i.2⟩, fun _ => rfl, fun _ => rfl⟩
  have heval (σ : Fin N → Bool) : (toFinCNF N hN ψ).eval σ =
      ψ.eval (fun v => if hv : v ∈ Finset.range N then eqv σ ⟨v, hv⟩ else false) := by
    rw [eval_toFinCNF_eq hN hsub σ]; refine CNF.eval_congr fun v hv => ?_
    have hlt := Finset.mem_range.mp (hsub (List.mem_toFinset.mpr hv))
    simp only [Finset.mem_range.mpr hlt, ↓reduceDIte, extendFinAssign_lt σ hlt]; rfl
  rw [CNF.modelCountOn]
  exact Finset.card_bij (fun σ _ => eqv σ)
    (fun σ hσ => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, heval] at hσ ⊢; exact hσ)
    (fun _ _ _ _ h => eqv.injective h)
    (fun τ hτ => ⟨eqv.symm τ, by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, heval, eqv.apply_symm_apply] at hτ ⊢
      exact hτ, eqv.apply_symm_apply τ⟩)

/-- **Semantic bridge to `equationToFinset` and `CNF.parityRowSystem`**: on a width-`≤ k` formula
`ψ` with variables `< N` (`1 ≤ N`), `commonZeroCount` on `compileParitySystemBounded k ψ rows`
equals both `numPassing` and `commonZeroCount` on `(relabel ... ψ).parityRowSystem`. -/
theorem commonZeroCount_compileParitySystemBounded_eq_numPassing {k N : ℕ} (hN : 1 ≤ N)
    {ψ : CNF ℕ} (hw : ∀ c ∈ ψ, c.length ≤ k) (hsub : ψ.vars.toFinset ⊆ Finset.range N)
    (rows : List (List Bool)) :
    let sys := compileParitySystemBounded k ψ rows
    let ψFin : CNF (Fin N) := ψ.relabel fun v => ⟨v % N, Nat.mod_lt v hN⟩
    commonZeroCount (Finset.univ : Finset (Fin sys.length))
        (fun i : Fin sys.length => equationToFinset N sys[i]) =
      numPassing ψFin.violations (rows.map (ofList ψFin.length)) ∧
    commonZeroCount (Finset.univ : Finset (Fin sys.length))
        (fun i : Fin sys.length => equationToFinset N sys[i]) =
      commonZeroCount Finset.univ (ψFin.parityRowSystem (rows.map (ofList ψFin.length))) := by
  dsimp only; set sys := compileParitySystemBounded k ψ rows
  have hsys_eq : sys = compileParitySystem ψ rows :=
    compileParitySystemBounded_eq_compileParitySystem hw rows
  have hcanon : ∀ eq ∈ sys, IsCanonicalEquation eq ∧ ∀ m ∈ eq, ∀ v ∈ m, v < N := by
    rw [hsys_eq]; intro eq heq; obtain ⟨r, _, rfl⟩ := List.mem_map.mp heq
    exact ⟨isCanonicalEquation_compileParityRow ψ r, fun m hm v hv =>
      Finset.mem_range.mp (hsub (List.mem_toFinset.mpr (mem_vars_of_mem_compileParityRow hm hv)))⟩
  have hnum : commonZeroCount (Finset.univ : Finset (Fin sys.length))
        (fun i : Fin sys.length => equationToFinset N sys[i]) =
      numPassing (toFinCNF N hN ψ).violations (rows.map (ofList (toFinCNF N hN ψ).length)) := by
    rw [← countSystemExhaustive_eq_commonZeroCount hcanon, countSystemExhaustive_eq_card_filter,
      hsys_eq, numPassing]
    congr 1; ext σ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      evalSystem_compileParitySystem_iff_passesTests, passesTests_toFinCNF_iff hN hsub]; rfl
  exact ⟨hnum, hnum.trans (CNF.commonZeroCount_parityRowSystem (toFinCNF N hN ψ) _).symm⟩

private theorem modelCountOn_le_two_pow_card {V : Type*} [DecidableEq V] (ψ : CNF V)
    (declared : Finset V) : ψ.modelCountOn declared ≤ 2 ^ declared.card := by
  rw [CNF.modelCountOn]; refine (Finset.card_filter_le _ _).trans ?_
  simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_coe, le_rfl]

/-- Unconditional upper bound: `sparseCNFDeclaredCounter` never exceeds `2 ^ NOf x.1`. -/
theorem sparseCNFDeclaredCounter_le_two_pow {P : Type*} (NOf BOf : P → ℕ) (k N₀ : ℕ)
    (polyCounter : ℕ × List (List (List ℕ)) → ℕ) (x : P × CNF ℕ) :
    sparseCNFDeclaredCounter NOf BOf k N₀ polyCounter x ≤ 2 ^ NOf x.1 := by
  unfold sparseCNFDeclaredCounter sparseCNFFastPath; dsimp only
  split_ifs
  · exact le_rfl
  · exact Nat.zero_le _
  · rw [countCNFExhaustive_eq_modelCountOn_range (NOf x.1) x.2]
    simpa only [Finset.card_range] using modelCountOn_le_two_pow_card x.2 (Finset.range (NOf x.1))
  · exact Nat.min_le_left _ _
  · exact Nat.zero_le _
  · exact Nat.zero_le _

/-- **Exactness of `sparseCNFDeclaredCounter` (§6.3, Lemmas 6.1–6.2).** -/
theorem sparseCNFDeclaredCounter_eq_modelCountOn {P : Type*} {NOf BOf : P → ℕ} {k N₀ : ℕ}
    {polyCounter : ℕ × List (List (List ℕ)) → ℕ} {p : P} {ψ : CNF ℕ}
    (hw : ∀ c ∈ ψ, c.length ≤ k) (hsub : ψ.vars.toFinset ⊆ Finset.range (NOf p))
    (hdom : ψ.length ≤ BOf p * NOf p ∨ ψ = [] ∨ [] ∈ ψ ∨ NOf p < N₀)
    (hpoly : N₀ ≤ NOf p → ∀ sys : List (List (List ℕ)),
      IsCompiledSparseSystem k (NOf p) (6 * NOf p)
        (initialRowWeightBound (BOf p) ψ.length * 2 ^ k) sys →
      polyCounter (NOf p, sys) =
        commonZeroCount (Finset.univ : Finset (Fin sys.length))
          (fun i : Fin sys.length => equationToFinset (NOf p) sys[i])) :
    sparseCNFDeclaredCounter NOf BOf k N₀ polyCounter (p, ψ) =
      ψ.modelCountOn (Finset.range (NOf p)) := by
  have hvalid : validDeclaredInput k (NOf p) ψ = true :=
    validDeclaredInput_eq_true_iff.mpr ⟨hw, hsub⟩
  unfold sparseCNFDeclaredCounter; simp only [hvalid, ↓reduceIte]
  by_cases he : ψ.isEmpty = true
  · simp only [he, ↓reduceIte]; rw [List.isEmpty_iff.mp he, CNF.modelCountOn_nil, Finset.card_range]
  · simp only [Bool.not_eq_true] at he; simp only [he, Bool.false_eq_true, ↓reduceIte]
    by_cases hnil : hasEmptyClause ψ = true
    · simp only [hnil, ↓reduceIte]
      exact (CNF.modelCountOn_eq_zero_of_nil_mem (hasEmptyClause_eq_true_iff.mp hnil) _).symm
    · simp only [Bool.not_eq_true] at hnil; simp only [hnil, Bool.false_eq_true, ↓reduceIte]
      by_cases hlt : NOf p < N₀
      · simp only [decide_eq_true hlt, ↓reduceIte]
        exact countCNFExhaustive_eq_modelCountOn_range (NOf p) ψ
      · have hge := Nat.le_of_not_lt hlt
        simp only [decide_eq_false hlt, Bool.false_eq_true, ↓reduceIte]
        have hmB : ψ.length ≤ BOf p * NOf p := by
          rcases hdom with hm | rfl | hmem | hlt'
          · exact hm
          · simp at he
          · exact False.elim (Bool.false_ne_true (hnil ▸ hasEmptyClause_eq_true_iff.mpr hmem))
          · exact False.elim (hlt hlt')
        simp only [decide_eq_true hmB, ↓reduceIte]
        obtain ⟨hN1, _⟩ := pos_of_nonempty_nonnil_valid hvalid he hnil
        have hB1 : 1 ≤ BOf p := by
          rcases Nat.eq_zero_or_pos (BOf p) with hB0 | hBp
          · rw [hB0, Nat.zero_mul] at hmB; omega
          · exact hBp
        obtain ⟨_, hinit_rows, hinit_dist⟩ := initialTestsRows_spec hN1 hB1 hmB
        let ψFin := toFinCNF (NOf p) hN1 ψ
        have hcard : Fintype.card (Fin (NOf p)) = NOf p := Fintype.card_fin (NOf p)
        have hlen_fin : ψFin.length = ψ.length := by
          simp only [ψFin, toFinCNF, CNF.relabel, List.length_map]
        have hgreedy := count_greedy_eq_card_sat (compiledRowCounter k polyCounter)
          (NOf p, ψ) ψFin (P := greedyRowListLength (BOf p) ψ.length)
          (by rw [hcard]; exact hN1) (greedyRowListLength_pos hB1)
          (initRows := initialTestsRows ψ.length (BOf p))
          (fun r hr => (hinit_rows r hr).1.trans hlen_fin.symm)
          (fun rows _ hrows_len hrows_wt => by
            have h6 : rows.length ≤ 6 * NOf p := by rw [hcard] at hrows_len; omega
            have hwt : ∀ r ∈ rows, r.count true ≤ initialRowWeightBound (BOf p) ψ.length :=
              fun r hr => (hrows_wt r hr).elim (fun h => (hinit_rows r h).2) fun hP =>
                hP.trans (greedyRowListLength_le_initialRowWeightBound (BOf p) ψ.length)
            have his := isCompiledSparseSystem_compileParitySystemBounded hw hsub h6 hwt
            simp only [compiledRowCounter, decide_eq_true h6, ↓reduceIte]; rw [hpoly hge _ his]
            exact (commonZeroCount_compileParitySystemBounded_eq_numPassing hN1 hw hsub rows).1)
          (fun σ hpass hfalse => by
            have hz_ne : ψFin.violations σ ≠ 0 := fun h0 =>
              Bool.false_ne_true (hfalse.symm.trans ((CNF.violations_eq_zero_iff ψFin σ).mp h0))
            have hdot : ∀ row ∈ initialTestsRows ψ.length (BOf p),
                ofList ψ.length row ⬝ᵥ
                  (fun e : Fin ψ.length => ψFin.violations σ ⟨e.1, by omega⟩) = false :=
              fun row hrow => (Fintype.sum_equiv (finCongr hlen_fin) _ _ fun _ => rfl).symm.trans
                (hpass (ofList ψFin.length row) (List.mem_map_of_mem hrow))
            let eqv : Fin ψ.length ≃ Fin ψFin.length := finCongr hlen_fin.symm
            have hwt_eq : weight (fun e : Fin ψ.length => ψFin.violations σ ⟨e.1, by omega⟩) =
                weight (ψFin.violations σ) :=
              Finset.card_bij (fun i _ => eqv i)
                (fun _ hi => by
                  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢; exact hi)
                (fun _ _ _ _ h => eqv.injective h)
                (fun j hj => ⟨eqv.symm j,
                  by simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢; exact hj,
                  eqv.apply_symm_apply j⟩)
            have hz_ne' : (fun e : Fin ψ.length => ψFin.violations σ ⟨e.1, by omega⟩) ≠ 0 :=
              fun h0 => hz_ne (funext fun e => congrFun h0 ⟨e.1, by omega⟩)
            have hdist := hinit_dist _ hz_ne' hdot
            rw [hwt_eq] at hdist; exact hlen_fin.le.trans hdist)
        rw [hcard, hlen_fin, card_sat_toFinCNF_eq_modelCountOn hN1 hsub] at hgreedy
        unfold sparseCNFFastPath; dsimp only; rw [hgreedy]
        exact Nat.min_eq_right (by
          simpa only [Finset.card_range] using
            modelCountOn_le_two_pow_card ψ (Finset.range (NOf p)))

/-- Instantiation of `sparseCNFDeclaredCounter` with `countSystemExhaustive` computes
`ψ.modelCountOn (Finset.range (NOf p))` unconditionally on every valid sparse formula. -/
theorem sparseCNFDeclaredCounter_exhaustive_eq_modelCountOn {P : Type*} {NOf BOf : P → ℕ}
    {k N₀ : ℕ} {p : P} {ψ : CNF ℕ}
    (hw : ∀ c ∈ ψ, c.length ≤ k) (hsub : ψ.vars.toFinset ⊆ Finset.range (NOf p))
    (hdom : ψ.length ≤ BOf p * NOf p ∨ ψ = [] ∨ [] ∈ ψ ∨ NOf p < N₀) :
    sparseCNFDeclaredCounter NOf BOf k N₀ countSystemExhaustive (p, ψ) =
      ψ.modelCountOn (Finset.range (NOf p)) :=
  sparseCNFDeclaredCounter_eq_modelCountOn hw hsub hdom fun _ _ hsys =>
    countSystemExhaustive_eq_commonZeroCount fun eq heq =>
      ⟨(hsys.2 eq heq).1, fun m hm v hv => ((hsys.2 eq heq).2.2 m hm).2 v hv⟩

/-! ### 3. Normalized Leaf Provider (`sparseCNFLeafCounter`) -/

/-- **Unconditional leaf-accumulator bound**: `sparseCNFLeafCounter` never exceeds `2 ^ ψ.numVars`
on any input `(p, ψ)`, regardless of `polyCounter`. -/
theorem sparseCNFLeafCounter_le_two_pow_numVars {P : Type*} (NOf BOf : P → ℕ) (k N₀ : ℕ)
    (polyCounter : ℕ × List (List (List ℕ)) → ℕ) (x : P × CNF ℕ) :
    sparseCNFLeafCounter NOf BOf k N₀ polyCounter x ≤ 2 ^ x.2.numVars := by
  rcases x with ⟨p, ψ⟩
  by_cases hv : validDeclaredInput k (NOf p) ψ = true
  · exact normalizeDeclaredLeaf_le_two_pow_numVars (validDeclaredInput_eq_true_iff.mp hv).2
      (sparseCNFDeclaredCounter_le_two_pow NOf BOf k N₀ polyCounter (p, ψ))
  · simp only [Bool.not_eq_true] at hv
    simp only [sparseCNFLeafCounter, normalizeDeclaredLeaf, sparseCNFDeclaredCounter, hv,
      Bool.false_eq_true, ↓reduceIte, Nat.zero_shiftRight, Nat.zero_le]

/-- **Exactness of `sparseCNFLeafCounter`**: returns `ψ.modelCount` on every valid width-`≤ k`
sparse leaf `ψ` with variables in `Finset.range (NOf p)`. -/
theorem sparseCNFLeafCounter_eq_modelCount {P : Type*} {NOf BOf : P → ℕ} {k N₀ : ℕ}
    {polyCounter : ℕ × List (List (List ℕ)) → ℕ} {p : P} {ψ : CNF ℕ}
    (hw : ∀ c ∈ ψ, c.length ≤ k) (hsub : ψ.vars.toFinset ⊆ Finset.range (NOf p))
    (hdom : ψ.length ≤ BOf p * NOf p ∨ ψ = [] ∨ [] ∈ ψ ∨ NOf p < N₀)
    (hpoly : N₀ ≤ NOf p → ∀ sys : List (List (List ℕ)),
      IsCompiledSparseSystem k (NOf p) (6 * NOf p)
        (initialRowWeightBound (BOf p) ψ.length * 2 ^ k) sys →
      polyCounter (NOf p, sys) =
        commonZeroCount (Finset.univ : Finset (Fin sys.length))
          (fun i : Fin sys.length => equationToFinset (NOf p) sys[i])) :
    sparseCNFLeafCounter NOf BOf k N₀ polyCounter (p, ψ) = ψ.modelCount :=
  normalizeDeclaredLeaf_eq_modelCount hsub
    (sparseCNFDeclaredCounter_eq_modelCountOn hw hsub hdom hpoly)

/-- Instantiation of `sparseCNFLeafCounter` with `countSystemExhaustive` computes `ψ.modelCount`. -/
theorem sparseCNFLeafCounter_exhaustive_eq_modelCount {P : Type*} {NOf BOf : P → ℕ} {k N₀ : ℕ}
    {p : P} {ψ : CNF ℕ}
    (hw : ∀ c ∈ ψ, c.length ≤ k) (hsub : ψ.vars.toFinset ⊆ Finset.range (NOf p))
    (hdom : ψ.length ≤ BOf p * NOf p ∨ ψ = [] ∨ [] ∈ ψ ∨ NOf p < N₀) :
    sparseCNFLeafCounter NOf BOf k N₀ countSystemExhaustive (p, ψ) = ψ.modelCount :=
  normalizeDeclaredLeaf_eq_modelCount hsub
    (sparseCNFDeclaredCounter_exhaustive_eq_modelCountOn hw hsub hdom)

end Cslib.Complexity.SparseCNFLeafCounter

end

/-! ### 4. Native Machine Certificates and Split Time / Polynomial-Space Bounds -/

public section

namespace Cslib.Complexity.SparseCNFLeafCounter

open Finset Cslib.BitString Cslib.GenericRAM Cslib.GenericRAM.ExhaustiveCountFallback
open Cslib.Logic.PL Cslib.Logic.PL.CNF Cslib.Logic.PL.CNF.GreedyContext
open Cslib.Complexity.InitialTestsSearch Turing.MultiTapeTM

local notation "encSys" => encList (encList (encList encNat))
local notation "PolySys" => ℕ × List (List (List ℕ))

private abbrev encCandCtx := encPair encUnary encCNF
private abbrev encCandIn := encPair encCandCtx (encList encBits)

variable {P : Type} {encP : P ↪ List Bool} {NOf BOf : P → ℕ} {polyCounter : PolySys → ℕ}

/-- Split Section 6.3 runtime upper bound: `poly L` outside `entersSparseFastPath`, and initial
Tanner search plus `(3 * N + 1) * ((2 * m) ^ P + 1)` candidate system evaluations inside. -/
def sparseCNFTimeBound (encP : P ↪ List Bool) (NOf BOf : P → ℕ) (k N₀ : ℕ)
    (poly qInit : ℕ → ℕ) (R : P × CNF ℕ → ℕ) (x : P × CNF ℕ) : ℕ :=
  let L := (encPair encP encCNF x).length; let N := NOf x.1; let B := BOf x.1; let m := x.2.length
  if entersSparseFastPath k N₀ N B x.2 then
    poly L + 2 ^ qInit (B + Nat.log 2 (m + 2)) +
      (3 * N + 1) * (candidateTupleCount m (greedyRowListLength B m) + 1) * (poly L + R x)
  else poly L

/-- Hypothesis bounding `cPoly.time (NOf x.1, sys) ≤ R x` on every compiled sparse system of at
most `6 * NOf x.1` equations and polynomial encoded length produced on the Section 6.3 fast path. -/
def ValidPolyTimeBound (encP : P ↪ List Bool) (NOf BOf : P → ℕ) (k N₀ : ℕ)
    {polyCounter : PolySys → ℕ}
    (cPoly : NativeCertificate polyCounter (encPair encUnary encSys) encNat)
    (polySys : ℕ → ℕ) (R : P × CNF ℕ → ℕ) : Prop :=
  ∀ x : P × CNF ℕ, entersSparseFastPath k N₀ (NOf x.1) (BOf x.1) x.2 = true →
    ∀ sys : List (List (List ℕ)),
      IsCompiledSparseSystem k (NOf x.1) (6 * NOf x.1)
        (initialRowWeightBound (BOf x.1) x.2.length * 2 ^ k) sys →
      (encPair encUnary encSys (NOf x.1, sys)).length ≤ polySys (encPair encP encCNF x).length →
      cPoly.time (NOf x.1, sys) ≤ R x

private theorem polyBounded_output_of_space {α β : Type} {ei : α ↪ List Bool} {eo : β ↪ List Bool}
    {f : α → β} (c : NativeCertificate f ei eo)
    (hs : PolyBounded (fun a => (ei a).length) c.space) :
    PolyBounded (fun a => (ei a).length) (fun a => (eo (f a)).length) :=
  let ⟨k, _, hl⟩ := c.computes; ((PolyBounded.const k).mul (hs.add (.const 1))).mono hl

private theorem polyBounded_comp_space {α β γ : Type} {ei : α ↪ List Bool} {em : β ↪ List Bool}
    {eo : γ ↪ List Bool} {f : α → β} {g : β → γ} (d : NativeCertificate g em eo)
    (c : NativeCertificate f ei em) (hd : PolyBounded (fun b => (em b).length) d.space)
    (hc : PolyBounded (fun a => (ei a).length) c.space) :
    PolyBounded (fun a => (ei a).length) (d.comp c).space :=
  hc.add (hd.comp (polyBounded_output_of_space c hc))

private theorem polyBounded_prod_space {α β γ : Type} {ei : α ↪ List Bool} {em : β ↪ List Bool}
    {eo : γ ↪ List Bool} {f : α → β} {g : α → γ} (c : NativeCertificate f ei em)
    (d : NativeCertificate g ei eo) (hc : PolyBounded (fun a => (ei a).length) c.space)
    (hd : PolyBounded (fun a => (ei a).length) d.space) :
    PolyBounded (fun a => (ei a).length) (c.prod d).space := hc.add hd

private theorem polyBounded_pair_len {α β : Type} {ei : α ↪ List Bool} {eo : β ↪ List Bool}
    {f : α → β} (hf : PolyBounded (fun a => (ei a).length) (fun a => (eo (f a)).length)) :
    PolyBounded (fun a => (ei a).length) (fun a => (encPair ei eo (a, f a)).length) :=
  ((((PolyBounded.const 2).mul PolyBounded.self).add hf).add (.const 2)).mono fun a => by
    simp only [length_encPair]; omega

private abbrev toSysInput (k : ℕ) (q : (ℕ × CNF ℕ) × List (List Bool)) : PolySys :=
  (q.1.1, compileParitySystemBounded k q.1.2 q.2)

private theorem computableInPolyTime_toSysInput (k : ℕ) :
    ComputableInPolyTime (toSysInput k) encCandIn (encPair encUnary encSys) := by
  unfold toSysInput encCandIn encCandCtx; fun_prop

private theorem computableInPolyTime_rowLenGuard :
    ComputableInPolyTime (fun q : (ℕ × CNF ℕ) × List (List Bool) => decide (q.2.length ≤ 6 * q.1.1))
      encCandIn encBool := by
  unfold encCandIn encCandCtx; fun_prop

private noncomputable def compiledRowCertificate (k : ℕ)
    (cPoly : NativeCertificate polyCounter (encPair encUnary encSys) encNat) :
    NativeCertificate (compiledRowCounter k polyCounter) encCandIn encNat :=
  guardedTargetOfPolyTime computableInPolyTime_rowLenGuard
    (cPoly.comp (NativeCertificate.ofPolyTime (computableInPolyTime_toSysInput k)))
    (NativeCertificate.const 0)
    (fun _ h => by simp only [Function.comp_apply, toSysInput, compiledRowCounter, h, ↓reduceIte])
    (fun _ h => by simp only [compiledRowCounter, h, Bool.false_eq_true, ↓reduceIte])

private theorem polyBounded_compiledRowCertificate_space (k : ℕ)
    (cPoly : NativeCertificate polyCounter (encPair encUnary encSys) encNat)
    (hSpace : PolyBounded (fun y => (encPair encUnary encSys y).length) cPoly.space) :
    PolyBounded (fun q => (encCandIn q).length) (compiledRowCertificate k cPoly).space :=
  polyBounded_branch_space _ _ _
    (NativeCertificate.ofPolyTime_isPolynomial computableInPolyTime_rowLenGuard).2
    (polyBounded_comp_space cPoly (NativeCertificate.ofPolyTime (computableInPolyTime_toSysInput k))
      hSpace (NativeCertificate.ofPolyTime_isPolynomial (computableInPolyTime_toSysInput k)).2)
    PolyBounded.self

private noncomputable def greedyCellTime (k : ℕ)
    (cPoly : NativeCertificate polyCounter (encPair encUnary encSys) encNat)
    (a : (ℕ × CNF ℕ) × ℕ × ℕ × ℕ × List (List Bool)) (i j : ℕ) : ℕ :=
  (compiledRowCertificate k cPoly).time (a.1,
    greedyParityRowsAt (fun r => compiledRowCounter k polyCounter (a.1, r))
      a.2.2.1 a.2.2.2.1 a.2.2.2.2 i ++
      [materializeTestRow a.2.2.1 (decodeTestTuple a.2.2.1 a.2.2.2.1 j)])

private noncomputable def greedyMaxCellTime (k : ℕ)
    (cPoly : NativeCertificate polyCounter (encPair encUnary encSys) encNat)
    (a : (ℕ × CNF ℕ) × ℕ × ℕ × ℕ × List (List Bool)) : ℕ :=
  listMax (fun i => listMax (greedyCellTime k cPoly a i)
    (List.range (candidateTupleCount a.2.2.1 a.2.2.2.1 + 1))) (List.range (3 * a.2.1 + 1))

private theorem le_greedyMaxCellTime (k : ℕ)
    (cPoly : NativeCertificate polyCounter (encPair encUnary encSys) encNat)
    (a : (ℕ × CNF ℕ) × ℕ × ℕ × ℕ × List (List Bool)) {i j : ℕ}
    (hi : i ≤ 3 * a.2.1) (hj : j ≤ candidateTupleCount a.2.2.1 a.2.2.2.1) :
    greedyCellTime k cPoly a i j ≤ greedyMaxCellTime k cPoly a :=
  (le_listMax (f := greedyCellTime k cPoly a i) (List.mem_range.mpr (by omega))).trans
    (le_listMax (f := fun i' => listMax (greedyCellTime k cPoly a i')
      (List.range (candidateTupleCount a.2.2.1 a.2.2.2.1 + 1))) (List.mem_range.mpr (by omega)))

open Classical in
private noncomputable def greedyBoundedCertificate (k : ℕ)
    (cPoly : NativeCertificate polyCounter (encPair encUnary encSys) encNat) :
    NativeCertificate
      (fun a : (ℕ × CNF ℕ) × ℕ × ℕ × ℕ × List (List Bool) =>
        greedyParityRows (fun r => compiledRowCounter k polyCounter (a.1, r))
          a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2)
      (encGreedyInput encCandCtx) (encList encBits) :=
  let cCand := compiledRowCertificate k cPoly
  if h : PolyBounded (fun y => (encPair encUnary encSys y).length) cPoly.space then
    let hG := computableInO_greedy cCand (polyBounded_compiledRowCertificate_space k cPoly h)
      (greedyMaxCellTime k cPoly) (fun a _ hi _ hj => le_greedyMaxCellTime k cPoly a hi hj)
    ⟨fun a => (3 * a.2.1 + 1) * (candidateTupleCount a.2.2.1 a.2.2.2.1 + 1) *
        (hG.choose (encGreedyInput encCandCtx a).length + greedyMaxCellTime k cPoly a),
      fun a => hG.choose (encGreedyInput encCandCtx a).length, hG.choose_spec.2⟩
  else greedyCertificate cCand

private theorem polyBounded_greedyBoundedCertificate_space (k : ℕ)
    (cPoly : NativeCertificate polyCounter (encPair encUnary encSys) encNat)
    (hSpace : PolyBounded (fun y => (encPair encUnary encSys y).length) cPoly.space) :
    PolyBounded (fun a => (encGreedyInput encCandCtx a).length)
      (greedyBoundedCertificate k cPoly).space := by
  let hG := computableInO_greedy (compiledRowCertificate k cPoly)
    (polyBounded_compiledRowCertificate_space k cPoly hSpace) (greedyMaxCellTime k cPoly)
    (fun a _ hi _ hj => le_greedyMaxCellTime k cPoly a hi hj)
  have heq : (greedyBoundedCertificate k cPoly).space =
      fun a => hG.choose (encGreedyInput encCandCtx a).length := by
    unfold greedyBoundedCertificate; simp only [hSpace, ↓reduceDIte]
  rw [heq]; exact PolyBounded.of_polynomiallyBounded _ hG.choose_spec.1

private theorem computableInPolyTime_validDeclaredInput (k : ℕ)
    (hNOf : ComputableInPolyTime NOf encP encUnary) :
    ComputableInPolyTime (fun x : P × CNF ℕ => validDeclaredInput k (NOf x.1) x.2)
      (encPair encP encCNF) encBool := by
  have hN_nat := (show ComputableInPolyTime id encUnary encNat by fun_prop).comp
    (hNOf.comp (ComputableInPolyTime.fst encP encCNF))
  have h1 : ComputableInPolyTime (fun x : P × CNF ℕ => x.2.all fun c => decide (c.length ≤ k))
      (encPair encP encCNF) encBool := by
    apply ComputableInPolyTime.allWithInput (by fun_prop)
    have := SAT.computableInPolyTime_clause_length (by fun_prop : ComputableInPolyTime Prod.snd
      (encPair (encPair encP encCNF) (encList (encPair encNat encBool))) _)
    fun_prop
  have h2 : ComputableInPolyTime
      (fun x : P × CNF ℕ => x.2.vars.all fun v => decide (v < NOf x.1))
      (encPair encP encCNF) encBool := by
    apply ComputableInPolyTime.allWithInput
      (SAT.computableInPolyTime_vars.comp (ComputableInPolyTime.snd encP encCNF))
    exact ComputableInPolyTime.binary_lt'
      (ComputableInPolyTime.snd (encPair encP encCNF) encNat)
      (hN_nat.comp (ComputableInPolyTime.fst (encPair encP encCNF) encNat))
  unfold validDeclaredInput; exact ComputableInPolyTime.bool_and' h1 h2

private theorem computableInPolyTime_isEmptyCNF :
    ComputableInPolyTime (fun x : P × CNF ℕ => x.2.isEmpty) (encPair encP encCNF) encBool :=
  (ComputableInPolyTime.decide_eq' (ComputableInPolyTime.snd encP encCNF)
    (.const [])).of_enc_eq fun x => congrArg encBool (by cases x.2 <;> rfl)

private theorem computableInPolyTime_hasEmptyClause :
    ComputableInPolyTime (fun x : P × CNF ℕ => hasEmptyClause x.2)
      (encPair encP encCNF) encBool := by
  unfold hasEmptyClause
  apply ComputableInPolyTime.anyWithInput (ComputableInPolyTime.snd encP encCNF)
  exact (ComputableInPolyTime.decide_eq' (ComputableInPolyTime.snd (encPair encP encCNF) _)
    (.const [])).of_enc_eq fun p => congrArg encBool (by cases p.2 <;> rfl)

private theorem computableInPolyTime_twoPowN (hNOf : ComputableInPolyTime NOf encP encUnary) :
    ComputableInPolyTime (fun x : P × CNF ℕ => 2 ^ NOf x.1) (encPair encP encCNF) encNat :=
  ComputableInPolyTime.binary_two_pow.comp (hNOf.comp (by fun_prop))

private theorem computableInPolyTime_baseGuard (k : ℕ)
    (hNOf : ComputableInPolyTime NOf encP encUnary) :
    ComputableInPolyTime (fun x : P × CNF ℕ =>
      validDeclaredInput k (NOf x.1) x.2 && !x.2.isEmpty && !hasEmptyClause x.2)
      (encPair encP encCNF) encBool :=
  ((computableInPolyTime_validDeclaredInput k hNOf).bool_and'
    (ComputableInPolyTime.bool_not.comp (computableInPolyTime_isEmptyCNF (encP := encP)))).bool_and'
    (ComputableInPolyTime.bool_not.comp (computableInPolyTime_hasEmptyClause (encP := encP)))

private theorem computableInPolyTime_entersSparseFastPath (k N₀ : ℕ)
    (hNOf : ComputableInPolyTime NOf encP encUnary)
    (hBOf : ComputableInPolyTime BOf encP encUnary) :
    ComputableInPolyTime
      (fun x : P × CNF ℕ => entersSparseFastPath k N₀ (NOf x.1) (BOf x.1) x.2)
      (encPair encP encCNF) encBool := by
  have hbase := computableInPolyTime_baseGuard k hNOf
  have hN := hNOf.comp (ComputableInPolyTime.fst encP encCNF)
  have hB := hBOf.comp (ComputableInPolyTime.fst encP encCNF)
  have hm := SAT.computableInPolyTime_length (ComputableInPolyTime.snd encP encCNF)
  have hlt : ComputableInPolyTime (fun x : P × CNF ℕ => decide (NOf x.1 < N₀))
      (encPair encP encCNF) encBool := by fun_prop
  have hle : ComputableInPolyTime (fun x : P × CNF ℕ => decide (x.2.length ≤ BOf x.1 * NOf x.1))
      (encPair encP encCNF) encBool := by fun_prop
  unfold entersSparseFastPath
  exact (hbase.bool_and' (ComputableInPolyTime.bool_not.comp hlt)).bool_and' hle

private def nonExhGuard {P : Type*} (NOf : P → ℕ) (k N₀ : ℕ) (x : P × CNF ℕ) : Bool :=
  !(validDeclaredInput k (NOf x.1) x.2 && !x.2.isEmpty && !hasEmptyClause x.2 &&
    decide (NOf x.1 < N₀))

private def nonExhDirect {P : Type*} (NOf : P → ℕ) (k : ℕ) (x : P × CNF ℕ) : ℕ :=
  if validDeclaredInput k (NOf x.1) x.2 && x.2.isEmpty then 2 ^ NOf x.1 else 0

private def sparseCNFNonFastFallback {P : Type*} (NOf : P → ℕ) (k N₀ : ℕ) (x : P × CNF ℕ) : ℕ :=
  if nonExhGuard NOf k N₀ x then nonExhDirect NOf k x else countCNFExhaustive (NOf x.1, x.2)

private theorem computableInPolyTime_nonExhGuard (k N₀ : ℕ)
    (hNOf : ComputableInPolyTime NOf encP encUnary) :
    ComputableInPolyTime (nonExhGuard NOf k N₀) (encPair encP encCNF) encBool := by
  have hbase := computableInPolyTime_baseGuard k hNOf
  have hN := hNOf.comp (ComputableInPolyTime.fst encP encCNF)
  have hlt : ComputableInPolyTime (fun x : P × CNF ℕ => decide (NOf x.1 < N₀))
      (encPair encP encCNF) encBool := by fun_prop
  unfold nonExhGuard
  exact ComputableInPolyTime.bool_not.comp (hbase.bool_and' hlt)

private theorem computableInPolyTime_nonExhDirect (k : ℕ)
    (hNOf : ComputableInPolyTime NOf encP encUnary) :
    ComputableInPolyTime (nonExhDirect NOf k) (encPair encP encCNF) encNat :=
  ((computableInPolyTime_validDeclaredInput k hNOf).bool_and'
    (computableInPolyTime_isEmptyCNF (encP := encP))).ite'
    (computableInPolyTime_twoPowN hNOf) (.const 0)

private theorem computableInPolyTime_exhInput (hNOf : ComputableInPolyTime NOf encP encUnary) :
    ComputableInPolyTime (fun x : P × CNF ℕ => (NOf x.1, x.2))
      (encPair encP encCNF) (encPair encUnary encCNF) :=
  (hNOf.comp (by fun_prop)).prod (by fun_prop)

private noncomputable def nonFastFallbackCertificate (k N₀ : ℕ)
    (hNOf : ComputableInPolyTime NOf encP encUnary) :
    NativeCertificate (sparseCNFNonFastFallback NOf k N₀) (encPair encP encCNF) encNat :=
  NativeCertificate.branch
    (NativeCertificate.ofPolyTime (computableInPolyTime_nonExhGuard k N₀ hNOf))
    (NativeCertificate.ofPolyTime (computableInPolyTime_nonExhDirect k hNOf))
    (countCNFExhaustiveCertificate.comp
      (NativeCertificate.ofPolyTime (computableInPolyTime_exhInput hNOf)))

private theorem isPolynomial_nonFastFallbackCertificate (k N₀ : ℕ)
    (hNOf : ComputableInPolyTime NOf encP encUnary) :
    (nonFastFallbackCertificate k N₀ hNOf).IsPolynomial := by
  have hDir := NativeCertificate.ofPolyTime_isPolynomial (computableInPolyTime_nonExhDirect k hNOf)
  have hExhIn := NativeCertificate.ofPolyTime_isPolynomial (computableInPolyTime_exhInput hNOf)
  have hExhLen := (computableInPolyTime_exhInput hNOf).polyBounded_length
  have hExhSpace := polyBounded_comp_space countCNFExhaustiveCertificate
    (NativeCertificate.ofPolyTime (computableInPolyTime_exhInput hNOf))
    polyBounded_countCNFExhaustive_space hExhIn.2
  obtain ⟨P_ex, Q_ex, hP_ex, hQ_ex, hExhT⟩ := exists_countCNFExhaustive_time_le
  obtain ⟨hSpace, C, d, hTime⟩ := exists_branch_time_le_of_finite_threshold
    (μ := fun x : P × CNF ℕ => NOf x.1) (N₀ := N₀) (P_ex := fun x => P_ex (NOf x.1, x.2))
    (Q_ex := fun x => (NativeCertificate.ofPolyTime (computableInPolyTime_exhInput hNOf)).time x +
      Q_ex (NOf x.1, x.2))
    (NativeCertificate.ofPolyTime (computableInPolyTime_nonExhGuard k N₀ hNOf))
    (NativeCertificate.ofPolyTime (computableInPolyTime_nonExhDirect k hNOf))
    (countCNFExhaustiveCertificate.comp
      (NativeCertificate.ofPolyTime (computableInPolyTime_exhInput hNOf)))
    (NativeCertificate.ofPolyTime_isPolynomial (computableInPolyTime_nonExhGuard k N₀ hNOf))
    hDir.2 hExhSpace
    (fun _ h => by
      simp only [nonExhGuard, Bool.not_eq_false', Bool.and_eq_true, decide_eq_true_eq] at h
      exact h.2)
    (hP_ex.comp hExhLen) (hExhIn.1.add (hQ_ex.comp hExhLen))
    (fun x _ => by
      have ht := hExhT (NOf x.1, x.2)
      simp only [NativeCertificate.comp_time]; dsimp only at ht ⊢; omega)
  refine ⟨(hDir.1.add (PolyBounded.of_forall_le C d fun _ => le_rfl)).mono fun x => ?_, hSpace⟩
  have hx := hTime x; dsimp only [nonFastFallbackCertificate] at hx ⊢; split_ifs at hx <;> omega

private theorem computableInPolyTime_mbPair (hBOf : ComputableInPolyTime BOf encP encUnary) :
    ComputableInPolyTime (fun x : P × CNF ℕ => (x.2.length, BOf x.1))
      (encPair encP encCNF) (encPair encUnary encUnary) :=
  (SAT.computableInPolyTime_length (by fun_prop)).prod (hBOf.comp (by fun_prop))

private def assembleGreedyInput (NOf BOf : P → ℕ) (y : (P × CNF ℕ) × List (List Bool)) :
    (ℕ × CNF ℕ) × ℕ × ℕ × ℕ × List (List Bool) :=
  ((NOf y.1.1, y.1.2), NOf y.1.1, y.1.2.length, greedyRowListLength (BOf y.1.1) y.1.2.length, y.2)

private theorem computableInPolyTime_assembleGreedyInput
    (hNOf : ComputableInPolyTime NOf encP encUnary)
    (hBOf : ComputableInPolyTime BOf encP encUnary) :
    ComputableInPolyTime (assembleGreedyInput NOf BOf)
      (encPair (encPair encP encCNF) (encList encBits)) (encGreedyInput encCandCtx) := by
  have hp : ComputableInPolyTime (fun y : (P × CNF ℕ) × List (List Bool) => y.1.1)
      (encPair (encPair encP encCNF) (encList encBits)) encP := by fun_prop
  have hψ : ComputableInPolyTime (fun y : (P × CNF ℕ) × List (List Bool) => y.1.2)
      (encPair (encPair encP encCNF) (encList encBits)) encCNF := by fun_prop
  have hN := hNOf.comp hp; have hm := SAT.computableInPolyTime_length hψ
  unfold assembleGreedyInput encGreedyInput encGreedyIn encCandCtx
  exact (hN.prod hψ).prod (hN.prod (hm.prod
    ((greedyRowListLength_polyTime hm (hBOf.comp hp)).prod (by fun_prop))))

private def assembleFinalCand (NOf : P → ℕ) (y : (P × CNF ℕ) × List (List Bool)) :
    (ℕ × CNF ℕ) × List (List Bool) := ((NOf y.1.1, y.1.2), y.2)

private theorem computableInPolyTime_assembleFinalCand
    (hNOf : ComputableInPolyTime NOf encP encUnary) :
    ComputableInPolyTime (assembleFinalCand NOf)
      (encPair (encPair encP encCNF) (encList encBits)) encCandIn := by
  unfold assembleFinalCand encCandIn encCandCtx
  exact ((hNOf.comp (by fun_prop)).prod (by fun_prop)).prod (by fun_prop)

private def capByTwoPow (NOf : P → ℕ) (y : (P × CNF ℕ) × ℕ) : ℕ := min (2 ^ NOf y.1.1) y.2

private theorem computableInPolyTime_capByTwoPow
    (hNOf : ComputableInPolyTime NOf encP encUnary) :
    ComputableInPolyTime (capByTwoPow NOf) (encPair (encPair encP encCNF) encNat) encNat := by
  have h2pow := (computableInPolyTime_twoPowN hNOf).comp
    (ComputableInPolyTime.fst (encPair encP encCNF) encNat)
  have hres := ComputableInPolyTime.snd (encPair encP encCNF) encNat
  have hle := (show ComputableInPolyTime (fun p : ℕ × ℕ => decide (p.1 ≤ p.2))
    (encPair encNat encNat) encBool by fun_prop).comp (h2pow.prod hres)
  refine (hle.ite' h2pow hres).of_enc_eq fun y => congrArg encNat ?_
  by_cases h : 2 ^ NOf y.1.1 ≤ y.2 <;> simp [capByTwoPow, h, Nat.le_of_not_le]

private noncomputable def initRowsCertificate (hBOf : ComputableInPolyTime BOf encP encUnary) :
    NativeCertificate (fun x : P × CNF ℕ => initialTestsRows x.2.length (BOf x.1))
      (encPair encP encCNF) (encList encBits) :=
  let cMB : NativeCertificate (fun p : ℕ × ℕ => initialTestsRows p.1 p.2)
      (encPair encUnary encUnary) (encList encBits) :=
    ⟨fun p => 2 ^ initialTestsRows_computableInO.choose (p.2 + Nat.log 2 (p.1 + 2)),
      fun p => initialTestsRows_computableInO.choose_spec.choose (p.1 + p.2),
      initialTestsRows_computableInO.choose_spec.choose_spec.2.2⟩
  (cMB.comp (NativeCertificate.ofPolyTime (computableInPolyTime_mbPair hBOf))).congr fun _ => rfl

private theorem polyBounded_initRowsCertificate_space
    (hBOf : ComputableInPolyTime BOf encP encUnary) :
    PolyBounded (fun x : P × CNF ℕ => (encPair encP encCNF x).length)
      (initRowsCertificate hBOf).space := by
  have hc := NativeCertificate.ofPolyTime_isPolynomial (computableInPolyTime_mbPair hBOf)
  have hsum : PolyBounded (fun p : ℕ × ℕ => (encPair encUnary encUnary p).length)
      (fun p => p.1 + p.2) := PolyBounded.self.mono fun p => by
    simp only [length_encPair, encUnary_apply, List.length_replicate]; omega
  exact hc.2.add (((PolyBounded.of_polynomiallyBounded id
    initialTestsRows_computableInO.choose_spec.choose_spec.2.1).comp hsum).comp
    (computableInPolyTime_mbPair hBOf).polyBounded_length)

private noncomputable def cIdPair (encP : P ↪ List Bool) :
    NativeCertificate (fun x : P × CNF ℕ => x) (encPair encP encCNF) (encPair encP encCNF) :=
  NativeCertificate.linear (ComputableInO.of_linear (.of_eq fun _ => rfl))

private noncomputable def withInputPost {β γ : Type} {em : β ↪ List Bool} {eo : γ ↪ List Bool}
    {f : P × CNF ℕ → β} {g : (P × CNF ℕ) × β → γ}
    (c : NativeCertificate f (encPair encP encCNF) em)
    (hg : ComputableInPolyTime g (encPair (encPair encP encCNF) em) eo) :
    NativeCertificate (fun x => g (x, f x)) (encPair encP encCNF) eo :=
  ((NativeCertificate.ofPolyTime hg).comp ((cIdPair encP).prod c)).congr fun _ => rfl

private theorem polyBounded_withInputPost_space {β γ : Type} {em : β ↪ List Bool}
    {eo : γ ↪ List Bool} {f : P × CNF ℕ → β} {g : (P × CNF ℕ) × β → γ}
    (c : NativeCertificate f (encPair encP encCNF) em)
    (hg : ComputableInPolyTime g (encPair (encPair encP encCNF) em) eo)
    (hs : PolyBounded (fun x => (encPair encP encCNF x).length) c.space) :
    PolyBounded (fun x => (encPair encP encCNF x).length)
      (withInputPost (encP := encP) c hg).space :=
  polyBounded_comp_space _ _ (NativeCertificate.ofPolyTime_isPolynomial hg).2
    (polyBounded_prod_space _ _ PolyBounded.self hs)

private theorem exists_withInputPost_time {β γ : Type} {em : β ↪ List Bool}
    {eo : γ ↪ List Bool} {f : P × CNF ℕ → β} {g : (P × CNF ℕ) × β → γ}
    (c : NativeCertificate f (encPair encP encCNF) em)
    (hg : ComputableInPolyTime g (encPair (encPair encP encCNF) em) eo)
    (hs : PolyBounded (fun x => (encPair encP encCNF x).length) c.space) :
    ∃ p : ℕ → ℕ, Cslib.PolynomiallyBounded p ∧
      ∀ x, (withInputPost (encP := encP) c hg).time x ≤
        c.time x + p (encPair encP encCNF x).length := by
  have hplen := polyBounded_pair_len (polyBounded_output_of_space c hs)
  obtain ⟨pG, hpG, _, hG⟩ := exists_mono_poly
    ((NativeCertificate.ofPolyTime_isPolynomial hg).1.comp hplen)
  refine ⟨fun L => L + pG L, (by fun_prop : Cslib.PolynomiallyBounded id).add hpG, fun x => ?_⟩
  have hx : (NativeCertificate.ofPolyTime hg).time (x, f x) ≤ pG (encPair encP encCNF x).length :=
    hG x
  change (encPair encP encCNF x).length + c.time x +
    (NativeCertificate.ofPolyTime hg).time (x, f x) ≤
    c.time x + ((encPair encP encCNF x).length + pG (encPair encP encCNF x).length); omega

private noncomputable def fastPathGreedyInCert
    (hNOf : ComputableInPolyTime NOf encP encUnary)
    (hBOf : ComputableInPolyTime BOf encP encUnary) :=
  withInputPost (initRowsCertificate (encP := encP) hBOf)
    (computableInPolyTime_assembleGreedyInput hNOf hBOf)

private noncomputable def fastPathFinalCandCert (k : ℕ)
    (hNOf : ComputableInPolyTime NOf encP encUnary) (hBOf : ComputableInPolyTime BOf encP encUnary)
    (cPoly : NativeCertificate polyCounter (encPair encUnary encSys) encNat) :=
  withInputPost ((greedyBoundedCertificate k cPoly).comp (fastPathGreedyInCert hNOf hBOf))
    (computableInPolyTime_assembleFinalCand hNOf)

private noncomputable def fastPathCertificate (k : ℕ)
    (hNOf : ComputableInPolyTime NOf encP encUnary) (hBOf : ComputableInPolyTime BOf encP encUnary)
    (cPoly : NativeCertificate polyCounter (encPair encUnary encSys) encNat) :
    NativeCertificate (fun x : P × CNF ℕ => sparseCNFFastPath k (NOf x.1) (BOf x.1) polyCounter x.2)
      (encPair encP encCNF) encNat :=
  (withInputPost ((compiledRowCertificate k cPoly).comp (fastPathFinalCandCert k hNOf hBOf cPoly))
    (computableInPolyTime_capByTwoPow hNOf)).congr fun x => by
    dsimp only [Function.comp_apply, capByTwoPow, assembleFinalCand, assembleGreedyInput,
      sparseCNFFastPath]

private theorem polyBounded_fastPathGreedyInCert_space
    (hNOf : ComputableInPolyTime NOf encP encUnary)
    (hBOf : ComputableInPolyTime BOf encP encUnary) :
    PolyBounded (fun x : P × CNF ℕ => (encPair encP encCNF x).length)
      (fastPathGreedyInCert hNOf hBOf).space :=
  polyBounded_withInputPost_space _ _ (polyBounded_initRowsCertificate_space (encP := encP) hBOf)

private theorem polyBounded_fastPathFinalCandCert_space (k : ℕ)
    (hNOf : ComputableInPolyTime NOf encP encUnary) (hBOf : ComputableInPolyTime BOf encP encUnary)
    (cPoly : NativeCertificate polyCounter (encPair encUnary encSys) encNat)
    (hSpace : PolyBounded (fun y => (encPair encUnary encSys y).length) cPoly.space) :
    PolyBounded (fun x : P × CNF ℕ => (encPair encP encCNF x).length)
      (fastPathFinalCandCert k hNOf hBOf cPoly).space :=
  polyBounded_withInputPost_space _ _ (polyBounded_comp_space _ _
    (polyBounded_greedyBoundedCertificate_space k cPoly hSpace)
    (polyBounded_fastPathGreedyInCert_space hNOf hBOf))

private theorem polyBounded_fastPathCertificate_space (k : ℕ)
    (hNOf : ComputableInPolyTime NOf encP encUnary) (hBOf : ComputableInPolyTime BOf encP encUnary)
    (cPoly : NativeCertificate polyCounter (encPair encUnary encSys) encNat)
    (hSpace : PolyBounded (fun y => (encPair encUnary encSys y).length) cPoly.space) :
    PolyBounded (fun x : P × CNF ℕ => (encPair encP encCNF x).length)
      (fastPathCertificate k hNOf hBOf cPoly).space :=
  polyBounded_withInputPost_space _ _ (polyBounded_comp_space _ _
    (polyBounded_compiledRowCertificate_space k cPoly hSpace)
    (polyBounded_fastPathFinalCandCert_space k hNOf hBOf cPoly hSpace))

private theorem fastPath_agrees {k N₀ : ℕ} (x : P × CNF ℕ)
    (h : entersSparseFastPath k N₀ (NOf x.1) (BOf x.1) x.2 = true) :
    sparseCNFFastPath k (NOf x.1) (BOf x.1) polyCounter x.2 =
      sparseCNFDeclaredCounter NOf BOf k N₀ polyCounter x := by
  obtain ⟨hv, he, hnil, hge, hmB⟩ := entersSparseFastPath_eq_true_iff.mp h
  simp only [sparseCNFDeclaredCounter, hv, he, hnil, decide_eq_false (not_lt.mpr hge),
    decide_eq_true hmB, Bool.false_eq_true, ↓reduceIte]

private theorem nonFastFallback_agrees {k N₀ : ℕ} (x : P × CNF ℕ)
    (h : entersSparseFastPath k N₀ (NOf x.1) (BOf x.1) x.2 = false) :
    sparseCNFNonFastFallback NOf k N₀ x = sparseCNFDeclaredCounter NOf BOf k N₀ polyCounter x := by
  unfold entersSparseFastPath sparseCNFNonFastFallback nonExhGuard nonExhDirect
    sparseCNFDeclaredCounter at *
  dsimp only at *
  cases hv : validDeclaredInput k (NOf x.1) x.2 <;> cases he : x.2.isEmpty <;>
    cases hnil : hasEmptyClause x.2 <;> by_cases hlt : NOf x.1 < N₀ <;>
    by_cases hmB : x.2.length ≤ BOf x.1 * NOf x.1 <;>
    simp only [hv, he, hnil, hlt, hmB, decide_true, decide_false, Bool.and_true, Bool.and_false,
      Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte] at h ⊢

/-- **Native resource certificate for `sparseCNFDeclaredCounter`.** -/
noncomputable def sparseCNFDeclaredCertificate (k N₀ : ℕ)
    (hNOf : ComputableInPolyTime NOf encP encUnary) (hBOf : ComputableInPolyTime BOf encP encUnary)
    {polyCounter : PolySys → ℕ}
    (cPoly : NativeCertificate polyCounter (encPair encUnary encSys) encNat) :
    NativeCertificate (sparseCNFDeclaredCounter NOf BOf k N₀ polyCounter)
      (encPair encP encCNF) encNat :=
  guardedTargetOfPolyTime (computableInPolyTime_entersSparseFastPath k N₀ hNOf hBOf)
    (fastPathCertificate k hNOf hBOf cPoly) (nonFastFallbackCertificate k N₀ hNOf)
    fastPath_agrees nonFastFallback_agrees

/-- **Polynomial workspace of `sparseCNFDeclaredCertificate`.** -/
theorem polyBounded_sparseCNFDeclaredCertificate_space (k N₀ : ℕ)
    (hNOf : ComputableInPolyTime NOf encP encUnary) (hBOf : ComputableInPolyTime BOf encP encUnary)
    {polyCounter : PolySys → ℕ}
    (cPoly : NativeCertificate polyCounter (encPair encUnary encSys) encNat)
    (hSpace : PolyBounded (fun y => (encPair encUnary encSys y).length) cPoly.space) :
    PolyBounded (fun x : P × CNF ℕ => (encPair encP encCNF x).length)
      (sparseCNFDeclaredCertificate k N₀ hNOf hBOf cPoly).space := by
  unfold sparseCNFDeclaredCertificate
  exact polyBounded_branch_space _ _ _
    (NativeCertificate.ofPolyTime_isPolynomial
      (computableInPolyTime_entersSparseFastPath k N₀ hNOf hBOf)).2
    (polyBounded_fastPathCertificate_space k hNOf hBOf cPoly hSpace)
    (isPolynomial_nonFastFallbackCertificate k N₀ hNOf).2

private theorem mem_greedyParityRowsAt_or {countSys : List (List Bool) → ℕ}
    {m P : ℕ} {initRows : List (List Bool)} {i : ℕ} {r : List Bool}
    (hr : r ∈ greedyParityRowsAt countSys m P initRows i) :
    r ∈ initRows ∨ (r.length = m ∧ r.count true ≤ P) := by
  induction i with
  | zero => exact Or.inl hr
  | succ i ih =>
    rw [greedyParityRowsAt_succ, List.mem_append, List.mem_singleton] at hr
    exact hr.elim ih fun h => h ▸ Or.inr ⟨length_selectBestTestRow _ _ _ _,
      count_true_selectBestTestRow_le _ _ _ _⟩

private theorem exists_compiledRowCertificate_bounds (k N₀ : ℕ)
    (hNOf : ComputableInPolyTime NOf encP encUnary)
    (cPoly : NativeCertificate polyCounter (encPair encUnary encSys) encNat) :
    ∃ pCandOver polySys : ℕ → ℕ,
      Cslib.PolynomiallyBounded pCandOver ∧ Cslib.PolynomiallyBounded polySys ∧
      ∀ R, ValidPolyTimeBound encP NOf BOf k N₀ cPoly polySys R → ∀ x : P × CNF ℕ,
        entersSparseFastPath k N₀ (NOf x.1) (BOf x.1) x.2 = true →
        ∀ rows : List (List Bool), rows.length ≤ 7 * NOf x.1 →
          (∀ r ∈ rows, r.length = x.2.length ∧
            r.count true ≤ initialRowWeightBound (BOf x.1) x.2.length) →
          (compiledRowCertificate k cPoly).time ((NOf x.1, x.2), rows) ≤
            pCandOver (encPair encP encCNF x).length + R x := by
  obtain ⟨pRowG, hpRowG, hmRowG, hRowG⟩ := exists_mono_poly
    (NativeCertificate.ofPolyTime_isPolynomial computableInPolyTime_rowLenGuard).1
  obtain ⟨pToSys, hpToSys, hmToSys, hToSys⟩ := exists_mono_poly
    (NativeCertificate.ofPolyTime_isPolynomial (computableInPolyTime_toSysInput k)).1
  obtain ⟨pSysLen, hpSysLen, hmSysLen, hSysLen⟩ := exists_mono_poly
    (computableInPolyTime_toSysInput k).polyBounded_length
  obtain ⟨pNLen, hpNLen, _, hNLen⟩ := exists_mono_poly
    ((hNOf.comp (by fun_prop : ComputableInPolyTime Prod.fst (encPair encP encCNF) encP)
      ).polyBounded_length)
  let candInBound (L : ℕ) : ℕ := 2 * (2 * pNLen L + L + 2) + (7 * pNLen L) * (2 * L + 1) + 2
  have hcandInBound_poly : Cslib.PolynomiallyBounded candInBound := by
    dsimp only [candInBound]; fun_prop
  let polySys (L : ℕ) : ℕ := pSysLen (candInBound L)
  let pCandOver (L : ℕ) : ℕ := pRowG (candInBound L) + pToSys (candInBound L) + candInBound L
  refine ⟨pCandOver, polySys,
    ((hpRowG.comp hcandInBound_poly).add (hpToSys.comp hcandInBound_poly)).add hcandInBound_poly,
    hpSysLen.comp hcandInBound_poly, fun R hR x hfast rows hrlen hrprops => ?_⟩
  set L := (encPair encP encCNF x).length
  obtain ⟨hv, _, _, _, _⟩ := entersSparseFastPath_eq_true_iff.mp hfast
  obtain ⟨hw, hsub⟩ := validDeclaredInput_eq_true_iff.mp hv
  have hN_le : NOf x.1 ≤ pNLen L := by
    simpa only [Function.comp_apply, encUnary_apply, List.length_replicate, L] using hNLen x
  have hψ_le : (encCNF x.2).length ≤ L := by simp only [L, length_encPair]; omega
  have hm_le : x.2.length ≤ L :=
    (show x.2.length ≤ (encCNF x.2).length from by
      unfold encCNF
      exact SizedListEncoding.length_le (encList (encPair encNat encBool)) x.2).trans hψ_le
  have hr_enc : (encList encBits rows).length ≤ (7 * pNLen L) * (2 * L + 1) :=
    (length_encList_le encBits rows (b := L) fun r hr => by
      simpa only [encBits_apply, (hrprops r hr).1] using hm_le).trans
      (Nat.mul_le_mul_right (2 * L + 1) (hrlen.trans (Nat.mul_le_mul_left 7 hN_le)))
  have hcin : (encCandIn ((NOf x.1, x.2), rows)).length ≤ candInBound L := by
    simp only [encCandIn, encCandCtx, length_encPair, encUnary_apply, List.length_replicate,
      candInBound]; omega
  have hrg := (hRowG ((NOf x.1, x.2), rows)).trans (hmRowG hcin)
  unfold compiledRowCertificate guardedTargetOfPolyTime; rw [guardedTargetCertificate_time]
  by_cases h6 : rows.length ≤ 6 * NOf x.1
  · simp only [decide_eq_true h6, ↓reduceIte, NativeCertificate.comp_time]
    have hts := (hToSys ((NOf x.1, x.2), rows)).trans (hmToSys hcin)
    have hsys_len := (hSysLen ((NOf x.1, x.2), rows)).trans (hmSysLen hcin)
    have his := isCompiledSparseSystem_compileParitySystemBounded hw hsub h6
      fun r hr => (hrprops r hr).2
    have hpoly_t : cPoly.time (toSysInput k ((NOf x.1, x.2), rows)) ≤ R x :=
      hR x hfast _ his hsys_len
    exact (Nat.add_le_add hrg (Nat.add_le_add hts hpoly_t)).trans (by dsimp only [pCandOver]; omega)
  · simp only [decide_eq_false h6, Bool.false_eq_true, ↓reduceIte, NativeCertificate.const_time]
    dsimp only [pCandOver]; omega

/-- **Explicit certificate-level workspace and split-time bounds for
`sparseCNFDeclaredCertificate`.** -/
theorem exists_sparseCNFDeclaredCertificate_bounds (k N₀ : ℕ)
    (hNOf : ComputableInPolyTime NOf encP encUnary) (hBOf : ComputableInPolyTime BOf encP encUnary)
    {polyCounter : PolySys → ℕ}
    (cPoly : NativeCertificate polyCounter (encPair encUnary encSys) encNat)
    (hSpace : PolyBounded (fun y => (encPair encUnary encSys y).length) cPoly.space) :
    ∃ poly qInit polySys : ℕ → ℕ,
      Cslib.PolynomiallyBounded poly ∧ Cslib.PolynomiallyBounded qInit ∧
      Cslib.PolynomiallyBounded polySys ∧
      (∀ x, (sparseCNFDeclaredCertificate k N₀ hNOf hBOf cPoly).space x ≤
        poly (encPair encP encCNF x).length) ∧
      ∀ R, ValidPolyTimeBound encP NOf BOf k N₀ cPoly polySys R → ∀ x,
        (sparseCNFDeclaredCertificate k N₀ hNOf hBOf cPoly).time x ≤
          2 * (sparseCNFTimeBound encP NOf BOf k N₀ poly qInit R x + 1) := by
  obtain ⟨pCandOver, polySys, hpCandOver, hpolySys, hCandT⟩ :=
    exists_compiledRowCertificate_bounds (BOf := BOf) k N₀ hNOf cPoly
  obtain ⟨pSp, hpSp, _, hSp⟩ := exists_mono_poly
    (polyBounded_sparseCNFDeclaredCertificate_space k N₀ hNOf hBOf cPoly hSpace)
  obtain ⟨pGuard, hpGuard, _, hGuard⟩ := exists_mono_poly (NativeCertificate.ofPolyTime_isPolynomial
    (computableInPolyTime_entersSparseFastPath k N₀ hNOf hBOf)).1
  obtain ⟨pFall, hpFall, _, hFall⟩ := exists_mono_poly
    (isPolynomial_nonFastFallbackCertificate k N₀ hNOf).1
  obtain ⟨pMB, hpMB, _, hMB⟩ := exists_mono_poly
    (NativeCertificate.ofPolyTime_isPolynomial (computableInPolyTime_mbPair hBOf)).1
  let qInit := initialTestsRows_computableInO.choose
  have hqInit := initialTestsRows_computableInO.choose_spec.choose_spec.1
  obtain ⟨pAsmG, hpAsmG, hAsmG⟩ := exists_withInputPost_time
    (initRowsCertificate (encP := encP) hBOf) (computableInPolyTime_assembleGreedyInput hNOf hBOf)
    (polyBounded_initRowsCertificate_space (encP := encP) hBOf)
  have hGreedyInSpace := polyBounded_fastPathGreedyInCert_space hNOf hBOf
  have hGreedyInLen := polyBounded_output_of_space (fastPathGreedyInCert hNOf hBOf) hGreedyInSpace
  have hCandSpace := polyBounded_compiledRowCertificate_space k cPoly hSpace
  let hG := computableInO_greedy (compiledRowCertificate k cPoly) hCandSpace
    (greedyMaxCellTime k cPoly) (fun a _ hi _ hj => le_greedyMaxCellTime k cPoly a hi hj)
  obtain ⟨pGC, hpGC, _, hGC⟩ := exists_mono_poly
    ((PolyBounded.of_polynomiallyBounded id hG.choose_spec.1).comp hGreedyInLen)
  obtain ⟨pAsmF, hpAsmF, hAsmF⟩ := exists_withInputPost_time
    ((greedyBoundedCertificate k cPoly).comp (fastPathGreedyInCert hNOf hBOf))
    (computableInPolyTime_assembleFinalCand hNOf)
    (polyBounded_comp_space _ _ (polyBounded_greedyBoundedCertificate_space k cPoly hSpace)
      hGreedyInSpace)
  obtain ⟨pCap, hpCap, hCap⟩ := exists_withInputPost_time
    ((compiledRowCertificate k cPoly).comp (fastPathFinalCandCert k hNOf hBOf cPoly))
    (computableInPolyTime_capByTwoPow hNOf)
    (polyBounded_comp_space _ _ hCandSpace
      (polyBounded_fastPathFinalCandCert_space k hNOf hBOf cPoly hSpace))
  let poly (L : ℕ) : ℕ :=
    pSp L + pGuard L + pFall L + pMB L + pAsmG L + pGC L + pAsmF L + pCap L + pCandOver L
  have hpoly : Cslib.PolynomiallyBounded poly :=
    (((((((hpSp.add hpGuard).add hpFall).add hpMB).add hpAsmG).add hpGC).add hpAsmF).add
      hpCap).add hpCandOver
  refine ⟨poly, qInit, polySys, hpoly, hqInit, hpolySys,
    fun x => (hSp x).trans (by dsimp only [poly]; omega), fun R hR x => ?_⟩
  have hg := hGuard x
  unfold sparseCNFDeclaredCertificate guardedTargetOfPolyTime sparseCNFTimeBound
  rw [guardedTargetCertificate_time]
  cases hfast : entersSparseFastPath k N₀ (NOf x.1) (BOf x.1) x.2
  · simp only [hfast, Bool.false_eq_true, ↓reduceIte]
    exact (Nat.add_le_add hg (hFall x)).trans (by dsimp only [poly]; omega)
  · simp only [hfast, ↓reduceIte]
    obtain ⟨hv, he, hnil, _, hmB⟩ := entersSparseFastPath_eq_true_iff.mp hfast
    obtain ⟨hN1, _⟩ := pos_of_nonempty_nonnil_valid hv he hnil
    have hB1 : 1 ≤ BOf x.1 := by
      rcases Nat.eq_zero_or_pos (BOf x.1) with hB0 | hBp
      · rw [hB0, Nat.zero_mul] at hmB; omega
      · exact hBp
    obtain ⟨hinit_len, hinit_rows, _⟩ := initialTestsRows_spec hN1 hB1 hmB
    let gIn := assembleGreedyInput NOf BOf (x, initialTestsRows x.2.length (BOf x.1))
    let finalRows := greedyParityRows
      (fun r => compiledRowCounter k polyCounter ((NOf x.1, x.2), r))
      (NOf x.1) x.2.length (greedyRowListLength (BOf x.1) x.2.length)
      (initialTestsRows x.2.length (BOf x.1))
    have hmax_cell : greedyMaxCellTime k cPoly gIn ≤
        pCandOver (encPair encP encCNF x).length + R x := by
      refine listMax_le fun i hi => listMax_le fun _ _ => ?_
      have hi' : i ≤ 3 * NOf x.1 := by
        have := List.mem_range.mp hi; dsimp only [gIn, assembleGreedyInput] at this; omega
      dsimp only [greedyCellTime, gIn, assembleGreedyInput]
      refine hCandT R hR x hfast _ (by
        rw [List.length_append, List.length_singleton, length_greedyParityRowsAt]
        exact (Nat.add_le_add (Nat.add_le_add hinit_len hi') (le_refl 1)).trans (by omega)) ?_
      intro r hr; rcases List.mem_append.mp hr with hprev | hcand
      · exact (mem_greedyParityRowsAt_or hprev).elim (fun h0 => hinit_rows r h0) fun ⟨hrl, hrw⟩ =>
          ⟨hrl, hrw.trans (greedyRowListLength_le_initialRowWeightBound (BOf x.1) x.2.length)⟩
      · rw [List.mem_singleton.mp hcand]
        exact ⟨length_materializeTestRow _ _,
          (count_true_materializeTestRow_decodeTestTuple_le _ _ _).trans
            (greedyRowListLength_le_initialRowWeightBound (BOf x.1) x.2.length)⟩
    have hfinal_cand_t : (compiledRowCertificate k cPoly).time ((NOf x.1, x.2), finalRows) ≤
        pCandOver (encPair encP encCNF x).length + R x :=
      hCandT R hR x hfast finalRows
        (by
          dsimp only [finalRows]; rw [length_greedyParityRows]
          exact (Nat.add_le_add_right hinit_len _).trans (by omega))
        fun r hr => (mem_greedyParityRowsAt_or hr).elim (fun h0 => hinit_rows r h0)
          fun ⟨hrl, hrw⟩ =>
            ⟨hrl, hrw.trans (greedyRowListLength_le_initialRowWeightBound (BOf x.1) x.2.length)⟩
    let K := (3 * NOf x.1 + 1) *
      (candidateTupleCount x.2.length (greedyRowListLength (BOf x.1) x.2.length) + 1)
    have hgreedy_t : (greedyBoundedCertificate k cPoly).time gIn ≤
        K * (poly (encPair encP encCNF x).length + R x) := by
      have heq : (greedyBoundedCertificate k cPoly).time gIn =
          K * (hG.choose (encGreedyInput encCandCtx gIn).length +
            greedyMaxCellTime k cPoly gIn) := by
        unfold greedyBoundedCertificate; simp only [hSpace, ↓reduceDIte]; rfl
      rw [heq]; refine Nat.mul_le_mul_left K ((Nat.add_le_add (hGC x) hmax_cell).trans ?_)
      dsimp only [poly]; omega
    have hfinal_absorb : (compiledRowCertificate k cPoly).time ((NOf x.1, x.2), finalRows) ≤
        K * (poly (encPair encP encCNF x).length + R x) :=
      (hfinal_cand_t.trans (by dsimp only [poly]; omega)).trans
        (Nat.le_mul_of_pos_left _ (Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _)))
    have ht1 : (initRowsCertificate (encP := encP) hBOf).time x ≤
        pMB (encPair encP encCNF x).length +
          2 ^ qInit (BOf x.1 + Nat.log 2 (x.2.length + 2)) := Nat.add_le_add_right (hMB x) _
    have ht2 := (hAsmG x).trans (Nat.add_le_add_right ht1 _)
    have ht3 : ((greedyBoundedCertificate k cPoly).comp (fastPathGreedyInCert hNOf hBOf)).time x ≤
        (pMB (encPair encP encCNF x).length + 2 ^ qInit (BOf x.1 + Nat.log 2 (x.2.length + 2)) +
          pAsmG (encPair encP encCNF x).length) +
        K * (poly (encPair encP encCNF x).length + R x) := by
      rw [NativeCertificate.comp_time]; exact Nat.add_le_add ht2 hgreedy_t
    have ht4 := (hAsmF x).trans (Nat.add_le_add_right ht3 _)
    have ht5 : ((compiledRowCertificate k cPoly).comp
        (fastPathFinalCandCert k hNOf hBOf cPoly)).time x ≤
        ((pMB (encPair encP encCNF x).length + 2 ^ qInit (BOf x.1 + Nat.log 2 (x.2.length + 2)) +
          pAsmG (encPair encP encCNF x).length +
          K * (poly (encPair encP encCNF x).length + R x)) +
          pAsmF (encPair encP encCNF x).length) +
        K * (poly (encPair encP encCNF x).length + R x) := by
      rw [NativeCertificate.comp_time]
      dsimp only [Function.comp_apply, assembleFinalCand, assembleGreedyInput]
      exact Nat.add_le_add ht4 hfinal_absorb
    have ht6 : (fastPathCertificate k hNOf hBOf cPoly).time x ≤ _ :=
      (hCap x).trans (Nat.add_le_add_right ht5 _)
    refine (Nat.add_le_add hg ht6).trans ?_
    dsimp only [K]
    generalize 2 ^ qInit (BOf x.1 + Nat.log 2 (x.2.length + 2)) = E_init
    generalize (3 * NOf x.1 + 1) *
      (candidateTupleCount x.2.length (greedyRowListLength (BOf x.1) x.2.length) + 1) *
      (poly (encPair encP encCNF x).length + R x) = T_prod
    dsimp only [poly]; omega

/-- **Split `ComputableInO` time and polynomial-workspace bound for `sparseCNFDeclaredCounter`.** -/
theorem computableInO_sparseCNFDeclaredCounter (k N₀ : ℕ)
    (hNOf : ComputableInPolyTime NOf encP encUnary) (hBOf : ComputableInPolyTime BOf encP encUnary)
    {polyCounter : PolySys → ℕ}
    (cPoly : NativeCertificate polyCounter (encPair encUnary encSys) encNat)
    (hSpace : PolyBounded (fun y => (encPair encUnary encSys y).length) cPoly.space) :
    ∃ poly qInit polySys : ℕ → ℕ, Cslib.PolynomiallyBounded poly ∧
      Cslib.PolynomiallyBounded qInit ∧ Cslib.PolynomiallyBounded polySys ∧
      ∀ R, ValidPolyTimeBound encP NOf BOf k N₀ cPoly polySys R →
        ComputableInO (sparseCNFDeclaredCounter NOf BOf k N₀ polyCounter)
          (encPair encP encCNF) encNat (sparseCNFTimeBound encP NOf BOf k N₀ poly qInit R)
          (fun x => poly (encPair encP encCNF x).length) := by
  obtain ⟨poly, qInit, polySys, hpoly, hqInit, hpolySys, hS, hT⟩ :=
    exists_sparseCNFDeclaredCertificate_bounds k N₀ hNOf hBOf cPoly hSpace
  exact ⟨poly, qInit, polySys, hpoly, hqInit, hpolySys, fun R hR =>
    (sparseCNFDeclaredCertificate k N₀ hNOf hBOf cPoly).computes.mono 2 (hT R hR) fun x =>
      (hS x).trans (by omega)⟩

/-! #### Right-Shift Normalization Certificate -/

private def shiftAmount (NOf : P → ℕ) (x : P × CNF ℕ) : ℕ := NOf x.1 - x.2.distinctVars.length

private theorem computableInPolyTime_shiftAmount
    (hNOf : ComputableInPolyTime NOf encP encUnary) :
    ComputableInPolyTime (shiftAmount NOf) (encPair encP encCNF) encNat := by
  have u2b : ComputableInPolyTime id encUnary encNat := by fun_prop
  have hN := u2b.comp (hNOf.comp (ComputableInPolyTime.fst encP encCNF))
  have hnv := u2b.comp
    (SAT.computableInPolyTime_numVars.comp (ComputableInPolyTime.snd encP encCNF))
  refine (ComputableInPolyTime.binary_sub' hN hnv).of_enc_eq fun x => congrArg encNat ?_
  rw [shiftAmount, CNF.length_distinctVars]; rfl

/-- **Native resource certificate for `normalizeDeclaredLeaf NOf h`**, composing `cLeaf` with
`ComputableInPolyTime.binary_shiftRight` on `NOf x.1 - x.2.distinctVars.length`. -/
noncomputable def normalizeDeclaredLeafCertificate
    (hNOf : ComputableInPolyTime NOf encP encUnary) {h : P × CNF ℕ → ℕ}
    (cLeaf : NativeCertificate h (encPair encP encCNF) encNat) :
    NativeCertificate (normalizeDeclaredLeaf NOf h) (encPair encP encCNF) encNat :=
  ((NativeCertificate.ofPolyTime ComputableInPolyTime.binary_shiftRight).comp
    (cLeaf.prod (NativeCertificate.ofPolyTime (computableInPolyTime_shiftAmount hNOf)))).congr
    fun _ => rfl

/-- Polynomial workspace preservation for `normalizeDeclaredLeafCertificate`. -/
theorem polyBounded_normalizeDeclaredLeafCertificate_space
    (hNOf : ComputableInPolyTime NOf encP encUnary) {h : P × CNF ℕ → ℕ}
    (cLeaf : NativeCertificate h (encPair encP encCNF) encNat)
    (hSpace : PolyBounded (fun x : P × CNF ℕ => (encPair encP encCNF x).length) cLeaf.space) :
    PolyBounded (fun x : P × CNF ℕ => (encPair encP encCNF x).length)
      (normalizeDeclaredLeafCertificate hNOf cLeaf).space := by
  unfold normalizeDeclaredLeafCertificate
  have hSh := NativeCertificate.ofPolyTime_isPolynomial (computableInPolyTime_shiftAmount hNOf)
  have hSr := NativeCertificate.ofPolyTime_isPolynomial ComputableInPolyTime.binary_shiftRight
  exact polyBounded_comp_space _ _ hSr.2 (polyBounded_prod_space _ _ hSpace hSh.2)

/-- Explicit certificate-level workspace and additive polynomial-time overhead bounds for
`normalizeDeclaredLeafCertificate`. -/
theorem exists_normalizeDeclaredLeafCertificate_bounds
    (hNOf : ComputableInPolyTime NOf encP encUnary) {h : P × CNF ℕ → ℕ}
    (cLeaf : NativeCertificate h (encPair encP encCNF) encNat)
    (hSpace : PolyBounded (fun x : P × CNF ℕ => (encPair encP encCNF x).length) cLeaf.space) :
    ∃ poly : ℕ → ℕ, Cslib.PolynomiallyBounded poly ∧
      (∀ x, (normalizeDeclaredLeafCertificate hNOf cLeaf).space x ≤
        poly (encPair encP encCNF x).length) ∧
      (∀ x, (normalizeDeclaredLeafCertificate hNOf cLeaf).time x ≤
        cLeaf.time x + poly (encPair encP encCNF x).length) := by
  have hNormSpace := polyBounded_normalizeDeclaredLeafCertificate_space hNOf cLeaf hSpace
  have hPairLen : PolyBounded (fun x : P × CNF ℕ => (encPair encP encCNF x).length)
      (fun x => (encPair encNat encNat (h x, shiftAmount NOf x)).length) :=
    ((((PolyBounded.const 2).mul (polyBounded_output_of_space cLeaf hSpace)).add
      (computableInPolyTime_shiftAmount hNOf).polyBounded_length).add (.const 2)).mono fun x => by
      simp only [length_encPair]; omega
  have hShT := (NativeCertificate.ofPolyTime_isPolynomial (computableInPolyTime_shiftAmount hNOf)).1
  have hSrT := (NativeCertificate.ofPolyTime_isPolynomial
    ComputableInPolyTime.binary_shiftRight).1.comp hPairLen
  obtain ⟨poly, hpoly, _, hB⟩ := exists_mono_poly ((hNormSpace.add hShT).add hSrT)
  refine ⟨poly, hpoly, fun x => by have hx := hB x; omega, fun x => ?_⟩
  have hx := hB x
  change cLeaf.time x +
    (NativeCertificate.ofPolyTime (computableInPolyTime_shiftAmount hNOf)).time x +
    (NativeCertificate.ofPolyTime ComputableInPolyTime.binary_shiftRight).time
      (h x, shiftAmount NOf x) ≤ _; omega

/-- Split `ComputableInO` time and polynomial-workspace bound for `normalizeDeclaredLeaf`. -/
theorem computableInO_normalizeDeclaredLeaf
    (hNOf : ComputableInPolyTime NOf encP encUnary) {h : P × CNF ℕ → ℕ}
    (cLeaf : NativeCertificate h (encPair encP encCNF) encNat)
    (hSpace : PolyBounded (fun x : P × CNF ℕ => (encPair encP encCNF x).length) cLeaf.space) :
    ∃ poly : ℕ → ℕ, Cslib.PolynomiallyBounded poly ∧
      ComputableInO (normalizeDeclaredLeaf NOf h) (encPair encP encCNF) encNat
        (fun x => cLeaf.time x + poly (encPair encP encCNF x).length)
        (fun x => poly (encPair encP encCNF x).length) := by
  obtain ⟨poly, hpoly, hS, hT⟩ := exists_normalizeDeclaredLeafCertificate_bounds hNOf cLeaf hSpace
  exact ⟨poly, hpoly, (normalizeDeclaredLeafCertificate hNOf cLeaf).computes.mono_le hT hS⟩

/-- **Native resource certificate for `sparseCNFLeafCounter`.** -/
noncomputable def sparseCNFLeafCertificate (k N₀ : ℕ)
    (hNOf : ComputableInPolyTime NOf encP encUnary) (hBOf : ComputableInPolyTime BOf encP encUnary)
    {polyCounter : PolySys → ℕ}
    (cPoly : NativeCertificate polyCounter (encPair encUnary encSys) encNat) :
    NativeCertificate (sparseCNFLeafCounter NOf BOf k N₀ polyCounter)
      (encPair encP encCNF) encNat :=
  (normalizeDeclaredLeafCertificate hNOf
    (sparseCNFDeclaredCertificate k N₀ hNOf hBOf cPoly)).congr fun _ => rfl

/-- **Polynomial workspace of `sparseCNFLeafCertificate`.** -/
theorem polyBounded_sparseCNFLeafCertificate_space (k N₀ : ℕ)
    (hNOf : ComputableInPolyTime NOf encP encUnary) (hBOf : ComputableInPolyTime BOf encP encUnary)
    {polyCounter : PolySys → ℕ}
    (cPoly : NativeCertificate polyCounter (encPair encUnary encSys) encNat)
    (hSpace : PolyBounded (fun y => (encPair encUnary encSys y).length) cPoly.space) :
    PolyBounded (fun x : P × CNF ℕ => (encPair encP encCNF x).length)
      (sparseCNFLeafCertificate k N₀ hNOf hBOf cPoly).space := by
  unfold sparseCNFLeafCertificate
  exact polyBounded_normalizeDeclaredLeafCertificate_space hNOf _
    (polyBounded_sparseCNFDeclaredCertificate_space k N₀ hNOf hBOf cPoly hSpace)

/-- **Certificate-level workspace and split-time bounds for `sparseCNFLeafCertificate`.** -/
theorem exists_sparseCNFLeafCertificate_bounds (k N₀ : ℕ)
    (hNOf : ComputableInPolyTime NOf encP encUnary) (hBOf : ComputableInPolyTime BOf encP encUnary)
    {polyCounter : PolySys → ℕ}
    (cPoly : NativeCertificate polyCounter (encPair encUnary encSys) encNat)
    (hSpace : PolyBounded (fun y => (encPair encUnary encSys y).length) cPoly.space) :
    ∃ poly qInit polySys : ℕ → ℕ, Cslib.PolynomiallyBounded poly ∧
      Cslib.PolynomiallyBounded qInit ∧ Cslib.PolynomiallyBounded polySys ∧
      (∀ x, (sparseCNFLeafCertificate k N₀ hNOf hBOf cPoly).space x ≤
        poly (encPair encP encCNF x).length) ∧
      ∀ R, ValidPolyTimeBound encP NOf BOf k N₀ cPoly polySys R → ∀ x,
        (sparseCNFLeafCertificate k N₀ hNOf hBOf cPoly).time x ≤
          2 * (sparseCNFTimeBound encP NOf BOf k N₀ poly qInit R x + 1) := by
  obtain ⟨pDecl, qInit, polySys, hpDecl, hqInit, hpolySys, _, hDeclT⟩ :=
    exists_sparseCNFDeclaredCertificate_bounds k N₀ hNOf hBOf cPoly hSpace
  obtain ⟨pNorm, hpNorm, hNormS, hNormT⟩ := exists_normalizeDeclaredLeafCertificate_bounds hNOf
    (sparseCNFDeclaredCertificate k N₀ hNOf hBOf cPoly)
    (polyBounded_sparseCNFDeclaredCertificate_space k N₀ hNOf hBOf cPoly hSpace)
  let poly (L : ℕ) : ℕ := pDecl L + pNorm L
  refine ⟨poly, qInit, polySys, hpDecl.add hpNorm, hqInit, hpolySys,
    fun x => by unfold sparseCNFLeafCertificate; exact (hNormS x).trans (Nat.le_add_left _ _),
    fun R hR x => ?_⟩
  have h1 : (sparseCNFLeafCertificate k N₀ hNOf hBOf cPoly).time x ≤
      (sparseCNFDeclaredCertificate k N₀ hNOf hBOf cPoly).time x +
        pNorm (encPair encP encCNF x).length := by
    unfold sparseCNFLeafCertificate; exact hNormT x
  have h2 := hDeclT R hR x
  unfold sparseCNFTimeBound at h2 ⊢; dsimp only at h2 ⊢
  cases hfast : entersSparseFastPath k N₀ (NOf x.1) (BOf x.1) x.2
  · simp only [hfast, Bool.false_eq_true, ↓reduceIte] at h2 ⊢; dsimp only [poly]; omega
  · simp only [hfast, ↓reduceIte] at h2 ⊢
    have hmul := Nat.mul_le_mul_left ((3 * NOf x.1 + 1) *
      (candidateTupleCount x.2.length (greedyRowListLength (BOf x.1) x.2.length) + 1))
      (show pDecl (encPair encP encCNF x).length + R x ≤
        poly (encPair encP encCNF x).length + R x by dsimp only [poly]; omega)
    dsimp only [poly] at hmul ⊢; omega

/-- **Split `ComputableInO` time and polynomial-workspace bound for `sparseCNFLeafCounter`.** -/
theorem computableInO_sparseCNFLeafCounter (k N₀ : ℕ)
    (hNOf : ComputableInPolyTime NOf encP encUnary) (hBOf : ComputableInPolyTime BOf encP encUnary)
    {polyCounter : PolySys → ℕ}
    (cPoly : NativeCertificate polyCounter (encPair encUnary encSys) encNat)
    (hSpace : PolyBounded (fun y => (encPair encUnary encSys y).length) cPoly.space) :
    ∃ poly qInit polySys : ℕ → ℕ, Cslib.PolynomiallyBounded poly ∧
      Cslib.PolynomiallyBounded qInit ∧ Cslib.PolynomiallyBounded polySys ∧
      ∀ R, ValidPolyTimeBound encP NOf BOf k N₀ cPoly polySys R →
        ComputableInO (sparseCNFLeafCounter NOf BOf k N₀ polyCounter)
          (encPair encP encCNF) encNat (sparseCNFTimeBound encP NOf BOf k N₀ poly qInit R)
          (fun x => poly (encPair encP encCNF x).length) := by
  obtain ⟨poly, qInit, polySys, hpoly, hqInit, hpolySys, hS, hT⟩ :=
    exists_sparseCNFLeafCertificate_bounds k N₀ hNOf hBOf cPoly hSpace
  exact ⟨poly, qInit, polySys, hpoly, hqInit, hpolySys, fun R hR =>
    (sparseCNFLeafCertificate k N₀ hNOf hBOf cPoly).computes.mono 2 (hT R hR) fun x =>
      (hS x).trans (by omega)⟩

end Cslib.Complexity.SparseCNFLeafCounter

end
