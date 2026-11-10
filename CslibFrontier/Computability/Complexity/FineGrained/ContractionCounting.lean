/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.ClauseNetworkPolyTime
public import CslibFrontier.Computability.Complexity.Classes.CountingSimulation.FastLeaves
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.Plain
import CslibFrontier.Computability.Complexity.Classes.CountingSimulation.ContractionCall
import CslibFrontier.Computability.Complexity.Problems.SAT.PolyTime
import CslibFrontier.Logics.Propositional.CNF.ModelCount.Declared
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListPrimitives
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeNatFrontends

/-!
# Model counting by tensor contraction: the fixed-density bound of Theorem 1.1

For every fixed clause width `k`, one native machine computes the number of satisfying
assignments `CNF.modelCount φ` of every formula `φ` whose clauses have at most `k` literals, in
time `2 ^ (A (m + 1) / √⌊log₂ (n + 2)⌋)` times a polynomial in the encoding length, and in
polynomial space, where `m` is the number of clauses and `n` the number of variables
(`ContractionCounting.exists_modelCounter`). For formulas with at most `D n` clauses this is
time `2 ^ O_{k,D}(n / √log n)` times a polynomial, the fixed-density bound of Theorem 1.1 of
[OpenAI2026ETH] (`ContractionCounting.exists_modelCounter_fixedDensity`). Measured by the number
`N` of literal occurrences instead, the time is `2 ^ (A (N + 1) / √⌊log₂ (N + 2)⌋)` times a
polynomial (`ContractionCounting.exists_modelCounter_occurrences`), with no logarithm of the number
of variables in the exponent; this form extends to formulas of unbounded clause width
(`Cslib.Complexity.ContractionCounting.exists_modelCounter_unboundedWidth`).

The machine is the proof of Appendix D.2: it writes out the clause network of the formula
(`Cslib.Circuits.Frontier.ClauseNetwork.clauseNetwork`), whose contraction is the model count,
and contracts it modulo `2 ^ (3 N)`, where `N` is the number of literal occurrences, with the
contraction algorithm of Theorem D.1 (`CountingSimulation.fastContractionAlgorithm`). The network
has `s = 3 N` edges, at most `3 N` vertices and degree at most `max k 4`, so it is admissible at
size `s` and the contraction takes `2 ^ O(s / √log s)` steps; since `n + 2 ≤ s ≤ 3 k m`, the
exponent is `O_k(m / √log n)`. Formulas that are empty, have an empty clause or have a clause
longer than `k` are answered directly.

This does not prove the arbitrary-density bound `2 ^ O_k(n log log n / √log n)` of Theorem 1.1,
which Appendix D.3 obtains from Theorem D.1 with truncation order `ℓ = n + 1`; the contraction
algorithm here has `ℓ = 1`. For dense formulas the exponent above exceeds `n`; the
interpolation-scale counter `CountingNativeEndpoint.exists_modelCounter` remains the bound for
them.

## Main results

* `Cslib.Complexity.ContractionCounting.exists_modelCounter`: the counter, with exponent
  `A (m + 1) / √⌊log₂ (n + 2)⌋`.
* `Cslib.Complexity.ContractionCounting.exists_modelCounter_occurrences`: the counter, with exponent
  `A (N + 1) / √⌊log₂ (N + 2)⌋` for `N` literal occurrences.
* `Cslib.Complexity.ContractionCounting.exists_modelCounter_fixedDensity`: for each density
  bound `D`, exponent `A (n + 1) / √⌊log₂ (n + 2)⌋` on formulas with at most `D n` clauses.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], Theorem 1.1 (p. 2),
  Appendix D.2 (p. 54) and Theorem D.1 (p. 53).
-/

public section

namespace Cslib.Complexity.ContractionCounting

open Cslib.Logic.PL Cslib.Circuits.Frontier Cslib.Circuits.Frontier.ClauseNetwork
  Turing.MultiTapeTM Cslib.GenericRAM CountingSimulation

/-- The formulas handed to the contraction algorithm: nonempty, with every clause of between one
and `k` literals. -/
@[expose] def guard (k : ℕ) (φ : CNF ℕ) : Bool :=
  !φ.isEmpty && φ.all fun c => decide (1 ≤ c.length ∧ c.length ≤ k)

/-- The input of the contraction algorithm: the precision `3 N`, for `N` literal occurrences, and
the clause network. -/
@[expose] def contractionInput (k : ℕ) (φ : CNF ℕ) : ℕ × ℕ × ExplicitTensorNetwork ℕ :=
  (3 * φ.vars.length, clauseNetwork k φ)

/-- The answer off the guard: one for the empty formula, zero otherwise. -/
@[expose] def fallback (φ : CNF ℕ) : ℕ := if φ.isEmpty then 1 else 0

/-- The count computed by the machine. -/
@[expose] def count (k : ℕ) (φ : CNF ℕ) : ℕ :=
  if guard k φ then (clauseNetwork k φ).2.contraction % 2 ^ (3 * φ.vars.length) else fallback φ

theorem computableInPolyTime_guard (k : ℕ) : ComputableInPolyTime (guard k) encCNF encBool := by
  unfold guard
  fun_prop

theorem computableInPolyTime_contractionInput (k : ℕ) :
    ComputableInPolyTime (contractionInput k) encCNF
      (encPair encNat (encPair encNat ExplicitTensorNetwork.encExplicitNetwork)) :=
  (ComputableInPolyTime.unary_to_binary.comp (ComputableInPolyTime.unary_mul'
    (ComputableInPolyTime.const 3)
    (SAT.computableInPolyTime_vars_length (ComputableInPolyTime.id' (encIn := encCNF))))).prod
    (computableInPolyTime_clauseNetwork k)

theorem computableInPolyTime_fallback : ComputableInPolyTime fallback encCNF encNat := by
  unfold fallback
  fun_prop

/-- **The machine**: the guard, then the contraction algorithm on the clause network or the
direct answer. -/
noncomputable def certificate (k : ℕ) : NativeCertificate (count k) encCNF encNat :=
  (NativeCertificate.branch (NativeCertificate.ofPolyTime (computableInPolyTime_guard k))
    (fastContractionAlgorithm.certificate.comp
      (NativeCertificate.ofPolyTime (computableInPolyTime_contractionInput k)))
    (NativeCertificate.ofPolyTime computableInPolyTime_fallback)).congr fun _ => rfl

/-! ### Correctness -/

theorem guard_eq_true_iff {k : ℕ} {φ : CNF ℕ} :
    guard k φ = true ↔ φ ≠ [] ∧ ∀ c ∈ φ, 1 ≤ c.length ∧ c.length ≤ k := by
  simp [guard]

/-- A formula whose clauses are nonempty has at least as many literals as clauses. -/
theorem length_le_length_vars {φ : CNF ℕ} (h : ∀ c ∈ φ, 1 ≤ c.length) :
    φ.length ≤ φ.vars.length := by
  rw [CNF.length_vars]
  induction φ with
  | nil => simp
  | cons c φ ih =>
    have hc := h c List.mem_cons_self
    have := ih fun c' hc' => h c' (List.mem_cons_of_mem _ hc')
    simp only [List.length_cons, List.map_cons, List.sum_cons]
    omega

/-- **The machine counts models** of every formula whose clauses have at most `k` literals. -/
theorem count_eq {k : ℕ} {φ : CNF ℕ} (hk : ∀ c ∈ φ, c.length ≤ k) :
    count k φ = φ.modelCount := by
  unfold count
  split
  · next hg =>
    obtain ⟨hne, hcl⟩ := guard_eq_true_iff.mp hg
    rw [contraction_clauseNetwork hk]
    refine Nat.mod_eq_of_lt (φ.modelCount_le_two_pow_numVars.trans_lt ?_)
    have h1 : 1 ≤ φ.length := List.length_pos_iff.mpr hne
    have h2 := length_le_length_vars fun c hc => (hcl c hc).1
    have h3 := CNF.numVars_le_length_vars φ
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  · next hg =>
    unfold fallback
    cases φ with
    | nil =>
      rw [← CNF.modelCountOn_vars, CNF.modelCountOn_nil]
      rfl
    | cons c φ =>
      have hnil : [] ∈ c :: φ := by
        by_contra hnil
        apply hg
        refine guard_eq_true_iff.mpr ⟨List.cons_ne_nil _ _, fun c' hc' => ⟨?_, hk c' hc'⟩⟩
        rcases Nat.eq_zero_or_pos c'.length with h0 | h0
        · exact (hnil (List.length_eq_zero_iff.mp h0 ▸ hc')).elim
        · exact h0
      rw [← CNF.modelCountOn_vars, CNF.modelCountOn_eq_zero_of_nil_mem hnil]
      simp


/-! ### Resources -/

/-- **Admissibility**: the clause network of a guarded formula with `N` literal occurrences is
admissible at size `3 N`, its number of edges, with constant `k + 4`. -/
theorem explicitAdmissible_clauseNetwork {k : ℕ} {φ : CNF ℕ} (hg : guard k φ = true) :
    ExplicitAdmissible (k + 4) (3 * φ.vars.length) (clauseNetwork k φ) := by
  obtain ⟨hne, hcl⟩ := guard_eq_true_iff.mp hg
  have hk : ∀ c ∈ φ, c.length ≤ k := fun c hc => (hcl c hc).2
  have h1 : 1 ≤ φ.length := List.length_pos_iff.mpr hne
  have hm := length_le_length_vars fun c hc => (hcl c hc).1
  have hlog : 1 ≤ Nat.log 2 (3 * φ.vars.length) := Nat.log_pos (by norm_num) (by omega)
  refine ⟨isRowsFirstBipartite_clauseNetwork k φ, ?_, ?_, ?_, length_table_clauseNetwork hk, ?_⟩
  · rw [numEdges_clauseNetwork]
    nlinarith
  · refine (maxDegree_clauseNetwork_le hk).trans ?_
    have : max k 4 ≤ k + 4 := max_le (by omega) (by omega)
    nlinarith
  · rw [length_vertices_clauseNetwork]
    nlinarith
  · rw [numEdges_clauseNetwork]

/-- The exponent of the contraction is at most `3 k K (m + 1) / √⌊log₂ (n + 2)⌋`. -/
theorem exponent_le {k K N m n : ℕ} (hN : 1 ≤ N) (hNm : N ≤ k * m) (hnN : n ≤ N) :
    K * (3 * N) / Nat.sqrt (Nat.log 2 (3 * N)) ≤
      3 * k * K * (m + 1) / Nat.sqrt (Nat.log 2 (n + 2)) := by
  refine Nat.div_le_div ?_ (Nat.sqrt_le_sqrt (Nat.log_mono_right (by omega))) ?_
  · have : K * (3 * N) ≤ K * (3 * (k * m)) := Nat.mul_le_mul_left _ (by omega)
    nlinarith
  · exact Nat.sqrt_eq_zero.not.mpr (Nat.log_pos (by norm_num) (by omega)).ne'

/-- The exponent of the contraction is at most `3 K (N + 1) / √⌊log₂ (N + 2)⌋` for `N ≥ 1` literal
occurrences. -/
theorem exponent_le_occurrences {K N : ℕ} (hN : 1 ≤ N) :
    K * (3 * N) / Nat.sqrt (Nat.log 2 (3 * N)) ≤
      3 * K * (N + 1) / Nat.sqrt (Nat.log 2 (N + 2)) := by
  refine Nat.div_le_div ?_ (Nat.sqrt_le_sqrt (Nat.log_mono_right (by omega))) ?_
  · nlinarith
  · exact Nat.sqrt_eq_zero.not.mpr (Nat.log_pos (by norm_num) (by omega)).ne'

/-- The machine runs in polynomial space, and in time `2 ^ F φ` times a polynomial for every
exponent `F` that bounds the contraction's exponent `K s / √⌊log₂ s⌋` at the network size
`s = 3 N` on the formulas handed to the contraction algorithm. -/
private theorem expTimePolySpace_certificate (k : ℕ) :
    ∃ K : ℕ, ∀ F : CNF ℕ → ℕ,
      (∀ φ, guard k φ = true →
        K * (3 * φ.vars.length) / Nat.sqrt (Nat.log 2 (3 * φ.vars.length)) ≤ F φ) →
      (certificate k).ExpTimePolySpace F :=
  fastContractionAlgorithm.expTimePolySpace_branch (computableInPolyTime_guard k)
    (computableInPolyTime_contractionInput k) computableInPolyTime_fallback (k + 4) 1
    (fun φ => 3 * φ.vars.length) fun φ hg => by
      obtain ⟨hne, hcl⟩ := guard_eq_true_iff.mp hg
      have h1 : 1 ≤ φ.length := List.length_pos_iff.mpr hne
      have hm := length_le_length_vars fun c hc => (hcl c hc).1
      dsimp only [contractionInput]
      exact ⟨by omega, by omega, by omega, explicitAdmissible_clauseNetwork hg⟩

/-- **Model counting by tensor contraction.** For each clause width `k`, one machine computes
`φ.modelCount` on every formula `φ` whose clauses have at most `k` literals, in time
`2 ^ (A (m + 1) / √⌊log₂ (n + 2)⌋)` times a polynomial in the encoding length and in polynomial
space, where `m` is the number of clauses and `n` the number of variables. -/
theorem exists_modelCounter (k : ℕ) :
    ∃ (count : CNF ℕ → ℕ) (A e b : ℕ),
      (∀ φ : CNF ℕ, (∀ c ∈ φ, c.length ≤ k) → count φ = φ.modelCount) ∧
      ComputableInO count encCNF encNat
        (fun φ => 2 ^ (A * (φ.length + 1) / Nat.sqrt (Nat.log 2 (φ.numVars + 2))) *
          ((encCNF φ).length + 1) ^ e)
        (fun φ => ((encCNF φ).length + 1) ^ b) := by
  obtain ⟨K, h⟩ := expTimePolySpace_certificate k
  have hc := h (fun φ => 3 * k * K * (φ.length + 1) / Nat.sqrt (Nat.log 2 (φ.numVars + 2)))
    fun φ hg => by
      obtain ⟨hne, hcl⟩ := guard_eq_true_iff.mp hg
      have h1 : 1 ≤ φ.length := List.length_pos_iff.mpr hne
      have hm := length_le_length_vars fun c hc => (hcl c hc).1
      exact exponent_le (by omega) (CNF.length_vars_le_mul_length fun c hc => (hcl c hc).2)
        (CNF.numVars_le_length_vars φ)
  obtain ⟨e, he⟩ := hc.computableInO
  exact ⟨count k, 3 * k * K, e, e, fun φ hk => count_eq hk, he⟩

/-- **Model counting by tensor contraction, measured by literal occurrences.** For each clause
width `k`, one machine computes `φ.modelCount` on every formula `φ` whose clauses have at most `k`
literals, in time `2 ^ (A (N + 1) / √⌊log₂ (N + 2)⌋)` times a polynomial in the encoding length
and in polynomial space, where `N` is the number of literal occurrences. Unlike
`exists_modelCounter`, the exponent does not divide by the logarithm of the number of variables,
so it stays `O(N / √log N)` for formulas with many clauses on few variables. -/
theorem exists_modelCounter_occurrences (k : ℕ) :
    ∃ (count : CNF ℕ → ℕ) (A e b : ℕ),
      (∀ φ : CNF ℕ, (∀ c ∈ φ, c.length ≤ k) → count φ = φ.modelCount) ∧
      ComputableInO count encCNF encNat
        (fun φ => 2 ^ (A * (φ.vars.length + 1) / Nat.sqrt (Nat.log 2 (φ.vars.length + 2))) *
          ((encCNF φ).length + 1) ^ e)
        (fun φ => ((encCNF φ).length + 1) ^ b) := by
  obtain ⟨K, h⟩ := expTimePolySpace_certificate k
  have hc := h (fun φ => 3 * K * (φ.vars.length + 1) / Nat.sqrt (Nat.log 2 (φ.vars.length + 2)))
    fun φ hg => by
      obtain ⟨hne, hcl⟩ := guard_eq_true_iff.mp hg
      have h1 : 1 ≤ φ.length := List.length_pos_iff.mpr hne
      have hm := length_le_length_vars fun c hc => (hcl c hc).1
      exact exponent_le_occurrences (by omega)
  obtain ⟨e, he⟩ := hc.computableInO
  exact ⟨count k, 3 * K, e, e, fun φ hk => count_eq hk, he⟩

/-- **The fixed-density bound of Theorem 1.1.** For each clause width `k`, one machine computes
`φ.modelCount` on every formula `φ` whose clauses have at most `k` literals, in polynomial space,
and for each density `D` its time on formulas with at most `D n` clauses, for `n` variables, is
`2 ^ (A (n + 1) / √⌊log₂ (n + 2)⌋)` times a polynomial in the encoding length. The machine, its
time and space functions and the degree `e` of the polynomial are fixed before `D`; only `A`
depends on `D`. -/
theorem exists_modelCounter_fixedDensity (k : ℕ) :
    ∃ (count : CNF ℕ → ℕ) (T S : CNF ℕ → ℕ) (e b : ℕ),
      (∀ φ : CNF ℕ, (∀ c ∈ φ, c.length ≤ k) → count φ = φ.modelCount) ∧
      ComputableInO count encCNF encNat T S ∧
      (∀ φ, S φ = ((encCNF φ).length + 1) ^ b) ∧
      ∀ D : ℕ, ∃ A : ℕ, ∀ φ : CNF ℕ, φ.length ≤ D * φ.numVars →
        T φ ≤ 2 ^ (A * (φ.numVars + 1) / Nat.sqrt (Nat.log 2 (φ.numVars + 2))) *
          ((encCNF φ).length + 1) ^ e := by
  obtain ⟨count, A, e, b, hcount, hc⟩ := exists_modelCounter k
  refine ⟨count, _, _, e, b, hcount, hc, fun _ => rfl, fun D => ⟨A * (D + 1), fun φ hφ => ?_⟩⟩
  refine Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) (Nat.div_le_div_right ?_))
  have : φ.length + 1 ≤ (D + 1) * (φ.numVars + 1) := by nlinarith
  calc A * (φ.length + 1) ≤ A * ((D + 1) * (φ.numVars + 1)) := Nat.mul_le_mul_left _ this
    _ = A * (D + 1) * (φ.numVars + 1) := by ring

end Cslib.Complexity.ContractionCounting
