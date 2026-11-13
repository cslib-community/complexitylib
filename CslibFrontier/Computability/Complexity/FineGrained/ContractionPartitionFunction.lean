/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.CSPNetworkPolyTime
public import CslibFrontier.Computability.Complexity.FineGrained.ContractionCounting
public import CslibFrontier.Logics.Propositional.CSP.HardCore
import CslibFrontier.Computability.Complexity.Classes.CountingSimulation.ContractionCall
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.PolyTime.CSP.Vars
import CslibFrontier.Logics.Propositional.CSP.Vars
import Mathlib.Data.Set.Finite.List

/-!
# Weighted `#CSP` by tensor contraction

For every fixed arity bound `k` and weight bound `W`, one native machine computes the partition
function `F.partitionFunction wt` of every weighted Boolean CSP instance `F : CSP Rel ℕ` whose
constraints have between one and `k` variables, in time `2 ^ (A (N + 1) / √⌊log₂ (n + 2)⌋)` times
a polynomial in the encoding length, and in polynomial space, where `N` is the number of variable
occurrences and `n` the number of variables
(`ContractionPartitionFunction.exists_partitionFunctionCounter`). The weights `wt R w` at patterns
of length at most `k` must be at most `W` and polynomial-time in the relation symbol `R`; both hold
over a finite relation alphabet
(`ContractionPartitionFunction.exists_partitionFunctionCounter_of_finite`).

On instances in which every variable occurs at most `Δ` times, `N ≤ Δ n`, so the time is
`2 ^ O_{k,W,Δ}(n / √log n)` times a polynomial
(`ContractionPartitionFunction.exists_partitionFunctionCounter_boundedDegree`). Weighted counting
problems on bounded-degree graphs, such as independent sets and the hard-core model
(`ContractionPartitionFunction.exists_hardCoreCounter`), or perfect matchings with one Boolean
variable per edge, are such instances.

The machine is that of `ContractionCounting.exists_modelCounter` with weighted tables: it writes
out the constraint network of the instance
(`Cslib.Circuits.Frontier.ClauseNetwork.cspNetwork`), whose contraction is the partition function,
and contracts it modulo `2 ^ ((W + 1) 3 N)`, which exceeds the partition function, with the
contraction algorithm of Theorem D.1 of [OpenAI2026ETH]
(`CountingSimulation.fastContractionAlgorithm`). The network has `s = 3 N` edges, at most `3 N`
vertices and degree at most `max k 4`, so it is admissible at size `s`. The empty instance is
answered directly.

Constraints with an empty scope are excluded: arbitrarily many of them would break the bound on the
number of vertices that admissibility requires. The rate is that of Theorem D.1; no claim of
novelty is made for the application.

## Main results

* `Cslib.Complexity.ContractionPartitionFunction.exists_partitionFunctionCounter`: the counter,
  with exponent `A (N + 1) / √⌊log₂ (n + 2)⌋`.
* `Cslib.Complexity.ContractionPartitionFunction.exists_partitionFunctionCounter_boundedDegree`:
  for each occurrence bound `Δ`, exponent `A (n + 1) / √⌊log₂ (n + 2)⌋`.
* `Cslib.Complexity.ContractionPartitionFunction.exists_partitionFunctionCounter_of_finite`: the
  counter over a finite relation alphabet.
* `Cslib.Complexity.ContractionPartitionFunction.exists_hardCoreCounter`: the weighted count of
  independent sets of bounded-degree graphs (the hard-core model with integer fugacity).

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], Appendix D.2 (p. 54) and
  Theorem D.1 (p. 53).
-/

public section

namespace Cslib.Complexity.ContractionPartitionFunction

open Cslib.Logic.PL Cslib.Circuits.Frontier Cslib.Circuits.Frontier.ClauseNetwork
  Turing.MultiTapeTM Cslib.GenericRAM CountingSimulation ComputableInPolyTime

variable {Rel : Type}

/-- The instances handed to the contraction algorithm: nonempty, with every constraint of between
one and `k` variables. -/
@[expose] def guard (k : ℕ) (F : CSP Rel ℕ) : Bool :=
  !F.isEmpty && F.all fun c => decide (1 ≤ c.scope.length ∧ c.scope.length ≤ k)

/-- The precision of the contraction, `(W + 1) 3 N` for `N` variable occurrences. -/
@[expose] def precision (W : ℕ) (F : CSP Rel ℕ) : ℕ := (W + 1) * (3 * F.vars.length)

/-- The input of the contraction algorithm: the precision and the constraint network. -/
@[expose] def contractionInput (k W : ℕ) (wt : Rel → List Bool → ℕ) (F : CSP Rel ℕ) :
    ℕ × ℕ × ExplicitTensorNetwork ℕ :=
  (precision W F, cspNetwork k wt F)

/-- The answer off the guard: one for the empty instance, zero otherwise. -/
@[expose] def fallback (F : CSP Rel ℕ) : ℕ := if F.isEmpty then 1 else 0

/-- The value computed by the machine. -/
@[expose] def count (k W : ℕ) (wt : Rel → List Bool → ℕ) (F : CSP Rel ℕ) : ℕ :=
  if guard k F then (cspNetwork k wt F).2.contraction % 2 ^ precision W F else fallback F

variable (encRel : Rel ↪ List Bool)

theorem computableInPolyTime_guard (k : ℕ) :
    ComputableInPolyTime (guard (Rel := Rel) k) (encCSP encRel encNat) encBool := by
  unfold guard
  fun_prop

theorem computableInPolyTime_fallback :
    ComputableInPolyTime (fallback (Rel := Rel)) (encCSP encRel encNat) encNat := by
  unfold fallback
  fun_prop

theorem computableInPolyTime_contractionInput (k W : ℕ) (wt : Rel → List Bool → ℕ)
    (hwt : ∀ w : List Bool, w.length ≤ k →
      ComputableInPolyTime (fun R : Rel => wt R w) encRel encNat) :
    ComputableInPolyTime (contractionInput k W wt) (encCSP encRel encNat)
      (encPair encNat (encPair encNat ExplicitTensorNetwork.encExplicitNetwork)) :=
  (unary_to_binary.comp (unary_mul' (const (W + 1)) (unary_mul' (const 3)
    (CSP.computableInPolyTime_length_vars encRel encNat)))).prod
    (computableInPolyTime_cspNetwork encRel k wt hwt)

variable (k W : ℕ) (wt : Rel → List Bool → ℕ)
  (hwt : ∀ w : List Bool, w.length ≤ k →
    ComputableInPolyTime (fun R : Rel => wt R w) encRel encNat)

/-- **The machine**: the guard, then the contraction algorithm on the constraint network or the
direct answer. -/
noncomputable def certificate : NativeCertificate (count k W wt) (encCSP encRel encNat) encNat :=
  (NativeCertificate.branch (NativeCertificate.ofPolyTime (computableInPolyTime_guard encRel k))
    (fastContractionAlgorithm.certificate.comp
      (NativeCertificate.ofPolyTime (computableInPolyTime_contractionInput encRel k W wt hwt)))
    (NativeCertificate.ofPolyTime (computableInPolyTime_fallback encRel))).congr fun _ => rfl

omit encRel hwt

/-! ### Correctness -/

variable {k W wt}

theorem guard_eq_true_iff {F : CSP Rel ℕ} :
    guard k F = true ↔ F ≠ [] ∧ ∀ c ∈ F, 1 ≤ c.scope.length ∧ c.scope.length ≤ k := by
  simp [guard]

/-- **The machine computes the partition function** of every instance whose constraints have
between one and `k` variables, when the weights at patterns of length at most `k` are at most
`W`. -/
theorem count_eq (hW : ∀ R w, w.length ≤ k → wt R w ≤ W) {F : CSP Rel ℕ}
    (hk : ∀ c ∈ F, 1 ≤ c.scope.length ∧ c.scope.length ≤ k) :
    count k W wt F = F.partitionFunction wt := by
  unfold count
  split
  · rw [contraction_cspNetwork fun c hc => (hk c hc).2]
    refine Nat.mod_eq_of_lt ?_
    obtain ⟨hne, -⟩ := guard_eq_true_iff.mp ‹_›
    have hm := CSP.length_le_length_vars fun c hc => (hk c hc).1
    have h1 : 1 ≤ F.length := List.length_pos_iff.mpr hne
    have hn : F.numVars ≤ F.vars.length := List.toFinset_card_le _
    have hZ := CSP.partitionFunction_le (wt := wt) (F := F) (W := W) fun c hc w hw =>
      hW c.rel w (hw ▸ (hk c hc).2)
    rw [Fintype.card_bool] at hZ
    set N := F.vars.length
    have hW2 : W + 1 ≤ 2 ^ W := Nat.lt_two_pow_self
    calc F.partitionFunction wt ≤ 2 ^ F.numVars * W ^ F.length := hZ
      _ ≤ 2 ^ N * (2 ^ W) ^ N := Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) hn)
          ((Nat.pow_le_pow_left (Nat.le_succ W) _).trans
            ((Nat.pow_le_pow_right (Nat.succ_pos W) hm).trans (Nat.pow_le_pow_left hW2 _)))
      _ = 2 ^ ((W + 1) * N) := by rw [← pow_mul, ← pow_add]; ring_nf
      _ < 2 ^ precision W F := Nat.pow_lt_pow_right (by norm_num) (by
          rw [precision]
          have : 1 ≤ N := h1.trans hm
          nlinarith)
  · next hg =>
    unfold fallback
    cases F with
    | nil =>
      simp only [List.isEmpty_nil, ↓reduceIte, CSP.partitionFunction, CSP.weight, List.map_nil,
        List.prod_nil, Finset.sum_const, smul_eq_mul, Nat.mul_one, Finset.card_univ]
      have hempty : ∀ x : (CSP.vars ([] : CSP Rel ℕ)).toFinset, False := fun x => by
        simpa [CSP.vars] using x.2
      exact (Fintype.card_eq_one_iff.mpr ⟨fun x => (hempty x).elim,
        fun _ => funext fun x => (hempty x).elim⟩).symm
    | cons c F =>
      exact absurd (guard_eq_true_iff.mpr ⟨List.cons_ne_nil _ _, hk⟩) hg

/-! ### Resources -/

/-- **Admissibility**: the constraint network of a guarded instance with `N` variable occurrences
is admissible at size `3 N`, its number of edges, with constant `k + 4`. -/
theorem explicitAdmissible_cspNetwork {F : CSP Rel ℕ} (hg : guard k F = true) :
    ExplicitAdmissible (k + 4) (3 * F.vars.length) (cspNetwork k wt F) := by
  obtain ⟨hne, hcl⟩ := guard_eq_true_iff.mp hg
  have hk : ∀ c ∈ F, c.scope.length ≤ k := fun c hc => (hcl c hc).2
  have h1 : 1 ≤ F.length := List.length_pos_iff.mpr hne
  have hm := CSP.length_le_length_vars fun c hc => (hcl c hc).1
  have hlog : 1 ≤ Nat.log 2 (3 * F.vars.length) := Nat.log_pos (by norm_num) (by omega)
  refine ⟨isRowsFirstBipartite_cspNetwork k wt F, ?_, ?_, ?_, length_table_cspNetwork hk, ?_⟩
  · rw [numEdges_cspNetwork]
    nlinarith
  · refine (maxDegree_cspNetwork_le hk).trans ?_
    have : max k 4 ≤ k + 4 := max_le (by omega) (by omega)
    nlinarith
  · rw [length_vertices_cspNetwork]
    nlinarith
  · rw [numEdges_cspNetwork]

/-- **Weighted `#CSP` by tensor contraction.** For each arity bound `k` and weight bound `W`, one
machine computes `F.partitionFunction wt` on every instance `F` whose constraints have between one
and `k` variables, in time `2 ^ (A (N + 1) / √⌊log₂ (n + 2)⌋)` times a polynomial in the encoding
length and in polynomial space, where `N` is the number of variable occurrences and `n` the number
of variables. The weights at patterns of length at most `k` are at most `W` and polynomial-time in
the relation symbol. -/
theorem exists_partitionFunctionCounter (encRel : Rel ↪ List Bool) (k W : ℕ)
    (wt : Rel → List Bool → ℕ)
    (hwt : ∀ w : List Bool, w.length ≤ k →
      ComputableInPolyTime (fun R : Rel => wt R w) encRel encNat)
    (hW : ∀ R w, w.length ≤ k → wt R w ≤ W) :
    ∃ (count : CSP Rel ℕ → ℕ) (A e b : ℕ),
      (∀ F : CSP Rel ℕ, (∀ c ∈ F, 1 ≤ c.scope.length ∧ c.scope.length ≤ k) →
        count F = F.partitionFunction wt) ∧
      ComputableInO count (encCSP encRel encNat) encNat
        (fun F => 2 ^ (A * (F.vars.length + 1) / Nat.sqrt (Nat.log 2 (F.numVars + 2))) *
          ((encCSP encRel encNat F).length + 1) ^ e)
        (fun F => ((encCSP encRel encNat F).length + 1) ^ b) := by
  obtain ⟨K, h⟩ := fastContractionAlgorithm.expTimePolySpace_branch
    (computableInPolyTime_guard encRel k) (computableInPolyTime_contractionInput encRel k W wt hwt)
    (computableInPolyTime_fallback encRel) (k + 4) (W + 1) (fun F => 3 * F.vars.length)
    fun F hg => by
      obtain ⟨hne, hcl⟩ := guard_eq_true_iff.mp hg
      have h1 : 1 ≤ F.length := List.length_pos_iff.mpr hne
      have hm := CSP.length_le_length_vars fun c hc => (hcl c hc).1
      dsimp only [contractionInput, precision]
      exact ⟨by omega, by nlinarith, le_rfl, explicitAdmissible_cspNetwork hg⟩
  have hc := h (fun F => 3 * K * (F.vars.length + 1) / Nat.sqrt (Nat.log 2 (F.numVars + 2)))
    fun F hg => by
      obtain ⟨hne, hcl⟩ := guard_eq_true_iff.mp hg
      have h1 : 1 ≤ F.length := List.length_pos_iff.mpr hne
      have hm := CSP.length_le_length_vars fun c hc => (hcl c hc).1
      have hexp := ContractionCounting.exponent_le (K := K) (k := 1) (m := F.vars.length)
        (by omega) (by omega) (List.toFinset_card_le F.vars)
      rwa [Nat.mul_one] at hexp
  obtain ⟨e, he⟩ := hc.computableInO
  exact ⟨count k W wt, 3 * K, e, e, fun F hk => count_eq hW hk, he⟩

/-- **Weighted `#CSP` on bounded-degree instances.** For each arity bound `k` and weight bound
`W`, one machine computes `F.partitionFunction wt` on every instance `F` whose constraints have
between one and `k` variables, in polynomial space, and for each occurrence bound `Δ` its time on
instances in which every variable occurs at most `Δ` times is
`2 ^ (A (n + 1) / √⌊log₂ (n + 2)⌋)` times a polynomial in the encoding length, for `n`
variables. The machine, its time and space functions and the degree `e` of the polynomial are
fixed before `Δ`; only `A` depends on `Δ`. -/
theorem exists_partitionFunctionCounter_boundedDegree (encRel : Rel ↪ List Bool) (k W : ℕ)
    (wt : Rel → List Bool → ℕ)
    (hwt : ∀ w : List Bool, w.length ≤ k →
      ComputableInPolyTime (fun R : Rel => wt R w) encRel encNat)
    (hW : ∀ R w, w.length ≤ k → wt R w ≤ W) :
    ∃ (count : CSP Rel ℕ → ℕ) (T S : CSP Rel ℕ → ℕ) (e b : ℕ),
      (∀ F : CSP Rel ℕ, (∀ c ∈ F, 1 ≤ c.scope.length ∧ c.scope.length ≤ k) →
        count F = F.partitionFunction wt) ∧
      ComputableInO count (encCSP encRel encNat) encNat T S ∧
      (∀ F, S F = ((encCSP encRel encNat F).length + 1) ^ b) ∧
      ∀ Δ : ℕ, ∃ A : ℕ, ∀ F : CSP Rel ℕ, (∀ v, F.vars.count v ≤ Δ) →
        T F ≤ 2 ^ (A * (F.numVars + 1) / Nat.sqrt (Nat.log 2 (F.numVars + 2))) *
          ((encCSP encRel encNat F).length + 1) ^ e := by
  obtain ⟨count, A, e, b, hcount, hc⟩ := exists_partitionFunctionCounter encRel k W wt hwt hW
  refine ⟨count, _, _, e, b, hcount, hc, fun _ => rfl, fun Δ => ⟨A * (Δ + 1), fun F hF => ?_⟩⟩
  refine Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) (Nat.div_le_div_right ?_))
  have h := CSP.length_vars_le_mul_numVars hF
  have : F.vars.length + 1 ≤ (Δ + 1) * (F.numVars + 1) := by nlinarith
  calc A * (F.vars.length + 1) ≤ A * ((Δ + 1) * (F.numVars + 1)) := Nat.mul_le_mul_left _ this
    _ = A * (Δ + 1) * (F.numVars + 1) := by ring

/-- **Weighted `#CSP` by tensor contraction over a finite relation alphabet**: the weights at
patterns of length at most `k` are then bounded and polynomial-time in the relation symbol. -/
theorem exists_partitionFunctionCounter_of_finite [Finite Rel] (encRel : Rel ↪ List Bool)
    (k : ℕ) (wt : Rel → List Bool → ℕ) :
    ∃ (count : CSP Rel ℕ → ℕ) (T S : CSP Rel ℕ → ℕ) (e b : ℕ),
      (∀ F : CSP Rel ℕ, (∀ c ∈ F, 1 ≤ c.scope.length ∧ c.scope.length ≤ k) →
        count F = F.partitionFunction wt) ∧
      ComputableInO count (encCSP encRel encNat) encNat T S ∧
      (∀ F, S F = ((encCSP encRel encNat F).length + 1) ^ b) ∧
      ∀ Δ : ℕ, ∃ A : ℕ, ∀ F : CSP Rel ℕ, (∀ v, F.vars.count v ≤ Δ) →
        T F ≤ 2 ^ (A * (F.numVars + 1) / Nat.sqrt (Nat.log 2 (F.numVars + 2))) *
          ((encCSP encRel encNat F).length + 1) ^ e := by
  have hfin : ((fun p : Rel × List Bool => wt p.1 p.2) ''
      (Set.univ ×ˢ {w : List Bool | w.length ≤ k})).Finite :=
    (Set.finite_univ.prod (List.finite_length_le Bool k)).image _
  obtain ⟨W, hW⟩ := hfin.bddAbove
  exact exists_partitionFunctionCounter_boundedDegree encRel k W wt (fun _ _ => of_finite _)
    fun R w hw => hW ⟨(R, w), ⟨Set.mem_univ _, hw⟩, rfl⟩

/-- **Independent sets of bounded-degree graphs.** For each fugacity `t`, one machine computes, on
the encoded hard-core instance `CSP.hardCore n E` of a graph on the vertices `0, …, n - 1` with
edge list `E`, the sum of `t ^ |I|` over the independent sets `I` of the graph (for `t = 1`, their
number), in polynomial space, and for each degree bound `Δ` in time
`2 ^ (A (n + 1) / √⌊log₂ (n + 2)⌋)` times a polynomial in the encoding length on graphs whose
vertices have at most `Δ` incident edges. -/
theorem exists_hardCoreCounter (t : ℕ) :
    ∃ (count : CSP Bool ℕ → ℕ) (T S : CSP Bool ℕ → ℕ) (e b : ℕ),
      (∀ (n : ℕ) (E : List (ℕ × ℕ)), (∀ x ∈ E, x.1 < n ∧ x.2 < n) →
        count (CSP.hardCore n E) =
          ∑ I ∈ (Finset.range n).powerset with ∀ x ∈ E, ¬(x.1 ∈ I ∧ x.2 ∈ I), t ^ I.card) ∧
      ComputableInO count (encCSP encBool encNat) encNat T S ∧
      (∀ F, S F = ((encCSP encBool encNat F).length + 1) ^ b) ∧
      ∀ Δ : ℕ, ∃ A : ℕ, ∀ (n : ℕ) (E : List (ℕ × ℕ)), (∀ x ∈ E, x.1 < n ∧ x.2 < n) →
        (∀ v, (E.flatMap fun x => [x.1, x.2]).count v ≤ Δ) →
        T (CSP.hardCore n E) ≤ 2 ^ (A * (n + 1) / Nat.sqrt (Nat.log 2 (n + 2))) *
          ((encCSP encBool encNat (CSP.hardCore n E)).length + 1) ^ e := by
  obtain ⟨count, T, S, e, b, hcount, hc, hS, hT⟩ :=
    exists_partitionFunctionCounter_of_finite encBool 2 (CSP.hardCoreWeight t)
  refine ⟨count, T, S, e, b, fun n E hE => ?_, hc, hS, fun Δ => ?_⟩
  · rw [hcount _ fun c hc => ?_, CSP.partitionFunction_hardCore t hE]
    simp only [CSP.hardCore, List.mem_append, List.mem_map] at hc
    rcases hc with ⟨v, -, rfl⟩ | ⟨x, -, rfl⟩ <;> simp
  · obtain ⟨A, hA⟩ := hT (Δ + 1)
    refine ⟨A, fun n E hE hΔ => ?_⟩
    have h := hA _ fun v => (CSP.count_vars_hardCore n E v).trans (by have := hΔ v; omega)
    rwa [CSP.numVars_hardCore hE] at h

end Cslib.Complexity.ContractionPartitionFunction
