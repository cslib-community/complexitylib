/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Frontier.TensorNetwork.CSPNetworkPolyTime
public import Complexity.Computability.Complexity.FineGrained.ContractionCounting
public import Complexity.Logics.Propositional.CSP.HardCore
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Complexity.Computability.PolyTime.CSP.Vars
import Complexity.Logics.Propositional.CSP.Vars
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
  !F.isEmpty && F.all fun c => decide (1 ≤ c.2.length ∧ c.2.length ≤ k)

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

private theorem certificate_time (F : CSP Rel ℕ) : (certificate encRel k W wt hwt).time F =
    (NativeCertificate.ofPolyTime (computableInPolyTime_guard encRel k)).time F +
      if guard k F then
          (NativeCertificate.ofPolyTime
            (computableInPolyTime_contractionInput encRel k W wt hwt)).time F +
            fastContractionAlgorithm.certificate.time (contractionInput k W wt F)
        else (NativeCertificate.ofPolyTime (computableInPolyTime_fallback encRel)).time F := rfl

private theorem certificate_space (F : CSP Rel ℕ) : (certificate encRel k W wt hwt).space F =
    (NativeCertificate.ofPolyTime (computableInPolyTime_guard encRel k)).space F +
      if guard k F then
          (NativeCertificate.ofPolyTime
            (computableInPolyTime_contractionInput encRel k W wt hwt)).space F +
            fastContractionAlgorithm.certificate.space (contractionInput k W wt F)
        else (NativeCertificate.ofPolyTime (computableInPolyTime_fallback encRel)).space F := rfl

omit encRel hwt

/-! ### Correctness -/

variable {k W wt}

theorem guard_eq_true_iff {F : CSP Rel ℕ} :
    guard k F = true ↔ F ≠ [] ∧ ∀ c ∈ F, 1 ≤ c.2.length ∧ c.2.length ≤ k := by
  simp [guard]

/-- **The machine computes the partition function** of every instance whose constraints have
between one and `k` variables, when the weights at patterns of length at most `k` are at most
`W`. -/
theorem count_eq (hW : ∀ R w, w.length ≤ k → wt R w ≤ W) {F : CSP Rel ℕ}
    (hk : ∀ c ∈ F, 1 ≤ c.2.length ∧ c.2.length ≤ k) :
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
      hW c.1 w (hw ▸ (hk c hc).2)
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
  have hk : ∀ c ∈ F, c.2.length ≤ k := fun c hc => (hcl c hc).2
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
      (∀ F : CSP Rel ℕ, (∀ c ∈ F, 1 ≤ c.2.length ∧ c.2.length ≤ k) →
        count F = F.partitionFunction wt) ∧
      ComputableInO count (encCSP encRel encNat) encNat
        (fun F => 2 ^ (A * (F.vars.length + 1) / Nat.sqrt (Nat.log 2 (F.numVars + 2))) *
          ((encCSP encRel encNat F).length + 1) ^ e)
        (fun F => ((encCSP encRel encNat F).length + 1) ^ b) := by
  obtain ⟨K, hK⟩ := fastContractionAlgorithm.bound (k + 4) (W + 1)
  have hg := NativeCertificate.ofPolyTime_isPolynomial (computableInPolyTime_guard encRel k)
  have hp := NativeCertificate.ofPolyTime_isPolynomial
    (computableInPolyTime_contractionInput encRel k W wt hwt)
  have hf := NativeCertificate.ofPolyTime_isPolynomial (computableInPolyTime_fallback encRel)
  obtain ⟨cg, dg, htg⟩ := hg.1.exists_le
  obtain ⟨cg', dg', hsg⟩ := hg.2.exists_le
  obtain ⟨cp, dp, htp⟩ := hp.1.exists_le
  obtain ⟨cp', dp', hsp⟩ := hp.2.exists_le
  obtain ⟨cf, df, htf⟩ := hf.1.exists_le
  obtain ⟨cf', df', hsf⟩ := hf.2.exists_le
  obtain ⟨p, q, hlen⟩ :=
    (computableInPolyTime_contractionInput encRel k W wt hwt).polyBounded_length.exists_le
  set e := dg + dp + df + q * K
  set b := dg' + dp' + df' + q * K
  refine ⟨count k W wt, 3 * K, e, b, fun F hk => count_eq hW hk,
    (certificate encRel k W wt hwt).computes.mono
      (cg + cp + cf + K * (p + 1) ^ K + cg' + cp' + cf' + 1) (fun F => ?_) (fun F => ?_)⟩
  all_goals
    set Y := (encCSP encRel encNat F).length + 1 with hY
    have hY1 : 1 ≤ Y := Nat.le_add_left 1 _
    have hpow {d d' : ℕ} (h : d ≤ d') : Y ^ d ≤ Y ^ d' := Nat.pow_le_pow_right hY1 h
    have hn' : ((encPair encNat (encPair encNat ExplicitTensorNetwork.encExplicitNetwork))
        (contractionInput k W wt F)).length + 1 ≤ (p + 1) * Y ^ q := by
      have h1 := hlen F
      have h2 : 1 ≤ Y ^ q := Nat.one_le_pow _ _ hY1
      rw [← hY] at h1
      nlinarith
    have hn'K : (((encPair encNat (encPair encNat ExplicitTensorNetwork.encExplicitNetwork))
        (contractionInput k W wt F)).length + 1) ^ K ≤ (p + 1) ^ K * Y ^ (q * K) := by
      calc _ ≤ ((p + 1) * Y ^ q) ^ K := Nat.pow_le_pow_left hn' K
        _ = _ := by rw [mul_pow, pow_mul]
  · -- time
    set E := 3 * K * (F.vars.length + 1) / Nat.sqrt (Nat.log 2 (F.numVars + 2))
    have h2E : 1 ≤ 2 ^ E := Nat.one_le_two_pow
    set Z := 2 ^ E * Y ^ e
    have hZ {d : ℕ} (h : d ≤ e) : Y ^ d ≤ Z :=
      (hpow h).trans (Nat.le_mul_of_pos_left _ h2E)
    have htg' : (NativeCertificate.ofPolyTime (computableInPolyTime_guard encRel k)).time F ≤
        cg * Z := (htg F).trans (Nat.mul_le_mul_left _ (hZ (by omega)))
    have htp' : (NativeCertificate.ofPolyTime
        (computableInPolyTime_contractionInput encRel k W wt hwt)).time F ≤ cp * Z :=
      (htp F).trans (Nat.mul_le_mul_left _ (hZ (by omega)))
    have htf' : (NativeCertificate.ofPolyTime (computableInPolyTime_fallback encRel)).time F ≤
        cf * Z := (htf F).trans (Nat.mul_le_mul_left _ (hZ (by omega)))
    have htc : guard k F = true →
        fastContractionAlgorithm.certificate.time (contractionInput k W wt F) ≤
          K * (p + 1) ^ K * Z := by
      intro hgF
      obtain ⟨hne, hcl⟩ := guard_eq_true_iff.mp hgF
      have h1 : 1 ≤ F.length := List.length_pos_iff.mpr hne
      have hm := CSP.length_le_length_vars fun c hc => (hcl c hc).1
      have hnN : F.numVars ≤ F.vars.length := List.toFinset_card_le _
      have hb := (hK (3 * F.vars.length) (precision W F) (cspNetwork k wt F) (by omega)
        (by rw [precision]; nlinarith) (by rw [precision])
        (explicitAdmissible_cspNetwork hgF)).1
      have hexp := ContractionCounting.exponent_le (K := K) (k := 1) (m := F.vars.length)
        (by omega) (by omega) hnN
      rw [Nat.mul_one] at hexp
      calc fastContractionAlgorithm.certificate.time (contractionInput k W wt F)
          ≤ K * ((p + 1) ^ K * Y ^ (q * K)) * 2 ^ E := by
            refine hb.trans ?_
            exact Nat.mul_le_mul (Nat.mul_le_mul_left _ hn'K)
              (Nat.pow_le_pow_right (by norm_num) hexp)
        _ ≤ K * (p + 1) ^ K * Z := by
            have := hpow (show q * K ≤ e by omega)
            calc K * ((p + 1) ^ K * Y ^ (q * K)) * 2 ^ E
                = K * (p + 1) ^ K * (2 ^ E * Y ^ (q * K)) := by ring
              _ ≤ K * (p + 1) ^ K * Z := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ this)
    rw [certificate_time]
    generalize hKP : K * (p + 1) ^ K = KP at htc
    have hC : ∀ c, c ≤ cg + cp + cf + KP + cg' + cp' + cf' + 1 →
        c * Z ≤ (cg + cp + cf + KP + cg' + cp' + cf' + 1) * (Z + 1) := fun c hc =>
      (Nat.mul_le_mul_right _ hc).trans (Nat.mul_le_mul_left _ (Nat.le_succ _))
    split
    · next hgF =>
      calc _ ≤ cg * Z + (cp * Z + KP * Z) := Nat.add_le_add htg' (Nat.add_le_add htp' (htc hgF))
        _ = (cg + cp + KP) * Z := by ring
        _ ≤ _ := hC _ (by omega)
    · calc _ ≤ cg * Z + cf * Z := Nat.add_le_add htg' htf'
        _ = (cg + cf) * Z := by ring
        _ ≤ _ := hC _ (by omega)
  · -- space
    have hsg' : (NativeCertificate.ofPolyTime (computableInPolyTime_guard encRel k)).space F ≤
        cg' * Y ^ b := (hsg F).trans (Nat.mul_le_mul_left _ (hpow (by omega)))
    have hsp' : (NativeCertificate.ofPolyTime
        (computableInPolyTime_contractionInput encRel k W wt hwt)).space F ≤ cp' * Y ^ b :=
      (hsp F).trans (Nat.mul_le_mul_left _ (hpow (by omega)))
    have hsf' : (NativeCertificate.ofPolyTime (computableInPolyTime_fallback encRel)).space F ≤
        cf' * Y ^ b := (hsf F).trans (Nat.mul_le_mul_left _ (hpow (by omega)))
    have hsc : guard k F = true →
        fastContractionAlgorithm.certificate.space (contractionInput k W wt F) ≤
          K * (p + 1) ^ K * Y ^ b := by
      intro hgF
      obtain ⟨hne, hcl⟩ := guard_eq_true_iff.mp hgF
      have h1 : 1 ≤ F.length := List.length_pos_iff.mpr hne
      have hm := CSP.length_le_length_vars fun c hc => (hcl c hc).1
      have hb := (hK (3 * F.vars.length) (precision W F) (cspNetwork k wt F) (by omega)
        (by rw [precision]; nlinarith) (by rw [precision])
        (explicitAdmissible_cspNetwork hgF)).2
      refine hb.trans ?_
      calc K * _ ≤ K * ((p + 1) ^ K * Y ^ (q * K)) := Nat.mul_le_mul_left _ hn'K
        _ ≤ K * (p + 1) ^ K * Y ^ b := by
            rw [← Nat.mul_assoc]
            exact Nat.mul_le_mul_left _ (hpow (by omega))
    rw [certificate_space]
    generalize hKP : K * (p + 1) ^ K = KP at hsc
    have hC : ∀ c, c ≤ cg + cp + cf + KP + cg' + cp' + cf' + 1 →
        c * Y ^ b ≤ (cg + cp + cf + KP + cg' + cp' + cf' + 1) * (Y ^ b + 1) := fun c hc =>
      (Nat.mul_le_mul_right _ hc).trans (Nat.mul_le_mul_left _ (Nat.le_succ _))
    split
    · next hgF =>
      calc _ ≤ cg' * Y ^ b + (cp' * Y ^ b + KP * Y ^ b) :=
            Nat.add_le_add hsg' (Nat.add_le_add hsp' (hsc hgF))
        _ = (cg' + cp' + KP) * Y ^ b := by ring
        _ ≤ _ := hC _ (by omega)
    · calc _ ≤ cg' * Y ^ b + cf' * Y ^ b := Nat.add_le_add hsg' hsf'
        _ = (cg' + cf') * Y ^ b := by ring
        _ ≤ _ := hC _ (by omega)

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
      (∀ F : CSP Rel ℕ, (∀ c ∈ F, 1 ≤ c.2.length ∧ c.2.length ≤ k) →
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
      (∀ F : CSP Rel ℕ, (∀ c ∈ F, 1 ≤ c.2.length ∧ c.2.length ≤ k) →
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
