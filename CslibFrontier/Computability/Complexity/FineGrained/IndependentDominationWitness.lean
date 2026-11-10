/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.FineGrained.GraphWitness
public import CslibFrontier.Computability.Complexity.FineGrained.IndependentDominationInterval
import CslibFrontier.Logics.Propositional.DNF.Relabel
import all CslibFrontier.Computability.PolyTime.CNF.SparseCNFLeafCounter

/-!
# Size-bounded original independent-domination witnesses

The actual signed-bound normalizer, cardinality gate writer and checked native self-reduction
return original selection bits, discarding every recovered gate bit. Negative thresholds,
contradictory bounds, empty graphs and huge binary thresholds use the same proved pipeline.
This is the threshold/witness clause of [ChenJiangZhu2027], Corollary 7.4 / Proposition D.3
and Appendix D.5 (PDF pp.26,36–37), including arbitrary runtime integer size bounds.

## Main results

* `exists_solver_sharp_certificate`, `exists_solver_realEta_certificate`: actual original sets
  within signed input bounds,
  sharp original-vertex native time and global polynomial workspace.
* `Minimum.seek_first`, `Minimum.exists_optimal_search`: actual least-successful size and
  original minimum-word correctness; native composition and closed resource estimates are in
  `CslibFrontier.Computability.Complexity.FineGrained.IndependentDominationMinimumResources`.
* `Minimum.exists_attained_optimal_search`: every finite graph returns an actual optimum word.
* `Signed.exists_decide_sharp_certificate`, `Signed.exists_decide_realEta_certificate`: actual
  Boolean decisions from the size solver tag with the same source resources.
-/

public section

namespace Cslib.Logic.PL.IndependentDominationInterval.Signed.Witness

open Turing.MultiTapeTM Cslib.GenericRAM Cslib.Complexity Cslib.Circuits.Boolean
open GraphWitness

/-- Conventional original independent dominating selection and signed cardinality bounds. -/
@[expose] def Feasible {n : ℕ} (G : SimpleGraph (Fin n)) (lo hi : ℤ) (σ : Fin n → Bool) : Prop :=
  G.IsIndepSet {u | σ u = true} ∧ G.IsDominatingSet {u | σ u = true} ∧
    lo ≤ (Cslib.BitString.weight σ : ℤ) ∧ (Cslib.BitString.weight σ : ℤ) ≤ hi
/-- Actual signed normalization followed by full graph/cardinality CNF writing. -/
@[expose] def construct (x : Signed.Input) : TwoBoundary.BinaryFrontend.Input :=
  IndependentDominationInterval.build (normalize x)
/-- Original declaration read from the original graph, rather than from gate advice. -/
@[expose] def sourceSize (x : Signed.Input) : ℕ := IndependentDomination.order (Signed.graph x)

private theorem construct_polytime : ComputableInPolyTime construct Signed.encInput
    TwoBoundary.BinaryFrontend.encInput :=
  IndependentDominationInterval.build_polytime.comp normalize_polytime

private theorem sourceSize_polytime : ComputableInPolyTime sourceSize Signed.encInput encUnary := by
  unfold sourceSize Signed.graph Signed.encInput IndependentDomination.order
    IndependentDomination.encInput
  fun_prop

/-- Pointwise soundness of the actual cardinality/graph writer on the full recovered word. -/
theorem model_sound {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (lo hi : ℤ)
    (y : ℕ → Bool)
    (hB : (TwoBoundary.BinaryFrontend.side (construct (Signed.ofGraph G lo hi))).eval y = true)
    (hP : ∀ p ∈ TwoBoundary.BinaryFrontend.conditions (construct (Signed.ofGraph G lo hi)),
      DNF.eval y p = true) : Feasible G lo hi (fun u => y u.val) := by
  let low := lowerNat lo hi
  let high := upperNat hi
  let c := CardinalityInterval.circuit n low high
  change (IndependentDomination.exclusions (IndependentDomination.ofGraph G) ++
    CardinalityInterval.formula (n, low, high)).eval y = true at hB
  rw [CNF.eval_append, Bool.and_eq_true] at hB
  have hf := hB.2
  rw [CardinalityInterval.formula, CardinalityInterval.payload_eq] at hf
  have hc : c.eval interpretation (fun u => y u.val) = CardinalityInterval.wanted :=
    ((FunctionalCNF.eval_write_iff c CardinalityInterval.wanted (fun u => y u.val) y
      (fun _ => rfl)).mp hf).2
  have hk := (CardinalityInterval.circuit_accepts n low high (fun u => y u.val)).mp hc
  have hBG := congrArg TwoBoundary.BinaryFrontend.side (IndependentDomination.build_ofGraph G)
  change IndependentDomination.exclusions (IndependentDomination.ofGraph G) =
    CNF.relabel Fin.val (IndependentDomination.finiteExclusions G) at hBG
  have hb : (IndependentDomination.finiteExclusions G).eval (fun u => y u.val) = true := by
    rw [hBG, CNF.eval_relabel] at hB
    exact hB.1
  have hPG := congrArg TwoBoundary.BinaryFrontend.conditions (IndependentDomination.build_ofGraph G)
  change IndependentDomination.coverage (IndependentDomination.ofGraph G) =
    (IndependentDomination.finiteCoverage G).map (CNF.relabel Fin.val) at hPG
  change ∀ p ∈ IndependentDomination.coverage (IndependentDomination.ofGraph G),
    DNF.eval y p = true at hP
  have hp : ∀ p ∈ IndependentDomination.finiteCoverage G, DNF.eval (fun u => y u.val) p = true := by
    intro p hmem
    have ht := hP (CNF.relabel Fin.val p) (by rw [hPG]; exact List.mem_map.mpr ⟨p, hmem, rfl⟩)
    simpa only [DNF.eval_relabel, Function.comp_def] using ht
  obtain ⟨hind, hdom⟩ := (IndependentDomination.finite_semantics G _).mp ⟨hb, hp⟩
  refine ⟨hind, ?_, (bounds_iff lo hi _).mp hk⟩
  rw [SimpleGraph.isDominatingSet_iff]
  simpa only [Set.mem_ofPred_eq, and_comm] using hdom

open Classical in
/-- Actual original selection output. Success is exactly existence within the signed bounds;
every returned word itself encodes such a set. Native resources include normalization, gates,
all self-reduction calls, checking, original-prefix copying and option-tag writing. -/
theorem exists_solver_sharp_certificate :
    ∃ solver : Signed.Input → TwoBoundary.BinaryFrontend.Witness.Output,
      ∃ cs : NativeCertificate solver Signed.encInput TwoBoundary.BinaryFrontend.Witness.encOutput,
      ∃ C e A : ℕ, (∀ x, cs.space x ≤ C * ((Signed.encInput x).length + 1) ^ e) ∧
      ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (lo hi : ℤ),
        ((solver (Signed.ofGraph G lo hi)).isSome = true ↔ ∃ σ, Feasible G lo hi σ) ∧
        (∀ bits, solver (Signed.ofGraph G lo hi) = some bits → bits.length = n ∧
          Feasible G lo hi (fun u => bits.getD u.val false)) ∧
        cs.time (Signed.ofGraph G lo hi) ≤ C *
          ((Signed.encInput (Signed.ofGraph G lo hi)).length + 1) ^ e *
            2 ^ (A * Nat.logLogSqrtLogScale n) := by
  obtain ⟨solver, cs, C, e, A, hs, h⟩ :=
    TwoBoundary.BinaryFrontend.Witness.exists_source_solver_sharp_certificate
      Signed.encInput construct sourceSize construct_polytime sourceSize_polytime 3 1 954 (by omega)
  refine ⟨solver, cs, C, e, A, hs, ?_⟩
  intro n G _ lo hi
  let low := lowerNat lo hi
  let high := upperNat hi
  let a := (CardinalityInterval.circuit n low high).size
  obtain ⟨B, P, hbuild, hb, hp, hplen, hcount⟩ := representation G low high
  have hg : construct (Signed.ofGraph G lo hi) = TwoBoundary.BinaryFrontend.ofFinite B P := hbuild
  have ha : a ≤ 952 * (n + 1) := CardinalityInterval.size_circuit n low high
  have ht := h (Signed.ofGraph G lo hi) B P hg hb hp (by change n ≤ n + a; omega)
    (by rw [hplen]; change (n + a) + n ≤ 954 * (n + 1); omega)
  have hfeas : (∃ y : Fin (n + a) → Bool, B.eval y = true ∧
      ∀ p ∈ P, DNF.eval y p = true) ↔ ∃ σ, Feasible G lo hi σ := by
    have he := congrArg (fun z => 0 < z) hcount
    simp only [Fintype.card_pos_iff, nonempty_subtype] at he
    have hh : (∃ σ : Fin n → Bool, G.IsIndepSet {u | σ u = true} ∧
        (∀ u, σ u = true ∨ ∃ v, G.Adj u v ∧ σ v = true) ∧
          low ≤ Cslib.BitString.weight σ ∧ Cslib.BitString.weight σ ≤ high) ↔
        ∃ σ, Feasible G lo hi σ := by
      apply exists_congr
      intro σ
      rw [show (low ≤ Cslib.BitString.weight σ ∧ Cslib.BitString.weight σ ≤ high) ↔
        (lo ≤ (Cslib.BitString.weight σ : ℤ) ∧
          (Cslib.BitString.weight σ : ℤ) ≤ hi) from bounds_iff _ _ _]
      simp only [Feasible, SimpleGraph.isDominatingSet_iff, Set.mem_ofPred_eq, and_comm]
    exact (Iff.of_eq he).trans hh
  refine ⟨ht.1.trans hfeas, ?_, ?_⟩
  · intro bits heq
    obtain ⟨hlen, full, hfull, hB, hP, hbits⟩ := ht.2.1 bits heq
    have hcheck := (TwoBoundary.BinaryFrontend.Witness.check_ofFinite B P full).mpr ⟨hB, hP⟩
    rw [← hg] at hcheck
    change (CNF.eval (fun i => full.getD i false)
      (TwoBoundary.BinaryFrontend.side (construct (Signed.ofGraph G lo hi))) &&
      (TwoBoundary.BinaryFrontend.conditions (construct (Signed.ofGraph G lo hi))).all
        (DNF.eval (fun i => full.getD i false))) = true at hcheck
    rw [Bool.and_eq_true] at hcheck
    obtain ⟨hside, hpred⟩ := hcheck
    have hm := model_sound G lo hi (fun i => full.getD i false) hside
      (List.all_eq_true.mp hpred)
    have he : (fun u : Fin n => bits.getD u.val false) = fun u => full.getD u.val false := by
      funext u
      rw [hbits]
      change (full.take n).getD u.val false = full.getD u.val false
      simp only [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt u.isLt]
    exact ⟨hlen, he.symm ▸ hm⟩
  · exact ht.2.2

open Classical in
/-- Real source eta wrapper for the same actual signed-bound solver. -/
theorem exists_solver_realEta_certificate :
    ∃ solver : Signed.Input → TwoBoundary.BinaryFrontend.Witness.Output,
      ∃ cs : NativeCertificate solver Signed.encInput TwoBoundary.BinaryFrontend.Witness.encOutput,
      ∃ C e A : ℕ, (∀ x, cs.space x ≤ C * ((Signed.encInput x).length + 1) ^ e) ∧
      ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (lo hi : ℤ),
        ((solver (Signed.ofGraph G lo hi)).isSome = true ↔ ∃ σ, Feasible G lo hi σ) ∧
        (∀ bits, solver (Signed.ofGraph G lo hi) = some bits → bits.length = n ∧
          Feasible G lo hi (fun u => bits.getD u.val false)) ∧
        (16 ≤ n → (cs.time (Signed.ofGraph G lo hi) : ℝ) ≤ (C : ℝ) *
          ((Signed.encInput (Signed.ofGraph G lo hi)).length + 1 : ℕ) ^ e *
            (2 : ℝ) ^ ((A : ℝ) * Real.logLogSqrtLogScale n)) := by
  obtain ⟨solver, cs, C, e, A, hs, h⟩ := exists_solver_sharp_certificate
  refine ⟨solver, cs, C, e, 6 * A, hs, ?_⟩
  intro n G _ lo hi
  refine ⟨(h G lo hi).1, (h G lo hi).2.1, ?_⟩
  intro hn16
  have hR : (cs.time (Signed.ofGraph G lo hi) : ℝ) ≤ (C : ℝ) *
      ((Signed.encInput (Signed.ofGraph G lo hi)).length + 1 : ℕ) ^ e *
        (2 : ℝ) ^ (A * Nat.logLogSqrtLogScale n) := by exact_mod_cast (h G lo hi).2.2
  exact hR.trans (mul_le_mul_of_nonneg_left
    (Nat.two_pow_mul_logLogSqrtLogScale_le A hn16) (by positivity))

end Cslib.Logic.PL.IndependentDominationInterval.Signed.Witness

namespace Cslib.Logic.PL.IndependentDominationInterval.Signed.Witness.Minimum

/-- Actual ascending exact-size search. Retain the first returned original vertex word;
no vertex-set family is enumerated. The recursion makes at most `limit + 1` solver calls. -/
@[expose] def seek (solver : Signed.Input → TwoBoundary.BinaryFrontend.Witness.Output)
    (g : IndependentDomination.Input) : ℕ → Option (ℕ × List Bool)
  | 0 => (solver (g, 0, 0)).map (fun bits => (0, bits))
  | k + 1 => match seek solver g k with
    | some out => some out
    | none => (solver (g, (k + 1 : ℕ), (k + 1 : ℕ))).map (fun bits => (k + 1, bits))

/-- The actual bounded search succeeds exactly when one of its actual size tests succeeds. -/
theorem seek_isSome (solver : Signed.Input → TwoBoundary.BinaryFrontend.Witness.Output)
    (g : IndependentDomination.Input) (limit : ℕ) :
    (seek solver g limit).isSome = true ↔
      ∃ k ≤ limit, (solver (g, (k : ℤ), (k : ℤ))).isSome = true := by
  induction limit with
  | zero => simp [seek]
  | succ k ih =>
    cases h : seek solver g k with
    | none =>
      have hn : ¬ ∃ j ≤ k, (solver (g, (j : ℤ), (j : ℤ))).isSome = true := by
        rw [← ih, h]; simp
      simp only [seek, h, Option.isSome_map]
      constructor
      · intro hs; exact ⟨k + 1, le_rfl, hs⟩
      · rintro ⟨j, hj, hs⟩
        have he : j = k + 1 := by
          by_contra he
          exact hn ⟨j, by omega, hs⟩
        simpa only [he] using hs
    | some out =>
      have he := ih.mp (by rw [h]; rfl)
      simp only [seek, h, Option.isSome_some, true_iff]
      obtain ⟨j, hj, hs⟩ := he
      exact ⟨j, by omega, hs⟩

/-- A returned pair contains the actual successful word at the least successful size. -/
theorem seek_first (solver : Signed.Input → TwoBoundary.BinaryFrontend.Witness.Output)
    (g : IndependentDomination.Input) (limit k : ℕ) (bits : List Bool)
    (h : seek solver g limit = some (k, bits)) :
    k ≤ limit ∧ solver (g, (k : ℤ), (k : ℤ)) = some bits ∧
      ∀ j < k, (solver (g, (j : ℤ), (j : ℤ))).isSome = false := by
  induction limit with
  | zero =>
    simp only [seek, Option.map_eq_some_iff] at h
    obtain ⟨word, hw, he⟩ := h
    cases he
    exact ⟨le_rfl, hw, by omega⟩
  | succ limit ih =>
    cases hp : seek solver g limit with
    | some out =>
      have he : out = (k, bits) := by simpa only [seek, hp, Option.some.injEq] using h
      subst out
      obtain ⟨hk, hw, hj⟩ := ih hp
      exact ⟨by omega, hw, hj⟩
    | none =>
      simp only [seek, hp, Option.map_eq_some_iff] at h
      obtain ⟨word, hw, he⟩ := h
      cases he
      refine ⟨le_rfl, hw, ?_⟩
      intro j hj
      by_contra hn
      have hs : (solver (g, (j : ℤ), (j : ℤ))).isSome = true := by
        cases ht : (solver (g, (j : ℤ), (j : ℤ))).isSome <;> simp_all
      have hh := (seek_isSome solver g limit).mpr ⟨j, by omega, hs⟩
      simp only [hp, Option.isSome_none, Bool.false_eq_true] at hh

/-- Search only the original declaration's possible cardinalities. This writes an actual value
and original word. The companion `IndependentDominationMinimumResources` module supplies
the native composition and closed sharp-time/polynomial-workspace estimates. -/
@[expose] def run (solver : Signed.Input → TwoBoundary.BinaryFrontend.Witness.Output)
    (g : IndependentDomination.Input) : Option (ℕ × List Bool) :=
  seek solver g (IndependentDomination.order g)

open Classical in
/-- Search correctness from a size solver: the returned word attains the least cardinality.
The production instantiations below discharge both solver hypotheses using the proved backend. -/
theorem run_correct (solver : Signed.Input → TwoBoundary.BinaryFrontend.Witness.Output)
    (hyes : ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (lo hi : ℤ),
      (solver (Signed.ofGraph G lo hi)).isSome = true ↔ ∃ σ, Feasible G lo hi σ)
    (hword : ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (lo hi : ℤ) bits,
      solver (Signed.ofGraph G lo hi) = some bits → bits.length = n ∧
        Feasible G lo hi (fun u => bits.getD u.val false)) :
      ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
        ((run solver (IndependentDomination.ofGraph G)).isSome = true ↔
          ∃ σ : Fin n → Bool, G.IsIndepSet {u | σ u = true} ∧
            G.IsDominatingSet {u | σ u = true}) ∧
        ∀ k bits, run solver (IndependentDomination.ofGraph G) = some (k, bits) →
          bits.length = n ∧ Feasible G k k (fun u => bits.getD u.val false) ∧
            ∀ σ : Fin n → Bool, G.IsIndepSet {u | σ u = true} →
              G.IsDominatingSet {u | σ u = true} → k ≤ Cslib.BitString.weight σ := by
  intro n G _
  constructor
  · rw [run, seek_isSome]
    constructor
    · rintro ⟨k, hk, ht⟩
      obtain ⟨σ, hi, hd, _⟩ := ((hyes G k k).mp ht)
      exact ⟨σ, hi, hd⟩
    · rintro ⟨σ, hi, hd⟩
      refine ⟨Cslib.BitString.weight σ, ?_, (hyes G _ _).mpr ⟨σ, hi, hd, le_rfl, le_rfl⟩⟩
      exact Cslib.BitString.weight_le_length σ
  · intro k bits hb
    obtain ⟨hk, hw, hj⟩ := seek_first solver (IndependentDomination.ofGraph G) n k bits hb
    obtain ⟨hlen, hf⟩ := hword G k k bits hw
    refine ⟨hlen, hf, ?_⟩
    intro σ hi hd
    by_contra hn
    have hh := (hyes G (Cslib.BitString.weight σ) (Cslib.BitString.weight σ)).mpr
      ⟨σ, hi, hd, le_rfl, le_rfl⟩
    have hz := hj (Cslib.BitString.weight σ) (by omega)
    change (solver (Signed.ofGraph G _ _)).isSome = false at hz
    rw [hz] at hh
    contradiction

open Classical in
/-- Actual production solver instantiation of minimum search correctness. -/
theorem exists_optimal_search :
    ∃ optimize : IndependentDomination.Input → Option (ℕ × List Bool),
      ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
        ((optimize (IndependentDomination.ofGraph G)).isSome = true ↔
          ∃ σ : Fin n → Bool, G.IsIndepSet {u | σ u = true} ∧
            G.IsDominatingSet {u | σ u = true}) ∧
        ∀ k bits, optimize (IndependentDomination.ofGraph G) = some (k, bits) →
          bits.length = n ∧ Feasible G k k (fun u => bits.getD u.val false) ∧
            ∀ σ : Fin n → Bool, G.IsIndepSet {u | σ u = true} →
              G.IsDominatingSet {u | σ u = true} → k ≤ Cslib.BitString.weight σ := by
  obtain ⟨solver, cs, C, e, A, hs, h⟩ := exists_solver_realEta_certificate
  exact ⟨run solver, run_correct solver (fun G _ lo hi => (h G lo hi).1)
    (fun G _ lo hi => (h G lo hi).2.1)⟩

open Classical in
private theorem exists_independent_dominating {n : ℕ} (G : SimpleGraph (Fin n)) :
    ∃ S : Set (Fin n), G.IsIndepSet S ∧ G.IsDominatingSet S := by
  obtain ⟨S, hi, hm⟩ := exists_maximal_of_wellFoundedGT G.IsIndepSet
    ⟨∅, by rw [G.isIndepSet_iff]; simp⟩
  refine ⟨S, hi, ?_⟩
  rw [SimpleGraph.isDominatingSet_iff]
  intro u
  by_cases hu : u ∈ S
  · exact Or.inl hu
  · right
    by_contra hn
    push Not at hn
    have hit : G.IsIndepSet (insert u S) := by
      rw [G.isIndepSet_iff]
      intro v hv w hw hne
      rcases hv with rfl | hv <;> rcases hw with rfl | hw
      · exact False.elim (hne rfl)
      · exact hn w hw
      · exact fun ha => hn v hv (G.adj_symm ha)
      · exact (G.isIndepSet_iff.mp hi) hv hw hne
    exact hu (hm hit (Set.subset_insert u S) (Set.mem_insert u S))

open Classical in
/-- Every finite graph, including the empty graph, yields an actual globally minimum word.
The size is attained by this output, rather than merely by an existential threshold witness. -/
theorem run_attained (solver : Signed.Input → TwoBoundary.BinaryFrontend.Witness.Output)
    (hyes : ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (lo hi : ℤ),
      (solver (Signed.ofGraph G lo hi)).isSome = true ↔ ∃ σ, Feasible G lo hi σ)
    (hword : ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (lo hi : ℤ) bits,
      solver (Signed.ofGraph G lo hi) = some bits → bits.length = n ∧
        Feasible G lo hi (fun u => bits.getD u.val false)) :
      ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
        ∃ k bits, run solver (IndependentDomination.ofGraph G) = some (k, bits) ∧
          bits.length = n ∧ Feasible G k k (fun u => bits.getD u.val false) ∧
            ∀ σ : Fin n → Bool, G.IsIndepSet {u | σ u = true} →
              G.IsDominatingSet {u | σ u = true} → k ≤ Cslib.BitString.weight σ := by
  intro n G _
  have h := run_correct solver hyes hword G
  obtain ⟨S, hi, hd⟩ := exists_independent_dominating G
  have he : ∃ σ : Fin n → Bool, G.IsIndepSet {u | σ u = true} ∧
      G.IsDominatingSet {u | σ u = true} := by
    refine ⟨fun u => decide (u ∈ S), ?_⟩
    simpa only [decide_eq_true_eq, Set.ofPred_mem_eq] using And.intro hi hd
  have hs := h.1.mpr he
  cases ho : run solver (IndependentDomination.ofGraph G) with
  | none => simp only [ho, Option.isSome_none, Bool.false_eq_true] at hs
  | some out =>
    obtain ⟨k, bits⟩ := out
    exact ⟨k, bits, rfl, h.2 k bits ho⟩

open Classical in
/-- Attained minimum from the actual production solver. -/
theorem exists_attained_optimal_search :
    ∃ optimize : IndependentDomination.Input → Option (ℕ × List Bool),
      ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
        ∃ k bits, optimize (IndependentDomination.ofGraph G) = some (k, bits) ∧
          bits.length = n ∧ Feasible G k k (fun u => bits.getD u.val false) ∧
            ∀ σ : Fin n → Bool, G.IsIndepSet {u | σ u = true} →
              G.IsDominatingSet {u | σ u = true} → k ≤ Cslib.BitString.weight σ := by
  obtain ⟨solver, cs, C, e, A, hs, h⟩ := exists_solver_realEta_certificate
  exact ⟨run solver, run_attained solver (fun G _ lo hi => (h G lo hi).1)
    (fun G _ lo hi => (h G lo hi).2.1)⟩

end Cslib.Logic.PL.IndependentDominationInterval.Signed.Witness.Minimum

namespace Cslib.Logic.PL.IndependentDominationInterval.Signed

open Turing.MultiTapeTM Cslib.GenericRAM Cslib.Complexity

/-- Read the actual size-bounded solver's success tag as a yes/no decision. -/
@[expose] def decideWith (solver : Input → TwoBoundary.BinaryFrontend.Witness.Output)
    (x : Input) : Bool := (solver x).isSome

open Classical in
/-- Actual signed size-bounded independent-domination decision, with the same sharp clock
and global polynomial workspace, including inspection/writing of the answer bit. -/
theorem exists_decide_sharp_certificate :
    ∃ test : Input → Bool, ∃ cs : NativeCertificate test encInput encBool, ∃ C e A : ℕ,
      (∀ x, cs.space x ≤ C * ((encInput x).length + 1) ^ e) ∧
      ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (lo hi : ℤ),
        (test (ofGraph G lo hi) = true ↔ ∃ σ, Witness.Feasible G lo hi σ) ∧
        cs.time (ofGraph G lo hi) ≤ C * ((encInput (ofGraph G lo hi)).length + 1) ^ e *
          2 ^ (A * Nat.logLogSqrtLogScale n) := by
  obtain ⟨solver, cp, D, f, A, hs, h⟩ := Witness.exists_solver_sharp_certificate
  have htag : ComputableInPolyTime
      (fun p : TwoBoundary.BinaryFrontend.Witness.Output => p.isSome)
      TwoBoundary.BinaryFrontend.Witness.encOutput encBool := by
    unfold TwoBoundary.BinaryFrontend.Witness.encOutput; fun_prop
  let post := NativeCertificate.ofPolyTime htag
  let cs := post.comp cp
  have hp := NativeCertificate.ofPolyTime_isPolynomial htag
  have hcp := PolyBounded.of_forall_le D f hs
  have hlen := SparseCNFLeafCounter.polyBounded_output_of_space cp hcp
  have hspace := hcp.add (hp.2.comp hlen)
  let W (x : Input) := D * ((encInput x).length + 1) ^ f + post.time (solver x) + cs.space x
  have hW : PolyBounded (fun x => (encInput x).length) W :=
    (((PolyBounded.const D).mul ((PolyBounded.self.add (.const 1)).pow f)).add
      (hp.1.comp hlen)).add hspace
  obtain ⟨C, e, hCe⟩ := hW.exists_le
  refine ⟨decideWith solver, cs, C, e, A, fun x => (Nat.le_add_left _ _).trans (hCe x), ?_⟩
  intro n G _ lo hi
  refine ⟨(h G lo hi).1, ?_⟩
  let x := ofGraph G lo hi
  let E := 2 ^ (A * Nat.logLogSqrtLogScale n)
  have hE : 0 < E := Nat.two_pow_pos _
  have ht := (h G lo hi).2.2
  have ho := Nat.le_mul_of_pos_right (post.time (solver x)) hE
  have hb : cs.time x ≤ W x * E := by
    change cp.time x + post.time (solver x) ≤ _
    change cp.time x ≤ D * ((encInput x).length + 1) ^ f * E at ht
    dsimp only [W]
    nlinarith
  exact hb.trans (Nat.mul_le_mul_right E (hCe x))

open Classical in
/-- Real source eta for the same actual Boolean decision, with arbitrary signed size bounds. -/
theorem exists_decide_realEta_certificate :
    ∃ test : Input → Bool, ∃ cs : NativeCertificate test encInput encBool, ∃ C e A : ℕ,
      (∀ x, cs.space x ≤ C * ((encInput x).length + 1) ^ e) ∧
      ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (lo hi : ℤ),
        (test (ofGraph G lo hi) = true ↔ ∃ σ, Witness.Feasible G lo hi σ) ∧
        (16 ≤ n → (cs.time (ofGraph G lo hi) : ℝ) ≤ (C : ℝ) *
          ((encInput (ofGraph G lo hi)).length + 1 : ℕ) ^ e *
            (2 : ℝ) ^ ((A : ℝ) * Real.logLogSqrtLogScale n)) := by
  obtain ⟨test, cs, C, e, A, hs, h⟩ := exists_decide_sharp_certificate
  refine ⟨test, cs, C, e, 6 * A, hs, ?_⟩
  intro n G _ lo hi
  refine ⟨(h G lo hi).1, ?_⟩
  intro hn
  have ht : (cs.time (ofGraph G lo hi) : ℝ) ≤ (C : ℝ) *
      ((encInput (ofGraph G lo hi)).length + 1 : ℕ) ^ e *
        (2 : ℝ) ^ (A * Nat.logLogSqrtLogScale n) := by exact_mod_cast (h G lo hi).2
  exact ht.trans (mul_le_mul_of_nonneg_left
    (Nat.two_pow_mul_logLogSqrtLogScale_le A hn) (by positivity))

end Cslib.Logic.PL.IndependentDominationInterval.Signed
