/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.FineGrained.TwoBoundarySourceSolver
public import CslibFrontier.Computability.PolyTime.CNF.IndependentDominationInterval
public import CslibFrontier.Computability.PolyTime.CNF.DigraphKernel
public import CslibFrontier.Computability.PolyTime.CNF.PerfectMatchingCut
public import CslibFrontier.Computability.PolyTime.CNF.DominatingInducedMatching
public import CslibFrontier.Foundations.Combinatorics.SimpleGraph.DominatingSet
import CslibFrontier.Logics.Propositional.DNF.Relabel

/-!
# Actual graph solutions from checked native self-reduction

Returned words are original vertex selections or side labels, never existential witnesses or
supplied solutions. Every constructor and native resource premise of the shared solver is
instantiated with the actual proved graph writer. The source is [ChenJiangZhu2027], Corollary 7.4
and Appendix D.5 (PDF pp.26,37). Canonical explicit matrices/unary declarations are unchanged.

## Main definitions

* `GraphWitness.selected`, `GraphWitness.decodeMatching`: original-set/subgraph decoding.
* `PerfectMatchingCut.Witness.construct`: actual empty-input rejection before recovery.

## Main results

* `IndependentDomination.Witness.exists_solver_realEta_certificate`.
* `DigraphKernel.Witness.exists_solver_realEta_certificate`.
* `PerfectMatchingCut.Witness.exists_solver_realEta_certificate`.
* `DominatingInducedMatching.Witness.exists_solver_realEta_certificate`.
-/

public section

namespace Cslib.Logic.PL

open Turing.MultiTapeTM Cslib.GenericRAM Cslib.Complexity

namespace GraphWitness

/-- Original vertices selected by the actual returned word. -/
@[expose] def selected {n : ℕ} (bits : List Bool) : Set (Fin n) :=
  {u | bits.getD u.val false = true}
/-- Conventional induced original subgraph decoded from the returned endpoint word. -/
@[expose] def decodeMatching {n : ℕ} (G : SimpleGraph (Fin n)) (bits : List Bool) : G.Subgraph :=
  (⊤ : G.Subgraph).induce (selected bits)

end GraphWitness

namespace IndependentDomination.Witness

open GraphWitness

open Classical in
/-- Actual original-vertex independent dominating sets, with failure exactly on infeasibility
and complete native sharp time/global polynomial workspace. This no-size interface does not
alone implement the size-threshold or optimum clauses. -/
theorem exists_solver_realEta_certificate :
    ∃ solver : Input → TwoBoundary.BinaryFrontend.Witness.Output,
      ∃ cs : NativeCertificate solver encInput TwoBoundary.BinaryFrontend.Witness.encOutput,
      ∃ C e A : ℕ, (∀ x, cs.space x ≤ C * ((encInput x).length + 1) ^ e) ∧
      ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
        ((solver (ofGraph G)).isSome = true ↔ ∃ σ : Fin n → Bool,
          G.IsIndepSet {u | σ u = true} ∧ G.IsDominatingSet {u | σ u = true}) ∧
        (∀ bits, solver (ofGraph G) = some bits → bits.length = n ∧
          G.IsIndepSet (selected bits) ∧ G.IsDominatingSet (selected bits)) ∧
        (16 ≤ n → (cs.time (ofGraph G) : ℝ) ≤ (C : ℝ) *
          ((encInput (ofGraph G)).length + 1 : ℕ) ^ e *
            (2 : ℝ) ^ ((A : ℝ) * Real.logLogSqrtLogScale n)) := by
  have hn : ComputableInPolyTime order encInput encUnary := by unfold order encInput; fun_prop
  obtain ⟨solver, cs, C, e, A, hs, h⟩ :=
    TwoBoundary.BinaryFrontend.Witness.exists_source_solver_sharp_certificate
      encInput build order build_polytime hn 3 1 2 (by omega)
  refine ⟨solver, cs, C, e, 6 * A, hs, ?_⟩
  intro n G _
  obtain ⟨hb, hp⟩ := widths G
  have ht := h (ofGraph G) (finiteExclusions G) (finiteCoverage G) (build_ofGraph G)
    (fun q hq => (hb q hq).trans (by omega)) hp (by rfl)
      (by rw [finiteCoverage_length]; change n + n ≤ 2 * (n + 1); omega)
  have hsem (σ : Fin n → Bool) :
      (finiteExclusions G).eval σ = true ∧ (∀ p ∈ finiteCoverage G, DNF.eval σ p = true) ↔
        G.IsIndepSet {u | σ u = true} ∧ G.IsDominatingSet {u | σ u = true} := by
    rw [finite_semantics, SimpleGraph.isDominatingSet_iff]
    simp only [Set.mem_ofPred_eq, and_comm]
  refine ⟨ht.1.trans (exists_congr hsem), ?_, ?_⟩
  · intro bits heq
    obtain ⟨hl, full, hfl, hB, hP, hbts⟩ := ht.2.1 bits heq
    have he : bits = full := by simpa only [show order (ofGraph G) = n from rfl,
      ← hfl, List.take_length] using hbts
    refine ⟨hl, ?_⟩
    rw [he]
    exact (hsem _).mp ⟨hB, hP⟩
  · intro hn16
    have hR : (cs.time (ofGraph G) : ℝ) ≤ (C : ℝ) *
        ((encInput (ofGraph G)).length + 1 : ℕ) ^ e *
          (2 : ℝ) ^ (A * Nat.logLogSqrtLogScale n) := by exact_mod_cast ht.2.2
    exact hR.trans (mul_le_mul_of_nonneg_left
      (Nat.two_pow_mul_logLogSqrtLogScale_le A hn16) (by positivity))

end IndependentDomination.Witness

namespace DigraphKernel.Witness

open IndependentDomination GraphWitness

open Classical in
/-- Checked original absorbing kernels, retaining arc orientation. No kernel is fabricated on
NO-instances; the empty digraph returns the empty set. The theorem also permits loops, while
the source Corollary 7.4 specializes to loopless digraphs. -/
theorem exists_solver_realEta_certificate :
    ∃ solver : Input → TwoBoundary.BinaryFrontend.Witness.Output,
      ∃ cs : NativeCertificate solver encInput TwoBoundary.BinaryFrontend.Witness.encOutput,
      ∃ C e A : ℕ, (∀ x, cs.space x ≤ C * ((encInput x).length + 1) ^ e) ∧
      ∀ {n : ℕ} (G : Digraph (Fin n)) [DecidableRel G.Adj],
        ((solver (ofDigraph G)).isSome = true ↔ ∃ S : Set (Fin n), G.IsKernel S) ∧
        (∀ bits, solver (ofDigraph G) = some bits → bits.length = n ∧ G.IsKernel (selected bits)) ∧
        (16 ≤ n → (cs.time (ofDigraph G) : ℝ) ≤ (C : ℝ) *
          ((encInput (ofDigraph G)).length + 1 : ℕ) ^ e *
            (2 : ℝ) ^ ((A : ℝ) * Real.logLogSqrtLogScale n)) := by
  have hn : ComputableInPolyTime order encInput encUnary := by unfold order encInput; fun_prop
  obtain ⟨solver, cs, C, e, A, hs, h⟩ :=
    TwoBoundary.BinaryFrontend.Witness.exists_source_solver_sharp_certificate
      encInput build order build_polytime hn 3 1 2 (by omega)
  refine ⟨solver, cs, C, e, 6 * A, hs, ?_⟩
  intro n G _
  obtain ⟨hb, hp⟩ := DigraphKernel.widths G
  have ht := h (ofDigraph G) (finiteExclusions G) (finiteCoverage G) (build_ofDigraph G)
    (fun q hq => (hb q hq).trans (by omega)) hp (by rfl)
      (by rw [finiteCoverage_length]; change n + n ≤ 2 * (n + 1); omega)
  have he : (∃ σ : Fin n → Bool, G.IsKernel {u | σ u = true}) ↔
      ∃ S : Set (Fin n), G.IsKernel S := by
    constructor
    · rintro ⟨σ, hσ⟩; exact ⟨_, hσ⟩
    · rintro ⟨S, hS⟩
      refine ⟨fun u => decide (u ∈ S), ?_⟩
      simpa only [decide_eq_true_eq, Set.ofPred_mem_eq] using hS
  refine ⟨ht.1.trans ((exists_congr (finite_semantics G)).trans he), ?_, ?_⟩
  · intro bits heq
    obtain ⟨hl, full, hfl, hB, hP, hbts⟩ := ht.2.1 bits heq
    have he : bits = full := by simpa only [show order (ofDigraph G) = n from rfl,
      ← hfl, List.take_length] using hbts
    refine ⟨hl, ?_⟩
    rw [he]
    exact (finite_semantics G _).mp ⟨hB, hP⟩
  · intro hn16
    have hR : (cs.time (ofDigraph G) : ℝ) ≤ (C : ℝ) *
        ((encInput (ofDigraph G)).length + 1 : ℕ) ^ e *
          (2 : ℝ) ^ (A * Nat.logLogSqrtLogScale n) := by exact_mod_cast ht.2.2
    exact hR.trans (mul_le_mul_of_nonneg_left
      (Nat.two_pow_mul_logLogSqrtLogScale_le A hn16) (by positivity))

end DigraphKernel.Witness

namespace PerfectMatchingCut.Witness

open IndependentDomination GraphWitness

/-- The actual empty graph rejection is encoded before the generic checked solver runs. -/
@[expose] def construct (x : Input) : TwoBoundary.BinaryFrontend.Input :=
  if isEmpty x then (0, [[]], []) else build x

private theorem construct_polytime : ComputableInPolyTime construct encInput
    TwoBoundary.BinaryFrontend.encInput :=
  isEmpty_polytime.ite' (.const (0, [[]], [])) build_polytime

/-- Finite bounded clauses with the actual empty rejection, for source correspondence. -/
@[expose] def solverSide {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : CNF (Fin n) :=
  if n = 0 then [[]] else finiteUpper G
/-- Finite predicates, with no vacuous empty cut admitted. -/
@[expose] def solverConditions {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    List (DNF (Fin n)) := if n = 0 then [] else finiteConditions G

private theorem construct_ofGraph {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    construct (ofGraph G) =
      TwoBoundary.BinaryFrontend.ofFinite (solverSide G) (solverConditions G) := by
  by_cases hn : n = 0
  · subst n
    simp [construct, isEmpty, order, ofGraph, solverSide, solverConditions,
      TwoBoundary.BinaryFrontend.ofFinite, CNF.relabel, Clause.relabel]
  · simp only [construct, isEmpty, order, ofGraph, hn, decide_false, Bool.false_eq_true, ite_false,
      solverSide, solverConditions]
    exact build_ofGraph G

private theorem solver_semantics {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (σ : Fin n → Bool) :
    (solverSide G).eval σ = true ∧ (∀ p ∈ solverConditions G, DNF.eval σ p = true) ↔
      G.IsPerfectMatchingCut σ := by
  by_cases hn : n = 0
  · subst n
    simp [solverSide, solverConditions, CNF.eval, Clause.eval, SimpleGraph.IsPerfectMatchingCut]
  · simpa only [solverSide, solverConditions, hn, ite_false] using finite_semantics G (by omega) σ

open Classical in
/-- The returned original side labels themselves form a perfect matching cut. Both classes are
nonempty; the empty graph and infeasible graphs return none, without an assumed decoder. -/
theorem exists_solver_realEta_certificate :
    ∃ solver : Input → TwoBoundary.BinaryFrontend.Witness.Output,
      ∃ cs : NativeCertificate solver encInput TwoBoundary.BinaryFrontend.Witness.encOutput,
      ∃ C e A : ℕ, (∀ x, cs.space x ≤ C * ((encInput x).length + 1) ^ e) ∧
      ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
        ((solver (ofGraph G)).isSome = true ↔ ∃ σ : Fin n → Bool, G.IsPerfectMatchingCut σ) ∧
        (∀ bits, solver (ofGraph G) = some bits → bits.length = n ∧
          G.IsPerfectMatchingCut (fun u => bits.getD u.val false)) ∧
        (16 ≤ n → (cs.time (ofGraph G) : ℝ) ≤ (C : ℝ) *
          ((encInput (ofGraph G)).length + 1 : ℕ) ^ e *
            (2 : ℝ) ^ ((A : ℝ) * Real.logLogSqrtLogScale n)) := by
  have hn : ComputableInPolyTime order encInput encUnary := by unfold order encInput; fun_prop
  obtain ⟨solver, cs, C, e, A, hs, h⟩ :=
    TwoBoundary.BinaryFrontend.Witness.exists_source_solver_sharp_certificate
      encInput construct order construct_polytime hn 3 1 3 (by omega)
  refine ⟨solver, cs, C, e, 6 * A, hs, ?_⟩
  intro n G _
  have hw := widths G
  have hb : ∀ q ∈ solverSide G, q.length ≤ 3 := by
    by_cases hz : n = 0
    · simp [solverSide, hz]
    · simpa only [solverSide, hz, ite_false] using hw.1
  have hp : ∀ p ∈ solverConditions G, ∀ t ∈ p, t.length ≤ 1 := by
    by_cases hz : n = 0
    · simp [solverConditions, hz]
    · simpa only [solverConditions, hz, ite_false] using hw.2
  have hdim : n + (solverConditions G).length ≤ 3 * (n + 1) := by
    by_cases hz : n = 0
    · simp [solverConditions, hz]
    · simp only [solverConditions, hz, ite_false, finiteConditions_length]; omega
  have ht := h (ofGraph G) (solverSide G) (solverConditions G) (construct_ofGraph G)
    hb hp (by rfl) hdim
  refine ⟨ht.1.trans (exists_congr (solver_semantics G)), ?_, ?_⟩
  · intro bits heq
    obtain ⟨hl, full, hfl, hB, hP, hbts⟩ := ht.2.1 bits heq
    have he : bits = full := by simpa only [show order (ofGraph G) = n from rfl,
      ← hfl, List.take_length] using hbts
    refine ⟨hl, ?_⟩
    rw [he]
    exact (solver_semantics G _).mp ⟨hB, hP⟩
  · intro hn16
    have hR : (cs.time (ofGraph G) : ℝ) ≤ (C : ℝ) *
        ((encInput (ofGraph G)).length + 1 : ℕ) ^ e *
          (2 : ℝ) ^ (A * Nat.logLogSqrtLogScale n) := by exact_mod_cast ht.2.2
    exact hR.trans (mul_le_mul_of_nonneg_left
      (Nat.two_pow_mul_logLogSqrtLogScale_le A hn16) (by positivity))

end PerfectMatchingCut.Witness

namespace DominatingInducedMatching.Witness

open IndependentDomination GraphWitness

/-- The decoded subgraph is a conventional efficient edge-dominating matching. -/
theorem decode_sound {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (bits : List Bool)
    (h : ((finiteUpper G ++ finiteCover G).eval (fun u => bits.getD u.val false) = true ∧
      ∀ p ∈ finiteConditions G, DNF.eval (fun u => bits.getD u.val false) p = true)) :
    (decodeMatching G bits).IsDominatingInducedMatching := by
  obtain ⟨hm, hc⟩ := (finite_semantics G _).mp h
  apply (SimpleGraph.Subgraph.isDominatingInducedMatching_iff _).mpr
  exact ⟨hm, (SimpleGraph.Subgraph.isInduced_iff_exists_eq_induce_top _).mpr ⟨_, rfl⟩, hc⟩

open Classical in
/-- Returned original endpoint bits decode to an actual matching dominating each edge exactly
once. This includes edgeless and empty graphs, and returns none precisely on infeasible inputs. -/
theorem exists_solver_realEta_certificate :
    ∃ solver : Input → TwoBoundary.BinaryFrontend.Witness.Output,
      ∃ cs : NativeCertificate solver encInput TwoBoundary.BinaryFrontend.Witness.encOutput,
      ∃ C e A : ℕ, (∀ x, cs.space x ≤ C * ((encInput x).length + 1) ^ e) ∧
      ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
        ((solver (ofGraph G)).isSome = true ↔
          ∃ M : G.Subgraph, M.IsDominatingInducedMatching) ∧
        (∀ bits, solver (ofGraph G) = some bits → bits.length = n ∧
          (decodeMatching G bits).IsDominatingInducedMatching) ∧
        (16 ≤ n → (cs.time (ofGraph G) : ℝ) ≤ (C : ℝ) *
          ((encInput (ofGraph G)).length + 1 : ℕ) ^ e *
            (2 : ℝ) ^ ((A : ℝ) * Real.logLogSqrtLogScale n)) := by
  have hn : ComputableInPolyTime order encInput encUnary := by unfold order encInput; fun_prop
  obtain ⟨solver, cs, C, e, A, hs, h⟩ :=
    TwoBoundary.BinaryFrontend.Witness.exists_source_solver_sharp_certificate
      encInput build order build_polytime hn 3 1 2 (by omega)
  refine ⟨solver, cs, C, e, 6 * A, hs, ?_⟩
  intro n G _
  obtain ⟨hb, hp⟩ := widths G
  have ht := h (ofGraph G) (finiteUpper G ++ finiteCover G) (finiteConditions G)
    (build_ofGraph G) hb hp (by rfl)
      (by rw [finiteConditions_length]; change n + n ≤ 2 * (n + 1); omega)
  have hex : (∃ σ : Fin n → Bool,
      ((⊤ : G.Subgraph).induce {u | σ u = true}).IsMatching ∧
        ∀ u v, G.Adj u v → σ u = true ∨ σ v = true) ↔
      ∃ M : G.Subgraph, M.IsDominatingInducedMatching := by
    have hc := SimpleGraph.card_dominatingMatching_supports_eq (G := G)
    have he := congrArg (fun a => 0 < a) hc
    simpa only [Nat.card_eq_fintype_card, Fintype.card_pos_iff, nonempty_subtype] using Iff.of_eq he
  refine ⟨ht.1.trans ((exists_congr (finite_semantics G)).trans hex), ?_, ?_⟩
  · intro bits heq
    obtain ⟨hl, full, hfl, hB, hP, hbts⟩ := ht.2.1 bits heq
    have he : bits = full := by simpa only [show order (ofGraph G) = n from rfl,
      ← hfl, List.take_length] using hbts
    refine ⟨hl, ?_⟩
    rw [he]
    exact decode_sound G _ ⟨hB, hP⟩
  · intro hn16
    have hR : (cs.time (ofGraph G) : ℝ) ≤ (C : ℝ) *
        ((encInput (ofGraph G)).length + 1 : ℕ) ^ e *
          (2 : ℝ) ^ (A * Nat.logLogSqrtLogScale n) := by exact_mod_cast ht.2.2
    exact hR.trans (mul_le_mul_of_nonneg_left
      (Nat.two_pow_mul_logLogSqrtLogScale_le A hn16) (by positivity))

end DominatingInducedMatching.Witness

end Cslib.Logic.PL
