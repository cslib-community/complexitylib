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

/-!
# Size-bounded original independent-domination witnesses

The actual signed-bound normalizer, cardinality gate writer and checked native self-reduction
return original selection bits, discarding every recovered gate bit. Negative thresholds,
contradictory bounds, empty graphs and huge binary thresholds use the same proved pipeline.
This is the threshold/witness clause of [ChenJiangZhu2027], Corollary 7.4 / Proposition D.3
and Appendix D.5 (PDF pp.26,36–37), including arbitrary runtime integer size bounds.

## Main results

* `exists_solver_realEta_certificate`: actual original sets within signed input bounds,
  sharp original-vertex native time and global polynomial workspace.
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
  obtain ⟨solver, cs, C, e, A, hs, h⟩ :=
    TwoBoundary.BinaryFrontend.Witness.exists_source_solver_sharp_certificate
      Signed.encInput construct sourceSize construct_polytime sourceSize_polytime 3 1 954 (by omega)
  refine ⟨solver, cs, C, e, 6 * A, hs, ?_⟩
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
  · intro hn16
    have hR : (cs.time (Signed.ofGraph G lo hi) : ℝ) ≤ (C : ℝ) *
        ((Signed.encInput (Signed.ofGraph G lo hi)).length + 1 : ℕ) ^ e *
          (2 : ℝ) ^ (A * Nat.logLogSqrtLogScale n) := by exact_mod_cast ht.2.2
    exact hR.trans (mul_le_mul_of_nonneg_left
      (Nat.two_pow_mul_logLogSqrtLogScale_le A hn16) (by positivity))

end Cslib.Logic.PL.IndependentDominationInterval.Signed.Witness
