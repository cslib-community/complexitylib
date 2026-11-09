/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.FineGrained.UpperDomination
public import CslibFrontier.Computability.Complexity.FineGrained.InducedMatchingOptimum
import all CslibFrontier.Computability.Complexity.FineGrained.InducedMatchingOptimum

/-!
# Actual maximum cardinality of a minimal dominating set

Reuse the existing bounded original-graph threshold traversal with the proved Upper Dominating
Set decider. The returned value is attained by an inclusion-minimal dominating set and bounds
all such sets. This is the optimum-threshold clause of [ChenJiangZhu2027], Corollary 7.4 /
Appendix D.5 (PDF pp.26,37). A polynomial scan replaces binary search with the same sharp bound.
This returns the original set cardinality, not a number of private-neighbor markings. Witness
output and the unique-mark refinements of Proposition 7.6 remain separate clauses.

## Main definitions

* `run`: actual bounded original-vertex threshold traversal.

## Main results

* `run_optimal`: the computed value is attained and globally optimal.
* `exists_optimum_realEta_certificate`: complete original-graph sharp time and polynomial space.
-/

public section

namespace Cslib.Logic.PL.UpperDomination.Optimum

open Turing.MultiTapeTM Cslib.GenericRAM Cslib.Complexity
open InducedMatchingInterval.Maximum.Optimum

/-- Scan original vertex-cardinality thresholds using the existing bounded graph-state iterator.
No family of sets or markings is enumerated, and no optimum is input advice. -/
@[expose] def run (test : UpperDomination.Input → Bool)
    (g : IndependentDomination.Input) : ℕ :=
  best ((step test)^[rounds g] (initial g))

open Classical in
/-- The actual scan returns an attained global maximum among inclusion-minimal dominating sets.
Its test premise is discharged by the actual native decider in the complete resource theorem. -/
theorem run_optimal (test : UpperDomination.Input → Bool) {n : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (htest : ∀ k : ℤ, test (ofGraph G k) = true ↔
      ∃ S : Set (Fin n), Minimal G.IsDominatingSet S ∧ k ≤ (Nat.card S : ℤ)) :
    (∃ S : Set (Fin n), Minimal G.IsDominatingSet S ∧
      Nat.card S = run test (IndependentDomination.ofGraph G)) ∧
      ∀ S : Set (Fin n), Minimal G.IsDominatingSet S →
        Nat.card S ≤ run test (IndependentDomination.ofGraph G) := by
  have hex : ∃ S : Set (Fin n), G.IsDominatingSet S :=
    ⟨Set.univ, fun w => ⟨w, Set.mem_univ _, Or.inl rfl⟩⟩
  obtain ⟨S, hS⟩ := exists_minimal_of_wellFoundedLT G.IsDominatingSet hex
  have he : test (ofGraph G 0) = true := (htest 0).mpr ⟨S, hS, by omega⟩
  have hs := scan_spec test (IndependentDomination.ofGraph G) he (n + 1)
  have hub (T : Set (Fin n)) : Nat.card T ≤ n := by
    have h := Nat.card_le_card_of_injective (Subtype.val : T → Fin n) Subtype.val_injective
    simpa only [Nat.card_fin] using h
  have hbound (T : Set (Fin n)) (hm : Minimal G.IsDominatingSet T) :
      Nat.card T ≤ run test (IndependentDomination.ofGraph G) := by
    apply hs.2 _ (by have := hub T; omega)
    exact (htest _).mpr ⟨T, hm, by omega⟩
  refine ⟨?_, hbound⟩
  obtain ⟨T, hm, hsize⟩ := (htest _).mp hs.1
  exact ⟨T, hm, Nat.le_antisymm (hbound T hm) (Int.ofNat_le.mp hsize)⟩

open Classical in
/-- One actual original-matrix optimizer outputs an attained maximum minimal-dominating-set size.
Its certificate charges every threshold query, loop update and final binary output, with global
polynomial workspace and the source single-loglog time. No optimum or call budget is supplied. -/
theorem exists_optimum_sharp_certificate :
    ∃ optimum : IndependentDomination.Input → ℕ,
      ∃ cs : NativeCertificate optimum IndependentDomination.encInput encNat, ∃ C e A : ℕ,
        (∀ g, cs.space g ≤ C * ((IndependentDomination.encInput g).length + 1) ^ e) ∧
        ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
          ((∃ S : Set (Fin n), Minimal G.IsDominatingSet S ∧
            Nat.card S = optimum (IndependentDomination.ofGraph G)) ∧
            ∀ S : Set (Fin n), Minimal G.IsDominatingSet S →
              Nat.card S ≤ optimum (IndependentDomination.ofGraph G)) ∧
          cs.time (IndependentDomination.ofGraph G) ≤
            C * ((IndependentDomination.encInput (IndependentDomination.ofGraph G)).length + 1) ^
              e *
              2 ^ (A * Nat.logLogSqrtLogScale n) := by
  obtain ⟨test, cp, D, f, A, hs, ht⟩ := UpperDomination.exists_decide_sharp_certificate
  let cq := NativeCertificate.ofPolyTime query_polytime
  let cy := NativeCertificate.ofPolyTime yes_polytime
  let cz := NativeCertificate.ofPolyTime no_polytime
  let ct := cp.comp cq
  let cb : NativeCertificate (step test) encState encState :=
    (NativeCertificate.branch ct cy cz).congr fun _ => rfl
  have hq := NativeCertificate.ofPolyTime_isPolynomial query_polytime
  have hy := NativeCertificate.ofPolyTime_isPolynomial yes_polytime
  have hz := NativeCertificate.ofPolyTime_isPolynomial no_polytime
  have hctS := SparseCNFLeafCounter.polyBounded_comp_space cp cq
    (PolyBounded.of_forall_le D f hs) hq.2
  have hcbS : PolyBounded (fun s => (encState s).length) cb.space :=
    ((hctS.add hy.2).add hz.2).mono fun s => by
      change ct.space s + (if test (query s) then cy.space s else cz.space s) ≤
        ct.space s + cy.space s + cz.space s
      split_ifs <;> omega
  let H (s : State) := cq.time s + cy.time s + cz.time s +
    D * ((UpperDomination.encInput (query s)).length + 1) ^ f
  have hH : PolyBounded (fun s => (encState s).length) H :=
    ((hq.1.add hy.1).add hz.1).add ((PolyBounded.const D).mul
      ((query_polytime.polyBounded_length.add (.const 1)).pow f))
  obtain ⟨cR, eR, hR⟩ := hH.exists_le
  obtain ⟨cS, eS, hS⟩ := hcbS.exists_le
  let B (g : IndependentDomination.Input) := 5 * ((IndependentDomination.encInput g).length + 1)
  let R (g : IndependentDomination.Input) := cR * (B g + 1) ^ eR
  let Q (g : IndependentDomination.Input) := cS * (B g + 1) ^ eS
  have hB : PolyBounded (fun g => (IndependentDomination.encInput g).length) B :=
    (PolyBounded.const 5).mul (PolyBounded.self.add (.const 1))
  have hRP : PolyBounded (fun g => (IndependentDomination.encInput g).length) R :=
    (PolyBounded.const cR).mul ((hB.add (.const 1)).pow eR)
  have hQP : PolyBounded (fun g => (IndependentDomination.encInput g).length) Q :=
    (PolyBounded.const cS).mul ((hB.add (.const 1)).pow eS)
  let cn := NativeCertificate.ofPolyTime rounds_polytime
  let ci := NativeCertificate.ofPolyTime initial_polytime
  let loop := NativeCertificate.iterate cn ci cb
  have hn := NativeCertificate.ofPolyTime_isPolynomial rounds_polytime
  have hi := NativeCertificate.ofPolyTime_isPolynomial initial_polytime
  have hN : PolyBounded (fun g => (IndependentDomination.encInput g).length) rounds :=
    PolyBounded.of_forall_le 1 1 fun g => by
      have := order_le_length g
      simp only [rounds, pow_one, one_mul]; omega
  have hLN := rounds_polytime.polyBounded_length
  have hmaxB (g : IndependentDomination.Input) :
      NativeCertificate.maxStateLength encState (step test) (rounds g) (initial g) ≤ B g :=
    NativeCertificate.maxStateLength_le _ _ _ _ fun j hj => trajectory_length test g hj
  have hmaxQ (g : IndependentDomination.Input) :
      NativeCertificate.maxRoundSpace cb (rounds g) (initial g) ≤ Q g :=
    NativeCertificate.maxRoundSpace_le _ _ _ fun j hj =>
      (hS _).trans (Nat.mul_le_mul_left cS
        (Nat.pow_le_pow_left (Nat.add_le_add_right (trajectory_length test g hj) 1) eS))
  have hloopS : PolyBounded (fun g => (IndependentDomination.encInput g).length) loop.space :=
    ((((hn.2.add hi.2).add hQP).add hB).add hLN).mono fun g => by
      change cn.space g + ci.space g +
        NativeCertificate.maxRoundSpace cb (rounds g) (initial g) +
        NativeCertificate.maxStateLength encState (step test) (rounds g) (initial g) +
        (encNat (rounds g)).length ≤
          cn.space g + ci.space g + Q g + B g + (encNat (rounds g)).length
      have := hmaxQ g
      have := hmaxB g
      omega
  have hfinalL : PolyBounded (fun g => (IndependentDomination.encInput g).length)
      (fun g => (encState ((step test)^[rounds g] (initial g))).length) :=
    hB.mono fun g => trajectory_length test g (Nat.le_refl _)
  let post := NativeCertificate.ofPolyTime output_polytime
  have hp := NativeCertificate.ofPolyTime_isPolynomial output_polytime
  have hpostT := hp.1.comp hfinalL
  have hpostS := hp.2.comp hfinalL
  let cs : NativeCertificate (run test) IndependentDomination.encInput encNat :=
    (post.comp loop).congr fun _ => rfl
  have hcsS : PolyBounded (fun g => (IndependentDomination.encInput g).length) cs.space :=
    hloopS.add hpostS
  let W (g : IndependentDomination.Input) := cn.time g + ci.time g +
    (rounds g + 1) * (R g + B g + ((encNat (rounds g)).length + 1) ^ 2) +
    post.time ((step test)^[rounds g] (initial g)) + cs.space g
  have hW : PolyBounded (fun g => (IndependentDomination.encInput g).length) W :=
    (((hn.1.add hi.1).add ((hN.add (.const 1)).mul
      ((hRP.add hB).add ((hLN.add (.const 1)).pow 2)))).add hpostT).add hcsS
  obtain ⟨C, e, hCe⟩ := hW.exists_le
  refine ⟨run test, cs, C, e, A, fun g => (Nat.le_add_left _ _).trans (hCe g), ?_⟩
  intro n G _
  refine ⟨run_optimal test G (fun k => (ht G k).1), ?_⟩
  let g := IndependentDomination.ofGraph G
  let E := 2 ^ (A * Nat.logLogSqrtLogScale n)
  have hE : 0 < E := Nat.two_pow_pos _
  have hmaxT : NativeCertificate.maxRoundTime cb (rounds g) (initial g) ≤ R g * E := by
    apply NativeCertificate.maxRoundTime_le
    intro j hj
    let s := (step test)^[j] (initial g)
    have hg : original s = g := (trajectory test g j).1
    have hquery : query s = UpperDomination.ofGraph G (next s : ℤ) := by
      exact Prod.ext hg rfl
    have htime := (ht G (next s : ℤ)).2
    rw [← hquery] at htime
    change cp.time (query s) ≤
      D * ((UpperDomination.encInput (query s)).length + 1) ^ f * E at htime
    have hlocal : cb.time s ≤ H s * E := by
      change cq.time s + cp.time (query s) +
        (if test (query s) then cy.time s else cz.time s) ≤ _
      have hsmall : cq.time s + (if test (query s) then cy.time s else cz.time s) ≤
          cq.time s + cy.time s + cz.time s := by split_ifs <;> omega
      have hm := Nat.le_mul_of_pos_right (cq.time s + cy.time s + cz.time s) hE
      have hh := Nat.add_le_add hm htime
      dsimp only [H]
      rw [Nat.add_mul]
      omega
    exact hlocal.trans (Nat.mul_le_mul_right E ((hR s).trans
      (Nat.mul_le_mul_left cR (Nat.pow_le_pow_left
        (Nat.add_le_add_right (trajectory_length test g hj) 1) eR))))
  change cn.time g + ci.time g + (rounds g + 1) *
    (NativeCertificate.maxRoundTime cb (rounds g) (initial g) +
      NativeCertificate.maxStateLength encState (step test) (rounds g) (initial g) +
      ((encNat (rounds g)).length + 1) ^ 2) +
    post.time ((step test)^[rounds g] (initial g)) ≤ _
  have hmb := hmaxB g
  have ht0 := Nat.le_mul_of_pos_right
    (cn.time g + ci.time g + post.time ((step test)^[rounds g] (initial g))) hE
  have ht1 := Nat.le_mul_of_pos_right
    (B g + ((encNat (rounds g)).length + 1) ^ 2) hE
  have ht2 := Nat.mul_le_mul_left (rounds g + 1) (Nat.add_le_add hmaxT ht1)
  have hfinal : cs.time g ≤ W g * E := by
    change cn.time g + ci.time g + (rounds g + 1) *
      (NativeCertificate.maxRoundTime cb (rounds g) (initial g) +
        NativeCertificate.maxStateLength encState (step test) (rounds g) (initial g) +
        ((encNat (rounds g)).length + 1) ^ 2) +
      post.time ((step test)^[rounds g] (initial g)) ≤ _
    have hm := Nat.mul_le_mul_left (rounds g + 1) (Nat.add_le_add_right
      (Nat.add_le_add_left hmb (NativeCertificate.maxRoundTime cb (rounds g) (initial g)))
      (((encNat (rounds g)).length + 1) ^ 2))
    dsimp only [W]
    nlinarith
  exact hfinal.trans (Nat.mul_le_mul_right E (hCe g))

open Classical in
/-- The same actual optimizer has the real source eta bound; the rounded certificate above covers
all smaller and empty graphs. The maximum set cardinality is attained, rather than only feasible. -/
theorem exists_optimum_realEta_certificate :
    ∃ optimum : IndependentDomination.Input → ℕ,
      ∃ cs : NativeCertificate optimum IndependentDomination.encInput encNat, ∃ C e A : ℕ,
        (∀ g, cs.space g ≤ C * ((IndependentDomination.encInput g).length + 1) ^ e) ∧
        ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
          ((∃ S : Set (Fin n), Minimal G.IsDominatingSet S ∧
            Nat.card S = optimum (IndependentDomination.ofGraph G)) ∧
            ∀ S : Set (Fin n), Minimal G.IsDominatingSet S →
              Nat.card S ≤ optimum (IndependentDomination.ofGraph G)) ∧
          (16 ≤ n → (cs.time (IndependentDomination.ofGraph G) : ℝ) ≤ (C : ℝ) *
            ((IndependentDomination.encInput (IndependentDomination.ofGraph G)).length + 1 : ℕ) ^
              e *
              (2 : ℝ) ^ ((A : ℝ) * Real.logLogSqrtLogScale n)) := by
  obtain ⟨optimum, cs, C, e, A, hs, h⟩ := exists_optimum_sharp_certificate
  refine ⟨optimum, cs, C, e, 6 * A, hs, ?_⟩
  intro n G _
  refine ⟨(h G).1, fun hn => ?_⟩
  have ht : (cs.time (IndependentDomination.ofGraph G) : ℝ) ≤ (C : ℝ) *
      ((IndependentDomination.encInput (IndependentDomination.ofGraph G)).length + 1 : ℕ) ^ e *
        (2 : ℝ) ^ (A * Nat.logLogSqrtLogScale n) := by exact_mod_cast (h G).2
  exact ht.trans (mul_le_mul_of_nonneg_left
    (Nat.two_pow_mul_logLogSqrtLogScale_le A hn) (by positivity))

end Cslib.Logic.PL.UpperDomination.Optimum
