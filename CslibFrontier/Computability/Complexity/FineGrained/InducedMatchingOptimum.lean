/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.FineGrained.InducedMatchingInterval
import all CslibFrontier.Computability.PolyTime.CNF.SparseCNFLeafCounter

/-!
# Executable maximum induced matching size

Scan the polynomially many original edge thresholds with the actual native threshold decider,
retaining the original graph, current threshold and best feasible edge count. The result is attained
by a conventional induced matching and bounds every such matching's unordered edge count.
This realizes the optimum-value clause of [ChenJiangZhu2027], Corollary 7.4 / Appendix D.5
(PDF pp. 26, 37). The scan makes `v + 1` tests rather than the paper's binary search; this preserves
the stated sharp time and polynomial workspace. Matching witness recovery is composed in
`CslibFrontier.Computability.Complexity.FineGrained.InducedMatchingWitness`.

## Main definitions

* `run`: actual bounded threshold traversal, returning a natural edge count.

## Main results

* `run_optimal`: attained and globally optimal edge count from a correct threshold test.
* `exists_optimum_realEta_certificate`: the actual original-input optimizer and complete sharp
  native time/global polynomial workspace.
-/

public section

namespace Cslib.Logic.PL.InducedMatchingInterval.Maximum.Optimum

open Turing.MultiTapeTM Cslib.GenericRAM Cslib.Complexity

/-- Retained original graph, current unary threshold and best unary edge count. -/
abbrev State := IndependentDomination.Input × ℕ × ℕ
/-- Original matrix retained through every threshold call. -/
@[expose] def original (s : State) : IndependentDomination.Input := s.1
/-- Next edge threshold, retained in unary within the polynomial-length scan. -/
@[expose] def next : State → ℕ | (_, j, _) => j
/-- Best feasible edge count seen so far. -/
@[expose] def best : State → ℕ | (_, _, k) => k
/-- Full live-state encoding, including the retained original matrix. -/
@[expose] def encState : State ↪ List Bool :=
  encPair IndependentDomination.encInput (encPair encUnary encUnary)
/-- Prepare the actual signed binary threshold query. -/
@[expose] def query (s : State) : Maximum.Input := (original s, (next s : ℤ))
/-- Advance after a successful threshold test. -/
@[expose] def yes (s : State) : State := (original s, next s + 1, next s)
/-- Advance after an unsuccessful threshold test. -/
@[expose] def no (s : State) : State := (original s, next s + 1, best s)
/-- One real threshold call and bounded-state update. -/
@[expose] def step (test : Maximum.Input → Bool) (s : State) : State :=
  if test (query s) then yes s else no s
/-- Initial zero threshold, retaining the entire runtime graph. -/
@[expose] def initial (g : IndependentDomination.Input) : State := (g, 0, 0)
/-- Number of real threshold calls, polynomial in the unary declaration. -/
@[expose] def rounds (g : IndependentDomination.Input) : ℕ := IndependentDomination.order g + 1
/-- Stream the edge thresholds; no matching or assignment family is enumerated. -/
@[expose] def run (test : Maximum.Input → Bool) (g : IndependentDomination.Input) : ℕ :=
  best ((step test)^[rounds g] (initial g))

private theorem trajectory (test : Maximum.Input → Bool) (g : IndependentDomination.Input) (j : ℕ) :
    original ((step test)^[j] (initial g)) = g ∧
      next ((step test)^[j] (initial g)) = j ∧ best ((step test)^[j] (initial g)) ≤ j := by
  induction j with
  | zero => exact ⟨rfl, rfl, Nat.le_refl _⟩
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    simp only [original, next, best] at ih
    simp only [step]
    split_ifs <;> simp only [yes, no, original, next, best] <;>
      exact ⟨ih.1, by omega, by omega⟩

private theorem scan_spec (test : Maximum.Input → Bool) (g : IndependentDomination.Input)
    (hzero : test (g, 0) = true) (j : ℕ) :
    test (g, (best ((step test)^[j] (initial g)) : ℤ)) = true ∧
      ∀ k < j, test (g, (k : ℤ)) = true → k ≤ best ((step test)^[j] (initial g)) := by
  induction j with
  | zero => exact ⟨hzero, by omega⟩
  | succ j ih =>
    have hp := trajectory test g j
    rw [Function.iterate_succ_apply']
    simp only [step, query, hp.1, hp.2]
    split_ifs with ht
    · constructor
      · change test (g, (next ((step test)^[j] (initial g)) : ℤ)) = true
        rwa [hp.2.1]
      · intro k hk _
        change k ≤ next ((step test)^[j] (initial g))
        omega
    · refine ⟨ih.1, ?_⟩
      intro k hk hkT
      have hkj : k < j := by
        by_contra h
        have : k = j := by omega
        exact ht (this ▸ hkT)
      exact ih.2 k hkj hkT

open Classical in
/-- The bounded traversal returns an attained global maximum, measured in actual unordered edges.
The test hypothesis is discharged by the proved production decider in the resource endpoint. -/
theorem run_optimal (test : Maximum.Input → Bool) {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj]
    (htest : ∀ k : ℤ, test (Maximum.ofGraph G k) = true ↔
      ∃ M : G.Subgraph, M.IsMatching ∧ M.IsInduced ∧ k ≤ (Nat.card M.edgeSet : ℤ)) :
    (∃ M : G.Subgraph, M.IsMatching ∧ M.IsInduced ∧
      Nat.card M.edgeSet = run test (IndependentDomination.ofGraph G)) ∧
      ∀ M : G.Subgraph, M.IsMatching → M.IsInduced →
        Nat.card M.edgeSet ≤ run test (IndependentDomination.ofGraph G) := by
  have he : test (Maximum.ofGraph G 0) = true := by
    apply (htest 0).mpr
    refine ⟨⊥, ?_, ?_, by omega⟩
    · intro u hu; exact hu.elim
    · intro u hu; exact hu.elim
  have hs := scan_spec test (IndependentDomination.ofGraph G) he (n + 1)
  have hub (M : G.Subgraph) (hm : M.IsMatching) : Nat.card M.edgeSet ≤ n := by
    have hv := Nat.card_le_card_of_injective (Subtype.val : M.verts → Fin n)
      Subtype.val_injective
    rw [hm.card_verts_eq_twice_edges, Nat.card_fin] at hv
    omega
  have hbound (M : G.Subgraph) (hm : M.IsMatching) (hi : M.IsInduced) :
      Nat.card M.edgeSet ≤ run test (IndependentDomination.ofGraph G) := by
    apply hs.2 _ (by have := hub M hm; omega)
    exact (htest _).mpr ⟨M, hm, hi, by omega⟩
  refine ⟨?_, hbound⟩
  obtain ⟨M, hm, hi, hsize⟩ := (htest _).mp hs.1
  have hsize' : run test (IndependentDomination.ofGraph G) ≤ Nat.card M.edgeSet :=
    Int.ofNat_le.mp hsize
  exact ⟨M, hm, hi, Nat.le_antisymm (hbound M hm hi) hsize'⟩

private theorem query_polytime : ComputableInPolyTime query encState Maximum.encInput := by
  have hj : ComputableInPolyTime next encState encUnary := by unfold next encState; fun_prop
  have hb := ComputableInPolyTime.intBin_natCast.comp
    (ComputableInPolyTime.unary_to_binary.comp hj)
  have hg : ComputableInPolyTime original encState IndependentDomination.encInput := by
    unfold original encState; fun_prop
  exact hg.prod hb

private theorem yes_polytime : ComputableInPolyTime yes encState encState := by
  unfold yes original next encState
  fun_prop

private theorem no_polytime : ComputableInPolyTime no encState encState := by
  unfold no original next best encState
  fun_prop

private theorem initial_polytime : ComputableInPolyTime initial IndependentDomination.encInput
    encState := by unfold initial encState; fun_prop

private theorem rounds_polytime : ComputableInPolyTime rounds IndependentDomination.encInput
    encNat := by
  have hu : ComputableInPolyTime rounds IndependentDomination.encInput encUnary := by
    unfold rounds IndependentDomination.order IndependentDomination.encInput; fun_prop
  exact ComputableInPolyTime.unary_to_binary.comp hu

private theorem output_polytime : ComputableInPolyTime best encState encNat := by
  have hu : ComputableInPolyTime best encState encUnary := by unfold best encState; fun_prop
  exact ComputableInPolyTime.unary_to_binary.comp hu

private theorem state_length (s : State) : (encState s).length =
    2 * (IndependentDomination.encInput (original s)).length + 2 * next s + best s + 2 := by
  rcases s with ⟨g, j, b⟩
  simp only [encState, original, next, best, length_encPair, encUnary_apply,
    List.length_replicate]
  omega

private theorem order_le_length (g : IndependentDomination.Input) :
    IndependentDomination.order g ≤ (IndependentDomination.encInput g).length := by
  rcases g with ⟨n, rows⟩
  simp only [IndependentDomination.order, IndependentDomination.encInput, length_encPair,
    encUnary_apply, List.length_replicate]
  omega

private theorem trajectory_length (test : Maximum.Input → Bool)
    (g : IndependentDomination.Input) {j : ℕ} (hj : j ≤ rounds g) :
    (encState ((step test)^[j] (initial g))).length ≤
      5 * ((IndependentDomination.encInput g).length + 1) := by
  obtain ⟨hg, hn, hb⟩ := trajectory test g j
  rw [state_length, hg, hn]
  have h := order_le_length g
  unfold rounds at hj
  omega

open Classical in
/-- One actual original-matrix optimizer outputs an attained maximum number of unordered edges.
Its certificate charges every threshold query, loop update and final binary output, with global
polynomial workspace and the source single-loglog time. No optimum or call budget is supplied. -/
theorem exists_optimum_sharp_certificate :
    ∃ optimum : IndependentDomination.Input → ℕ,
      ∃ cs : NativeCertificate optimum IndependentDomination.encInput encNat, ∃ C e A : ℕ,
        (∀ g, cs.space g ≤ C * ((IndependentDomination.encInput g).length + 1) ^ e) ∧
        ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
          ((∃ M : G.Subgraph, M.IsMatching ∧ M.IsInduced ∧
            Nat.card M.edgeSet = optimum (IndependentDomination.ofGraph G)) ∧
            ∀ M : G.Subgraph, M.IsMatching → M.IsInduced →
              Nat.card M.edgeSet ≤ optimum (IndependentDomination.ofGraph G)) ∧
          cs.time (IndependentDomination.ofGraph G) ≤
            C * ((IndependentDomination.encInput (IndependentDomination.ofGraph G)).length + 1) ^
              e *
              2 ^ (A * Nat.logLogSqrtLogScale n) := by
  obtain ⟨test, cp, D, f, A, hs, ht⟩ := Maximum.exists_decide_sharp_certificate
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
    D * ((Maximum.encInput (query s)).length + 1) ^ f
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
    have hquery : query s = Maximum.ofGraph G (next s : ℤ) := by
      exact Prod.ext hg rfl
    have htime := (ht G (next s : ℤ)).2
    rw [← hquery] at htime
    change cp.time (query s) ≤ D * ((Maximum.encInput (query s)).length + 1) ^ f * E at htime
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
all smaller and empty graphs. A maximum edge count is attained, rather than only feasible. -/
theorem exists_optimum_realEta_certificate :
    ∃ optimum : IndependentDomination.Input → ℕ,
      ∃ cs : NativeCertificate optimum IndependentDomination.encInput encNat, ∃ C e A : ℕ,
        (∀ g, cs.space g ≤ C * ((IndependentDomination.encInput g).length + 1) ^ e) ∧
        ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
          ((∃ M : G.Subgraph, M.IsMatching ∧ M.IsInduced ∧
            Nat.card M.edgeSet = optimum (IndependentDomination.ofGraph G)) ∧
            ∀ M : G.Subgraph, M.IsMatching → M.IsInduced →
              Nat.card M.edgeSet ≤ optimum (IndependentDomination.ofGraph G)) ∧
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

end Cslib.Logic.PL.InducedMatchingInterval.Maximum.Optimum
