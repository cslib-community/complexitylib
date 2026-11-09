/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.FineGrained.InducedMatching
public import CslibFrontier.Computability.Complexity.FineGrained.InducedMatchingInterval
import all CslibFrontier.Computability.PolyTime.CNF.SparseCNFLeafCounter
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div

/-!
# The full induced matching size distribution

Compute exact edge-size coefficients in order, retaining only the original matrix, current index
and binary coefficient list. Each coefficient uses the approved functional endpoint-equality
construction. The count is of conventional induced matching subgraphs, not markings or gate
traces. This is [ChenJiangZhu2027], Corollary 7.5 / Appendix D.1 (PDF pp. 26, 34).

## Main definitions

* `caseInput`: compute the actual endpoint equality test for an edge index.
* `run`: sequentially compute the entire ordered coefficient list.

## Main results

* `run_eq_map`: exact list order, without a supplied output list.
* `exists_distribution_realEta_certificate`: actual complete coefficient list with sharp native
  time, global polynomial workspace and a separate quadratic binary output bound.
-/

public section

namespace Cslib.Logic.PL.InducedMatching.Distribution

open Turing.MultiTapeTM Cslib.GenericRAM Cslib.Complexity

/-- Original graph and unary edge index, used only within a polynomial-length traversal. -/
abbrev Case := IndependentDomination.Input × ℕ
/-- Original matrix of a coefficient request. -/
@[expose] def graph (p : Case) : IndependentDomination.Input := p.1
/-- Number of unordered edges required in this coefficient. -/
@[expose] def index (p : Case) : ℕ := p.2
/-- Complete coefficient request, including retained original input. -/
@[expose] def encCase : Case ↪ List Bool := encPair IndependentDomination.encInput encUnary
/-- Compute twice the edge index as both binary endpoint bounds. No circuit is supplied as input. -/
@[expose] def caseInput (p : Case) : IndependentDominationInterval.Input :=
  (graph p, 2 * index p, 2 * index p)

private theorem caseInput_polytime : ComputableInPolyTime caseInput encCase
    IndependentDominationInterval.encInput := by
  have hk : ComputableInPolyTime (fun p => 2 * index p) encCase encUnary := by
    unfold index encCase; fun_prop
  have hb := ComputableInPolyTime.unary_to_binary.comp hk
  have hg : ComputableInPolyTime graph encCase IndependentDomination.encInput := by
    unfold graph encCase; fun_prop
  exact hg.prod (hb.prod hb)

open Classical in
/-- Exact endpoint equality is an exact edge-count test on actual matching subgraphs. -/
theorem coefficient_count {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ) :
    Fintype.card {σ : Fin n → Bool //
      ((⊤ : G.Subgraph).induce {u | σ u = true}).IsMatching ∧
        2 * k ≤ Cslib.BitString.weight σ ∧ Cslib.BitString.weight σ ≤ 2 * k} =
      Nat.card {M : G.Subgraph // M.IsMatching ∧ M.IsInduced ∧ Nat.card M.edgeSet = k} := by
  have h := SimpleGraph.card_inducedMatching_supports_eq G
    (fun w => 2 * k ≤ w ∧ w ≤ 2 * k)
  rw [← Nat.card_eq_fintype_card]
  have he (M : G.Subgraph) :
      (M.IsMatching ∧ M.IsInduced ∧ 2 * k ≤ 2 * Nat.card M.edgeSet ∧
        2 * Nat.card M.edgeSet ≤ 2 * k) ↔
      (M.IsMatching ∧ M.IsInduced ∧ Nat.card M.edgeSet = k) := by
    constructor
    · rintro ⟨hm, hi, hl, hu⟩; exact ⟨hm, hi, by omega⟩
    · rintro ⟨hm, hi, he⟩; exact ⟨hm, hi, by omega, by omega⟩
  exact h.trans (Nat.card_congr (Equiv.subtypeEquivRight he))

open Classical in
/-- Distinct matching supports give at most one coefficient contribution per original bit word. -/
theorem coefficient_le_two_pow {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ) :
    Nat.card {M : G.Subgraph // M.IsMatching ∧ M.IsInduced ∧ Nat.card M.edgeSet = k} ≤ 2 ^ n := by
  rw [← coefficient_count G k]
  calc
    _ ≤ Fintype.card (Fin n → Bool) := Fintype.card_subtype_le _
    _ = _ := by simp

/-- Original matrix, unary next index and reverse-ordered accumulated binary coefficients. -/
abbrev State := IndependentDomination.Input × ℕ × List ℕ
/-- Retained original matrix throughout the sequential coefficient calls. -/
@[expose] def original (s : State) : IndependentDomination.Input := s.1
/-- Next coefficient index. -/
@[expose] def next : State → ℕ | (_, j, _) => j
/-- Accumulated binary coefficients, newest first. -/
@[expose] def stored : State → List ℕ | (_, _, xs) => xs
/-- Full live-state framing includes every stored coefficient bit. -/
@[expose] def encState : State ↪ List Bool :=
  encPair IndependentDomination.encInput (encPair encUnary (encList encNat))
/-- One coefficient case, excluding previously accumulated coefficients. -/
@[expose] def request (s : State) : Case := (original s, next s)
/-- Retain the computed coefficient and advance one position. -/
@[expose] def finish (p : State × ℕ) : State :=
  let (s, c) := p
  (original s, next s + 1, c :: stored s)
/-- A real exact-size count followed by binary accumulation. -/
@[expose] def step (counter : IndependentDominationInterval.Input → ℕ) (s : State) : State :=
  finish (s, counter (caseInput (request s)))
/-- Initial retained input and empty output prefix. -/
@[expose] def initial (g : IndependentDomination.Input) : State := (g, 0, [])
/-- Actual number of coefficients, including the empty matching. -/
@[expose] def rounds (g : IndependentDomination.Input) : ℕ := IndependentDomination.order g / 2 + 1
/-- Put the accumulated coefficients into increasing edge-size order. -/
@[expose] def output (s : State) : List ℕ := (stored s).reverse
/-- Actual complete ordered coefficient list, with no matching or auxiliary-cube enumeration. -/
@[expose] def run (counter : IndependentDominationInterval.Input → ℕ)
    (g : IndependentDomination.Input) : List ℕ :=
  output ((step counter)^[rounds g] (initial g))

private theorem trajectory (counter : IndependentDominationInterval.Input → ℕ)
    (g : IndependentDomination.Input) (j : ℕ) :
    (step counter)^[j] (initial g) =
      (g, j, ((List.range j).map fun k => counter (caseInput (g, k))).reverse) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih]
    simp [step, finish, request, original, next, stored, List.range_succ]

/-- Every coefficient is produced in its intended position, including the sole empty coefficient. -/
theorem run_eq_map (counter : IndependentDominationInterval.Input → ℕ)
    (g : IndependentDomination.Input) : run counter g =
      (List.range (rounds g)).map fun k => counter (caseInput (g, k)) := by
  rw [run, trajectory]
  exact List.reverse_reverse _

private theorem request_polytime : ComputableInPolyTime request encState encCase := by
  unfold request original next encState encCase; fun_prop

private theorem finish_polytime : ComputableInPolyTime finish (encPair encState encNat)
    encState := by
  unfold finish original next stored encState
  fun_prop

private theorem initial_polytime : ComputableInPolyTime initial IndependentDomination.encInput
    encState := by unfold initial encState; fun_prop

private theorem rounds_polytime : ComputableInPolyTime rounds IndependentDomination.encInput
    encNat := by
  have ho : ComputableInPolyTime IndependentDomination.order IndependentDomination.encInput
      encUnary := by unfold IndependentDomination.order IndependentDomination.encInput; fun_prop
  have hd := (ComputableInPolyTime.unary_div_const 2).comp ho
  have hn : ComputableInPolyTime rounds IndependentDomination.encInput encUnary := by
    unfold rounds; fun_prop
  exact ComputableInPolyTime.unary_to_binary.comp hn

private theorem output_polytime : ComputableInPolyTime output encState (encList encNat) := by
  have hs : ComputableInPolyTime stored encState (encList encNat) := by
    unfold stored encState; fun_prop
  exact .of_tidy ((ComputableTidilyInPolyTime.listReverse encNat).comp hs.tidy)

open Classical in
/-- Each exact matching coefficient needs at most `v+1` binary bits. -/
theorem coefficient_bits_le {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ) :
    (encNat (Nat.card {M : G.Subgraph //
      M.IsMatching ∧ M.IsInduced ∧ Nat.card M.edgeSet = k})).length ≤ n + 1 := by
  have h := Nat.size_le_size (coefficient_le_two_pow G k)
  simpa only [encNat_apply, Nat.size_eq_bits_len, Nat.size_pow] using h

private theorem rounds_le_length (g : IndependentDomination.Input) :
    rounds g ≤ (IndependentDomination.encInput g).length + 1 := by
  rcases g with ⟨n, rows⟩
  have hn := Nat.div_le_self n 2
  simp only [rounds, IndependentDomination.order, IndependentDomination.encInput,
    length_encPair, encUnary_apply, List.length_replicate]
  omega

private theorem case_length_le (g : IndependentDomination.Input) {j : ℕ} (hj : j ≤ rounds g) :
    (encCase (g, j)).length ≤ 3 * ((IndependentDomination.encInput g).length + 1) := by
  have hn := rounds_le_length g
  simp only [encCase, length_encPair, encUnary_apply, List.length_replicate]
  omega

private theorem trajectory_length (counter : IndependentDominationInterval.Input → ℕ)
    (g : IndependentDomination.Input) {j V : ℕ} (hj : j ≤ rounds g)
    (hV : ∀ k ≤ rounds g, (encNat (counter (caseInput (g, k)))).length ≤ V) :
    (encState ((step counter)^[j] (initial g))).length ≤
      2 * (IndependentDomination.encInput g).length + 2 * rounds g + 2 +
        rounds g * (2 * V + 1) := by
  rw [trajectory]
  simp only [encState, length_encPair, encUnary_apply, List.length_replicate,
    length_encList_reverse]
  have hl := length_encList_le encNat
    ((List.range j).map fun k => counter (caseInput (g, k))) (b := V) (by
      intro c hc
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hc
      exact hV k (by have := List.mem_range.mp hk; omega))
  simp only [List.length_map, List.length_range] at hl
  have hm := Nat.mul_le_mul_right (2 * V + 1) hj
  omega

open Classical in
/-- The complete actual ordered size distribution has sharp original-vertex time and global
polynomial workspace. All sequential count calls, accumulation, reversal, intermediate integer
encodings and output writes are charged. No counter contract or output/runtime advice is input. -/
theorem exists_distribution_sharp_certificate :
    ∃ distribution : IndependentDomination.Input → List ℕ,
      ∃ cs : NativeCertificate distribution IndependentDomination.encInput (encList encNat),
        ∃ C e A : ℕ,
          (∀ g, cs.space g ≤ C * ((IndependentDomination.encInput g).length + 1) ^ e) ∧
          ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
            distribution (IndependentDomination.ofGraph G) =
              (List.range (n / 2 + 1)).map (fun k => Nat.card {M : G.Subgraph //
                M.IsMatching ∧ M.IsInduced ∧ Nat.card M.edgeSet = k}) ∧
            cs.time (IndependentDomination.ofGraph G) ≤ C *
              ((IndependentDomination.encInput (IndependentDomination.ofGraph G)).length + 1) ^ e *
                2 ^ (A * Nat.logLogSqrtLogScale n) := by
  obtain ⟨counter, cp, D, f, A, hs, ht⟩ :=
    InducedMatchingInterval.exists_count_sharp_certificate
  let cq := NativeCertificate.ofPolyTime caseInput_polytime
  have hq := NativeCertificate.ofPolyTime_isPolynomial caseInput_polytime
  let cc := cp.comp cq
  have hccS := SparseCNFLeafCounter.polyBounded_comp_space cp cq
    (PolyBounded.of_forall_le D f hs) hq.2
  have hccL := SparseCNFLeafCounter.polyBounded_output_of_space cc hccS
  obtain ⟨cL, eL, hL⟩ := hccL.exists_le
  let J (g : IndependentDomination.Input) := 3 * ((IndependentDomination.encInput g).length + 1)
  let V (g : IndependentDomination.Input) := cL * (J g + 1) ^ eL
  have hJ : PolyBounded (fun g => (IndependentDomination.encInput g).length) J :=
    (PolyBounded.const 3).mul (PolyBounded.self.add (.const 1))
  have hVP : PolyBounded (fun g => (IndependentDomination.encInput g).length) V :=
    (PolyBounded.const cL).mul ((hJ.add (.const 1)).pow eL)
  have hV (g : IndependentDomination.Input) (j : ℕ) (hj : j ≤ rounds g) :
      (encNat (counter (caseInput (g, j)))).length ≤ V g :=
    (hL _).trans (Nat.mul_le_mul_left cL
      (Nat.pow_le_pow_left (Nat.add_le_add_right (case_length_le g hj) 1) eL))
  let cproj := NativeCertificate.ofPolyTime request_polytime
  have hproj := NativeCertificate.ofPolyTime_isPolynomial request_polytime
  let cf := cc.comp cproj
  have hcfS := SparseCNFLeafCounter.polyBounded_comp_space cc cproj hccS hproj.2
  let cid : NativeCertificate (fun s : State => s) encState encState :=
    NativeCertificate.linear (ComputableInO.of_eq fun _ => rfl)
  let pair := cid.prod cf
  have hpairS : PolyBounded (fun s => (encState s).length) pair.space :=
    PolyBounded.self.add hcfS
  have hpairL := SparseCNFLeafCounter.polyBounded_output_of_space pair hpairS
  let finishC := NativeCertificate.ofPolyTime finish_polytime
  have hfinish := NativeCertificate.ofPolyTime_isPolynomial finish_polytime
  let cb : NativeCertificate (step counter) encState encState :=
    (finishC.comp pair).congr fun _ => rfl
  have hcbS := SparseCNFLeafCounter.polyBounded_comp_space finishC pair hfinish.2 hpairS
  let H (s : State) := (encState s).length + cproj.time s +
    finishC.time (s, counter (caseInput (request s)))
  have hH : PolyBounded (fun s => (encState s).length) H :=
    (PolyBounded.self.add hproj.1).add (hfinish.1.comp hpairL)
  obtain ⟨cH, eH, hHbound⟩ := hH.exists_le
  let F (p : Case) := cq.time p +
    D * ((IndependentDominationInterval.encInput (caseInput p)).length + 1) ^ f
  have hF : PolyBounded (fun p => (encCase p).length) F :=
    hq.1.add ((PolyBounded.const D).mul
      ((caseInput_polytime.polyBounded_length.add (.const 1)).pow f))
  obtain ⟨cF, eF, hFbound⟩ := hF.exists_le
  let cn := NativeCertificate.ofPolyTime rounds_polytime
  let ci := NativeCertificate.ofPolyTime initial_polytime
  have hn := NativeCertificate.ofPolyTime_isPolynomial rounds_polytime
  have hi := NativeCertificate.ofPolyTime_isPolynomial initial_polytime
  have hN : PolyBounded (fun g => (IndependentDomination.encInput g).length) rounds :=
    PolyBounded.of_forall_le 1 1 fun g => by simpa only [one_mul, pow_one] using rounds_le_length g
  let B (g : IndependentDomination.Input) := 2 * (IndependentDomination.encInput g).length +
    2 * rounds g + 2 + rounds g * (2 * V g + 1)
  have hB : PolyBounded (fun g => (IndependentDomination.encInput g).length) B :=
    ((((PolyBounded.const 2).mul PolyBounded.self).add
      ((PolyBounded.const 2).mul hN)).add (.const 2)).add
      (hN.mul (((PolyBounded.const 2).mul hVP).add (.const 1)))
  have hstate (g : IndependentDomination.Input) (j : ℕ) (hj : j ≤ rounds g) :
      (encState ((step counter)^[j] (initial g))).length ≤ B g :=
    trajectory_length counter g hj (hV g)
  let R (g : IndependentDomination.Input) := cH * (B g + 1) ^ eH + cF * (J g + 1) ^ eF
  have hRP : PolyBounded (fun g => (IndependentDomination.encInput g).length) R :=
    ((PolyBounded.const cH).mul ((hB.add (.const 1)).pow eH)).add
      ((PolyBounded.const cF).mul ((hJ.add (.const 1)).pow eF))
  obtain ⟨cS, eS, hS⟩ := hcbS.exists_le
  let Q (g : IndependentDomination.Input) := cS * (B g + 1) ^ eS
  have hQP : PolyBounded (fun g => (IndependentDomination.encInput g).length) Q :=
    (PolyBounded.const cS).mul ((hB.add (.const 1)).pow eS)
  let loop := NativeCertificate.iterate cn ci cb
  have hLN := rounds_polytime.polyBounded_length
  have hmaxB (g : IndependentDomination.Input) :
      NativeCertificate.maxStateLength encState (step counter) (rounds g) (initial g) ≤ B g :=
    NativeCertificate.maxStateLength_le _ _ _ _ (hstate g)
  have hmaxQ (g : IndependentDomination.Input) :
      NativeCertificate.maxRoundSpace cb (rounds g) (initial g) ≤ Q g :=
    NativeCertificate.maxRoundSpace_le _ _ _ fun j hj =>
      (hS _).trans (Nat.mul_le_mul_left cS
        (Nat.pow_le_pow_left (Nat.add_le_add_right (hstate g j hj) 1) eS))
  have hloopS : PolyBounded (fun g => (IndependentDomination.encInput g).length) loop.space :=
    ((((hn.2.add hi.2).add hQP).add hB).add hLN).mono fun g => by
      change cn.space g + ci.space g +
        NativeCertificate.maxRoundSpace cb (rounds g) (initial g) +
        NativeCertificate.maxStateLength encState (step counter) (rounds g) (initial g) +
        (encNat (rounds g)).length ≤
          cn.space g + ci.space g + Q g + B g + (encNat (rounds g)).length
      have := hmaxQ g
      have := hmaxB g
      omega
  have hfinalL : PolyBounded (fun g => (IndependentDomination.encInput g).length)
      (fun g => (encState ((step counter)^[rounds g] (initial g))).length) :=
    hB.mono fun g => hstate g _ (Nat.le_refl _)
  let post := NativeCertificate.ofPolyTime output_polytime
  have hp := NativeCertificate.ofPolyTime_isPolynomial output_polytime
  have hpostT := hp.1.comp hfinalL
  have hpostS := hp.2.comp hfinalL
  let cs : NativeCertificate (run counter) IndependentDomination.encInput (encList encNat) :=
    (post.comp loop).congr fun _ => rfl
  have hcsS : PolyBounded (fun g => (IndependentDomination.encInput g).length) cs.space :=
    hloopS.add hpostS
  let W (g : IndependentDomination.Input) := cn.time g + ci.time g +
    (rounds g + 1) * (R g + B g + ((encNat (rounds g)).length + 1) ^ 2) +
    post.time ((step counter)^[rounds g] (initial g)) + cs.space g
  have hW : PolyBounded (fun g => (IndependentDomination.encInput g).length) W :=
    (((hn.1.add hi.1).add ((hN.add (.const 1)).mul
      ((hRP.add hB).add ((hLN.add (.const 1)).pow 2)))).add hpostT).add hcsS
  obtain ⟨C, e, hCe⟩ := hW.exists_le
  refine ⟨run counter, cs, C, e, A, fun g => (Nat.le_add_left _ _).trans (hCe g), ?_⟩
  intro n G _
  constructor
  · rw [run_eq_map]
    apply List.map_congr_left
    intro k _
    exact (ht G (2 * k) (2 * k)).1.trans (coefficient_count G k)
  · let g := IndependentDomination.ofGraph G
    let E := 2 ^ (A * Nat.logLogSqrtLogScale n)
    have hE : 0 < E := Nat.two_pow_pos _
    have hmaxT : NativeCertificate.maxRoundTime cb (rounds g) (initial g) ≤ R g * E := by
      apply NativeCertificate.maxRoundTime_le
      intro j hj
      let s := (step counter)^[j] (initial g)
      have hrequest : request s = (g, j) := by
        dsimp only [s]
        rw [trajectory]
        rfl
      have htime := (ht G (2 * j) (2 * j)).2
      change cp.time (caseInput (g, j)) ≤ D *
        ((IndependentDominationInterval.encInput (caseInput (g, j))).length + 1) ^ f * E at htime
      have hcountT : cc.time (g, j) ≤ F (g, j) * E := by
        change cq.time (g, j) + cp.time (caseInput (g, j)) ≤ _
        dsimp only [F]
        rw [Nat.add_mul]
        exact Nat.add_le_add (Nat.le_mul_of_pos_right _ hE) htime
      have hbody : cb.time s ≤ (H s + F (g, j)) * E := by
        change (encState s).length + (cproj.time s + cc.time (request s)) +
          finishC.time (s, counter (caseInput (request s))) ≤ _
        rw [hrequest]
        have hm := Nat.le_mul_of_pos_right (H s) hE
        dsimp only [H] at hm
        dsimp only [H]
        rw [hrequest] at hm ⊢
        rw [Nat.add_mul]
        omega
      have hupper : H s + F (g, j) ≤ R g := Nat.add_le_add
        ((hHbound s).trans (Nat.mul_le_mul_left cH
          (Nat.pow_le_pow_left (Nat.add_le_add_right (hstate g j hj) 1) eH)))
        ((hFbound (g, j)).trans (Nat.mul_le_mul_left cF
          (Nat.pow_le_pow_left (Nat.add_le_add_right (case_length_le g hj) 1) eF)))
      exact hbody.trans (Nat.mul_le_mul_right E hupper)
    have hmb := hmaxB g
    have ht0 := Nat.le_mul_of_pos_right
      (cn.time g + ci.time g + post.time ((step counter)^[rounds g] (initial g))) hE
    have ht1 := Nat.le_mul_of_pos_right
      (B g + ((encNat (rounds g)).length + 1) ^ 2) hE
    have ht2 := Nat.mul_le_mul_left (rounds g + 1) (Nat.add_le_add hmaxT ht1)
    have hm := Nat.mul_le_mul_left (rounds g + 1) (Nat.add_le_add_right
      (Nat.add_le_add_left hmb (NativeCertificate.maxRoundTime cb (rounds g) (initial g)))
      (((encNat (rounds g)).length + 1) ^ 2))
    have htime : cs.time g ≤ W g * E := by
      change cn.time g + ci.time g + (rounds g + 1) *
        (NativeCertificate.maxRoundTime cb (rounds g) (initial g) +
          NativeCertificate.maxStateLength encState (step counter) (rounds g) (initial g) +
          ((encNat (rounds g)).length + 1) ^ 2) +
        post.time ((step counter)^[rounds g] (initial g)) ≤ _
      dsimp only [W]
      nlinarith
    exact htime.trans (Nat.mul_le_mul_right E (hCe g))

open Classical in
/-- Binary framing of the complete mathematical coefficient list is quadratic in the original
vertex count, including every element's delimiter. This is separate from the runtime proof. -/
theorem coefficient_list_encoding_bound {n : ℕ} (G : SimpleGraph (Fin n)) :
    (encList encNat ((List.range (n / 2 + 1)).map (fun k => Nat.card {M : G.Subgraph //
      M.IsMatching ∧ M.IsInduced ∧ Nat.card M.edgeSet = k}))).length ≤
        (n / 2 + 1) * (2 * (n + 1) + 1) := by
  have h := length_encList_le encNat ((List.range (n / 2 + 1)).map (fun k => Nat.card
    {M : G.Subgraph // M.IsMatching ∧ M.IsInduced ∧ Nat.card M.edgeSet = k})) (b := n + 1) (by
      intro c hc
      obtain ⟨k, _, rfl⟩ := List.mem_map.mp hc
      exact coefficient_bits_le G k)
  simpa only [List.length_map, List.length_range] using h

open Classical in
/-- Complete Corollary 7.5 size distribution with the real source exponent, actual binary output
bound and global polynomial workspace. Rounded resources above cover small and empty graphs. -/
theorem exists_distribution_realEta_certificate :
    ∃ distribution : IndependentDomination.Input → List ℕ,
      ∃ cs : NativeCertificate distribution IndependentDomination.encInput (encList encNat),
        ∃ C e A : ℕ,
          (∀ g, cs.space g ≤ C * ((IndependentDomination.encInput g).length + 1) ^ e) ∧
          ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
            distribution (IndependentDomination.ofGraph G) =
              (List.range (n / 2 + 1)).map (fun k => Nat.card {M : G.Subgraph //
                M.IsMatching ∧ M.IsInduced ∧ Nat.card M.edgeSet = k}) ∧
            (encList encNat (distribution (IndependentDomination.ofGraph G))).length ≤
              (n / 2 + 1) * (2 * (n + 1) + 1) ∧
            (16 ≤ n → (cs.time (IndependentDomination.ofGraph G) : ℝ) ≤ (C : ℝ) *
              ((IndependentDomination.encInput (IndependentDomination.ofGraph G)).length + 1 : ℕ) ^
                e * (2 : ℝ) ^ ((A : ℝ) * Real.logLogSqrtLogScale n)) := by
  obtain ⟨distribution, cs, C, e, A, hs, h⟩ := exists_distribution_sharp_certificate
  refine ⟨distribution, cs, C, e, 6 * A, hs, ?_⟩
  intro n G _
  refine ⟨(h G).1, ?_, fun hn => ?_⟩
  · rw [(h G).1]
    exact coefficient_list_encoding_bound G
  · have ht : (cs.time (IndependentDomination.ofGraph G) : ℝ) ≤ (C : ℝ) *
        ((IndependentDomination.encInput (IndependentDomination.ofGraph G)).length + 1 : ℕ) ^ e *
          (2 : ℝ) ^ (A * Nat.logLogSqrtLogScale n) := by exact_mod_cast (h G).2
    exact ht.trans (mul_le_mul_of_nonneg_left
      (Nat.two_pow_mul_logLogSqrtLogScale_le A hn) (by positivity))

end Cslib.Logic.PL.InducedMatching.Distribution
