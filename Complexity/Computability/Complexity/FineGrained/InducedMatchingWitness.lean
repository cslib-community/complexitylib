/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.FineGrained.InducedMatchingOptimum
import all Complexity.Computability.PolyTime.CNF.IndependentDomination
import all Complexity.Computability.PolyTime.CNF.SparseCNFLeafCounter

/-!
# Recovering an optimal induced matching on original vertices

The self-reduction isolates one original vertex at a time, retaining the restriction exactly when
it still admits the computed optimum threshold. No vertices are added. Matching supports cannot
contain isolates, so this restriction is equivalent to fixing the corresponding original bit to
false. The returned support decodes to a conventional optimal induced matching, not just a
threshold certificate. This implements the witness clause of [ChenJiangZhu2027], Corollary 7.4 /
Appendix D.5 (PDF pp. 26, 37), using graph restriction in place of explicit unit-clause insertion.

## Main definitions

* `restrict`: actual original-matrix restriction retaining the declaration.
* `run`: one-vertex-at-a-time original-support recovery.
* `solve`: actual optimum pass followed by recovery at that computed value.
* `decode`: returned original bits as a conventional Mathlib subgraph.

## Main results

* `run_recovers`: returned bits themselves form a feasible matching.
* `exists_optimalWitness_realEta_certificate`: complete attained/global optimum and actual matching
  witness, with sharp original-vertex time and global polynomial workspace.
-/

public section

namespace Cslib.Logic.PL.InducedMatchingInterval.Maximum.Witness

open Turing.MultiTapeTM Cslib.GenericRAM Cslib.Complexity

/-- Retain precisely the original edges whose two endpoints are allowed. The declaration is
unchanged; forbidden vertices become isolates rather than disappearing or becoming free bits. -/
@[expose] def restrict (g : IndependentDomination.Input) (allowed : List Bool) :
    IndependentDomination.Input :=
  (IndependentDomination.order g,
    (List.range (IndependentDomination.order g)).map fun u =>
      (List.range (IndependentDomination.order g)).map fun v =>
        allowed.getD u false && allowed.getD v false && IndependentDomination.adjacent g u v)

/-- The conventional spanning graph obtained by restricting original endpoints. -/
@[expose] def restrictedGraph {n : ℕ} (G : SimpleGraph (Fin n)) (allowed : List Bool) :
    SimpleGraph (Fin n) :=
  ((⊤ : G.Subgraph).induce {u | allowed.getD u.val false = true}).spanningCoe

instance {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (allowed : List Bool) :
    DecidableRel (restrictedGraph G allowed).Adj := fun u v =>
  inferInstanceAs (Decidable (allowed.getD u.val false = true ∧
    allowed.getD v.val false = true ∧ G.Adj u v))

/-- The actual matrix writer preserves the canonical graph promise on every restriction. -/
theorem restrict_ofGraph {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (allowed : List Bool) : restrict (IndependentDomination.ofGraph G) allowed =
      IndependentDomination.ofGraph (restrictedGraph G allowed) := by
  simp only [restrict, IndependentDomination.ofGraph, IndependentDomination.order,
    ← List.map_coe_finRange_eq_range, Function.comp_def, List.finRange, List.map_ofFn]
  congr 1
  apply congrArg List.ofFn
  funext u
  apply congrArg List.ofFn
  funext v
  have ha : IndependentDomination.adjacent
      (n, List.ofFn fun u => List.ofFn fun v => decide (G.Adj u v)) u.val v.val =
        decide (G.Adj u v) := IndependentDomination.adjacent_ofGraph G u v
  rw [ha]
  simp [restrictedGraph, Bool.and_assoc,
    SimpleGraph.Subgraph.spanningCoe_adj, SimpleGraph.Subgraph.induce_adj]

private theorem matching_restriction {n : ℕ} (G : SimpleGraph (Fin n)) (allowed : List Bool)
    (σ : Fin n → Bool) :
    ((⊤ : (restrictedGraph G allowed).Subgraph).induce {u | σ u = true}).IsMatching ↔
      ((⊤ : G.Subgraph).induce {u | σ u = true}).IsMatching ∧
        ∀ u, σ u = true → allowed.getD u.val false = true := by
  constructor
  · intro hm
    have ha (u : Fin n) (hu : σ u = true) : allowed.getD u.val false = true := by
      obtain ⟨v, hv, _⟩ := hm hu
      exact hv.2.2.1
    refine ⟨?_, ha⟩
    intro u hu
    obtain ⟨v, hv, huniq⟩ := hm hu
    refine ⟨v, ⟨hv.1, hv.2.1, hv.2.2.2.2⟩, ?_⟩
    intro w hw
    exact huniq w ⟨hw.1, hw.2.1, ha u hw.1, ha w hw.2.1, hw.2.2⟩
  · rintro ⟨hm, ha⟩ u hu
    obtain ⟨v, hv, huniq⟩ := hm hu
    refine ⟨v, ⟨hv.1, hv.2.1, ha u hv.1, ha v hv.2.1, hv.2.2⟩, ?_⟩
    intro w hw
    exact huniq w ⟨hw.1, hw.2.1, hw.2.2.2.2⟩

/-- Original matching supports extending the current vertex restriction and edge threshold. -/
@[expose] def Admits {n : ℕ} (G : SimpleGraph (Fin n)) (allowed : List Bool) (k : ℕ) : Prop :=
  ∃ σ : Fin n → Bool, ((⊤ : G.Subgraph).induce {u | σ u = true}).IsMatching ∧
    (∀ u, σ u = true → allowed.getD u.val false = true) ∧ 2 * k ≤ Cslib.BitString.weight σ

open Classical in
private theorem threshold_support {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ) :
    (∃ M : G.Subgraph, M.IsMatching ∧ M.IsInduced ∧ (k : ℤ) ≤ (Nat.card M.edgeSet : ℤ)) ↔
      ∃ σ : Fin n → Bool, ((⊤ : G.Subgraph).induce {u | σ u = true}).IsMatching ∧
        2 * k ≤ Cslib.BitString.weight σ := by
  have hc := Maximum.count_correspondence G (k : ℤ)
  have he := congrArg (fun z => 0 < z) hc
  simp only [Nat.card_eq_fintype_card, Fintype.card_pos_iff, nonempty_subtype] at he
  have hcast : (2 * (k : ℤ)).toNat = 2 * k := by omega
  rw [hcast] at he
  have heI := Iff.of_eq he
  simp only [Nat.card_eq_fintype_card]
  exact heI.symm.trans (by
    constructor
    · rintro ⟨σ, hm, hk, _⟩; exact ⟨σ, hm, hk⟩
    · rintro ⟨σ, hm, hk⟩; exact ⟨σ, hm, hk, Cslib.BitString.weight_le_length σ⟩)

/-- The actual threshold query on the written restricted graph is equivalent to an original
matching support extending the restriction. It introduces no graph-reduction assumption. -/
theorem restrict_test {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (test : Maximum.Input → Bool)
    (htest : ∀ (H : SimpleGraph (Fin n)) [DecidableRel H.Adj] (k : ℤ),
      test (Maximum.ofGraph H k) = true ↔
        ∃ M : H.Subgraph, M.IsMatching ∧ M.IsInduced ∧ k ≤ (Nat.card M.edgeSet : ℤ))
    (allowed : List Bool) (k : ℕ) :
    test (restrict (IndependentDomination.ofGraph G) allowed, (k : ℤ)) = true ↔
      Admits G allowed k := by
  rw [restrict_ofGraph]
  change test (Maximum.ofGraph (restrictedGraph G allowed) (k : ℤ)) = true ↔ _
  rw [htest, threshold_support]
  simp only [matching_restriction, Admits, and_assoc]

/-- Original graph and natural threshold for witness self-reduction. The complete optimizer
computes this threshold internally; it is not an optimum certificate accepted from the user. -/
abbrev Input := IndependentDomination.Input × ℕ
/-- Original graph of a recovery instance. -/
@[expose] def graph (x : Input) : IndependentDomination.Input := x.1
/-- Requested minimum edge count. -/
@[expose] def target (x : Input) : ℕ := x.2
/-- Explicit graph and binary natural threshold. -/
@[expose] def encInput : Input ↪ List Bool := encPair IndependentDomination.encInput encNat
/-- Retained problem, unary next vertex, and original-vertex allowed bits. -/
abbrev State := Input × ℕ × List Bool
/-- Retained original graph and threshold. -/
@[expose] def problem (s : State) : Input := s.1
/-- Next original vertex to test. -/
@[expose] def index : State → ℕ | (_, j, _) => j
/-- Current allowed original vertices. -/
@[expose] def allowed : State → List Bool | (_, _, bs) => bs
/-- Full framed live state. -/
@[expose] def encState : State ↪ List Bool := encPair encInput (encPair encUnary encBits)
/-- Fix one original bit to false, retaining all declared positions. -/
@[expose] def clear (bs : List Bool) (j : ℕ) : List Bool := bs.set j false
/-- Test the actual vertex-restricted graph at the unchanged target edge count. -/
@[expose] def query (s : State) : Maximum.Input :=
  (restrict (graph (problem s)) (clear (allowed s) (index s)), (target (problem s) : ℤ))
/-- Retain a feasible restriction and advance to the next original vertex. -/
@[expose] def yes (s : State) : State :=
  (problem s, index s + 1, clear (allowed s) (index s))
/-- An essential vertex remains allowed. -/
@[expose] def no (s : State) : State := (problem s, index s + 1, allowed s)
/-- One real threshold test, with no supplied restriction decision. -/
@[expose] def step (test : Maximum.Input → Bool) (s : State) : State :=
  if test (query s) then yes s else no s
/-- Initially allow every declared vertex, including isolates. -/
@[expose] def initial (x : Input) : State :=
  (x, 0, List.replicate (IndependentDomination.order (graph x)) true)
/-- Inspect every original vertex exactly once. -/
@[expose] def rounds (x : Input) : ℕ := IndependentDomination.order (graph x)
/-- Actual recovered original selection bits. -/
@[expose] def run (test : Maximum.Input → Bool) (x : Input) : List Bool :=
  allowed ((step test)^[rounds x] (initial x))

private theorem clear_get (bs : List Bool) (j i : ℕ) :
    (clear bs j).getD i false = if i = j then false else bs.getD i false := by
  simp only [clear, List.getD_eq_getElem?_getD, List.getElem?_set]
  by_cases h : j = i
  · subst i; by_cases hj : j < bs.length <;> simp [hj]
  · simp [h, Ne.symm h]

private theorem clear_subset (bs : List Bool) (j i : ℕ)
    (h : (clear bs j).getD i false = true) : bs.getD i false = true := by
  by_cases hi : i = j
  · simp only [clear_get, hi, ↓reduceIte] at h
    exact Bool.false_ne_true h |>.elim
  · simpa only [clear_get, hi, ↓reduceIte] using h

private theorem trajectory (test : Maximum.Input → Bool) (x : Input) (j : ℕ) :
    problem ((step test)^[j] (initial x)) = x ∧
      index ((step test)^[j] (initial x)) = j ∧
      (allowed ((step test)^[j] (initial x))).length = rounds x := by
  induction j with
  | zero => exact ⟨rfl, rfl, List.length_replicate⟩
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    simp only [problem, index, allowed] at ih
    simp only [step]
    split_ifs <;> simp only [yes, no, problem, index, allowed, clear, List.length_set] <;>
      exact ⟨ih.1, by omega, ih.2.2⟩

open Classical in
private theorem preserve {n : ℕ} (G : SimpleGraph (Fin n)) (k j : ℕ) (bs : List Bool)
    (hfeas : Admits G bs k)
    (hfixed : ∀ σ : Fin n → Bool, ((⊤ : G.Subgraph).induce {u | σ u = true}).IsMatching →
      (∀ u, σ u = true → bs.getD u.val false = true) → 2 * k ≤ Cslib.BitString.weight σ →
        ∀ u : Fin n, u.val < j → bs.getD u.val false = true → σ u = true) :
    let updated := if Admits G (clear bs j) k then clear bs j else bs
    Admits G updated k ∧
      ∀ σ : Fin n → Bool, ((⊤ : G.Subgraph).induce {u | σ u = true}).IsMatching →
        (∀ u, σ u = true → updated.getD u.val false = true) →
          2 * k ≤ Cslib.BitString.weight σ → ∀ u : Fin n,
            u.val < j + 1 → updated.getD u.val false = true → σ u = true := by
  classical
  dsimp only
  split_ifs with he
  · refine ⟨he, ?_⟩
    intro σ hm hs hk u hu hbu
    have hne : u.val ≠ j := by
      intro h
      rw [clear_get] at hbu
      have hb : false = true := by simpa only [h, ↓reduceIte] using hbu
      exact Bool.false_ne_true hb
    exact hfixed σ hm (fun v hv => clear_subset bs j v.val (hs v hv)) hk u
      (by omega) (clear_subset bs j u.val hbu)
  · refine ⟨hfeas, ?_⟩
    intro σ hm hs hk u hu hbu
    by_cases hlt : u.val < j
    · exact hfixed σ hm hs hk u hlt hbu
    · have huj : u.val = j := by omega
      by_contra hfalse
      apply he
      refine ⟨σ, hm, ?_, hk⟩
      intro v hv
      rw [clear_get]
      split_ifs with hvj
      · have hvu : v = u := Fin.ext (hvj.trans huj.symm)
        exact False.elim (hfalse (hvu ▸ hv))
      · exact hs v hv

open Classical in
private theorem recovery_invariant {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (test : Maximum.Input → Bool)
    (htest : ∀ (H : SimpleGraph (Fin n)) [DecidableRel H.Adj] (k : ℤ),
      test (Maximum.ofGraph H k) = true ↔
        ∃ M : H.Subgraph, M.IsMatching ∧ M.IsInduced ∧ k ≤ (Nat.card M.edgeSet : ℤ))
    (k : ℕ) (hbase : Admits G (List.replicate n true) k) (j : ℕ) :
    let bs := allowed ((step test)^[j] (initial (IndependentDomination.ofGraph G, k)))
    Admits G bs k ∧
      ∀ σ : Fin n → Bool, ((⊤ : G.Subgraph).induce {u | σ u = true}).IsMatching →
        (∀ u, σ u = true → bs.getD u.val false = true) →
          2 * k ≤ Cslib.BitString.weight σ → ∀ u : Fin n,
            u.val < j → bs.getD u.val false = true → σ u = true := by
  induction j with
  | zero => exact ⟨hbase, by omega⟩
  | succ j ih =>
    let s := (step test)^[j] (initial (IndependentDomination.ofGraph G, k))
    have hp := trajectory test (IndependentDomination.ofGraph G, k) j
    have hproblem : problem s = (IndependentDomination.ofGraph G, k) := hp.1
    have hindex : index s = j := hp.2.1
    have hQ : test (query s) = true ↔ Admits G (clear (allowed s) j) k := by
      unfold query
      rw [hproblem, hindex]
      exact restrict_test G test htest (clear (allowed s) j) k
    have hnew := preserve G k j (allowed s) ih.1 ih.2
    rw [Function.iterate_succ_apply']
    let Inv (bs : List Bool) := Admits G bs k ∧
      ∀ σ : Fin n → Bool, ((⊤ : G.Subgraph).induce {u | σ u = true}).IsMatching →
        (∀ u, σ u = true → bs.getD u.val false = true) →
          2 * k ≤ Cslib.BitString.weight σ → ∀ u : Fin n,
            u.val < j + 1 → bs.getD u.val false = true → σ u = true
    change Inv (allowed (step test s))
    change Inv (if Admits G (clear (allowed s) j) k then clear (allowed s) j else allowed s) at hnew
    by_cases he : Admits G (clear (allowed s) j) k
    · have hy := hQ.mpr he
      simp only [he, ↓reduceIte] at hnew
      change Inv (clear (allowed s) j) at hnew
      simpa only [step, hy, ↓reduceIte, yes, allowed, hindex] using hnew
    · have hz : test (query s) = false := Bool.eq_false_iff.mpr (fun h => he (hQ.mp h))
      simp only [he, ↓reduceIte] at hnew
      change Inv (allowed s) at hnew
      simpa only [step, hz, Bool.false_eq_true, ↓reduceIte, no, allowed] using hnew

/-- Decode actual original-vertex output bits to a conventional induced subgraph. -/
@[expose] def decode {n : ℕ} (G : SimpleGraph (Fin n)) (bits : List Bool) : G.Subgraph :=
  (⊤ : G.Subgraph).induce {u | bits.getD u.val false = true}

open Classical in
/-- The actual vertex restriction loop recovers a matching whenever the requested threshold is
feasible. Every retained final vertex is forced in every surviving support, so the returned bits,
not a chosen extension, form the matching. Empty and isolated graphs are included. -/
theorem run_recovers {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (test : Maximum.Input → Bool)
    (htest : ∀ (H : SimpleGraph (Fin n)) [DecidableRel H.Adj] (k : ℤ),
      test (Maximum.ofGraph H k) = true ↔
        ∃ M : H.Subgraph, M.IsMatching ∧ M.IsInduced ∧ k ≤ (Nat.card M.edgeSet : ℤ))
    (k : ℕ) (hk : ∃ M : G.Subgraph, M.IsMatching ∧ M.IsInduced ∧ k ≤ Nat.card M.edgeSet) :
    let bits := run test (IndependentDomination.ofGraph G, k)
    bits.length = n ∧ (decode G bits).IsMatching ∧ (decode G bits).IsInduced ∧
      k ≤ Nat.card (decode G bits).edgeSet := by
  have hbase : Admits G (List.replicate n true) k := by
    obtain ⟨σ, hm, hs⟩ := (threshold_support G k).mp (by
      obtain ⟨M, hm, hi, hsize⟩ := hk
      exact ⟨M, hm, hi, by exact_mod_cast hsize⟩)
    exact ⟨σ, hm, fun u _ => by simp [List.getD_eq_getElem?_getD, u.isLt], hs⟩
  obtain ⟨hfeas, hfixed⟩ := recovery_invariant G test htest k hbase n
  obtain ⟨σ, hm, hs, hsize⟩ := hfeas
  have he : σ = fun u => (run test (IndependentDomination.ofGraph G, k)).getD u.val false := by
    funext u
    have h1 := hs u
    have h2 := hfixed σ hm hs hsize u u.isLt
    change σ u = true →
      (run test (IndependentDomination.ofGraph G, k)).getD u.val false = true at h1
    change (run test (IndependentDomination.ofGraph G, k)).getD u.val false = true →
      σ u = true at h2
    cases hσ : σ u <;>
      cases hb : (run test (IndependentDomination.ofGraph G, k)).getD u.val false <;> simp_all
  rw [he] at hm hsize
  refine ⟨(trajectory test (IndependentDomination.ofGraph G, k) n).2.2, hm,
    (SimpleGraph.Subgraph.isInduced_iff_exists_eq_induce_top _).mpr ⟨_, rfl⟩, ?_⟩
  have hw : Cslib.BitString.weight
      (fun u : Fin n => (run test (IndependentDomination.ofGraph G, k)).getD u.val false) =
        Nat.card (decode G (run test (IndependentDomination.ofGraph G, k))).verts := by
    rw [Cslib.BitString.weight_eq_card_subtype, ← Nat.card_eq_fintype_card]
    rfl
  change (decode G (run test (IndependentDomination.ofGraph G, k))).IsMatching at hm
  rw [hw, hm.card_verts_eq_twice_edges] at hsize
  omega

private theorem restrict_polytime : ComputableInPolyTime
    (fun p : IndependentDomination.Input × List Bool => restrict p.1 p.2)
      (encPair IndependentDomination.encInput encBits) IndependentDomination.encInput := by
  let ei := encPair IndependentDomination.encInput encBits
  have hn : ComputableInPolyTime (fun p : IndependentDomination.Input × List Bool =>
      IndependentDomination.order p.1) ei encUnary := by
    unfold IndependentDomination.order ei IndependentDomination.encInput; fun_prop
  let er := encPair ei encUnary
  let ec := encPair er encUnary
  have hbs : ComputableInPolyTime
      (fun p : ((IndependentDomination.Input × List Bool) × ℕ) × ℕ => p.1.1.2) ec encBits := by
    unfold ec er ei; fun_prop
  have hu : ComputableInPolyTime
      (fun p : ((IndependentDomination.Input × List Bool) × ℕ) × ℕ => p.1.2) ec encUnary := by
    unfold ec er ei; fun_prop
  have hv : ComputableInPolyTime
      (fun p : ((IndependentDomination.Input × List Bool) × ℕ) × ℕ => p.2) ec encUnary := by
    unfold ec er ei; fun_prop
  have hau := ComputableInPolyTime.bitsGetDWithInput hbs hu false
  have hav := ComputableInPolyTime.bitsGetDWithInput hbs hv false
  have hadj := IndependentDomination.adjacent_polytime.comp (show ComputableInPolyTime
    (fun p : ((IndependentDomination.Input × List Bool) × ℕ) × ℕ => (p.1.1.1, p.1.2, p.2))
      ec (encPair IndependentDomination.encInput (encPair encUnary encUnary)) from by
        unfold ec er ei; fun_prop)
  have hcell : ComputableInPolyTime
      (fun p : ((IndependentDomination.Input × List Bool) × ℕ) × ℕ =>
        p.1.1.2.getD p.1.2 false && p.1.1.2.getD p.2 false &&
          IndependentDomination.adjacent p.1.1.1 p.1.2 p.2) ec encBool := by fun_prop
  have hrow := ComputableInPolyTime.mapWithInput
    (f := fun (p : (IndependentDomination.Input × List Bool) × ℕ) v =>
      p.1.2.getD p.2 false && p.1.2.getD v false && IndependentDomination.adjacent p.1.1 p.2 v)
    (ComputableInPolyTime.range.comp (hn.comp (ComputableInPolyTime.fst ei encUnary))) hcell
  exact (hn.prod (ComputableInPolyTime.mapWithInput
    (f := fun (p : IndependentDomination.Input × List Bool) u =>
      (List.range (IndependentDomination.order p.1)).map fun v =>
        p.2.getD u false && p.2.getD v false && IndependentDomination.adjacent p.1 u v)
    (ComputableInPolyTime.range.comp hn) hrow)).of_enc_eq fun _ => rfl

private theorem clear_polytime : ComputableInPolyTime
    (fun p : List Bool × ℕ => clear p.1 p.2) (encPair encBits encUnary) encBits := by
  have hbs := ComputableInPolyTime.fst encBits encUnary
  have hj := ComputableInPolyTime.snd encBits encUnary
  have hlen := (ComputableInPolyTime.length_bits).comp hbs
  have hlt : ComputableInPolyTime (fun p : List Bool × ℕ => decide (p.2 < p.1.length))
      (encPair encBits encUnary) encBool := by fun_prop
  have htake := ComputableInPolyTime.bitsTakeWithInput hbs hj
  have hsucc : ComputableInPolyTime (fun p : List Bool × ℕ => p.2 + 1)
      (encPair encBits encUnary) encUnary := by fun_prop
  have hdrop := ComputableInPolyTime.bitsDropWithInput hbs hsucc
  have hyes := ComputableInPolyTime.bitsAppend htake
    (ComputableInPolyTime.bitsAppend (ComputableInPolyTime.const [false]) hdrop)
  exact (hlt.ite' hyes hbs).of_enc_eq fun ⟨bs, j⟩ => by
    simp only [clear, List.set_eq_take_append_cons_drop, decide_eq_true_eq]
    split_ifs <;> rfl

private theorem query_polytime : ComputableInPolyTime query encState Maximum.encInput := by
  have hg : ComputableInPolyTime (fun s => graph (problem s)) encState
      IndependentDomination.encInput := by unfold graph problem encState encInput; fun_prop
  have hbs : ComputableInPolyTime allowed encState encBits := by unfold allowed encState; fun_prop
  have hj : ComputableInPolyTime index encState encUnary := by unfold index encState; fun_prop
  have hc := clear_polytime.comp (hbs.prod hj)
  have hr := restrict_polytime.comp (hg.prod hc)
  have hk : ComputableInPolyTime (fun s => target (problem s)) encState encNat := by
    unfold target problem encState encInput; fun_prop
  exact hr.prod (ComputableInPolyTime.intBin_natCast.comp hk)

private theorem yes_polytime : ComputableInPolyTime yes encState encState := by
  have hc := clear_polytime.comp (show ComputableInPolyTime (fun s => (allowed s, index s))
    encState (encPair encBits encUnary) from by unfold allowed index encState; fun_prop)
  unfold yes problem index encState
  fun_prop

private theorem no_polytime : ComputableInPolyTime no encState encState := by
  unfold no problem index allowed encState; fun_prop

private theorem initial_polytime : ComputableInPolyTime initial encInput encState := by
  unfold initial encState graph IndependentDomination.order encInput IndependentDomination.encInput
  fun_prop

private theorem rounds_polytime : ComputableInPolyTime rounds encInput encNat := by
  have hn : ComputableInPolyTime rounds encInput encUnary := by
    unfold rounds graph IndependentDomination.order encInput IndependentDomination.encInput;
      fun_prop
  exact ComputableInPolyTime.unary_to_binary.comp hn

private theorem output_polytime : ComputableInPolyTime allowed encState encBits := by
  unfold allowed encState; fun_prop

private theorem state_length (s : State) : (encState s).length =
    2 * (encInput (problem s)).length + 2 * index s + (allowed s).length + 2 := by
  rcases s with ⟨x, j, bs⟩
  simp only [encState, problem, index, allowed, length_encPair, encUnary_apply,
    List.length_replicate, encBits_apply]
  omega

private theorem rounds_le_length (x : Input) : rounds x ≤ (encInput x).length := by
  rcases x with ⟨⟨n, rows⟩, k⟩
  simp only [rounds, graph, IndependentDomination.order, encInput,
    IndependentDomination.encInput, length_encPair, encUnary_apply, List.length_replicate]
  omega

private theorem trajectory_length (test : Maximum.Input → Bool) (x : Input)
    {j : ℕ} (hj : j ≤ rounds x) : (encState ((step test)^[j] (initial x))).length ≤
      5 * ((encInput x).length + 1) := by
  obtain ⟨hp, hi, hl⟩ := trajectory test x j
  rw [state_length, hp, hi, hl]
  have h := rounds_le_length x
  omega

open Classical in
/-- Complete native recovery resources on the original graph and binary requested edge threshold.
Correctness requires feasibility; resources do not require a supplied matching or optimum.
The final original-graph optimizer computes a feasible optimum before invoking this recovery. -/
theorem exists_recovery_sharp_certificate :
    ∃ recover : Input → List Bool, ∃ cs : NativeCertificate recover encInput encBits, ∃ C e A : ℕ,
      (∀ x, cs.space x ≤ C * ((encInput x).length + 1) ^ e) ∧
      ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k : ℕ),
        ((∃ M : G.Subgraph, M.IsMatching ∧ M.IsInduced ∧ k ≤ Nat.card M.edgeSet) →
          let bits := recover (IndependentDomination.ofGraph G, k)
          bits.length = n ∧ (decode G bits).IsMatching ∧ (decode G bits).IsInduced ∧
            k ≤ Nat.card (decode G bits).edgeSet) ∧
        cs.time (IndependentDomination.ofGraph G, k) ≤
          C * ((encInput (IndependentDomination.ofGraph G, k)).length + 1) ^ e *
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
  let B (g : Input) := 5 * ((encInput g).length + 1)
  let R (g : Input) := cR * (B g + 1) ^ eR
  let Q (g : Input) := cS * (B g + 1) ^ eS
  have hB : PolyBounded (fun g => (encInput g).length) B :=
    (PolyBounded.const 5).mul (PolyBounded.self.add (.const 1))
  have hRP : PolyBounded (fun g => (encInput g).length) R :=
    (PolyBounded.const cR).mul ((hB.add (.const 1)).pow eR)
  have hQP : PolyBounded (fun g => (encInput g).length) Q :=
    (PolyBounded.const cS).mul ((hB.add (.const 1)).pow eS)
  let cn := NativeCertificate.ofPolyTime rounds_polytime
  let ci := NativeCertificate.ofPolyTime initial_polytime
  let loop := NativeCertificate.iterate cn ci cb
  have hn := NativeCertificate.ofPolyTime_isPolynomial rounds_polytime
  have hi := NativeCertificate.ofPolyTime_isPolynomial initial_polytime
  have hN : PolyBounded (fun g => (encInput g).length) rounds :=
    PolyBounded.of_forall_le 1 1 fun g => by
      have := rounds_le_length g
      simp only [pow_one, one_mul]; omega
  have hLN := rounds_polytime.polyBounded_length
  have hmaxB (g : Input) :
      NativeCertificate.maxStateLength encState (step test) (rounds g) (initial g) ≤ B g :=
    NativeCertificate.maxStateLength_le _ _ _ _ fun j hj => trajectory_length test g hj
  have hmaxQ (g : Input) :
      NativeCertificate.maxRoundSpace cb (rounds g) (initial g) ≤ Q g :=
    NativeCertificate.maxRoundSpace_le _ _ _ fun j hj =>
      (hS _).trans (Nat.mul_le_mul_left cS
        (Nat.pow_le_pow_left (Nat.add_le_add_right (trajectory_length test g hj) 1) eS))
  have hloopS : PolyBounded (fun g => (encInput g).length) loop.space :=
    ((((hn.2.add hi.2).add hQP).add hB).add hLN).mono fun g => by
      change cn.space g + ci.space g +
        NativeCertificate.maxRoundSpace cb (rounds g) (initial g) +
        NativeCertificate.maxStateLength encState (step test) (rounds g) (initial g) +
        (encNat (rounds g)).length ≤
          cn.space g + ci.space g + Q g + B g + (encNat (rounds g)).length
      have := hmaxQ g
      have := hmaxB g
      omega
  have hfinalL : PolyBounded (fun g => (encInput g).length)
      (fun g => (encState ((step test)^[rounds g] (initial g))).length) :=
    hB.mono fun g => trajectory_length test g (Nat.le_refl _)
  let post := NativeCertificate.ofPolyTime output_polytime
  have hp := NativeCertificate.ofPolyTime_isPolynomial output_polytime
  have hpostT := hp.1.comp hfinalL
  have hpostS := hp.2.comp hfinalL
  let cs : NativeCertificate (run test) encInput encBits :=
    (post.comp loop).congr fun _ => rfl
  have hcsS : PolyBounded (fun g => (encInput g).length) cs.space :=
    hloopS.add hpostS
  let W (g : Input) := cn.time g + ci.time g +
    (rounds g + 1) * (R g + B g + ((encNat (rounds g)).length + 1) ^ 2) +
    post.time ((step test)^[rounds g] (initial g)) + cs.space g
  have hW : PolyBounded (fun g => (encInput g).length) W :=
    (((hn.1.add hi.1).add ((hN.add (.const 1)).mul
      ((hRP.add hB).add ((hLN.add (.const 1)).pow 2)))).add hpostT).add hcsS
  obtain ⟨C, e, hCe⟩ := hW.exists_le
  refine ⟨run test, cs, C, e, A, fun g => (Nat.le_add_left _ _).trans (hCe g), ?_⟩
  intro n G _ k
  refine ⟨run_recovers G test (fun H _ q => (ht H q).1) k, ?_⟩
  let g : Input := (IndependentDomination.ofGraph G, k)
  let E := 2 ^ (A * Nat.logLogSqrtLogScale n)
  have hE : 0 < E := Nat.two_pow_pos _
  have hmaxT : NativeCertificate.maxRoundTime cb (rounds g) (initial g) ≤ R g * E := by
    apply NativeCertificate.maxRoundTime_le
    intro j hj
    let s := (step test)^[j] (initial g)
    have hg : problem s = g := (trajectory test g j).1
    have hquery : query s = Maximum.ofGraph
        (restrictedGraph G (clear (allowed s) (index s))) (k : ℤ) := by
      unfold query
      rw [hg]
      exact Prod.ext (restrict_ofGraph G _) rfl
    have htime := (ht (restrictedGraph G (clear (allowed s) (index s))) (k : ℤ)).2
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

/-- Binary optimum edge count and original-vertex output bits. -/
abbrev Output := ℕ × List Bool
/-- Maximum number of unordered matching edges. -/
@[expose] def value (out : Output) : ℕ := out.1
/-- Original-vertex matching support, in declared vertex order. -/
@[expose] def vertices (out : Output) : List Bool := out.2
/-- Binary optimum and raw original-vertex output word. -/
@[expose] def encOutput : Output ↪ List Bool := encPair encNat encBits
/-- Compute the attained optimum, then recover its actual original matching support. Both functions
are instantiated by proved native machines in `exists_optimalWitness_sharp_certificate`. -/
@[expose] def solve (optimum : IndependentDomination.Input → ℕ)
    (recover : Input → List Bool) (g : IndependentDomination.Input) : Output :=
  (optimum g, recover (g, optimum g))

open Classical in
/-- Complete original-graph maximum induced matching optimization, including an actual witness.
The binary value equals the returned matching's unordered edge count, and every induced matching
has at most that many edges. All preparation, polynomially many calls and output writes are
charged; global workspace is polynomial and sharp time uses the original vertex count. -/
theorem exists_optimalWitness_sharp_certificate :
    ∃ optimize : IndependentDomination.Input → Output,
      ∃ cs : NativeCertificate optimize IndependentDomination.encInput encOutput, ∃ C e A : ℕ,
        (∀ g, cs.space g ≤ C * ((IndependentDomination.encInput g).length + 1) ^ e) ∧
        ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
          (let out := optimize (IndependentDomination.ofGraph G)
           let M := decode G (vertices out)
           (vertices out).length = n ∧ M.IsMatching ∧ M.IsInduced ∧
             Nat.card M.edgeSet = value out ∧
               ∀ Q : G.Subgraph, Q.IsMatching → Q.IsInduced → Nat.card Q.edgeSet ≤ value out) ∧
          cs.time (IndependentDomination.ofGraph G) ≤
            C * ((IndependentDomination.encInput (IndependentDomination.ofGraph G)).length + 1) ^
              e *
              2 ^ (A * Nat.logLogSqrtLogScale n) := by
  obtain ⟨optimum, co, C0, e0, A0, hso, ho⟩ := Optimum.exists_optimum_sharp_certificate
  obtain ⟨recover, cw, C1, e1, A1, hsw, hw⟩ := exists_recovery_sharp_certificate
  let ci : NativeCertificate (fun g : IndependentDomination.Input => g)
      IndependentDomination.encInput IndependentDomination.encInput :=
    NativeCertificate.linear (ComputableInO.of_eq fun _ => rfl)
  let cc := ci.prod co
  have hccS : PolyBounded (fun g => (IndependentDomination.encInput g).length) cc.space :=
    PolyBounded.self.add (PolyBounded.of_forall_le C0 e0 hso)
  obtain ⟨k, _, hlen⟩ := cc.computes
  have hlength : PolyBounded (fun g => (IndependentDomination.encInput g).length)
      (fun g => (encInput (g, optimum g)).length) :=
    ((PolyBounded.const k).mul (hccS.add (.const 1))).mono hlen
  let cv : NativeCertificate target encInput encNat :=
    NativeCertificate.linear (ComputableInO.snd IndependentDomination.encInput encNat)
  let cr := cv.prod cw
  have hcrS : PolyBounded (fun x => (encInput x).length) cr.space :=
    PolyBounded.self.add (PolyBounded.of_forall_le C1 e1 hsw)
  let cs : NativeCertificate (solve optimum recover) IndependentDomination.encInput encOutput :=
    (cr.comp cc).congr fun _ => rfl
  have hcsS := SparseCNFLeafCounter.polyBounded_comp_space cr cc hcrS hccS
  let W (g : IndependentDomination.Input) := (IndependentDomination.encInput g).length +
    C0 * ((IndependentDomination.encInput g).length + 1) ^ e0 +
    (encInput (g, optimum g)).length + C1 * ((encInput (g, optimum g)).length + 1) ^ e1 + cs.space g
  have hW : PolyBounded (fun g => (IndependentDomination.encInput g).length) W :=
    (((PolyBounded.self.add ((PolyBounded.const C0).mul
      ((PolyBounded.self.add (.const 1)).pow e0))).add hlength).add
      ((PolyBounded.const C1).mul ((hlength.add (.const 1)).pow e1))).add hcsS
  obtain ⟨C, e, hCe⟩ := hW.exists_le
  refine ⟨solve optimum recover, cs, C, e, A0 + A1,
    fun g => (Nat.le_add_left _ _).trans (hCe g), ?_⟩
  intro n G _
  obtain ⟨hopt, hupper⟩ := (ho G).1
  have hfeas : ∃ M : G.Subgraph, M.IsMatching ∧ M.IsInduced ∧
      optimum (IndependentDomination.ofGraph G) ≤ Nat.card M.edgeSet := by
    obtain ⟨M, hm, hi, he⟩ := hopt
    exact ⟨M, hm, hi, he.ge⟩
  obtain ⟨hl, hm, hi, hk⟩ := (hw G (optimum (IndependentDomination.ofGraph G))).1 hfeas
  constructor
  · exact ⟨hl, hm, hi, Nat.le_antisymm (hupper _ hm hi) hk, hupper⟩
  · let g := IndependentDomination.ofGraph G
    let E := 2 ^ ((A0 + A1) * Nat.logLogSqrtLogScale n)
    have hE : 0 < E := Nat.two_pow_pos _
    have hE0 : 2 ^ (A0 * Nat.logLogSqrtLogScale n) ≤ E :=
      Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ (Nat.le_add_right A0 A1))
    have hE1 : 2 ^ (A1 * Nat.logLogSqrtLogScale n) ≤ E :=
      Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ (Nat.le_add_left A1 A0))
    have ht0 := (ho G).2.trans (Nat.mul_le_mul_left _ hE0)
    have ht1 := (hw G (optimum g)).2.trans (Nat.mul_le_mul_left _ hE1)
    have hlin := Nat.le_mul_of_pos_right
      ((IndependentDomination.encInput g).length + (encInput (g, optimum g)).length) hE
    have htime : cs.time g ≤ W g * E := by
      change (IndependentDomination.encInput g).length + co.time g +
        ((encInput (g, optimum g)).length + cw.time (g, optimum g)) ≤ _
      dsimp only [W]
      nlinarith
    exact htime.trans (Nat.mul_le_mul_right E (hCe g))

open Classical in
/-- The complete optimum-value and original-matching witness algorithm has the real source eta
bound. Small and empty graphs retain the rounded guarantee, without a feasibility promise. -/
theorem exists_optimalWitness_realEta_certificate :
    ∃ optimize : IndependentDomination.Input → Output,
      ∃ cs : NativeCertificate optimize IndependentDomination.encInput encOutput, ∃ C e A : ℕ,
        (∀ g, cs.space g ≤ C * ((IndependentDomination.encInput g).length + 1) ^ e) ∧
        ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
          (let out := optimize (IndependentDomination.ofGraph G)
           let M := decode G (vertices out)
           (vertices out).length = n ∧ M.IsMatching ∧ M.IsInduced ∧
             Nat.card M.edgeSet = value out ∧
               ∀ Q : G.Subgraph, Q.IsMatching → Q.IsInduced → Nat.card Q.edgeSet ≤ value out) ∧
          (16 ≤ n → (cs.time (IndependentDomination.ofGraph G) : ℝ) ≤ (C : ℝ) *
            ((IndependentDomination.encInput (IndependentDomination.ofGraph G)).length + 1 : ℕ) ^
              e *
              (2 : ℝ) ^ ((A : ℝ) * Real.logLogSqrtLogScale n)) := by
  obtain ⟨optimize, cs, C, e, A, hs, h⟩ := exists_optimalWitness_sharp_certificate
  refine ⟨optimize, cs, C, e, 6 * A, hs, ?_⟩
  intro n G _
  refine ⟨(h G).1, fun hn => ?_⟩
  have ht : (cs.time (IndependentDomination.ofGraph G) : ℝ) ≤ (C : ℝ) *
      ((IndependentDomination.encInput (IndependentDomination.ofGraph G)).length + 1 : ℕ) ^ e *
        (2 : ℝ) ^ (A * Nat.logLogSqrtLogScale n) := by exact_mod_cast (h G).2
  exact ht.trans (mul_le_mul_of_nonneg_left
    (Nat.two_pow_mul_logLogSqrtLogScale_le A hn) (by positivity))

end Cslib.Logic.PL.InducedMatchingInterval.Maximum.Witness
