/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PolyTime.CNF.UpperDomination
public import CslibFrontier.Foundations.Combinatorics.SimpleGraph.PrivateNeighborMarks
import all CslibFrontier.Computability.PolyTime.CNF.UpperDomination
import all CslibFrontier.Computability.PolyTime.CNF.IndependentDominationInterval

/-!
# Actual unique-mark upper-domination construction

Append the pair-or-mark predicates of [ChenJiangZhu2027], Proposition 7.6 / Appendix D.3
(PDF pp.27,35). Marks become functional, so the resulting count is of original minimal dominating
sets meeting the varying signed threshold. No variables are introduced for neighbor pairs.

## Main definitions

* `complete`, `build`: actual augmented predicates and original-input construction.

## Main results

* `build_polytime`: binary polynomial construction, including every literal write.
* `representation`: exact original-set count, with unique gate/mark extensions.
* `query_budget`: two width-four queries on exactly `5v+a-1` variables, with cubic clauses.
-/

public section

namespace Cslib.Logic.PL.UpperDomination.Unique

open Turing.MultiTapeTM Cslib.Circuits.Boolean

/-- Actual positive mark term and selected distinct-neighbor pair terms for every original row. -/
@[expose] def complete (x : CoreInput) : List (DNF ℕ) :=
  (List.range (IndependentDomination.order (coreGraph x))).map fun w =>
    [[(markBase x + w, true)]] ++
      (List.range (IndependentDomination.order (coreGraph x))).flatMap fun u =>
        (List.range (IndependentDomination.order (coreGraph x))).flatMap fun v =>
          if decide (u ≠ v) && closed (coreGraph x) w u && closed (coreGraph x) w v then
            [[(u, true), (v, true)]] else []

/-- Retain all approved selection/gate/mark wires and append actual unique-mark predicates. -/
@[expose] def build (x : Input) : TwoBoundary.BinaryFrontend.Input :=
  let base := UpperDomination.build x
  (TwoBoundary.BinaryFrontend.declared base, TwoBoundary.BinaryFrontend.side base,
    TwoBoundary.BinaryFrontend.conditions base ++ complete (coreInput x))

/-- Finite pair-or-mark predicate, sharing every original selection and private-mark wire. -/
@[expose] def finiteCondition {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (a : ℕ) (w : Fin n) : DNF (Fin ((n + a) + n)) :=
  [[(mark a w, true)]] ++ (List.finRange n).flatMap fun u =>
    (List.finRange n).flatMap fun v =>
      if u ≠ v ∧ G.ClosedAdj w u ∧ G.ClosedAdj w v then
        [[(selection a u, true), (selection a v, true)]] else []
/-- Exactly one additional condition per original vertex. -/
@[expose] def finiteComplete {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (a : ℕ) : List (DNF (Fin ((n + a) + n))) :=
  (List.finRange n).map (finiteCondition G a)

/-- The bounded predicate is precisely a mark or two distinct selected closed neighbors. -/
theorem finiteComplete_eval {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (a : ℕ) (y : Fin ((n + a) + n) → Bool) :
    (∀ p ∈ finiteComplete G a, DNF.eval y p = true) ↔
      ∀ w, y (mark a w) = true ∨ ∃ u, y (selection a u) = true ∧
        ∃ v, y (selection a v) = true ∧ u ≠ v ∧ G.ClosedAdj w u ∧ G.ClosedAdj w v := by
  have he (w : Fin n) : DNF.eval y (finiteCondition G a w) = true ↔
      y (mark a w) = true ∨ ∃ u v, (u ≠ v ∧ G.ClosedAdj w u ∧ G.ClosedAdj w v) ∧
        y (selection a u) = true ∧ y (selection a v) = true := by
    simp [finiteCondition, DNF.eval_eq_true_iff, Term.eval, Literal.eval, and_assoc]
  simp only [finiteComplete, List.forall_mem_map, List.mem_finRange, forall_const]
  apply forall_congr'
  intro w
  rw [he]
  constructor
  · rintro (hw | ⟨u, v, ⟨hne, hwu, hwv⟩, hu, hv⟩)
    · exact Or.inl hw
    · exact Or.inr ⟨u, hu, v, hv, hne, hwu, hwv⟩
  · rintro (hw | ⟨u, hu, v, hv, hne, hwu, hwv⟩)
    · exact Or.inl hw
    · exact Or.inr ⟨u, v, ⟨hne, hwu, hwv⟩, hu, hv⟩

/-- Finite condition erasure is the actual original-matrix pair traversal. -/
theorem complete_ofGraph {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (a : ℕ) :
    complete (IndependentDomination.ofGraph G, n + a) =
      (finiteComplete G a).map (CNF.relabel Fin.val) := by
  simp only [complete, finiteComplete, finiteCondition, coreGraph, markBase,
    IndependentDomination.order, IndependentDomination.ofGraph,
    ← List.map_coe_finRange_eq_range, List.map_map, List.flatMap_map,
    CNF.relabel, List.map_append, List.map_flatMap, Function.comp_def]
  congr 1
  funext w
  congr 1
  congr 1
  funext u
  congr 1
  funext v
  have hc (w u : Fin n) : closed
      (n, List.ofFn fun u => List.ofFn fun v => decide (G.Adj u v)) w.val u.val =
        decide (G.ClosedAdj w u) := closed_ofGraph G w u
  simp only [hc, Bool.and_eq_true, decide_eq_true_eq, ne_eq, Fin.val_inj, and_assoc]
  split_ifs <;> rfl

/-- The additional predicates have term width at most two and exactly the original vertex count. -/
theorem complete_widths {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (a : ℕ) :
    (∀ p ∈ finiteComplete G a, ∀ t ∈ p, t.length ≤ 2) ∧
      (finiteComplete G a).length = n := by
  refine ⟨?_, by simp [finiteComplete]⟩
  intro p hp t ht
  obtain ⟨w, _, rfl⟩ := List.mem_map.mp hp
  rcases List.mem_append.mp ht with ht | ht
  · have h := List.mem_singleton.mp ht
    subst t
    simp
  · simp only [List.mem_flatMap, List.mem_finRange, true_and] at ht
    obtain ⟨u, v, ht⟩ := ht
    split_ifs at ht <;> simp_all

private theorem complete_polytime : ComputableInPolyTime complete encCore
    (encList VCOne.encSignedCNF) := by
  have hn : ComputableInPolyTime (fun x => IndependentDomination.order (coreGraph x))
      encCore encUnary := by
    unfold coreGraph encCore IndependentDomination.order IndependentDomination.encInput; fun_prop
  unfold complete
  apply ComputableInPolyTime.mapWithInput (ComputableInPolyTime.range.comp hn)
  have hmark : ComputableInPolyTime (fun p : CoreInput × ℕ => markBase p.1 + p.2)
      (encPair encCore encUnary) encNat :=
    ComputableInPolyTime.unary_to_binary.comp (by unfold markBase encCore; fun_prop)
  have hfirst : ComputableInPolyTime (fun p : CoreInput × ℕ => [[(markBase p.1 + p.2, true)]])
      (encPair encCore encUnary) VCOne.encSignedCNF := by
    unfold VCOne.encSignedCNF; fun_prop
  apply ComputableInPolyTime.listAppend' hfirst
  apply ComputableInPolyTime.flatMapWithInput
    (ComputableInPolyTime.range.comp (hn.comp (ComputableInPolyTime.fst _ _)))
  apply ComputableInPolyTime.flatMapWithInput
    (ComputableInPolyTime.range.comp (hn.comp ((ComputableInPolyTime.fst _ _).comp
      (ComputableInPolyTime.fst _ _))))
  let ei := encPair (encPair (encPair encCore encUnary) encUnary) encUnary
  have hwu := closed_polytime.comp (show ComputableInPolyTime
    (fun p : ((CoreInput × ℕ) × ℕ) × ℕ => (coreGraph p.1.1.1, p.1.1.2, p.1.2)) ei
      (encPair IndependentDomination.encInput (encPair encUnary encUnary)) from by
        unfold coreGraph ei encCore; fun_prop)
  have hwv := closed_polytime.comp (show ComputableInPolyTime
    (fun p : ((CoreInput × ℕ) × ℕ) × ℕ => (coreGraph p.1.1.1, p.1.1.2, p.2)) ei
      (encPair IndependentDomination.encInput (encPair encUnary encUnary)) from by
        unfold coreGraph ei encCore; fun_prop)
  have hne : ComputableInPolyTime (fun p : ((CoreInput × ℕ) × ℕ) × ℕ => decide (p.1.2 ≠ p.2))
      ei encBool := by unfold ei; fun_prop
  have hu : ComputableInPolyTime (fun p : ((CoreInput × ℕ) × ℕ) × ℕ => p.1.2) ei encNat :=
    ComputableInPolyTime.unary_to_binary.comp (by unfold ei; fun_prop)
  have hv : ComputableInPolyTime (fun p : ((CoreInput × ℕ) × ℕ) × ℕ => p.2) ei encNat :=
    ComputableInPolyTime.unary_to_binary.comp (by unfold ei; fun_prop)
  have htest : ComputableInPolyTime (fun p : ((CoreInput × ℕ) × ℕ) × ℕ =>
      decide (p.1.2 ≠ p.2) && closed (coreGraph p.1.1.1) p.1.1.2 p.1.2 &&
        closed (coreGraph p.1.1.1) p.1.1.2 p.2) ei encBool := by fun_prop
  have hbody : ComputableInPolyTime (fun p : ((CoreInput × ℕ) × ℕ) × ℕ =>
      [[(p.1.2, true), (p.2, true)]])
      ei (encList (encList (encPair encNat encBool))) := by fun_prop
  exact (htest.ite' hbody (.const [])).of_enc_eq fun _ => rfl

/-- Actual augmented predicate writing and original normalization/gate construction are binary
polynomial-time. There is no enumerated assignment family, supplied mark word or runtime advice. -/
@[fun_prop] theorem build_polytime : ComputableInPolyTime build encInput
    TwoBoundary.BinaryFrontend.encInput := by
  have hg : ComputableInPolyTime graph encInput IndependentDomination.encInput := by
    unfold graph encInput; fun_prop
  have hn : ComputableInPolyTime (fun x => IndependentDomination.order (graph x))
      encInput encUnary := by
    unfold graph encInput IndependentDomination.order IndependentDomination.encInput; fun_prop
  have ha := IndependentDominationInterval.auxiliary_polytime.comp normalize_polytime
  have hcore : ComputableInPolyTime coreInput encInput encCore :=
    hg.prod (ComputableInPolyTime.unary_add.comp (hn.prod ha))
  have hmore := complete_polytime.comp hcore
  have hbase := UpperDomination.build_polytime
  exact (hbase.fst'.prod (hbase.snd'.fst'.prod
    (ComputableInPolyTime.listAppend' hbase.snd'.snd' hmore))).of_enc_eq fun _ => rfl
open Classical in
/-- Gate and complete-mark words have the actual augmented formula semantics. -/
private theorem representation_words {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (k : ℤ) :
    let a := (CardinalityInterval.circuit n k.toNat n).size
    ∃ B : CNF (Fin ((n + a) + n)), ∃ P : List (DNF (Fin ((n + a) + n))),
      build (ofGraph G k) = TwoBoundary.BinaryFrontend.ofFinite B P ∧
      (∀ q ∈ B, q.length ≤ 3) ∧ (∀ p ∈ P, ∀ t ∈ p, t.length ≤ 2) ∧ P.length = 3 * n ∧
      Fintype.card {y : Fin ((n + a) + n) → Bool //
        B.eval y = true ∧ ∀ p ∈ P, DNF.eval y p = true} =
        Fintype.card {p : (Fin n → Bool) × (Fin n → Bool) //
          G.IsCompletePrivateMarking {u | p.1 u = true} {w | p.2 w = true} ∧
            k.toNat ≤ Cslib.BitString.weight p.1 ∧ Cslib.BitString.weight p.1 ≤ n} := by
  generalize hc : CardinalityInterval.circuit n k.toNat n = c
  let a := c.size
  obtain ⟨_, hCbounds⟩ := CardinalityInterval.formula_bounds n k.toNat n
  rw [hc] at hCbounds
  obtain ⟨F, hF⟩ := IndependentDominationInterval.lift_cnf
    (CardinalityInterval.formula (n, k.toNat, n)) (fun q hq => (hCbounds q hq).2)
  let B := F.relabel (Fin.castAdd n) ++ finiteUpper G a
  let oldP := finiteDomination G a ++ finiteWitnesses G a
  let P := oldP ++ finiteComplete G a
  have haux : auxiliary (ofGraph G k) = c.size := by
    change IndependentDominationInterval.auxiliary
      (IndependentDominationInterval.ofGraph G k.toNat n) = _
    rw [IndependentDominationInterval.auxiliary_ofGraph, hc]
  have hNF : CNF.relabel Fin.val B = CardinalityInterval.formula (n, k.toNat, n) ++
      upper (IndependentDomination.ofGraph G, n + a) := by
    simp only [B, CNF.relabel, List.map_append, List.map_map, Clause.relabel, Function.comp_def]
    rw [← hF, upper_ofGraph]
    rfl
  have hD := congrArg TwoBoundary.BinaryFrontend.conditions (IndependentDomination.build_ofGraph G)
  change IndependentDomination.coverage (IndependentDomination.ofGraph G) =
    (IndependentDomination.finiteCoverage G).map (CNF.relabel Fin.val) at hD
  have hDom : (finiteDomination G a).map (CNF.relabel Fin.val) =
      IndependentDomination.coverage (IndependentDomination.ofGraph G) := by
    rw [hD]
    simp only [finiteDomination, List.map_map, CNF.relabel, Clause.relabel, Function.comp_def]
    rfl
  have hPF : P.map (CNF.relabel Fin.val) = (IndependentDomination.coverage
      (IndependentDomination.ofGraph G) ++ witnesses (IndependentDomination.ofGraph G, n + a)) ++
        complete (IndependentDomination.ofGraph G, n + a) := by
    simp only [P, oldP, List.map_append, hDom, witnesses_ofGraph, complete_ofGraph]
  obtain ⟨hU, hOld, hOldLen⟩ := UpperDomination.widths G a
  have hP : ∀ p ∈ P, ∀ t ∈ p, t.length ≤ 2 := by
    intro p hp t ht
    rcases List.mem_append.mp hp with hp | hp
    · exact (hOld p hp t ht).trans (by omega)
    · exact (complete_widths G a).1 p hp t ht
  have hplen : P.length = 3 * n := by
    simp only [P, List.length_append, (complete_widths G a).2]
    change (finiteDomination G a ++ finiteWitnesses G a).length + n = 3 * n
    omega
  refine ⟨B, P, ?_, ?_, hP, hplen, ?_⟩
  · have hgraph : graph (ofGraph G k) = IndependentDomination.ofGraph G := rfl
    have horder : IndependentDomination.order (IndependentDomination.ofGraph G) = n := rfl
    have hcard : cardinalityInput (ofGraph G k) = (n, k.toNat, n) := rfl
    simp only [build, UpperDomination.build, TwoBoundary.BinaryFrontend.declared,
      TwoBoundary.BinaryFrontend.side, TwoBoundary.BinaryFrontend.conditions,
      coreInput, hgraph, horder, haux, hcard,
      TwoBoundary.BinaryFrontend.ofFinite]
    rw [← hNF, ← hPF]
  · intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · obtain ⟨q0, hq0, rfl⟩ := List.mem_map.mp hq
      have hmem : q0.relabel Fin.val ∈ CardinalityInterval.formula (n, k.toNat, n) := by
        rw [← hF]; exact List.mem_map.mpr ⟨q0, hq0, rfl⟩
      have hh := (hCbounds _ hmem).1
      simp only [Clause.relabel, List.length_map] at hh ⊢
      omega
    · exact hU q hq
  · simp only [← Nat.card_eq_fintype_card]
    have hFE (ν : Fin (n + a) → Bool) : F.eval ν =
        (CardinalityInterval.formula (n, k.toNat, n)).eval
          (Function.extend Fin.val ν (fun _ => false)) := by
      rw [← hF, CNF.eval_relabel, Function.extend_comp Fin.val_injective]
    have hPred (y : Fin ((n + a) + n) → Bool) :
        B.eval y = true ∧ (∀ p ∈ P, DNF.eval y p = true) ↔
        (CardinalityInterval.formula (n, k.toNat, n)).eval
          (Function.extend Fin.val (fun j => y (Fin.castAdd n j)) (fun _ => false)) = true ∧
        G.IsCompletePrivateMarking {u | y (selection a u) = true} {w | y (mark a w) = true} := by
      simp only [B, P, oldP, CNF.eval_append, Bool.and_eq_true, CNF.eval_relabel,
        List.forall_mem_append, hFE]
      rw [SimpleGraph.IsCompletePrivateMarking, ← finite_semantics G a y]
      simp only [Set.mem_ofPred_eq]
      rw [← finiteComplete_eval G a y]
      simp only [List.forall_mem_append]
      tauto
    have haccept (σ : Fin n → Bool) : c.eval interpretation σ = CardinalityInterval.wanted ↔
        k.toNat ≤ Cslib.BitString.weight σ ∧ Cslib.BitString.weight σ ≤ n := by
      have h := CardinalityInterval.circuit_accepts n k.toNat n σ
      rwa [hc] at h
    calc
      _ = Nat.card {y : Fin ((n + c.size) + n) → Bool //
          (FunctionalCNF.write (FunctionalCNF.ofCircuit c CardinalityInterval.wanted)).eval
            (Function.extend Fin.val (fun j => y (Fin.castAdd n j)) (fun _ => false)) = true ∧
          G.IsCompletePrivateMarking {u | y (selection c.size u) = true}
            {w | y (mark c.size w) = true}} := by
        apply Nat.card_congr
        apply Equiv.subtypeEquivRight
        intro y
        simpa only [CardinalityInterval.formula, CardinalityInterval.payload_eq, hc] using hPred y
      _ = Nat.card {p : (Fin n → Bool) × (Fin n → Bool) //
          c.eval interpretation p.2 = CardinalityInterval.wanted ∧
          G.IsCompletePrivateMarking {u | p.2 u = true} {w | p.1 w = true}} :=
        FunctionalCNF.count_extensions_appended c CardinalityInterval.wanted n
          (fun (μ : Fin n → Bool) (σ : Fin n → Bool) =>
            G.IsCompletePrivateMarking {u | σ u = true} {w | μ w = true})
      _ = _ := by
        apply Nat.card_congr
        apply (Equiv.prodComm _ _).subtypeEquiv
        intro p
        rw [haccept]
        constructor
        · rintro ⟨⟨hl, hu⟩, hm⟩; exact ⟨hm, hl, hu⟩
        · rintro ⟨hm, hl, hu⟩; exact ⟨⟨hl, hu⟩, hm⟩

open Classical in
/-- Original Boolean words biject with ordinary set–marking pairs, preserving the signed size
bound. Gate values and owners are absent from this source object type. -/
private theorem word_count_eq_pairs {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℤ) :
    Fintype.card {p : (Fin n → Bool) × (Fin n → Bool) //
      G.IsCompletePrivateMarking {u | p.1 u = true} {w | p.2 w = true} ∧
        k.toNat ≤ Cslib.BitString.weight p.1 ∧ Cslib.BitString.weight p.1 ≤ n} =
      Fintype.card {p : Set (Fin n) × Set (Fin n) //
        G.IsCompletePrivateMarking p.1 p.2 ∧ k ≤ (Nat.card p.1 : ℤ)} := by
  have hw (σ : Fin n → Bool) : Cslib.BitString.weight σ = Nat.card {u | σ u = true} := by
    rw [Cslib.BitString.weight_eq_card_subtype, ← Nat.card_eq_fintype_card]
    rfl
  let f : {p : (Fin n → Bool) × (Fin n → Bool) //
      G.IsCompletePrivateMarking {u | p.1 u = true} {w | p.2 w = true} ∧
        k.toNat ≤ Cslib.BitString.weight p.1 ∧ Cslib.BitString.weight p.1 ≤ n} →
      {p : Set (Fin n) × Set (Fin n) // G.IsCompletePrivateMarking p.1 p.2 ∧
        k ≤ (Nat.card p.1 : ℤ)} := fun p =>
    ⟨({u | p.val.1 u = true}, {w | p.val.2 w = true}), p.property.1,
      Int.toNat_le.mp (by simpa only [← hw] using p.property.2.1)⟩
  apply Fintype.card_of_bijective (f := f)
  constructor
  · intro x y he
    apply Subtype.ext
    apply Prod.ext
    · funext u
      have hh := Set.ext_iff.mp (congrArg (fun z => z.val.1) he) u
      change (x.val.1 u = true) ↔ (y.val.1 u = true) at hh
      cases hx : x.val.1 u <;> cases hy : y.val.1 u <;> simp_all
    · funext u
      have hh := Set.ext_iff.mp (congrArg (fun z => z.val.2) he) u
      change (x.val.2 u = true) ↔ (y.val.2 u = true) at hh
      cases hx : x.val.2 u <;> cases hy : y.val.2 u <;> simp_all
  · rintro ⟨⟨S, W⟩, hmark, hk⟩
    let σ (u : Fin n) := decide (u ∈ S)
    let μ (w : Fin n) := decide (w ∈ W)
    have hS : {u | σ u = true} = S := by ext u; simp [σ]
    have hW : {w | μ w = true} = W := by ext w; simp [μ]
    refine ⟨⟨(σ, μ), ?_, ?_, Cslib.BitString.weight_le_length σ⟩, ?_⟩
    · simpa only [hS, hW] using hmark
    · rw [hw, hS]
      exact Int.toNat_le.mpr hk
    · apply Subtype.ext
      exact Prod.ext hS hW

open Classical in
private theorem word_count_eq_sets {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℤ) :
    Fintype.card {p : (Fin n → Bool) × (Fin n → Bool) //
      G.IsCompletePrivateMarking {u | p.1 u = true} {w | p.2 w = true} ∧
        k.toNat ≤ Cslib.BitString.weight p.1 ∧ Cslib.BitString.weight p.1 ≤ n} =
      Fintype.card {S : Set (Fin n) // Minimal G.IsDominatingSet S ∧ k ≤ (Nat.card S : ℤ)} := by
  rw [word_count_eq_pairs, ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
  exact G.card_completePrivateMarking (fun S => k ≤ (Nat.card S : ℤ))

open Classical in
/-- The actual augmented writer counts each original minimal dominating set exactly once.
Unique gate traces and complete private marks are derived, not supplied as input advice. -/
theorem representation {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k : ℤ) :
    let a := (CardinalityInterval.circuit n k.toNat n).size
    ∃ B : CNF (Fin ((n + a) + n)), ∃ P : List (DNF (Fin ((n + a) + n))),
      build (ofGraph G k) = TwoBoundary.BinaryFrontend.ofFinite B P ∧
      (∀ c ∈ B, c.length ≤ 3) ∧ (∀ p ∈ P, ∀ t ∈ p, t.length ≤ 2) ∧ P.length = 3 * n ∧
      Fintype.card {y : Fin ((n + a) + n) → Bool //
        B.eval y = true ∧ ∀ p ∈ P, DNF.eval y p = true} =
        Fintype.card {S : Set (Fin n) // Minimal G.IsDominatingSet S ∧ k ≤ (Nat.card S : ℤ)} := by
  obtain ⟨B, P, he, hb, hp, hl, hc⟩ := representation_words G k
  exact ⟨B, P, he, hb, hp, hl, hc.trans (word_count_eq_sets G k)⟩

/-- Pair enumeration contributes at most one term per ordered distinct-neighbor candidate. -/
theorem complete_volumes {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (a : ℕ) :
    ((finiteComplete G a).map List.length).sum ≤ n ^ 3 + n := by
  have hw (w : Fin n) : (finiteCondition G a w).length ≤ n ^ 2 + 1 := by
    simp only [finiteCondition, List.length_append, List.length_cons, List.length_nil,
      List.length_flatMap, List.finRange, List.map_ofFn, List.sum_ofFn, Function.comp_def]
    calc
      _ ≤ 1 + ∑ _u : Fin n, ∑ _v : Fin n, 1 := by
        apply Nat.add_le_add_left
        apply Finset.sum_le_sum
        intro u _
        apply Finset.sum_le_sum
        intro v _
        split_ifs <;> simp
      _ = _ := by simp; ring
  simp only [finiteComplete, List.finRange, List.map_ofFn,
    List.sum_ofFn, Function.comp_def]
  calc
    _ ≤ ∑ _w : Fin n, (n ^ 2 + 1) := Finset.sum_le_sum fun w _ => hw w
    _ = _ := by simp; ring

/-- Positive graphs produce exactly the source's two ordinary boundary queries. -/
theorem query_count {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k : ℤ)
    (hn : 1 ≤ n) :
    (TwoBoundary.BinaryFrontend.queries
      (TwoBoundary.BinaryFrontend.compile (build (ofGraph G k)))).length = 2 := by
  obtain ⟨B, P, he, _, _, hl, _⟩ := representation G k
  rw [he, TwoBoundary.BinaryFrontend.compile_query_count]
  have hem : P.isEmpty ≠ true := by
    intro hp
    have hz := List.isEmpty_iff_length_eq_zero.mp hp
    omega
  simp only [TwoBoundary.BinaryFrontend.conditions, TwoBoundary.BinaryFrontend.ofFinite,
    List.isEmpty_map, hem, Bool.false_eq_true, ↓reduceIte]

/-- Actual source query budgets, including every cardinality gate and literal label. -/
theorem query_budget {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k : ℤ)
    (hn : 1 ≤ n) (N : ℕ) (q : CNF ℕ)
    (hq : (N, q) ∈ TwoBoundary.BinaryFrontend.queries
      (TwoBoundary.BinaryFrontend.compile (build (ofGraph G k)))) :
    N = 5 * n + (CardinalityInterval.circuit n k.toNat n).size - 1 ∧
      q.length ≤ 3 * n ^ 3 + 4 * n ^ 2 + 4 * n + 2 + 2856 * (n + 1) ∧
      ∀ c ∈ q, c.length ≤ 4 ∧ ∀ l ∈ c, l.1 < N := by
  classical
  obtain ⟨B, P, he, hb, hp, hl, _⟩ := representation G k
  rw [he] at hq
  obtain ⟨hN, hM, hW⟩ := TwoBoundary.BinaryFrontend.compile_budget B P hb hp N q hq
  have hem : P.isEmpty ≠ true := by
    intro hs
    have hz := List.isEmpty_iff_length_eq_zero.mp hs
    omega
  simp only [hem, Bool.false_eq_true, ↓reduceIte] at hN
  let a := (CardinalityInterval.circuit n k.toNat n).size
  have haux : auxiliary (ofGraph G k) = a := by
    exact IndependentDominationInterval.auxiliary_ofGraph G k.toNat n
  have hB := congrArg (fun x => (TwoBoundary.BinaryFrontend.side x).length) he
  change (CardinalityInterval.formula (n, k.toNat, n) ++
    upper (coreInput (ofGraph G k))).length = (CNF.relabel Fin.val B).length at hB
  have hcore : coreInput (ofGraph G k) = (IndependentDomination.ofGraph G, n + a) := by
    simp only [coreInput, haux]
    rfl
  rw [hcore, upper_ofGraph] at hB
  simp only [List.length_append, CNF.relabel, List.length_map] at hB
  have hP := congrArg (fun x => ((TwoBoundary.BinaryFrontend.conditions x).map List.length).sum) he
  change ((IndependentDomination.coverage (IndependentDomination.ofGraph G) ++
    witnesses (coreInput (ofGraph G k)) ++ complete (coreInput (ofGraph G k))).map
      List.length).sum =
      ((P.map (CNF.relabel Fin.val)).map List.length).sum at hP
  have hD := congrArg TwoBoundary.BinaryFrontend.conditions (IndependentDomination.build_ofGraph G)
  change IndependentDomination.coverage (IndependentDomination.ofGraph G) =
    (IndependentDomination.finiteCoverage G).map (CNF.relabel Fin.val) at hD
  rw [hcore, witnesses_ofGraph, complete_ofGraph, hD] at hP
  simp only [List.map_append, List.map_map, List.sum_append, CNF.relabel,
    List.length_map, Function.comp_def] at hP
  change ((IndependentDomination.finiteCoverage G).map List.length).sum +
    ((finiteWitnesses G a).map List.length).sum +
      ((finiteComplete G a).map List.length).sum = (P.map List.length).sum at hP
  obtain ⟨hu, hpterms⟩ := UpperDomination.volumes G a
  have hMore := complete_volumes G a
  simp only [finiteDomination, List.map_append, List.map_map, List.sum_append,
    CNF.relabel, List.length_map, Function.comp_def] at hpterms
  change ((IndependentDomination.finiteCoverage G).map List.length).sum +
    ((finiteWitnesses G a).map List.length).sum ≤ 2 * n ^ 2 + n at hpterms
  have hc := (CardinalityInterval.formula_bounds n k.toNat n).1
  refine ⟨by omega, by omega, by simpa using hW⟩

/-- The source cubic clause bound, uniformly over the binary input threshold. -/
theorem query_cubic_budget {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k : ℤ)
    (hn : 1 ≤ n) (N : ℕ) (q : CNF ℕ)
    (hq : (N, q) ∈ TwoBoundary.BinaryFrontend.queries
      (TwoBoundary.BinaryFrontend.compile (build (ofGraph G k)))) : q.length ≤ 6000 * n ^ 3 := by
  have h := (query_budget G k hn N q hq).2.1
  have hn2 : n ≤ n ^ 2 := by simpa only [pow_two] using Nat.le_mul_of_pos_right n hn
  have hn3 : n ^ 2 ≤ n ^ 3 := by
    calc n ^ 2 ≤ n ^ 2 * n := Nat.le_mul_of_pos_right _ hn
      _ = n ^ 3 := by ring
  nlinarith

end Cslib.Logic.PL.UpperDomination.Unique
