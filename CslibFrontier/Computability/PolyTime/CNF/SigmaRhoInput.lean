/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PolyTime.CNF.SigmaRho
import all CslibFrontier.Computability.PolyTime.CNF.IndependentDominationInterval

/-!
# Original-input fixed degree-rule construction with binary size bounds

The cutoff/rules and choice of size testing are fixed problem parameters. The explicit graph and
binary bounds vary. No supplied threshold array, size circuit or rank is accepted as advice.
Source: [ChenJiangZhu2027], Corollary 7.2 / Appendix C.2 (PDF pp.24–25,31–32).
-/

public section

namespace Cslib.Logic.PL.SigmaRho.BinaryFrontend

open Turing.MultiTapeTM Cslib.Circuits.Boolean DegreeThreshold

/-- Explicit original matrix, unary declaration and binary natural interval bounds. -/
abbrev Input := IndependentDominationInterval.Input
/-- Original graph, with no threshold wires installed by the caller. -/
@[expose] def original := IndependentDominationInterval.graph
/-- Inclusive binary lower bound. -/
@[expose] def lower := IndependentDominationInterval.lower
/-- Inclusive binary upper bound. -/
@[expose] def upper := IndependentDominationInterval.upper
/-- Full original runtime input encoding. -/
@[expose] def encInput := IndependentDominationInterval.encInput
/-- Actual generated gate count; without tests no gate is introduced. -/
@[expose] def auxiliary (active : Bool) (x : Input) : ℕ :=
  if active then IndependentDominationInterval.auxiliary x else 0
/-- Actual functional interval clauses, or no size constraint. -/
@[expose] def sizeFormula (active : Bool) (x : Input) : CNF ℕ :=
  if active then CardinalityInterval.formula (IndependentDominationInterval.cardinalityInput x)
  else []
/-- Compute the first threshold wire after the original inputs and actual size gates. -/
@[expose] def core (active : Bool) (x : Input) : Core :=
  (original x, IndependentDomination.order (original x) + auxiliary active x)
/-- Complete executable original-input threshold/rule/size construction. -/
@[expose] def build (D : ℕ) (σ ρ : SimpleGraph.DegreeRule D) (active : Bool)
    (x : Input) : TwoBoundary.BinaryFrontend.Input :=
  (IndependentDomination.order (original x) + auxiliary active x +
      D * IndependentDomination.order (original x),
    sizeFormula active x ++ forward D (core active x) ++ rules D σ ρ (core active x),
    reverse D (core active x))
/-- Canonical original graph and input-varying size bounds. -/
@[expose] def ofGraph {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (lo hi : ℕ) :
    Input := IndependentDominationInterval.ofGraph G lo hi
/-- No bounds are imposed in the no-test variant; otherwise use the actual input interval. -/
@[expose] def InBounds (active : Bool) (lo hi k : ℕ) : Prop := active = true → lo ≤ k ∧ k ≤ hi

private theorem aux_polytime (active : Bool) :
    ComputableInPolyTime (auxiliary active) encInput encUnary := by
  cases active
  · exact .const 0
  · exact IndependentDominationInterval.auxiliary_polytime

private theorem size_polytime (active : Bool) :
    ComputableInPolyTime (sizeFormula active) encInput VCOne.encSignedCNF := by
  cases active
  · exact .const []
  · exact CardinalityInterval.formula_polytime.comp
      IndependentDominationInterval.cardinalityInput_polytime

/-- Actual normalization, size generation, threshold subsets, state clauses and binary writes. -/
@[fun_prop] theorem build_polytime (D : ℕ) (σ ρ : SimpleGraph.DegreeRule D) (active : Bool) :
    ComputableInPolyTime (build D σ ρ active) encInput TwoBoundary.BinaryFrontend.encInput := by
  have hg : ComputableInPolyTime original encInput IndependentDomination.encInput := by
    unfold original encInput IndependentDominationInterval.graph
      IndependentDominationInterval.encInput; fun_prop
  have hn : ComputableInPolyTime (fun x => IndependentDomination.order (original x))
      encInput encUnary := by
    unfold original encInput IndependentDominationInterval.graph
      IndependentDominationInterval.encInput IndependentDomination.order
      IndependentDomination.encInput; fun_prop
  have ha := aux_polytime active
  have hc : ComputableInPolyTime (core active) encInput encCore :=
    hg.prod (ComputableInPolyTime.unary_add.comp (hn.prod ha))
  have hf := (forward_polytime D).comp hc
  have hr := (rules_polytime D σ ρ).comp hc
  have hp := (reverse_polytime D).comp hc
  have hs := size_polytime active
  have hN : ComputableInPolyTime (fun x => IndependentDomination.order (original x) +
      auxiliary active x + D * IndependentDomination.order (original x)) encInput encUnary := by
    fun_prop
  exact (hN.prod ((ComputableInPolyTime.listAppend'
    (ComputableInPolyTime.listAppend' hs hf) hr).prod hp)).of_enc_eq fun _ => rfl

/-- The actual auxiliary declaration is derived from the size circuit, not input advice. -/
theorem auxiliary_ofGraph {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (active : Bool) (lo hi : ℕ) : auxiliary active (ofGraph G lo hi) =
      if active then (CardinalityInterval.circuit n lo hi).size else 0 := by
  cases active
  · rfl
  · exact IndependentDominationInterval.auxiliary_ofGraph G lo hi

/-- Generated interval gates remain linear, uniformly over binary input bounds. -/
theorem auxiliary_bound {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (active : Bool) (lo hi : ℕ) : auxiliary active (ofGraph G lo hi) ≤ 952 * (n + 1) := by
  rw [auxiliary_ofGraph]
  cases active
  · simp
  · exact CardinalityInterval.size_circuit n lo hi


open Classical in
private theorem core_representation {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (D : ℕ) (hD : 1 ≤ D) (σ ρ : SimpleGraph.DegreeRule D) (active : Bool) (lo hi a : ℕ)
    (ha : auxiliary active (ofGraph G lo hi) = a) (F : CNF (Fin (n + a)))
    (hF : sizeFormula active (ofGraph G lo hi) = F.relabel Fin.val)
    (hw : ∀ c ∈ F, c.length ≤ 3) :
    ∃ B : CNF (Fin ((n + a) + D * n)), ∃ P : List (DNF (Fin ((n + a) + D * n))),
      build D σ ρ active (ofGraph G lo hi) = TwoBoundary.BinaryFrontend.ofFinite B P ∧
      (∀ c ∈ B, c.length ≤ max (D + 1) 3) ∧ (∀ p ∈ P, ∀ t ∈ p, t.length ≤ D) ∧
      P.length = D * n ∧
      Nat.card {y : Fin ((n + a) + D * n) → Bool //
        B.eval y = true ∧ ∀ p ∈ P, DNF.eval y p = true} =
      Nat.card {x : Fin (n + a) → Bool // F.eval x = true ∧
        G.IsSigmaRhoSet σ.counts ρ.counts {u | x (Fin.castAdd a u) = true}} := by
  let e := wireEquiv n D a
  let B := (finiteBase G D hD σ ρ a F).relabel e
  let P := (finiteReverse G D a).map (CNF.relabel e)
  have hmap (T : CNF (Vars n D a)) : (T.relabel e).relabel Fin.val =
      T.relabel (fun v => (e v).val) := by
    simp only [CNF.relabel, Clause.relabel, List.map_map, Function.comp_def]
    rfl
  have hprefix : (F.relabel (Sum.inl : Fin (n + a) → Vars n D a)).relabel
      (fun v => (e v).val) = F.relabel Fin.val := by
    simp only [CNF.relabel, Clause.relabel, List.map_map, Function.comp_def]
    rfl
  have hBE : B.relabel Fin.val = F.relabel Fin.val ++
      forward D (IndependentDomination.ofGraph G, n + a) ++
        rules D σ ρ (IndependentDomination.ofGraph G, n + a) := by
    rw [hmap]
    simp only [finiteBase, CNF.relabel, List.map_append]
    change (F.relabel (Sum.inl : Fin (n + a) → Vars n D a)).relabel
      (fun v => (e v).val) ++ (finiteForward G D a).relabel (fun v => (e v).val) ++
        (finiteRules D hD σ ρ a).relabel (fun v => (e v).val) = _
    exact congrArg₂ List.append
      (congrArg₂ List.append hprefix (forward_ofGraph G D a).symm)
      (rules_ofGraph G D hD σ ρ a).symm
  have hPE : P.map (CNF.relabel Fin.val) =
      reverse D (IndependentDomination.ofGraph G, n + a) := by
    simp only [P, List.map_map]
    change (finiteReverse G D a).map (fun p => CNF.relabel Fin.val (CNF.relabel e p)) = _
    simp only [hmap]
    exact (reverse_ofGraph G D a).symm
  obtain ⟨hf, hTerms, hl⟩ := DegreeThreshold.widths G D a hD
  refine ⟨B, P, ?_, ?_, ?_, ?_, ?_⟩
  · have hg : original (ofGraph G lo hi) = IndependentDomination.ofGraph G := rfl
    have hn : IndependentDomination.order (IndependentDomination.ofGraph G) = n := rfl
    have hc : core active (ofGraph G lo hi) = (IndependentDomination.ofGraph G, n + a) := by
      simp only [core, hg, hn, ha]
    simp only [build, hg, hn, ha, hc, hF, TwoBoundary.BinaryFrontend.ofFinite]
    rw [← hBE, ← hPE]
  · intro c hc
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hc
    simp only [Clause.relabel, List.length_map]
    rcases List.mem_append.mp hq with hq | hq
    · rcases List.mem_append.mp hq with hq | hq
      · obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hq
        simpa only [Clause.relabel, List.length_map] using (hw t ht).trans (le_max_right _ _)
      · exact (hf q hq).trans (le_max_left _ _)
    · exact (rule_widths hD σ ρ a q hq).trans (le_max_right _ _)
  · intro p hp t ht
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
    simpa only [Clause.relabel, List.length_map] using hTerms q hq s hs
  · simpa only [P, List.length_map] using hl
  · exact (count_relabel _ _).trans (count_extensions G D hD σ ρ a F)


open Classical in
private theorem word_count {n D : ℕ} (G : SimpleGraph (Fin n))
    (σ ρ : SimpleGraph.DegreeRule D) (active : Bool) (lo hi : ℕ) :
    Nat.card {x : Fin n → Bool // G.IsSigmaRhoSet σ.counts ρ.counts {u | x u = true} ∧
      InBounds active lo hi (Cslib.BitString.weight x)} =
      Nat.card {S : Set (Fin n) // G.IsSigmaRhoSet σ.counts ρ.counts S ∧
        InBounds active lo hi (Nat.card S)} := by
  have hw (x : Fin n → Bool) : Cslib.BitString.weight x = Nat.card {u | x u = true} := by
    rw [Cslib.BitString.weight_eq_card_subtype, ← Nat.card_eq_fintype_card]
    rfl
  let f : {x : Fin n → Bool // G.IsSigmaRhoSet σ.counts ρ.counts {u | x u = true} ∧
      InBounds active lo hi (Cslib.BitString.weight x)} →
      {S : Set (Fin n) // G.IsSigmaRhoSet σ.counts ρ.counts S ∧
        InBounds active lo hi (Nat.card S)} :=
    fun x => ⟨{u | x.val u = true}, x.property.1, by simpa only [← hw] using x.property.2⟩
  apply Nat.card_congr
  apply Equiv.ofBijective f
  constructor
  · intro x y he
    apply Subtype.ext
    funext u
    have hh := Set.ext_iff.mp (congrArg Subtype.val he) u
    change (x.val u = true) ↔ (y.val u = true) at hh
    cases hx : x.val u <;> cases hy : y.val u <;> simp_all
  · rintro ⟨S, hs, hb⟩
    let x (u : Fin n) := decide (u ∈ S)
    have hS : {u | x u = true} = S := by ext u; simp [x]
    refine ⟨⟨x, ?_, ?_⟩, ?_⟩
    · simpa only [hS] using hs
    · simpa only [hw, hS] using hb
    · apply Subtype.ext
      exact hS

open Classical in
private theorem size_representation {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (D : ℕ) (σ ρ : SimpleGraph.DegreeRule D) (active : Bool) (lo hi : ℕ) :
    ∃ a : ℕ, ∃ F : CNF (Fin (n + a)), auxiliary active (ofGraph G lo hi) = a ∧
      sizeFormula active (ofGraph G lo hi) = F.relabel Fin.val ∧
      (∀ c ∈ F, c.length ≤ 3) ∧
      Nat.card {x : Fin (n + a) → Bool // F.eval x = true ∧
        G.IsSigmaRhoSet σ.counts ρ.counts {u | x (Fin.castAdd a u) = true}} =
      Nat.card {x : Fin n → Bool // G.IsSigmaRhoSet σ.counts ρ.counts {u | x u = true} ∧
        InBounds active lo hi (Cslib.BitString.weight x)} := by
  cases active with
  | false =>
    refine ⟨0, [], rfl, rfl, by simp, ?_⟩
    apply Nat.card_congr
    exact (Equiv.refl _).subtypeEquiv fun _ => by simp [InBounds]
  | true =>
    let c := CardinalityInterval.circuit n lo hi
    let a := c.size
    have hb := (CardinalityInterval.formula_bounds n lo hi).2
    obtain ⟨F, hF⟩ := IndependentDominationInterval.lift_cnf
      (CardinalityInterval.formula (n, lo, hi)) (fun q hq => (hb q hq).2)
    have hw : ∀ q ∈ F, q.length ≤ 3 := by
      intro q hq
      have hm : q.relabel Fin.val ∈ CardinalityInterval.formula (n, lo, hi) := by
        rw [← hF]; exact List.mem_map.mpr ⟨q, hq, rfl⟩
      have hh := (hb _ hm).1
      simpa only [Clause.relabel, List.length_map] using hh.le
    refine ⟨a, F, IndependentDominationInterval.auxiliary_ofGraph G lo hi, hF.symm, hw, ?_⟩
    have hFE (x : Fin (n + a) → Bool) : F.eval x =
        (CardinalityInterval.formula (n, lo, hi)).eval
          (Function.extend Fin.val x (fun _ => false)) := by
      rw [← hF, CNF.eval_relabel, Function.extend_comp Fin.val_injective]
    calc
      _ = Nat.card {x : Fin (n + a) → Bool //
          (FunctionalCNF.write (FunctionalCNF.ofCircuit c CardinalityInterval.wanted)).eval
            (Function.extend Fin.val x (fun _ => false)) = true ∧
          G.IsSigmaRhoSet σ.counts ρ.counts {u | x (Fin.castAdd a u) = true}} := by
        apply Nat.card_congr
        apply Equiv.subtypeEquivRight
        intro x
        rw [hFE]
        simp only [CardinalityInterval.formula, CardinalityInterval.payload_eq]
        rfl
      _ = Nat.card {x : Fin n → Bool // c.eval interpretation x = CardinalityInterval.wanted ∧
          G.IsSigmaRhoSet σ.counts ρ.counts {u | x u = true}} := by
        simpa only [← Nat.card_eq_fintype_card] using FunctionalCNF.count_extensions c
          CardinalityInterval.wanted (fun x => G.IsSigmaRhoSet σ.counts ρ.counts {u | x u = true})
      _ = _ := by
        apply Nat.card_congr
        exact (Equiv.refl _).subtypeEquiv fun x => by
          have hc := CardinalityInterval.circuit_accepts n lo hi x
          change (c.eval interpretation x = CardinalityInterval.wanted ∧ _) ↔ _
          rw [hc]
          simp only [InBounds, true_implies]
          tauto

open Classical in
/-- Complete original-input representation: each selection has exactly one threshold/gate
extension, retaining its actual input size bound and ordinary sigma-rho semantics. -/
theorem representation {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (D : ℕ) (hD : 1 ≤ D) (σ ρ : SimpleGraph.DegreeRule D) (active : Bool) (lo hi : ℕ) :
    let a := auxiliary active (ofGraph G lo hi)
    ∃ B : CNF (Fin ((n + a) + D * n)), ∃ P : List (DNF (Fin ((n + a) + D * n))),
      build D σ ρ active (ofGraph G lo hi) = TwoBoundary.BinaryFrontend.ofFinite B P ∧
      (∀ c ∈ B, c.length ≤ max (D + 1) 3) ∧ (∀ p ∈ P, ∀ t ∈ p, t.length ≤ D) ∧
      P.length = D * n ∧
      Fintype.card {y : Fin ((n + a) + D * n) → Bool //
        B.eval y = true ∧ ∀ p ∈ P, DNF.eval y p = true} =
      Fintype.card {S : Set (Fin n) // G.IsSigmaRhoSet σ.counts ρ.counts S ∧
        InBounds active lo hi (Nat.card S)} := by
  obtain ⟨a, F, ha, hF, hw, hcount⟩ := size_representation G D σ ρ active lo hi
  dsimp only
  rw [ha]
  obtain ⟨B, P, he, hb, hp, hl, hc⟩ := core_representation G D hD σ ρ active lo hi a ha F hF hw
  refine ⟨B, P, he, hb, hp, hl, ?_⟩
  simpa only [Nat.card_eq_fintype_card] using
    hc.trans (hcount.trans (word_count G σ ρ active lo hi))

/-- Every nonempty graph emits exactly the two source queries; the empty graph is retained by
construction correctness and the native counter, without invoking a fictitious negative index. -/
theorem query_count {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (D : ℕ) (hD : 1 ≤ D) (σ ρ : SimpleGraph.DegreeRule D) (active : Bool) (lo hi : ℕ)
    (hn : 1 ≤ n) :
    (TwoBoundary.BinaryFrontend.queries
      (TwoBoundary.BinaryFrontend.compile (build D σ ρ active (ofGraph G lo hi)))).length = 2 := by
  classical
  obtain ⟨B, P, he, _, _, hl, _⟩ := representation G D hD σ ρ active lo hi
  have hem : P.isEmpty ≠ true := by
    intro h
    have hz := List.isEmpty_iff_length_eq_zero.mp h
    have hp := Nat.mul_pos (by omega : 0 < D) (by omega : 0 < n)
    omega
  rw [he]
  simp only [TwoBoundary.BinaryFrontend.compile, TwoBoundary.BinaryFrontend.conditions,
    TwoBoundary.BinaryFrontend.ofFinite, List.isEmpty_map, hem, Bool.false_eq_true, ↓reduceIte,
    TwoBoundary.BinaryFrontend.queries, List.length_cons, List.length_nil]

/-- Actual source variable/width budgets, with no subset variables. The constructor's separate
binary polytime proof charges enumeration and every output literal, rather than inferring runtime
from this output bound. -/
theorem query_budget {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (D : ℕ) (hD : 1 ≤ D) (σ ρ : SimpleGraph.DegreeRule D) (active : Bool) (lo hi : ℕ)
    (hn : 1 ≤ n) (N : ℕ) (q : CNF ℕ)
    (hq : (N, q) ∈ TwoBoundary.BinaryFrontend.queries
      (TwoBoundary.BinaryFrontend.compile (build D σ ρ active (ofGraph G lo hi)))) :
    N = (2 * D + 1) * n + auxiliary active (ofGraph G lo hi) - 1 ∧
      ∀ c ∈ q, c.length ≤ D + 2 ∧ ∀ l ∈ c, l.1 < N := by
  classical
  obtain ⟨B, P, he, hb, hp, hl, _⟩ := representation G D hD σ ρ active lo hi
  rw [he] at hq
  obtain ⟨hN, _, hw⟩ := TwoBoundary.BinaryFrontend.compile_budget B P hb hp N q hq
  have hem : P.isEmpty ≠ true := by
    intro h
    have hz := List.isEmpty_iff_length_eq_zero.mp h
    have hp := Nat.mul_pos (by omega : 0 < D) (by omega : 0 < n)
    omega
  simp only [hem, Bool.false_eq_true, ↓reduceIte, hl] at hN
  refine ⟨hN.trans ?_, fun c hc => ⟨(hw c hc).1.trans ?_, (hw c hc).2⟩⟩
  · congr 1; ring
  · omega

/-- Every actual query has polynomial clause volume in the vertex count for fixed D, independent
of the bit magnitude of the input bounds. All gate and forbidden-state clauses are included. -/
theorem query_volume {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (D : ℕ) (hD : 1 ≤ D) (σ ρ : SimpleGraph.DegreeRule D) (active : Bool) (lo hi : ℕ)
    (N : ℕ) (q : CNF ℕ)
    (hq : (N, q) ∈ TwoBoundary.BinaryFrontend.queries
      (TwoBoundary.BinaryFrontend.compile (build D σ ρ active (ofGraph G lo hi)))) :
    q.length ≤ 2 + 2856 * (n + 1) + 3 * D * n * (n + 1) ^ D + (4 * D + 2) * n := by
  classical
  let a := auxiliary active (ofGraph G lo hi)
  have hc : core active (ofGraph G lo hi) = (IndependentDomination.ofGraph G, n + a) := rfl
  have hf := congrArg List.length (forward_ofGraph G D a)
  have hr := congrArg List.length (rules_ofGraph G D hD σ ρ a)
  have hp := congrArg (fun ps => (ps.map List.length).sum) (reverse_ofGraph G D a)
  simp only [CNF.relabel, List.length_map] at hf hr
  simp only [List.map_map, CNF.relabel, List.length_map, Function.comp_def] at hp
  have hs : (sizeFormula active (ofGraph G lo hi)).length ≤ 2 + 2856 * (n + 1) := by
    cases active
    · simp [sizeFormula]
    · exact (CardinalityInterval.formula_bounds n lo hi).1
  obtain ⟨B, P, he, hb, ht, _, _⟩ := representation G D hD σ ρ active lo hi
  have hB := congrArg (fun z => (TwoBoundary.BinaryFrontend.side z).length) he
  have hP := congrArg
    (fun z => ((TwoBoundary.BinaryFrontend.conditions z).map List.length).sum) he
  change (sizeFormula active (ofGraph G lo hi) ++ forward D (core active (ofGraph G lo hi)) ++
    rules D σ ρ (core active (ofGraph G lo hi))).length =
      (CNF.relabel Fin.val B).length at hB
  change ((reverse D (core active (ofGraph G lo hi))).map List.length).sum =
    ((P.map (CNF.relabel Fin.val)).map List.length).sum at hP
  simp only [List.length_append] at hB
  rw [hc, hf, hr] at hB
  rw [hc, hp] at hP
  simp only [CNF.relabel, List.length_map] at hB
  simp only [List.map_map, CNF.relabel, List.length_map, Function.comp_def] at hP
  rw [he] at hq
  have hqM := (TwoBoundary.BinaryFrontend.compile_budget B P hb ht N q hq).2.1
  have hv := volumes G D a
  have hrv := rule_volume n D hD σ ρ a
  nlinarith

end Cslib.Logic.PL.SigmaRho.BinaryFrontend
