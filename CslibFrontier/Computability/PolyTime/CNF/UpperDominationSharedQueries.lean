/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PolyTime.CNF.UpperDominationSharedMarkers
import Mathlib.Data.List.GetD
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import all CslibFrontier.Computability.PolyTime.CNF.TwoBoundaryFrontend

/-!
# Global shared-marker query writing

The actual original-graph writer for [ChenJiangZhu2027], Appendix D.3 (PDF p.35).
Only the added pair-or-mark predicates receive markers. The first two families retain their
original endpoint-substituted clauses, with the full augmented path length throughout.

## Main definitions

* `query`: the complete ordinary boundary query, including the original gate/mark side formula.
* `compile`: actual empty-graph dispatch or two refined boundary queries.
* `context`: source ports and one fresh suffix marker for each added predicate.

## Main results

* `query_polytime`, `compile_polytime`: binary polynomial-time construction from the graph and
  signed bound, charging normalization, gate generation and all clause/literal writes.
* `query_eval`: simultaneous semantics of all prefix edges and all shared-marker blocks.
* `declaration`, `query_width`: source variable budget and global width-three bound.
* `context_ports`, `context_terms`: global port/term separation from every new marker.

The companion `UpperDominationSharedTransport` and `UpperDominationSharedBounds` modules prove
finite-model count transport and the closed source-wide query budgets. The native shared-marker
counter has polynomial workspace; its closed sharp-time composition remains separate.
-/

public section

namespace Cslib.Logic.PL.UpperDomination.Unique.SharedMarkers

open Turing.MultiTapeTM WeightedRow

/-- The old augmented declaration, including every internal path variable. -/
@[expose] def oldDeclaration (x : UpperDomination.Input) : ℕ :=
  TwoBoundary.BinaryFrontend.declared (Unique.build x) +
    (TwoBoundary.BinaryFrontend.conditions (Unique.build x)).length - 1

/-- Actual suffix-edge descriptor. The ignored final right index can coincide with a marker. -/
@[expose] def context (x : UpperDomination.Input) (β : Bool) (w : ℕ) : Context :=
  let base := UpperDomination.build x
  let j := (TwoBoundary.BinaryFrontend.conditions base).length + w
  { left := TwoBoundary.BinaryFrontend.declared base + j - 1
    right := TwoBoundary.BinaryFrontend.declared base + j
    marker := oldDeclaration x + w
    last := decide (w + 1 = IndependentDomination.order (graph x))
    boundary := β
    terms := (complete (coreInput x)).getD w [] }

/-- Prefix clauses keep the full augmented path length, rather than closing an earlier path. -/
@[expose] def prefixClauses (x : UpperDomination.Input) (β : Bool) : CNF ℕ :=
  let base := UpperDomination.build x
  (List.range (TwoBoundary.BinaryFrontend.conditions base).length).flatMap fun j =>
    ((TwoBoundary.BinaryFrontend.conditions base).getD j []).flatMap
      (BinaryQuery.termClauses (TwoBoundary.BinaryFrontend.declared base)
        ((TwoBoundary.BinaryFrontend.conditions (Unique.build x)).length - 1) β j)

/-- Write the entire refined query, with one shared marker per added predicate, never per term.
No assignments, marker advice or family of graph solutions is enumerated. -/
@[expose] def query (x : UpperDomination.Input) (β : Bool) : CNF ℕ :=
  TwoBoundary.BinaryFrontend.side (UpperDomination.build x) ++ prefixClauses x β ++
    (List.range (IndependentDomination.order (graph x))).flatMap fun w => block (context x β w)

private theorem order_polytime : ComputableInPolyTime
    (fun x => IndependentDomination.order (graph x)) encInput encUnary := by
  unfold graph encInput IndependentDomination.order IndependentDomination.encInput
  fun_prop

private theorem base_declared_polytime : ComputableInPolyTime
    (fun x => TwoBoundary.BinaryFrontend.declared (UpperDomination.build x)) encInput encUnary := by
  simpa only [TwoBoundary.BinaryFrontend.declared] using UpperDomination.build_polytime.fst'

private theorem base_conditions_polytime : ComputableInPolyTime
    (fun x => TwoBoundary.BinaryFrontend.conditions (UpperDomination.build x)) encInput
      (encList VCOne.encSignedCNF) := by
  simpa only [TwoBoundary.BinaryFrontend.conditions] using
    UpperDomination.build_polytime.snd'.snd'

private theorem path_length_polytime : ComputableInPolyTime
    (fun x => (TwoBoundary.BinaryFrontend.conditions (Unique.build x)).length - 1)
      encInput encUnary := by
  have h := (ComputableInPolyTime.length_list VCOne.encSignedCNF).comp
    Unique.build_polytime.snd'.snd'
  exact ComputableInPolyTime.unary_sub.comp (h.prod (.const 1))

/-- The declaration is computed in unary and its conversion to binary is charged separately. -/
theorem oldDeclaration_polytime : ComputableInPolyTime oldDeclaration encInput encUnary := by
  have hn : ComputableInPolyTime
      (fun x => TwoBoundary.BinaryFrontend.declared (Unique.build x)) encInput encUnary := by
    simpa only [TwoBoundary.BinaryFrontend.declared] using Unique.build_polytime.fst'
  have hl := (ComputableInPolyTime.length_list VCOne.encSignedCNF).comp
    Unique.build_polytime.snd'.snd'
  unfold oldDeclaration
  exact ComputableInPolyTime.unary_sub.comp
    ((ComputableInPolyTime.unary_add.comp (hn.prod hl)).prod (.const 1))

/-- Framed original input and a unary suffix position; literal/port fields remain binary. -/
abbrev encPosition := encPair encInput encUnary

private theorem context_polytime (β : Bool) : ComputableInPolyTime
    (fun p : UpperDomination.Input × ℕ => context p.1 β p.2) encPosition encContext := by
  have hp := ComputableInPolyTime.fst encInput encUnary
  have hw := ComputableInPolyTime.snd encInput encUnary
  have hlen := (ComputableInPolyTime.length_list VCOne.encSignedCNF).comp base_conditions_polytime
  have hj := ComputableInPolyTime.unary_add.comp ((hlen.comp hp).prod hw)
  have hn := base_declared_polytime.comp hp
  have hsum := ComputableInPolyTime.unary_add.comp (hn.prod hj)
  have hl := ComputableInPolyTime.unary_to_binary.comp
    (ComputableInPolyTime.unary_sub.comp (hsum.prod (.const 1)))
  have hr := ComputableInPolyTime.unary_to_binary.comp hsum
  have hm := ComputableInPolyTime.unary_to_binary.comp
    (ComputableInPolyTime.unary_add.comp ((oldDeclaration_polytime.comp hp).prod hw))
  have ht : ComputableInPolyTime
      (fun p : UpperDomination.Input × ℕ =>
        decide (p.2 + 1 = IndependentDomination.order (graph p.1))) encPosition encBool := by
    have hn := order_polytime.comp hp
    fun_prop
  have hmore : ComputableInPolyTime (fun x => complete (coreInput x)) encInput
      (encList VCOne.encSignedCNF) := by
    have hbase := base_conditions_polytime
    have hfull := Unique.build_polytime.snd'.snd'
    -- Drop exactly the old predicate prefix, preserving repeated terms and every suffix row.
    have he : (fun x => complete (coreInput x)) = fun x =>
        (TwoBoundary.BinaryFrontend.conditions (Unique.build x)).drop
          (TwoBoundary.BinaryFrontend.conditions (UpperDomination.build x)).length := by
      funext x
      simp [Unique.build, TwoBoundary.BinaryFrontend.conditions]
    rw [he]
    exact (ComputableTidilyInPolyTime.listDropWithInput hfull.tidy
      ((ComputableInPolyTime.length_list VCOne.encSignedCNF).comp hbase).tidy).computableInPolyTime
  have hpterms := ComputableInPolyTime.listGetDWithInput (hmore.comp hp) hw []
  have hmk : ComputableInPolyTime
      (fun p => Context.mk p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2)
      encContextFields encContext := encContext_mk_deg.computableInPolyTime
  exact (hmk.comp (hl.prod (hr.prod (hm.prod (ht.prod
    ((ComputableInPolyTime.const β).prod hpterms)))))).of_enc_eq fun _ => rfl

private theorem prefix_polytime (β : Bool) : ComputableInPolyTime
    (fun x => prefixClauses x β) encInput VCOne.encSignedCNF := by
  have hl := (ComputableInPolyTime.length_list VCOne.encSignedCNF).comp base_conditions_polytime
  have hp := ComputableInPolyTime.fst encInput encUnary
  have hj := ComputableInPolyTime.snd encInput encUnary
  have ht := ComputableInPolyTime.listGetDWithInput (base_conditions_polytime.comp hp) hj []
  have hc := ComputableInPolyTime.fst encPosition (encList (encPair encNat encBool))
  have hx := hp.comp hc
  have hw := TwoBoundary.BinaryFrontend.term_polytime (base_declared_polytime.comp hx)
    (path_length_polytime.comp hx) (hj.comp hc) (.const β)
    (ComputableInPolyTime.snd encPosition (encList (encPair encNat encBool)))
  unfold prefixClauses
  exact ComputableInPolyTime.flatMapWithInput (ComputableInPolyTime.range.comp hl)
    (ComputableInPolyTime.flatMapWithInput ht hw)

/-- Polynomial binary construction for the complete original-input query, including all writes. -/
theorem query_polytime (β : Bool) : ComputableInPolyTime
    (fun x => query x β) encInput VCOne.encSignedCNF := by
  have hs : ComputableInPolyTime
      (fun x => TwoBoundary.BinaryFrontend.side (UpperDomination.build x)) encInput
        VCOne.encSignedCNF := by
    simpa only [TwoBoundary.BinaryFrontend.side] using UpperDomination.build_polytime.snd'.fst'
  unfold query
  exact ComputableInPolyTime.listAppend' (ComputableInPolyTime.listAppend' hs (prefix_polytime β))
    (ComputableInPolyTime.flatMapWithInput (ComputableInPolyTime.range.comp order_polytime)
      (block_polytime.comp (context_polytime β)))

/-- All suffix constraints hold simultaneously, with the same old assignment on shared wires. -/
theorem query_eval (x : UpperDomination.Input) (β : Bool) (σ : ℕ → Bool) :
    (query x β).eval σ = true ↔
      (TwoBoundary.BinaryFrontend.side (UpperDomination.build x)).eval σ = true ∧
        (prefixClauses x β).eval σ = true ∧
        ∀ w < IndependentDomination.order (graph x),
          σ (context x β w).marker =
            (σ (context x β w).left ^^
              (if (context x β w).last then β else σ (context x β w).right)) ∧
          (DNF.eval σ (context x β w).terms = true → σ (context x β w).marker = false) := by
  have hs : CNF.eval σ ((List.range (IndependentDomination.order (graph x))).flatMap
      fun w => block (context x β w)) = true ↔
        ∀ w < IndependentDomination.order (graph x), (block (context x β w)).eval σ = true := by
    simp only [CNF.eval_eq_true_iff, List.mem_flatMap, List.mem_range]
    constructor
    · intro h w hw c hc
      exact h c ⟨w, hw, hc⟩
    · rintro h c ⟨w, hw, hc⟩
      exact h w hw c hc
  rw [query, CNF.eval_append, CNF.eval_append, Bool.and_eq_true, Bool.and_eq_true, hs]
  simp_rw [block_eval]
  change ((_ ∧ _) ∧ _) ↔ _ ∧ _ ∧ _
  tauto

/-- Actual raw-input family lengths; no graph promise is needed for the row traversal. -/
theorem layout (x : UpperDomination.Input) :
    TwoBoundary.BinaryFrontend.declared (UpperDomination.build x) =
        2 * IndependentDomination.order (graph x) + auxiliary x ∧
      (TwoBoundary.BinaryFrontend.conditions (UpperDomination.build x)).length =
        2 * IndependentDomination.order (graph x) ∧
      (TwoBoundary.BinaryFrontend.conditions (Unique.build x)).length =
        3 * IndependentDomination.order (graph x) := by
  simp [UpperDomination.build, Unique.build, TwoBoundary.BinaryFrontend.declared,
    TwoBoundary.BinaryFrontend.conditions, IndependentDomination.coverage, witnesses,
    complete, coreInput, coreGraph, two_mul, Nat.add_assoc]
  omega

/-- Only the new suffix markers enlarge the source declaration. On a nonempty graph this is
exactly the advertised `6v+a-1`, including the actual size-test gate count. -/
theorem declaration (x : UpperDomination.Input)
    (hn : 1 ≤ IndependentDomination.order (graph x)) :
    oldDeclaration x + IndependentDomination.order (graph x) =
      6 * IndependentDomination.order (graph x) + auxiliary x - 1 := by
  obtain ⟨hd, _, hp⟩ := layout x
  have hdecl : TwoBoundary.BinaryFrontend.declared (Unique.build x) =
      TwoBoundary.BinaryFrontend.declared (UpperDomination.build x) := rfl
  unfold oldDeclaration
  rw [hdecl, hd, hp]
  omega

/-- Every used port is below every new marker, not merely different from its own marker.
The dummy right port on the last edge is deliberately excluded. -/
theorem context_ports (x : UpperDomination.Input) (β : Bool) (w : ℕ)
    (hw : w < IndependentDomination.order (graph x)) :
    (context x β w).left < oldDeclaration x ∧
      ((context x β w).last = false → (context x β w).right < oldDeclaration x) ∧
      (context x β w).marker = oldDeclaration x + w ∧
      (context x β w).marker < oldDeclaration x + IndependentDomination.order (graph x) := by
  obtain ⟨hd, hp, hfull⟩ := layout x
  have hdecl : TwoBoundary.BinaryFrontend.declared (Unique.build x) =
      TwoBoundary.BinaryFrontend.declared (UpperDomination.build x) := rfl
  simp only [context, oldDeclaration, hdecl, hd, hp, hfull]
  refine ⟨by omega, ?_, by trivial, by omega⟩
  intro he
  have hne : w + 1 ≠ IndependentDomination.order (graph x) := of_decide_eq_false he
  omega

/-- Empty graphs retain the existing direct/no-condition branch. Positive graphs emit exactly
one refined query for each boundary, sharing the source declaration. -/
@[expose] def compile (x : UpperDomination.Input) : TwoBoundary.BinaryFrontend.Output :=
  if IndependentDomination.order (graph x) = 0 then
    TwoBoundary.BinaryFrontend.compile (Unique.build x)
  else .inr (oldDeclaration x + IndependentDomination.order (graph x), query x false, query x true)

/-- Binary polynomial resources for the actual complete tagged query constructor. This is a
construction certificate, not a certificate for counting its models. -/
theorem compile_polytime : ComputableInPolyTime compile encInput
    TwoBoundary.BinaryFrontend.encOutput := by
  have hz : ComputableInPolyTime
      (fun x => decide (IndependentDomination.order (graph x) = 0)) encInput encBool := by
    have hn := order_polytime
    fun_prop
  have hn := ComputableInPolyTime.unary_add.comp (oldDeclaration_polytime.prod order_polytime)
  have hq := (ComputableInPolyTime.sumInr (encPair encUnary VCOne.encSignedCNF)
    (encPair encUnary (encPair VCOne.encSignedCNF VCOne.encSignedCNF))).comp
      (hn.prod ((query_polytime false).prod (query_polytime true)))
  have hd := TwoBoundary.BinaryFrontend.compile_polytime.comp Unique.build_polytime
  unfold compile
  simpa only [decide_eq_true_eq, Function.comp_def] using hz.ite' hd hq

/-- The positive-input dispatch emits the two computed boundary formulas on `6v+a-1` variables. -/
theorem compile_queries (x : UpperDomination.Input)
    (hn : 1 ≤ IndependentDomination.order (graph x)) :
    TwoBoundary.BinaryFrontend.queries (compile x) =
      [(6 * IndependentDomination.order (graph x) + auxiliary x - 1, query x false),
        (6 * IndependentDomination.order (graph x) + auxiliary x - 1, query x true)] := by
  have hz : IndependentDomination.order (graph x) ≠ 0 := by omega
  simp only [compile, hz, ↓reduceIte, TwoBoundary.BinaryFrontend.queries, declaration x hn]

private theorem complete_terms (x : UpperDomination.Input) :
    ∀ p ∈ complete (coreInput x), ∀ t ∈ p,
      t.length ≤ 2 ∧ ∀ l ∈ t, l.1 < 2 * IndependentDomination.order (graph x) + auxiliary x := by
  intro p hp t ht
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hp
  have hw' : w < IndependentDomination.order (graph x) := List.mem_range.mp hw
  rcases List.mem_append.mp ht with ht | ht
  · obtain rfl := List.mem_singleton.mp ht
    refine ⟨by simp, ?_⟩
    intro l hl
    obtain rfl := List.mem_singleton.mp hl
    dsimp only [markBase, coreInput]
    omega
  · simp only [List.mem_flatMap, List.mem_range] at ht
    obtain ⟨u, hu, v, hv, ht⟩ := ht
    split_ifs at ht <;> simp only [List.mem_singleton, List.not_mem_nil] at ht
    subst t
    change u < IndependentDomination.order (graph x) at hu
    change v < IndependentDomination.order (graph x) at hv
    refine ⟨by simp, ?_⟩
    intro l hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl <;> dsimp only <;> omega

/-- Every added term reads only old variables, below every new marker. This is a global
freshness bound for the actual graph allocation, including all ordered duplicate pair terms. -/
theorem context_terms (x : UpperDomination.Input) (β : Bool) (w : ℕ)
    (hw : w < IndependentDomination.order (graph x)) :
    ∀ t ∈ (context x β w).terms, t.length ≤ 2 ∧ ∀ l ∈ t, l.1 < oldDeclaration x := by
  have hlen : w < (complete (coreInput x)).length := by
    simpa only [complete, List.length_map, List.length_range, coreInput, coreGraph] using hw
  intro t ht
  change t ∈ (complete (coreInput x)).getD w [] at ht
  rw [List.getD_eq_getElem (complete (coreInput x)) [] hlen] at ht
  obtain ⟨htw, htl⟩ := complete_terms x _ (List.getElem_mem hlen) t ht
  refine ⟨htw, fun l hl => (htl l hl).trans_le ?_⟩
  obtain ⟨hd, _, hp⟩ := layout x
  have hdecl : TwoBoundary.BinaryFrontend.declared (Unique.build x) =
      TwoBoundary.BinaryFrontend.declared (UpperDomination.build x) := rfl
  simp only [oldDeclaration, hdecl, hd, hp]
  omega

private theorem base_terms (x : UpperDomination.Input) :
    ∀ p ∈ TwoBoundary.BinaryFrontend.conditions (UpperDomination.build x),
      ∀ t ∈ p, t.length ≤ 1 := by
  intro p hp t ht
  change p ∈ IndependentDomination.coverage (graph x) ++ witnesses (coreInput x) at hp
  rcases List.mem_append.mp hp with hp | hp
  · obtain ⟨u, _, rfl⟩ := List.mem_map.mp hp
    obtain ⟨v, _, rfl⟩ := List.mem_map.mp ht
    simp
  · obtain ⟨u, _, rfl⟩ := List.mem_map.mp hp
    rcases List.mem_append.mp ht with ht | ht
    · obtain rfl := List.mem_singleton.mp ht
      simp
    · obtain ⟨v, _, rfl⟩ := List.mem_map.mp ht
      simp

private theorem side_width (x : UpperDomination.Input) :
    ∀ c ∈ TwoBoundary.BinaryFrontend.side (UpperDomination.build x), c.length ≤ 3 := by
  intro c hc
  change c ∈ CardinalityInterval.formula (cardinalityInput x) ++ upper (coreInput x) at hc
  rcases List.mem_append.mp hc with hc | hc
  · exact ((CardinalityInterval.formula_bounds _ _ _).2 c hc).1.le
  · simp only [upper, List.mem_flatMap, List.mem_range] at hc
    obtain ⟨w, _, u, _, v, _, hc⟩ := hc
    split_ifs at hc <;> simp_all

/-- The complete original-input query has width three, including the old prefix and side gates.
This syntactic bound holds even for a raw matrix failing the simple-graph admission promise. -/
theorem query_width (x : UpperDomination.Input) (β : Bool) :
    ∀ c ∈ query x β, c.length ≤ 3 := by
  intro c hc
  rcases List.mem_append.mp hc with hc | hc
  · rcases List.mem_append.mp hc with hc | hc
    · exact side_width x c hc
    · simp only [prefixClauses, List.mem_flatMap, List.mem_range] at hc
      obtain ⟨j, hj, t, ht, hc⟩ := hc
      have hj' : j < (TwoBoundary.BinaryFrontend.conditions (UpperDomination.build x)).length := hj
      rw [List.getD_eq_getElem _ [] hj'] at ht
      have hw := base_terms x _ (List.getElem_mem hj') t ht
      simp only [BinaryQuery.termClauses] at hc
      split_ifs at hc <;>
        simp_all [List.length_append, List.length_map] <;> grind
  · obtain ⟨w, hw, hc⟩ := List.mem_flatMap.mp hc
    exact block_width _ (fun t ht => (context_terms x β w (List.mem_range.mp hw) t ht).1) c hc

end Cslib.Logic.PL.UpperDomination.Unique.SharedMarkers
