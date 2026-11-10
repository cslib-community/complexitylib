/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PolyTime.CNF.RegularInducedCore
public import CslibFrontier.Computability.PolyTime.CNF.IndependentDominationInterval
import all CslibFrontier.Computability.PolyTime.CNF.IndependentDominationInterval

/-!
# Compact regular induced subgraphs with binary size bounds

Attach the actual functional cardinality circuit to the original selection prefix of
[ChenJiangZhu2027], Proposition C.2 (PDF pp.32–33). Degree is a fixed parameter, not an encoded
input or supplied threshold array. The existing graph/interval encoding is reused unchanged.

## Main definitions

* `build`: actual original-graph and binary-interval constructor.

## Main results

* `build_polytime`: binary normalization/gate generation and bounded neighbor enumeration.
* `representation`, `plan_count`, `Signed.plan_count`: functional extension and exact counts.
* `query_budget`, `query_polynomial_budget`: compact source dimensions, widths and clause bounds.
* `Signed.build_polytime`: actual signed binary normalization and construction.
-/

public section

namespace Cslib.Logic.PL.RegularInducedInterval

open Turing.MultiTapeTM Cslib.Circuits.Boolean

section

open IndependentDominationInterval

/-- Original selections followed only by the computed size gates; no degree threshold bits. -/
@[expose] def build (d : ℕ) (x : Input) : TwoBoundary.BinaryFrontend.Input :=
  (IndependentDomination.order (graph x) + auxiliary x,
    RegularInducedCore.upper d (graph x) ++ CardinalityInterval.formula (cardinalityInput x),
    RegularInducedCore.conditions d (graph x))

/-- Actual binary construction for each fixed degree, including gate and query-input writes. -/
theorem build_polytime (d : ℕ) : ComputableInPolyTime (build d) encInput
    TwoBoundary.BinaryFrontend.encInput := by
  have hg : ComputableInPolyTime graph encInput IndependentDomination.encInput := by
    unfold graph encInput; fun_prop
  have hcore := (RegularInducedCore.build_polytime d).comp hg
  have hn : ComputableInPolyTime (fun x => IndependentDomination.order (graph x))
      encInput encUnary := by
    unfold graph encInput IndependentDomination.order IndependentDomination.encInput
    fun_prop
  have hC := CardinalityInterval.formula_polytime.comp cardinalityInput_polytime
  exact (ComputableInPolyTime.unary_add.comp (hn.prod auxiliary_polytime)).prod
    ((ComputableInPolyTime.listAppend' hcore.snd'.fst' hC).prod hcore.snd'.snd')

open Classical in
/-- Every accepted original selection has exactly one size-gate extension. Both binary bounds
vary; the degree remains fixed. No constructor or count-correctness contract is assumed. -/
theorem representation {n : ℕ} (d : ℕ) (hd : 1 ≤ d) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (lo hi : ℕ) :
    let a := (CardinalityInterval.circuit n lo hi).size
    ∃ B : CNF (Fin (n + a)), ∃ P : List (DNF (Fin (n + a))),
      build d (ofGraph G lo hi) = TwoBoundary.BinaryFrontend.ofFinite B P ∧
      (∀ c ∈ B, c.length ≤ d + 2) ∧ (∀ p ∈ P, ∀ t ∈ p, t.length ≤ d) ∧ P.length = n ∧
      Fintype.card {y : Fin (n + a) → Bool // B.eval y = true ∧ ∀ p ∈ P, DNF.eval y p = true} =
        Fintype.card {x : Fin n → Bool // G.IsSigmaRhoSet {d} Set.univ {u | x u = true} ∧
          lo ≤ Cslib.BitString.weight x ∧ Cslib.BitString.weight x ≤ hi} := by
  generalize hc : CardinalityInterval.circuit n lo hi = c
  let a := c.size
  let ι : Fin n → Fin (n + a) := Fin.castAdd a
  obtain ⟨_, hCbounds⟩ := CardinalityInterval.formula_bounds n lo hi
  rw [hc] at hCbounds
  obtain ⟨F, hF⟩ := IndependentDominationInterval.lift_cnf
    (CardinalityInterval.formula (n, lo, hi)) (fun q hq => (hCbounds q hq).2)
  let B := (RegularInducedCore.finiteUpper d G).relabel ι ++ F
  let P := (RegularInducedCore.finiteConditions d G).map (CNF.relabel ι)
  obtain ⟨hb, hp, hplen⟩ := RegularInducedCore.widths d hd G
  have hcore := RegularInducedCore.build_ofGraph d G
  have hBG := congrArg TwoBoundary.BinaryFrontend.side hcore
  have hPG := congrArg TwoBoundary.BinaryFrontend.conditions hcore
  change RegularInducedCore.upper d (IndependentDomination.ofGraph G) =
    (RegularInducedCore.finiteUpper d G).relabel Fin.val at hBG
  change RegularInducedCore.conditions d (IndependentDomination.ofGraph G) =
    (RegularInducedCore.finiteConditions d G).map (CNF.relabel Fin.val) at hPG
  have herase (D : CNF (Fin n)) : CNF.relabel Fin.val (D.relabel ι) = D.relabel Fin.val := by
    simp only [CNF.relabel, Clause.relabel, List.map_map, Function.comp_def]
    congr 1
  have hNF : CNF.relabel Fin.val B = RegularInducedCore.upper d
      (IndependentDomination.ofGraph G) ++ CardinalityInterval.formula (n, lo, hi) := by
    simp only [B, CNF.relabel, List.map_append]
    change CNF.relabel Fin.val ((RegularInducedCore.finiteUpper d G).relabel ι) ++
      CNF.relabel Fin.val F = _
    rw [herase, hF, hBG]
  have hPF : P.map (CNF.relabel Fin.val) =
      RegularInducedCore.conditions d (IndependentDomination.ofGraph G) := by
    rw [hPG]
    simp only [P, List.map_map, Function.comp_def, herase]
  have haux := auxiliary_ofGraph G lo hi
  rw [hc] at haux
  have hgraph : graph (ofGraph G lo hi) = IndependentDomination.ofGraph G := rfl
  have horder : IndependentDomination.order (IndependentDomination.ofGraph G) = n := rfl
  have hcard : cardinalityInput (ofGraph G lo hi) = (n, lo, hi) := rfl
  refine ⟨B, P, ?_, ?_, ?_, by simpa only [P, List.length_map] using hplen, ?_⟩
  · simp only [build, hgraph, hcard, horder, haux, TwoBoundary.BinaryFrontend.ofFinite]
    rw [← hNF, ← hPF]
  · intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hq
      simpa only [Clause.relabel, List.length_map] using hb r hr
    · have hq' : q.relabel Fin.val ∈ CardinalityInterval.formula (n, lo, hi) := by
        rw [← hF]; exact List.mem_map.mpr ⟨q, hq, rfl⟩
      have hlen := (hCbounds _ hq').1
      simp only [Clause.relabel, List.length_map] at hlen
      omega
  · intro p hp' t ht
    obtain ⟨p0, hp0, rfl⟩ := List.mem_map.mp hp'
    obtain ⟨t0, ht0, rfl⟩ := List.mem_map.mp ht
    simpa only [Clause.relabel, List.length_map] using hp p0 hp0 t0 ht0
  · simp only [← Nat.card_eq_fintype_card]
    have hPred (y : Fin (n + a) → Bool) :
        (B.eval y = true ∧ ∀ p ∈ P, DNF.eval y p = true) ↔
        (CardinalityInterval.formula (n, lo, hi)).eval
          (Function.extend Fin.val y (fun _ => false)) = true ∧
          G.IsSigmaRhoSet {d} Set.univ {u | y (ι u) = true} := by
      have hFE : F.eval y = (CardinalityInterval.formula (n, lo, hi)).eval
          (Function.extend Fin.val y (fun _ => false)) := by
        rw [← hF, CNF.eval_relabel, Function.extend_comp Fin.val_injective]
      have hPE : (∀ p ∈ P, DNF.eval y p = true) ↔
          ∀ p ∈ RegularInducedCore.finiteConditions d G, DNF.eval (y ∘ ι) p = true := by
        simp only [P, List.forall_mem_map, DNF.eval_relabel, Function.comp_def]
      have hR := RegularInducedCore.finite_semantics d G (y ∘ ι)
      simp only [B, CNF.eval_append, Bool.and_eq_true, CNF.eval_relabel, hFE, hPE]
      constructor
      · rintro ⟨⟨hu, hf⟩, hr⟩
        exact ⟨hf, hR.mp ⟨hu, hr⟩⟩
      · rintro ⟨hf, hr⟩
        obtain ⟨hu, hp⟩ := hR.mpr hr
        exact ⟨⟨hu, hf⟩, hp⟩
    have haccept (x : Fin n → Bool) : c.eval interpretation x = CardinalityInterval.wanted ↔
        lo ≤ Cslib.BitString.weight x ∧ Cslib.BitString.weight x ≤ hi := by
      have h := CardinalityInterval.circuit_accepts n lo hi x
      rwa [hc] at h
    calc
      _ = Nat.card {y : Fin (n + c.size) → Bool //
          (FunctionalCNF.write (FunctionalCNF.ofCircuit c CardinalityInterval.wanted)).eval
            (Function.extend Fin.val y (fun _ => false)) = true ∧
              G.IsSigmaRhoSet {d} Set.univ {u | y (Fin.castAdd c.size u) = true}} := by
        apply Nat.card_congr
        apply Equiv.subtypeEquivRight
        intro y
        simpa only [CardinalityInterval.formula, CardinalityInterval.payload_eq, hc] using hPred y
      _ = Nat.card {x : Fin n → Bool // c.eval interpretation x = CardinalityInterval.wanted ∧
          G.IsSigmaRhoSet {d} Set.univ {u | x u = true}} := by
        have h := FunctionalCNF.count_extensions c CardinalityInterval.wanted
          (fun x => G.IsSigmaRhoSet {d} Set.univ {u | x u = true})
        simpa only [← Nat.card_eq_fintype_card] using h
      _ = _ := by
        apply Nat.card_congr
        apply Equiv.subtypeEquivRight
        intro x
        rw [haccept]
        constructor
        · rintro ⟨⟨hl, hh⟩, hr⟩
          exact ⟨hr, hl, hh⟩
        · rintro ⟨hr, hl, hh⟩
          exact ⟨⟨hl, hh⟩, hr⟩

open Classical in
/-- The actual compiled plan counts size-constrained original selections, not gate traces. -/
theorem plan_count {n : ℕ} (d : ℕ) (hd : 1 ≤ d) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (lo hi : ℕ) :
    TwoBoundary.BinaryFrontend.value (TwoBoundary.BinaryFrontend.compile
      (build d (ofGraph G lo hi))) =
        Fintype.card {x : Fin n → Bool // G.IsSigmaRhoSet {d} Set.univ {u | x u = true} ∧
          lo ≤ Cslib.BitString.weight x ∧ Cslib.BitString.weight x ≤ hi} := by
  obtain ⟨B, P, he, _, _, _, hc⟩ := representation d hd G lo hi
  rw [he, TwoBoundary.BinaryFrontend.compile_count]
  exact hc

/-- Positive original graphs emit exactly two ordinary boundary queries. -/
theorem query_count {n : ℕ} (d : ℕ) (hd : 1 ≤ d) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (lo hi : ℕ) (hn : 1 ≤ n) :
    (TwoBoundary.BinaryFrontend.queries
      (TwoBoundary.BinaryFrontend.compile (build d (ofGraph G lo hi)))).length = 2 := by
  obtain ⟨B, P, he, _, _, hl, _⟩ := representation d hd G lo hi
  rw [he, TwoBoundary.BinaryFrontend.compile_query_count]
  have hem : P.isEmpty ≠ true := by
    intro h
    have hz := List.isEmpty_iff_length_eq_zero.mp h
    omega
  simp only [TwoBoundary.BinaryFrontend.conditions, TwoBoundary.BinaryFrontend.ofFinite,
    List.isEmpty_map, hem, Bool.false_eq_true, ↓reduceIte]

/-- The compact source budgets include every actual size-test gate and clause. -/
theorem query_budget {n : ℕ} (d : ℕ) (hd : 1 ≤ d) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (lo hi : ℕ) (hn : 1 ≤ n) (N : ℕ) (q : CNF ℕ)
    (hq : (N, q) ∈ TwoBoundary.BinaryFrontend.queries
      (TwoBoundary.BinaryFrontend.compile (build d (ofGraph G lo hi)))) :
    N = 2 * n + (CardinalityInterval.circuit n lo hi).size - 1 ∧
      q.length ≤ n ^ (d + 2) + 2 * (n + n ^ (d + 1)) + 2 + 2856 * (n + 1) ∧
      ∀ c ∈ q, c.length ≤ d + 2 ∧ ∀ l ∈ c, l.1 < N := by
  classical
  obtain ⟨B, P, he, hb, hp, hl, _⟩ := representation d hd G lo hi
  rw [he] at hq
  obtain ⟨hN, hM, hW⟩ := TwoBoundary.BinaryFrontend.compile_budget B P hb hp N q hq
  have hem : P.isEmpty ≠ true := by
    intro h
    have hz := List.isEmpty_iff_length_eq_zero.mp h
    omega
  simp only [hem, Bool.false_eq_true, ↓reduceIte] at hN
  have hB := congrArg (fun x => (TwoBoundary.BinaryFrontend.side x).length) he
  change (RegularInducedCore.upper d (IndependentDomination.ofGraph G) ++
    CardinalityInterval.formula (n, lo, hi)).length = (CNF.relabel Fin.val B).length at hB
  have hP := congrArg (fun x => ((TwoBoundary.BinaryFrontend.conditions x).map List.length).sum) he
  have hcore := RegularInducedCore.build_ofGraph d G
  have hU := congrArg (fun x => (TwoBoundary.BinaryFrontend.side x).length) hcore
  have hV := congrArg (fun x => ((TwoBoundary.BinaryFrontend.conditions x).map List.length).sum)
    hcore
  simp only [RegularInducedCore.build, TwoBoundary.BinaryFrontend.side,
    TwoBoundary.BinaryFrontend.conditions, TwoBoundary.BinaryFrontend.ofFinite,
    List.length_append, CNF.relabel, List.length_map, List.map_map, Function.comp_def]
    at hB hP hU hV
  change ((RegularInducedCore.conditions d (IndependentDomination.ofGraph G)).map
    List.length).sum = (P.map List.length).sum at hP
  change ((RegularInducedCore.conditions d (IndependentDomination.ofGraph G)).map
    List.length).sum = ((RegularInducedCore.finiteConditions d G).map List.length).sum at hV
  obtain ⟨hu, hv⟩ := RegularInducedCore.volumes d G
  have hc := (CardinalityInterval.formula_bounds n lo hi).1
  refine ⟨by omega, by omega, by simpa only [Nat.max_self] using hW⟩

/-- A closed source-polynomial clause bound for positive graphs, uniformly in both input bounds. -/
theorem query_polynomial_budget {n : ℕ} (d : ℕ) (hd : 1 ≤ d) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (lo hi : ℕ) (hn : 1 ≤ n) (N : ℕ) (q : CNF ℕ)
    (hq : (N, q) ∈ TwoBoundary.BinaryFrontend.queries
      (TwoBoundary.BinaryFrontend.compile (build d (ofGraph G lo hi)))) :
    q.length ≤ 6000 * n ^ (d + 2) := by
  have h := (query_budget d hd G lo hi hn N q hq).2.1
  have hnP : n ≤ n ^ (d + 2) := Nat.le_pow (by omega : 0 < d + 2)
  have hP : n ^ (d + 1) ≤ n ^ (d + 2) := Nat.pow_le_pow_right hn (by omega)
  omega

end

namespace Signed

open IndependentDominationInterval.Signed

/-- Actual signed normalization followed by the compact degree/size constructor. -/
@[expose] def build (d : ℕ) (x : Input) : TwoBoundary.BinaryFrontend.Input :=
  RegularInducedInterval.build d (normalize x)

/-- Sign inspection, capped binary cardinality gates and every query write are charged. -/
theorem build_polytime (d : ℕ) : ComputableInPolyTime (build d) encInput
    TwoBoundary.BinaryFrontend.encInput :=
  (RegularInducedInterval.build_polytime d).comp normalize_polytime

open Classical in
/-- Signed normalization preserves the concrete query-count difference for every original word. -/
theorem plan_count {n : ℕ} (d : ℕ) (hd : 1 ≤ d) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (lo hi : ℤ) :
    TwoBoundary.BinaryFrontend.value (TwoBoundary.BinaryFrontend.compile
      (build d (ofGraph G lo hi))) =
        Fintype.card {x : Fin n → Bool // G.IsSigmaRhoSet {d} Set.univ {u | x u = true} ∧
          lo ≤ (Cslib.BitString.weight x : ℤ) ∧ (Cslib.BitString.weight x : ℤ) ≤ hi} := by
  have he : build d (ofGraph G lo hi) = RegularInducedInterval.build d
      (IndependentDominationInterval.ofGraph G (lowerNat lo hi) (upperNat hi)) := rfl
  rw [he, RegularInducedInterval.plan_count d hd]
  apply Fintype.card_congr
  apply Equiv.subtypeEquivRight
  intro x
  rw [bounds_iff]

/-- Positive signed-bound inputs retain the exact compact source declaration and query widths. -/
theorem query_budget {n : ℕ} (d : ℕ) (hd : 1 ≤ d) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (lo hi : ℤ) (hn : 1 ≤ n) (N : ℕ) (q : CNF ℕ)
    (hq : (N, q) ∈ TwoBoundary.BinaryFrontend.queries
      (TwoBoundary.BinaryFrontend.compile (build d (ofGraph G lo hi)))) :
    N = 2 * n + (CardinalityInterval.circuit n (lowerNat lo hi) (upperNat hi)).size - 1 ∧
      q.length ≤ 6000 * n ^ (d + 2) ∧
      ∀ c ∈ q, c.length ≤ d + 2 ∧ ∀ l ∈ c, l.1 < N := by
  have he : build d (ofGraph G lo hi) = RegularInducedInterval.build d
      (IndependentDominationInterval.ofGraph G (lowerNat lo hi) (upperNat hi)) := rfl
  rw [he] at hq
  have h := RegularInducedInterval.query_budget d hd G _ _ hn N q hq
  exact ⟨h.1, RegularInducedInterval.query_polynomial_budget d hd G _ _ hn N q hq, h.2.2⟩

open Classical in
/-- Direct empty-graph counting for the signed algorithm: its only selection has weight zero. -/
theorem zero_count (d : ℕ) (G : SimpleGraph (Fin 0)) (lo hi : ℤ) :
    Fintype.card {x : Fin 0 → Bool // G.IsSigmaRhoSet {d} Set.univ {u | x u = true} ∧
      lo ≤ (Cslib.BitString.weight x : ℤ) ∧ (Cslib.BitString.weight x : ℤ) ≤ hi} =
        if lo ≤ 0 ∧ 0 ≤ hi then 1 else 0 := by
  have hp (x : Fin 0 → Bool) :
      (G.IsSigmaRhoSet {d} Set.univ {u | x u = true} ∧
        lo ≤ (Cslib.BitString.weight x : ℤ) ∧ (Cslib.BitString.weight x : ℤ) ≤ hi) ↔
      lo ≤ 0 ∧ 0 ≤ hi := by
    have hw : Cslib.BitString.weight x = 0 := by simp [Cslib.BitString.weight]
    rw [hw]
    have hr : G.IsSigmaRhoSet {d} Set.univ {u | x u = true} := fun u => Fin.elim0 u
    simp only [hr, true_and, Nat.cast_zero]
  calc _ = Fintype.card {x : Fin 0 → Bool // lo ≤ 0 ∧ 0 ≤ hi} :=
      Fintype.card_congr (Equiv.subtypeEquivRight hp)
    _ = _ := by by_cases h : lo ≤ 0 ∧ 0 ≤ hi <;> simp [h]

end Signed

end Cslib.Logic.PL.RegularInducedInterval
