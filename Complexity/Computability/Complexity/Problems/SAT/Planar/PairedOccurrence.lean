/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.SAT.Planar.PairedCompile
public import Complexity.Computability.Complexity.Problems.SAT.Planar.PathGeometry
public import Complexity.Logics.Propositional.CNF.Compact.Relabel
import Mathlib.Data.List.Nodup
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Tactic.FinCases

/-!
# Literal occurrences in the paired-port compiler

Each directed path half has its own port on each lane. These keys are distinct across all
canonical source paths. The emitted external literals form a submultiset of those keys, so a
port receives at most one external occurrence. Each emitted ring contributes two internal
occurrences per port; the paired crossover contributes two at its ports and at most three at
its internal variables.

## Main results

* `count_vars_rawFormula_le_three`: the actual structured output respects the occurrence bound.
* `count_vars_formula_le_three`: injective compaction preserves that bound.

## References

This literal-position accounting for the paired compiler is original.
-/

@[expose] public section

namespace Cslib.Complexity.SAT.ParsimoniousPlanar

open Cslib.Logic.PL Cslib.Logic.PL.CNF Orthogonal

/-- The directed side used by each half of every unit step. -/
def pathPortKeys (r : Route) : List (Point × Fin 4) :=
  r.consecutivePairs.flatMap fun e => [(e.1, side e.1 e.2), (e.2, side e.2 e.1)]

/-- The signal attached to one directed half on one lane. -/
def portKeySignal (sites : List Point) (k : (Point × Fin 4) × Fin 2) : Variable :=
  port sites k.1.1 k.1.2 k.2

/-- Both lanes of each directed path half, including the unused halves at the final clause. -/
def pathPortSignals (sites : List Point) (r : Route) : List Variable :=
  ((pathPortKeys r).product [0, 1]).map (portKeySignal sites)

private theorem portKeySignal_injective (sites : List Point) :
    Function.Injective (portKeySignal sites) := by
  rintro ⟨⟨p, s⟩, l⟩ ⟨⟨q, t⟩, k⟩ h
  have hcell : p = q := congrArg Prod.fst h
  subst q
  by_cases hp : p ∈ sites
  · have he : s = t ∧ l = k := by
      simpa [portKeySignal, port, hp, PairedCrossover.terminal] using h
    rcases he with ⟨rfl, rfl⟩
    rfl
  · have he : s = t ∧ l = k := by
      simpa [portKeySignal, port, hp] using h
    rcases he with ⟨rfl, rfl⟩
    rfl

private theorem pathPortSignals_cons_cons (sites : List Point) (a b : Point) (r : Route) :
    pathPortSignals sites (a :: b :: r) =
      [signal sites a b 0, signal sites a b 1, signal sites b a 0, signal sites b a 1] ++
        pathPortSignals sites (b :: r) := rfl

private theorem links_cons_cons_cons (sites : List Point) (a b c : Point) (r : Route) :
    links sites (a :: b :: c :: r) =
      [link sites a b 0, link sites a b 1] ++ links sites (b :: c :: r) := rfl

private theorem lastLiteral_cons_cons_cons (sites : List Point) (positive : Bool)
    (a b c : Point) (r : Route) :
    lastLiteral sites (a :: b :: c :: r) positive =
      lastLiteral sites (b :: c :: r) positive := by
  simp [lastLiteral]

private theorem count_vars_append (φ ψ : CNF Variable) (v : Variable) :
    (φ ++ ψ).vars.count v = φ.vars.count v + ψ.vars.count v := by
  simp [CNF.vars]

private theorem count_two_links (sites : List Point) (a b : Point) (v : Variable) :
    (CNF.vars [(link sites a b 0).1, (link sites a b 1).1]).count v =
      [signal sites a b 0, signal sites a b 1, signal sites b a 0, signal sites b a 1].count v := by
  simp [link, CNF.vars, List.count_cons, Nat.add_comm, Nat.add_left_comm]

private theorem count_last_pair_le (sites : List Point) (a b : Point) (l : Fin 2) (v : Variable) :
    [signal sites a b l].count v ≤ (pathPortSignals sites [a, b]).count v := by
  have hp : pathPortSignals sites [a, b] =
      [signal sites a b 0, signal sites a b 1, signal sites b a 0, signal sites b a 1] := rfl
  rw [hp]
  have hl : l = 0 ∨ l = 1 := by fin_cases l <;> simp
  rcases hl with rfl | rfl <;> simp only [List.count_cons, List.count_nil] <;> omega

/-- External literals use only their actual path-half ports; unused clause halves overcount. -/
theorem count_links_lastLiteral_le (sites : List Point) (positive : Bool) (r : Route)
    (hlen : 2 ≤ r.length) (v : Variable) :
    (CNF.vars ((links sites r).map Prod.fst)).count v +
      [(lastLiteral sites r positive).1.1].count v ≤ (pathPortSignals sites r).count v := by
  induction r with
  | nil => simp at hlen
  | cons a r ih =>
    cases r with
    | nil => simp at hlen
    | cons b r =>
      cases r with
      | nil =>
        simpa [links, lastLiteral, List.consecutivePairs, CNF.vars] using
          count_last_pair_le sites a b (PairedPorts.spokeLane (side b a)) v
      | cons c r =>
        have ht := ih (by simp : 2 ≤ (b :: c :: r).length)
        rw [links_cons_cons_cons, List.map_append, List.map_cons, List.map_cons, List.map_nil,
          count_vars_append, lastLiteral_cons_cons_cons,
          pathPortSignals_cons_cons, List.count_append, count_two_links]
        omega

/-- Both lanes of every directed port in all actual canonical paths. -/
def allPathPortSignals (φ : CNF ℕ) : List Variable :=
  (paths φ).flatMap (pathPortSignals (crossingSites φ))

/-- Across all canonical paths each presented side/lane variable is distinct. -/
theorem allPathPortSignals_nodup {φ : CNF ℕ}
    (hw : ∀ c ∈ φ, c.length ≤ 3) (hv : ∀ v, φ.vars.count v ≤ 3) :
    (allPathPortSignals φ).Nodup := by
  have hn : ((paths φ).flatMap pathPortKeys).Nodup := PlanarCompile.pathPorts_nodup hw hv
  have heq : allPathPortSignals φ =
      (((paths φ).flatMap pathPortKeys).product [0, 1]).map
        (portKeySignal (crossingSites φ)) := by
    change ((paths φ).flatMap fun r =>
      ((pathPortKeys r).product [0, 1]).map (portKeySignal (crossingSites φ))) = _
    simp [List.product, List.map_flatMap, List.flatMap_assoc]
  rw [heq]
  exact (hn.product (by decide)).map (portKeySignal_injective _)

private theorem vars_originalClauses (φ : CNF ℕ) (sites : List Point) :
    CNF.vars ((originalClauses φ sites).map Prod.fst) =
      (Cslib.Logic.PL.occurrences φ).map
        (fun o => (lastLiteral sites (occurrencePath φ o) o.2.2.2).1.1) := by
  simp [originalClauses, Cslib.Logic.PL.occurrences, CNF.vars, List.map_flatten,
    List.map_map, Function.comp_def, List.flatMap_def]

private theorem count_external_blocks_le {φ : CNF ℕ} (sites : List Point)
    (os : List (Occurrence ℕ))
    (hpaths : ∀ o ∈ os, 2 ≤ (occurrencePath φ o).length) (v : Variable) :
    (CNF.vars ((os.flatMap fun o => links sites (occurrencePath φ o)).map Prod.fst)).count v +
      (os.map (fun o => (lastLiteral sites (occurrencePath φ o) o.2.2.2).1.1)).count v ≤
      (os.flatMap fun o => pathPortSignals sites (occurrencePath φ o)).count v := by
  induction os with
  | nil => simp [CNF.vars]
  | cons o os ih =>
    have ht := ih (fun a ha => hpaths a (List.mem_cons_of_mem _ ha))
    have ho := count_links_lastLiteral_le sites o.2.2.2 (occurrencePath φ o)
      (hpaths o List.mem_cons_self) v
    rw [List.flatMap_cons, List.map_append, count_vars_append, List.map_cons,
      List.count_cons, List.flatMap_cons, List.count_append]
    have hc : [(lastLiteral sites (occurrencePath φ o) o.2.2.2).1.1].count v =
        if (lastLiteral sites (occurrencePath φ o) o.2.2.2).1.1 == v then 1 else 0 := by
      simp [List.count_cons]
    rw [hc] at ho
    omega

private theorem vars_append (φ ψ : CNF Variable) : (φ ++ ψ).vars = φ.vars ++ ψ.vars := by
  simp [CNF.vars]

private theorem vars_flatMap (ps : List Point) (f : Point → List PlacedClause) :
    CNF.vars ((ps.flatMap f).map Prod.fst) =
      ps.flatMap fun p => CNF.vars ((f p).map Prod.fst) := by
  induction ps with
  | nil => rfl
  | cons p ps ih => rw [List.flatMap_cons, List.map_append, vars_append, ih]; rfl

private theorem vars_ordinaryBlock (p : Point) :
    CNF.vars ((ordinaryClauses p).map Prod.fst) =
      OrdinaryRing.formula.vars.map (fun v => ((p, Sum.inl v) : Variable)) := by
  have h : (ordinaryClauses p).map Prod.fst =
      OrdinaryRing.formula.relabel (fun v => ((p, Sum.inl v) : Variable)) := by
    simpa only [ordinaryClauses, CNF.relabel, List.map_map, Function.comp_def] using
      congrArg (List.map (fun c : Clause OrdinaryRing.Variable =>
        c.relabel (fun v => ((p, Sum.inl v) : Variable))))
        (List.zipIdx_map_fst (l := OrdinaryRing.formula) 0)
  rw [h, CNF.vars_relabel]

private theorem vars_crossingBlock (p : Point) :
    CNF.vars ((crossingClauses p).map Prod.fst) =
      PairedCrossover.formula.vars.map (fun v => ((p, Sum.inr v) : Variable)) := by
  have h : (crossingClauses p).map Prod.fst =
      PairedCrossover.formula.relabel (fun v => ((p, Sum.inr v) : Variable)) := by
    simpa only [crossingClauses, CNF.relabel, List.map_map, Function.comp_def] using
      congrArg (List.map (fun c : Clause PairedCrossover.Variable =>
        c.relabel (fun v => ((p, Sum.inr v) : Variable))))
        (List.zipIdx_map_fst (l := PairedCrossover.formula) 0)
  rw [h, CNF.vars_relabel]

/-- Literal positions supplied by all emitted ordinary rings. -/
def ordinarySignals (φ : CNF ℕ) : List Variable :=
  (ordinaryCells φ).flatMap fun p =>
    OrdinaryRing.formula.vars.map (fun v => ((p, Sum.inl v) : Variable))

/-- Literal positions supplied by all emitted paired crossovers. -/
def crossingSignals (φ : CNF ℕ) : List Variable :=
  (crossingSites φ).flatMap fun p =>
    PairedCrossover.formula.vars.map (fun v => ((p, Sum.inr v) : Variable))

private theorem count_tagged {W : Type*} [DecidableEq W] (ls : List W)
    (tag : W → ((Fin 4 × Fin 2) ⊕ PairedCrossover.Variable))
    (hinj : Function.Injective tag) (ps : List Point) (p : Point) (v : W) :
    (ps.flatMap fun q => ls.map (fun w => ((q, tag w) : Variable))).count (p, tag v) =
      ps.count p * ls.count v := by
  have hone (q : Point) :
      (ls.map (fun w => ((q, tag w) : Variable))).count (p, tag v) =
        if q = p then ls.count v else 0 := by
    by_cases h : q = p
    · subst q
      rw [ite_eq_left rfl]
      exact List.count_map_of_injective ls (fun w => ((p, tag w) : Variable))
        (fun _ _ he => hinj (congrArg Prod.snd he)) v
    · rw [ite_eq_right h, List.count_eq_zero]
      rintro hm
      obtain ⟨w, _, he⟩ := List.mem_map.mp hm
      exact h (congrArg Prod.fst he)
  induction ps with
  | nil => simp
  | cons q ps ih =>
    rw [List.flatMap_cons, List.count_append, hone, List.count_cons, ih]
    by_cases h : q = p <;> simp [h, beq_iff_eq, Nat.add_mul, Nat.add_comm]

private theorem count_ordinary_inl (φ : CNF ℕ) (p : Point) (v : Fin 4 × Fin 2) :
    (ordinarySignals φ).count (p, Sum.inl v) = (ordinaryCells φ).count p * 2 := by
  rw [ordinarySignals, count_tagged _ Sum.inl Sum.inl_injective,
    OrdinaryRing.internal_occurrences]

private theorem count_crossing_inr (φ : CNF ℕ) (p : Point) (v : PairedCrossover.Variable) :
    (crossingSignals φ).count (p, Sum.inr v) =
      (crossingSites φ).count p * PairedCrossover.formula.vars.count v :=
  count_tagged _ Sum.inr Sum.inr_injective _ _ _

private theorem count_ordinary_inr (φ : CNF ℕ) (p : Point) (v : PairedCrossover.Variable) :
    (ordinarySignals φ).count (p, Sum.inr v) = 0 := by
  rw [List.count_eq_zero]
  simp [ordinarySignals]

private theorem count_crossing_inl (φ : CNF ℕ) (p : Point) (v : Fin 4 × Fin 2) :
    (crossingSignals φ).count (p, Sum.inl v) = 0 := by
  rw [List.count_eq_zero]
  simp [crossingSignals]

/-- Count actual emitted literals by internal template literals and actual path-half ports. -/
theorem count_vars_rawFormula_le (φ : CNF ℕ) (v : Variable) :
    (rawFormula φ).vars.count v ≤ (ordinarySignals φ).count v +
      (crossingSignals φ).count v + (allPathPortSignals φ).count v := by
  have he := count_external_blocks_le (φ := φ) (crossingSites φ)
    (Cslib.Logic.PL.occurrences φ) (fun _ => PlanarCompile.occurrencePath_length_ge_two) v
  have heq : ((Cslib.Logic.PL.occurrences φ).flatMap fun o =>
      pathPortSignals (crossingSites φ) (occurrencePath φ o)) = allPathPortSignals φ := by
    rw [allPathPortSignals, paths, ← PlanarCompile.occurrencePaths_eq_paths, List.flatMap_map]
  rw [heq] at he
  have ho : CNF.vars (((ordinaryCells φ).flatMap ordinaryClauses).map Prod.fst) =
      ordinarySignals φ := by
    rw [vars_flatMap]
    simp_rw [vars_ordinaryBlock]
    rfl
  have hc : CNF.vars (((crossingSites φ).flatMap crossingClauses).map Prod.fst) =
      crossingSignals φ := by
    rw [vars_flatMap]
    simp_rw [vars_crossingBlock]
    rfl
  simp only [rawFormula, placedClauses, List.map_append, count_vars_append,
    vars_originalClauses, ho, hc]
  omega

private theorem count_allPathPortSignals_nonterminal {φ : CNF ℕ} (p : Point)
    (v : PairedCrossover.Variable) (hv : ¬ ∃ s l, PairedCrossover.terminal s l = v) :
    (allPathPortSignals φ).count (p, Sum.inr v) = 0 := by
  rw [List.count_eq_zero]
  intro hm
  obtain ⟨r, _, hm⟩ := List.mem_flatMap.mp hm
  obtain ⟨k, _, hk⟩ := List.mem_map.mp hm
  have hs := congrArg Prod.snd hk
  by_cases hp : k.1.1 ∈ crossingSites φ
  · have ht : PairedCrossover.terminal k.1.2 k.2 = v := by
      simpa [portKeySignal, port, hp] using hs
    exact hv ⟨_, _, ht⟩
  · simp [portKeySignal, port, hp] at hs

private theorem count_vars_pairedFormula : ∀ v, PairedCrossover.formula.vars.count v ≤ 3 := by
  decide +kernel

private theorem count_vars_pairedTerminal :
    ∀ s l, PairedCrossover.formula.vars.count (PairedCrossover.terminal s l) = 2 := by
  decide +kernel

/-- Every actual output variable has at most three literal occurrences, including repetitions
inside a clause. No occurrence certificate is assumed for the output. -/
theorem count_vars_rawFormula_le_three {φ : CNF ℕ}
    (hw : ∀ c ∈ φ, c.length ≤ 3) (hv : ∀ v, φ.vars.count v ≤ 3) :
    ∀ v, (rawFormula φ).vars.count v ≤ 3 := by
  rintro ⟨p, v⟩
  have hcompare := count_vars_rawFormula_le φ (p, v)
  have hext := List.nodup_iff_count_le_one.mp (allPathPortSignals_nodup hw hv) (p, v)
  cases v with
  | inl v =>
    have hn : (ordinaryCells φ).count p ≤ 1 := List.nodup_iff_count_le_one.mp
      (nodup_selectDistinct _ _ : (ordinaryCells φ).Nodup) p
    rw [count_ordinary_inl, count_crossing_inl] at hcompare
    omega
  | inr v =>
    have hn : (crossingSites φ).count p ≤ 1 :=
      List.nodup_iff_count_le_one.mp (PlanarCompile.crossingSites_nodup φ) p
    rw [count_ordinary_inr, count_crossing_inr] at hcompare
    by_cases ht : ∃ s l, PairedCrossover.terminal s l = v
    · obtain ⟨s, l, rfl⟩ := ht
      rw [count_vars_pairedTerminal] at hcompare
      omega
    · rw [count_allPathPortSignals_nonterminal p v ht] at hcompare
      have hlocal := count_vars_pairedFormula v
      have hmul := Nat.mul_le_mul hn hlocal
      omega

/-- Injective compaction preserves the actual literal-occurrence bound. -/
theorem count_vars_formula_le_three {φ : CNF ℕ}
    (hw : ∀ c ∈ φ, c.length ≤ 3) (hv : ∀ v, φ.vars.count v ≤ 3) :
    ∀ v, (formula φ).vars.count v ≤ 3 :=
  CNF.count_vars_compact_le (rawFormula φ) (count_vars_rawFormula_le_three hw hv)

end Cslib.Complexity.SAT.ParsimoniousPlanar
