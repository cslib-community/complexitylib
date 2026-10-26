/-
Copyright (c) 2026 Bolton Bailey, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.PCP.Encoded.Amplification
public import Complexity.Computability.PCP.Encoded.SelectedComposition.Enumeration

/-!
# Complete enumeration for executable amplification

Constructive finite enumerations supply the walk labels, assignment-tester slots, coins, and
queries of an amplification round. The enumerations are fixed with the degree and alphabet;
the graph is runtime input, and the construction certificate charges all materialized tables.
The fixed enumerations can be enormous, so this interface asserts polynomial time in the graph
encoding rather than practical running time at arbitrary fixed parameters.

## Main definitions

* `Cslib.PCP.Encoded.Graph.amplifyEnumerated`: an amplification round with complete enumerations.

## Main results

* `Cslib.PCP.Encoded.Graph.isPolyTime_amplifyEnumerated`: a uniform construction certificate.
* `Cslib.PCP.Encoded.Graph.satisfiable_amplifyEnumerated_iff`: preservation of satisfiability.
* `Cslib.PCP.Encoded.Graph.le_unsatVal_amplifyEnumerated`: the quantitative amplification bound.
* `Cslib.PCP.Encoded.Graph.min_le_unsatVal_amplifyEnumerated`: doubling up to a fixed threshold.

## References

* [I. Dinur, *The PCP theorem by gap amplification*][Dinur2007]
-/

@[expose] public section

namespace Cslib.PCP

open Turing.MultiTapeTM ComputableTidilyInPolyTime Cslib.PCP.HadamardTester

namespace Encoded.Graph

attribute [local instance] HadamardTester.Rand.finEnum SelectedComposeSlot.finEnum

variable {C α D : Type} [FinEnum α] [FinEnum D]

/-- An amplification round with complete constructive enumerations for every finite parameter. -/
def amplifyEnumerated (eval : C → α → α → Bool) (fallback : C)
    (rotate : ℕ × (ℕ × D) → ℕ × D) (T q : ℕ) [NeZero q] (g : Graph C) :
    Graph (SelectedAlphabet → SelectedAlphabet → Bool) :=
  g.amplify eval fallback rotate T q (FinEnum.toList (PowerLabel D T q)) FinEnum.equiv
    (FinEnum.toList (Fin 5 × Rand (PowerAlphabet D α T))) (FinEnum.toList (Fin 6))

/-- A certified graph expression feeds the round without finite enumeration proof obligations. -/
@[fun_prop]
theorem isPolyTime_amplifyEnumerated {Input : Type} {input : Input ↪ List Bool}
    {enc : C ↪ List Bool} {alphabet : α ↪ List Bool} {labelEncoding : D ↪ List Bool}
    {graph : Input → Graph C} {eval : C → α → α → Bool} {rotate : ℕ × (ℕ × D) → ℕ × D}
    (hgraph : ComputableInPolyTime graph input (encoding enc))
    (hrotate : ComputableInPolyTime rotate
      (encPair encUnary (encPair encUnary labelEncoding)) (encPair encUnary labelEncoding))
    (heval : ComputableInPolyTime (fun p : C × (α × α) => eval p.1 p.2.1 p.2.2)
      (encPair enc (encPair alphabet alphabet)) encBool)
    (fallback : C) (T q : ℕ) [NeZero q] :
    ComputableInPolyTime (fun x => (graph x).amplifyEnumerated eval fallback rotate T q)
      input (encoding (encPi (encPi encBool))) := by
  unfold amplifyEnumerated
  fun_prop

/-- The output vertex count uses the cardinalities of the complete finite enumerations. -/
@[simp]
theorem vertices_amplifyEnumerated (eval : C → α → α → Bool) (fallback : C)
    (rotate : ℕ × (ℕ × D) → ℕ × D) (T q : ℕ) [NeZero q] (g : Graph C) :
    (g.amplifyEnumerated eval fallback rotate T q).vertices =
      (2 * g.edges.length + 2 * g.edges.length * Fintype.card (PowerLabel D T q)) *
        Fintype.card (SelectedComposeSlot (PowerAlphabet D α T)) := by
  simp only [amplifyEnumerated, vertices_amplify, FinEnum.toList, List.length_map,
    List.length_finRange, FinEnum.card_eq_fintypeCard]

/-- Every walk, coin, and query contributes exactly one edge per original half-edge. -/
@[simp]
theorem length_edges_amplifyEnumerated (eval : C → α → α → Bool) (fallback : C)
    (rotate : ℕ × (ℕ × D) → ℕ × D) (T q : ℕ) [NeZero q] (g : Graph C) :
    (g.amplifyEnumerated eval fallback rotate T q).edges.length =
      2 * g.edges.length * Fintype.card (PowerLabel D T q) *
        Fintype.card (Fin 5 × Rand (PowerAlphabet D α T)) * Fintype.card (Fin 6) := by
  simp only [amplifyEnumerated, length_edges_amplify, FinEnum.toList, List.length_map,
    List.length_finRange, FinEnum.card_eq_fintypeCard]

section Correctness

variable (g : Graph C) (eval : C → α → α → Bool) (fallback : C)
  (family : (n : ℕ) → RotationMap (Fin n) D) (rotate : ℕ × (ℕ × D) → ℕ × D)
  (hrotate : ∀ n (v : Fin n) d, rotate (n, v.val, d) =
    (((family n).rot (v, d)).1.val, ((family n).rot (v, d)).2))
  (T q : ℕ) [NeZero q]

include hrotate in
/-- The complete round produces valid endpoint indices, even for malformed input graphs. -/
theorem wellFormed_amplifyEnumerated :
    (g.amplifyEnumerated eval fallback rotate T q).WellFormed :=
  g.wellFormed_amplify eval fallback family rotate hrotate T q
    (FinEnum.toList _) FinEnum.equiv (FinEnum.toList _) (FinEnum.toList _)

variable [Nonempty α]

include hrotate in
/-- The complete round retains the tester's `1/840` fraction of the powered value. -/
theorem div_le_unsatVal_amplifyEnumerated :
    ((g.regularPreprocess eval fallback family).power T q).toConstraintGraph.unsatVal / 840 ≤
      ((g.amplifyEnumerated eval fallback rotate T q).toGraph id).unsatVal :=
  g.div_le_unsatVal_amplify eval fallback family rotate hrotate T q
    (FinEnum.toList _) FinEnum.equiv (FinEnum.toList _) (FinEnum.toList _)
    FinEnum.nodup_toList FinEnum.mem_toList FinEnum.nodup_toList FinEnum.nodup_toList
    FinEnum.mem_toList FinEnum.mem_toList

include hrotate in
/-- Constructive enumeration discharges all completeness hypotheses of the quantitative bound. -/
theorem le_unsatVal_amplifyEnumerated [Nonempty D] (μ : ℝ)
    (hgap : ∀ n, (family n).spectralExpansion ≤ μ) (hμ : μ < 1) (hq : 2 ≤ q)
    (hT : T = 4 * Fintype.card α * (q - 1)) :
    ((q : ℝ) - 1) / ConstraintGraph.Amplification.denominator 840
        (Fintype.card α) (Fintype.card D) μ *
      min (ConstraintGraph.Amplification.retention (Fintype.card D) μ *
        (g.toGraph eval).unsatVal) (1 / T ^ 2) ≤
      ((g.amplifyEnumerated eval fallback rotate T q).toGraph id).unsatVal :=
  g.le_unsatVal_amplify eval fallback family rotate hrotate T q
    (FinEnum.toList _) FinEnum.equiv (FinEnum.toList _) (FinEnum.toList _)
    FinEnum.nodup_toList FinEnum.mem_toList FinEnum.nodup_toList FinEnum.nodup_toList
    FinEnum.mem_toList FinEnum.mem_toList μ hgap hμ hq hT

include hrotate in
/-- A killing rate with sufficient gain doubles the value up to the fixed threshold. -/
theorem min_le_unsatVal_amplifyEnumerated [Nonempty D] (μ : ℝ)
    (hgap : ∀ n, (family n).spectralExpansion ≤ μ) (hμ : μ < 1) (hq : 2 ≤ q)
    (hT : T = 4 * Fintype.card α * (q - 1))
    {γ : ℝ} (hγ : 0 ≤ γ)
    (hgain : 2 ≤ ConstraintGraph.Amplification.gain 840
      (Fintype.card α) (Fintype.card D) T q μ γ) :
    min (2 * (g.toGraph eval).unsatVal) γ ≤
      ((g.amplifyEnumerated eval fallback rotate T q).toGraph id).unsatVal :=
  g.min_le_unsatVal_amplify eval fallback family rotate hrotate T q
    (FinEnum.toList _) FinEnum.equiv (FinEnum.toList _) (FinEnum.toList _)
    FinEnum.nodup_toList FinEnum.mem_toList FinEnum.nodup_toList FinEnum.nodup_toList
    FinEnum.mem_toList FinEnum.mem_toList μ hgap hμ hq hT hγ hgain

include hrotate in
/-- A complete round preserves satisfiability whenever the expander family has a spectral gap. -/
theorem satisfiable_amplifyEnumerated_iff [Nonempty D] (μ : ℝ)
    (hgap : ∀ n, (family n).spectralExpansion ≤ μ) (hμ : μ < 1) (hT : 1 ≤ T) (hq : 2 ≤ q) :
    ((g.amplifyEnumerated eval fallback rotate T q).toGraph id).Satisfiable ↔
      (g.toGraph eval).Satisfiable :=
  g.satisfiable_amplify_iff eval fallback family rotate hrotate T q
    (FinEnum.toList _) FinEnum.equiv (FinEnum.toList _) (FinEnum.toList _)
    FinEnum.nodup_toList FinEnum.mem_toList FinEnum.nodup_toList FinEnum.nodup_toList
    FinEnum.mem_toList FinEnum.mem_toList μ hgap hμ hT hq

end Correctness

end Encoded.Graph

end Cslib.PCP
