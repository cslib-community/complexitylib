/-
Copyright (c) 2026 Bolton Bailey, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.Encoded.Power
public import CslibFrontier.Computability.PCP.Encoded.SelectedComposition
public import CslibFrontier.Computability.PCP.Amplification.Family

/-!
# Executable amplification rounds

A round follows the preprocessed graph's rotations, constructs the powered edge of every killed
walk with its Boolean table, then applies the selected assignment tester and tabulates its output.
The output uses the fixed answer alphabet, so it has the same representation as the next round's
input.

The killed walks and the tester's slots, coins and queries are enumerated constructively
(`FinEnum`), so a round takes no lists and needs no completeness hypotheses. The degree, alphabet,
walk length and killing rate are fixed. All claims are uniform in the runtime graph, and the
construction certificate charges the complete intermediate and output tables.

## Main definitions

* `Cslib.PCP.Encoded.Graph.amplify`: the normalized preprocess, power, compose round.

## Main results

* `Cslib.PCP.Encoded.Graph.isPolyTime_amplify`: compositional construction certificate.
* `Cslib.PCP.Encoded.Graph.satisfiable_amplify_iff`: preservation of satisfiability.
* `Cslib.PCP.Encoded.Graph.le_unsatVal_amplify`: the full quantitative amplification bound.
* `Cslib.PCP.Encoded.Graph.min_le_unsatVal_amplify`: sufficient fixed gain doubles the value up to
  the threshold.

## References

* [I. Dinur, *The PCP theorem by gap amplification*][Dinur2007]
-/

@[expose] public section

namespace Cslib.PCP.Encoded.Graph

open Turing.MultiTapeTM Cslib.PCP.HadamardTester

attribute [local instance] HadamardTester.Rand.finEnum SelectedComposeSlot.finEnum

variable {C α D : Type} [FinEnum α] [FinEnum D]

/-- A normalized amplification round: power the preprocessed graph along every killed walk, then
compose with every selected check and query. Each stage materializes the next stage's input. -/
def amplify (eval : C → α → α → Bool) (fallback : C) (rotate : ℕ × (ℕ × D) → ℕ × D)
    (T q : ℕ) [NeZero q] (g : Graph C) : Graph (SelectedAlphabet → SelectedAlphabet → Bool) :=
  (g.powerPreprocess eval fallback rotate T q (FinEnum.toList _)).composeSelectedEnumerated

/-- Any certified graph expression can feed a round, with all internal finite encodings hidden. -/
@[fun_prop]
theorem isPolyTime_amplify {Input : Type} {input : Input ↪ List Bool}
    {enc : C ↪ List Bool} {alphabet : α ↪ List Bool} {labelEncoding : D ↪ List Bool}
    {graph : Input → Graph C} {eval : C → α → α → Bool} {rotate : ℕ × (ℕ × D) → ℕ × D}
    (hgraph : ComputableInPolyTime graph input (encoding enc))
    (hrotate : ComputableInPolyTime rotate
      (encPair encUnary (encPair encUnary labelEncoding)) (encPair encUnary labelEncoding))
    (heval : ComputableInPolyTime (fun p : C × (α × α) => eval p.1 p.2.1 p.2.2)
      (encPair enc (encPair alphabet alphabet)) encBool)
    (fallback : C) (T q : ℕ) [NeZero q] :
    ComputableInPolyTime (fun x => (graph x).amplify eval fallback rotate T q)
      input (encoding encConstraintTable) :=
  isPolyTime_composeSelectedEnumerated (isPolyTime_powerPreprocess hgraph hrotate heval
    fallback T q _ (output := encPi (encPi encBool)))

/-- The output vertex count is linear in the number of original edges. -/
@[simp]
theorem vertices_amplify (eval : C → α → α → Bool) (fallback : C)
    (rotate : ℕ × (ℕ × D) → ℕ × D) (T q : ℕ) [NeZero q] (g : Graph C) :
    (g.amplify eval fallback rotate T q).vertices =
      (2 * g.edges.length + 2 * g.edges.length * Fintype.card (PowerLabel D T q)) *
        Fintype.card (SelectedComposeSlot (PowerAlphabet D α T)) := by
  simp only [amplify, vertices_composeSelectedEnumerated, vertices_powerPreprocess,
    length_edges_powerPreprocess, FinEnum.toList, List.length_map, List.length_finRange,
    FinEnum.card_eq_fintypeCard, Fintype.card_eq_nat_card]

/-- Every original half-edge contributes one edge for each killed walk, coin and query. -/
@[simp]
theorem length_edges_amplify (eval : C → α → α → Bool) (fallback : C)
    (rotate : ℕ × (ℕ × D) → ℕ × D) (T q : ℕ) [NeZero q] (g : Graph C) :
    (g.amplify eval fallback rotate T q).edges.length =
      2 * g.edges.length * Fintype.card (PowerLabel D T q) *
        Fintype.card (Fin 5 × Rand (PowerAlphabet D α T)) * 6 := by
  simp only [amplify, length_edges_composeSelectedEnumerated, length_edges_powerPreprocess,
    FinEnum.toList, List.length_map, List.length_finRange, FinEnum.card_eq_fintypeCard,
    Fintype.card_eq_nat_card]

section Correctness

variable (g : Graph C) (eval : C → α → α → Bool) (fallback : C)
  (family : (n : ℕ) → RotationMap (Fin n) D) (rotate : ℕ × (ℕ × D) → ℕ × D)
  (hrotate : ∀ n (v : Fin n) d, rotate (n, v.val, d) =
    (((family n).rot (v, d)).1.val, ((family n).rot (v, d)).2))
  (T q : ℕ) [NeZero q]

include hrotate in
/-- Every generated endpoint lies in the declared range, independently of the input bounds. -/
theorem wellFormed_amplify : (g.amplify eval fallback rotate T q).WellFormed :=
  WellFormed.composeSelectedEnumerated
    (g.wellFormed_powerPreprocess eval fallback family rotate hrotate T q _)

variable [Nonempty α]

include hrotate in
/-- The executable round retains the assignment tester's `1/840` fraction of the powered gap. -/
theorem div_le_unsatVal_amplify :
    ((g.regularPreprocess eval fallback family).power T q).toConstraintGraph.unsatVal / 840 ≤
      ((g.amplify eval fallback rotate T q).toGraph id).unsatVal := by
  rw [← unsatVal_powerPreprocess g eval fallback family rotate hrotate T q _
    FinEnum.nodup_toList FinEnum.mem_toList]
  exact le_unsatVal_composeSelectedEnumerated _

include hrotate in
/-- The complete executable round inherits the mathematical amplification bound, using the
explicit cloud numberings selected by its preprocessing program. -/
theorem le_unsatVal_amplify [Nonempty D] (μ : ℝ)
    (hgap : ∀ n, (family n).spectralExpansion ≤ μ) (hμ : μ < 1) (hq : 2 ≤ q)
    (hT : T = 4 * Fintype.card α * (q - 1)) :
    ((q : ℝ) - 1) / ConstraintGraph.Amplification.denominator 840
        (Fintype.card α) (Fintype.card D) μ *
      min (ConstraintGraph.Amplification.retention (Fintype.card D) μ *
        (g.toGraph eval).unsatVal) (1 / T ^ 2) ≤
      ((g.amplify eval fallback rotate T q).toGraph id).unsatVal :=
  ((g.toGraph eval).le_div_unsatVal_power_preprocessWith
    (g.preprocessExpanders eval fallback family μ hgap) 840 (by norm_num) hμ hq hT).trans
      (g.div_le_unsatVal_amplify eval fallback family rotate hrotate T q)

include hrotate in
/-- A killing rate with sufficient gain doubles the value up to the fixed threshold. The
pre-composition bound is shared with the mathematical amplification proof. -/
theorem min_le_unsatVal_amplify [Nonempty D] (μ : ℝ)
    (hgap : ∀ n, (family n).spectralExpansion ≤ μ) (hμ : μ < 1) (hq : 2 ≤ q)
    (hT : T = 4 * Fintype.card α * (q - 1))
    {γ : ℝ} (hγ : 0 ≤ γ)
    (hgain : 2 ≤ ConstraintGraph.Amplification.gain 840
      (Fintype.card α) (Fintype.card D) T q μ γ) :
    min (2 * (g.toGraph eval).unsatVal) γ ≤
      ((g.amplify eval fallback rotate T q).toGraph id).unsatVal :=
  ((g.toGraph eval).min_le_div_unsatVal_power_preprocessWith
    (g.preprocessExpanders eval fallback family μ hgap) 840 (by norm_num) hμ hq hT hγ hgain).trans
      (g.div_le_unsatVal_amplify eval fallback family rotate hrotate T q)

include hrotate in
/-- A complete round preserves satisfiability whenever the expander family has a spectral gap. -/
theorem satisfiable_amplify_iff [Nonempty D] (μ : ℝ)
    (hgap : ∀ n, (family n).spectralExpansion ≤ μ) (hμ : μ < 1) (hT : 1 ≤ T) (hq : 2 ≤ q) :
    ((g.amplify eval fallback rotate T q).toGraph id).Satisfiable ↔
      (g.toGraph eval).Satisfiable := by
  rw [amplify, satisfiable_composeSelectedEnumerated_iff, satisfiable_powerPreprocess_iff g eval
    fallback family rotate hrotate T q _ FinEnum.nodup_toList FinEnum.mem_toList,
    RegularConstraintGraph.satisfiable_power_iff _ _ _ hT hq]
  exact (g.toGraph eval).satisfiable_preprocessWith_iff
    (g.preprocessExpanders eval fallback family μ hgap) hμ

end Correctness

end Cslib.PCP.Encoded.Graph
