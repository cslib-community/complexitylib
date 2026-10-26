/-
Copyright (c) 2026 Bolton Bailey, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.PCP.Encoded.Power
public import Complexity.Computability.PCP.Encoded.SelectedComposition
public import Complexity.Computability.PCP.Amplification.Family

/-!
# Executable amplification rounds

A round follows the preprocessed graph's rotations, constructs every supplied powered edge and
its Boolean table, then applies the assignment tester and tabulates its output. The output uses
the fixed answer alphabet, so it has the same representation as the next round's input.

The degree, alphabet, walk length, killing rate, slot numbering and finite lists are fixed. All
claims are uniform in the runtime graph, and the construction certificate charges the complete
intermediate and output tables. Exact interpretations require complete duplicate-free lists.

## Main definitions

* `Cslib.PCP.Encoded.Graph.amplify`: the normalized preprocess, power, compose pipeline.

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

open Turing.MultiTapeTM ComputableTidilyInPolyTime Cslib.PCP.HadamardTester

variable {C α D : Type} [Fintype α] [DecidableEq α] [Fintype D] [DecidableEq D]
  {width : ℕ}

/-- A normalized amplification round. Each stage materializes the next stage's input graph. -/
def amplify (eval : C → α → α → Bool) (fallback : C)
    (rotate : ℕ × (ℕ × D) → ℕ × D) (T q : ℕ) [NeZero q]
    (walks : List (PowerLabel D T q))
    (number : SelectedComposeSlot (PowerAlphabet D α T) ≃ Fin width)
    (coins : List (Fin 5 × Rand (PowerAlphabet D α T))) (queries : List (Fin 6)) (g : Graph C) :
    Graph (SelectedAlphabet → SelectedAlphabet → Bool) :=
  (g.powerPreprocess eval fallback rotate T q walks).composeSelectedTabulated number coins queries

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
    (fallback : C) (T q : ℕ) [NeZero q] (walks : List (PowerLabel D T q))
    (number : SelectedComposeSlot (PowerAlphabet D α T) ≃ Fin width)
    (coins : List (Fin 5 × Rand (PowerAlphabet D α T))) (queries : List (Fin 6)) :
    ComputableInPolyTime
      (fun x => (graph x).amplify eval fallback rotate T q walks number coins queries)
      input (encoding (encPi (encPi encBool))) := by
  unfold amplify
  fun_prop

/-- The declared output vertex count is linear in the number of original edges. -/
@[simp]
theorem vertices_amplify (eval : C → α → α → Bool) (fallback : C)
    (rotate : ℕ × (ℕ × D) → ℕ × D) (T q : ℕ) [NeZero q]
    (walks : List (PowerLabel D T q))
    (number : SelectedComposeSlot (PowerAlphabet D α T) ≃ Fin width)
    (coins : List (Fin 5 × Rand (PowerAlphabet D α T))) (queries : List (Fin 6)) (g : Graph C) :
    (g.amplify eval fallback rotate T q walks number coins queries).vertices =
      (2 * g.edges.length + 2 * g.edges.length * walks.length) * width := by
  simp [amplify]

/-- Every original half-edge contributes one edge for each walk, coin and query triple. -/
@[simp]
theorem length_edges_amplify (eval : C → α → α → Bool) (fallback : C)
    (rotate : ℕ × (ℕ × D) → ℕ × D) (T q : ℕ) [NeZero q]
    (walks : List (PowerLabel D T q))
    (number : SelectedComposeSlot (PowerAlphabet D α T) ≃ Fin width)
    (coins : List (Fin 5 × Rand (PowerAlphabet D α T))) (queries : List (Fin 6)) (g : Graph C) :
    (g.amplify eval fallback rotate T q walks number coins queries).edges.length =
      2 * g.edges.length * walks.length * coins.length * queries.length := by
  simp [amplify]

section Correctness

variable (g : Graph C) (eval : C → α → α → Bool) (fallback : C)
  (family : (n : ℕ) → RotationMap (Fin n) D) (rotate : ℕ × (ℕ × D) → ℕ × D)
  (hrotate : ∀ n (v : Fin n) d, rotate (n, v.val, d) =
    (((family n).rot (v, d)).1.val, ((family n).rot (v, d)).2))
  (T q : ℕ) [NeZero q] (walks : List (PowerLabel D T q))
  (number : SelectedComposeSlot (PowerAlphabet D α T) ≃ Fin width)
  (coins : List (Fin 5 × Rand (PowerAlphabet D α T))) (queries : List (Fin 6))

include hrotate in
/-- Every generated endpoint lies in the declared range, independently of the input bounds. -/
theorem wellFormed_amplify :
    (g.amplify eval fallback rotate T q walks number coins queries).WellFormed := by
  apply WellFormed.composeSelectedTabulated
  exact g.wellFormed_powerPreprocess eval fallback family rotate hrotate T q walks

variable [Nonempty α]
  (hwalks : walks.Nodup) (hmemWalks : ∀ d, d ∈ walks)
  (hcoins : coins.Nodup) (hqueries : queries.Nodup)
  (hmemCoins : ∀ ω, ω ∈ coins) (hmemQueries : ∀ i, i ∈ queries)

include hrotate hwalks hmemWalks hcoins hqueries hmemCoins hmemQueries in
/-- The executable round retains the assignment tester's `1/840` fraction of the powered gap. -/
theorem div_le_unsatVal_amplify :
    ((g.regularPreprocess eval fallback family).power T q).toConstraintGraph.unsatVal / 840 ≤
      ((g.amplify eval fallback rotate T q walks number coins queries).toGraph id).unsatVal := by
  rw [← unsatVal_powerPreprocess g eval fallback family rotate hrotate T q walks hwalks hmemWalks]
  exact le_unsatVal_composeSelectedTabulated number coins queries _
    hcoins hqueries hmemCoins hmemQueries

include hrotate hwalks hmemWalks hcoins hqueries hmemCoins hmemQueries in
/-- The complete executable round inherits the mathematical amplification bound, using the
explicit cloud numberings selected by its preprocessing program. -/
theorem le_unsatVal_amplify [Nonempty D] (μ : ℝ)
    (hgap : ∀ n, (family n).spectralExpansion ≤ μ) (hμ : μ < 1) (hq : 2 ≤ q)
    (hT : T = 4 * Fintype.card α * (q - 1)) :
    ((q : ℝ) - 1) / ConstraintGraph.Amplification.denominator 840
        (Fintype.card α) (Fintype.card D) μ *
      min (ConstraintGraph.Amplification.retention (Fintype.card D) μ *
        (g.toGraph eval).unsatVal) (1 / T ^ 2) ≤
      ((g.amplify eval fallback rotate T q walks number coins queries).toGraph id).unsatVal :=
  ((g.toGraph eval).le_div_unsatVal_power_preprocessWith
    (g.preprocessExpanders eval fallback family μ hgap) 840 (by norm_num) hμ hq hT).trans
      (g.div_le_unsatVal_amplify eval fallback family rotate hrotate T q walks number coins queries
        hwalks hmemWalks hcoins hqueries hmemCoins hmemQueries)

include hrotate hwalks hmemWalks hcoins hqueries hmemCoins hmemQueries in
/-- A killing rate with sufficient gain doubles the value up to the fixed threshold. The
pre-composition bound is shared with the mathematical amplification proof. -/
theorem min_le_unsatVal_amplify [Nonempty D] (μ : ℝ)
    (hgap : ∀ n, (family n).spectralExpansion ≤ μ) (hμ : μ < 1) (hq : 2 ≤ q)
    (hT : T = 4 * Fintype.card α * (q - 1))
    {γ : ℝ} (hγ : 0 ≤ γ)
    (hgain : 2 ≤ ConstraintGraph.Amplification.gain 840
      (Fintype.card α) (Fintype.card D) T q μ γ) :
    min (2 * (g.toGraph eval).unsatVal) γ ≤
      ((g.amplify eval fallback rotate T q walks number coins queries).toGraph id).unsatVal :=
  ((g.toGraph eval).min_le_div_unsatVal_power_preprocessWith
    (g.preprocessExpanders eval fallback family μ hgap) 840 (by norm_num) hμ hq hT hγ hgain).trans
      (g.div_le_unsatVal_amplify eval fallback family rotate hrotate T q walks number coins queries
        hwalks hmemWalks hcoins hqueries hmemCoins hmemQueries)

include hrotate hwalks hmemWalks hcoins hqueries hmemCoins hmemQueries in
/-- A complete round preserves satisfiability whenever the expander family has a spectral gap. -/
theorem satisfiable_amplify_iff [Nonempty D] (μ : ℝ)
    (hgap : ∀ n, (family n).spectralExpansion ≤ μ) (hμ : μ < 1) (hT : 1 ≤ T) (hq : 2 ≤ q) :
    ((g.amplify eval fallback rotate T q walks number coins queries).toGraph id).Satisfiable ↔
      (g.toGraph eval).Satisfiable := by
  rw [amplify, satisfiable_composeSelectedTabulated_iff number coins queries _ hcoins hqueries
    hmemCoins hmemQueries, satisfiable_powerPreprocess_iff g eval fallback family rotate hrotate
    T q walks hwalks hmemWalks, RegularConstraintGraph.satisfiable_power_iff _ _ _ hT hq]
  exact (g.toGraph eval).satisfiable_preprocessWith_iff
    (g.preprocessExpanders eval fallback family μ hgap) hμ

end Correctness

end Cslib.PCP.Encoded.Graph
