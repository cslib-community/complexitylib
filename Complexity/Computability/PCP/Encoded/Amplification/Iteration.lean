/-
Copyright (c) 2026 Bolton Bailey, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.PCP.Encoded.Amplification
public import Complexity.Computability.PCP.Encoded.Iteration
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Iteration
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Log
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Iterating executable amplification rounds

Normalized constraint tables keep the alphabet and representation fixed across rounds. A fixed
round multiplies the sum of vertices and edges by a constant and creates well-formed endpoints;
every stored constraint has the same bounded table encoding. The existing iteration calculus
therefore certifies a logarithmic number of complete rounds, charging all intermediate states.

The parameters and finite enumeration lists are fixed before the runtime graph. Construction
certificates need no completeness assumption on those lists; gap and satisfiability claims do.

## Main definitions

* `Cslib.PCP.Encoded.Graph.amplifyIter`: repeated normalized amplification.

## Main results

* `Cslib.PCP.Encoded.Graph.isPolyTime_amplifyIter_clog`: a certificate for logarithmically many
  rounds, including their full intermediate and output table encodings.
* `Cslib.PCP.Encoded.Graph.satisfiable_amplifyIter_iff`: complete rounds preserve satisfiability.
* `Cslib.PCP.Encoded.Graph.gap_le_unsatVal_amplifyIter_clog`: logarithmically many complete rounds
  give a fixed positive gap on every unsatisfiable input.

## References

* [I. Dinur, *The PCP theorem by gap amplification*][Dinur2007]
-/

@[expose] public section

namespace Cslib.PCP.Encoded.Graph

open Turing.MultiTapeTM ComputableTidilyInPolyTime Cslib.PCP.HadamardTester

local notation "Constraint" => (SelectedAlphabet → SelectedAlphabet → Bool)

variable {D : Type} [Fintype D] [DecidableEq D] {width : ℕ}

/-- Iterate the same normalized round over its fixed answer alphabet. Irreducibility keeps
failed certificate search from unfolding the complete loop; clients use its resource and semantic
contracts, or unfold the definition explicitly when reasoning about the program. -/
@[irreducible]
def amplifyIter (fallback : Constraint) (rotate : ℕ × (ℕ × D) → ℕ × D)
    (T q : ℕ) [NeZero q] (walks : List (PowerLabel D T q))
    (number : SelectedComposeSlot (PowerAlphabet D SelectedAlphabet T) ≃ Fin width)
    (coins : List (Fin 5 × Rand (PowerAlphabet D SelectedAlphabet T)))
    (queries : List (Fin 6)) (k : ℕ) :
    Graph Constraint → Graph Constraint :=
  (amplify id fallback rotate T q walks number coins queries)^[k]

/-- A logarithmic number of normalized rounds has polynomial cost in the original input
encoding. Well-formed endpoints and the full table bound supply the loop's size invariant. -/
@[fun_prop]
theorem isPolyTime_amplifyIter_clog {Input : Type} {input : Input ↪ List Bool}
    {graph : Input → Graph Constraint} {labelEncoding : D ↪ List Bool}
    (hgraph : ComputableInPolyTime graph input (encoding (encPi (encPi encBool))))
    (hwellFormed : ∀ x, (graph x).WellFormed)
    (family : (n : ℕ) → RotationMap (Fin n) D) (rotate : ℕ × (ℕ × D) → ℕ × D)
    (hrotate : ∀ n (v : Fin n) d, rotate (n, v.val, d) =
      (((family n).rot (v, d)).1.val, ((family n).rot (v, d)).2))
    (hcost : ComputableInPolyTime rotate
      (encPair encUnary (encPair encUnary labelEncoding)) (encPair encUnary labelEncoding))
    (fallback : Constraint) (T q : ℕ) [NeZero q] (walks : List (PowerLabel D T q))
    (number : SelectedComposeSlot (PowerAlphabet D SelectedAlphabet T) ≃ Fin width)
    (coins : List (Fin 5 × Rand (PowerAlphabet D SelectedAlphabet T))) (queries : List (Fin 6)) :
    ComputableInPolyTime
      (fun x => amplifyIter fallback rotate T q walks number coins queries
        (Nat.clog 2 (graph x).edges.length) (graph x))
      input (encoding (encPi (encPi encBool))) := by
  have hgraph := hgraph.tidy
  have hcost := hcost.tidy
  refine .of_tidy ?_
  let factor := (2 + 2 * walks.length) * width + 2 * walks.length * coins.length * queries.length
  let descriptorBound := Fintype.card SelectedAlphabet * (6 * Fintype.card SelectedAlphabet + 1)
  have hgrowth (g : Graph Constraint) :
      (g.amplify id fallback rotate T q walks number coins queries).vertices +
        (g.amplify id fallback rotate T q walks number coins queries).edges.length ≤
          factor * (g.vertices + g.edges.length) := by
    calc _ = factor * g.edges.length := by
           simp only [vertices_amplify, length_edges_amplify, factor]
           ring
      _ ≤ _ := Nat.mul_le_mul_left _ (Nat.le_add_left _ _)
  have heval :=
    (isPolyTime_constraintTableEval (α := SelectedAlphabet) (encPair encBool (encPi encBool))).tidy
  have hedges := (isPolyTime_edges (graph := fun g : Graph Constraint => g)
    (enc := encPi (encPi encBool)) (.of_tidy .id')).tidy
  have hamplify := ComputableInPolyTime.tidy (isPolyTime_amplify (graph := id) (eval := id)
    (alphabet := encPair encBool (encPi encBool)) (.of_tidy .id') (.of_tidy hcost)
    (.of_tidy heval) fallback T q walks number coins queries)
  unfold amplifyIter
  apply ComputableTidilyInPolyTime.iterate (by fun_prop) hgraph (by fun_prop)
    (polyBounded_iterationSize_clog (.of_tidy hgraph) factor descriptorBound)
  exact fun x _ hi => iterate_length_encoding_le (valid := WellFormed) factor descriptorBound
    (fun g _ =>
      g.wellFormed_amplify id fallback family rotate hrotate T q walks number coins queries)
    (fun _ h => h) (fun _ _ edge _ => length_constraintTable_le edge.constraint)
    (fun g _ => hgrowth g) (hwellFormed x) hi

section Correctness

variable [Nonempty D] (fallback : Constraint)
  (family : (n : ℕ) → RotationMap (Fin n) D) (rotate : ℕ × (ℕ × D) → ℕ × D)
  (hrotate : ∀ n (v : Fin n) d, rotate (n, v.val, d) =
    (((family n).rot (v, d)).1.val, ((family n).rot (v, d)).2))
  (T q : ℕ) [NeZero q] (walks : List (PowerLabel D T q))
  (number : SelectedComposeSlot (PowerAlphabet D SelectedAlphabet T) ≃ Fin width)
  (coins : List (Fin 5 × Rand (PowerAlphabet D SelectedAlphabet T))) (queries : List (Fin 6))
  (hwalks : walks.Nodup) (hmemWalks : ∀ d, d ∈ walks)
  (hcoins : coins.Nodup) (hqueries : queries.Nodup)
  (hmemCoins : ∀ ω, ω ∈ coins) (hmemQueries : ∀ i, i ∈ queries)
  (μ : ℝ) (hgap : ∀ n, (family n).spectralExpansion ≤ μ) (hμ : μ < 1)

include hrotate hwalks hmemWalks hcoins hqueries hmemCoins hmemQueries hgap hμ in
/-- Every complete round preserves satisfiability, hence so does their iteration. -/
theorem satisfiable_amplifyIter_iff (hT : 1 ≤ T) (hq : 2 ≤ q) (k : ℕ)
    (g : Graph Constraint) :
    ((amplifyIter fallback rotate T q walks number coins queries k g).toGraph id).Satisfiable ↔
      (g.toGraph id).Satisfiable := by
  unfold amplifyIter
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', satisfiable_amplify_iff _ id fallback family
      rotate hrotate T q walks number coins queries hwalks hmemWalks hcoins hqueries hmemCoins
      hmemQueries μ hgap hμ hT hq]
    exact ih

include hrotate hwalks hmemWalks hcoins hqueries hmemCoins hmemQueries hgap hμ in
/-- The complete rounds double the value until the fixed threshold is reached. -/
theorem min_le_unsatVal_amplifyIter (hq : 2 ≤ q)
    (hT : T = 4 * Fintype.card SelectedAlphabet * (q - 1))
    {γ : ℝ} (hγ : 0 ≤ γ)
    (hgain : 2 ≤ ConstraintGraph.Amplification.gain 840
      (Fintype.card SelectedAlphabet) (Fintype.card D) T q μ γ)
    (k : ℕ) (g : Graph Constraint) :
    min (2 ^ k * (g.toGraph id).unsatVal) γ ≤
      ((amplifyIter fallback rotate T q walks number coins queries k g).toGraph id).unsatVal := by
  unfold amplifyIter
  exact min_two_pow_mul_le_iterate _ (fun graph : Graph Constraint => (graph.toGraph id).unsatVal)
      hγ (fun graph => graph.min_le_unsatVal_amplify id fallback family rotate hrotate
        T q walks number coins queries hwalks hmemWalks hcoins hqueries hmemCoins hmemQueries
        μ hgap hμ hq hT hγ hgain) k g

include hrotate hwalks hmemWalks hcoins hqueries hmemCoins hmemQueries hgap hμ in
/-- Enough complete rounds turn every unsatisfiable input into a graph above the fixed gap. -/
theorem gap_le_unsatVal_amplifyIter (hq : 2 ≤ q)
    (hT : T = 4 * Fintype.card SelectedAlphabet * (q - 1))
    {γ : ℝ} (hγ : 0 ≤ γ) (hγ₁ : γ ≤ 1)
    (hgain : 2 ≤ ConstraintGraph.Amplification.gain 840
      (Fintype.card SelectedAlphabet) (Fintype.card D) T q μ γ)
    {g : Graph Constraint} (hunsat : ¬ (g.toGraph id).Satisfiable) {k : ℕ}
    (hk : g.edges.length ≤ 2 ^ k) :
    γ ≤
      ((amplifyIter fallback rotate T q walks number coins queries k g).toGraph id).unsatVal :=
  (g.toGraph id).gap_le_of_min_two_pow_mul_le hγ₁ hunsat
    (by simpa only [Fintype.card_fin] using hk)
    (min_le_unsatVal_amplifyIter fallback family rotate hrotate T q walks number coins queries
      hwalks hmemWalks hcoins hqueries hmemCoins hmemQueries μ hgap hμ hq hT hγ hgain k g)

include hrotate hwalks hmemWalks hcoins hqueries hmemCoins hmemQueries hgap hμ in
/-- The logarithmic program has a constant soundness gap on every unsatisfiable input. -/
theorem gap_le_unsatVal_amplifyIter_clog (hq : 2 ≤ q)
    (hT : T = 4 * Fintype.card SelectedAlphabet * (q - 1))
    {γ : ℝ} (hγ : 0 ≤ γ) (hγ₁ : γ ≤ 1)
    (hgain : 2 ≤ ConstraintGraph.Amplification.gain 840
      (Fintype.card SelectedAlphabet) (Fintype.card D) T q μ γ)
    {g : Graph Constraint} (hunsat : ¬ (g.toGraph id).Satisfiable) :
    γ ≤
      ((amplifyIter fallback rotate T q walks number coins queries
        (Nat.clog 2 g.edges.length) g).toGraph id).unsatVal :=
  gap_le_unsatVal_amplifyIter fallback family rotate hrotate T q walks number coins queries
    hwalks hmemWalks hcoins hqueries hmemCoins hmemQueries μ hgap hμ hq hT hγ hγ₁ hgain hunsat
    (Nat.le_pow_clog (by decide) _)

end Correctness

end Cslib.PCP.Encoded.Graph
