/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.FirstOrder.Reduction
public import CslibFrontier.Logics.FirstOrder.ZeroOneLaw.ExtensionProbability
public import CslibFrontier.Logics.FirstOrder.ZeroOneLaw.Transfer
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Order.Basic

/-!
# The 0-1 law for first-order logic on finite graphs

**Theorem** (Glebskiĭ–Kogan–Liogon'kiĭ–Talanov 1969; Fagin 1976). For every first-order
sentence `φ` in the language of graphs, the probability that the uniform random labelled graph
`G(n, 1/2)` on `n` vertices satisfies `φ` tends to `0` or to `1` as `n → ∞`
[GlebskiiKoganLiogonkiiTalanov1969] [Fagin1976] [Libkin2004, Chapter 12].

The proof is Fagin's. Every extension axiom holds almost surely
(`Cslib.Logic.FO.graph.tendsto_randomGraphProb_extensionAxiom`), hence so does every finite subset
of the theory `T` of the random graph. By compactness `T` is satisfiable; it has no finite models
and is `ℵ₀`-categorical, so by the Łoś–Vaught test it is complete. If `T ⊨ φ` then a finite
subset of `T` entails `φ`, so `φ` holds almost surely; otherwise `T ⊨ ¬φ` and `φ` fails almost
surely. In particular, the sentences holding almost surely are exactly the consequences of `T`.

The 0-1 law shows that a graph property is not first-order definable when its probability does not
converge to `0` or `1`: for example, having an even number of vertices (probability alternating
between `1` and `0`) or an even number of edges (probability exactly `1/2` for `n ≥ 2`).

## Main results

* `Cslib.Logic.FO.graph.randomGraphProb_satisfies_eq`: satisfaction probability in `G(n, 1/2)`
  matches sentence probability on graph structures.
* `Cslib.Logic.FO.graph.tendsto_randomGraphProb_finset`: every finite subset of the theory of the
  random graph holds almost surely.
* `Cslib.Logic.FO.graph.isSatisfiable_randomGraphTheory`: the theory of the random graph is
  satisfiable.
* `Cslib.Logic.FO.graph.isComplete_randomGraphTheory`: it is complete.
* `Cslib.Logic.FO.graph.zero_one_law`: the 0-1 law.
* `Cslib.Logic.FO.graph.tendsto_randomGraphProb_one_iff`,
  `Cslib.Logic.FO.graph.tendsto_randomGraphProb_zero_iff`: the limit is `1` exactly when `T ⊨ φ`,
  and `0` exactly when `T ⊨ ¬φ`.
* `Cslib.Logic.FO.graph.not_exists_sentence_of_not_tendsto`: a property whose probability tends
  neither to `0` nor to `1` agrees with no sentence on all large graphs.
* `Cslib.Logic.FO.graph.not_exists_sentence_even_card`,
  `Cslib.Logic.FO.graph.not_definable_even_card`: an even number of vertices is not first-order
  definable on graphs.
* `Cslib.Logic.FO.graph.not_exists_sentence_evenEdges`: neither is an even number of edges.

## References

* [Y. V. Glebskiĭ, D. I. Kogan, M. I. Liogon'kiĭ and V. A. Talanov, *Range and degree of
  realizability of formulas in the restricted predicate calculus*]
  [GlebskiiKoganLiogonkiiTalanov1969]
* [R. Fagin, *Probabilities on finite models*][Fagin1976]
* [L. Libkin, *Elements of Finite Model Theory*][Libkin2004], Chapter 12.
-/

public section

open FirstOrder Language Structure Cardinal CategoryTheory

namespace Cslib.Logic.FO.graph

/-- The sequence of uniform random graph distributions mapped to first-order graph structures. -/
noncomputable def randomGraphStructure (n : ℕ) : PMF (Language.graph.Structure (Fin n)) :=
  (randomGraph n).map SimpleGraph.structure

/-- The probability that `G(n, 1/2)` satisfies a first-order sentence `φ` equals the sentence
probability under the pushforward distribution on graph structures. -/
theorem randomGraphProb_satisfies_eq (n : ℕ) (φ : Language.graph.Sentence) :
    randomGraphProb n (fun G => Satisfies G φ) = sentenceProb (randomGraphStructure n) φ := by
  rw [sentenceProb_def, structProb_def, randomGraphStructure, PMF.toOuterMeasure_map_apply,
    randomGraphProb_def]
  rfl

/-- The probability that `G(n, 1/2)` satisfies a property of its structure equals the structure
probability under the pushforward distribution on graph structures. -/
theorem randomGraphProb_structure_eq (n : ℕ) (P : Language.graph.Structure (Fin n) → Prop) :
    randomGraphProb n (fun G => P G.structure) = structProb (randomGraphStructure n) P := by
  rw [structProb_def, randomGraphStructure, PMF.toOuterMeasure_map_apply, randomGraphProb_def]
  rfl

/-- Every sentence of the theory of the random graph holds in `G(n, 1/2)` with probability tending
to `1`. -/
theorem tendsto_randomGraphProb_of_mem_randomGraphTheory {φ : Language.graph.Sentence}
    (h : φ ∈ randomGraphTheory) :
    Filter.Tendsto (fun n => randomGraphProb n fun G => Satisfies G φ) Filter.atTop (nhds 1) := by
  rcases mem_randomGraphTheory.1 h with hφ | ⟨k, s, rfl⟩
  · have h : ∀ n, randomGraphProb n (fun G => ¬Satisfies G φ) = 0 := fun n => by
      have : (fun G : SimpleGraph (Fin n) => ¬Satisfies G φ) = fun _ => False :=
        funext fun G => propext (iff_false_intro (not_not_intro
          (satisfies_of_mem_simpleGraph G hφ)))
      rw [this, randomGraphProb_false]
    have h1 : (fun n => randomGraphProb n fun G => Satisfies G φ) = fun _ => 1 := by
      funext n
      have := randomGraphProb_not n fun G => Satisfies G φ
      rw [h n] at this
      linarith
    rw [h1]
    exact tendsto_const_nhds
  · exact tendsto_randomGraphProb_extensionAxiom k s

/-- Every sentence of the theory of the random graph holds in `randomGraphStructure` with
probability tending to `1`. -/
theorem tendsto_sentenceProb_randomGraphStructure {φ : Language.graph.Sentence}
    (h : φ ∈ randomGraphTheory) :
    Filter.Tendsto (fun n => sentenceProb (randomGraphStructure n) φ) Filter.atTop (nhds 1) := by
  simp only [← randomGraphProb_satisfies_eq]
  exact tendsto_randomGraphProb_of_mem_randomGraphTheory h

/-- Every finite subset of the theory of the random graph holds in `G(n, 1/2)` with probability
tending to `1`. -/
theorem tendsto_randomGraphProb_finset (T₀ : Finset Language.graph.Sentence)
    (hT₀ : (T₀ : Language.graph.Theory) ⊆ randomGraphTheory) :
    Filter.Tendsto (fun n => randomGraphProb n fun G => ∀ φ ∈ T₀, Satisfies G φ)
      Filter.atTop (nhds 1) := by
  have h := tendsto_structProb_forall_finset randomGraphStructure T₀ fun φ hφ =>
    tendsto_sentenceProb_randomGraphStructure (hT₀ hφ)
  simp only [← randomGraphProb_structure_eq] at h
  exact h

/-- The theory of the random graph is satisfiable. By compactness it suffices that each finite
subset has a model, and a finite subset holds in `G(n, 1/2)` with positive probability for large
`n`. -/
theorem isSatisfiable_randomGraphTheory : randomGraphTheory.IsSatisfiable :=
  isSatisfiable_of_tendsto_sentenceProb randomGraphStructure
    fun _ => tendsto_sentenceProb_randomGraphStructure

/-- The theory of the random graph is complete, by the Łoś–Vaught test: it is satisfiable, has
no finite models and is `ℵ₀`-categorical in a countable language [Fagin1976]
[Libkin2004, Chapter 12]. -/
theorem isComplete_randomGraphTheory : randomGraphTheory.IsComplete := by
  have hcard : lift.{0} Language.graph.card ≤ lift.{0} ℵ₀ := by
    have : Countable Language.graph.Symbols := by
      unfold Language.Symbols
      infer_instance
    rw [lift_aleph0, lift_le_aleph0]
    exact Cardinal.mk_le_aleph0
  exact aleph0_categorical_randomGraphTheory.{0}.isComplete ℵ₀ _ le_rfl hcard
    isSatisfiable_randomGraphTheory fun M => infinite_of_model_randomGraphTheory

/-- A consequence of the theory of the random graph holds in `G(n, 1/2)` with probability tending
to `1`. -/
theorem tendsto_randomGraphProb_of_models {φ : Language.graph.Sentence}
    (h : randomGraphTheory ⊨ᵇ φ) :
    Filter.Tendsto (fun n => randomGraphProb n fun G => Satisfies G φ) Filter.atTop (nhds 1) := by
  have h1 := tendsto_sentenceProb_of_models randomGraphStructure
    (fun _ => tendsto_sentenceProb_randomGraphStructure) h
  simpa only [randomGraphProb_satisfies_eq] using h1

/-- A sentence refuted by the theory of the random graph holds in `G(n, 1/2)` with probability
tending to `0`. -/
theorem tendsto_randomGraphProb_of_models_not {φ : Language.graph.Sentence}
    (h : randomGraphTheory ⊨ᵇ φ.not) :
    Filter.Tendsto (fun n => randomGraphProb n fun G => Satisfies G φ) Filter.atTop (nhds 0) := by
  have h0 := tendsto_sentenceProb_of_models_not randomGraphStructure
    (fun _ => tendsto_sentenceProb_randomGraphStructure) h
  simpa only [randomGraphProb_satisfies_eq] using h0

/-- **The 0-1 law for first-order logic on graphs** (Glebskiĭ–Kogan–Liogon'kiĭ–Talanov; Fagin).
For every first-order sentence `φ` in the language of graphs, the probability that the uniform
random labelled graph `G(n, 1/2)` satisfies `φ` tends to `0` or to `1`
[GlebskiiKoganLiogonkiiTalanov1969] [Fagin1976] [Libkin2004, Chapter 12]. -/
theorem zero_one_law (φ : Language.graph.Sentence) :
    Filter.Tendsto (fun n => randomGraphProb n fun G => Satisfies G φ) Filter.atTop (nhds 0) ∨
      Filter.Tendsto (fun n => randomGraphProb n fun G => Satisfies G φ) Filter.atTop
        (nhds 1) := by
  have h := zero_one_law_of_isComplete randomGraphStructure isComplete_randomGraphTheory
    (fun _ => tendsto_sentenceProb_randomGraphStructure) φ
  simpa only [randomGraphProb_satisfies_eq] using h

/-- A sentence holds almost surely exactly when it is a consequence of the theory of the random
graph [Fagin1976]. -/
theorem tendsto_randomGraphProb_one_iff (φ : Language.graph.Sentence) :
    Filter.Tendsto (fun n => randomGraphProb n fun G => Satisfies G φ) Filter.atTop (nhds 1) ↔
      randomGraphTheory ⊨ᵇ φ := by
  have h := tendsto_sentenceProb_one_iff_of_isComplete randomGraphStructure
    isComplete_randomGraphTheory (fun _ => tendsto_sentenceProb_randomGraphStructure) φ
  simpa only [randomGraphProb_satisfies_eq] using h

/-- A sentence fails almost surely exactly when the theory of the random graph refutes it. -/
theorem tendsto_randomGraphProb_zero_iff (φ : Language.graph.Sentence) :
    Filter.Tendsto (fun n => randomGraphProb n fun G => Satisfies G φ) Filter.atTop (nhds 0) ↔
      randomGraphTheory ⊨ᵇ φ.not := by
  have h := tendsto_sentenceProb_zero_iff_of_isComplete randomGraphStructure
    isComplete_randomGraphTheory (fun _ => tendsto_sentenceProb_randomGraphStructure) φ
  simpa only [randomGraphProb_satisfies_eq] using h

/-! ### Properties that are not first-order definable -/

/-- If the probability of a graph property `P` tends neither to `0` nor to `1`, then no
first-order sentence agrees with `P` on all graphs with sufficiently many vertices. -/
theorem not_exists_sentence_of_not_tendsto (P : ∀ n, SimpleGraph (Fin n) → Prop)
    (h0 : ¬Filter.Tendsto (fun n => randomGraphProb n (P n)) Filter.atTop (nhds 0))
    (h1 : ¬Filter.Tendsto (fun n => randomGraphProb n (P n)) Filter.atTop (nhds 1)) :
    ¬∃ φ : Language.graph.Sentence, ∀ᶠ n in Filter.atTop,
      ∀ G : SimpleGraph (Fin n), Satisfies G φ ↔ P n G := by
  rintro ⟨φ, hφ⟩
  have heq : (fun n => randomGraphProb n fun G => Satisfies G φ) =ᶠ[Filter.atTop]
      fun n => randomGraphProb n (P n) := by
    filter_upwards [hφ] with n hn
    rw [show (fun G => Satisfies G φ) = P n from funext fun G => propext (hn G)]
  rcases zero_one_law φ with h | h
  · exact h0 (h.congr' heq)
  · exact h1 (h.congr' heq)

/-- **Parity of the number of vertices is not first-order definable** on graphs: no sentence
holds in exactly the graphs with an even number of vertices, even among graphs with sufficiently
many vertices [Libkin2004, Chapter 12]. -/
theorem not_exists_sentence_even_card :
    ¬∃ φ : Language.graph.Sentence, ∀ᶠ n in Filter.atTop,
      ∀ G : SimpleGraph (Fin n), Satisfies G φ ↔ Even n := by
  have hval : ∀ n, randomGraphProb n (fun _ => Even n) = if Even n then 1 else 0 := fun n => by
    by_cases hn : Even n
    · simp only [hn, ↓reduceIte, randomGraphProb_true]
    · simp only [hn, ↓reduceIte, randomGraphProb_false]
  have hev : Filter.Tendsto (fun m : ℕ => 2 * m) Filter.atTop Filter.atTop :=
    Filter.tendsto_id.const_mul_atTop' two_pos
  have hodd : Filter.Tendsto (fun m : ℕ => 2 * m + 1) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_mono (fun m => Nat.le_succ (2 * m)) hev
  refine not_exists_sentence_of_not_tendsto (fun n _ => Even n) (fun h => ?_) (fun h => ?_)
  · -- Along even `n` the probability is `1`.
    have := h.comp hev
    simp only [Function.comp_def, hval, even_two_mul, ↓reduceIte] at this
    exact one_ne_zero (tendsto_const_nhds_iff.1 this)
  · -- Along odd `n` the probability is `0`.
    have := h.comp hodd
    simp only [Function.comp_def, hval, Nat.not_even_two_mul_add_one, ↓reduceIte] at this
    exact zero_ne_one (tendsto_const_nhds_iff.1 this)

/-- The class of finite structures in the language of graphs with an even number of elements is
not first-order definable (`Cslib.Logic.FO.Definable`). -/
theorem not_definable_even_card :
    ¬Definable {M : Bundled.{0} Language.graph.Structure | Even (Nat.card M)} := by
  rintro ⟨φ, hφ⟩
  refine not_exists_sentence_even_card ⟨φ, Filter.Eventually.of_forall fun n G => ?_⟩
  let M : Bundled.{0} Language.graph.Structure := ⟨Fin n, G.structure⟩
  have hM : Even (Nat.card (Fin n)) ↔ Satisfies G φ := @hφ M (inferInstanceAs (Finite (Fin n)))
  rw [Nat.card_fin] at hM
  exact hM.symm

/-- **Parity of the number of edges is not first-order definable** on graphs: no sentence holds in
exactly the graphs with an even number of edges, even among graphs with sufficiently many
vertices. The probability of an even number of edges is exactly `1/2` for `n ≥ 2`. -/
theorem not_exists_sentence_evenEdges :
    ¬∃ φ : Language.graph.Sentence, ∀ᶠ n in Filter.atTop,
      ∀ G : SimpleGraph (Fin n), Satisfies G φ ↔ G.EvenEdges := by
  have hlim : Filter.Tendsto (fun n => randomGraphProb n SimpleGraph.EvenEdges) Filter.atTop
      (nhds (1 / 2)) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop 2] with n hn
    exact (randomGraphProb_evenEdges hn).symm
  refine not_exists_sentence_of_not_tendsto (fun _ => SimpleGraph.EvenEdges) (fun h => ?_)
    (fun h => ?_)
  · have := tendsto_nhds_unique hlim h
    norm_num at this
  · have := tendsto_nhds_unique hlim h
    norm_num at this

end Cslib.Logic.FO.graph
