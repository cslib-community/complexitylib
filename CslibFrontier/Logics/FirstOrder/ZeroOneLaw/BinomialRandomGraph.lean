/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.FirstOrder.ZeroOneLaw.Rado

/-!
# The 0-1 law for `G(n, p)` with constant edge probability

**Theorem** [AlonSpencer2016, Section 10.4]. Fix a real `p` with `0 < p < 1`. For
every first-order sentence `φ` in the language of graphs, the probability that the binomial random
graph `G(n, p)` (Mathlib's `SimpleGraph.binomialRandom (Fin n) p`) satisfies `φ` tends to `0` or
to `1` as `n → ∞`. The limit is `1` exactly when `φ` holds in the Rado graph, so the almost-sure
theory of `G(n, p)` is the same for every such `p`: it is the theory
`Cslib.Logic.FO.graph.randomGraphTheory` of the random graph, whose `p = 1/2` law is
`Cslib.Logic.FO.graph.zero_one_law` [GlebskiiKoganLiogonkiiTalanov1969] [Fagin1976].

The proof is Fagin's argument for `p = 1/2` [Fagin1976], and only its probabilistic step depends
on `p`. For a tuple `x` of `k` distinct vertices, each of the `n - k` other vertices realizes a
prescribed adjacency pattern towards `x` with probability at least `min (p, 1 - p) ^ k`,
independently of the others (`SimpleGraph.binomialRandom_real_forall_not_witness`). The union
bound over the `n (n - 1) ⋯ (n - k + 1)` tuples bounds the failure probability of the extension
axiom by `n (n - 1) ⋯ (n - k + 1) · (1 - min (p, 1 - p) ^ k) ^ (n - k) → 0`
(`Cslib.Logic.FO.graph.binomialRandom_real_not_extensionAxiom_le` and
`Cslib.Logic.FO.graph.tendsto_binomialRandom_real_extensionAxiom`, which the `p = 1/2` law also
uses). The rest is the measure-independent transfer of `Cslib.Logic.FO.zero_one_law_of_isComplete`,
applied to the completeness of `randomGraphTheory` already proved for the `p = 1/2` law.

The hypothesis `0 < p < 1` is needed for the characterization by `randomGraphTheory` and the Rado
graph. `G(n, 0)` has no edges and `G(n, 1)` is complete, so the extension axiom "every vertex has a
neighbour", respectively "every vertex has a non-neighbour", has probability `0` for every `n ≥ 1`
although it holds in the Rado graph.

At `p = 1/2`, `G(n, p)` is the uniform random graph `Cslib.Logic.FO.graph.randomGraph`
(`Cslib.Logic.FO.graph.binomialRandom_real_eq_randomGraphProb`).

## Main definitions

* `Cslib.Logic.FO.graph.binomialRandomStructure`: `G(n, p)` as a distribution on graph
  structures, for the measure-independent transfer.

## Main results

* `Cslib.Logic.FO.graph.binomialRandom_zero_one_law`: the 0-1 law for `G(n, p)`.
* `Cslib.Logic.FO.graph.tendsto_binomialRandom_real_one_iff`,
  `Cslib.Logic.FO.graph.tendsto_binomialRandom_real_zero_iff`: the limit is `1` exactly when
  `randomGraphTheory ⊨ φ`, and `0` exactly when `randomGraphTheory ⊨ ¬φ`.
* `Cslib.Logic.FO.graph.tendsto_binomialRandom_real_one_iff_radoGraph`,
  `Cslib.Logic.FO.graph.tendsto_binomialRandom_real_zero_iff_radoGraph`: the same through the
  Rado graph.
* `Cslib.Logic.FO.graph.tendsto_binomialRandom_real_one_iff_tendsto_randomGraphProb`: the
  almost-sure sentences of `G(n, p)` are those of `G(n, 1/2)`.
* `Cslib.Logic.FO.graph.not_exists_sentence_of_not_tendsto_binomialRandom`: a property whose
  probability in `G(n, p)` tends neither to `0` nor to `1` agrees with no sentence on all large
  graphs.

## References

* [R. Fagin, *Probabilities on finite models*][Fagin1976]
* [Y. V. Glebskiĭ, D. I. Kogan, M. I. Liogon'kiĭ and V. A. Talanov, *Range and degree of
  realizability of formulas in the restricted predicate calculus*]
  [GlebskiiKoganLiogonkiiTalanov1969]
* [N. Alon, J. H. Spencer, *The Probabilistic Method*, Section 10.4][AlonSpencer2016] (locator from
  secondary sources, unverified)
* [L. Libkin, *Elements of Finite Model Theory*][Libkin2004], Chapter 12.
-/

public section

open FirstOrder Language Structure MeasureTheory ProbabilityTheory unitInterval Filter
open scoped SimpleGraph

namespace Cslib.Logic.FO.graph

/-! ### Transfer -/

/-- `G(n, p)` as a distribution on first-order graph structures on `Fin n`: the pushforward of
`G(Fin n, p)` along `SimpleGraph.structure`. -/
noncomputable def binomialRandomStructure (p : I) (n : ℕ) :
    PMF (Language.graph.Structure (Fin n)) :=
  (G(Fin n, p)).toPMF.map SimpleGraph.structure

/-- The probability that `G(n, p)` satisfies a sentence is its sentence probability under
`binomialRandomStructure`. -/
theorem binomialRandom_real_satisfies_eq (p : I) (n : ℕ) (φ : Language.graph.Sentence) :
    G(Fin n, p).real {G | Satisfies G φ} = sentenceProb (binomialRandomStructure p n) φ := by
  rw [sentenceProb_def, structProb_def, binomialRandomStructure, PMF.toOuterMeasure_map_apply,
    ← PMF.toMeasure_apply_eq_toOuterMeasure, Measure.toPMF_toMeasure, measureReal_def]
  rfl

/-- Every sentence of the theory of the random graph holds in `G(n, p)` with probability tending
to `1`, for every constant `0 < p < 1`. -/
theorem tendsto_binomialRandom_real_of_mem_randomGraphTheory {p : I} (hp0 : 0 < (p : ℝ))
    (hp1 : (p : ℝ) < 1) {φ : Language.graph.Sentence} (h : φ ∈ randomGraphTheory) :
    Tendsto (fun n => G(Fin n, p).real {G | Satisfies G φ}) atTop (nhds 1) := by
  rcases mem_randomGraphTheory.1 h with hφ | ⟨k, s, rfl⟩
  · refine tendsto_const_nhds.congr fun n => ?_
    rw [show {G : SimpleGraph (Fin n) | Satisfies G φ} = Set.univ from
      Set.eq_univ_of_forall fun G => satisfies_of_mem_simpleGraph G hφ, probReal_univ]
  · exact tendsto_binomialRandom_real_extensionAxiom hp0 hp1 k s

/-- Every sentence of the theory of the random graph holds in `binomialRandomStructure` with
probability tending to `1`, for every constant `0 < p < 1`. -/
theorem tendsto_sentenceProb_binomialRandomStructure {p : I} (hp0 : 0 < (p : ℝ))
    (hp1 : (p : ℝ) < 1) {φ : Language.graph.Sentence} (h : φ ∈ randomGraphTheory) :
    Tendsto (fun n => sentenceProb (binomialRandomStructure p n) φ) atTop (nhds 1) := by
  simp only [← binomialRandom_real_satisfies_eq]
  exact tendsto_binomialRandom_real_of_mem_randomGraphTheory hp0 hp1 h

/-! ### The 0-1 law -/

/-- **The 0-1 law for `G(n, p)`** [AlonSpencer2016, Section 10.4]. For every constant `0 < p < 1`
and every first-order sentence `φ` in the language of graphs, the probability that `G(n, p)`
satisfies `φ` tends to `0` or to `1`. The proof is Fagin's [Fagin1976]. -/
theorem binomialRandom_zero_one_law {p : I} (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (φ : Language.graph.Sentence) :
    Tendsto (fun n => G(Fin n, p).real {G | Satisfies G φ}) atTop (nhds 0) ∨
      Tendsto (fun n => G(Fin n, p).real {G | Satisfies G φ}) atTop (nhds 1) := by
  have h := zero_one_law_of_isComplete (binomialRandomStructure p) isComplete_randomGraphTheory
    (fun _ => tendsto_sentenceProb_binomialRandomStructure hp0 hp1) φ
  simpa only [binomialRandom_real_satisfies_eq] using h

/-- For constant `0 < p < 1`, a sentence holds almost surely in `G(n, p)` exactly when it is a
consequence of the theory of the random graph. -/
theorem tendsto_binomialRandom_real_one_iff {p : I} (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (φ : Language.graph.Sentence) :
    Tendsto (fun n => G(Fin n, p).real {G | Satisfies G φ}) atTop (nhds 1) ↔
      randomGraphTheory ⊨ᵇ φ := by
  have h := tendsto_sentenceProb_one_iff_of_isComplete (binomialRandomStructure p)
    isComplete_randomGraphTheory (fun _ => tendsto_sentenceProb_binomialRandomStructure hp0 hp1) φ
  simpa only [binomialRandom_real_satisfies_eq] using h

/-- For constant `0 < p < 1`, a sentence fails almost surely in `G(n, p)` exactly when the theory
of the random graph refutes it. -/
theorem tendsto_binomialRandom_real_zero_iff {p : I} (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (φ : Language.graph.Sentence) :
    Tendsto (fun n => G(Fin n, p).real {G | Satisfies G φ}) atTop (nhds 0) ↔
      randomGraphTheory ⊨ᵇ φ.not := by
  have h := tendsto_sentenceProb_zero_iff_of_isComplete (binomialRandomStructure p)
    isComplete_randomGraphTheory (fun _ => tendsto_sentenceProb_binomialRandomStructure hp0 hp1) φ
  simpa only [binomialRandom_real_satisfies_eq] using h

/-- **The almost-sure theory of `G(n, p)` is the theory of the Rado graph** for every constant
`0 < p < 1`: a sentence holds in `G(n, p)` with probability tending to `1` exactly when it holds
in the Rado graph. -/
theorem tendsto_binomialRandom_real_one_iff_radoGraph {p : I} (hp0 : 0 < (p : ℝ))
    (hp1 : (p : ℝ) < 1) (φ : Language.graph.Sentence) :
    Tendsto (fun n => G(Fin n, p).real {G | Satisfies G φ}) atTop (nhds 1) ↔
      Satisfies SimpleGraph.radoGraph φ :=
  (tendsto_binomialRandom_real_one_iff hp0 hp1 φ).trans (models_iff_satisfies_radoGraph φ)

/-- For constant `0 < p < 1`, a sentence holds in `G(n, p)` with probability tending to `0`
exactly when it fails in the Rado graph. -/
theorem tendsto_binomialRandom_real_zero_iff_radoGraph {p : I} (hp0 : 0 < (p : ℝ))
    (hp1 : (p : ℝ) < 1) (φ : Language.graph.Sentence) :
    Tendsto (fun n => G(Fin n, p).real {G | Satisfies G φ}) atTop (nhds 0) ↔
      ¬Satisfies SimpleGraph.radoGraph φ :=
  (tendsto_binomialRandom_real_zero_iff hp0 hp1 φ).trans <|
    (models_iff_satisfies_radoGraph φ.not).trans (satisfies_not _ φ)

/-- **The almost-sure theory does not depend on `p`.** For constant `0 < p < 1`, a sentence holds
almost surely in `G(n, p)` exactly when it holds almost surely in the uniform random graph
`G(n, 1/2)`. -/
theorem tendsto_binomialRandom_real_one_iff_tendsto_randomGraphProb {p : I} (hp0 : 0 < (p : ℝ))
    (hp1 : (p : ℝ) < 1) (φ : Language.graph.Sentence) :
    Tendsto (fun n => G(Fin n, p).real {G | Satisfies G φ}) atTop (nhds 1) ↔
      Tendsto (fun n => randomGraphProb n fun G => Satisfies G φ) atTop (nhds 1) := by
  rw [tendsto_binomialRandom_real_one_iff hp0 hp1, tendsto_randomGraphProb_one_iff]

/-- For constant `0 < p < 1`, if the probability that `G(n, p)` has a graph property `P` tends
neither to `0` nor to `1`, then no first-order sentence agrees with `P` on all graphs with
sufficiently many vertices. -/
theorem not_exists_sentence_of_not_tendsto_binomialRandom {p : I} (hp0 : 0 < (p : ℝ))
    (hp1 : (p : ℝ) < 1) (P : ∀ n, SimpleGraph (Fin n) → Prop)
    (h0 : ¬Tendsto (fun n => G(Fin n, p).real {G | P n G}) atTop (nhds 0))
    (h1 : ¬Tendsto (fun n => G(Fin n, p).real {G | P n G}) atTop (nhds 1)) :
    ¬∃ φ : Language.graph.Sentence, ∀ᶠ n in atTop,
      ∀ G : SimpleGraph (Fin n), Satisfies G φ ↔ P n G := by
  rintro ⟨φ, hφ⟩
  have heq : (fun n => G(Fin n, p).real {G | Satisfies G φ}) =ᶠ[atTop]
      fun n => G(Fin n, p).real {G | P n G} := by
    filter_upwards [hφ] with n hn
    congr 1
    ext G
    exact hn G
  rcases binomialRandom_zero_one_law hp0 hp1 φ with h | h
  · exact h0 (h.congr' heq)
  · exact h1 (h.congr' heq)

end Cslib.Logic.FO.graph
