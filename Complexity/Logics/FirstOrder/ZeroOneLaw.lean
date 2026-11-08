/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.FirstOrder.Reduction
public import Complexity.Logics.FirstOrder.ZeroOneLaw.ExtensionProbability
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

/-- Every finite subset of the theory of the random graph holds in `G(n, 1/2)` with probability
tending to `1`. -/
theorem tendsto_randomGraphProb_finset (T₀ : Finset Language.graph.Sentence)
    (hT₀ : (T₀ : Language.graph.Theory) ⊆ randomGraphTheory) :
    Filter.Tendsto (fun n => randomGraphProb n fun G => ∀ φ ∈ T₀, Satisfies G φ)
      Filter.atTop (nhds 1) := by
  have hfail : ∀ φ ∈ T₀, Filter.Tendsto (fun n => randomGraphProb n fun G => ¬Satisfies G φ)
      Filter.atTop (nhds 0) := by
    intro φ hφ
    rcases mem_randomGraphTheory.1 (hT₀ hφ) with hφ | ⟨k, s, rfl⟩
    · -- The simple-graph axioms hold in every graph.
      have h : ∀ n, randomGraphProb n (fun G => ¬Satisfies G φ) = 0 := fun n => by
        have : (fun G : SimpleGraph (Fin n) => ¬Satisfies G φ) = fun _ => False :=
          funext fun G => propext (iff_false_intro (not_not_intro
            (satisfies_of_mem_simpleGraph G hφ)))
        rw [this, randomGraphProb_false]
      simp only [h]
      exact tendsto_const_nhds
    · have := (tendsto_randomGraphProb_extensionAxiom k s).const_sub 1
      simp only [sub_self, ← randomGraphProb_not] at this
      exact this
  have hsum := tendsto_finsetSum T₀ hfail
  simp only [Finset.sum_const_zero] at hsum
  -- Union bound over the finitely many sentences of `T₀`.
  have hbad : Filter.Tendsto
      (fun n => randomGraphProb n fun G => ¬∀ φ ∈ T₀, Satisfies G φ) Filter.atTop (nhds 0) := by
    refine squeeze_zero (fun n => randomGraphProb_nonneg _ _) (fun n => ?_) hsum
    refine (randomGraphProb_mono fun G hG => ?_).trans (randomGraphProb_exists_le n T₀ _)
    push Not at hG
    exact hG
  have := hbad.const_sub 1
  simp only [sub_zero, randomGraphProb_not, sub_sub_cancel] at this
  exact this

/-- The theory of the random graph is satisfiable. By compactness it suffices that each finite
subset has a model, and a finite subset holds in `G(n, 1/2)` with positive probability for large
`n`. -/
theorem isSatisfiable_randomGraphTheory : randomGraphTheory.IsSatisfiable := by
  rw [Theory.isSatisfiable_iff_isFinitelySatisfiable]
  intro T₀ hT₀
  obtain ⟨n, hn, hn1⟩ := ((tendsto_randomGraphProb_finset T₀ hT₀).eventually
    (lt_mem_nhds (show (0 : ℝ) < 1 from one_pos))).and (Filter.eventually_ge_atTop 1) |>.exists
  obtain ⟨G, hG⟩ := exists_of_randomGraphProb_pos hn
  let := G.structure
  have : Nonempty (Fin n) := ⟨⟨0, hn1⟩⟩
  have : Fin n ⊨ (T₀ : Language.graph.Theory) := (Theory.model_iff _).2 fun φ hφ => hG φ hφ
  exact Theory.Model.isSatisfiable (Fin n)

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
  obtain ⟨T₀, hT₀, hφ⟩ := Theory.models_iff_finset_models.1 h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (tendsto_randomGraphProb_finset T₀ hT₀)
    tendsto_const_nhds ?_ (Filter.Eventually.of_forall fun n => randomGraphProb_le_one _ _)
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  refine randomGraphProb_mono fun G hG => ?_
  let := G.structure
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have : Fin n ⊨ (T₀ : Language.graph.Theory) := (Theory.model_iff _).2 fun ψ hψ => hG ψ hψ
  exact hφ.realize_sentence (Fin n)

/-- A sentence refuted by the theory of the random graph holds in `G(n, 1/2)` with probability
tending to `0`. -/
theorem tendsto_randomGraphProb_of_models_not {φ : Language.graph.Sentence}
    (h : randomGraphTheory ⊨ᵇ φ.not) :
    Filter.Tendsto (fun n => randomGraphProb n fun G => Satisfies G φ) Filter.atTop (nhds 0) := by
  have := (tendsto_randomGraphProb_of_models h).const_sub 1
  simp only [satisfies_not, randomGraphProb_not, sub_sub_cancel, sub_self] at this
  exact this

/-- **The 0-1 law for first-order logic on graphs** (Glebskiĭ–Kogan–Liogon'kiĭ–Talanov; Fagin).
For every first-order sentence `φ` in the language of graphs, the probability that the uniform
random labelled graph `G(n, 1/2)` satisfies `φ` tends to `0` or to `1`
[GlebskiiKoganLiogonkiiTalanov1969] [Fagin1976] [Libkin2004, Chapter 12]. -/
theorem zero_one_law (φ : Language.graph.Sentence) :
    Filter.Tendsto (fun n => randomGraphProb n fun G => Satisfies G φ) Filter.atTop (nhds 0) ∨
      Filter.Tendsto (fun n => randomGraphProb n fun G => Satisfies G φ) Filter.atTop
        (nhds 1) := by
  rcases isComplete_randomGraphTheory.2 φ with h | h
  · exact Or.inr (tendsto_randomGraphProb_of_models h)
  · exact Or.inl (tendsto_randomGraphProb_of_models_not h)

/-- A sentence holds almost surely exactly when it is a consequence of the theory of the random
graph [Fagin1976]. -/
theorem tendsto_randomGraphProb_one_iff (φ : Language.graph.Sentence) :
    Filter.Tendsto (fun n => randomGraphProb n fun G => Satisfies G φ) Filter.atTop (nhds 1) ↔
      randomGraphTheory ⊨ᵇ φ := by
  refine ⟨fun h1 => (isComplete_randomGraphTheory.2 φ).resolve_right fun hn => ?_,
    tendsto_randomGraphProb_of_models⟩
  exact zero_ne_one (tendsto_nhds_unique (tendsto_randomGraphProb_of_models_not hn) h1)

/-- A sentence fails almost surely exactly when the theory of the random graph refutes it. -/
theorem tendsto_randomGraphProb_zero_iff (φ : Language.graph.Sentence) :
    Filter.Tendsto (fun n => randomGraphProb n fun G => Satisfies G φ) Filter.atTop (nhds 0) ↔
      randomGraphTheory ⊨ᵇ φ.not := by
  refine ⟨fun h0 => (isComplete_randomGraphTheory.2 φ).resolve_left fun hp => ?_,
    tendsto_randomGraphProb_of_models_not⟩
  exact zero_ne_one (tendsto_nhds_unique h0 (tendsto_randomGraphProb_of_models hp))

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
