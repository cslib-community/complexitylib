/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.FirstOrder.Reduction
public import CslibFrontier.Logics.FirstOrder.ZeroOneLaw.Relational.ExtensionProbability

/-!
# The 0-1 law for finite relational vocabularies

**Theorem** (Glebskiĭ–Kogan–Liogon'kiĭ–Talanov 1969; Fagin 1976). Let `L` be a relational language
with finitely many relation symbols, none of them nullary. For every first-order sentence `φ` of
`L`, the fraction `μₙ(φ)` of the `L`-structures on `{0, …, n - 1}` that satisfy `φ` tends to `0` or
to `1` as `n → ∞` [GlebskiiKoganLiogonkiiTalanov1969] [Fagin1976] [Libkin2004, Chapter 12].

Here `μₙ(φ)` is `Cslib.Logic.FO.sentenceProb (uniformStructure n) φ`, which is the fraction of
structures by `Cslib.Logic.FO.structProb_uniformStructure_eq_card`. The proof is Fagin's. Every
extension axiom holds almost surely
(`Cslib.Logic.FO.Relational.tendsto_sentenceProb_extensionAxiom`), so by compactness the extension
theory `T` is satisfiable. It has no finite models and is `ℵ₀`-categorical, so by the Łoś–Vaught
test it is complete. The transfer theorem `Cslib.Logic.FO.zero_one_law_of_isComplete` then gives the
0-1 law, and the sentences holding almost surely are exactly the consequences of `T`.

The same holds with a constant probability `0 < p R < 1` for each relation symbol `R`: under the
random structure `Cslib.Logic.FO.bernoulliStructure p n`, in which every atomic fact `R(t)` holds
independently with probability `p R`, every sentence has limit probability `0` or `1`
(`Cslib.Logic.FO.Relational.bernoulliStructure_zero_one_law`), and the almost-sure sentences are
again the consequences of `T`, so they do not depend on `p`. This is Fagin's proof with only the
probabilistic step changed; we know of no primary source stating it for per-symbol probabilities
over arbitrary finite relational vocabularies, so it should be read as an adaptation of [Fagin1976].

The hypothesis that no relation symbol is nullary is needed: a nullary relation symbol holds with
probability exactly `1/2` for every `n` (`Cslib.Logic.FO.not_zero_one_law_of_nullary`), and with
probability exactly `p R` under `bernoulliStructure p n`
(`Cslib.Logic.FO.not_zero_one_law_bernoulliStructure_of_nullary`). The hypothesis `0 < p R < 1` is
needed too: with `p R = 0` the extension axiom asking for an `R`-fact fails in every structure.

For `L = Language.graph` the measure `μₙ` is uniform on directed graphs with loops, so this theorem
does not specialize to the 0-1 law for the uniform random simple graph `G(n, 1/2)`, which is
`Cslib.Logic.FO.graph.zero_one_law`. Likewise `bernoulliStructure p n` for `Language.graph` is a
random directed graph with loops, not `G(n, p)`, whose law is
`Cslib.Logic.FO.graph.binomialRandom_zero_one_law`.

## Main results

* `Cslib.Logic.FO.Relational.isSatisfiable_extensionTheory`: the extension theory is satisfiable.
* `Cslib.Logic.FO.Relational.isComplete_extensionTheory`: without nullary relation symbols, it is
  complete.
* `Cslib.Logic.FO.Relational.zero_one_law`: the 0-1 law.
* `Cslib.Logic.FO.Relational.tendsto_sentenceProb_one_iff`,
  `Cslib.Logic.FO.Relational.tendsto_sentenceProb_zero_iff`: the limit is `1` exactly when `T ⊨ φ`,
  and `0` exactly when `T ⊨ ¬φ`.
* `Cslib.Logic.FO.Relational.not_exists_sentence_even_card`,
  `Cslib.Logic.FO.Relational.not_definable_even_card`: an even number of elements is not
  first-order definable.
* `Cslib.Logic.FO.Relational.bernoulliStructure_zero_one_law`: the 0-1 law for constant
  probabilities `0 < p R < 1`.
* `Cslib.Logic.FO.Relational.tendsto_sentenceProb_bernoulliStructure_one_iff`,
  `Cslib.Logic.FO.Relational.tendsto_sentenceProb_bernoulliStructure_zero_iff`,
  `Cslib.Logic.FO.Relational.tendsto_sentenceProb_bernoulliStructure_one_iff_uniformStructure`: the
  almost-sure sentences are the consequences of `T`, for every such `p`.
* `Cslib.Logic.FO.Relational.not_exists_sentence_of_not_tendsto_bernoulliStructure`:
  non-definability from the law.

## References

* [Y. V. Glebskiĭ, D. I. Kogan, M. I. Liogon'kiĭ and V. A. Talanov, *Range and degree of
  realizability of formulas in the restricted predicate calculus*]
  [GlebskiiKoganLiogonkiiTalanov1969]
* [R. Fagin, *Probabilities on finite models*][Fagin1976]
* [L. Libkin, *Elements of Finite Model Theory*][Libkin2004], Chapter 12.
-/

public section

open FirstOrder Language Structure Cardinal CategoryTheory Filter
open scoped unitInterval

namespace Cslib.Logic.FO.Relational

universe u v

variable {L : Language.{u, v}} [L.IsRelational] [Finite (Σ l, L.Relations l)]

/-- The extension theory is satisfiable: its finite subsets hold with probability tending to `1`,
so by compactness it has a model [Fagin1976]. -/
theorem isSatisfiable_extensionTheory : (extensionTheory L).IsSatisfiable :=
  isSatisfiable_of_tendsto_sentenceProb _ fun _ => tendsto_sentenceProb_of_mem_extensionTheory

variable [IsEmpty (L.Relations 0)]

/-- The extension theory is complete, by the Łoś–Vaught test [Fagin1976]. -/
theorem isComplete_extensionTheory : (extensionTheory L).IsComplete := by
  have hcard : lift.{max u v} L.card ≤ lift.{max u v} ℵ₀ := by
    rw [lift_aleph0, lift_le_aleph0]
    exact Cardinal.mk_le_aleph0
  exact aleph0_categorical_extensionTheory.{u, v, max u v}.isComplete ℵ₀ _ le_rfl hcard
    isSatisfiable_extensionTheory fun M => infinite_of_model_extensionTheory (L := L)

/-- **The 0-1 law** (Glebskiĭ–Kogan–Liogon'kiĭ–Talanov; Fagin) for a finite relational vocabulary
without nullary relation symbols: for every first-order sentence `φ`, the probability that the
uniform random structure on `Fin n` satisfies `φ` tends to `0` or to `1`
[GlebskiiKoganLiogonkiiTalanov1969] [Fagin1976]. -/
theorem zero_one_law (φ : L.Sentence) :
    Tendsto (fun n => sentenceProb (uniformStructure n) φ) atTop (nhds 0) ∨
      Tendsto (fun n => sentenceProb (uniformStructure n) φ) atTop (nhds 1) :=
  zero_one_law_of_isComplete _ isComplete_extensionTheory
    (fun _ => tendsto_sentenceProb_of_mem_extensionTheory) φ

/-- A sentence holds almost surely exactly when it is a consequence of the extension theory. -/
theorem tendsto_sentenceProb_one_iff (φ : L.Sentence) :
    Tendsto (fun n => sentenceProb (uniformStructure n) φ) atTop (nhds 1) ↔
      extensionTheory L ⊨ᵇ φ :=
  tendsto_sentenceProb_one_iff_of_isComplete _ isComplete_extensionTheory
    (fun _ => tendsto_sentenceProb_of_mem_extensionTheory) φ

/-- A sentence fails almost surely exactly when the extension theory refutes it. -/
theorem tendsto_sentenceProb_zero_iff (φ : L.Sentence) :
    Tendsto (fun n => sentenceProb (uniformStructure n) φ) atTop (nhds 0) ↔
      extensionTheory L ⊨ᵇ φ.not :=
  tendsto_sentenceProb_zero_iff_of_isComplete _ isComplete_extensionTheory
    (fun _ => tendsto_sentenceProb_of_mem_extensionTheory) φ

/-- **Parity of the number of elements is not first-order definable** over a finite relational
vocabulary without nullary relation symbols: no sentence holds in exactly the structures with an
even number of elements, even among structures with sufficiently many elements. -/
theorem not_exists_sentence_even_card :
    ¬∃ φ : L.Sentence, ∀ᶠ n in atTop,
      ∀ S : L.Structure (Fin n), @Sentence.Realize L _ S φ ↔ Even n :=
  not_exists_sentence_even_card_of_zero_one_law _ zero_one_law

/-- The class of finite `L`-structures with an even number of elements is not first-order definable
(`Cslib.Logic.FO.Definable`). -/
theorem not_definable_even_card :
    ¬Definable {M : Bundled.{0} L.Structure | Even (Nat.card M)} := by
  rintro ⟨φ, hφ⟩
  refine not_exists_sentence_even_card ⟨φ, Eventually.of_forall fun n S => ?_⟩
  let M : Bundled.{0} L.Structure := ⟨Fin n, S⟩
  have hM : Even (Nat.card (Fin n)) ↔ @Sentence.Realize L _ S φ :=
    @hφ M (inferInstanceAs (Finite (Fin n)))
  rw [Nat.card_fin] at hM
  exact hM.symm

/-! ### Constant probabilities per relation symbol -/

/-- **The 0-1 law for constant probabilities**, an adaptation of Fagin's proof [Fagin1976]. Let
every relation symbol `R` have a probability `0 < p R < 1`. For every first-order sentence `φ`, the
probability that `bernoulliStructure p n` satisfies `φ` tends to `0` or to `1`. -/
theorem bernoulliStructure_zero_one_law {p : (Σ l, L.Relations l) → I}
    (hp : ∀ R, 0 < (p R : ℝ) ∧ (p R : ℝ) < 1) (φ : L.Sentence) :
    Tendsto (fun n => sentenceProb (bernoulliStructure p n) φ) atTop (nhds 0) ∨
      Tendsto (fun n => sentenceProb (bernoulliStructure p n) φ) atTop (nhds 1) :=
  zero_one_law_of_isComplete _ isComplete_extensionTheory
    (fun _ => tendsto_sentenceProb_bernoulliStructure_of_mem_extensionTheory hp) φ

/-- For constant probabilities `0 < p R < 1`, a sentence holds almost surely in
`bernoulliStructure p n` exactly when it is a consequence of the extension theory. -/
theorem tendsto_sentenceProb_bernoulliStructure_one_iff {p : (Σ l, L.Relations l) → I}
    (hp : ∀ R, 0 < (p R : ℝ) ∧ (p R : ℝ) < 1) (φ : L.Sentence) :
    Tendsto (fun n => sentenceProb (bernoulliStructure p n) φ) atTop (nhds 1) ↔
      extensionTheory L ⊨ᵇ φ :=
  tendsto_sentenceProb_one_iff_of_isComplete _ isComplete_extensionTheory
    (fun _ => tendsto_sentenceProb_bernoulliStructure_of_mem_extensionTheory hp) φ

/-- For constant probabilities `0 < p R < 1`, a sentence fails almost surely in
`bernoulliStructure p n` exactly when the extension theory refutes it. -/
theorem tendsto_sentenceProb_bernoulliStructure_zero_iff {p : (Σ l, L.Relations l) → I}
    (hp : ∀ R, 0 < (p R : ℝ) ∧ (p R : ℝ) < 1) (φ : L.Sentence) :
    Tendsto (fun n => sentenceProb (bernoulliStructure p n) φ) atTop (nhds 0) ↔
      extensionTheory L ⊨ᵇ φ.not :=
  tendsto_sentenceProb_zero_iff_of_isComplete _ isComplete_extensionTheory
    (fun _ => tendsto_sentenceProb_bernoulliStructure_of_mem_extensionTheory hp) φ

/-- **The almost-sure theory does not depend on `p`.** For constant probabilities `0 < p R < 1`, a
sentence holds almost surely in `bernoulliStructure p n` exactly when it holds almost surely in the
uniform random structure. -/
theorem tendsto_sentenceProb_bernoulliStructure_one_iff_uniformStructure
    {p : (Σ l, L.Relations l) → I} (hp : ∀ R, 0 < (p R : ℝ) ∧ (p R : ℝ) < 1) (φ : L.Sentence) :
    Tendsto (fun n => sentenceProb (bernoulliStructure p n) φ) atTop (nhds 1) ↔
      Tendsto (fun n => sentenceProb (uniformStructure n) φ) atTop (nhds 1) := by
  rw [tendsto_sentenceProb_bernoulliStructure_one_iff hp, tendsto_sentenceProb_one_iff]

/-- For constant probabilities `0 < p R < 1`, if the probability that `bernoulliStructure p n` has
a property `P` tends neither to `0` nor to `1`, then no first-order sentence agrees with `P` on all
structures with sufficiently many elements. -/
theorem not_exists_sentence_of_not_tendsto_bernoulliStructure {p : (Σ l, L.Relations l) → I}
    (hp : ∀ R, 0 < (p R : ℝ) ∧ (p R : ℝ) < 1) (P : ∀ n, L.Structure (Fin n) → Prop)
    (h0 : ¬Tendsto (fun n => structProb (bernoulliStructure p n) (P n)) atTop (nhds 0))
    (h1 : ¬Tendsto (fun n => structProb (bernoulliStructure p n) (P n)) atTop (nhds 1)) :
    ¬∃ φ : L.Sentence, ∀ᶠ n in atTop,
      ∀ S : L.Structure (Fin n), @Sentence.Realize L _ S φ ↔ P n S :=
  not_exists_sentence_of_not_tendsto _ (bernoulliStructure_zero_one_law hp) P h0 h1

end Cslib.Logic.FO.Relational
