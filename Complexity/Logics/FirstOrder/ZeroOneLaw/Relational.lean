/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.FirstOrder.Reduction
public import Complexity.Logics.FirstOrder.ZeroOneLaw.Relational.ExtensionProbability

/-!
# Fagin's 0-1 law for finite relational vocabularies

**Theorem** (Fagin 1976). Let `L` be a relational language with finitely many relation symbols, none
of them nullary. For every first-order sentence `φ` of `L`, the fraction `μₙ(φ)` of the
`L`-structures on `{0, …, n - 1}` that satisfy `φ` tends to `0` or to `1` as `n → ∞` [Fagin1976]
[Libkin2004, Chapter 12].

Here `μₙ(φ)` is `Cslib.Logic.FO.sentenceProb (uniformStructure n) φ`, which is the fraction of
structures by `Cslib.Logic.FO.structProb_uniformStructure_eq_card`. The proof is Fagin's. Every
extension axiom holds almost surely
(`Cslib.Logic.FO.Relational.tendsto_sentenceProb_extensionAxiom`), so by compactness the extension
theory `T` is satisfiable. It has no finite models and is `ℵ₀`-categorical, so by the Łoś–Vaught
test it is complete. The transfer theorem `Cslib.Logic.FO.zero_one_law_of_isComplete` then gives the
0-1 law, and the sentences holding almost surely are exactly the consequences of `T`.

The hypothesis that no relation symbol is nullary is needed: a nullary relation symbol holds with
probability exactly `1/2` for every `n` (`Cslib.Logic.FO.not_zero_one_law_of_nullary`).

For `L = Language.graph` the measure `μₙ` is uniform on directed graphs with loops, so this theorem
does not specialize to the 0-1 law for the uniform random simple graph `G(n, 1/2)`, which is
`Cslib.Logic.FO.graph.zero_one_law`.

## Main results

* `Cslib.Logic.FO.Relational.isSatisfiable_extensionTheory`: the extension theory is satisfiable.
* `Cslib.Logic.FO.Relational.isComplete_extensionTheory`: without nullary relation symbols, it is
  complete.
* `Cslib.Logic.FO.Relational.zero_one_law`: Fagin's 0-1 law.
* `Cslib.Logic.FO.Relational.tendsto_sentenceProb_one_iff`,
  `Cslib.Logic.FO.Relational.tendsto_sentenceProb_zero_iff`: the limit is `1` exactly when `T ⊨ φ`,
  and `0` exactly when `T ⊨ ¬φ`.
* `Cslib.Logic.FO.Relational.not_exists_sentence_even_card`,
  `Cslib.Logic.FO.Relational.not_definable_even_card`: an even number of elements is not
  first-order definable.

## References

* [R. Fagin, *Probabilities on finite models*][Fagin1976]
* [L. Libkin, *Elements of Finite Model Theory*][Libkin2004], Chapter 12.
-/

public section

open FirstOrder Language Structure Cardinal CategoryTheory Filter

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

/-- **Fagin's 0-1 law** for a finite relational vocabulary without nullary relation symbols:
for every first-order sentence `φ`, the probability that the uniform random structure on
`Fin n` satisfies `φ` tends to `0` or to `1` [Fagin1976]. -/
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

end Cslib.Logic.FO.Relational
