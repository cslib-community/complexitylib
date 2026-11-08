/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Logics.FirstOrder.ZeroOneLaw.ExtensionAxiom
import CslibFrontier.Logics.FirstOrder.ZeroOneLaw.Relational
import Mathlib.Tactic.FinCases

/-!
# Tests for the 0-1 law for finite relational vocabularies

The law instantiated at the language of graphs; exact probabilities of atomic facts; an extension
axiom holding in a concrete one-element structure and failing in every one-element structure;
nonvacuity of the extension theory through a sentence it proves; the distinction between uniform
`Language.graph`-structures and `G(n, 1/2)`, under which the irreflexivity axiom of simple graphs
has probability `2⁻ⁿ`; and a vocabulary with a nullary relation symbol, for which the law fails.
-/

namespace ComplexityTests.RelationalZeroOneLaw

open FirstOrder Language Structure Cslib.Logic.FO Cslib.Circuits.Boolean.ModelChecking Filter

/-! ### The law for the language of graphs -/

/-- The relational 0-1 law for the language of graphs: uniform random directed graphs with loops. -/
example (φ : Language.graph.Sentence) :
    Tendsto (fun n => sentenceProb (uniformStructure n) φ) atTop (nhds 0) ∨
      Tendsto (fun n => sentenceProb (uniformStructure n) φ) atTop (nhds 1) :=
  Relational.zero_one_law φ

example : (Relational.extensionTheory Language.graph).IsComplete :=
  Relational.isComplete_extensionTheory

example : ¬∃ φ : Language.graph.Sentence, ∀ᶠ n in atTop,
    ∀ S : Language.graph.Structure (Fin n), @Sentence.Realize _ _ S φ ↔ Even n :=
  Relational.not_exists_sentence_even_card

example : ¬Definable {M : CategoryTheory.Bundled.{0} Language.graph.Structure |
    Even (Nat.card M)} :=
  Relational.not_definable_even_card

/-! ### Exact probabilities -/

/-- In the uniform random structure on `Fin 3`, the edge `0 → 1` is present with probability
exactly `1/2`. -/
example : structProb (uniformStructure 3)
    (fun S => @RelMap Language.graph (Fin 3) S 2 adj ![0, 1]) = 1 / 2 :=
  structProb_uniformStructure_relMap adj ![0, 1]

/-- The uniform random structure is the uniform distribution on structures. -/
example (P : Language.graph.Structure (Fin 2) → Prop) :
    structProb (uniformStructure 2) P =
      Nat.card {S // P S} / Nat.card (Language.graph.Structure (Fin 2)) :=
  structProb_uniformStructure_eq_card 2 P

/-! ### Extension axioms on concrete structures -/

/-- The extension axiom "some element has a loop" holds in the one-element structure with a
loop. -/
example : @Sentence.Realize _ (Fin 1) (atomStructure fun _ => true)
    (Relational.extensionAxiom (L := Language.graph) 0 fun _ => true) := by
  let := atomStructure (L := Language.graph) (n := 1) fun _ => true
  refine (Relational.realize_extensionAxiom _).2 fun x _ => ⟨0, fun i => i.elim0, fun a => ?_⟩
  exact iff_of_true ((relMap_atomStructure _ _ _).2 rfl) rfl

/-- Every extension axiom with one given element fails in every one-element structure: there is
no fresh element. So the limit statement `tendsto_sentenceProb_extensionAxiom` is not a statement
about every structure. -/
example (S : Language.graph.Structure (Fin 1))
    (p : Relational.NewAtom Language.graph 1 → Bool) :
    ¬@Sentence.Realize _ (Fin 1) S (Relational.extensionAxiom 1 p) := by
  let := S
  intro h
  obtain ⟨z, hz, -⟩ := (Relational.realize_extensionAxiom p).1 h (fun _ => 0)
    (fun _ _ _ => Subsingleton.elim _ _)
  exact hz 0 (Subsingleton.elim _ _)

/-- Nonvacuity: some element has a loop, almost surely, because the extension theory proves it
through the extension axiom with `k = 0` and the pattern "loop". -/
example : Tendsto (fun n => sentenceProb (uniformStructure n)
    (closeEx (Fin 1) (rel₂ adj (0 : Fin 1) 0) : Language.graph.Sentence)) atTop (nhds 1) := by
  rw [Relational.tendsto_sentenceProb_one_iff, Theory.models_sentence_iff]
  intro M
  obtain ⟨z, -, hz⟩ := Relational.model_extensionTheory_iff.1 M.is_model 0 (fun _ => true)
    Fin.elim0 (fun i => i.elim0)
  have h := (hz ⟨⟨⟨2, adj⟩, ![0, 0]⟩, ⟨0, rfl⟩⟩).2 rfl
  rw [realize_closeEx]
  refine ⟨fun _ => z, ?_⟩
  rw [realize_rel₂]
  convert h using 2
  funext i
  fin_cases i <;> rfl

/-! ### Uniform `Language.graph`-structures are not `G(n, 1/2)` -/

/-- Under the uniform measure on `Language.graph`-structures, the irreflexivity axiom of simple
graphs holds with probability `2⁻ⁿ`: each of the `n` loops is absent with probability `1/2`. -/
theorem sentenceProb_irreflexive (n : ℕ) :
    sentenceProb (uniformStructure n) (adj.irreflexive : Language.graph.Sentence) =
      ((2 : ℝ) ^ n)⁻¹ := by
  classical
  rw [sentenceProb_def, structProb_uniformStructure]
  let ι : Fin n → Atom Language.graph n := fun a => ⟨⟨2, adj⟩, ![a, a]⟩
  have hι : Function.Injective ι := fun a b h => by
    have := congrFun (eq_of_heq (Sigma.mk.inj_iff.1 h).2) 0
    simpa using this
  have hev : ∀ y : Atom Language.graph n → Bool,
      @Sentence.Realize _ _ (atomStructure y) (adj.irreflexive : Language.graph.Sentence) ↔
        (fun h : Fin n → Bool => ∀ a, h a = false) (y ∘ ι) := by
    intro y
    let := atomStructure y
    rw [Relations.realize_irreflexive, irrefl_def]
    exact forall_congr' fun a =>
      (not_congr (relMap_atomStructure y adj ![a, a])).trans (Bool.not_eq_true _).to_iff
  rw [Nat.card_congr (Equiv.subtypeEquivRight hev),
    Nat.card_subtype_comp_injective_div ι hι (fun h : Fin n → Bool => ∀ a, h a = false)]
  have h1 : Nat.card {h : Fin n → Bool // ∀ a, h a = false} = 1 :=
    Nat.card_eq_one_iff_unique.2 ⟨⟨fun a b => Subtype.ext (funext fun u => by
      rw [a.2, b.2])⟩, ⟨⟨fun _ => false, fun _ => rfl⟩⟩⟩
  rw [h1, Nat.card_fun, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool, Nat.card_fin]
  push_cast
  rw [one_div]

/-- So the simple-graph axioms fail almost surely, and the extension theory refutes them: the 0-1
law for `G(n, 1/2)` is not the special case `L = Language.graph` of the relational law. -/
example : Tendsto (fun n => sentenceProb (uniformStructure n)
    (adj.irreflexive : Language.graph.Sentence)) atTop (nhds 0) := by
  simp only [sentenceProb_irreflexive]
  exact tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt one_lt_two)

example : Relational.extensionTheory Language.graph ⊨ᵇ
    (adj.irreflexive : Language.graph.Sentence).not := by
  rw [← Relational.tendsto_sentenceProb_zero_iff]
  simp only [sentenceProb_irreflexive]
  exact tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt one_lt_two)

/-! ### A vocabulary with a nullary relation symbol: the law fails -/

/-- One nullary relation symbol. -/
inductive NullaryRel : ℕ → Type
  | r : NullaryRel 0

/-- The language with one nullary relation symbol and no function symbols. -/
def nullaryLang : Language := ⟨fun _ => Empty, NullaryRel⟩

instance : nullaryLang.IsRelational := fun _ => inferInstanceAs (IsEmpty Empty)

instance : Finite (Σ l, nullaryLang.Relations l) :=
  Finite.of_surjective (fun _ : Unit => (⟨0, .r⟩ : Σ l, nullaryLang.Relations l))
    (fun ⟨_, s⟩ => by cases s; exact ⟨(), rfl⟩)

example (n : ℕ) : sentenceProb (uniformStructure (L := nullaryLang) n)
    (Relations.formula NullaryRel.r Fin.elim0) = 1 / 2 :=
  sentenceProb_uniformStructure_nullary _ n

example : ¬∀ φ : nullaryLang.Sentence,
    Tendsto (fun n => sentenceProb (uniformStructure n) φ) atTop (nhds 0) ∨
      Tendsto (fun n => sentenceProb (uniformStructure n) φ) atTop (nhds 1) :=
  not_zero_one_law_of_nullary NullaryRel.r

/-- The extension theory is still satisfiable without the hypothesis on nullary symbols. -/
example : (Relational.extensionTheory nullaryLang).IsSatisfiable :=
  Relational.isSatisfiable_extensionTheory

end ComplexityTests.RelationalZeroOneLaw
