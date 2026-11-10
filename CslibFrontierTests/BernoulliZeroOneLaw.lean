/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Logics.FirstOrder.ZeroOneLaw.Relational
import CslibFrontierTests.RelationalZeroOneLaw

/-!
# Tests for the 0-1 law with constant probabilities per relation symbol

The law for the language of graphs at edge probability `1/3` (random directed graphs with loops),
with a sentence of limit `1` and one of limit `0`; exact probabilities of atomic facts; the bridge
to the uniform random structure at `p = 1/2`; and the two hypotheses. With `p = 0` or `p = 1` the
almost-sure sentences are no longer the consequences of the extension theory (the 0-1 law itself
still holds, since the symbol is then a.s. empty or full and can be replaced by `⊥` or `⊤`; that
reduction is not formalized), and a nullary relation symbol of probability `1/3` breaks the law.
-/

namespace CslibFrontierTests.BernoulliZeroOneLaw

open FirstOrder Language Structure Cslib.Logic.FO Filter
open scoped unitInterval

/-- The constant probability `1/3`. -/
noncomputable def third : I := ⟨1 / 3, by norm_num, by norm_num⟩

theorem third_mem : 0 < (third : ℝ) ∧ (third : ℝ) < 1 := by
  simp only [third]
  norm_num

/-- "Some element has a loop." -/
noncomputable def someLoop : Language.graph.Sentence :=
  closeEx (Fin 1) (rel₂ adj (0 : Fin 1) 0)

theorem realize_someLoop {M : Type*} [Language.graph.Structure M] :
    M ⊨ someLoop ↔ ∃ z : M, RelMap adj ![z, z] := by
  rw [someLoop, realize_closeEx]
  exact ⟨fun ⟨v, h⟩ => ⟨v 0, by rwa [realize_rel₂] at h⟩,
    fun ⟨z, h⟩ => ⟨fun _ => z, by rwa [realize_rel₂]⟩⟩

/-- The extension axiom with `k = 0` and the pattern "loop" proves that some element has a
loop. -/
theorem extensionTheory_models_someLoop :
    Relational.extensionTheory Language.graph ⊨ᵇ someLoop := by
  rw [Theory.models_sentence_iff]
  intro M
  obtain ⟨z, -, hz⟩ := Relational.model_extensionTheory_iff.1 M.is_model 0 (fun _ => true)
    Fin.elim0 (fun i => i.elim0)
  refine realize_someLoop.2 ⟨z, ?_⟩
  convert (hz ⟨⟨⟨2, adj⟩, ![0, 0]⟩, ⟨0, rfl⟩⟩).2 rfl using 2
  funext i
  fin_cases i <;> rfl

/-- The extension axiom with `k = 0` and the pattern "no loop" proves that some element has no
loop. -/
theorem extensionTheory_models_someNoLoop :
    Relational.extensionTheory Language.graph ⊨ᵇ
      (closeEx (Fin 1) (rel₂ adj (0 : Fin 1) 0).not : Language.graph.Sentence) := by
  rw [Theory.models_sentence_iff]
  intro M
  obtain ⟨z, -, hz⟩ := Relational.model_extensionTheory_iff.1 M.is_model 0 (fun _ => false)
    Fin.elim0 (fun i => i.elim0)
  rw [realize_closeEx]
  refine ⟨fun _ => z, ?_⟩
  rw [Formula.realize_not, realize_rel₂]
  intro h
  have := (hz ⟨⟨⟨2, adj⟩, ![0, 0]⟩, ⟨0, rfl⟩⟩).1
  refine Bool.false_ne_true (this ?_)
  convert h using 2
  funext i
  fin_cases i <;> rfl

/-! ### The law for the language of graphs at `p = 1/3` -/

example (φ : Language.graph.Sentence) :
    Tendsto (fun n => sentenceProb (bernoulliStructure (fun _ => third) n) φ) atTop (nhds 0) ∨
      Tendsto (fun n => sentenceProb (bernoulliStructure (fun _ => third) n) φ) atTop
        (nhds 1) :=
  Relational.bernoulliStructure_zero_one_law (fun _ => third_mem) φ

/-- Some element has a loop, almost surely: the extension theory proves it. -/
example : Tendsto (fun n => sentenceProb (bernoulliStructure (fun _ => third) n) someLoop) atTop
    (nhds 1) :=
  (Relational.tendsto_sentenceProb_bernoulliStructure_one_iff (fun _ => third_mem) _).2
    extensionTheory_models_someLoop

/-- "No element has a loop", the irreflexivity axiom of simple graphs, fails almost surely: the
extension theory refutes it. -/
example : Tendsto (fun n => sentenceProb (bernoulliStructure (fun _ => third) n)
    (adj.irreflexive : Language.graph.Sentence)) atTop (nhds 0) := by
  rw [Relational.tendsto_sentenceProb_bernoulliStructure_zero_iff (fun _ => third_mem),
    Theory.models_sentence_iff]
  intro M
  obtain ⟨z, hz⟩ :=
    realize_someLoop.1 (Theory.models_sentence_iff.1 extensionTheory_models_someLoop M)
  rw [Sentence.realize_not, Relations.realize_irreflexive, irrefl_def]
  exact fun h => h hz

/-- The almost-sure sentences do not depend on `p`. -/
example (φ : Language.graph.Sentence) :
    Tendsto (fun n => sentenceProb (bernoulliStructure (fun _ => third) n) φ) atTop (nhds 1) ↔
      Tendsto (fun n => sentenceProb (uniformStructure n) φ) atTop (nhds 1) :=
  Relational.tendsto_sentenceProb_bernoulliStructure_one_iff_uniformStructure
    (fun _ => third_mem) φ

/-! ### Exact probabilities and the bridge at `p = 1/2` -/

/-- At `p = 1/3` the edge `0 → 1` on `Fin 3` is present with probability exactly `1/3`. -/
example : structProb (bernoulliStructure (fun _ => third) 3)
    (fun S => @RelMap Language.graph (Fin 3) S 2 adj ![0, 1]) = 1 / 3 :=
  structProb_bernoulliStructure_relMap _ adj ![0, 1]

/-- At `p = 1/2` the random structure is the uniform random structure. -/
example (n : ℕ) :
    bernoulliStructure (L := Language.graph) (fun _ => ⟨1 / 2, by norm_num, by norm_num⟩) n =
      uniformStructure n :=
  bernoulliStructure_eq_uniformStructure (fun _ => rfl) n

/-! ### The characterization needs `0 < p` -/

/-- With edge probability `0` no element has a loop, so `someLoop` has probability `0` for every
`n`. -/
theorem sentenceProb_someLoop_zero (n : ℕ) :
    sentenceProb (bernoulliStructure (L := Language.graph) (fun _ => 0) n) someLoop = 0 := by
  refine le_antisymm ?_ (structProb_nonneg _ _)
  calc _ ≤ structProb (bernoulliStructure (L := Language.graph) (fun _ => 0) n)
        (fun S => ∃ z ∈ (Finset.univ : Finset (Fin n)), @RelMap _ _ S 2 adj ![z, z]) :=
        structProb_mono fun S h => by
          obtain ⟨z, hz⟩ := (@realize_someLoop (Fin n) S).1 h
          exact ⟨z, Finset.mem_univ _, hz⟩
    _ ≤ ∑ z : Fin n, structProb (bernoulliStructure (L := Language.graph) (fun _ => 0) n)
        (fun S => @RelMap _ _ S 2 adj ![z, z]) := structProb_exists_le _ _ _
    _ = 0 := by
        simp only [structProb_bernoulliStructure_relMap, Set.Icc.coe_zero, Finset.sum_const_zero]

/-- So with `p = 0` a consequence of the extension theory does not hold almost surely: the
characterization of the almost-sure sentences needs `0 < p`. -/
example : Relational.extensionTheory Language.graph ⊨ᵇ someLoop ∧
    ¬Tendsto (fun n => sentenceProb (bernoulliStructure (L := Language.graph) (fun _ => 0) n)
      someLoop) atTop (nhds 1) := by
  refine ⟨extensionTheory_models_someLoop, fun h => ?_⟩
  simp only [sentenceProb_someLoop_zero] at h
  exact zero_ne_one (tendsto_nhds_unique tendsto_const_nhds h)

/-! ### The characterization needs `p < 1` -/

/-- With edge probability `1` every element has a loop, so "some element has no loop" has
probability `0` for every `n`. -/
theorem sentenceProb_someNoLoop_one (n : ℕ) :
    sentenceProb (bernoulliStructure (L := Language.graph) (fun _ => 1) n)
      (closeEx (Fin 1) (rel₂ adj (0 : Fin 1) 0).not) = 0 := by
  refine le_antisymm ?_ (structProb_nonneg _ _)
  calc _ ≤ structProb (bernoulliStructure (L := Language.graph) (fun _ => 1) n)
        (fun S => ∃ z ∈ (Finset.univ : Finset (Fin n)), ¬@RelMap _ _ S 2 adj ![z, z]) :=
        structProb_mono fun S h => by
          let := S
          rw [realize_closeEx] at h
          obtain ⟨v, hv⟩ := h
          rw [Formula.realize_not, realize_rel₂] at hv
          exact ⟨v 0, Finset.mem_univ _, hv⟩
    _ ≤ ∑ z : Fin n, structProb (bernoulliStructure (L := Language.graph) (fun _ => 1) n)
        (fun S => ¬@RelMap _ _ S 2 adj ![z, z]) := structProb_exists_le _ _ _
    _ = 0 := by
        simp only [structProb_not, structProb_bernoulliStructure_relMap, Set.Icc.coe_one,
          sub_self, Finset.sum_const_zero]

/-- So with `p = 1` a consequence of the extension theory does not hold almost surely: the
characterization of the almost-sure sentences needs `p < 1`. -/
example : Relational.extensionTheory Language.graph ⊨ᵇ
      (closeEx (Fin 1) (rel₂ adj (0 : Fin 1) 0).not : Language.graph.Sentence) ∧
    ¬Tendsto (fun n => sentenceProb (bernoulliStructure (L := Language.graph) (fun _ => 1) n)
      (closeEx (Fin 1) (rel₂ adj (0 : Fin 1) 0).not)) atTop (nhds 1) := by
  refine ⟨extensionTheory_models_someNoLoop, fun h => ?_⟩
  simp only [sentenceProb_someNoLoop_one] at h
  exact zero_ne_one (tendsto_nhds_unique tendsto_const_nhds h)

/-! ### No nullary symbols is needed -/

open CslibFrontierTests.RelationalZeroOneLaw in
/-- A nullary relation symbol of probability `1/3` holds with probability exactly `1/3` for every
`n`. -/
example (n : ℕ) : sentenceProb (bernoulliStructure (L := nullaryLang) (fun _ => third) n)
    (Relations.formula NullaryRel.r Fin.elim0) = 1 / 3 :=
  sentenceProb_bernoulliStructure_nullary _ _ n

open CslibFrontierTests.RelationalZeroOneLaw in
/-- So the law fails for that vocabulary. -/
example : ¬∀ φ : nullaryLang.Sentence,
    Tendsto (fun n => sentenceProb (bernoulliStructure (fun _ => third) n) φ) atTop (nhds 0) ∨
      Tendsto (fun n => sentenceProb (bernoulliStructure (fun _ => third) n) φ) atTop
        (nhds 1) :=
  not_zero_one_law_bernoulliStructure_of_nullary NullaryRel.r third_mem.1 third_mem.2

end CslibFrontierTests.BernoulliZeroOneLaw
