/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Probability.PMF
public import Mathlib.ModelTheory.Satisfiability
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Topology.Instances.Real.Lemmas
import Complexity.Probability.PMF.Event
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Order.Basic

/-!
# Asymptotic probabilities of first-order sentences

For a sequence of distributions `μ n` on the `L`-structures with universe `Fin n`, the probability
that `μ n` satisfies a sentence `φ` is `Cslib.Logic.FO.sentenceProb (μ n) φ`. This file proves
the measure-independent half of Fagin's proof of the 0-1 law [Fagin1976] [Libkin2004, Chapter 12]:
if every sentence of a theory `T` holds with probability tending to `1`, then by compactness `T` is
satisfiable and every consequence of `T` holds with probability tending to `1`. If `T` is also
complete, every sentence has probability tending to `0` or to `1`, and the sentences of limit
probability `1` are exactly the consequences of `T`.

Under a 0-1 law, a property whose probability converges to neither `0` nor `1`, such as having an
even number of elements, agrees with no sentence on all large structures.

## Main definitions

* `Cslib.Logic.FO.structProb`: the probability that a random structure has a property.
* `Cslib.Logic.FO.sentenceProb`: the probability that a random structure satisfies a sentence.

## Main results

* `Cslib.Logic.FO.structProb_not`, `Cslib.Logic.FO.structProb_mono`,
  `Cslib.Logic.FO.structProb_exists_le`: complement, monotonicity, union bound.
* `Cslib.Logic.FO.isSatisfiable_of_tendsto_sentenceProb`: a theory whose sentences hold with
  probability tending to `1` is satisfiable.
* `Cslib.Logic.FO.tendsto_sentenceProb_of_models`: so does every consequence of it.
* `Cslib.Logic.FO.zero_one_law_of_isComplete`: the transfer to a 0-1 law.
* `Cslib.Logic.FO.tendsto_sentenceProb_one_iff_of_isComplete`,
  `Cslib.Logic.FO.tendsto_sentenceProb_zero_iff_of_isComplete`: the limit is `1` exactly for the
  consequences of `T`, and `0` exactly for the sentences that `T` refutes.
* `Cslib.Logic.FO.not_exists_sentence_of_not_tendsto`,
  `Cslib.Logic.FO.not_exists_sentence_even_card_of_zero_one_law`: under a 0-1 law, such properties
  as an even number of elements are not first-order definable.

## References

* [R. Fagin, *Probabilities on finite models*][Fagin1976]
* [L. Libkin, *Elements of Finite Model Theory*][Libkin2004], Chapter 12.
-/

public section

open FirstOrder Language Structure Cslib.Probability Filter

namespace Cslib.Logic.FO

universe u v

variable {L : Language.{u, v}}

/-- The probability that a random structure drawn from `μ` has the property `P`. -/
noncomputable def structProb {α : Type*} (μ : PMF (L.Structure α)) (P : L.Structure α → Prop) :
    ℝ :=
  (μ.toOuterMeasure {S | P S}).toReal

/-- The probability that a random structure drawn from `μ` satisfies the sentence `φ`. -/
noncomputable def sentenceProb {α : Type*} (μ : PMF (L.Structure α)) (φ : L.Sentence) : ℝ :=
  structProb μ fun S => @Sentence.Realize L α S φ

section API

variable {α : Type*} (μ : PMF (L.Structure α))

theorem structProb_def (P : L.Structure α → Prop) :
    structProb μ P = (μ.toOuterMeasure {S | P S}).toReal := by
  rw [structProb]

theorem sentenceProb_def (φ : L.Sentence) :
    sentenceProb μ φ = structProb μ fun S => @Sentence.Realize L α S φ := by
  rw [sentenceProb]

theorem structProb_nonneg (P : L.Structure α → Prop) : 0 ≤ structProb μ P :=
  ENNReal.toReal_nonneg

theorem structProb_not (P : L.Structure α → Prop) :
    structProb μ (fun S => ¬P S) = 1 - structProb μ P := by
  rw [structProb, structProb, ← PMF.toOuterMeasure_toReal_add_compl μ {S | P S},
    add_sub_cancel_left]
  rfl

theorem structProb_le_one (P : L.Structure α → Prop) : structProb μ P ≤ 1 := by
  have h := structProb_not μ P
  have h0 := structProb_nonneg μ fun S => ¬P S
  linarith

variable {μ} in
theorem structProb_mono {P Q : L.Structure α → Prop} (h : ∀ S, P S → Q S) :
    structProb μ P ≤ structProb μ Q :=
  ENNReal.toReal_mono (PMF.toOuterMeasure_ne_top _ _)
    (MeasureTheory.measure_mono fun S hS => h S hS)

@[simp]
theorem structProb_false : structProb μ (fun _ => False) = 0 := by
  rw [structProb, Set.ofPred_false, MeasureTheory.measure_empty, ENNReal.toReal_zero]

@[simp]
theorem structProb_true : structProb μ (fun _ => True) = 1 := by
  have h := structProb_not μ fun _ => True
  simp only [not_true_eq_false, structProb_false] at h
  linarith

variable {μ} in
/-- A property of positive probability holds of some structure. -/
theorem exists_of_structProb_pos {P : L.Structure α → Prop} (h : 0 < structProb μ P) :
    ∃ S, P S := by
  by_contra hne
  push Not at hne
  have := structProb_mono (μ := μ) (Q := fun _ => False) fun S hS => hne S hS
  rw [structProb_false] at this
  linarith

/-- **Union bound.** -/
theorem structProb_exists_le {ι : Type*} (I : Finset ι) (P : ι → L.Structure α → Prop) :
    structProb μ (fun S => ∃ i ∈ I, P i S) ≤ ∑ i ∈ I, structProb μ (P i) := by
  have hset : {S | ∃ i ∈ I, P i S} = ⋃ i ∈ I, {S | P i S} := by
    ext S
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, exists_prop]
  rw [structProb, hset]
  calc _ ≤ (∑ i ∈ I, μ.toOuterMeasure {S | P i S}).toReal :=
        ENNReal.toReal_mono (ENNReal.sum_ne_top.2 fun i _ => PMF.toOuterMeasure_ne_top _ _)
          (MeasureTheory.measure_biUnion_finset_le I _)
    _ = _ := by
        rw [ENNReal.toReal_sum fun i _ => PMF.toOuterMeasure_ne_top _ _]
        rfl

theorem sentenceProb_not (φ : L.Sentence) : sentenceProb μ φ.not = 1 - sentenceProb μ φ := by
  rw [sentenceProb, sentenceProb, ← structProb_not]
  rfl

end API

/-! ### Transfer -/

section Transfer

variable (μ : ∀ n, PMF (L.Structure (Fin n)))

/-- If each sentence of a finite set holds with probability tending to `1`, so does their
conjunction. -/
theorem tendsto_structProb_forall_finset (T₀ : Finset L.Sentence)
    (h : ∀ φ ∈ T₀, Tendsto (fun n => sentenceProb (μ n) φ) atTop (nhds 1)) :
    Tendsto (fun n => structProb (μ n) fun S => ∀ φ ∈ T₀, @Sentence.Realize L _ S φ)
      atTop (nhds 1) := by
  have hfail : ∀ φ ∈ T₀, Tendsto (fun n => sentenceProb (μ n) φ.not) atTop (nhds 0) := by
    intro φ hφ
    have := (h φ hφ).const_sub 1
    simp only [sub_self, ← sentenceProb_not] at this
    exact this
  have hsum := tendsto_finsetSum T₀ hfail
  simp only [Finset.sum_const_zero] at hsum
  have hbad : Tendsto
      (fun n => structProb (μ n) fun S => ¬∀ φ ∈ T₀, @Sentence.Realize L _ S φ)
      atTop (nhds 0) := by
    refine squeeze_zero (fun n => structProb_nonneg _ _) (fun n => ?_) hsum
    refine (structProb_mono fun S hS => ?_).trans (structProb_exists_le (μ n) T₀ _)
    push Not at hS
    obtain ⟨φ, hφ, hS⟩ := hS
    exact ⟨φ, hφ, (@Sentence.realize_not L _ S φ).2 hS⟩
  have := hbad.const_sub 1
  simp only [sub_zero, structProb_not, sub_sub_cancel] at this
  exact this

/-- **Compactness.** If every sentence of `T` holds with probability tending to `1`, then `T` is
satisfiable. -/
theorem isSatisfiable_of_tendsto_sentenceProb {T : L.Theory}
    (h : ∀ φ ∈ T, Tendsto (fun n => sentenceProb (μ n) φ) atTop (nhds 1)) :
    T.IsSatisfiable := by
  rw [Theory.isSatisfiable_iff_isFinitelySatisfiable]
  intro T₀ hT₀
  have hT₀1 := tendsto_structProb_forall_finset μ T₀ fun φ hφ => h φ (hT₀ hφ)
  obtain ⟨n, hn, hn1⟩ := (hT₀1.eventually (lt_mem_nhds (show (0 : ℝ) < 1 from one_pos))).and
    (eventually_ge_atTop 1) |>.exists
  obtain ⟨S, hS⟩ := exists_of_structProb_pos hn
  let := S
  have : Nonempty (Fin n) := ⟨⟨0, hn1⟩⟩
  have : Fin n ⊨ (T₀ : L.Theory) := (Theory.model_iff _).2 fun φ hφ => hS φ hφ
  exact Theory.Model.isSatisfiable (Fin n)

/-- If every sentence of `T` holds with probability tending to `1`, so does every consequence
of `T`. -/
theorem tendsto_sentenceProb_of_models {T : L.Theory}
    (h : ∀ φ ∈ T, Tendsto (fun n => sentenceProb (μ n) φ) atTop (nhds 1))
    {φ : L.Sentence} (hφ : T ⊨ᵇ φ) :
    Tendsto (fun n => sentenceProb (μ n) φ) atTop (nhds 1) := by
  obtain ⟨T₀, hT₀, hφ⟩ := Theory.models_iff_finset_models.1 hφ
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_structProb_forall_finset μ T₀ fun ψ hψ => h ψ (hT₀ hψ))
    tendsto_const_nhds ?_ (Eventually.of_forall fun n => structProb_le_one _ _)
  filter_upwards [eventually_ge_atTop 1] with n hn
  refine structProb_mono fun S hS => ?_
  let := S
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have : Fin n ⊨ (T₀ : L.Theory) := (Theory.model_iff _).2 fun ψ hψ => hS ψ hψ
  exact hφ.realize_sentence (Fin n)

/-- If every sentence of `T` holds with probability tending to `1`, then every sentence refuted by
`T` holds with probability tending to `0`. -/
theorem tendsto_sentenceProb_of_models_not {T : L.Theory}
    (h : ∀ φ ∈ T, Tendsto (fun n => sentenceProb (μ n) φ) atTop (nhds 1))
    {φ : L.Sentence} (hφ : T ⊨ᵇ φ.not) :
    Tendsto (fun n => sentenceProb (μ n) φ) atTop (nhds 0) := by
  have := (tendsto_sentenceProb_of_models μ h hφ).const_sub 1
  simp only [sentenceProb_not, sub_sub_cancel, sub_self] at this
  exact this

/-- **Transfer to a 0-1 law.** If every sentence of a complete theory `T` holds with probability
tending to `1`, then every sentence has probability tending to `0` or to `1` [Fagin1976]. -/
theorem zero_one_law_of_isComplete {T : L.Theory} (hT : T.IsComplete)
    (h : ∀ φ ∈ T, Tendsto (fun n => sentenceProb (μ n) φ) atTop (nhds 1))
    (φ : L.Sentence) :
    Tendsto (fun n => sentenceProb (μ n) φ) atTop (nhds 0) ∨
      Tendsto (fun n => sentenceProb (μ n) φ) atTop (nhds 1) := by
  rcases hT.2 φ with hφ | hφ
  · exact Or.inr (tendsto_sentenceProb_of_models μ h hφ)
  · exact Or.inl (tendsto_sentenceProb_of_models_not μ h hφ)

/-- If every sentence of a complete theory `T` holds with probability tending to `1`, then the
sentences of limit probability `1` are exactly the consequences of `T`. -/
theorem tendsto_sentenceProb_one_iff_of_isComplete {T : L.Theory} (hT : T.IsComplete)
    (h : ∀ φ ∈ T, Tendsto (fun n => sentenceProb (μ n) φ) atTop (nhds 1))
    (φ : L.Sentence) :
    Tendsto (fun n => sentenceProb (μ n) φ) atTop (nhds 1) ↔ T ⊨ᵇ φ := by
  refine ⟨fun h1 => (hT.2 φ).resolve_right fun hn => ?_, tendsto_sentenceProb_of_models μ h⟩
  exact zero_ne_one (tendsto_nhds_unique (tendsto_sentenceProb_of_models_not μ h hn) h1)

/-- If every sentence of a complete theory `T` holds with probability tending to `1`, then the
sentences of limit probability `0` are exactly the sentences that `T` refutes. -/
theorem tendsto_sentenceProb_zero_iff_of_isComplete {T : L.Theory} (hT : T.IsComplete)
    (h : ∀ φ ∈ T, Tendsto (fun n => sentenceProb (μ n) φ) atTop (nhds 1))
    (φ : L.Sentence) :
    Tendsto (fun n => sentenceProb (μ n) φ) atTop (nhds 0) ↔ T ⊨ᵇ φ.not := by
  refine ⟨fun h0 => (hT.2 φ).resolve_left fun hp => ?_, tendsto_sentenceProb_of_models_not μ h⟩
  exact zero_ne_one (tendsto_nhds_unique h0 (tendsto_sentenceProb_of_models μ h hp))

/-- Under a 0-1 law, a property whose probability tends neither to `0` nor to `1` agrees with no
sentence on all sufficiently large structures. -/
theorem not_exists_sentence_of_not_tendsto
    (hzo : ∀ φ : L.Sentence,
      Tendsto (fun n => sentenceProb (μ n) φ) atTop (nhds 0) ∨
        Tendsto (fun n => sentenceProb (μ n) φ) atTop (nhds 1))
    (P : ∀ n, L.Structure (Fin n) → Prop)
    (h0 : ¬Tendsto (fun n => structProb (μ n) (P n)) atTop (nhds 0))
    (h1 : ¬Tendsto (fun n => structProb (μ n) (P n)) atTop (nhds 1)) :
    ¬∃ φ : L.Sentence, ∀ᶠ n in atTop,
      ∀ S : L.Structure (Fin n), @Sentence.Realize L _ S φ ↔ P n S := by
  rintro ⟨φ, hφ⟩
  have heq : (fun n => sentenceProb (μ n) φ) =ᶠ[atTop] fun n => structProb (μ n) (P n) := by
    filter_upwards [hφ] with n hn
    rw [sentenceProb, show (fun S => @Sentence.Realize L _ S φ) = P n from
      funext fun S => propext (hn S)]
  rcases hzo φ with h | h
  · exact h0 (h.congr' heq)
  · exact h1 (h.congr' heq)

/-- Under a 0-1 law, having an even number of elements agrees with no sentence on all
sufficiently large structures: its probability alternates between `1` and `0`. -/
theorem not_exists_sentence_even_card_of_zero_one_law
    (hzo : ∀ φ : L.Sentence,
      Tendsto (fun n => sentenceProb (μ n) φ) atTop (nhds 0) ∨
        Tendsto (fun n => sentenceProb (μ n) φ) atTop (nhds 1)) :
    ¬∃ φ : L.Sentence, ∀ᶠ n in atTop,
      ∀ S : L.Structure (Fin n), @Sentence.Realize L _ S φ ↔ Even n := by
  have hval : ∀ n, structProb (μ n) (fun _ => Even n) = if Even n then 1 else 0 := fun n => by
    by_cases hn : Even n
    · simp only [hn, ↓reduceIte, structProb_true]
    · simp only [hn, ↓reduceIte, structProb_false]
  have hev : Tendsto (fun m : ℕ => 2 * m) atTop atTop := tendsto_id.const_mul_atTop' two_pos
  have hodd : Tendsto (fun m : ℕ => 2 * m + 1) atTop atTop :=
    tendsto_atTop_mono (fun m => Nat.le_succ (2 * m)) hev
  refine not_exists_sentence_of_not_tendsto μ hzo (fun n _ => Even n) (fun h => ?_) (fun h => ?_)
  · -- Along even `n` the probability is `1`.
    have := h.comp hev
    simp only [Function.comp_def, hval, even_two_mul, ↓reduceIte] at this
    exact one_ne_zero (tendsto_const_nhds_iff.1 this)
  · -- Along odd `n` the probability is `0`.
    have := h.comp hodd
    simp only [Function.comp_def, hval, Nat.not_even_two_mul_add_one, ↓reduceIte] at this
    exact zero_ne_one (tendsto_const_nhds_iff.1 this)

end Transfer

end Cslib.Logic.FO
