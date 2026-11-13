/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.MachineLearning.PACLearning.Compression.Basic
public import CslibFrontier.MachineLearning.OnlineLearning.MistakeBound.OnlineToBatch
public import CslibFrontier.MachineLearning.OnlineLearning.MistakeBound.SOA

/-!
# Compression schemes from mistake bounds

A deterministic online learner `A` with mistake bound `M` on a class `C` gives a sample compression
scheme of size `M` for `C` [FloydWarmuth1995] (locator unverified);
[ShalevShwartzBenDavid2014, §30.2.4] uses the same idea for the Perceptron, whose at most
`1 / γ ^ 2` updates on a sample separated with margin `γ` give a scheme of that size. Run `A`
over the sample in index order, feeding it only the examples it has got wrong so far, and keep
exactly those examples. Repeat this pass from the examples kept so far. On a sample realized by
`C` the kept examples are, in order, a sequence on which `A` errs every time, so there are at most
`M` of them; each pass that keeps a new example therefore increases their number, and after
`M + 1` passes a pass keeps nothing new. In that last pass `A`, fed the kept examples, labels
every example of the sample correctly. The reconstruction is `A` itself.

For a measurable learner (`IsMeasurableLearner`), the compression bound gives the realizable
sample size `(m + 1) ^ M (1 - ε) ^ (m - M) ≤ δ`, which is logarithmic in `1 / δ`
(`isPACLearnerFor_of_mistakeBound_le`). The prefix-majority conversion of
`CslibFrontier/MachineLearning/OnlineLearning/MistakeBound/OnlineToBatch.lean`
(`isPACLearnerFor_prefixMajority`) needs `2 M ≤ ε δ (m + 1)`, linear in `1 / δ`, but has no
`log m` factor. With the Standard Optimal Algorithm, a class of Littlestone dimension at most `d`
has a scheme of size `d`; on a countable domain this gives the sample size
`(m + 1) ^ d (1 - ε) ^ (m - d) ≤ δ` (`isPACLearnerFor_of_littlestoneDim_le`).

## Main definitions

- `SampleCompressionScheme.mistakePass`: one pass of the online learner over the sample, keeping
  the examples it gets wrong.
- `SampleCompressionScheme.ofMistakeBound`: the size-`M` scheme of a learner with mistake bound
  `M`, reconstructing with the learner itself.
- `SampleCompressionScheme.ofLittlestoneDim`: the size-`d` scheme of a class of Littlestone
  dimension at most `d`, from the Standard Optimal Algorithm.

## Main results

- `SampleCompressionScheme.mistakes_mistakePass_iterate`: on every sample, the examples kept after
  any number of passes form a sequence on which the learner errs at every step.
- `IsMeasurableLearner.measurableReconstruction`: a measurable online learner is a measurable
  reconstruction map.
- `SampleCompressionScheme.isPACLearnerFor_of_mistakeBound_le`: a measurable learner with mistake
  bound `M` on `C` gives a PAC learner in the realizable setting from every `m` with
  `(m + 1) ^ M (1 - ε) ^ (m - M) ≤ δ`.
- `SampleCompressionScheme.isPACLearnerFor_of_littlestoneDim_le`: on a countable domain, a class of
  Littlestone dimension at most `d` is PAC learnable in the realizable setting from every `m` with
  `(m + 1) ^ d (1 - ε) ^ (m - d) ≤ δ`.

## References

* [S. Floyd, M. K. Warmuth, *Sample compression, learnability, and the Vapnik–Chervonenkis
  dimension*][FloydWarmuth1995]
* [S. Shalev-Shwartz, S. Ben-David, *Understanding Machine Learning: From Theory to
  Algorithms*][ShalevShwartzBenDavid2014]
* [N. Littlestone, *Learning quickly when irrelevant attributes abound: a new linear-threshold
  algorithm*][Littlestone1988]
-/

public section

open MeasureTheory
open scoped NNReal
open Cslib.MachineLearning.OnlineLearning.MistakeBound (OnlineLearner IsMeasurableLearner mistakes
  mistakesFrom
  mistakesFrom_append mistakesFrom_cons mistakeBound mistakes_le_mistakeBound littlestoneDim soa
  mistakeBound_soa)

namespace Cslib.MachineLearning.OnlineLearning.MistakeBound

/-- A measurable online learner, used as a reconstruction map, has measurable misclassification
sets. -/
theorem IsMeasurableLearner.measurableReconstruction {α : Type*} [MeasurableSpace α]
    {A : OnlineLearner α} (hA : IsMeasurableLearner A) :
    PACLearning.MeasurableReconstruction A :=
  PACLearning.measurableReconstruction_of_measurable hA

end Cslib.MachineLearning.OnlineLearning.MistakeBound

namespace Cslib.MachineLearning.PACLearning.SampleCompressionScheme

variable {α : Type*} {m : ℕ}

/-- One step of a pass: keep the example `i` if the learner `A`, fed the kept examples `L`, labels
it wrongly. -/
@[expose] def mistakeStep (A : OnlineLearner α) (S : LabeledSample α Bool m) (L : List (Fin m))
    (i : Fin m) : List (Fin m) :=
  if A (L.map S) (S i).1 = (S i).2 then L else L ++ [i]

/-- One pass of the learner `A` over the sample `S` in index order, starting from the kept
examples `L`: each example that `A`, fed the examples kept so far, labels wrongly is kept. -/
@[expose] def mistakePass (A : OnlineLearner α) (S : LabeledSample α Bool m) (L : List (Fin m)) :
    List (Fin m) :=
  (List.finRange m).foldl (mistakeStep A S) L

/-- A step of a pass keeps its example exactly when the learner errs on it, so it preserves the
property that the learner errs at every kept example. -/
private theorem mistakesFrom_mistakeStep (A : OnlineLearner α) (S : LabeledSample α Bool m)
    (L : List (Fin m)) (i : Fin m) :
    mistakesFrom A [] ((mistakeStep A S L i).map S) = mistakesFrom A [] (L.map S) +
      ((mistakeStep A S L i).length - L.length) := by
  unfold mistakeStep
  split_ifs with h
  · simp
  · rw [List.map_append, mistakesFrom_append, List.nil_append, List.map_singleton,
      ← Prod.mk.eta (p := S i), mistakesFrom_cons]
    simp [h]

/-- The fold invariant of a pass: if the learner errs at every kept example before the pass, it
errs at every kept example after it; the kept list only grows; and if it does not grow then it is
unchanged and the learner, fed it, labels every example of the pass correctly. -/
private theorem foldl_mistakeStep (A : OnlineLearner α) (S : LabeledSample α Bool m)
    (is : List (Fin m)) (L : List (Fin m)) (hL : mistakesFrom A [] (L.map S) = L.length) :
    mistakesFrom A [] ((is.foldl (mistakeStep A S) L).map S) = (is.foldl (mistakeStep A S) L).length
      ∧ L.length ≤ (is.foldl (mistakeStep A S) L).length ∧
      ((is.foldl (mistakeStep A S) L).length = L.length →
        is.foldl (mistakeStep A S) L = L ∧ ∀ i ∈ is, A (L.map S) (S i).1 = (S i).2) := by
  induction is generalizing L with
  | nil => simp [hL]
  | cons i is ih =>
    have hstep : L.length ≤ (mistakeStep A S L i).length := by
      unfold mistakeStep; split_ifs <;> simp
    have hinv : mistakesFrom A [] ((mistakeStep A S L i).map S) =
        (mistakeStep A S L i).length := by
      rw [mistakesFrom_mistakeStep, hL]; omega
    obtain ⟨h1, h2, h3⟩ := ih (mistakeStep A S L i) hinv
    simp only [List.foldl_cons]
    refine ⟨h1, hstep.trans h2, fun heq => ?_⟩
    have hlen : (mistakeStep A S L i).length = L.length := le_antisymm (heq ▸ h2) hstep
    have hi : A (L.map S) (S i).1 = (S i).2 := by
      by_contra h
      simp [mistakeStep, h] at hlen
    have hL' : mistakeStep A S L i = L := by simp [mistakeStep, hi]
    obtain ⟨h4, h5⟩ := h3 (heq.trans hlen.symm)
    rw [hL'] at h5
    exact ⟨h4.trans hL', List.forall_mem_cons.2 ⟨hi, h5⟩⟩

/-- **Kept examples are mistakes.** After any number of passes from no kept examples, the learner
errs at every kept example, in the kept order. -/
theorem mistakes_mistakePass_iterate (A : OnlineLearner α) (S : LabeledSample α Bool m) (n : ℕ) :
    mistakes A (((mistakePass A S)^[n] []).map S) = ((mistakePass A S)^[n] []).length := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact (foldl_mistakeStep A S _ _ ih).1

/-- After `n` passes from no kept examples, either the next pass keeps nothing new or at least `n`
examples are kept. -/
private theorem mistakePass_iterate_fixed_or_le (A : OnlineLearner α) (S : LabeledSample α Bool m)
    (n : ℕ) :
    mistakePass A S ((mistakePass A S)^[n] []) = (mistakePass A S)^[n] [] ∨
      n ≤ ((mistakePass A S)^[n] []).length := by
  induction n with
  | zero => exact Or.inr le_rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    set L := (mistakePass A S)^[n] []
    obtain ⟨-, hle, hfix⟩ : _ ∧ L.length ≤ (mistakePass A S L).length ∧
        ((mistakePass A S L).length = L.length → mistakePass A S L = L ∧ _) :=
      foldl_mistakeStep A S (List.finRange m) L (mistakes_mistakePass_iterate A S n)
    rcases ih with ih | ih
    · left; rw [ih, ih]
    · by_cases hlen : (mistakePass A S L).length = L.length
      · left; rw [(hfix hlen).1, (hfix hlen).1]
      · right; exact (Nat.succ_le_of_lt (lt_of_le_of_lt ih (lt_of_le_of_ne hle (Ne.symm hlen))))

/-- On a sample realized by `C`, if `A` makes at most `M` mistakes on sequences realized by `C`,
then at most `M` examples are kept after any number of passes. -/
theorem length_mistakePass_iterate_le {A : OnlineLearner α} {C : ConceptClass α Bool} {M : ℕ}
    (hA : mistakeBound A C ≤ M) {S : LabeledSample α Bool m} (hS : Realizable C S) (n : ℕ) :
    ((mistakePass A S)^[n] []).length ≤ M := by
  obtain ⟨c, hc, hcS⟩ := hS
  have hreal : OnlineLearning.MistakeBound.Realizable C (((mistakePass A S)^[n] []).map S) :=
    OnlineLearning.MistakeBound.realizable_iff.2 ⟨c, hc, by simp [hcS]⟩
  rw [← mistakes_mistakePass_iterate]
  exact_mod_cast (mistakes_le_mistakeBound hreal).trans hA

/-- On a sample realized by `C`, if `A` makes at most `M` mistakes on sequences realized by `C`,
then after `M + 1` passes the learner, fed the kept examples, labels every example of the sample
correctly. -/
theorem apply_mistakePass_iterate_eq {A : OnlineLearner α} {C : ConceptClass α Bool} {M : ℕ}
    (hA : mistakeBound A C ≤ M) {S : LabeledSample α Bool m} (hS : Realizable C S) (i : Fin m) :
    A (((mistakePass A S)^[M + 1] []).map S) (S i).1 = (S i).2 := by
  set L := (mistakePass A S)^[M + 1] []
  have hfix : mistakePass A S L = L :=
    (mistakePass_iterate_fixed_or_le A S (M + 1)).resolve_right fun h =>
      (length_mistakePass_iterate_le hA hS (M + 1)).not_gt h
  obtain ⟨-, -, h⟩ := foldl_mistakeStep A S (List.finRange m) L
    (mistakes_mistakePass_iterate A S (M + 1))
  exact (h (congrArg List.length hfix)).2 i (List.mem_finRange i)

/-- **Mistake bounds give compression schemes** [FloydWarmuth1995]. If the online learner `A`
makes at most `M` mistakes on every sequence realized by `C`, then `M + 1` passes of `A` over the
sample, each keeping the examples that `A`, fed the examples kept so far, labels wrongly, compress
every realizable sample to at most `M` examples, from which `A` itself reconstructs a hypothesis
that labels the whole sample correctly. -/
@[expose] def ofMistakeBound (A : OnlineLearner α) {C : ConceptClass α Bool} {M : ℕ}
    (hA : mistakeBound A C ≤ M) : SampleCompressionScheme C M where
  compress S := (mistakePass A S)^[M + 1] []
  reconstruct := A
  length_compress_le _ hS := length_mistakePass_iterate_le hA hS (M + 1)
  reconstruct_correct _ hS i := apply_mistakePass_iterate_eq hA hS i

/-- The scheme of a mistake bound keeps the examples left after `M + 1` passes. -/
@[simp] theorem ofMistakeBound_compress (A : OnlineLearner α) {C : ConceptClass α Bool} {M : ℕ}
    (hA : mistakeBound A C ≤ M) (S : LabeledSample α Bool m) :
    (ofMistakeBound A hA).compress S = (mistakePass A S)^[M + 1] [] := rfl

/-- The scheme of a mistake bound reconstructs with the online learner itself. -/
@[simp] theorem ofMistakeBound_reconstruct (A : OnlineLearner α) {C : ConceptClass α Bool}
    {M : ℕ} (hA : mistakeBound A C ≤ M) : (ofMistakeBound A hA).reconstruct = A := rfl

/-- A class of Littlestone dimension at most `d` has a sample compression scheme of size `d`,
which reconstructs with the Standard Optimal Algorithm. -/
noncomputable def ofLittlestoneDim {C : ConceptClass α Bool} {d : ℕ}
    (hC : littlestoneDim C ≤ d) : SampleCompressionScheme C d :=
  ofMistakeBound (soa C) ((mistakeBound_soa C).trans_le hC)

/-- **Explicit realizable sample size from a mistake bound.** A measurable online learner `A` with
mistake bound `M` on `C` gives, through its compression scheme, a PAC learner in the realizable
setting from every number `m` of examples with `(m + 1) ^ M (1 - ε) ^ (m - M) ≤ δ`. -/
theorem isPACLearnerFor_of_mistakeBound_le [MeasurableSpace α] {A : OnlineLearner α}
    (hA : IsMeasurableLearner A) {C : ConceptClass α Bool} {M : ℕ} (hM : mistakeBound A C ≤ M)
    {m : ℕ} {ε δ : Set.Ioo (0 : ℝ≥0) 1}
    (hm : ((m : ℝ) + 1) ^ M * (1 - (ε.val : ℝ)) ^ (m - M) ≤ δ.val) :
    IsPACLearnerFor m ε δ C (realizableDistributions C) :=
  (ofMistakeBound A hM).isPACLearnerFor hA.measurableReconstruction hm

/-- **Explicit realizable sample size from the Littlestone dimension.** On a countable domain, a
class of Littlestone dimension at most `d` has a PAC learner in the realizable setting from every
number `m` of examples with `(m + 1) ^ d (1 - ε) ^ (m - d) ≤ δ`. -/
theorem isPACLearnerFor_of_littlestoneDim_le [MeasurableSpace α] [Countable α]
    [MeasurableSingletonClass α] {C : ConceptClass α Bool} {d : ℕ} (hC : littlestoneDim C ≤ d)
    {m : ℕ} {ε δ : Set.Ioo (0 : ℝ≥0) 1}
    (hm : ((m : ℝ) + 1) ^ d * (1 - (ε.val : ℝ)) ^ (m - d) ≤ δ.val) :
    IsPACLearnerFor m ε δ C (realizableDistributions C) :=
  (ofLittlestoneDim hC).isPACLearnerFor (measurableReconstruction_of_countable _) hm

end Cslib.MachineLearning.PACLearning.SampleCompressionScheme
