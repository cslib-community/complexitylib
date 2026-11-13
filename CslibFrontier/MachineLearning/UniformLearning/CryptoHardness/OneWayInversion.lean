/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.OneWay.Weak
public import CslibFrontier.MachineLearning.UniformLearning.CryptoHardness.Inversion
public import CslibFrontier.Foundations.Data.BitString.List
public import CslibFrontier.Probability.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Probability.PMF.Bool

/-!
# No one-way functions: learning by inversion in polynomial time

A *key-and-point family* is given by a polynomial-time predicate `F : ℕ → List Bool → Bool`, a key
length `keyBits n` and a sample count `samples n`: at scale `n` the key `K` labels the `n`-bit
point `x` by `F n (K ++ x)` (`family`). Its labelling map `labelMap` reads a key and `samples n`
points from its input and outputs the points followed by their labels, so a uniform input is a
uniform key with uniform examples. An inverter for `labelMap` therefore returns, on the encoding
`encodeSample S` of a labelled sample, a key consistent with `S` whenever it succeeds. By
`bind_labelInversion_lt_uniformError_le`, such a key has small uniform error.

If no weak one-way function exists, `OneWayReindex.weakOneWay` shows that `labelMap` is not weakly
one-way, so for every positive polynomial `q` some uniform strict PPT inverter wins its inversion
game with probability above `1 - 1 / q n` on infinitely many scales. This is the easy direction of
the equivalence between average-case learning and one-way functions
[BlumFurstKearnsLipton1993] [ImpagliazzoLevin1990], over uniform examples. The learning guarantee
holds only on infinitely many scales, because the negation of one-wayness supplies a good
inverter only there.

## Main definitions

* `Cslib.MachineLearning.UniformLearning.OneWayInversion.family`: the key-and-point family.
* `Cslib.MachineLearning.UniformLearning.OneWayInversion.labelMap`: its labelling map on bit
  strings.
* `Cslib.MachineLearning.UniformLearning.OneWayInversion.inverterLearner`: the learner that runs an
  inverter on the encoded sample.
* `Cslib.MachineLearning.UniformLearning.OneWayInversion.learningExperiment`: a uniform key,
  uniform examples and the learner's key.

## Main results

* `Cslib.MachineLearning.UniformLearning.OneWayInversion.learningExperiment_inconsistent_le`: the
  learner's inconsistency probability is at most the inverter's failure probability.
* `Cslib.MachineLearning.UniformLearning.OneWayInversion.computableInPolyTime_labelMap`: the
  labelling map is polynomial-time computable.
* `Cslib.MachineLearning.UniformLearning.OneWayInversion.exists_learner_of_not_exists_weakOneWay`:
  without weak one-way functions, every polynomial-time key-and-point family is learned on
  infinitely many scales.

## References

* [A. Blum, M. Furst, M. Kearns, R. J. Lipton, *Cryptographic primitives based on hard learning
  problems*][BlumFurstKearnsLipton1993]
* [R. Impagliazzo, L. A. Levin, *No better ways to generate hard NP instances than picking
  uniformly at random*][ImpagliazzoLevin1990]
-/

public section

namespace Cslib.MachineLearning.UniformLearning.OneWayInversion

open PACLearning Cslib.Crypto Cslib.Probability Turing.MultiTapeTM Filter
open scoped ENNReal

variable (keyBits samples : ℕ → ℕ) (F : ℕ → List Bool → Bool)

/-- The key-and-point family at scale `n`: key `K` labels the point `x` by `F n (K ++ x)`. -/
@[expose] def family (n : ℕ) (K : BitString (keyBits n)) (x : Fin n → Bool) : Bool :=
  F n (List.ofFn K ++ List.ofFn x)

/-- Input length at scale `n`: a key, `samples n` points and `n + 1` spare bits. -/
def inputLength (n : ℕ) : ℕ := keyBits n + samples n * n + (n + 1)

/-- The labelling map at scale `n`: read a key and `samples n` points of `n` bits from the input,
padding missing bits with `false`, and output the points followed by their labels. -/
def labelMap (n : ℕ) (w : List Bool) : List Bool :=
  let key := BitString.listRow (keyBits n) 0 w
  let rows := BitString.listRows (samples n) n (w.drop (keyBits n))
  rows.flatten ++ rows.map fun x => F n (key ++ x)

/-- The bit encoding of a labelled sample: its points followed by their labels. -/
@[expose] def encodeSample {n m : ℕ} (S : LabeledSample (Fin n → Bool) Bool m) : List Bool :=
  (List.ofFn fun i => List.ofFn (S i).1).flatten ++ List.ofFn fun i => (S i).2

/-- The rows of `s` points of `n` bits followed by anything are the points. -/
private theorem listRows_flatten_ofFn_append {s n : ℕ} (x : Fin s → Fin n → Bool)
    (rest : List Bool) :
    BitString.listRows s n ((List.ofFn fun i => List.ofFn (x i)).flatten ++ rest) =
      List.ofFn fun i => List.ofFn (x i) := by
  induction s with
  | zero => simp [BitString.listRows]
  | succ s ih =>
    rw [List.ofFn_succ, List.flatten_cons, List.append_assoc,
      BitString.listRows_succ_append _ _ (List.length_ofFn), ih fun i => x i.succ]

/-- The labelling map on a key followed by the points of a sample is the encoding of the
labelled sample. -/
theorem labelMap_append (n : ℕ) (K : BitString (keyBits n)) (x : Fin (samples n) → Fin n → Bool)
    (rest : List Bool) :
    labelMap keyBits samples F n
        (List.ofFn K ++ ((List.ofFn fun i => List.ofFn (x i)).flatten ++ rest)) =
      encodeSample (examples (family keyBits F n K) x) := by
  have hkey : BitString.listRow (keyBits n) 0
      (List.ofFn K ++ ((List.ofFn fun i => List.ofFn (x i)).flatten ++ rest)) = List.ofFn K := by
    rw [BitString.listRow_zero, BitString.ofList_ofFn_append]
  have hdrop : (List.ofFn K ++ ((List.ofFn fun i => List.ofFn (x i)).flatten ++ rest)).drop
      (keyBits n) = (List.ofFn fun i => List.ofFn (x i)).flatten ++ rest :=
    List.drop_left' (by simp)
  simp only [labelMap, hkey, hdrop, listRows_flatten_ofFn_append, encodeSample, examples_apply,
    family, List.map_ofFn, Function.comp_def]

/-- A word whose labelling map is the encoding of a labelled sample starts with a key that is
consistent with the sample. -/
theorem consistent_of_labelMap_eq {n : ℕ} {S : LabeledSample (Fin n → Bool) Bool (samples n)}
    {w : List Bool} (h : labelMap keyBits samples F n w = encodeSample S) (i : Fin (samples n)) :
    family keyBits F n (BitString.ofList (keyBits n) w) (S i).1 = (S i).2 := by
  have hlen : (BitString.listRows (samples n) n (w.drop (keyBits n))).flatten.length =
      (List.ofFn fun i => List.ofFn (S i).1).flatten.length := by
    rw [List.length_flatten, List.length_flatten]
    simp [List.map_ofFn, Function.comp_def, BitString.listRows]
  have happ := List.append_inj h hlen
  have hrows : BitString.listRows (samples n) n (w.drop (keyBits n)) =
      List.ofFn fun i => List.ofFn (S i).1 := by
    have e := BitString.listRows_eq_ofFn (samples n) n (w.drop (keyBits n))
    have h1 := congrArg (fun l => BitString.listRows (samples n) n (l ++ [])) happ.1
    rw [e] at h1 ⊢
    rwa [listRows_flatten_ofFn_append, listRows_flatten_ofFn_append] at h1
  have hlabels := happ.2
  rw [hrows, List.map_ofFn] at hlabels
  have := congrFun (List.ofFn_inj.1 hlabels) i
  simpa only [Function.comp_apply, BitString.listRow_zero, family] using this

/-- Independent uniform points of `n` bits, concatenated, form a uniform word. -/
theorem map_flatten_uniformOfFintype (s n : ℕ) :
    (PMF.uniformOfFintype (Fin s → Fin n → Bool)).map
      (fun x => (List.ofFn fun i => List.ofFn (x i)).flatten) = BitString.uniformList (s * n) := by
  rw [BitString.uniformList,
    ← PMF.uniformOfFintype_map_equiv (BitString.blocksEquiv (α := Bool) (m := s) (k := n)),
    PMF.map_comp]
  congr 1
  funext y
  rw [Function.comp_apply, ← BitString.ofFn_blocksEquiv_symm, Equiv.symm_apply_apply]

/-- A uniform input of the labelling map is a uniform key, then uniform points, then uniform spare
bits. -/
theorem uniformList_inputLength (n : ℕ) :
    BitString.uniformList (inputLength keyBits samples n) =
      (PMF.uniformOfFintype (BitString (keyBits n))).bind fun K =>
        (PMF.uniformOfFintype (Fin (samples n) → Fin n → Bool)).bind fun x =>
          (BitString.uniformList (n + 1)).map fun rest =>
            List.ofFn K ++ ((List.ofFn fun i => List.ofFn (x i)).flatten ++ rest) := by
  rw [inputLength, add_assoc, BitString.uniformList_add (keyBits n),
    BitString.uniformList_add (samples n * n), ← map_flatten_uniformOfFintype]
  simp only [BitString.uniformList, PMF.bind_map, PMF.map_bind, PMF.map_comp, Function.comp_def]

/-- The learner obtained from an inverter `A` for the labelling map: run `A` on the encoded sample
and read a key from the first `keyBits n` bits of its answer. -/
@[expose] noncomputable def inverterLearner (A : Inverter) (n : ℕ) {m : ℕ}
    (S : LabeledSample (Fin n → Bool) Bool m) : PMF (BitString (keyBits n)) :=
  (ProbComp.eval (A n (encodeSample S))).map (BitString.ofList (keyBits n))

/-- The learning experiment at scale `n`: a uniform key `K`, `samples n` uniform examples `S` of its
function, and the key `K'` that `inverterLearner keyBits A n` returns on `S`. -/
@[expose] noncomputable def learningExperiment (A : Inverter) (n : ℕ) :
    PMF (BitString (keyBits n) × LabeledSample (Fin n → Bool) Bool (samples n) ×
      BitString (keyBits n)) :=
  (PMF.uniformOfFintype (BitString (keyBits n))).bind fun K =>
    (labelInversion (family keyBits F n) (inverterLearner keyBits A n) K).map fun p => (K, p)

/-- **Inversion failure is game failure.** In the learning experiment, the probability that the
learner built from `A` returns a key inconsistent with its sample is at most the probability that
`A` loses the inversion game for the labelling map. -/
theorem learningExperiment_inconsistent_le (A : Inverter) (n : ℕ) :
    (learningExperiment keyBits samples F A n).toOuterMeasure
        {(_, S, K') : BitString (keyBits n) × LabeledSample (Fin n → Bool) Bool (samples n) ×
          BitString (keyBits n) | ∃ i, family keyBits F n K' (S i).1 ≠ (S i).2} ≤
      ProbComp.eval (OneWayReindex.familyInversionGame (inputLength keyBits samples)
        (labelMap keyBits samples F) A n) false := by
  classical
  set Q : PMF (BitString (keyBits n) × (Fin (samples n) → Fin n → Bool) × List Bool) :=
    (PMF.uniformOfFintype (BitString (keyBits n))).bind fun K =>
      (PMF.uniformOfFintype (Fin (samples n) → Fin n → Bool)).bind fun x =>
        (ProbComp.eval (A n (encodeSample (examples (family keyBits F n K) x)))).map
          fun c => (K, x, c)
  have hleft : learningExperiment keyBits samples F A n = Q.map fun (K, x, c) =>
      (K, examples (family keyBits F n K) x, BitString.ofList (keyBits n) c) := by
    simp only [Q, learningExperiment, labelInversion, inverterLearner, uniformExamples,
      PMF.map_bind, PMF.bind_map, PMF.map_comp, Function.comp_def]
  have hright : ProbComp.eval (OneWayReindex.familyInversionGame (inputLength keyBits samples)
      (labelMap keyBits samples F) A n) =
      Q.map fun (K, x, c) =>
        labelMap keyBits samples F n (c.take (inputLength keyBits samples n)) ==
          encodeSample (examples (family keyBits F n K) x) := by
    simp only [OneWayReindex.familyInversionGame, ProbComp.eval_bind, ProbComp.eval_pure,
      BitString.eval_sampleList, uniformList_inputLength, PMF.bind_bind, PMF.bind_map,
      Function.comp_def, labelMap_append]
    simp only [Q, PMF.map_bind, PMF.map_comp, Function.comp_def, PMF.bind_const]
    rfl
  rw [hleft, hright, PMF.toOuterMeasure_map_apply, ← PMF.toOuterMeasure_apply_singleton,
    PMF.toOuterMeasure_map_apply]
  refine Q.toOuterMeasure.mono fun ⟨K, x, c⟩ ⟨i, hi⟩ => ?_
  simp only [Set.mem_preimage, Set.mem_singleton_iff, beq_eq_false_iff_ne]
  intro heq
  refine hi ?_
  have hkb : keyBits n ≤ inputLength keyBits samples n :=
    (Nat.le_add_right _ _).trans (Nat.le_add_right _ _)
  have := consistent_of_labelMap_eq keyBits samples F heq i
  rwa [← BitString.ofList_take, List.take_take, min_eq_left hkb, BitString.ofList_take] at this

/-! ### Polynomial-time certificates -/

/-- The input length is polynomial-time computable in unary. -/
theorem computableInPolyTime_inputLength
    (hkeyBits : ComputableInPolyTime keyBits encUnary encUnary)
    (hsamples : ComputableInPolyTime samples encUnary encUnary) :
    ComputableInPolyTime (inputLength keyBits samples) encUnary encUnary := by
  unfold inputLength
  fun_prop

/-- The labelling map is polynomial-time computable when the scale-indexed predicate `F`, the key
length and the sample count are. -/
theorem computableInPolyTime_labelMap
    (hkeyBits : ComputableInPolyTime keyBits encUnary encUnary)
    (hsamples : ComputableInPolyTime samples encUnary encUnary)
    (hF : ComputableInPolyTime (fun p : ℕ × List Bool => F p.1 p.2) (encPair encUnary encBits)
      encBool) :
    ComputableInPolyTime (fun p : ℕ × List Bool => labelMap keyBits samples F p.1 p.2)
      (encPair encUnary encBits) encBits := by
  unfold labelMap
  fun_prop

/-! ### Learning from the absence of weak one-way functions -/

/-- **No weak one-way functions: learning by inversion in polynomial time**
([Blum, Furst, Kearns and Lipton][BlumFurstKearnsLipton1993];
[Impagliazzo and Levin][ImpagliazzoLevin1990]).
If no weak one-way function exists, then for every polynomial-time key-and-point family `F` with
polynomial-time key length and sample count and every positive polynomial `q`, some uniform strict
PPT inverter `A` gives a learner with the following guarantee on infinitely many scales `n`. For
a uniform key and `samples n` uniform examples of its function (`learningExperiment`), the learner
`inverterLearner keyBits A n` returns a key whose function has uniform error above `ε` with
probability at most
`1 / q n + 2 ^ keyBits n * (1 - ε) ^ samples n`, simultaneously for all `ε ≥ 0`. -/
theorem exists_learner_of_not_exists_weakOneWay
    (hOWF : ¬ ∃ f, WeakOneWay f)
    (hkeyBits : ComputableInPolyTime keyBits encUnary encUnary)
    (hsamples : ComputableInPolyTime samples encUnary encUnary)
    (hF : ComputableInPolyTime (fun p : ℕ × List Bool => F p.1 p.2) (encPair encUnary encBits)
      encBool)
    {q : Polynomial ℕ} (hq : ∀ n, 0 < q.eval n) :
    ∃ A : Inverter, IsPPT encBits A ∧ ∃ᶠ n in atTop, ∀ ε : ℝ, 0 ≤ ε →
      (learningExperiment keyBits samples F A n).toOuterMeasure
          {(K, _, K') : BitString (keyBits n) × LabeledSample (Fin n → Bool) Bool (samples n) ×
            BitString (keyBits n) |
            ε < uniformError (family keyBits F n K) (family keyBits F n K')} ≤
        ((q.eval n : ℕ) : ℝ≥0∞)⁻¹ + 2 ^ keyBits n * (1 - ENNReal.ofReal ε) ^ samples n := by
  have hex : ∃ A : Inverter, IsPPT encBits A ∧ ∃ᶠ n in atTop,
      1 - 1 / ((q.eval n : ℕ) : ℝ) < (Game.succProbability (ProbComp.eval
        (OneWayReindex.familyInversionGame (inputLength keyBits samples)
          (labelMap keyBits samples F) A n)) : ℝ) := by
    by_contra hcon
    push Not at hcon
    exact hOWF ⟨_, OneWayReindex.weakOneWay (computableInPolyTime_inputLength _ _ hkeyBits hsamples)
      (fun n => Nat.le_add_left _ _) (computableInPolyTime_labelMap _ _ _ hkeyBits hsamples hF) hq
      hcon⟩
  obtain ⟨A, hA, hfreq⟩ := hex
  refine ⟨A, hA, hfreq.mono fun n hn ε hε => ?_⟩
  set G := ProbComp.eval (OneWayReindex.familyInversionGame (inputLength keyBits samples)
    (labelMap keyBits samples F) A n)
  have hpos : (0 : ℝ) < (q.eval n : ℕ) := Nat.cast_pos.mpr (hq n)
  have hfail : G false ≤ ((q.eval n : ℕ) : ℝ≥0∞)⁻¹ := by
    have hlt : (G false).toReal < 1 / ((q.eval n : ℕ) : ℝ) := by
      rw [Cslib.Probability.PMF.toReal_false_eq_one_sub]
      simp only [Game.succProbability, ENNReal.coe_toNNReal_eq_toReal] at hn
      linarith
    rw [← ENNReal.ofReal_toReal (G.apply_ne_top false), ← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_inv_of_pos hpos, ← one_div]
    exact ENNReal.ofReal_le_ofReal hlt.le
  calc _ ≤ _ + Fintype.card (BitString (keyBits n)) * (1 - ENNReal.ofReal ε) ^ samples n :=
        bind_labelInversion_lt_uniformError_le (family keyBits F n) (inverterLearner keyBits A n)
          _ hε
    _ ≤ _ := by
        gcongr
        · exact (learningExperiment_inconsistent_le keyBits samples F A n).trans hfail
        · simp

end Cslib.MachineLearning.UniformLearning.OneWayInversion
