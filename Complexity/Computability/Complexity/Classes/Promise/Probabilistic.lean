/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.BPP
public import Complexity.Computability.Complexity.Classes.Promise.Reduction
public import Complexity.Computability.Complexity.Classes.RP
public import Complexity.Computability.Complexity.Classes.SharpP
public import Complexity.Computability.Probabilistic.PPT
public import Complexity.Languages.Probabilistic.BitString
public import Complexity.Languages.Probabilistic.Notation
import Complexity.Computability.Complexity.Classes.RP.Closure
import Complexity.Computability.Complexity.Classes.SharpP.Probability
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Probabilistic.CoinTape
import Complexity.Computability.Probabilistic.PPT.Capture
import Complexity.Computability.Probabilistic.Sampling
import Complexity.Probability.PMF.Uniform

/-!
# Probabilistic classes of promise problems

The probabilistic promise classes `PromiseBPP`, `PromiseRP` and `PromiseCoRP`, defined in
`Complexity.Computability.Complexity.Classes.BPP` and
`Complexity.Computability.Complexity.Classes.RP` together with the error conditions they share
with `BPP`, `RP` and `coRP`, follow Goldreich's semantic definitions [Goldreich, Definition 1.2
and Section 6.2][Goldreich2006], requiring bounded or one-sided error only on instances in the
promise. They contain the lifted classes `promiseClass (BPP enc)`, `promiseClass (RP enc)` and
`promiseClass (coRP enc)`.

Each class is equivalent to its uniform strict PPT program characterization
(`mem_PromiseBPP_iff_exists_isPPTOn`, `mem_PromiseRP_iff_exists_isPPTOn`,
`mem_PromiseCoRP_iff_exists_isPPTOn`) via saved-coin replay (`IsPPTOn.exists_seeded_evaluator`,
`IsPPTOn.exists_total_seeded_evaluator`), and is closed under deterministic polynomial-time promise
reductions (`PromiseProblem.PolyTimeReducible.mem_PromiseBPP`,
`PromiseProblem.PolyTimeReducible.mem_PromiseRP`,
`PromiseProblem.PolyTimeReducible.mem_PromiseCoRP`).

## Main results

* `Cslib.Complexity.mem_PromiseCoRP_iff`: a seeded-verifier characterization of `PromiseCoRP`.
* `Cslib.Complexity.promiseClass_BPP_subset_PromiseBPP`,
  `Cslib.Complexity.promiseClass_RP_subset_PromiseRP`,
  `Cslib.Complexity.promiseClass_coRP_subset_PromiseCoRP`: inclusion of the lifts of `BPP`, `RP`
  and `coRP`.
* `Cslib.Complexity.compl_mem_PromiseRP_iff`, `Cslib.Complexity.compl_mem_PromiseCoRP_iff`:
  complement relations between `PromiseRP` and `PromiseCoRP`.
* `Cslib.Complexity.PromiseP_subset_PromiseRP`, `Cslib.Complexity.PromiseP_subset_PromiseCoRP`,
  `Cslib.Complexity.PromiseP_subset_PromiseBPP`.
* `Cslib.Complexity.probability_sampleList_verifier`: acceptance probability of sampling a uniform
  random word for a seeded verifier.
* `Cslib.Complexity.mem_PromiseBPP_iff_exists_isPPTOn`,
  `Cslib.Complexity.mem_PromiseRP_iff_exists_isPPTOn`,
  `Cslib.Complexity.mem_PromiseCoRP_iff_exists_isPPTOn`: characterizations by uniform strict PPT
  programs.
* `Cslib.Complexity.PromiseProblem.PolyTimeReducible.mem_PromiseBPP`,
  `Cslib.Complexity.PromiseProblem.PolyTimeReducible.mem_PromiseRP`,
  `Cslib.Complexity.PromiseProblem.PolyTimeReducible.mem_PromiseCoRP`: closure of probabilistic
  promise classes under deterministic polynomial-time reductions.

## References

* [O. Goldreich, *On promise problems: a survey*][Goldreich2006]
-/

@[expose] public section

namespace Cslib.Complexity

open Turing.MultiTapeTM Probability PromiseProblem

section PromiseProbabilistic

variable {α : Type} {enc : α ↪ List Bool} {Q : PromiseProblem α} {A : Set α}

/-- A promise problem is in `PromiseCoRP` when a polynomial-time verifier accepts every random
string on every yes-instance and rejects at least half on every no-instance. -/
theorem mem_PromiseCoRP_iff : Q ∈ PromiseCoRP enc ↔
    ∃ (p : Polynomial ℕ) (V : α × List Bool → Bool),
      ComputableInPolyTime V (encPair enc encBits) encBool ∧
      (∀ a ∈ Q.yes, ∀ r : Fin (p.eval (enc a).length) → Bool, V (a, List.ofFn r) = true) ∧
      ∀ a ∈ Q.no, 2 ^ p.eval (enc a).length ≤
        2 * (Finset.univ.filter fun r : Fin (p.eval (enc a).length) → Bool =>
          V (a, List.ofFn r) = false).card := by
  constructor
  · rintro ⟨p, V, hV, h⟩
    refine ⟨p, fun x => !V x, ComputableInPolyTime.bool_not.comp hV,
      fun a ha r => by simp [(h a).2 ha r], fun a ha => by simpa using (h a).1 ha⟩
  · rintro ⟨p, V, hV, hyes, hno⟩
    refine ⟨p, fun x => !V x, ComputableInPolyTime.bool_not.comp hV,
      fun a => ⟨fun ha => by simpa using hno a ha, fun ha r => by simp [hyes a ha r]⟩⟩

/-- Every promise problem separated by a language in `BPP` is in `PromiseBPP`. -/
theorem promiseClass_BPP_subset_PromiseBPP : promiseClass (BPP enc) ⊆ PromiseBPP enc := by
  rintro Q ⟨B, ⟨p, V, hV, hB⟩, hyes, hno⟩
  exact ⟨p, V, hV, fun a => ⟨fun ha => (hB a).1 (hyes ha),
    fun ha => (hB a).2 (Set.disjoint_right.1 hno ha)⟩⟩

/-- Every promise problem separated by a language in `RP` is in `PromiseRP`. -/
theorem promiseClass_RP_subset_PromiseRP : promiseClass (RP enc) ⊆ PromiseRP enc := by
  rintro Q ⟨B, ⟨p, V, hV, hB⟩, hyes, hno⟩
  exact ⟨p, V, hV, fun a => ⟨fun ha => (hB a).1 (hyes ha),
    fun ha => (hB a).2 (Set.disjoint_right.1 hno ha)⟩⟩

/-- Every promise problem separated by a language in `coRP` is in `PromiseCoRP`. -/
theorem promiseClass_coRP_subset_PromiseCoRP : promiseClass (coRP enc) ⊆ PromiseCoRP enc := by
  rintro Q ⟨B, hB, hyes, hno⟩
  exact promiseClass_RP_subset_PromiseRP ⟨Bᶜ, hB,
    Set.subset_compl_iff_disjoint_left.2 hno, Set.disjoint_compl_left_iff_subset.2 hyes⟩

/-- A promise problem's complement is in `PromiseRP` exactly when the problem is in
`PromiseCoRP`. -/
theorem compl_mem_PromiseRP_iff : Qᶜ ∈ PromiseRP enc ↔ Q ∈ PromiseCoRP enc :=
  Iff.rfl

/-- A promise problem's complement is in `PromiseCoRP` exactly when the problem is in
`PromiseRP`. -/
theorem compl_mem_PromiseCoRP_iff : Qᶜ ∈ PromiseCoRP enc ↔ Q ∈ PromiseRP enc := by
  rw [← compl_mem_PromiseRP_iff, compl_compl]

/-- Every promise problem in `PromiseP` is in `PromiseRP`. -/
theorem PromiseP_subset_PromiseRP : PromiseP enc ⊆ PromiseRP enc :=
  (promiseClass_mono P_subset_RP).trans promiseClass_RP_subset_PromiseRP

/-- Every promise problem in `PromiseP` is in `PromiseCoRP`. -/
theorem PromiseP_subset_PromiseCoRP : PromiseP enc ⊆ PromiseCoRP enc :=
  (promiseClass_mono P_subset_coRP).trans promiseClass_coRP_subset_PromiseCoRP

/-- Every promise problem in `PromiseP` is in `PromiseBPP`. -/
theorem PromiseP_subset_PromiseBPP : PromiseP enc ⊆ PromiseBPP enc :=
  (promiseClass_mono P_subset_BPP).trans promiseClass_BPP_subset_PromiseBPP

/-- The program sampling a random string for a seeded verifier accepts with the accepted
fraction of the strings. -/
theorem probability_sampleList_verifier (V : α × List Bool → Bool) (a : α) (n : ℕ) :
    Pr[(fun w => V (a, w)) <$> BitString.sampleList n] = (acceptCount V a n : ℝ) / 2 ^ n := by
  simp only [ProbComp.eval_map, BitString.eval_sampleList]
  exact uniformList_acceptCount_toReal V a n

/-- **Probabilistic-program characterization of `PromiseBPP`**: a promise problem is in
`PromiseBPP` exactly when a uniform strict PPT Boolean program accepts every yes-instance with
probability at least `2 / 3` and rejects every no-instance with probability at least `2 / 3`. -/
theorem mem_PromiseBPP_iff_exists_isPPTOn : Q ∈ PromiseBPP enc ↔
    ∃ M : α → ProbComp Bool, IsPPTOn enc encBool M ∧
      (∀ a ∈ Q.yes, 2 / 3 ≤ Pr[M a]) ∧
      ∀ a ∈ Q.no, 2 / 3 ≤ Pr[Bool.not <$> M a] := by
  rw [mem_PromiseBPP_iff]
  constructor
  · rintro ⟨p, V, hV, hQ⟩
    refine ⟨fun a => (fun w => V (a, w)) <$> BitString.sampleList (p.eval (enc a).length),
      IsPPTOn.of_seeded ((ComputableInPolyTime.unary_eval p).comp
        (ComputableInPolyTime.encoding_length enc)) hV,
      fun a ha => ?_, fun a ha => ?_⟩
    · rw [probability_sampleList_verifier, le_div_iff₀ (by positivity)]
      have h : (2 : ℝ) * 2 ^ p.eval (enc a).length ≤
          3 * (acceptCount V a (p.eval (enc a).length) : ℝ) := by
        exact_mod_cast (hQ a).1 ha
      linarith
    · rw [Functor.map_map, probability_sampleList_verifier (V := fun x => !V x),
        le_div_iff₀ (by positivity)]
      have h : (2 : ℝ) * 2 ^ p.eval (enc a).length ≤
          3 * (acceptCount (fun x => !V x) a (p.eval (enc a).length) : ℝ) := by
        simpa only [acceptCount, Bool.not_eq_true'] using
          (by exact_mod_cast (hQ a).2 ha : (2 : ℝ) * 2 ^ p.eval (enc a).length ≤ _)
      linarith
  · rintro ⟨M, hM, hyes, hno⟩
    obtain ⟨c, d, evalM, hevalM, hlaw⟩ := hM.exists_seeded_evaluator
    refine ⟨Polynomial.C c * (Polynomial.X + 1) ^ d, fun x => evalM x.1 x.2, .of_tidy hevalM,
      fun a => ⟨fun ha => ?_, fun ha => ?_⟩⟩
    · have hp : (Polynomial.C c * (Polynomial.X + 1) ^ d).eval (enc a).length =
          c * ((enc a).length + 1) ^ d := by simp
      dsimp only [BoundedErrorAt]
      rw [hp]
      have hprob := hyes a ha
      rw [hlaw a, uniformList_acceptCount_toReal (V := fun x => evalM x.1 x.2),
        le_div_iff₀ (by positivity)] at hprob
      have h3 : (2 : ℝ) * 2 ^ (c * ((enc a).length + 1) ^ d) ≤
          3 * (acceptCount (fun x => evalM x.1 x.2) a (c * ((enc a).length + 1) ^ d) : ℝ) := by
        linarith
      exact_mod_cast h3
    · have hp : (Polynomial.C c * (Polynomial.X + 1) ^ d).eval (enc a).length =
          c * ((enc a).length + 1) ^ d := by simp
      dsimp only [BoundedErrorAt]
      rw [hp]
      have hprob := hno a ha
      have hmap : ProbComp.eval (Bool.not <$> M a) =
          (BitString.uniformList (c * ((enc a).length + 1) ^ d)).map (fun w => !evalM a w) := by
        rw [ProbComp.eval_map, hlaw a, PMF.map_comp]
        rfl
      rw [hmap, uniformList_acceptCount_toReal (V := fun x => !evalM x.1 x.2),
        le_div_iff₀ (by positivity)] at hprob
      have h3 : (2 : ℝ) * 2 ^ (c * ((enc a).length + 1) ^ d) ≤
          3 * (acceptCount (fun x => !evalM x.1 x.2) a (c * ((enc a).length + 1) ^ d) : ℝ) := by
        linarith
      simpa only [acceptCount, Bool.not_eq_true'] using (by exact_mod_cast h3 :
        2 * 2 ^ (c * ((enc a).length + 1) ^ d) ≤
          3 * acceptCount (fun x => !evalM x.1 x.2) a (c * ((enc a).length + 1) ^ d))

/-- **Probabilistic-program characterization of `PromiseRP`**: a promise problem is in `PromiseRP`
exactly when a uniform strict PPT Boolean program accepts every yes-instance with probability at
least `1 / 2` and never accepts a no-instance. -/
theorem mem_PromiseRP_iff_exists_isPPTOn : Q ∈ PromiseRP enc ↔
    ∃ M : α → ProbComp Bool, IsPPTOn enc encBool M ∧
      (∀ a ∈ Q.yes, 1 / 2 ≤ Pr[M a]) ∧
      ∀ a ∈ Q.no, true ∉ (ProbComp.eval (M a)).support := by
  rw [mem_PromiseRP_iff]
  constructor
  · rintro ⟨p, V, hV, hQ⟩
    refine ⟨fun a => (fun w => V (a, w)) <$> BitString.sampleList (p.eval (enc a).length),
      IsPPTOn.of_seeded ((ComputableInPolyTime.unary_eval p).comp
        (ComputableInPolyTime.encoding_length enc)) hV,
      fun a ha => ?_, fun a ha hmem => ?_⟩
    · rw [probability_sampleList_verifier, le_div_iff₀ (by positivity)]
      have h : (2 : ℝ) ^ p.eval (enc a).length ≤
          2 * (acceptCount V a (p.eval (enc a).length) : ℝ) := by
        exact_mod_cast (hQ a).1 ha
      linarith
    · simp only [ProbComp.eval_map, BitString.eval_sampleList,
        PMF.mem_support_map_iff, BitString.mem_support_uniformList_iff] at hmem
      obtain ⟨w, hw, hVw⟩ := hmem
      have := hQ.exists_certificate.2 a ha w hw
      rw [this] at hVw
      exact Bool.noConfusion hVw
  · rintro ⟨M, hM, hyes, hno⟩
    obtain ⟨c, d, evalM, hevalM, hsupp, hlaw⟩ := hM.exists_total_seeded_evaluator
    refine ⟨Polynomial.C c * (Polynomial.X + 1) ^ d, fun x => evalM x.1 x.2, .of_tidy hevalM,
      fun a => ⟨fun ha => ?_, fun ha r => ?_⟩⟩
    · have hp : (Polynomial.C c * (Polynomial.X + 1) ^ d).eval (enc a).length =
          c * ((enc a).length + 1) ^ d := by simp
      rw [hp]
      have hprob := hyes a ha
      rw [hlaw a _ le_rfl, uniformList_acceptCount_toReal (V := fun x => evalM x.1 x.2),
        le_div_iff₀ (by positivity)] at hprob
      have h2 : (2 : ℝ) ^ (c * ((enc a).length + 1) ^ d) ≤
          2 * (acceptCount (fun x => evalM x.1 x.2) a (c * ((enc a).length + 1) ^ d) : ℝ) := by
        linarith
      exact_mod_cast h2
    · rw [← Bool.not_eq_true]
      intro htrue
      exact hno a ha (htrue ▸ hsupp a (List.ofFn r))

/-- **Probabilistic-program characterization of `PromiseCoRP`**: a promise problem is in
`PromiseCoRP` exactly when a uniform strict PPT Boolean program never rejects a yes-instance and
rejects every no-instance with probability at least `1 / 2`. -/
theorem mem_PromiseCoRP_iff_exists_isPPTOn : Q ∈ PromiseCoRP enc ↔
    ∃ M : α → ProbComp Bool, IsPPTOn enc encBool M ∧
      (∀ a ∈ Q.yes, false ∉ (ProbComp.eval (M a)).support) ∧
      ∀ a ∈ Q.no, 1 / 2 ≤ Pr[Bool.not <$> M a] := by
  rw [PromiseCoRP, Set.mem_ofPred_eq, mem_PromiseRP_iff_exists_isPPTOn]
  constructor
  · rintro ⟨M, hM, hyes, hno⟩
    refine ⟨fun a => Bool.not <$> M a,
      hM.map_with (ComputableInPolyTime.bool_not.comp (.snd enc encBool)),
      fun a ha hmem => ?_, fun a ha => ?_⟩
    · simp only [ProbComp.eval_map, PMF.mem_support_map_iff,
        Bool.not_eq_false'] at hmem
      obtain ⟨b, hb, rfl⟩ := hmem
      exact hno a ha hb
    · have h : Bool.not <$> (Bool.not <$> M a) = M a := by simp
      rw [h]
      exact hyes a ha
  · rintro ⟨M, hM, hyes, hno⟩
    refine ⟨fun a => Bool.not <$> M a,
      hM.map_with (ComputableInPolyTime.bool_not.comp (.snd enc encBool)),
      fun a ha => hno a ha, fun a ha hmem => ?_⟩
    simp only [ProbComp.eval_map, PMF.mem_support_map_iff,
      Bool.not_eq_true'] at hmem
    obtain ⟨b, hb, rfl⟩ := hmem
    exact hyes a ha hb

end PromiseProbabilistic

namespace PromiseProblem

variable {α β : Type} {encA : α ↪ List Bool} {encB : β ↪ List Bool}
  {X : PromiseProblem α} {Y : PromiseProblem β}

/-- **`PromiseBPP` is closed under polynomial-time reductions.** -/
theorem PolyTimeReducible.mem_PromiseBPP (h : PolyTimeReducible encA encB X Y)
    (hY : Y ∈ PromiseBPP encB) : X ∈ PromiseBPP encA := by
  obtain ⟨f, hf, hfyes, hfno⟩ := h
  obtain ⟨M, hM, hyes, hno⟩ := mem_PromiseBPP_iff_exists_isPPTOn.mp hY
  exact mem_PromiseBPP_iff_exists_isPPTOn.mpr
    ⟨fun a => M (f a), hM.preprocess hf, fun a ha => hyes (f a) (hfyes ha),
      fun a ha => hno (f a) (hfno ha)⟩

/-- **`PromiseRP` is closed under polynomial-time reductions.** -/
theorem PolyTimeReducible.mem_PromiseRP (h : PolyTimeReducible encA encB X Y)
    (hY : Y ∈ PromiseRP encB) : X ∈ PromiseRP encA := by
  obtain ⟨f, hf, hfyes, hfno⟩ := h
  obtain ⟨M, hM, hyes, hno⟩ := mem_PromiseRP_iff_exists_isPPTOn.mp hY
  exact mem_PromiseRP_iff_exists_isPPTOn.mpr
    ⟨fun a => M (f a), hM.preprocess hf, fun a ha => hyes (f a) (hfyes ha),
      fun a ha => hno (f a) (hfno ha)⟩

/-- **`PromiseCoRP` is closed under polynomial-time reductions.** -/
theorem PolyTimeReducible.mem_PromiseCoRP (h : PolyTimeReducible encA encB X Y)
    (hY : Y ∈ PromiseCoRP encB) : X ∈ PromiseCoRP encA := by
  obtain ⟨f, hf, hfyes, hfno⟩ := h
  obtain ⟨M, hM, hyes, hno⟩ := mem_PromiseCoRP_iff_exists_isPPTOn.mp hY
  exact mem_PromiseCoRP_iff_exists_isPPTOn.mpr
    ⟨fun a => M (f a), hM.preprocess hf, fun a ha => hyes (f a) (hfyes ha),
      fun a ha => hno (f a) (hfno ha)⟩

end PromiseProblem

end Cslib.Complexity
