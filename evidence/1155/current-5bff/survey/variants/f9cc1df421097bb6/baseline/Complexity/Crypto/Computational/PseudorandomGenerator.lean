/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
public import Complexity.Crypto.Computational.Basic
public import Complexity.Crypto.Primitives.PRG.Game
public import Complexity.Foundations.Data.BitString.List
public import Complexity.Languages.Probabilistic.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Probability.PMF.Map
import Complexity.Tactic.PPT

/-!
# Uniform computational pseudorandom generators

A generator is ordinary functional code on lists of bits. Its finite family uses the existing
`PRG.Generator` API on `BitString n` and `BitString (length n)`. The output-length condition makes
this representation exact: no padding or truncation enters the real experiment. Admissible finite
tests must be realized by one uniform PPT program on every parameter and valid output word.

Security is the existing `PRG.Family.Secure`, with the seed length supplied as the parameter in
both experiments. Its equivalence to computational indistinguishability lets reductions use
list programs without manipulating dependent finite types. The real and ideal experiments below
are executable fair-bit programs; their efficiency follows from the generator and length routine.

## Main definitions

* `Cslib.Crypto.PRG.wordFamily`: the finite family represented by a word function.
* `Cslib.Crypto.IsPPTBitStringTest`: uniform realization of finite tests on valid words.
* `Cslib.Crypto.PseudorandomGenerator`: efficient generation, exact length, stretch and security.

## Main results

* `Cslib.Crypto.PRG.wordFamily_secure_iff`: equivalence to word-ensemble indistinguishability.
* `Cslib.Crypto.PseudorandomGenerator.of_indistinguishable`: prove security with word programs.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09], Section 9.2.3.

Adapted from Crypto/Computational/PseudorandomGenerator.lean on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`, retaining the pinned finite PRG API.
-/

@[expose] public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM

/-- The output distribution of a word function on a uniform seed. -/
noncomputable def generatorEnsemble (generator : List Bool → List Bool) (n : ℕ) :
    PMF (List Bool) := (BitString.uniformList n).map generator

/-- Length-dependent postprocessing can use the sampled seed length as its parameter. -/
theorem generatorEnsemble_postprocess (generator : List Bool → List Bool)
    (f : ℕ → List Bool → List Bool) (n : ℕ) :
    generatorEnsemble (fun seed => f seed.length (generator seed)) n =
      (generatorEnsemble generator n).map (f n) := by
  simp only [generatorEnsemble, PMF.map_comp]
  apply Probability.PMF.map_congr_on_support
  intro seed hseed
  simp only [Function.comp_def, BitString.length_of_mem_support_uniformList hseed]

/-- The finite family represented by a word function. An exact output-length hypothesis is
required by the experiment and security bridges below. -/
def PRG.wordFamily (generator : List Bool → List Bool) (length : ℕ → ℕ) :
    PRG.Family BitString (fun n => BitString (length n)) :=
  fun n => ⟨fun seed => BitString.ofList (length n) (generator (List.ofFn seed))⟩

/-- One uniform program realizes the entire finite test family on its valid output words.
Its behavior on other word lengths is unrestricted, but its machine clock bounds every input. -/
def IsPPTBitStringTest {length : ℕ → ℕ}
    (test : ∀ n, PRG.Adversary (BitString (length n))) : Prop :=
  ∃ program : Distinguisher, IsPPT encBool program ∧
    ∀ n bits, ProbComp.eval (program n (List.ofFn bits)) = test n bits

/-- Exact output lengths identify finite generated samples with the original word distribution. -/
theorem generatorEnsemble_eq_outputDist {generator : List Bool → List Bool} {length : ℕ → ℕ}
    (hlen : ∀ word, (generator word).length = length word.length) (n : ℕ) :
    generatorEnsemble generator n = ((PRG.wordFamily generator length n).outputDist).map
      List.ofFn := by
  simp only [generatorEnsemble, BitString.uniformList, PRG.wordFamily,
    PRG.Generator.outputDist, PRG.Generator.coe_mk, PMF.map_comp]
  congr 1
  funext seed
  exact (BitString.ofFn_ofList (by simpa using hlen (List.ofFn seed))).symm

/-- The finite and word experiments coincide for every uniformly realized test. -/
theorem PRG.wordFamily_realExperiment {generator : List Bool → List Bool} {length : ℕ → ℕ}
    (hlen : ∀ word, (generator word).length = length word.length)
    (adversary : Distinguisher) (n : ℕ) :
    (wordFamily generator length n).realExperiment
      (fun bits => ProbComp.eval (adversary n (List.ofFn bits))) =
        distinguishingGame (generatorEnsemble generator n) (adversary n) := by
  rw [generatorEnsemble_eq_outputDist hlen]
  simp only [distinguishingGame, PMF.monad_bind_eq_bind, PMF.bind_map, Function.comp_def,
    PRG.Generator.realExperiment]

/-- The ideal finite test sees exactly the uniform word of the declared output length. -/
theorem PRG.wordFamily_idealExperiment (length : ℕ → ℕ) (adversary : Distinguisher) (n : ℕ) :
    Generator.idealExperiment
      (fun bits : BitString (length n) => ProbComp.eval (adversary n (List.ofFn bits))) =
        distinguishingGame (BitString.uniformList (length n)) (adversary n) := by
  simp only [Generator.idealExperiment, distinguishingGame, PMF.monad_bind_eq_bind,
    BitString.uniformList,
    PMF.bind_map, Function.comp_def]

/-- Finite-family security against uniformly realizable tests is exactly computational
indistinguishability of the generated and uniform word ensembles. -/
theorem PRG.wordFamily_secure_iff {generator : List Bool → List Bool} {length : ℕ → ℕ}
    (hlen : ∀ word, (generator word).length = length word.length) :
    (wordFamily generator length).Secure IsPPTBitStringTest ↔
      ComputationallyIndistinguishable (generatorEnsemble generator)
        (fun n => BitString.uniformList (length n)) := by
  rw [Family.secure_iff_indistinguishable]
  constructor
  · intro h adversary ha
    simpa only [wordFamily_realExperiment hlen, wordFamily_idealExperiment] using
      h (fun n bits => ProbComp.eval (adversary n (List.ofFn bits)))
        ⟨adversary, ha, fun _ _ => rfl⟩
  · rintro h test ⟨adversary, ha, heq⟩
    have heq := funext fun n => funext (heq n)
    subst test
    simpa only [wordFamily_realExperiment hlen, wordFamily_idealExperiment] using h adversary ha

/-- Sample a uniform seed, evaluate the generator, and run the distinguisher. -/
noncomputable def prgRealGame (generator : List Bool → List Bool)
    (adversary : Distinguisher) (n : ℕ) : ProbComp Bool := do
  let seed ← BitString.sampleList n
  adversary n (generator seed)

/-- Sample a uniform word at the declared length and run the distinguisher. -/
noncomputable def prgIdealGame (length : ℕ → ℕ) (adversary : Distinguisher) (n : ℕ) :
    ProbComp Bool := do
  let word ← BitString.sampleList (length n)
  adversary n word

/-- The real program denotes the generated-word experiment. -/
@[simp] theorem eval_prgRealGame (generator : List Bool → List Bool)
    (adversary : Distinguisher) (n : ℕ) :
    ProbComp.eval (prgRealGame generator adversary n) =
      distinguishingGame (generatorEnsemble generator n) (adversary n) := by
  simp [prgRealGame, distinguishingGame, generatorEnsemble, PMF.bind_map, Function.comp_def]

/-- The ideal program denotes the uniform-word experiment. -/
@[simp] theorem eval_prgIdealGame (length : ℕ → ℕ) (adversary : Distinguisher) (n : ℕ) :
    ProbComp.eval (prgIdealGame length adversary n) =
      distinguishingGame (BitString.uniformList (length n)) (adversary n) := by
  simp [prgIdealGame, distinguishingGame]

/-- The real experiment is an efficient program when its generator and distinguisher are. -/
@[program_certificate]
theorem isPPTOn_prgRealGame {generator : List Bool → List Bool} {adversary : Distinguisher}
    (hg : ComputableInPolyTime generator encBits encBits) (ha : IsPPT encBool adversary) :
    IsPPTOn encUnary encBool (prgRealGame generator adversary) := by
  unfold prgRealGame
  ppt

/-- The ideal experiment is efficient when its length routine and distinguisher are. -/
@[program_certificate]
theorem isPPTOn_prgIdealGame {length : ℕ → ℕ} {adversary : Distinguisher}
    (hl : ComputableInPolyTime length encUnary encUnary) (ha : IsPPT encBool adversary) :
    IsPPTOn encUnary encBool (prgIdealGame length adversary) := by
  unfold prgIdealGame
  ppt

/-- A plain polynomial-time stretching generator, secure in the existing finite-family API. -/
structure PseudorandomGenerator (generator : List Bool → List Bool) (length : ℕ → ℕ) : Prop where
  /-- One deterministic polynomial-time machine evaluates the generator. -/
  polyTime : ComputableInPolyTime generator encBits encBits
  /-- The output length depends only on the seed length. -/
  length_eq : ∀ word, (generator word).length = length word.length
  /-- Every seed length is strictly expanded. -/
  stretch : ∀ n, n < length n
  /-- The finite family is secure against uniformly realizable PPT tests. -/
  secure : (PRG.wordFamily generator length).Secure IsPPTBitStringTest

/-- Establish a uniform PRG with an ordinary word-ensemble security argument. -/
theorem PseudorandomGenerator.of_indistinguishable
    {generator : List Bool → List Bool} {length : ℕ → ℕ}
    (hg : ComputableInPolyTime generator encBits encBits)
    (hlen : ∀ word, (generator word).length = length word.length)
    (hstretch : ∀ n, n < length n)
    (hsecure : ComputationallyIndistinguishable (generatorEnsemble generator)
      (fun n => BitString.uniformList (length n))) : PseudorandomGenerator generator length := by
  have hg := hg.tidy
  exact ⟨.of_tidy hg, hlen, hstretch, (PRG.wordFamily_secure_iff hlen).mpr hsecure⟩

/-- The generated words are computationally indistinguishable from uniform words. -/
theorem PseudorandomGenerator.indistinguishable
    {generator : List Bool → List Bool} {length : ℕ → ℕ}
    (h : PseudorandomGenerator generator length) :
    ComputationallyIndistinguishable (generatorEnsemble generator)
      (fun n => BitString.uniformList (length n)) :=
  (PRG.wordFamily_secure_iff h.length_eq).mp h.secure

/-- Compute the expansion length by evaluating the generator on a canonical seed. No separate
efficiency or security assumption on the length function is needed. -/
theorem PRG.polyTime_length
    {generator : List Bool → List Bool} {length : ℕ → ℕ}
    (hg : ComputableInPolyTime generator encBits encBits)
    (hlen : ∀ word, (generator word).length = length word.length) :
    ComputableInPolyTime length encUnary encUnary := by
  have hc : ComputableInPolyTime
      (fun n => (generator (List.replicate n false)).length) encUnary encUnary := by fun_prop
  simpa only [hlen, List.length_replicate] using hc

/-- A secure generator has an efficient unary expansion-length routine. -/
@[fun_prop]
theorem PseudorandomGenerator.polyTime_length
    {generator : List Bool → List Bool} {length : ℕ → ℕ}
    (h : PseudorandomGenerator generator length) :
    ComputableInPolyTime length encUnary encUnary :=
  (PRG.polyTime_length h.polyTime h.length_eq)

/-- The declared expansion is bounded by a polynomial in the seed length. -/
theorem PseudorandomGenerator.length_le {generator : List Bool → List Bool} {length : ℕ → ℕ}
    (h : PseudorandomGenerator generator length) :
    ∃ c d : ℕ, ∀ n, length n ≤ c * (n + 1) ^ d := by
  obtain ⟨c, d, hbound⟩ := h.polyTime.polyBounded_length.exists_le
  refine ⟨c, d, fun n => ?_⟩
  simpa [h.length_eq] using hbound (List.replicate n false)

end Cslib.Crypto
