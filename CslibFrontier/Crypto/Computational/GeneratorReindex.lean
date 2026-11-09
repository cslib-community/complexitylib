/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.GeneratorPadding
public import CslibFrontier.Crypto.Computational.Nonuniform.Basic
public import CslibFrontier.Crypto.Computational.PseudorandomGenerator
public import Mathlib.Data.Nat.Find
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Search
import CslibFrontier.Computability.Probabilistic.PPT.Capture
import CslibFrontier.Computability.Probabilistic.Sampling
import CslibFrontier.Crypto.Computational.UniformChoice
import CslibFrontier.Crypto.Negligible.Basic
import CslibFrontier.Tactic.PolyTime.Init

/-!
# Extending an expanding family to every seed length

Choose the largest parameter whose seed fits the input, run that family member on a prefix,
and retain the unused suffix. A finite initial range uses a trivial one-bit extension.
The schedule need not be monotone. Bounded search is efficient, and adjacent parameters give
the polynomial relation needed to preserve negligible decay.

Security uses `ComputationallyIndistinguishable.uniform_bound`: the padding test receives the
prospective input length as an ordinary index, and one negligible bound covers all relevant
lengths. No nonuniform choice of a bad length is supplied to the reduction.

## Main definitions

* `Cslib.Crypto.GeneratorReindex.parameter`: bounded search for the greatest fitting parameter.
* `Cslib.Crypto.GeneratorReindex.generate`: prefix generation with the unused suffix preserved.

## Main results

* `Cslib.Crypto.GeneratorReindex.parameter_apply_of_strictMono`: exact parameter recovery on the
  range of a strictly monotone schedule.
* `Cslib.Crypto.GeneratorReindex.isPolyTime_generate`: uniform machine-backed efficiency.
* `Cslib.Crypto.GeneratorReindex.indistinguishable`,
  `Cslib.Crypto.GeneratorReindex.nonuniformIndistinguishable`: extending a secure family preserves
  uniform and nonuniform computational indistinguishability at every seed length.
* `Cslib.Crypto.GeneratorReindex.pseudorandomGenerator`,
  `Cslib.Crypto.GeneratorReindex.nonuniformPRG`: one-bit stretch at every seed length.

## References

This completes the seed-length convention for the construction in
[T. Holenstein, *Pseudorandom Generators from One-Way Functions*][Holenstein2006], Section 5.

Adapted from Crypto/Computational/GeneratorReindex.lean
on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`, using typed machine certificates and the
nonnegative game API.
-/

@[expose] public section

namespace Cslib.Crypto.GeneratorReindex

open Probability BitString Filter Turing.MultiTapeTM

/-- The greatest parameter at most `size` whose prescribed seed fits, or zero when none fits. -/
def parameter (length : ℕ → ℕ) (size : ℕ) : ℕ :=
  Nat.findGreatest (fun n => length n ≤ size) size

/-- Searching an efficient schedule up to an efficient unary input size is polynomial-time. -/
@[program_certificate]
theorem isPolyTime_parameter {α : Type} {input : α ↪ List Bool} {length : ℕ → ℕ} {size : α → ℕ}
    (hlength : ComputableInPolyTime length encUnary encUnary)
    (hsize : ComputableInPolyTime size input encUnary) :
    ComputableInPolyTime (fun a => parameter length (size a)) input encUnary :=
  hsize.findGreatest ((hlength.comp (.snd input encUnary)).unary_le'
    (hsize.comp (.fst input encUnary)))

/-- The bounded search never returns a parameter above its input size. -/
theorem parameter_le (length : ℕ → ℕ) (size : ℕ) : parameter length size ≤ size :=
  Nat.findGreatest_le _

/-- Once the zeroth seed fits, the selected seed fits too. -/
theorem parameter_fits {length : ℕ → ℕ} {size : ℕ} (hsize : length 0 ≤ size) :
    length (parameter length size) ≤ size :=
  Nat.findGreatest_spec (P := fun n => length n ≤ size) (Nat.zero_le _) hsize

/-- For a strictly monotone schedule `length`, `parameter length (length n) = n`. -/
@[simp]
theorem parameter_apply_of_strictMono {length : ℕ → ℕ} (hmono : StrictMono length) (n : ℕ) :
    parameter length (length n) = n := by
  apply le_antisymm
  · by_contra! hlt
    have hspec : length (parameter length (length n)) ≤ length n :=
      parameter_fits (hmono.monotone (Nat.zero_le n))
    exact (hmono hlt).not_ge hspec
  · exact Nat.le_findGreatest (hmono.id_le n) le_rfl

/-- The next parameter's seed is too large, even when the schedule is not monotone. -/
theorem lt_length_succ_parameter {length : ℕ → ℕ} (hge : ∀ n, n + 1 ≤ length n) (size : ℕ) :
    size < length (parameter length size + 1) := by
  have hle := parameter_le length size
  by_cases hlt : parameter length size < size
  · exact Nat.lt_of_not_ge (Nat.findGreatest_is_greatest (P := fun n => length n ≤ size)
      (Nat.lt_succ_self (parameter length size)) (by lia : parameter length size + 1 ≤ size))
  · have := hge (parameter length size + 1)
    lia

/-- Every fixed parameter eventually fits, so the selected parameter tends to infinity. -/
theorem parameter_tendsto (length : ℕ → ℕ) : Tendsto (parameter length) atTop atTop := by
  apply tendsto_atTop.2
  intro n
  filter_upwards [eventually_ge_atTop (max n (length n))] with size hsize
  exact Nat.le_findGreatest (by lia : n ≤ size) (by lia : length n ≤ size)

/-- Search for a family member that fits, then preserve the remaining seed bits as padding. -/
def generate (length : ℕ → ℕ) (generator : ℕ → List Bool → List Bool)
    (seed : List Bool) : List Bool :=
  if length 0 ≤ seed.length then
    let n := parameter length seed.length
    GeneratorPadding.generate (length n) seed.length (generator n) seed
  else seed ++ [false]

/-- Generation composes bounded search, the supplied family, and padding. -/
theorem isPolyTime_generate {length : ℕ → ℕ} {generator : ℕ → List Bool → List Bool}
    (hlength : ComputableInPolyTime length encUnary encUnary)
    (hgenerator : ComputableInPolyTime (fun a => generator a.1 a.2)
      (encPair encUnary encBits) encBits) :
    ComputableInPolyTime (generate length generator) encBits encBits := by
  have hparameter := isPolyTime_parameter hlength .length_bits
  have hgen := ((hparameter.comp (.fst encBits encBits)).prod (.snd encBits encBits)).trans
    hgenerator
  have hpadded := GeneratorPadding.isPolyTime_generate (α := List Bool) (input := encBits)
    (generator := fun seed => generator (parameter length seed.length))
    (hlength.comp hparameter) .length_bits hgen .id'
  unfold generate
  simpa only [decide_eq_true_eq, Function.comp_def] using
    ((ComputableInPolyTime.const (length 0)).unary_le' .length_bits).ite hpadded
      (ComputableInPolyTime.bitsAppend .id' (.const [false]))

/-- Every input is expanded by exactly one bit, including the finite initial range. -/
theorem length_generate {length : ℕ → ℕ} {generator : ℕ → List Bool → List Bool}
    (houtput : ∀ n seed, seed.length = length n → (generator n seed).length = length n + 1)
    (seed : List Bool) : (generate length generator seed).length = seed.length + 1 := by
  unfold generate
  split_ifs with hfits
  · exact GeneratorPadding.length_generate (parameter_fits hfits)
      (fun word hword => by rw [houtput _ _ hword]; lia) rfl
  · simp

/-- At a fixed seed length, the reindexed ensemble is exactly the corresponding padded family. -/
theorem generate_distribution (length : ℕ → ℕ) (generator : ℕ → List Bool → List Bool)
    {size : ℕ} (hsize : length 0 ≤ size) :
    generatorEnsemble (generate length generator) size =
      (uniformList size).map (GeneratorPadding.generate (length (parameter length size)) size
        (generator (parameter length size))) := by
  simp only [generatorEnsemble, PMF.map]
  apply PMF.bind_congr_on_support
  intro seed hseed
  simp only [Function.comp_def, generate, length_of_mem_support_uniformList hseed,
    ite_eq_left hsize]

/-- Extending a uniformly efficient secure family preserves uniform security at every seed
length. A single calibrated reduction controls every padding length in the polynomial range. -/
theorem indistinguishable {length : ℕ → ℕ} {generator : ℕ → List Bool → List Bool}
    (hlength : ComputableInPolyTime length encUnary encUnary)
    (hge : ∀ n, n + 1 ≤ length n)
    (hgenerator : ComputableInPolyTime (fun a => generator a.1 a.2)
      (encPair encUnary encBits) encBits)
    (hsecure : ComputationallyIndistinguishable
      (fun n => (uniformList (length n)).map (generator n))
      (fun n => uniformList (length n + 1))) :
    ComputationallyIndistinguishable (generatorEnsemble (generate length generator))
      (fun n => uniformList (n + 1)) := by
  intro adversary hadversary
  let real : ℕ → ProbComp (List Bool) := fun n => generator n <$> BitString.sampleList (length n)
  let ideal : ℕ → ProbComp (List Bool) := fun n => BitString.sampleList (length n + 1)
  have hreal : IsPPTOn encUnary encBits real := hlength.sampleList.map_with hgenerator
  have hideal : IsPPTOn encUnary encBits ideal := (hlength.unary_add' (.const 1)).sampleList
  have hfamily : ComputationallyIndistinguishable
      (fun n => ProbComp.eval (real n)) (fun n => ProbComp.eval (ideal n)) := by
    simpa only [real, ideal, ProbComp.eval_map, BitString.eval_sampleList] using hsecure
  let test := fun n size => GeneratorPadding.test (length n) size (adversary size)
  let eIn := encPair (encPair encUnary encUnary) encBits
  have hadv' := hadversary.on.preprocess
    ((ComputableInPolyTime.fst eIn encBits).fst'.snd'.prod (.snd eIn encBits))
  have htest : IsPPTOn eIn encBool (fun a => test a.1.1 a.1.2 a.2) :=
    GeneratorPadding.isPPTOn_test (hlength.comp (ComputableInPolyTime.fst _ _).fst')
      (ComputableInPolyTime.fst _ _).snd' hadv' (.snd _ encBits)
  obtain ⟨ε, hε, hbound⟩ := hfamily.uniform_bound hreal hideal
    (bound := fun n => length (n + 1)) (hlength.comp .unary_succ) test htest
  have hdecay := hε.comp_of_polynomial_bound (parameter_tendsto length)
    (hlength.tidy.polynomiallyBounded.comp (PolynomiallyBounded.id.add (.const 1)))
    (Eventually.of_forall (fun size => (lt_length_succ_parameter hge size).le))
  apply negligible_of_eventually_le hdecay
  filter_upwards [eventually_ge_atTop (length 0)] with size hsize
  simp only [distinguishingGame, PMF.monad_bind_eq_bind]
  rw [generate_distribution length generator hsize,
    GeneratorPadding.advantage_eq _ _ (parameter_fits hsize) (Nat.lt_succ_self _)]
  simpa only [real, ideal, test, ProbComp.eval_bind, ProbComp.eval_map,
    BitString.eval_sampleList] using
    hbound (parameter length size) size (lt_length_succ_parameter hge size).le

/-- A uniformly efficient one-bit expanding family on a polynomial schedule gives a PRG
stretching every input by one bit. -/
theorem pseudorandomGenerator {length : ℕ → ℕ} {generator : ℕ → List Bool → List Bool}
    (hlength : ComputableInPolyTime length encUnary encUnary)
    (hge : ∀ n, n + 1 ≤ length n)
    (hgenerator : ComputableInPolyTime (fun a => generator a.1 a.2)
      (encPair encUnary encBits) encBits)
    (houtput : ∀ n seed, seed.length = length n → (generator n seed).length = length n + 1)
    (hsecure : ComputationallyIndistinguishable
      (fun n => (uniformList (length n)).map (generator n))
      (fun n => uniformList (length n + 1))) :
    PseudorandomGenerator (generate length generator) (fun n => n + 1) :=
  .of_indistinguishable (isPolyTime_generate hlength hgenerator)
    (length_generate houtput) (fun _ => Nat.lt_succ_self _)
    (indistinguishable hlength hge hgenerator hsecure)

open scoped NNReal in
/-- Extending a uniformly efficient nonuniformly secure family preserves nonuniform security at
every seed length. For each parameter `n`, the proof passes the worst-case seed length
`size ≤ length (n + 1)` and its advice word `advice size` as polynomially bounded advice to the
padding reduction. -/
theorem nonuniformIndistinguishable {length : ℕ → ℕ} {generator : ℕ → List Bool → List Bool}
    (hlength : ComputableInPolyTime length encUnary encUnary)
    (hge : ∀ n, n + 1 ≤ length n)
    (_hgenerator : ComputableInPolyTime (fun a => generator a.1 a.2)
      (encPair encUnary encBits) encBits)
    (hsecure : NonuniformlyIndistinguishable
      (fun n => (uniformList (length n)).map (generator n))
      (fun n => uniformList (length n + 1))) :
    NonuniformlyIndistinguishable (generatorEnsemble (generate length generator))
      (fun n => uniformList (n + 1)) := by
  have hlengthPoly : PolynomiallyBounded length := hlength.tidy.polynomiallyBounded
  intro advice hadvice adversary hadversary
  let test (n size : ℕ) (adv : List Bool) (word : List Bool) : ProbComp Bool :=
    GeneratorPadding.test (length n) size (fun w => adversary ((size, adv), w)) word
  let eIn := encPair (encPair encUnary (encPair encUnary encBits)) encBits
  have hadv' := hadversary.preprocess
    ((ComputableInPolyTime.fst eIn encBits).fst'.snd'.prod (.snd eIn encBits))
  have htest : IsPPTOn eIn encBool
      (fun input => test input.1.1 input.1.2.1 input.1.2.2 input.2) :=
    GeneratorPadding.isPPTOn_test (hlength.comp (ComputableInPolyTime.fst _ _).fst')
      (ComputableInPolyTime.fst _ _).snd'.fst' hadv' (.snd _ encBits)
  let advAt (n size : ℕ) : ℝ≥0 :=
    Game.advantage
      (((uniformList (length n)).map (generator n)).bind
        (fun word => ProbComp.eval (test n size (advice size) word)))
      ((uniformList (length n + 1)).bind
        (fun word => ProbComp.eval (test n size (advice size) word)))
  have hexists (n : ℕ) : ∃ s ≤ length (n + 1), ∀ size ≤ length (n + 1),
      advAt n size ≤ advAt n s := by
    obtain ⟨s, hs, hmax⟩ := Finset.exists_max_image (Finset.Iic (length (n + 1))) (advAt n)
      ⟨0, Finset.mem_Iic.mpr (Nat.zero_le _)⟩
    exact ⟨s, Finset.mem_Iic.mp hs, fun size hsize => hmax size (Finset.mem_Iic.mpr hsize)⟩
  obtain ⟨worstSize, hworst⟩ := Classical.axiomOfChoice hexists
  have hworst_le (n : ℕ) : worstSize n ≤ length (n + 1) := (hworst n).1
  have hworst_max (n size : ℕ) (hsize : size ≤ length (n + 1)) :
      advAt n size ≤ advAt n (worstSize n) := (hworst n).2 size hsize
  have hworstPoly : PolynomiallyBounded worstSize :=
    (hlengthPoly.comp (PolynomiallyBounded.id.add (.const 1))).mono_of_le hworst_le
  have hadviceWorst : PolynomiallyBounded (fun n => (advice (worstSize n)).length) :=
    hadvice.comp hworstPoly
  have hadvicePair : PolynomiallyBounded
      (fun n => (encPair encUnary encBits (worstSize n, advice (worstSize n))).length) := by
    simp only [length_encPair, encUnary_apply, List.length_replicate, encBits_apply]
    exact (((PolynomiallyBounded.const 2).mul hworstPoly).add (.const 1)).add hadviceWorst
  have hε : Negligible (fun n => advAt n (worstSize n)) := by
    simpa only [advAt, distinguishingGame, PMF.monad_bind_eq_bind] using
      (hsecure (fun n => encPair encUnary encBits (worstSize n, advice (worstSize n)))
        hadvicePair).negligible_encoded htest
  have hdecay := hε.comp_of_polynomial_bound (parameter_tendsto length)
    (hlengthPoly.comp (PolynomiallyBounded.id.add (.const 1)))
    (Eventually.of_forall (fun size => (lt_length_succ_parameter hge size).le))
  apply negligible_of_eventually_le hdecay
  filter_upwards [eventually_ge_atTop (length 0)] with size hsize
  simp only [distinguishingGame, PMF.monad_bind_eq_bind]
  rw [generate_distribution length generator hsize,
    GeneratorPadding.advantage_eq _ _ (parameter_fits hsize) (Nat.lt_succ_self _)]
  exact hworst_max (parameter length size) size (lt_length_succ_parameter hge size).le

/-- A uniformly efficient one-bit expanding nonuniformly secure family on a polynomial schedule
gives a nonuniform PRG stretching every input by one bit. -/
theorem nonuniformPRG {length : ℕ → ℕ} {generator : ℕ → List Bool → List Bool}
    (hlength : ComputableInPolyTime length encUnary encUnary)
    (hge : ∀ n, n + 1 ≤ length n)
    (hgenerator : ComputableInPolyTime (fun a => generator a.1 a.2)
      (encPair encUnary encBits) encBits)
    (houtput : ∀ n seed, seed.length = length n → (generator n seed).length = length n + 1)
    (hsecure : NonuniformlyIndistinguishable
      (fun n => (uniformList (length n)).map (generator n))
      (fun n => uniformList (length n + 1))) :
    NonuniformPRG (generate length generator) (fun n => n + 1) :=
  ⟨isPolyTime_generate hlength hgenerator, length_generate houtput, fun _ => Nat.lt_succ_self _,
    nonuniformIndistinguishable hlength hge hgenerator hsecure⟩

end Cslib.Crypto.GeneratorReindex
