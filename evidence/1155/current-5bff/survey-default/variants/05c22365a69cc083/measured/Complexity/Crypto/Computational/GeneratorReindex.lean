/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.GeneratorPadding
public import Complexity.Crypto.Computational.PseudorandomGenerator
public import Mathlib.Data.Nat.Find
import Complexity.Probability.PMF.Bind
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Search
import Complexity.Crypto.Computational.UniformChoice
import Complexity.Crypto.Negligible.Basic
import Complexity.Tactic.PPT


import Diag1155.Measure
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
* `Cslib.Crypto.GeneratorReindex.indistinguishable`: extending a secure family preserves
  computational indistinguishability at every seed length.
* `Cslib.Crypto.GeneratorReindex.pseudorandomGenerator`: one-bit stretch at every seed length.

## References

This completes the seed-length convention for the construction in
[T. Holenstein, *Pseudorandom Generators from One-Way Functions*][Holenstein2006], Section 5.

Adapted from Crypto/Computational/GeneratorReindex.lean
on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`, using typed machine certificates and the
nonnegative game API.
-/


diag1155_install
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
    ComputableInPolyTime (fun a => parameter length (size a)) input encUnary := by
  simp only [Turing.MultiTapeTM.computableInPolyTime_iff_computableTidilyInPolyTime] at hlength
  simp only [Turing.MultiTapeTM.computableInPolyTime_iff_computableTidilyInPolyTime] at hsize
  simp only [Turing.MultiTapeTM.computableInPolyTime_iff_computableTidilyInPolyTime]
  unfold parameter
  polytime

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
  simp only [Turing.MultiTapeTM.computableInPolyTime_iff_computableTidilyInPolyTime] at hlength
  simp only [Turing.MultiTapeTM.computableInPolyTime_iff_computableTidilyInPolyTime] at hgenerator
  simp only [Turing.MultiTapeTM.computableInPolyTime_iff_computableTidilyInPolyTime]
  have hparameter : ComputableTidilyInPolyTime
      (fun seed : List Bool => parameter length seed.length) encBits encUnary :=
    (isPolyTime_parameter (.of_tidy hlength) (.of_tidy (by fun_prop))).tidy
  have hpadded : ComputableTidilyInPolyTime (fun seed : List Bool =>
      GeneratorPadding.generate (length (parameter length seed.length)) seed.length
        (generator (parameter length seed.length)) seed) encBits encBits :=
    (GeneratorPadding.isPolyTime_generate (α := List Bool) (input := encBits)
      (generator := fun seed => generator (parameter length seed.length))
      (.of_tidy (by fun_prop))
      (.of_tidy (by fun_prop))
      (.of_tidy (hgenerator.comp
        ((hparameter.comp (ComputableTidilyInPolyTime.fst encBits encBits)).prod
          (ComputableTidilyInPolyTime.snd encBits encBits))))
      (.of_tidy (by fun_prop))).tidy
  unfold generate
  polytime

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
  have hlength := hlength.tidy
  have hgenerator := hgenerator.tidy
  intro adversary hadversary
  let real : ℕ → ProbComp (List Bool) := fun n => generator n <$> BitString.sampleList (length n)
  let ideal : ℕ → ProbComp (List Bool) := fun n => BitString.sampleList (length n + 1)
  have hreal : IsPPTOn encUnary encBits real := by unfold real; ppt
  have hideal : IsPPTOn encUnary encBits ideal := by unfold ideal; ppt
  have hfamily : ComputationallyIndistinguishable
      (fun n => ProbComp.eval (real n)) (fun n => ProbComp.eval (ideal n)) := by
    simpa only [real, ideal, ProbComp.eval_map, BitString.eval_sampleList] using hsecure
  let test := fun n size => GeneratorPadding.test (length n) size (adversary size)
  have htest : IsPPTOn (encPair (encPair encUnary encUnary) encBits)
      encBool (fun a => test a.1.1 a.1.2 a.2) := by
    unfold test
    ppt
  obtain ⟨ε, hε, hbound⟩ := hfamily.uniform_bound hreal hideal
    (bound := fun n => length (n + 1)) (.of_tidy (by polytime)) test htest
  have hdecay := hε.comp_of_polynomial_bound (parameter_tendsto length)
    (hlength.polynomiallyBounded.comp (PolynomiallyBounded.id.add (.const 1)))
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
    PseudorandomGenerator (generate length generator) (fun n => n + 1) := by
  have hlength := hlength.tidy
  have hgenerator := hgenerator.tidy
  exact .of_indistinguishable (isPolyTime_generate (.of_tidy hlength) (.of_tidy hgenerator))
    (length_generate houtput) (fun _ => Nat.lt_succ_self _)
    (indistinguishable (.of_tidy hlength) hge (.of_tidy hgenerator) hsecure)

end Cslib.Crypto.GeneratorReindex
