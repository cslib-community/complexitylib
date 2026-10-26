/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.PseudorandomGenerator
public import Complexity.Crypto.Computational.Stretch.Quantitative
public import Complexity.Languages.Probabilistic.UniformNat
import Complexity.Probability.PMF.Bind
import Complexity.Crypto.Game.Hybrid
import Complexity.Computability.Probabilistic.UniformNat
import Complexity.Probability.PMF.Map
import Complexity.Tactic.PPT
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Polynomial stretch from one-bit pseudorandom generators

Keep a seed of the original length at the front of a word. Each iteration expands that seed
by one bit and retains the previously emitted suffix. The security proof replaces successive
seed expansions by uniform bits, using one uniformly randomized reduction across all hops.
The seed width may differ from the security parameter, and the generator may capture an index.
`indexed_indistinguishable` preserves a secure choice in such a family.

The deterministic iteration and stretch operators (`PRGStretch.step`, `PRGStretch.iterate`,
`PRGStretch.stretch`) and their polynomial-time and cumulative quantitative certificates live in
`Complexity.Crypto.Computational.Stretch.Quantitative`, which this module re-exports.

## Main definitions

* `PRGStretch.stretch`: repeatedly expand a fixed-width seed prefix and retain emitted bits
  (re-exported from `Stretch.Quantitative`).
* `PRGStretch.reduction`: one uniform bounded-hop security reduction.

## Main results

* `PRGStretch.polyTime_iterate`: captured functional iteration has a uniform TM certificate
  (re-exported from `Stretch.Quantitative`).
* `PRGStretch.advantage_eq`: exact sampling-range loss for the uniform reduction.
* `PRGStretch.indexed_indistinguishable`, `PRGStretch.indistinguishable`,
  `PRGStretch.pseudorandomGenerator`: polynomially many one-bit expansions preserve computational
  indistinguishability and yield a secure PRG.
* `PseudorandomGenerator.amplify`, `.truncate`: efficient changes of output length.

## References

* [B. Barak, *Pseudorandomness*, CS 127][Barak2016PRG], length extension for PRGs.
  We retain the final seed and reverse the order of the emitted bits. The reduction explicitly
  samples its hop to preserve uniformity, with dyadic padding for strict fair-coin sampling.

Adapted from Crypto/Computational/Stretch.lean on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`, using the tidy calculus and current upstream games.
-/

@[expose] public section

namespace Cslib.Crypto.PRGStretch

open ProbComp Probability BitString Turing.MultiTapeTM

/-- Hybrid `i` has `i` genuinely random suffix bits and `total - i` seed expansions left. -/
noncomputable def hybrid (generator : List Bool → List Bool) (n total i : ℕ) : PMF (List Bool) :=
  (uniformList (n + i)).map (iterate generator n (total - i))

/-- The initial hybrid is the stretched generator's output. -/
theorem hybrid_zero (generator : List Bool → List Bool) (count : ℕ → ℕ) (n : ℕ) :
    hybrid generator n (count n) 0 = generatorEnsemble (stretch generator count) n := by
  simp only [hybrid, Nat.add_zero, Nat.sub_zero, generatorEnsemble]
  apply PMF.map_congr_on_support
  intro seed hseed
  simp only [stretch, length_of_mem_support_uniformList hseed]

/-- The final hybrid is uniform at the expanded length. -/
@[simp] theorem hybrid_last (generator : List Bool → List Bool) (n total : ℕ) :
    hybrid generator n total total = uniformList (n + total) := by
  unfold hybrid iterate
  simp only [Nat.sub_self, Function.iterate_zero]
  exact PMF.map_id _

/-- Replacing the challenge by a genuine generator output gives the earlier hybrid. -/
theorem real_hop (generator : List Bool → List Bool) (n total i : ℕ) (hi : i < total) :
    (do
      let challenge ← generatorEnsemble generator n
      (uniformList i).map (fun suffix =>
        iterate generator n (total - (i + 1)) (challenge ++ suffix))) =
      hybrid generator n total i := by
  have hcount : total - i = total - (i + 1) + 1 := by lia
  simp only [generatorEnsemble, PMF.monad_bind_eq_bind, PMF.bind_map, hybrid,
    uniformList_add, PMF.map_bind, PMF.map_comp, Function.comp_def]
  apply PMF.bind_congr_on_support
  intro seed hseed
  congr 1
  funext suffix
  simp only [iterate, hcount, Function.iterate_succ_apply,
    step_append generator seed suffix (length_of_mem_support_uniformList hseed)]

/-- Replacing the challenge by uniform bits gives the next hybrid. -/
theorem ideal_hop (generator : List Bool → List Bool) (n total i : ℕ) :
    (do
      let challenge ← uniformList (n + 1)
      (uniformList i).map (fun suffix =>
        iterate generator n (total - (i + 1)) (challenge ++ suffix))) =
      hybrid generator n total (i + 1) := by
  rw [hybrid, show n + (i + 1) = (n + 1) + i by lia, uniformList_add (n + 1) i]
  simp only [PMF.monad_bind_eq_bind, PMF.map_bind, PMF.map_comp, Function.comp_def]

/-- Embed one challenge at a chosen hop; out-of-range hops reject on both sides. -/
noncomputable def hop (generator : List Bool → List Bool) (count : ℕ → ℕ)
    (adversary : Distinguisher)
    (n i : ℕ) (challenge : List Bool) : ProbComp Bool := do
  if i < count n then
    let suffix ← BitString.sampleList i
    adversary n (iterate generator n (count n - (i + 1)) (challenge ++ suffix))
  else pure false

/-- One uniform reduction samples its hop using a bounded number of fair bits. -/
noncomputable def reduction (generator : List Bool → List Bool) (count : ℕ → ℕ)
    (adversary : Distinguisher) : Distinguisher := fun n challenge => do
  let i ← sampleBoundedIndex (count n)
  hop generator count adversary n i challenge

/-- Apply the same random-hop reduction at an explicit seed length, with any captured test. -/
noncomputable def test (generator : List Bool → List Bool) (seedBits count : ℕ)
    (adversary : List Bool → ProbComp Bool) (challenge : List Bool) : ProbComp Bool :=
  reduction generator (fun _ => count) (fun _ => adversary) seedBits challenge

attribute [local fun_prop] ComputableInPolyTime.tidy in
/-- Captured parameters, generator code, and the adversary compose through the public tactics. -/
@[program_certificate]
theorem isPPT_test {α : Type} {input : α ↪ List Bool}
    {generator : α → List Bool → List Bool} {seedBits count : α → ℕ}
    {adversary : α → List Bool → ProbComp Bool} {challenge : α → List Bool}
    (hgenerator : ComputableInPolyTime (fun pair => generator pair.1 pair.2)
      (encPair input encBits) encBits)
    (hseedBits : ComputableInPolyTime seedBits input encUnary)
    (hcount : ComputableInPolyTime count input encUnary)
    (hadversary : IsPPTOn (encPair input encBits) encBool
      (fun pair => adversary pair.1 pair.2))
    (hchallenge : ComputableInPolyTime challenge input encBits) :
    IsPPTOn input encBool
      (fun a => test (generator a) (seedBits a) (count a) (adversary a) (challenge a)) := by
  let pairEncoding := encPair input encUnary
  let fullEncoding := encPair pairEncoding encBits
  have ha := ComputableInPolyTime.fst input encUnary
  have hi := ComputableInPolyTime.snd input encUnary
  have houter := ComputableInPolyTime.fst pairEncoding encBits
  have hsuffix := ComputableInPolyTime.snd pairEncoding encBits
  have hprepare : ComputableInPolyTime
      (fun p : (α × ℕ) × List Bool => (p.1.1,
        iterate (generator p.1.1) (seedBits p.1.1) (count p.1.1 - (p.1.2 + 1))
          (challenge p.1.1 ++ p.2))) fullEncoding (encPair input encBits) := by
    apply ComputableInPolyTime.prod (ha.comp houter)
    apply polyTime_iterate
    · have hparam := ComputableInPolyTime.fst fullEncoding encBits
      have hword := ComputableInPolyTime.snd fullEncoding encBits
      have harg : ComputableInPolyTime
          (fun p : ((α × ℕ) × List Bool) × List Bool => (p.1.1.1, p.2))
          (encPair fullEncoding encBits) (encPair input encBits) :=
        ((ha.comp houter).comp hparam).prod hword
      exact hgenerator.comp harg
    · exact hseedBits.comp (ha.comp houter)
    · exact ComputableInPolyTime.unary_sub.comp
        ((hcount.comp (ha.comp houter)).prod
          (ComputableInPolyTime.unary_succ.comp (hi.comp houter)))
    · exact ComputableInPolyTime.bitsAppend (hchallenge.comp (ha.comp houter)) hsuffix
  have hsample := isPPTOn_sampleList.preprocess hi
  have hpost : IsPPTOn fullEncoding encBool (fun p : (α × ℕ) × List Bool =>
      adversary p.1.1 (iterate (generator p.1.1) (seedBits p.1.1)
        (count p.1.1 - (p.1.2 + 1)) (challenge p.1.1 ++ p.2))) := by
    simpa only [Function.comp_def] using hadversary.preprocess hprepare
  have hyes := hsample.bind_with
    (second := fun p suffix => adversary p.1 (iterate (generator p.1) (seedBits p.1)
      (count p.1 - (p.2 + 1)) (challenge p.1 ++ suffix))) hpost
  have hcond := ComputableInPolyTime.unary_lt' hi (hcount.comp ha)
  have hfalse : IsPPTOn pairEncoding encBool (fun _ => pure false) :=
    (ComputableInPolyTime.const false).isPPTOn
  have hbranch := IsPPTOn.ite hcond.tidy hyes hfalse
  have hindex := isPPTOn_sampleBoundedIndex hcount
  simpa only [test, reduction, hop, pairEncoding, fullEncoding, Function.comp_def] using
    hindex.bind_with hbranch

/-- The reduction's complete efficiency proof uses the public programming interface. -/
@[program_certificate]
theorem isPPT_reduction {generator : List Bool → List Bool} {count : ℕ → ℕ}
    {adversary : Distinguisher} (hgenerator : ComputableInPolyTime generator encBits encBits)
    (hcount : ComputableInPolyTime count encUnary encUnary)
    (hadversary : IsPPT encBool adversary) :
    IsPPT encBool (reduction generator count adversary) := by
  have hgen : ComputableInPolyTime
      (fun p : (ℕ × List Bool) × List Bool => generator p.2)
      (encPair (encPair encUnary encBits) encBits) encBits :=
    hgenerator.comp (ComputableInPolyTime.snd (encPair encUnary encBits) encBits)
  have hadv : IsPPTOn (encPair (encPair encUnary encBits) encBits) encBool
      (fun p => adversary p.1.1 p.2) := hadversary.on.preprocess
    ((ComputableInPolyTime.fst (encPair encUnary encBits) encBits).fst'.prod
      (ComputableInPolyTime.snd (encPair encUnary encBits) encBits))
  simpa only [IsPPT, test, reduction, hop, Function.comp_def] using
    (isPPT_test hgen (ComputableInPolyTime.fst encUnary encBits)
      (hcount.comp (ComputableInPolyTime.fst encUnary encBits)) hadv
      (ComputableInPolyTime.snd encUnary encBits))

/-- Capping a sampled index only merges rejecting branches. -/
theorem hop_min (generator : List Bool → List Bool) (count : ℕ → ℕ)
    (adversary : Distinguisher)
    (n i : ℕ) (challenge : List Bool) :
    hop generator count adversary n (min (count n) i) challenge =
      hop generator count adversary n i challenge := by
  by_cases hi : i < count n
  · rw [Nat.min_eq_right (by lia)]
  · simp [hop, hi, Nat.min_eq_left (by lia : count n ≤ i)]

/-- The randomized reduction is exactly a uniform mixture of its padded hop reductions. -/
theorem eval_reduction (generator : List Bool → List Bool) (count : ℕ → ℕ)
    (adversary : Distinguisher)
    (n : ℕ) (challenge : List Bool) :
    ProbComp.eval (reduction generator count adversary n challenge) =
      (PMF.uniformOfFintype (Fin (2 ^ (Nat.log 2 (count n) + 1)))).bind
        (fun i => ProbComp.eval (hop generator count adversary n i.val challenge)) := by
  simp only [reduction, ProbComp.eval_bind, eval_sampleBoundedIndex, PMF.bind_map,
    Function.comp_def, hop_min]

/-- The real challenge at a fixed hop realizes the earlier hybrid experiment. -/
theorem eval_real_hop (generator : List Bool → List Bool) (count : ℕ → ℕ)
    (adversary : Distinguisher)
    (n i : ℕ) :
    (generatorEnsemble generator n).bind
        (fun challenge => ProbComp.eval (hop generator count adversary n i challenge)) =
      if i < count n then
        (hybrid generator n (count n) i).bind (fun word => ProbComp.eval (adversary n word))
      else PMF.pure false := by
  by_cases hi : i < count n
  · simp only [hi, ↓reduceIte]
    have h := congrArg (fun distribution : PMF (List Bool) =>
      distribution.bind (fun word => ProbComp.eval (adversary n word)))
      (real_hop generator n (count n) i hi)
    simpa only [hop, hi, ↓reduceIte, ProbComp.eval_bind, eval_sampleList, PMF.monad_bind_eq_bind,
      PMF.bind_bind, PMF.bind_map, Function.comp_def] using h
  · simp [hop, hi, PMF.bind_const]

/-- The ideal challenge at a fixed hop realizes the next hybrid experiment. -/
theorem eval_ideal_hop (generator : List Bool → List Bool) (count : ℕ → ℕ)
    (adversary : Distinguisher)
    (n i : ℕ) :
    (uniformList (n + 1)).bind
        (fun challenge => ProbComp.eval (hop generator count adversary n i challenge)) =
      if i < count n then
        (hybrid generator n (count n) (i + 1)).bind (fun word => ProbComp.eval (adversary n word))
      else PMF.pure false := by
  by_cases hi : i < count n
  · simp only [hi, ↓reduceIte]
    have h := congrArg (fun distribution : PMF (List Bool) =>
      distribution.bind (fun word => ProbComp.eval (adversary n word)))
      (ideal_hop generator n (count n) i)
    simpa only [hop, hi, ↓reduceIte, ProbComp.eval_bind, eval_sampleList, PMF.monad_bind_eq_bind,
      PMF.bind_bind, PMF.bind_map, Function.comp_def] using h
  · simp [hop, hi, PMF.bind_const]

/-- Exact loss of the uniform reduction, including the padded sampling outcomes. -/
theorem advantage_eq (generator : List Bool → List Bool) (count : ℕ → ℕ)
    (adversary : Distinguisher)
    (n : ℕ) :
    Game.advantage (ProbComp.eval (prgRealGame (stretch generator count) adversary n))
        (ProbComp.eval (prgIdealGame (fun n => n + count n) adversary n)) =
      (2 ^ (Nat.log 2 (count n) + 1) : ℕ) *
        Game.advantage
          (ProbComp.eval (prgRealGame generator (reduction generator count adversary) n))
          (ProbComp.eval
            (prgIdealGame (fun n => n + 1) (reduction generator count adversary) n)) := by
  have hreal : ProbComp.eval (prgRealGame generator (reduction generator count adversary) n) =
      (PMF.uniformOfFintype (Fin (2 ^ (Nat.log 2 (count n) + 1)))).bind (fun i =>
        if i.val < count n then (hybrid generator n (count n) i.val).bind
          (fun word => ProbComp.eval (adversary n word)) else PMF.pure false) := by
    rw [eval_prgRealGame]
    change (generatorEnsemble generator n).bind _ = _
    simp_rw [eval_reduction]
    rw [PMF.bind_comm]
    congr 1
    funext i
    exact eval_real_hop generator count adversary n i.val
  have hideal : ProbComp.eval (prgIdealGame (fun n => n + 1)
      (reduction generator count adversary) n) =
      (PMF.uniformOfFintype (Fin (2 ^ (Nat.log 2 (count n) + 1)))).bind (fun i =>
        if i.val < count n then (hybrid generator n (count n) (i.val + 1)).bind
          (fun word => ProbComp.eval (adversary n word)) else PMF.pure false) := by
    rw [eval_prgIdealGame]
    change (uniformList (n + 1)).bind _ = _
    simp_rw [eval_reduction]
    rw [PMF.bind_comm]
    congr 1
    funext i
    exact eval_ideal_hop generator count adversary n i.val
  have havg := Game.advantage_hybrid_average
    (fun i => (hybrid generator n (count n) i).bind
      (fun word => ProbComp.eval (adversary n word))) (count n)
    (2 ^ (Nat.log 2 (count n) + 1))
    (Nat.le_of_lt (Nat.lt_pow_succ_log_self Nat.one_lt_two (count n)))
  rw [← hreal, ← hideal, hybrid_zero, hybrid_last] at havg
  simpa only [eval_prgRealGame, eval_prgIdealGame, distinguishingGame,
    PMF.monad_bind_eq_bind] using havg

/-- The same exact loss applies with the seed length independent of the security parameter.
This form is convenient for indexed candidate families. -/
theorem test_advantage_eq (generator : List Bool → List Bool) (seedBits count : ℕ)
    (adversary : List Bool → ProbComp Bool) :
    Game.advantage
      (((uniformList seedBits).map (iterate generator seedBits count)).bind
        (fun word => ProbComp.eval (adversary word)))
      ((uniformList (seedBits + count)).bind (fun word => ProbComp.eval (adversary word))) =
      (2 ^ (Nat.log 2 count + 1) : ℕ) *
        Game.advantage
          (((uniformList seedBits).map generator).bind
            (fun word => ProbComp.eval (test generator seedBits count adversary word)))
          ((uniformList (seedBits + 1)).bind
            (fun word => ProbComp.eval (test generator seedBits count adversary word))) := by
  have h := advantage_eq generator (fun _ => count) (fun _ => adversary) seedBits
  simp only [eval_prgRealGame, eval_prgIdealGame] at h
  rw [← hybrid_zero generator (fun _ => count) seedBits] at h
  simpa only [hybrid, Nat.add_zero, Nat.sub_zero, generatorEnsemble,
    distinguishingGame, PMF.monad_bind_eq_bind, test] using h

/-- Padding the sampled hop loses at most twice the number of expansions. -/
theorem advantage_le (generator : List Bool → List Bool) (count : ℕ → ℕ)
    (adversary : Distinguisher)
    (n : ℕ) (hpositive : 0 < count n) :
    Game.advantage (ProbComp.eval (prgRealGame (stretch generator count) adversary n))
        (ProbComp.eval (prgIdealGame (fun n => n + count n) adversary n)) ≤
      (2 * count n : ℕ) *
        Game.advantage
          (ProbComp.eval (prgRealGame generator (reduction generator count adversary) n))
          (ProbComp.eval
            (prgIdealGame (fun n => n + 1) (reduction generator count adversary) n)) := by
  rw [advantage_eq]
  have hpow : 2 ^ (Nat.log 2 (count n) + 1) ≤ 2 * count n := by
    rw [pow_succ]
    have := Nat.pow_log_le_self 2 (by lia : count n ≠ 0)
    lia
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hpow) zero_le

/-- Efficient unary counts give a polynomial bound on the reduction's dyadic loss. -/
theorem loss_polynomial {count : ℕ → ℕ}
    (hcount : ComputableInPolyTime count encUnary encUnary) :
    PolynomiallyBounded (fun n => 2 ^ (Nat.log 2 (count n) + 1)) := by
  have hcount := hcount.tidy
  exact dyadicSize_polynomiallyBounded.comp hcount.polynomiallyBounded

/-- Polynomially many expansions preserve the secure choice in a uniformly efficient family.
The choice is supplied only in the proof; each reduction receives its index as ordinary input. -/
theorem indexed_indistinguishable {generator : ℕ → ℕ → List Bool → List Bool}
    {seedBits count choose : ℕ → ℕ}
    (hgenerator : ComputableInPolyTime
      (fun input => generator input.1.1 input.1.2 input.2)
      (encPair (encPair encUnary encUnary) encBits) encBits)
    (hseedBits : ComputableInPolyTime seedBits encUnary encUnary)
    (hcount : ComputableInPolyTime count encUnary encUnary)
    (hsecure : ∀ adversary : ℕ → ℕ → List Bool → ProbComp Bool,
      IsPPTOn (encPair (encPair encUnary encUnary) encBits)
        encBool (fun input => adversary input.1.1 input.1.2 input.2) →
      Negligible (fun n => Game.advantage
        (((uniformList (seedBits n)).map (generator n (choose n))).bind
          (fun word => ProbComp.eval (adversary n (choose n) word)))
        ((uniformList (seedBits n + 1)).bind
          (fun word => ProbComp.eval (adversary n (choose n) word))))) :
    ∀ adversary : ℕ → ℕ → List Bool → ProbComp Bool,
      IsPPTOn (encPair (encPair encUnary encUnary) encBits)
        encBool (fun input => adversary input.1.1 input.1.2 input.2) →
      Negligible (fun n => Game.advantage
        (((uniformList (seedBits n)).map
          (iterate (generator n (choose n)) (seedBits n) (count n))).bind
            (fun word => ProbComp.eval (adversary n (choose n) word)))
        ((uniformList (seedBits n + count n)).bind
          (fun word => ProbComp.eval (adversary n (choose n) word)))) := by
  simp only [Turing.MultiTapeTM.computableInPolyTime_iff_computableTidilyInPolyTime] at hgenerator
  simp only [Turing.MultiTapeTM.computableInPolyTime_iff_computableTidilyInPolyTime] at hseedBits
  simp only [Turing.MultiTapeTM.computableInPolyTime_iff_computableTidilyInPolyTime] at hcount
  intro adversary hadversary
  let reduction := fun n index =>
    test (generator n index) (seedBits n) (count n) (adversary n index)
  have hprepare : ComputableTidilyInPolyTime
      (fun p : ((ℕ × ℕ) × List Bool) × List Bool => (p.1.1, p.2))
      (encPair (encPair (encPair encUnary encUnary) encBits) encBits)
      (encPair (encPair encUnary encUnary) encBits) := by fun_prop
  have hreduce : IsPPTOn (encPair (encPair encUnary encUnary) encBits)
      encBool (fun input => reduction input.1.1 input.1.2 input.2) := by
    unfold reduction
    exact isPPT_test (.of_tidy (hgenerator.comp hprepare)) (.of_tidy (by polytime))
      (.of_tidy (by polytime))
      (hadversary.preprocess (.of_tidy hprepare)) (.of_tidy (by polytime))
  have h := (hsecure reduction hreduce).polynomiallyBounded_mul (loss_polynomial (.of_tidy hcount))
  exact h.congr' (Filter.Eventually.of_forall (fun n => (test_advantage_eq _ _ _ _).symm))

/-- Polynomially many seed expansions preserve computational indistinguishability. -/
theorem indistinguishable {generator : List Bool → List Bool} {count : ℕ → ℕ}
    (hgenerator : PseudorandomGenerator generator (fun n => n + 1))
    (hcount : ComputableInPolyTime count encUnary encUnary) :
    ComputationallyIndistinguishable (generatorEnsemble (stretch generator count))
      (fun n => uniformList (n + count n)) := by
  have hcount := hcount.tidy
  intro adversary hadversary
  have hreduce := isPPT_reduction hgenerator.polyTime (.of_tidy hcount) hadversary
  have hnegligible := hgenerator.indistinguishable _ hreduce
  have hloss := hnegligible.polynomiallyBounded_mul (loss_polynomial (.of_tidy hcount))
  convert hloss using 1
  funext n
  simpa only [eval_prgRealGame, eval_prgIdealGame] using
    advantage_eq generator count adversary n

/-- A positive efficiently computed number of one-bit expansions is a secure PRG. -/
theorem pseudorandomGenerator {generator : List Bool → List Bool} {count : ℕ → ℕ}
    (hgenerator : PseudorandomGenerator generator (fun n => n + 1))
    (hcount : ComputableInPolyTime count encUnary encUnary)
    (hpositive : ∀ n, 0 < count n) :
    PseudorandomGenerator (stretch generator count) (fun n => n + count n) := by
  have hcount := hcount.tidy
  refine PseudorandomGenerator.of_indistinguishable
    (polyTime_stretch hgenerator.polyTime (.of_tidy hcount)) ?_ ?_
    (indistinguishable hgenerator (.of_tidy hcount))
  · intro seed
    exact length_iterate hgenerator.length_eq _ _ _
  · intro n
    exact Nat.lt_add_of_pos_right (hpositive n)

end Cslib.Crypto.PRGStretch

namespace Cslib.Crypto

open ProbComp Probability BitString Turing.MultiTapeTM

/-- Amplify a one-bit PRG to any efficiently computed, strictly larger output length. -/
theorem PseudorandomGenerator.amplify {generator : List Bool → List Bool}
    (hgenerator : PseudorandomGenerator generator (fun n => n + 1))
    (target : ℕ → ℕ) (htarget : ComputableInPolyTime target encUnary encUnary)
    (hstretch : ∀ n, n < target n) :
    PseudorandomGenerator (PRGStretch.stretch generator (fun n => target n - n)) target := by
  simp only [Turing.MultiTapeTM.computableInPolyTime_iff_computableTidilyInPolyTime] at htarget
  have hcount : ComputableTidilyInPolyTime (fun n => target n - n) encUnary encUnary := by polytime
  have h := PRGStretch.pseudorandomGenerator hgenerator (.of_tidy hcount) (fun n => by
    have := hstretch n
    lia)
  convert h using 1
  funext n
  have := hstretch n
  lia

/-- Truncating a PRG to an efficiently computed, still-expanding length preserves security. -/
theorem PseudorandomGenerator.truncate {generator : List Bool → List Bool} {length : ℕ → ℕ}
    (hgenerator : PseudorandomGenerator generator length)
    (target : ℕ → ℕ)
    (htarget : ComputableInPolyTime target encUnary encUnary)
    (hle : ∀ n, target n ≤ length n) (hstretch : ∀ n, n < target n) :
    PseudorandomGenerator (fun seed => (generator seed).take (target seed.length)) target := by
  simp only [Turing.MultiTapeTM.computableInPolyTime_iff_computableTidilyInPolyTime] at htarget
  have hpoly := hgenerator.polyTime.tidy
  refine PseudorandomGenerator.of_indistinguishable (.of_tidy (by polytime)) ?_ hstretch ?_
  · intro seed
    simp only [List.length_take, hgenerator.length_eq, Nat.min_eq_left (hle _)]
  · have h := hgenerator.indistinguishable.map
      (f := fun n word => word.take (target n)) (by polytime)
    simpa only [← generatorEnsemble_postprocess generator (fun n word => word.take (target n)),
      uniformList_take (hle _)] using h

end Cslib.Crypto
