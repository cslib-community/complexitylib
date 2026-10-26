/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.Basic
public import Complexity.Crypto.Game.Hybrid
public import Complexity.Computability.Probabilistic.Repeat
public import Complexity.Computability.Probabilistic.UniformNat
import Complexity.Tactic.PPT


import Diag1155.Measure
/-!
# Replacing independent samples one coordinate at a time

`sequenceHybrid` draws an initial segment from a replacement source and the remaining segment
from the original source. `spliceTest` samples the surrounding coordinates and inserts one
challenge into the resulting list. Its adjacent-game laws expose the usual hybrid proof without
tuple-index bookkeeping, and apply to arbitrary discrete sample types.

## Main definitions

* `Cslib.Crypto.sequenceHybrid`: replace an initial segment of independent samples.
* `Cslib.Crypto.spliceTest`: insert one challenge between two independently sampled segments.
* `Cslib.Crypto.sequenceTest`: select one coordinate from a padded dyadic range.

## Main results

* `Cslib.Crypto.sequenceTest_gap`: an exact signed gap with the dyadic sampling-range loss.
* `Cslib.Crypto.sequenceTest_advantage`: the corresponding exact unsigned loss,
  including count zero.
* `Cslib.Crypto.isPPTOn_sequenceTest`: a uniform strict PPT certificate, including padding indices.

## References

* [T. Holenstein, *Pseudorandom Generators from One-Way Functions: A Simple Construction for
  Any Hardness*][Holenstein2006], Section 5, Games 3–5.

Adapted from Crypto/Computational/Hybrid/Sequence.lean on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`, using the current nonnegative game API.

-/


diag1155_install
@[expose] public section

namespace Cslib.Crypto

open ProbComp Probability Turing.MultiTapeTM
open scoped NNReal

variable {α : Type}

/-- Replace the initial `split` samples of an independent sequence. -/
def sequenceHybrid (replacement original : ProbComp α) (count split : ℕ) : ProbComp (List α) := do
  let front ← OracleComp.replicate split replacement
  let back ← OracleComp.replicate (count - split) original
  return front ++ back

/-- Simulate all surrounding coordinates and insert the supplied challenge between them. -/
def spliceTest (replacement original : ProbComp α) (before after : ℕ)
    (test : List α → ProbComp Bool) (challenge : α) : ProbComp Bool := do
  let front ← OracleComp.replicate before replacement
  let back ← OracleComp.replicate after original
  test (front ++ challenge :: back)

@[simp] theorem sequenceHybrid_zero (replacement original : ProbComp α) (count : ℕ) :
    sequenceHybrid replacement original count 0 = OracleComp.replicate count original := by
  simp [sequenceHybrid]

@[simp] theorem sequenceHybrid_self (replacement original : ProbComp α) (count : ℕ) :
    sequenceHybrid replacement original count count = OracleComp.replicate count replacement := by
  simp [sequenceHybrid]

/-- An original challenge supplies the first draw of the remaining original segment. -/
theorem eval_spliceTest_original (replacement original : ProbComp α) (before after : ℕ)
    (test : List α → ProbComp Bool) :
    ProbComp.eval (original >>= spliceTest replacement original before after test) =
      ProbComp.eval (do
        let front ← OracleComp.replicate before replacement
        let back ← OracleComp.replicate (after + 1) original
        test (front ++ back)) := by
  simp only [spliceTest, OracleComp.replicate_succ, ProbComp.eval_bind, ProbComp.eval_map,
    PMF.bind_bind, PMF.bind_map, Function.comp_def]
  exact PMF.bind_comm _ _ _

/-- A replacement challenge supplies the last draw of the replacement segment. -/
theorem eval_spliceTest_replacement (replacement original : ProbComp α) (before after : ℕ)
    (test : List α → ProbComp Bool) :
    ProbComp.eval (replacement >>= spliceTest replacement original before after test) =
      ProbComp.eval (do
        let front ← OracleComp.replicate (before + 1) replacement
        let back ← OracleComp.replicate after original
        test (front ++ back)) := by
  simp only [spliceTest, OracleComp.replicate_snoc, ProbComp.eval_bind, ProbComp.eval_map,
    PMF.bind_bind, PMF.bind_map, Function.comp_def, List.append_assoc, List.singleton_append]
  exact PMF.bind_comm _ _ _

/-- Inserting an original challenge gives the earlier adjacent hybrid. -/
theorem eval_spliceTest_step_original (replacement original : ProbComp α) (count split : ℕ)
    (hsplit : split < count) (test : List α → ProbComp Bool) :
    ProbComp.eval (original >>= spliceTest replacement original split (count - split - 1) test) =
      ProbComp.eval (sequenceHybrid replacement original count split >>= test) := by
  rw [eval_spliceTest_original]
  have hcount : count - split - 1 + 1 = count - split := by lia
  simp only [hcount, sequenceHybrid, bind_assoc, pure_bind]

/-- Inserting a replacement challenge gives the later adjacent hybrid. -/
theorem eval_spliceTest_step_replacement (replacement original : ProbComp α) (count split : ℕ)
    (test : List α → ProbComp Bool) :
    ProbComp.eval
        (replacement >>= spliceTest replacement original split (count - split - 1) test) =
      ProbComp.eval (sequenceHybrid replacement original count (split + 1) >>= test) := by
  rw [eval_spliceTest_replacement]
  simp only [sequenceHybrid, bind_assoc, pure_bind, Nat.sub_sub]

/-- Sample a coordinate uniformly from a dyadic range and run its adjacent-hybrid test.
Unused coordinates reject, so they contribute zero signed gap. -/
noncomputable def sequenceTest (replacement original : ProbComp α) (count : ℕ)
    (test : List α → ProbComp Bool) (challenge : α) : ProbComp Bool := do
  let split ← sampleDyadicIndex count
  if split < count then
    spliceTest replacement original split (count - split - 1) test challenge
  else pure false

/-- One uniform single-sample distinguisher captures the entire sequence gap, with the linear
dyadic-range loss. The identity also covers zero repetitions. -/
theorem sequenceTest_gap (replacement original : ProbComp α) (count : ℕ)
    (test : List α → ProbComp Bool) :
    (Game.succProbability (ProbComp.eval (OracleComp.replicate count original >>= test)) : ℝ) -
        Game.succProbability (ProbComp.eval (OracleComp.replicate count replacement >>= test)) =
      (dyadicSize count : ℝ) *
        (Game.succProbability
            (ProbComp.eval (original >>= sequenceTest replacement original count test)) -
          Game.succProbability
            (ProbComp.eval (replacement >>= sequenceTest replacement original count test))) := by
  unfold sequenceTest
  have horiginal := eval_bind_sampleDyadicIndex_guard original count
    (fun split => spliceTest replacement original split (count - split - 1) test) false
  have hreplacement := eval_bind_sampleDyadicIndex_guard replacement count
    (fun split => spliceTest replacement original split (count - split - 1) test) false
  simp only [eval_spliceTest_step_replacement] at hreplacement
  simp (config := { contextual := true }) only [eval_spliceTest_step_original] at horiginal
  have h := Game.succProbability_hybrid_average
    (fun i => ProbComp.eval (sequenceHybrid replacement original count i >>= test))
    count (dyadicSize count) (lt_dyadicSize count).le
  simpa only [sequenceHybrid_zero, sequenceHybrid_self, PMF.monad_bind_eq_bind,
    horiginal, hreplacement] using h

/-- The exact unsigned sequence-hybrid loss, including the empty sequence. -/
theorem sequenceTest_advantage (replacement original : ProbComp α) (count : ℕ)
    (test : List α → ProbComp Bool) :
    Game.advantage (ProbComp.eval (OracleComp.replicate count original >>= test))
        (ProbComp.eval (OracleComp.replicate count replacement >>= test)) =
      (dyadicSize count : ℝ≥0) *
        Game.advantage (ProbComp.eval (original >>= sequenceTest replacement original count test))
          (ProbComp.eval (replacement >>= sequenceTest replacement original count test)) := by
  apply NNReal.eq
  rw [NNReal.coe_mul, NNReal.coe_natCast, Game.coe_advantage, Game.coe_advantage,
    sequenceTest_gap, abs_mul, Nat.abs_cast]

/-- Efficient source programs and counts give an efficient independent hybrid sequence. -/
theorem isPPTOn_sequenceHybrid {Param : Type} {input : Param ↪ List Bool} {sample : α ↪ List Bool}
    {replacement original : Param → ProbComp α} {count split : Param → ℕ}
    (hreplacement : IsPPTOn input sample replacement)
    (horiginal : IsPPTOn input sample original)
    (hcount : ComputableInPolyTime count input encUnary)
    (hsplit : ComputableInPolyTime split input encUnary) :
    IsPPTOn input (encList sample)
      (fun a => sequenceHybrid (replacement a) (original a) (count a) (split a)) := by
  have hfront := hreplacement.replicate hsplit
  have hremain := ComputableInPolyTime.unary_sub.comp (hcount.prod hsplit)
  have hback := (horiginal.replicate hremain).preprocess
    (ComputableInPolyTime.fst input (encList sample))
  have houter := ComputableInPolyTime.fst (encPair input (encList sample)) (encList sample)
  have hlast := ComputableInPolyTime.snd (encPair input (encList sample)) (encList sample)
  have hjoin := ComputableInPolyTime.listAppend' houter.snd' hlast
  simpa only [sequenceHybrid, bind_pure_comp, Function.comp_def] using
    hfront.bind_with (hback.map_with hjoin)

/-- The inserted challenge and every simulated coordinate are charged by the strict PPT
certificate. The test may capture the complete original input. -/
theorem isPPTOn_spliceTest {Param : Type} {input : Param ↪ List Bool} {sample : α ↪ List Bool}
    {replacement original : Param → ProbComp α} {before after : Param → ℕ}
    {test : Param → List α → ProbComp Bool} {challenge : Param → α}
    (hreplacement : IsPPTOn input sample replacement)
    (horiginal : IsPPTOn input sample original)
    (hbefore : ComputableInPolyTime before input encUnary)
    (hafter : ComputableInPolyTime after input encUnary)
    (htest : IsPPTOn (encPair input (encList sample)) encBool
      (fun pair => test pair.1 pair.2))
    (hchallenge : ComputableInPolyTime challenge input sample) :
    IsPPTOn input encBool
      (fun a => spliceTest (replacement a) (original a) (before a) (after a)
        (test a) (challenge a)) := by
  have hfront := hreplacement.replicate hbefore
  have hback := (horiginal.replicate hafter).preprocess
    (ComputableInPolyTime.fst input (encList sample))
  have houter := ComputableInPolyTime.fst (encPair input (encList sample)) (encList sample)
  have hlast := ComputableInPolyTime.snd (encPair input (encList sample)) (encList sample)
  have harg := houter.fst'.prod (ComputableInPolyTime.listAppend' houter.snd'
    (ComputableInPolyTime.cons' (hchallenge.comp houter.fst') hlast))
  have hpost : IsPPTOn (encPair (encPair input (encList sample)) (encList sample)) encBool
      (fun p => test p.1.1 (p.1.2 ++ challenge p.1.1 :: p.2)) := by
    simpa only [Function.comp_def] using htest.preprocess harg
  have hbody := hback.bind_with
    (second := fun p back => test p.1 (p.2 ++ challenge p.1 :: back)) hpost
  simpa only [spliceTest, Function.comp_def] using
    hfront.bind_with (second := fun a front => do
      let back ← OracleComp.replicate (after a) (original a)
      test a (front ++ challenge a :: back)) hbody

attribute [program_certificate] isPPTOn_spliceTest

/-- Random-coordinate hybrid reduction is uniformly strict PPT, including zero repetitions and
all rejected padding indices. -/
theorem isPPTOn_sequenceTest {Param : Type} {input : Param ↪ List Bool} {sample : α ↪ List Bool}
    {replacement original : Param → ProbComp α} {count : Param → ℕ}
    {test : Param → List α → ProbComp Bool} {challenge : Param → α}
    (hreplacement : IsPPTOn input sample replacement)
    (horiginal : IsPPTOn input sample original)
    (hcount : ComputableInPolyTime count input encUnary)
    (htest : IsPPTOn (encPair input (encList sample)) encBool
      (fun pair => test pair.1 pair.2))
    (hchallenge : ComputableInPolyTime challenge input sample) :
    IsPPTOn input encBool
      (fun a => sequenceTest (replacement a) (original a) (count a) (test a) (challenge a)) := by
  have hfirst := isPPTOn_sampleDyadicIndex hcount
  have ha := ComputableInPolyTime.fst input encUnary
  have hi := ComputableInPolyTime.snd input encUnary
  have htest' : IsPPTOn (encPair (encPair input encUnary) (encList sample)) encBool
      (fun p => test p.1.1 p.2) := htest.preprocess
    ((ComputableInPolyTime.fst (encPair input encUnary) (encList sample)).fst'.prod
      (ComputableInPolyTime.snd (encPair input encUnary) (encList sample)))
  have hafter := ComputableInPolyTime.unary_sub.comp
    ((ComputableInPolyTime.unary_sub.comp ((hcount.comp ha).prod hi)).prod
      (ComputableInPolyTime.const 1))
  have hsplice := isPPTOn_spliceTest (test := fun p : Param × ℕ => test p.1)
    (hreplacement.preprocess ha) (horiginal.preprocess ha)
    hi hafter htest' (hchallenge.comp ha)
  have hcond := ComputableInPolyTime.unary_lt' hi (hcount.comp ha)
  have hfalse : IsPPTOn (encPair input encUnary) encBool (fun _ => pure false) :=
    (ComputableInPolyTime.const false).isPPTOn
  have hbranch := IsPPTOn.ite hcond.tidy hsplice hfalse
  simpa only [sequenceTest, Function.comp_def] using hfirst.bind_with hbranch

attribute [program_certificate] isPPTOn_sequenceTest

/-- Repeating two computationally indistinguishable PPT samplers a polynomially bounded number of
times and applying an efficient postprocessor preserves computational indistinguishability. -/
theorem ComputationallyIndistinguishable.replicate_bind {orig repl : ℕ → ProbComp (List Bool)}
    (horig : IsPPTOn encUnary encBits orig) (hrepl : IsPPTOn encUnary encBits repl)
    (h : ComputationallyIndistinguishable
      (fun n => ProbComp.eval (orig n)) (fun n => ProbComp.eval (repl n)))
    {count : ℕ → ℕ} (hcount : ComputableInPolyTime count encUnary encUnary)
    {process : ℕ → List (List Bool) → ProbComp (List Bool)}
    (hprocess : IsPPTOn (encPair encUnary (encList encBits)) encBits
      (fun p => process p.1 p.2)) :
    ComputationallyIndistinguishable
      (fun n => ProbComp.eval (OracleComp.replicate (count n) (orig n) >>= process n))
      (fun n => ProbComp.eval (OracleComp.replicate (count n) (repl n) >>= process n)) := by
  have hcount := hcount.tidy
  intro adversary hadversary
  let test (n : ℕ) (xs : List (List Bool)) : ProbComp Bool := process n xs >>= adversary n
  have htest : IsPPTOn (encPair encUnary (encList encBits)) encBool
      (fun p => test p.1 p.2) := by
    dsimp only [test]
    ppt
  let red : Distinguisher := fun n challenge =>
    sequenceTest (repl n) (orig n) (count n) (test n) challenge
  have hred : IsPPT encBool red := by
    change IsPPTOn (encPair encUnary encBits) encBool (fun p => red p.1 p.2)
    dsimp only [red]
    ppt
  have hpoly : PolynomiallyBounded (fun n => dyadicSize (count n)) := by
    have hc : PolynomiallyBounded count := hcount.polynomiallyBounded
    fun_prop
  have hneg := (h red hred).polynomiallyBounded_mul hpoly
  refine negligible_of_le hneg (fun n => ?_)
  apply le_of_eq
  apply NNReal.eq
  dsimp only
  have hgap := sequenceTest_gap (repl n) (orig n) (count n) (test n)
  have horig_eq : distinguishingGame
      (ProbComp.eval (OracleComp.replicate (count n) (orig n) >>= process n)) (adversary n) =
      ProbComp.eval (OracleComp.replicate (count n) (orig n) >>= test n) := by
    simp only [distinguishingGame, PMF.monad_bind_eq_bind, test, ProbComp.eval_bind, PMF.bind_bind]
  have hrepl_eq : distinguishingGame
      (ProbComp.eval (OracleComp.replicate (count n) (repl n) >>= process n)) (adversary n) =
      ProbComp.eval (OracleComp.replicate (count n) (repl n) >>= test n) := by
    simp only [distinguishingGame, PMF.monad_bind_eq_bind, test, ProbComp.eval_bind, PMF.bind_bind]
  have hred_orig : distinguishingGame (ProbComp.eval (orig n)) (red n) =
      ProbComp.eval (orig n >>= sequenceTest (repl n) (orig n) (count n) (test n)) := by
    simp only [distinguishingGame, PMF.monad_bind_eq_bind, red, ProbComp.eval_bind]
  have hred_repl : distinguishingGame (ProbComp.eval (repl n)) (red n) =
      ProbComp.eval (repl n >>= sequenceTest (repl n) (orig n) (count n) (test n)) := by
    simp only [distinguishingGame, PMF.monad_bind_eq_bind, red, ProbComp.eval_bind]
  rw [horig_eq, hrepl_eq, hred_orig, hred_repl, NNReal.coe_mul, NNReal.coe_natCast,
    Game.coe_advantage, Game.coe_advantage, hgap, abs_mul, Nat.abs_cast]

end Cslib.Crypto
