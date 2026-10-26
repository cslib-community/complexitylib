/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
public import Complexity.Computability.Probabilistic.Parameter
public import Complexity.Crypto.Game
import Complexity.Crypto.Negligible.Basic
import Complexity.Probability.PMF
import Complexity.Tactic.PPT

/-!
# Uniform computational indistinguishability

An ensemble supplies a distribution at each security parameter. A distinguisher is one strict
PPT program, given the unary parameter and a sample; its clock is polynomial in their combined
length. Ensembles need not themselves be efficiently sampleable or have polynomial sample lengths.
The distinguishing experiment is therefore a probability law, not an unrestricted sampling
primitive in the program language.

The negligible bound may depend on the adversary: one complete algorithm is fixed before
asserting decay. Semantic tests are admissible exactly when one such program realizes all their
distributions. Both presentations use the shared `Game.Indistinguishable` definition.

## Main definitions

* `Cslib.Crypto.IsPPTTest`: uniform realization of a family of randomized tests.
* `Cslib.Crypto.distinguishingGame`: give an ensemble sample to a program.
* `Cslib.Crypto.ComputationallyIndistinguishable`: security against every uniform strict PPT test.

## Main results

* `Cslib.Crypto.computationallyIndistinguishable_iff_tests`: equivalent semantic-test presentation.
* `Cslib.Crypto.ComputationallyIndistinguishable.bind`: efficient randomized postprocessing.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09], Chapter 9.
* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023], Section 3.2.

Adapted from Crypto/Computational/Basic.lean on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`, with arbitrary ensemble laws kept outside the program
syntax and the current upstream nonnegative game API.
-/

@[expose] public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM

/-- A distinguisher receives the unary security parameter and a sampled word. -/
abbrev Distinguisher := ℕ → List Bool → ProbComp Bool

/-- One uniform strict PPT algorithm realizes the whole family of randomized tests. -/
def IsPPTTest (test : ℕ → List Bool → PMF Bool) : Prop :=
  ∃ program : Distinguisher, IsPPT encBool program ∧
    ∀ n input, ProbComp.eval (program n input) = test n input

/-- Interpreting a program preserves exactly its uniform PPT restriction. -/
@[simp] theorem isPPTTest_eval {adversary : Distinguisher} :
    IsPPTTest (fun n input => ProbComp.eval (adversary n input)) ↔ IsPPT encBool adversary := by
  constructor
  · rintro ⟨program, h, heq⟩
    exact h.congr heq
  · exact fun h => ⟨adversary, h, fun _ _ => rfl⟩

/-- Give a sample from a distribution to a distinguisher; this law assumes no efficient sampler. -/
noncomputable def distinguishingGame (distribution : PMF (List Bool))
    (adversary : List Bool → ProbComp Bool) : Game := do
  let word ← distribution
  ProbComp.eval (adversary word)

/-- An actual sampler followed by a distinguisher realizes the corresponding experiment. -/
theorem eval_bind_eq_distinguishingGame (sample : ProbComp (List Bool))
    (adversary : List Bool → ProbComp Bool) :
    ProbComp.eval (sample >>= adversary) = distinguishingGame (ProbComp.eval sample) adversary :=
  ProbComp.eval_bind _ _

/-- Postprocessing the distinguisher's answer postprocesses the experiment's answer. -/
theorem distinguishingGame_map (distribution : PMF (List Bool))
    (adversary : List Bool → ProbComp Bool) (f : Bool → Bool) :
    distinguishingGame distribution (fun word => f <$> adversary word) =
      (distinguishingGame distribution adversary).map f := by
  simp only [distinguishingGame, PMF.monad_bind_eq_bind, ProbComp.eval_map, PMF.map_bind]

/-- Each uniform strict PPT distinguisher has negligible advantage between the two ensembles.
Neither ensemble is required to be efficiently sampleable or polynomially bounded in length. -/
def ComputationallyIndistinguishable (X Y : ℕ → PMF (List Bool)) : Prop :=
  Game.Indistinguishable
    (fun adversary n => distinguishingGame (X n) (adversary n))
    (fun adversary n => distinguishingGame (Y n) (adversary n)) (IsPPT encBool)

/-- Program distinguishers and uniformly realizable semantic tests give the same notion. -/
theorem computationallyIndistinguishable_iff_tests {X Y : ℕ → PMF (List Bool)} :
    ComputationallyIndistinguishable X Y ↔
      Game.Indistinguishable (fun test n => (X n).bind (test n))
        (fun test n => (Y n).bind (test n)) IsPPTTest := by
  constructor
  · rintro h test ⟨program, hprogram, heq⟩
    simpa only [distinguishingGame, PMF.monad_bind_eq_bind, heq] using h program hprogram
  · intro h adversary hadversary
    exact h (fun n input => ProbComp.eval (adversary n input)) (isPPTTest_eval.mpr hadversary)

/-- An ensemble is computationally indistinguishable from itself. -/
theorem ComputationallyIndistinguishable.refl (X : ℕ → PMF (List Bool)) :
    ComputationallyIndistinguishable X X := Game.Indistinguishable.refl _ _

/-- Swapping the ensembles preserves computational indistinguishability. -/
theorem ComputationallyIndistinguishable.symm {X Y : ℕ → PMF (List Bool)}
    (h : ComputationallyIndistinguishable X Y) : ComputationallyIndistinguishable Y X :=
  Game.Indistinguishable.symm h

/-- A two-hop hybrid argument uses the same uniform distinguisher in both hops. -/
theorem ComputationallyIndistinguishable.trans {X Y Z : ℕ → PMF (List Bool)}
    (hXY : ComputationallyIndistinguishable X Y) (hYZ : ComputationallyIndistinguishable Y Z) :
    ComputationallyIndistinguishable X Z := Game.Indistinguishable.trans hXY hYZ

/-- Efficient randomized postprocessing preserves computational indistinguishability. -/
theorem ComputationallyIndistinguishable.bind {X Y : ℕ → PMF (List Bool)}
    (h : ComputationallyIndistinguishable X Y) {process : ℕ → List Bool → ProbComp (List Bool)}
    (hprocess : IsPPT encBits process) :
    ComputationallyIndistinguishable
      (fun n => (X n).bind (fun word => ProbComp.eval (process n word)))
      (fun n => (Y n).bind (fun word => ProbComp.eval (process n word))) := by
  intro adversary hadversary
  have hefficient : IsPPT encBool (fun n word => do
      let result ← process n word
      adversary n result) := by ppt
  simpa only [distinguishingGame, PMF.monad_bind_eq_bind, ProbComp.eval_bind,
    PMF.bind_bind] using h _ hefficient

/-- Efficient parameter-dependent deterministic postprocessing preserves indistinguishability. -/
theorem ComputationallyIndistinguishable.map {X Y : ℕ → PMF (List Bool)}
    (h : ComputationallyIndistinguishable X Y) {f : ℕ → List Bool → List Bool}
    (hf : ComputableInPolyTime (fun p : ℕ × List Bool => f p.1 p.2)
      (encPair encUnary encBits) encBits) :
    ComputationallyIndistinguishable (fun n => (X n).map (f n)) (fun n => (Y n).map (f n)) := by
  have hp : IsPPT encBits (fun n word => pure (f n word)) := by ppt
  simpa only [ProbComp.eval_pure, PMF.map, Function.comp_def] using h.bind hp

/-- Shifting the security parameter by a fixed additive offset preserves computational
indistinguishability. -/
theorem ComputationallyIndistinguishable.shift {X Y : ℕ → PMF (List Bool)}
    (h : ComputationallyIndistinguishable X Y) (c : ℕ) :
    ComputationallyIndistinguishable (fun n => X (n + c)) (fun n => Y (n + c)) := by
  intro adversary hadversary
  have hadv' : IsPPT encBool (fun m word => adversary (m - c) word) :=
    hadversary.preprocess (by fun_prop) (by fun_prop)
  have hneg := (h (fun m word => adversary (m - c) word) hadv').shift c
  simpa only [Game.advantage, Nat.add_sub_cancel] using hneg

end Cslib.Crypto
