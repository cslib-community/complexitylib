/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.OneWay
public import CslibFrontier.Crypto.Computational.PseudorandomGenerator
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Probabilistic.PPT.Extension
import CslibFrontier.Crypto.Negligible.Basic
import CslibFrontier.Probability.BitString
import CslibFrontier.Tactic.PPT

/-!
# Security against adversaries with advice

Nonuniform security lets every adversary read, besides the unary parameter `n` and its
challenge, an advice word `advice n` from an arbitrary family whose lengths are polynomially
bounded. The adversary itself is still one uniform strict PPT program, clocked on the whole
input, including the advice. This is the usual "PPT with polynomial advice" adversary class: the
family need not be computable, so it can hard-wire information about every parameter separately.

`NonuniformlyIndistinguishable`, `NonuniformOneWay` and `NonuniformPRG` relativize
`ComputationallyIndistinguishable`, `OneWay` and `PseudorandomGenerator` to this class. Each
uniform adversary is an advice adversary that ignores empty advice, so every nonuniform notion
implies its uniform counterpart. `IndistinguishableWithAdvice advice` and
`InversionHardWithAdvice f advice` fix one advice family; with empty advice they are exactly the
uniform notions, so a reduction proved relative to a fixed family yields both the uniform and the
nonuniform theorem. Moreover, an advice word may carry a value of any type under any encoding
(`IndistinguishableWithAdvice.negligible_encoded`,
`InversionHardWithAdvice.inversion_negligible_encoded`): an adversary need not decode its advice,
since it may run on the encoded word exactly as on the typed value.

These are definitions, not assertions that such primitives exist.

## Main definitions

* `Cslib.Crypto.encAdvisedInput`: the input encoding `((1ⁿ, advice), x)` of an adversary with
  advice.
* `Cslib.Crypto.IndistinguishableWithAdvice`: indistinguishability against uniform strict PPT
  tests given one fixed advice family.
* `Cslib.Crypto.NonuniformlyIndistinguishable`: indistinguishability with every polynomially
  bounded advice family.
* `Cslib.Crypto.InversionHardWithAdvice`: hardness of inversion against uniform strict PPT
  inverters given one fixed advice family.
* `Cslib.Crypto.NonuniformOneWay`: one-wayness against inverters given polynomially bounded
  advice.
* `Cslib.Crypto.NonuniformPRG`: a stretching generator whose output is nonuniformly
  indistinguishable from uniform.

## Main results

* `Cslib.Crypto.NonuniformlyIndistinguishable.refl`,
  `Cslib.Crypto.NonuniformlyIndistinguishable.symm`,
  `Cslib.Crypto.NonuniformlyIndistinguishable.trans`: an equivalence relation on ensembles.
* `Cslib.Crypto.NonuniformOneWay.of_inversion_negligible`: the inversion-probability constructor.
* `Cslib.Crypto.NonuniformlyIndistinguishable.computationallyIndistinguishable`,
  `Cslib.Crypto.NonuniformOneWay.toOneWay`, `Cslib.Crypto.NonuniformPRG.toPRG`: nonuniform
  security implies uniform security.
* `Cslib.Crypto.computationallyIndistinguishable_iff_indistinguishableWithAdvice_nil`: uniform
  indistinguishability is indistinguishability with empty advice.
* `Cslib.Crypto.IndistinguishableWithAdvice.map`: efficient postprocessing.
* `Cslib.Crypto.IndistinguishableWithAdvice.negligible_encoded`,
  `Cslib.Crypto.InversionHardWithAdvice.inversion_negligible_encoded`: advice of any encoded type.
* `Cslib.Crypto.oneWay_iff_inversionHardWithAdvice_nil`: uniform one-wayness is hardness of
  inversion with empty advice.
* `Cslib.Crypto.not_computationallyIndistinguishable_pure_uniformList`,
  `Cslib.Crypto.not_nonuniformlyIndistinguishable_pure_uniformList`: fixed words are
  distinguishable from uniform words, so the indistinguishability notions are not trivially true.

## References

* [O. Goldreich, *Foundations of Cryptography, Volume 1*][Goldreich2001], Sections 2.2 and 3.2.
-/

@[expose] public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM
open scoped NNReal ENNReal

/-- Input `((1ⁿ, advice), x)` of an adversary with advice: the parameter `n` in unary paired
with the advice word, then the challenge word `x`. The pair `(n, advice)` is framed, and within it
the parameter; `x` is not. -/
abbrev encAdvisedInput : (ℕ × List Bool) × List Bool ↪ List Bool :=
  encPair (encPair encUnary encBits) encBits

/-- A uniform adversary is an advice adversary that ignores its advice. -/
private theorem isPPTOn_dropAdvice {β : Type} {output : β ↪ List Bool}
    {adversary : ℕ → List Bool → ProbComp β} (h : IsPPT output adversary) :
    IsPPTOn encAdvisedInput output
      (fun input : (ℕ × List Bool) × List Bool => adversary input.1.1 input.2) :=
  h.on.preprocess (input := encPair (encPair encUnary encBits) encBits)
    (prepare := fun input : (ℕ × List Bool) × List Bool => (input.1.1, input.2)) (by fun_prop)

/-- Two ensembles are **indistinguishable with advice** `advice` when each uniform strict PPT
test reading the parameter `n`, the advice word `advice n` and a sample has negligible advantage.
The advice family is not bounded here; its length is charged to the test's clock, which is
polynomial in the length of its whole input, including the advice and the sample, as for
`ComputationallyIndistinguishable`: for ensembles of superpolynomial sample length the test gets
more than `poly(n)` time, unlike a polynomial-size circuit. With empty advice this is uniform
computational indistinguishability
(`computationallyIndistinguishable_iff_indistinguishableWithAdvice_nil`). -/
def IndistinguishableWithAdvice (advice : ℕ → List Bool) (X Y : ℕ → PMF (List Bool)) : Prop :=
  Game.Indistinguishable
    (fun (test : (ℕ × List Bool) × List Bool → ProbComp Bool) n =>
      distinguishingGame (X n) (fun word => test ((n, advice n), word)))
    (fun test n => distinguishingGame (Y n) (fun word => test ((n, advice n), word)))
    (IsPPTOn encAdvisedInput encBool)

/-- Two ensembles are **nonuniformly indistinguishable** when they are indistinguishable with
every polynomially bounded advice family. -/
def NonuniformlyIndistinguishable (X Y : ℕ → PMF (List Bool)) : Prop :=
  ∀ advice : ℕ → List Bool, PolynomiallyBounded (fun n => (advice n).length) →
    IndistinguishableWithAdvice advice X Y

/-- **Uniform indistinguishability is the empty-advice case.** A uniform test is an advice test
that ignores its advice, and an advice test run on empty advice is a uniform test. -/
theorem computationallyIndistinguishable_iff_indistinguishableWithAdvice_nil
    {X Y : ℕ → PMF (List Bool)} :
    ComputationallyIndistinguishable X Y ↔ IndistinguishableWithAdvice (fun _ => []) X Y := by
  constructor
  · intro h test htest
    have hprepare : ComputableInPolyTime (fun input : ℕ × List Bool => ((input.1, []), input.2))
        (encPair encUnary encBits) (encPair (encPair encUnary encBits) encBits) := by fun_prop
    exact h (fun n word => test ((n, []), word)) (htest.preprocess hprepare)
  · intro h adversary hadversary
    have hneg := h (fun input => adversary input.1.1 input.2) (isPPTOn_dropAdvice hadversary)
    simpa only using hneg

/-- Efficient parameter-dependent deterministic postprocessing preserves indistinguishability
with advice. -/
theorem IndistinguishableWithAdvice.map {advice : ℕ → List Bool} {X Y : ℕ → PMF (List Bool)}
    (h : IndistinguishableWithAdvice advice X Y) {f : ℕ → List Bool → List Bool}
    (hf : ComputableInPolyTime (fun (n, word) => f n word) (encPair encUnary encBits) encBits) :
    IndistinguishableWithAdvice advice (fun n => (X n).map (f n)) (fun n => (Y n).map (f n)) := by
  intro test htest
  have hprepare : ComputableInPolyTime
      (fun input : (ℕ × List Bool) × List Bool => (input.1, f input.1.1 input.2))
      (encPair (encPair encUnary encBits) encBits)
      (encPair (encPair encUnary encBits) encBits) := by
    have hpair : ComputableInPolyTime (fun input : (ℕ × List Bool) × List Bool =>
        (input.1.1, input.2)) (encPair (encPair encUnary encBits) encBits)
        (encPair encUnary encBits) := by fun_prop
    exact (ComputableInPolyTime.fst _ _).prod (hf.comp hpair)
  have hneg := h (fun input => test (input.1, f input.1.1 input.2)) (htest.preprocess hprepare)
  simpa only [distinguishingGame, PMF.monad_bind_eq_bind, PMF.bind_map, Function.comp_def]
    using hneg

/-- Every ensemble is nonuniformly indistinguishable from itself. -/
theorem NonuniformlyIndistinguishable.refl (X : ℕ → PMF (List Bool)) :
    NonuniformlyIndistinguishable X X := fun _ _ => Game.Indistinguishable.refl _ _

/-- Nonuniform indistinguishability is symmetric. -/
theorem NonuniformlyIndistinguishable.symm {X Y : ℕ → PMF (List Bool)}
    (h : NonuniformlyIndistinguishable X Y) : NonuniformlyIndistinguishable Y X :=
  fun advice hadvice => (h advice hadvice).symm

/-- Nonuniform indistinguishability composes through an intermediate ensemble. -/
theorem NonuniformlyIndistinguishable.trans {X Y Z : ℕ → PMF (List Bool)}
    (hXY : NonuniformlyIndistinguishable X Y) (hYZ : NonuniformlyIndistinguishable Y Z) :
    NonuniformlyIndistinguishable X Z :=
  fun advice hadvice => (hXY advice hadvice).trans (hYZ advice hadvice)

/-- Nonuniform indistinguishability implies uniform indistinguishability: a uniform test ignores
empty advice. -/
theorem NonuniformlyIndistinguishable.computationallyIndistinguishable
    {X Y : ℕ → PMF (List Bool)} (h : NonuniformlyIndistinguishable X Y) :
    ComputationallyIndistinguishable X Y :=
  computationallyIndistinguishable_iff_indistinguishableWithAdvice_nil.mpr
    (h _ (PolynomiallyBounded.const 0))

/-- **Advice of any encoded type.** Indistinguishability with the advice words
`encAdvice (advice n)` covers every uniform strict PPT test that reads the advice value
`advice n` itself, of an arbitrary type `γ` under an arbitrary encoding. The test need not be able
to decode the advice word: the proof runs its machine on that word
(`Cslib.Probability.IsPPTOn.exists_extension`). -/
theorem IndistinguishableWithAdvice.negligible_encoded {X Y : ℕ → PMF (List Bool)}
    {γ : Type} {encAdvice : γ ↪ List Bool} {advice : ℕ → γ}
    (h : IndistinguishableWithAdvice (fun n => encAdvice (advice n)) X Y)
    {test : (ℕ × γ) × List Bool → ProbComp Bool}
    (htest : IsPPTOn (encPair (encPair encUnary encAdvice) encBits) encBool test) :
    Negligible (fun n => Game.advantage
      (distinguishingGame (X n) (fun word => test ((n, advice n), word)))
      (distinguishingGame (Y n) (fun word => test ((n, advice n), word)))) := by
  obtain ⟨extension, hextension, heq⟩ :=
    htest.exists_extension (ComputableInPolyTime.headD false) (fun _ => rfl)
  have hword : IsPPTOn (encPair (encPair encUnary encBits) encBits) encBool
      (fun input => extension (encPair (encPair encUnary encBits) encBits input)) :=
    hextension.preprocess (ComputableInPolyTime.of_eq fun _ => rfl)
  have hkey (n : ℕ) (word : List Bool) :
      ProbComp.eval (extension (encPair (encPair encUnary encBits) encBits
        ((n, encAdvice (advice n)), word))) = ProbComp.eval (test ((n, advice n), word)) :=
    heq ((n, advice n), word)
  simpa only [distinguishingGame, hkey] using h _ hword

/-- **Fixed words are distinguishable from uniform words**, already by a uniform test: the first
bit of `PMF.pure (target n)` is constant, while that of a uniform word of positive length is a fair
coin. This needs no bound on `target`. -/
theorem not_computationallyIndistinguishable_pure_uniformList (target : ℕ → List Bool)
    {length : ℕ → ℕ} (hlength : ∀ᶠ n in Filter.atTop, 1 ≤ length n) :
    ¬ ComputationallyIndistinguishable (fun n => PMF.pure (target n))
      (fun n => BitString.uniformList (length n)) := by
  intro h
  have hfirst : IsPPT encBool (fun _ word => pure (word.headD false)) :=
    ((ComputableInPolyTime.headD false).comp (ComputableInPolyTime.snd encUnary encBits)).isPPTOn
  have hneg := h _ hfirst
  refine not_negligible_const (c := 1 / 2) (by norm_num) (negligible_of_eventually_le hneg ?_)
  filter_upwards [hlength] with n hn
  obtain ⟨m, hm⟩ : ∃ m, length n = m + 1 := ⟨length n - 1, by omega⟩
  have hreal : distinguishingGame (PMF.pure (target n)) (fun word => pure (word.headD false)) =
      PMF.pure ((target n).headD false) := by
    simp [distinguishingGame]
  have hideal : distinguishingGame (BitString.uniformList (length n))
      (fun word => pure (word.headD false)) = PMF.uniformOfFintype Bool := by
    rw [hm, BitString.uniformList_succ]
    simp [distinguishingGame, PMF.bind_map, Function.comp_def]
  rw [← NNReal.coe_le_coe, Game.coe_advantage, hreal, hideal]
  cases (target n).headD false <;> norm_num [Game.succProbability, ENNReal.toNNReal_ofNat]

/-- Nonuniform indistinguishability is not trivially true: fixed words are not nonuniformly
indistinguishable from uniform words (`not_computationallyIndistinguishable_pure_uniformList`). -/
theorem not_nonuniformlyIndistinguishable_pure_uniformList (target : ℕ → List Bool)
    {length : ℕ → ℕ} (hlength : ∀ᶠ n in Filter.atTop, 1 ≤ length n) :
    ¬ NonuniformlyIndistinguishable (fun n => PMF.pure (target n))
      (fun n => BitString.uniformList (length n)) := fun h =>
  not_computationallyIndistinguishable_pure_uniformList target hlength
    h.computationallyIndistinguishable

/-- **Inversion of `f` is hard with advice** `advice` when each uniform strict PPT inverter
reading the parameter `n`, the advice word `advice n` and the image of a uniform `n`-bit input has
negligible probability of finding any preimage. The advice family is not bounded here; its length
is charged to the inverter's clock. With empty advice this is the security condition of `OneWay`
(`oneWay_iff_inversionHardWithAdvice_nil`). -/
def InversionHardWithAdvice (f : List Bool → List Bool) (advice : ℕ → List Bool) : Prop :=
  Game.Indistinguishable
    (fun (adversary : (ℕ × List Bool) × List Bool → ProbComp (List Bool)) n =>
      ProbComp.eval (inversionGame f (fun n image => adversary ((n, advice n), image)) n))
    (fun _ _ => PMF.pure false) (IsPPTOn encAdvisedInput encBits)

/-- Each efficient inverter with the given advice has negligible success. -/
theorem InversionHardWithAdvice.inversion_negligible {f : List Bool → List Bool}
    {advice : ℕ → List Bool} (h : InversionHardWithAdvice f advice)
    (adversary : (ℕ × List Bool) × List Bool → ProbComp (List Bool))
    (hPPT : IsPPTOn encAdvisedInput encBits adversary) :
    Negligible (fun n => Game.succProbability (ProbComp.eval
      (inversionGame f (fun n image => adversary ((n, advice n), image)) n))) := by
  simpa only [Game.advantage_pure_false] using h adversary hPPT

/-- Establish hardness with advice by bounding every efficient inverter's success
probability. -/
theorem InversionHardWithAdvice.of_inversion_negligible {f : List Bool → List Bool}
    {advice : ℕ → List Bool}
    (h : ∀ adversary : (ℕ × List Bool) × List Bool → ProbComp (List Bool),
      IsPPTOn encAdvisedInput encBits adversary →
        Negligible (fun n => Game.succProbability (ProbComp.eval
          (inversionGame f (fun n image => adversary ((n, advice n), image)) n)))) :
    InversionHardWithAdvice f advice := fun adversary hPPT => by
  simpa only [Game.advantage_pure_false] using h adversary hPPT

/-- **Advice of any encoded type.** Hardness with the advice words `encAdvice (advice n)` covers
every uniform strict PPT inverter that reads the advice value `advice n` itself, of an arbitrary
type under an arbitrary encoding. -/
theorem InversionHardWithAdvice.inversion_negligible_encoded {f : List Bool → List Bool}
    {γ : Type} {encAdvice : γ ↪ List Bool} {advice : ℕ → γ}
    (h : InversionHardWithAdvice f (fun n => encAdvice (advice n)))
    {adversary : (ℕ × γ) × List Bool → ProbComp (List Bool)}
    (hPPT : IsPPTOn (encPair (encPair encUnary encAdvice) encBits) encBits adversary) :
    Negligible (fun n => Game.succProbability (ProbComp.eval
      (inversionGame f (fun n image => adversary ((n, advice n), image)) n))) := by
  obtain ⟨extension, hextension, heq⟩ :=
    hPPT.exists_extension (decode := id) (ComputableInPolyTime.of_eq fun _ => rfl) (fun _ => rfl)
  have hword : IsPPTOn (encPair (encPair encUnary encBits) encBits) encBits
      (fun input => extension (encPair (encPair encUnary encBits) encBits input)) :=
    hextension.preprocess (ComputableInPolyTime.of_eq fun _ => rfl)
  have hkey (n : ℕ) (image : List Bool) :
      ProbComp.eval (extension (encPair (encPair encUnary encBits) encBits
        ((n, encAdvice (advice n)), image))) = ProbComp.eval (adversary ((n, advice n), image)) :=
    heq ((n, advice n), image)
  have hgame (n : ℕ) :
      ProbComp.eval (inversionGame f (fun n image => extension
        (encPair (encPair encUnary encBits) encBits ((n, encAdvice (advice n)), image))) n) =
      ProbComp.eval (inversionGame f (fun n image => adversary ((n, advice n), image)) n) := by
    simp only [inversionGame, ProbComp.eval_bind, hkey]
  simpa only [hgame] using h.inversion_negligible _ hword

/-- **Uniform one-wayness is the empty-advice case.** A uniform inverter is an advice inverter
that ignores its advice, and an advice inverter run on empty advice is a uniform inverter. -/
theorem oneWay_iff_inversionHardWithAdvice_nil {f : List Bool → List Bool} :
    OneWay f ↔
      ComputableInPolyTime f encBits encBits ∧ InversionHardWithAdvice f (fun _ => []) := by
  constructor
  · intro h
    refine ⟨h.polyTime, .of_inversion_negligible fun adversary hPPT => ?_⟩
    have hprepare : ComputableInPolyTime (fun input : ℕ × List Bool => ((input.1, []), input.2))
        (encPair encUnary encBits) (encPair (encPair encUnary encBits) encBits) := by fun_prop
    exact h.inversion_negligible (fun n image => adversary ((n, []), image))
      (hPPT.preprocess hprepare)
  · rintro ⟨hf, h⟩
    refine OneWay.of_inversion_negligible hf fun adversary hPPT => ?_
    have hneg := h.inversion_negligible (fun input => adversary input.1.1 input.2)
      (isPPTOn_dropAdvice hPPT)
    simpa only using hneg

/-- A function is **nonuniformly one-way** when one deterministic polynomial-time algorithm
evaluates it and inversion is hard with every polynomially bounded advice family. -/
structure NonuniformOneWay (f : List Bool → List Bool) : Prop where
  /-- A deterministic polynomial-time algorithm evaluates the function. -/
  polyTime : ComputableInPolyTime f encBits encBits
  /-- With each polynomially bounded advice family, inversion is hard. -/
  secure : ∀ advice : ℕ → List Bool, PolynomiallyBounded (fun n => (advice n).length) →
    InversionHardWithAdvice f advice

/-- Each efficient inverter with polynomially bounded advice has negligible success. -/
theorem NonuniformOneWay.inversion_negligible {f : List Bool → List Bool}
    (h : NonuniformOneWay f) (adversary : (ℕ × List Bool) × List Bool → ProbComp (List Bool))
    (hPPT : IsPPTOn encAdvisedInput encBits adversary)
    {advice : ℕ → List Bool} (hadvice : PolynomiallyBounded (fun n => (advice n).length)) :
    Negligible (fun n => Game.succProbability (ProbComp.eval
      (inversionGame f (fun n image => adversary ((n, advice n), image)) n))) :=
  (h.secure advice hadvice).inversion_negligible adversary hPPT

/-- Establish nonuniform one-wayness by bounding the success probability of every efficient
inverter with polynomially bounded advice. -/
theorem NonuniformOneWay.of_inversion_negligible {f : List Bool → List Bool}
    (hf : ComputableInPolyTime f encBits encBits)
    (h : ∀ adversary : (ℕ × List Bool) × List Bool → ProbComp (List Bool),
      IsPPTOn encAdvisedInput encBits adversary →
      ∀ advice : ℕ → List Bool, PolynomiallyBounded (fun n => (advice n).length) →
        Negligible (fun n => Game.succProbability (ProbComp.eval
          (inversionGame f (fun n image => adversary ((n, advice n), image)) n)))) :
    NonuniformOneWay f :=
  ⟨hf, fun advice hadvice =>
    .of_inversion_negligible fun adversary hPPT => h adversary hPPT advice hadvice⟩

/-- Nonuniform one-wayness implies uniform one-wayness: a uniform inverter ignores empty
advice. -/
theorem NonuniformOneWay.toOneWay {f : List Bool → List Bool} (h : NonuniformOneWay f) :
    OneWay f :=
  oneWay_iff_inversionHardWithAdvice_nil.mpr ⟨h.polyTime, h.secure _ (PolynomiallyBounded.const 0)⟩

/-- A **nonuniform pseudorandom generator**: a plain polynomial-time generator with exact output
length `length`, strictly expanding every seed length, whose output on a uniform seed is
nonuniformly indistinguishable from a uniform word of the output length. -/
structure NonuniformPRG (generator : List Bool → List Bool) (length : ℕ → ℕ) : Prop where
  /-- One deterministic polynomial-time machine evaluates the generator. -/
  polyTime : ComputableInPolyTime generator encBits encBits
  /-- The output length depends only on the seed length. -/
  length_eq : ∀ word, (generator word).length = length word.length
  /-- Every seed length is strictly expanded. -/
  stretch : ∀ n, n < length n
  /-- Generated words are indistinguishable from uniform words with polynomially bounded advice. -/
  secure : NonuniformlyIndistinguishable (generatorEnsemble generator)
    (fun n => BitString.uniformList (length n))

/-- A nonuniform pseudorandom generator is a uniform pseudorandom generator. -/
theorem NonuniformPRG.toPRG {generator : List Bool → List Bool} {length : ℕ → ℕ}
    (h : NonuniformPRG generator length) : PseudorandomGenerator generator length :=
  .of_indistinguishable h.polyTime h.length_eq h.stretch
    h.secure.computationallyIndistinguishable

end Cslib.Crypto
