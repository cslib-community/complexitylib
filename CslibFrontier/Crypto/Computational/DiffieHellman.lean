/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.DiffieHellman.Finite
public import CslibFrontier.Computability.Probabilistic.UniformNat
public import CslibFrontier.Crypto.Computational.DiscreteLog
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
public import CslibFrontier.Crypto.Game.Statistical
public import CslibFrontier.Languages.Probabilistic.BitString
public import CslibFrontier.Languages.Probabilistic.Repeat
public import CslibFrontier.Languages.Probabilistic.UniformNat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Probabilistic.PPT.Capture
import CslibFrontier.Computability.Probabilistic.PPT.Extension
import CslibFrontier.Computability.Probabilistic.Repeat
import CslibFrontier.Crypto.Negligible.Basic
import CslibFrontier.Foundations.Data.Nat.Bits
import CslibFrontier.Languages.Probabilistic.Concentration
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF
import CslibFrontier.Probability.PMF.Uniform
import CslibFrontier.Probability.Uniform
import CslibFrontier.Tactic.GameHop
import CslibFrontier.Tactic.Negligible
import CslibFrontier.Tactic.PolyTime.Init
import Mathlib.FieldTheory.Finite.Basic
import CslibFrontier.Probability.PMF.EventBind
import CslibFrontier.Probability.PMF.Bind

/-!
# The Computational and Decisional Diffie–Hellman assumptions

Over a `PrimeOrderGroupFamily`, the Computational Diffie–Hellman (CDH) game ([BonehShoup2023],
Attack Game 10.5) draws public group parameters `d` from a setup law and runs the fixed-group
experiment `Cslib.Crypto.cdhExperiment` in `F.Carrier d`: the adversary receives `a • g` and `b • g`
(the textbook `g^a` and `g^b`) and wins when it outputs `(a * b) • g`. The Decisional
Diffie–Hellman (DDH) games ([BonehShoup2023], Attack Game 10.6) likewise run
`Cslib.Crypto.ddhRealExperiment` and `Cslib.Crypto.ddhRandomExperiment`.

Adversaries receive and return group elements. Their efficiency is stated on encodings:
`CDHAdversary.IsPPT` and `DDHDistinguisher.IsPPT` ask for one uniform strict PPT machine that reads
`encCDHInput` or `encDDHInput` (the unary security parameter, group parameters and encoded
elements) and writes the encoding of the adversary's output. `encCDHInput_apply` and
`encDDHInput_apply` give the word layouts.

A distinguisher outputs a bit, so `DDH` is the same assumption as its word-level form over
distinguishers that read the encoded tuple (`ddh_iff_encoded`). A CDH adversary must output a group
element, whereas a word-level adversary may output any word. `CDH`, and hence the conclusion of
`DDH.cdh`, is therefore the textbook assumption, which is weaker than the word-level CDH assumption;
[#4783](https://github.com/cslib-community/cslib-frontier/issues/4783) tracks restoring the
word-level form for families with decodable encodings.

We prove the implications `DDH ⇒ CDH ⇒ DiscreteLog` between the assumptions from the fixed-group
bounds `Cslib.Crypto.dlAdvantage_le_cdhAdvantage_dlToCDH` and
`Cslib.Crypto.probability_ddhRandomExperiment_cdhToDDH_le`. We also prove the random
self-reducibility of DDH ([BonehShoup2023], Section 10.11, Exercises 10.8–10.10, pp. 425–426): the
distributional rerandomisation lemma (`ddhRerandomizeLaw_real`, `ddhRerandomizeLaw_random`), its
efficient form `ddhSelfReduceDistinguisher`, the equivalence of average-case and worst-case DDH
(`ddh_of_worstCase`), and a Chernoff-amplified decider `ddhAmplifiedDecider` that turns a
distinguisher with inverse-polynomial advantage into one that decides every triple except with
negligible error. The Diffie–Hellman assumptions are hypotheses, not theorems.

## Main definitions

* `Cslib.Crypto.PrimeOrderGroupFamily.CDHInput`, `Cslib.Crypto.PrimeOrderGroupFamily.DDHInput`:
  the inputs of CDH adversaries and DDH distinguishers.
* `Cslib.Crypto.PrimeOrderGroupFamily.encCDHInput`,
  `Cslib.Crypto.PrimeOrderGroupFamily.encDDHInput`: their encodings, with layouts given by the
  generated `encCDHInput_apply` and `encDDHInput_apply`.
* `Cslib.Crypto.PrimeOrderGroupFamily.CDHAdversary`,
  `Cslib.Crypto.PrimeOrderGroupFamily.CDHAdversary.IsPPT`,
  `Cslib.Crypto.PrimeOrderGroupFamily.cdhGame`, `Cslib.Crypto.PrimeOrderGroupFamily.CDH`: the
  Computational Diffie–Hellman game and assumption.
* `Cslib.Crypto.PrimeOrderGroupFamily.dlToCDHAdversary`: the reduction from discrete logarithm to
  CDH.
* `Cslib.Crypto.PrimeOrderGroupFamily.DDHDistinguisher`,
  `Cslib.Crypto.PrimeOrderGroupFamily.DDHDistinguisher.IsPPT`,
  `Cslib.Crypto.PrimeOrderGroupFamily.ddhRealGame`,
  `Cslib.Crypto.PrimeOrderGroupFamily.ddhRandomGame`, `Cslib.Crypto.PrimeOrderGroupFamily.DDH`:
  the real and random Decisional Diffie–Hellman games and assumption.
* `Cslib.Crypto.PrimeOrderGroupFamily.cdhToDDHDistinguisher`: the reduction from CDH to DDH.
* `Cslib.Crypto.PrimeOrderGroupFamily.ddhRerandomize`,
  `Cslib.Crypto.PrimeOrderGroupFamily.ddhRerandomizeLaw`: DDH triple rerandomisation
  ([BonehShoup2023], Exercises 10.8–10.9, pp. 425–426).
* `Cslib.Crypto.PrimeOrderGroupFamily.sampleExp`: approximate uniform exponent sampling modulo
  `F.order d` via `ProbComp.sampleModNat` with statistical distance at most `1 / 2 ^ n`.
* `Cslib.Crypto.PrimeOrderGroupFamily.ddhSelfReduceDistinguisher`: the efficient DDH random
  self-reduction.
* `Cslib.Crypto.PrimeOrderGroupFamily.ddhRerandomizeGame`,
  `Cslib.Crypto.PrimeOrderGroupFamily.ddhWorstCaseGame`: rerandomised and worst-case DDH games on
  fixed triple families.
* `Cslib.Crypto.PrimeOrderGroupFamily.ddhAmplifiedDecider`: the Chernoff-amplified worst-case DDH
  decider ([BonehShoup2023], Exercise 10.10, p. 426).

## Main results

* `Cslib.Crypto.PrimeOrderGroupFamily.ddh_iff_encoded`: `DDH` is the word-level DDH assumption.
* `Cslib.Crypto.PrimeOrderGroupFamily.succProbability_discreteLogGame_le_cdhGame`,
  `Cslib.Crypto.PrimeOrderGroupFamily.CDH.discreteLog`: `CDH` implies `DiscreteLog`.
* `Cslib.Crypto.PrimeOrderGroupFamily.succProbability_cdhGame_le_advantage_ddh_add`,
  `Cslib.Crypto.PrimeOrderGroupFamily.DDH.cdh`,
  `Cslib.Crypto.PrimeOrderGroupFamily.DDH.discreteLog`: `DDH` implies `CDH` and `DiscreteLog`
  when `1 / q` is negligible.
* `Cslib.Crypto.PrimeOrderGroupFamily.ddhRerandomizeLaw_real`,
  `Cslib.Crypto.PrimeOrderGroupFamily.ddhRerandomizeLaw_random`: the distributional rerandomisation
  lemma for DDH tuples ([BonehShoup2023], Exercises 10.8–10.9, pp. 425–426).
* `Cslib.Crypto.PrimeOrderGroupFamily.isPPT_ddhSelfReduceDistinguisher`,
  `Cslib.Crypto.PrimeOrderGroupFamily.advantage_ddhRerandomizeLaw_ddhSelfReduceDistinguisher_le`:
  the self-reduction is PPT and loses at most `3 / 2 ^ n` against exact rerandomisation.
* `Cslib.Crypto.PrimeOrderGroupFamily.DDH.ddhRerandomizeGame`,
  `Cslib.Crypto.PrimeOrderGroupFamily.advantage_ddhRealGame_le_ddhWorstCaseGame`,
  `Cslib.Crypto.PrimeOrderGroupFamily.ddh_of_worstCase`: average-case and worst-case DDH agree.
* `Cslib.Crypto.PrimeOrderGroupFamily.isPPT_ddhAmplifiedDecider`,
  `Cslib.Crypto.PrimeOrderGroupFamily.ddhAmplifiedDecider_error_le_pow`,
  `Cslib.Crypto.PrimeOrderGroupFamily.negligible_ddhAmplifiedDecider_error`: the amplified
  decider is PPT and errs on every triple with probability at most `(1 / 2) ^ n`.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Section 10.5 (Attack Games 10.5–10.6, pp. 409–410) and
  Section 10.11 (Exercises 10.7–10.10, pp. 425–426).
-/

@[expose] public section

namespace Cslib.Crypto.PrimeOrderGroupFamily

open Probability Turing.MultiTapeTM
open scoped ENNReal NNReal Cslib.Probability.PMF

variable (F : PrimeOrderGroupFamily)

/-! ### Adversary inputs and their encodings -/

/-- The input of a CDH adversary: the security parameter, public group parameters `d` and two
elements of `F.Carrier d`, which are `a • g` and `b • g` in the experiment. -/
structure CDHInput where
  /-- The security parameter, given to machines in unary. -/
  secParam : ℕ
  /-- Public parameters selecting the group, its prime order and generator within the family.
  For Schnorr groups these contain the modulus `p`, subgroup order `q` and generator `g`. -/
  groupParameters : F.Desc
  /-- The first public element, `a • g` in the experiment. -/
  leftPublic : F.Carrier groupParameters
  /-- The second public element, `b • g` in the experiment. -/
  rightPublic : F.Carrier groupParameters

/-- The input of a DDH distinguisher: a CDH input and a candidate shared element, which is
`(a * b) • g` in the real experiment and an independent `c • g` in the random one. -/
structure DDHInput extends F.CDHInput where
  /-- The candidate shared element. -/
  candidateShared : F.Carrier groupParameters

/-- The encoding of a CDH input: the unary security parameter, the group parameters and the words
`F.encode d u`, `F.encode d v` of the public elements, each framed except the last
(`encCDHInput_apply`). -/
enc_structure encCDHInput (F : PrimeOrderGroupFamily) : CDHInput F where
  secParam : encUnary, groupParameters : F.encDesc,
  leftPublic : (F.encode groupParameters) using (F.encode_injective groupParameters),
  rightPublic : (F.encode groupParameters) using (F.encode_injective groupParameters)

/-- The encoding of a DDH input: the fields of its CDH input followed by the word of the candidate
shared element, each framed except the last (`encDDHInput_apply`). -/
enc_structure encDDHInput (F : PrimeOrderGroupFamily) : DDHInput F
    flattened toCDHInput : (F.encCDHInput) where
  secParam : encUnary, groupParameters : F.encDesc,
  leftPublic : (F.encode groupParameters) using (F.encode_injective groupParameters),
  rightPublic : (F.encode groupParameters) using (F.encode_injective groupParameters),
  candidateShared : (F.encode groupParameters) using (F.encode_injective groupParameters)

variable {F} in
/-- The encoded generator of computed group parameters. -/
@[fun_prop] theorem computableInPolyTime_encode_generator {α : Type} {enc : α ↪ List Bool}
    {d : α → F.Desc} (hd : ComputableInPolyTime d enc F.encDesc) :
    ComputableInPolyTime (fun a => F.encode (d a) (F.generator (d a))) enc encBits :=
  F.computableInPolyTime_generator.comp hd

variable {F} in
/-- The encoded identity of computed group parameters, computed as `0 • g`. -/
@[fun_prop] theorem computableInPolyTime_encode_zero {α : Type} {enc : α ↪ List Bool}
    {d : α → F.Desc} (hd : ComputableInPolyTime d enc F.encDesc) :
    ComputableInPolyTime (fun a => F.encode (d a) 0) enc encBits :=
  .of_enc_eq (F.computableInPolyTime_smul.comp
      (hd.prod ((ComputableInPolyTime.const 0).prod (computableInPolyTime_encode_generator hd))))
    fun a => by simp [F.smul_encode]

variable {F} in
/-- The encoded sum of computed elements. -/
@[fun_prop] theorem computableInPolyTime_encode_add {α : Type} {enc : α ↪ List Bool}
    {d : α → F.Desc} {x y : (a : α) → F.Carrier (d a)} (hd : ComputableInPolyTime d enc F.encDesc)
    (hx : ComputableInPolyTime (fun a => F.encode (d a) (x a)) enc encBits)
    (hy : ComputableInPolyTime (fun a => F.encode (d a) (y a)) enc encBits) :
    ComputableInPolyTime (fun a => F.encode (d a) (x a + y a)) enc encBits :=
  .of_enc_eq (F.computableInPolyTime_add.comp (hd.prod (hx.prod hy))) fun a => by
    simp [F.add_encode]

variable {F} in
/-- The encoded multiple of a computed element by a computed natural number. -/
@[fun_prop] theorem computableInPolyTime_encode_natCast_smul {α : Type} {enc : α ↪ List Bool}
    {d : α → F.Desc} {k : α → ℕ} {x : (a : α) → F.Carrier (d a)}
    (hd : ComputableInPolyTime d enc F.encDesc) (hk : ComputableInPolyTime k enc encNat)
    (hx : ComputableInPolyTime (fun a => F.encode (d a) (x a)) enc encBits) :
    ComputableInPolyTime (fun a => F.encode (d a) ((k a : ZMod (F.order (d a))) • x a)) enc
      encBits :=
  .of_enc_eq (F.computableInPolyTime_smul.comp (hd.prod (hk.prod hx))) fun a => by
    simp [F.smul_encode]

/-! ### Computational Diffie–Hellman (CDH) -/

/-- A CDH adversary over the family: given the security parameter, public group parameters `d`
and two elements of `F.Carrier d`, it outputs an element of `F.Carrier d`. `CDHAdversary.IsPPT`
states its efficiency on encodings. -/
abbrev CDHAdversary : Type :=
  ℕ → (d : F.Desc) → F.Carrier d → F.Carrier d → ProbComp (F.Carrier d)

variable {F} in
/-- A CDH adversary is PPT when one uniform strict PPT machine reads `encCDHInput` and writes the
encoding of the adversary's output element. -/
def CDHAdversary.IsPPT (adversary : F.CDHAdversary) : Prop :=
  IsPPTOn F.encCDHInput encBits fun x => F.encode x.groupParameters <$>
    adversary x.secParam x.groupParameters x.leftPublic x.rightPublic

/-- The Computational Diffie–Hellman experiment ([BonehShoup2023], Attack Game 10.5): choose
group parameters `d` using the arbitrary setup law, then run `Cslib.Crypto.cdhExperiment` in the
group `F.Carrier d`. No efficient sampler for setup is required. -/
noncomputable def cdhGame (setup : ℕ → PMF F.Desc) (adversary : F.CDHAdversary) (n : ℕ) :
    Game :=
  Game.withSetup (setup n) fun d => cdhExperiment (F.order d) (F.generator d) (adversary n d)

/-- The Computational Diffie–Hellman assumption for a family and a setup law: every PPT CDH
adversary wins `cdhGame` with negligible probability. -/
def CDH (setup : ℕ → PMF F.Desc) : Prop :=
  ∀ adversary : F.CDHAdversary, adversary.IsPPT →
    Negligible fun n => Game.succProbability (F.cdhGame setup adversary n)

/-- The fixed-group discrete-logarithm adversary run by a word-level one: encode the instance,
run the word-level adversary and read its output as a binary exponent, as `discreteLogGame`
does. -/
noncomputable def discreteLogAdversary
    (adversary : ℕ → F.Desc × List Bool → ProbComp (List Bool)) (n : ℕ) (d : F.Desc)
    (u : F.Carrier d) : ProbComp (ZMod (F.order d)) :=
  (fun guess => (ofBits guess : ZMod (F.order d))) <$> adversary n (d, F.encode d u)

/-- `discreteLogGame` averages `Cslib.Crypto.dlExperiment` of `discreteLogAdversary` over the
setup law. -/
theorem discreteLogGame_eq (setup : ℕ → PMF F.Desc)
    (adversary : ℕ → F.Desc × List Bool → ProbComp (List Bool)) (n : ℕ) :
    F.discreteLogGame setup adversary n = Game.withSetup (setup n) fun d =>
      dlExperiment (F.order d) (F.generator d) (F.discreteLogAdversary adversary n d) := by
  simp [discreteLogGame, Game.withSetup, dlExperiment, discreteLogAdversary, PMF.map,
    Function.comp_def]

/-- Turn a word-level discrete-logarithm adversary into a CDH adversary: run
`Cslib.Crypto.dlToCDH` on its `discreteLogAdversary`. -/
noncomputable def dlToCDHAdversary
    (adversary : ℕ → F.Desc × List Bool → ProbComp (List Bool)) : F.CDHAdversary :=
  fun n d => dlToCDH (F.discreteLogAdversary adversary n d)

/-- Whenever the discrete-logarithm adversary recovers `α`, `dlToCDHAdversary` outputs the
Diffie–Hellman shared element. -/
theorem succProbability_discreteLogGame_le_cdhGame (setup : ℕ → PMF F.Desc)
    (adversary : ℕ → F.Desc × List Bool → ProbComp (List Bool)) (n : ℕ) :
    Game.succProbability (F.discreteLogGame setup adversary n) ≤
      Game.succProbability (F.cdhGame setup (F.dlToCDHAdversary adversary) n) := by
  rw [discreteLogGame_eq]
  refine Game.succProbability_mono (PMF.bind_apply_mono_on_support _ _ fun d _ => ?_)
  exact (ENNReal.toNNReal_le_toNNReal (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
    (dlAdvantage_le_cdhAdvantage_dlToCDH _ _ _)

/-- The discrete-logarithm-to-CDH reduction is uniform strict PPT when the discrete-logarithm
adversary is. -/
theorem isPPT_dlToCDHAdversary
    {adversary : ℕ → F.Desc × List Bool → ProbComp (List Bool)}
    (hA : IsPPTOn (encPair encUnary (encPair F.encDesc encBits)) encBits
      (fun input => adversary input.1 input.2)) :
    (F.dlToCDHAdversary adversary).IsPPT := by
  refine ((hA.preprocess (prepare := fun x : F.CDHInput =>
      (x.secParam, x.groupParameters, F.encode x.groupParameters x.leftPublic))
      (by fun_prop)).map_with
    (f := fun x guess => F.smul (x.groupParameters, ofBits guess,
      F.encode x.groupParameters x.rightPublic))
    (F.computableInPolyTime_smul.comp (by fun_prop))).congr fun x => ?_
  simp [dlToCDHAdversary, dlToCDH, discreteLogAdversary, F.smul_encode]

/-- **CDH implies the discrete-logarithm assumption**. -/
theorem CDH.discreteLog {F : PrimeOrderGroupFamily} {setup : ℕ → PMF F.Desc} (h : F.CDH setup) :
    F.DiscreteLog setup := by
  intro adversary hA
  have hcdh := h _ (F.isPPT_dlToCDHAdversary hA)
  negligible using F.succProbability_discreteLogGame_le_cdhGame setup adversary

/-! ### Decisional Diffie–Hellman (DDH) -/

/-- A DDH distinguisher over the family: given the security parameter, public group parameters
`d` and three elements of `F.Carrier d`, it outputs a bit. `DDHDistinguisher.IsPPT` states its
efficiency on encodings. -/
abbrev DDHDistinguisher : Type :=
  ℕ → (d : F.Desc) → F.Carrier d → F.Carrier d → F.Carrier d → ProbComp Bool

variable {F} in
/-- A DDH distinguisher is PPT when one uniform strict PPT machine reads `encDDHInput` and writes
the distinguisher's output bit. -/
def DDHDistinguisher.IsPPT (distinguisher : F.DDHDistinguisher) : Prop :=
  IsPPTOn F.encDDHInput encBool fun x =>
    distinguisher x.secParam x.groupParameters x.leftPublic x.rightPublic x.candidateShared

/-- The real DDH game ([BonehShoup2023], Attack Game 10.6, Experiment 0): choose group parameters
`d` using the arbitrary setup law, then run `Cslib.Crypto.ddhRealExperiment` in `F.Carrier d`. -/
noncomputable def ddhRealGame (setup : ℕ → PMF F.Desc) (distinguisher : F.DDHDistinguisher)
    (n : ℕ) : Game :=
  Game.withSetup (setup n) fun d =>
    ddhRealExperiment (F.order d) (F.generator d) (distinguisher n d)

/-- The random DDH game ([BonehShoup2023], Attack Game 10.6, Experiment 1): choose group
parameters `d` using the arbitrary setup law, then run `Cslib.Crypto.ddhRandomExperiment` in
`F.Carrier d`. -/
noncomputable def ddhRandomGame (setup : ℕ → PMF F.Desc) (distinguisher : F.DDHDistinguisher)
    (n : ℕ) : Game :=
  Game.withSetup (setup n) fun d =>
    ddhRandomExperiment (F.order d) (F.generator d) (distinguisher n d)

/-- The Decisional Diffie–Hellman assumption for a family and a setup law: every PPT DDH
distinguisher has negligible advantage between `ddhRealGame` and `ddhRandomGame`. -/
def DDH (setup : ℕ → PMF F.Desc) : Prop :=
  Game.Indistinguishable (F.ddhRealGame setup) (F.ddhRandomGame setup)
    DDHDistinguisher.IsPPT

variable {F} in
/-- A PPT DDH distinguisher run on computed inputs is uniform strict PPT. -/
theorem DDHDistinguisher.IsPPT.comp {distinguisher : F.DDHDistinguisher}
    (hD : distinguisher.IsPPT)
    {α : Type} {enc : α ↪ List Bool} {n : α → ℕ} {d : α → F.Desc}
    {u v w : (a : α) → F.Carrier (d a)} (hn : ComputableInPolyTime n enc encUnary)
    (hd : ComputableInPolyTime d enc F.encDesc)
    (hu : ComputableInPolyTime (fun a => F.encode (d a) (u a)) enc encBits)
    (hv : ComputableInPolyTime (fun a => F.encode (d a) (v a)) enc encBits)
    (hw : ComputableInPolyTime (fun a => F.encode (d a) (w a)) enc encBits) :
    IsPPTOn enc encBool fun a => distinguisher (n a) (d a) (u a) (v a) (w a) :=
  IsPPTOn.preprocess hD (F.encDDHInput_mk_polyTime hn hd hu hv hw)

/-- **`DDH` is the word-level DDH assumption.** Quantifying over distinguishers that read the
encoded tuple `(1ⁿ, d, encode u, encode v, encode w)` as words, each with one uniform strict PPT
machine on its flat layout, gives the same assumption as quantifying over typed distinguishers.
A typed distinguisher's machine reads exactly that layout; conversely, a word distinguisher is
typed by encoding its elements, and a typed one is a word distinguisher on that layout run on the
encoded elements (`IsPPTOn.exists_bool_factor`), since its output is a single bit. -/
theorem ddh_iff_encoded (setup : ℕ → PMF F.Desc) :
    F.DDH setup ↔ ∀ W : ℕ → F.Desc × List Bool × List Bool × List Bool → ProbComp Bool,
      IsPPTOn (encPair encUnary (encPair F.encDesc (encPair encBits (encPair encBits encBits))))
        encBool (fun x => W x.1 x.2) →
      Negligible fun n => Game.advantage
        (F.ddhRealGame setup (fun n d u v w => W n (d, F.encode d u, F.encode d v, F.encode d w)) n)
        (F.ddhRandomGame setup
          (fun n d u v w => W n (d, F.encode d u, F.encode d v, F.encode d w)) n) := by
  constructor
  · intro h W hW
    exact h _ (hW.preprocess (prepare := fun x : F.DDHInput => (x.secParam, x.groupParameters,
      F.encode _ x.leftPublic, F.encode _ x.rightPublic, F.encode _ x.candidateShared))
      (by fun_prop))
  · intro h D hD
    obtain ⟨W, hW, hWD⟩ := hD.exists_bool_factor F.encDDHInput_apply
    obtain rfl : D = fun n d u v w => W (n, d, F.encode d u, F.encode d v, F.encode d w) :=
      funext₂ fun n d => funext₃ fun u v w => hWD ⟨⟨n, d, u, v⟩, w⟩
    exact h (fun n t => W (n, t)) hW

/-- Turn a CDH adversary into a DDH distinguisher by running `Cslib.Crypto.cdhToDDH` in each
group. -/
def cdhToDDHDistinguisher (adversary : F.CDHAdversary) : F.DDHDistinguisher :=
  fun n d => cdhToDDH (adversary n d)

/-- In the real DDH game, `cdhToDDHDistinguisher` runs the CDH game. -/
@[simp] theorem ddhRealGame_cdhToDDHDistinguisher (setup : ℕ → PMF F.Desc)
    (adversary : F.CDHAdversary) (n : ℕ) :
    F.ddhRealGame setup (F.cdhToDDHDistinguisher adversary) n = F.cdhGame setup adversary n :=
  rfl

/-- In the random DDH game, `cdhToDDHDistinguisher` accepts with probability at most `1 / m`
whenever every supported group order is at least `m > 0`. -/
theorem succProbability_ddhRandomGame_cdhToDDHDistinguisher_le (setup : ℕ → PMF F.Desc)
    (adversary : F.CDHAdversary) (n m : ℕ) (hm0 : 0 < m)
    (hm : ∀ d ∈ (setup n).support, m ≤ F.order d) :
    Game.succProbability (F.ddhRandomGame setup (F.cdhToDDHDistinguisher adversary) n) ≤ 1 / m :=
  Game.succProbability_withSetup_le _ _ fun d hd => by
    rw [← NNReal.coe_le_coe]
    push_cast
    exact (probability_ddhRandomExperiment_cdhToDDH_le _ _ (F.smul_generator_injective d) _).trans
      (one_div_le_one_div_of_le (by exact_mod_cast hm0) (by exact_mod_cast hm d hd))

/-- **Quantitative reduction from CDH to DDH**: when every supported group at parameter `n` has
order at least `m > 0`, any CDH adversary's success probability is at most the DDH distinguishing
advantage of `cdhToDDHDistinguisher` plus `1 / m`. -/
theorem succProbability_cdhGame_le_advantage_ddh_add (setup : ℕ → PMF F.Desc)
    (adversary : F.CDHAdversary) (n m : ℕ) (hm0 : 0 < m)
    (hm : ∀ d ∈ (setup n).support, m ≤ F.order d) :
    Game.succProbability (F.cdhGame setup adversary n) ≤
      Game.advantage (F.ddhRealGame setup (F.cdhToDDHDistinguisher adversary) n)
        (F.ddhRandomGame setup (F.cdhToDDHDistinguisher adversary) n) + 1 / m := by
  game_trans
    [F.ddhRealGame setup (F.cdhToDDHDistinguisher adversary) n,
     F.ddhRandomGame setup (F.cdhToDDHDistinguisher adversary) n]
    using [F.ddhRealGame_cdhToDDHDistinguisher setup adversary n, le_rfl,
      F.succProbability_ddhRandomGame_cdhToDDHDistinguisher_le setup adversary n m hm0 hm]

/-- The CDH-to-DDH reduction is uniform strict PPT when the CDH adversary is. -/
theorem isPPT_cdhToDDHDistinguisher {adversary : F.CDHAdversary} (hA : adversary.IsPPT) :
    (F.cdhToDDHDistinguisher adversary).IsPPT := by
  refine ((IsPPTOn.preprocess hA (prepare := DDHInput.toCDHInput) (by fun_prop)).map_with
    (f := fun x z => decide (z = F.encode x.groupParameters x.candidateShared))
    (by fun_prop)).congr fun x => ?_
  simp [cdhToDDHDistinguisher, cdhToDDH, (F.encode_injective _).eq_iff]

/-- **DDH implies CDH** when every supported group at parameter `n` has order at least `m n > 0`
and `1 / m n` is negligible. The conclusion is the textbook CDH assumption against adversaries that
output group elements, which is weaker than the word-level CDH assumption;
[#4783](https://github.com/cslib-community/cslib-frontier/issues/4783) tracks the word-level
form. -/
theorem DDH.cdh {F : PrimeOrderGroupFamily} {setup : ℕ → PMF F.Desc} (hDDH : F.DDH setup)
    {m : ℕ → ℕ} (hm0 : ∀ n, 0 < m n) (hm : ∀ n, ∀ d ∈ (setup n).support, m n ≤ F.order d)
    (hinv : Negligible fun n => (1 / m n : ℝ≥0)) : F.CDH setup := by
  intro adversary hA
  have hddh := hDDH _ (F.isPPT_cdhToDDHDistinguisher hA)
  negligible using fun n =>
    F.succProbability_cdhGame_le_advantage_ddh_add setup adversary n (m n) (hm0 n) (hm n)

/-- **DDH implies the discrete-logarithm assumption** when every supported group at parameter `n`
has order at least `m n > 0` and `1 / m n` is negligible. -/
theorem DDH.discreteLog {F : PrimeOrderGroupFamily} {setup : ℕ → PMF F.Desc} (hDDH : F.DDH setup)
    {m : ℕ → ℕ} (hm0 : ∀ n, 0 < m n) (hm : ∀ n, ∀ d ∈ (setup n).support, m n ≤ F.order d)
    (hinv : Negligible fun n => (1 / m n : ℝ≥0)) : F.DiscreteLog setup :=
  (hDDH.cdh hm0 hm hinv).discreteLog

/-! ### Random self-reducibility of DDH -/

/-- Re-randomize a candidate DDH triple `(u, v, w)` in `F.Carrier d` using exponents
`r, s₁, s₂ : ZMod (F.order d)`. -/
def ddhRerandomize (d : F.Desc) (u v w : F.Carrier d)
    (r s₁ s₂ : ZMod (F.order d)) : F.Carrier d × F.Carrier d × F.Carrier d :=
  (r • u + s₁ • F.generator d,
    v + s₂ • F.generator d,
    r • w + (r * s₂) • u + s₁ • v + (s₁ * s₂) • F.generator d)

/-- Algebraic action of `ddhRerandomize` on multiples of the generator: a tuple error
`γ - α * β` is scaled by `r` and added to the new Diffie–Hellman product
`(r * α + s₁) * (β + s₂)`. -/
theorem ddhRerandomize_smul_generator (d : F.Desc) (α β γ r s₁ s₂ : ZMod (F.order d)) :
    F.ddhRerandomize d (α • F.generator d) (β • F.generator d) (γ • F.generator d) r s₁ s₂ =
      ((r * α + s₁) • F.generator d,
        (β + s₂) • F.generator d,
        ((r * α + s₁) * (β + s₂) + r * (γ - α * β)) • F.generator d) := by
  simp only [ddhRerandomize, smul_smul, ← add_smul]
  refine Prod.ext rfl (Prod.ext rfl (congrArg (· • F.generator d) (by ring)))

/-- The re-randomized triple distribution obtained by drawing `r, s₁, s₂ : ZMod (F.order d)`
independently and uniformly. -/
noncomputable def ddhRerandomizeLaw (d : F.Desc) (u v w : F.Carrier d) :
    PMF (F.Carrier d × F.Carrier d × F.Carrier d) := do
  let r ← PMF.uniformOfFintype (ZMod (F.order d))
  let s₁ ← PMF.uniformOfFintype (ZMod (F.order d))
  let s₂ ← PMF.uniformOfFintype (ZMod (F.order d))
  return F.ddhRerandomize d u v w r s₁ s₂

/-- The real DDH tuple distribution on `F.Carrier d`. -/
noncomputable def ddhRealTupleLaw (d : F.Desc) :
    PMF (F.Carrier d × F.Carrier d × F.Carrier d) := do
  let α ← PMF.uniformOfFintype (ZMod (F.order d))
  let β ← PMF.uniformOfFintype (ZMod (F.order d))
  return (α • F.generator d, β • F.generator d, (α * β) • F.generator d)

/-- The random DDH tuple distribution on `F.Carrier d`: the triple that
`Cslib.Crypto.ddhRandomExperiment` gives its distinguisher. -/
noncomputable def ddhRandomTupleLaw (d : F.Desc) :
    PMF (F.Carrier d × F.Carrier d × F.Carrier d) := do
  let α ← PMF.uniformOfFintype (ZMod (F.order d))
  let β ← PMF.uniformOfFintype (ZMod (F.order d))
  let γ ← PMF.uniformOfFintype (ZMod (F.order d))
  return (α • F.generator d, β • F.generator d, γ • F.generator d)


/-- **Random self-reducibility of DDH (real case)**: re-randomizing any fixed real DDH tuple
`(α • g, β • g, (α * β) • g)` yields the exact uniform real DDH tuple distribution. -/
theorem ddhRerandomizeLaw_real (d : F.Desc) (α β : ZMod (F.order d)) :
    F.ddhRerandomizeLaw d (α • F.generator d) (β • F.generator d) ((α * β) • F.generator d) =
      F.ddhRealTupleLaw d := by
  simp only [ddhRerandomizeLaw, ddhRealTupleLaw, ddhRerandomize_smul_generator, sub_self, mul_zero,
    add_zero, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure]
  have hs₂ (α' : ZMod (F.order d)) :
      ((PMF.uniformOfFintype (ZMod (F.order d))).bind fun s₂ =>
        PMF.pure (α' • F.generator d, (β + s₂) • F.generator d,
          (α' * (β + s₂)) • F.generator d)) =
      ((PMF.uniformOfFintype (ZMod (F.order d))).bind fun β' =>
        PMF.pure (α' • F.generator d, β' • F.generator d, (α' * β') • F.generator d)) :=
    PMF.uniformOfFintype_bind_add_left β
      (fun β' => PMF.pure (α' • F.generator d, β' • F.generator d, (α' * β') • F.generator d))
  have hs₁ (r : ZMod (F.order d)) :
      ((PMF.uniformOfFintype (ZMod (F.order d))).bind fun s₁ =>
        (PMF.uniformOfFintype (ZMod (F.order d))).bind fun s₂ =>
          PMF.pure ((r * α + s₁) • F.generator d, (β + s₂) • F.generator d,
            ((r * α + s₁) * (β + s₂)) • F.generator d)) =
      ((PMF.uniformOfFintype (ZMod (F.order d))).bind fun α' =>
        (PMF.uniformOfFintype (ZMod (F.order d))).bind fun β' =>
          PMF.pure (α' • F.generator d, β' • F.generator d, (α' * β') • F.generator d)) := by
    simp_rw [hs₂]
    exact PMF.uniformOfFintype_bind_add_left (r * α)
      (fun α' => (PMF.uniformOfFintype (ZMod (F.order d))).bind fun β' =>
        PMF.pure (α' • F.generator d, β' • F.generator d, (α' * β') • F.generator d))
  simp_rw [hs₁, PMF.bind_const]

/-- **Random self-reducibility of DDH (random case)**: re-randomizing any fixed non-DDH tuple
`(α • g, β • g, γ • g)` with `γ ≠ α * β` yields the exact uniform random DDH tuple distribution. -/
theorem ddhRerandomizeLaw_random (d : F.Desc) {α β γ : ZMod (F.order d)} (hγ : γ ≠ α * β) :
    F.ddhRerandomizeLaw d (α • F.generator d) (β • F.generator d) (γ • F.generator d) =
      F.ddhRandomTupleLaw d := by
  simp only [ddhRerandomizeLaw, ddhRandomTupleLaw, ddhRerandomize_smul_generator,
    PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure]
  have hs₂ (r α' : ZMod (F.order d)) :
      ((PMF.uniformOfFintype (ZMod (F.order d))).bind fun s₂ =>
        PMF.pure (α' • F.generator d, (β + s₂) • F.generator d,
          (α' * (β + s₂) + r * (γ - α * β)) • F.generator d)) =
      ((PMF.uniformOfFintype (ZMod (F.order d))).bind fun β' =>
        PMF.pure (α' • F.generator d, β' • F.generator d,
          (α' * β' + r * (γ - α * β)) • F.generator d)) :=
    PMF.uniformOfFintype_bind_add_left β
      (fun β' => PMF.pure (α' • F.generator d, β' • F.generator d,
        (α' * β' + r * (γ - α * β)) • F.generator d))
  have hs₁ (r : ZMod (F.order d)) :
      ((PMF.uniformOfFintype (ZMod (F.order d))).bind fun s₁ =>
        (PMF.uniformOfFintype (ZMod (F.order d))).bind fun s₂ =>
          PMF.pure ((r * α + s₁) • F.generator d, (β + s₂) • F.generator d,
            ((r * α + s₁) * (β + s₂) + r * (γ - α * β)) • F.generator d)) =
      ((PMF.uniformOfFintype (ZMod (F.order d))).bind fun α' =>
        (PMF.uniformOfFintype (ZMod (F.order d))).bind fun β' =>
          PMF.pure (α' • F.generator d, β' • F.generator d,
            (α' * β' + r * (γ - α * β)) • F.generator d)) := by
    simp_rw [hs₂]
    exact PMF.uniformOfFintype_bind_add_left (r * α)
      (fun α' => (PMF.uniformOfFintype (ZMod (F.order d))).bind fun β' =>
        PMF.pure (α' • F.generator d, β' • F.generator d,
          (α' * β' + r * (γ - α * β)) • F.generator d))
  simp_rw [hs₁]
  rw [PMF.bind_comm]
  refine congrArg (PMF.bind _) (funext fun α' => ?_)
  rw [PMF.bind_comm]
  refine congrArg (PMF.bind _) (funext fun β' => ?_)
  exact PMF.uniformOfFintype_bind_equiv
    ((Equiv.mulRight₀ (γ - α * β) (sub_ne_zero.mpr hγ)).trans (Equiv.addLeft (α' * β')))
    (fun γ' => PMF.pure (α' • F.generator d, β' • F.generator d, γ' • F.generator d))

/-! ### Approximately uniform exponents -/

/-- Sample one approximate uniform exponent modulo `F.order d` using `n + |encNat (F.order d)|`
fair coins via `ProbComp.sampleModNat`, within statistical distance `1 / 2 ^ n` of exact uniform on
`ZMod (F.order d)`. -/
noncomputable def sampleExp (n : ℕ) (d : F.Desc) : ProbComp ℕ :=
  ProbComp.sampleModNat (n + (encNat (F.order d)).length) (F.order d)

/-- `sampleExp` is uniform strict PPT whenever `n` and `d` are computable in polynomial time. -/
theorem isPPTOn_sampleExp {γ : Type} {encIn : γ ↪ List Bool}
    {n : γ → ℕ} {d : γ → F.Desc}
    (hn : ComputableInPolyTime n encIn encUnary)
    (hd : ComputableInPolyTime d encIn F.encDesc) :
    IsPPTOn encIn encNat (fun a => F.sampleExp (n a) (d a)) := by
  have hord := F.computableInPolyTime_order.comp hd
  exact isPPTOn_sampleModNat
    (hn.unary_add' ((ComputableInPolyTime.encoding_length encNat).comp hord)) hord

/-- Replacing one `sampleExp n d` draw by an exact uniform draw on `ZMod (F.order d)`
changes `Game.advantage` by at most `1 / 2 ^ n`. -/
theorem advantage_bind_sampleExp_le (n : ℕ) (d : F.Desc)
    (k : ZMod (F.order d) → Game) :
    Game.advantage
      ((ProbComp.eval (F.sampleExp n d)).bind fun s => k (s : ZMod (F.order d)))
      ((PMF.uniformOfFintype (ZMod (F.order d))).bind k) ≤
      1 / 2 ^ n := by
  have hmap :
      ((ProbComp.eval (F.sampleExp n d)).bind fun s => k (s : ZMod (F.order d))) =
        ((ProbComp.eval (F.sampleExp n d)).map
          (Nat.cast : ℕ → ZMod (F.order d))).bind k :=
    (PMF.bind_map _ _ _).symm
  have hlt : F.order d < 2 ^ (encNat (F.order d)).length := by
    simpa only [encNat_apply, ← Nat.size_eq_bits_len] using Nat.lt_size_self (F.order d)
  have hord_le : (F.order d : ℝ) ≤ 2 ^ (encNat (F.order d)).length := by
    exact_mod_cast hlt.le
  rw [← NNReal.coe_le_coe, hmap, Game.advantage_eq_nndist, coe_nndist]
  refine (PMF.dist_bind_le ((ProbComp.eval (F.sampleExp n d)).map
      (Nat.cast : ℕ → ZMod (F.order d)))
    (PMF.uniformOfFintype (ZMod (F.order d))) k).trans ?_
  refine (ProbComp.dist_map_natCast_eval_sampleModNat_le
    (n + (encNat (F.order d)).length) (F.order d)).trans ?_
  rw [Nat.add_comm n, pow_add, ← div_div]
  have hdiv : (F.order d : ℝ) / 2 ^ (encNat (F.order d)).length ≤ 1 :=
    (div_le_one (by positivity)).mpr hord_le
  have hbound :
      (F.order d : ℝ) / 2 ^ (encNat (F.order d)).length / 2 ^ n ≤ 1 / 2 ^ n :=
    div_le_div_of_nonneg_right hdiv (by positivity)
  simpa only [NNReal.coe_div, NNReal.coe_one, NNReal.coe_pow, NNReal.coe_ofNat] using hbound

/-- Distribution of a single modular exponent sampled via `ProbComp.sampleModNat` at parameter `n`
and group parameters `d`, projected to `ZMod (F.order d)` (original). -/
noncomputable def sampleModZModLaw (n : ℕ) (d : F.Desc) : PMF (ZMod (F.order d)) :=
  (ProbComp.eval (ProbComp.sampleModNat ((F.order d).size + n) (F.order d))).map Nat.cast

/-- Each modular exponent sampled by `ProbComp.sampleModNat ((F.order d).size + n) (F.order d)`
is within statistical distance `1 / 2 ^ n` of `PMF.uniformOfFintype (ZMod (F.order d))`
(original). -/
theorem dist_sampleModZModLaw_le (n : ℕ) (d : F.Desc) :
    dist (PMF.uniformOfFintype (ZMod (F.order d))) (F.sampleModZModLaw n d) ≤ 1 / 2 ^ n := by
  have : NeZero (F.order d) := ⟨(F.prime_order d).ne_zero⟩
  rw [dist_comm]
  refine (ProbComp.dist_map_natCast_eval_sampleModNat_le
    ((F.order d).size + n) (F.order d)).trans ?_
  have hlt : (F.order d : ℝ) ≤ 2 ^ (F.order d).size := by
    exact_mod_cast (Nat.lt_size_self (F.order d)).le
  have hpos : (0 : ℝ) < 2 ^ (F.order d).size := by positivity
  calc
    (F.order d : ℝ) / 2 ^ ((F.order d).size + n)
      ≤ 2 ^ (F.order d).size / (2 ^ (F.order d).size * 2 ^ n) := by
        rw [pow_add]
        gcongr
    _ = 1 / 2 ^ n := by
        rw [div_mul_eq_div_div, div_self hpos.ne']

/-! ### Efficient DDH random self-reduction -/

/-- The DDH random self-reduction ([BonehShoup2023], Exercises 10.8–10.9, pp. 425–426): draw three
approximately uniform exponents with `sampleExp`, re-randomize the input triple with
`ddhRerandomize`, and run `distinguisher` on the result. -/
noncomputable def ddhSelfReduceDistinguisher (distinguisher : F.DDHDistinguisher) :
    F.DDHDistinguisher := fun n d u v w => do
  let r ← F.sampleExp n d
  let s₁ ← F.sampleExp n d
  let s₂ ← F.sampleExp n d
  let (u', v', w') := F.ddhRerandomize d u v w r s₁ s₂
  distinguisher n d u' v' w'

variable {F} in
/-- The encoded components of `ddhRerandomize` with natural-number exponents are computable. -/
private theorem computableInPolyTime_encode_ddhRerandomize {α : Type} {enc : α ↪ List Bool}
    {d : α → F.Desc} {u v w : (a : α) → F.Carrier (d a)} {r s₁ s₂ : α → ℕ}
    (hd : ComputableInPolyTime d enc F.encDesc)
    (hu : ComputableInPolyTime (fun a => F.encode (d a) (u a)) enc encBits)
    (hv : ComputableInPolyTime (fun a => F.encode (d a) (v a)) enc encBits)
    (hw : ComputableInPolyTime (fun a => F.encode (d a) (w a)) enc encBits)
    (hr : ComputableInPolyTime r enc encNat) (hs₁ : ComputableInPolyTime s₁ enc encNat)
    (hs₂ : ComputableInPolyTime s₂ enc encNat) :
    ComputableInPolyTime (fun a => F.encode (d a)
        (F.ddhRerandomize (d a) (u a) (v a) (w a) (r a) (s₁ a) (s₂ a)).1) enc encBits ∧
      ComputableInPolyTime (fun a => F.encode (d a)
        (F.ddhRerandomize (d a) (u a) (v a) (w a) (r a) (s₁ a) (s₂ a)).2.1) enc encBits ∧
      ComputableInPolyTime (fun a => F.encode (d a)
        (F.ddhRerandomize (d a) (u a) (v a) (w a) (r a) (s₁ a) (s₂ a)).2.2) enc encBits := by
  have hg := computableInPolyTime_encode_generator hd
  refine ⟨.of_enc_eq (computableInPolyTime_encode_add hd
      (computableInPolyTime_encode_natCast_smul hd hr hu)
      (computableInPolyTime_encode_natCast_smul hd hs₁ hg)) fun _ => rfl,
    .of_enc_eq (computableInPolyTime_encode_add hd hv
      (computableInPolyTime_encode_natCast_smul hd hs₂ hg)) fun _ => rfl,
    .of_enc_eq (computableInPolyTime_encode_add hd (computableInPolyTime_encode_add hd
      (computableInPolyTime_encode_add hd (computableInPolyTime_encode_natCast_smul hd hr hw)
        (computableInPolyTime_encode_natCast_smul hd (hr.binary_mul' hs₂) hu))
      (computableInPolyTime_encode_natCast_smul hd hs₁ hv))
      (computableInPolyTime_encode_natCast_smul hd (hs₁.binary_mul' hs₂) hg)) fun _ => ?_⟩
  simp only [ddhRerandomize, Nat.cast_mul]

/-- `ddhSelfReduceDistinguisher` is uniform strict PPT whenever `distinguisher` is. -/
theorem isPPT_ddhSelfReduceDistinguisher {distinguisher : F.DDHDistinguisher}
    (hD : distinguisher.IsPPT) : (F.ddhSelfReduceDistinguisher distinguisher).IsPPT := by
  have hs {α : Type} {enc : α ↪ List Bool} {x : α → F.DDHInput}
      (hx : ComputableInPolyTime x enc F.encDDHInput) :
      IsPPTOn enc encNat fun a => F.sampleExp (x a).secParam (x a).groupParameters :=
    F.isPPTOn_sampleExp (by fun_prop) (by fun_prop)
  refine IsPPTOn.bind_with (hs .id') ?_
  refine IsPPTOn.bind_with (hs (by fun_prop)) ?_
  refine IsPPTOn.bind_with (hs (by fun_prop)) ?_
  let E := encPair (encPair (encPair F.encDDHInput encNat) encNat) encNat
  have hx : ComputableInPolyTime (fun p : ((F.DDHInput × ℕ) × ℕ) × ℕ => p.1.1.1) E
      F.encDDHInput := by fun_prop
  have hd := F.encDDHInput_groupParameters_polyTime hx
  have h := computableInPolyTime_encode_ddhRerandomize hd
    (F.encDDHInput_leftPublic_polyTime hx) (F.encDDHInput_rightPublic_polyTime hx)
    (F.encDDHInput_candidateShared_polyTime hx)
    (show ComputableInPolyTime (fun p : ((F.DDHInput × ℕ) × ℕ) × ℕ => p.1.1.2) E encNat by
      fun_prop)
    (show ComputableInPolyTime (fun p : ((F.DDHInput × ℕ) × ℕ) × ℕ => p.1.2) E encNat by
      fun_prop)
    (show ComputableInPolyTime (fun p : ((F.DDHInput × ℕ) × ℕ) × ℕ => p.2) E encNat by
      fun_prop)
  exact (hD.comp (F.encDDHInput_secParam_polyTime hx) hd h.1 h.2.1 h.2.2).congr
    fun _ => rfl

/-- **Sampling loss of the DDH self-reduction**: on any fixed triple, replacing the three exact
uniform exponents of `ddhRerandomizeLaw` by the `sampleExp` draws of
`ddhSelfReduceDistinguisher` changes the acceptance law by at most `3 / 2 ^ n`. -/
theorem advantage_ddhRerandomizeLaw_ddhSelfReduceDistinguisher_le
    (distinguisher : F.DDHDistinguisher) (n : ℕ) (d : F.Desc) (u v w : F.Carrier d) :
    Game.advantage
      ((F.ddhRerandomizeLaw d u v w).bind fun (u', v', w') =>
        ProbComp.eval (distinguisher n d u' v' w'))
      (ProbComp.eval (F.ddhSelfReduceDistinguisher distinguisher n d u v w)) ≤ 3 / 2 ^ n := by
  let k : ZMod (F.order d) → ZMod (F.order d) → ZMod (F.order d) → Game := fun r s₁ s₂ =>
    let (u', v', w') := F.ddhRerandomize d u v w r s₁ s₂
    ProbComp.eval (distinguisher n d u' v' w')
  have hlaw : ((F.ddhRerandomizeLaw d u v w).bind fun (u', v', w') =>
      ProbComp.eval (distinguisher n d u' v' w')) =
      (PMF.uniformOfFintype (ZMod (F.order d))).bind fun r =>
        (PMF.uniformOfFintype (ZMod (F.order d))).bind fun s₁ =>
          (PMF.uniformOfFintype (ZMod (F.order d))).bind fun s₂ => k r s₁ s₂ := by
    simp only [ddhRerandomizeLaw, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.bind_bind,
      PMF.pure_bind]
    rfl
  have hself : ProbComp.eval (F.ddhSelfReduceDistinguisher distinguisher n d u v w) =
      (ProbComp.eval (F.sampleExp n d)).bind fun r =>
        (ProbComp.eval (F.sampleExp n d)).bind fun s₁ =>
          (ProbComp.eval (F.sampleExp n d)).bind fun s₂ =>
            k (r : ZMod (F.order d)) (s₁ : ZMod (F.order d)) (s₂ : ZMod (F.order d)) := by
    simp only [ddhSelfReduceDistinguisher, ProbComp.eval_bind]
    rfl
  rw [hlaw, hself, Game.advantage_comm]
  have h₁ := F.advantage_bind_sampleExp_le n d fun r =>
    (ProbComp.eval (F.sampleExp n d)).bind fun s₁ =>
      (ProbComp.eval (F.sampleExp n d)).bind fun s₂ =>
        k r (s₁ : ZMod (F.order d)) (s₂ : ZMod (F.order d))
  have h₂ := Game.advantage_bind_le_nnreal (PMF.uniformOfFintype (ZMod (F.order d))) _ _ fun r =>
    F.advantage_bind_sampleExp_le n d fun s₁ =>
      (ProbComp.eval (F.sampleExp n d)).bind fun s₂ => k r s₁ (s₂ : ZMod (F.order d))
  have h₃ := Game.advantage_bind_le_nnreal (PMF.uniformOfFintype (ZMod (F.order d))) _ _ fun r =>
    Game.advantage_bind_le_nnreal (PMF.uniformOfFintype (ZMod (F.order d))) _ _ fun s₁ =>
      F.advantage_bind_sampleExp_le n d (k r s₁)
  calc _ ≤ _ := Game.advantage_triangle _ _ _
    _ ≤ (1 : ℝ≥0) / 2 ^ n + (1 / 2 ^ n + 1 / 2 ^ n) :=
      add_le_add h₁ ((Game.advantage_triangle _ _ _).trans (add_le_add h₂ h₃))
    _ = 3 / 2 ^ n := by ring

/-- Running a distinguisher on the uniform real DDH tuple is the real DDH experiment. -/
theorem ddhRealTupleLaw_bind_eq (distinguisher : F.DDHDistinguisher) (n : ℕ) (d : F.Desc) :
    ((F.ddhRealTupleLaw d).bind fun (u, v, w) => ProbComp.eval (distinguisher n d u v w)) =
      ProbComp.eval (ddhRealExperiment (F.order d) (F.generator d) (distinguisher n d)) := by
  simp only [ddhRealTupleLaw, eval_ddhRealExperiment, PMF.monad_bind_eq_bind,
    PMF.monad_pure_eq_pure, PMF.bind_bind, PMF.pure_bind]

/-- Running a distinguisher on the uniform random DDH tuple is the random DDH experiment. -/
theorem ddhRandomTupleLaw_bind_eq (distinguisher : F.DDHDistinguisher) (n : ℕ) (d : F.Desc) :
    ((F.ddhRandomTupleLaw d).bind fun (u, v, w) => ProbComp.eval (distinguisher n d u v w)) =
      ProbComp.eval (ddhRandomExperiment (F.order d) (F.generator d) (distinguisher n d)) := by
  simp only [ddhRandomTupleLaw, eval_ddhRandomExperiment, PMF.monad_bind_eq_bind,
    PMF.monad_pure_eq_pure, PMF.bind_bind, PMF.pure_bind]

/-- On any fixed real DDH triple, `ddhSelfReduceDistinguisher` accepts within `3 / 2 ^ n` of the
real DDH experiment. -/
theorem advantage_ddhRealExperiment_ddhSelfReduceDistinguisher_le
    (distinguisher : F.DDHDistinguisher) (n : ℕ) (d : F.Desc) (α β : ZMod (F.order d)) :
    Game.advantage
      (ProbComp.eval (ddhRealExperiment (F.order d) (F.generator d) (distinguisher n d)))
      (ProbComp.eval (F.ddhSelfReduceDistinguisher distinguisher n d (α • F.generator d)
        (β • F.generator d) ((α * β) • F.generator d))) ≤ 3 / 2 ^ n := by
  have h := F.advantage_ddhRerandomizeLaw_ddhSelfReduceDistinguisher_le distinguisher n d
    (α • F.generator d) (β • F.generator d) ((α * β) • F.generator d)
  rwa [ddhRerandomizeLaw_real, ddhRealTupleLaw_bind_eq] at h

/-- On any fixed non-DDH triple, `ddhSelfReduceDistinguisher` accepts within `3 / 2 ^ n` of the
random DDH experiment. -/
theorem advantage_ddhRandomExperiment_ddhSelfReduceDistinguisher_le
    (distinguisher : F.DDHDistinguisher) (n : ℕ) (d : F.Desc) {α β γ : ZMod (F.order d)}
    (hγ : γ ≠ α * β) :
    Game.advantage
      (ProbComp.eval (ddhRandomExperiment (F.order d) (F.generator d) (distinguisher n d)))
      (ProbComp.eval (F.ddhSelfReduceDistinguisher distinguisher n d (α • F.generator d)
        (β • F.generator d) (γ • F.generator d))) ≤ 3 / 2 ^ n := by
  have h := F.advantage_ddhRerandomizeLaw_ddhSelfReduceDistinguisher_le distinguisher n d
    (α • F.generator d) (β • F.generator d) (γ • F.generator d)
  rwa [ddhRerandomizeLaw_random _ _ hγ, ddhRandomTupleLaw_bind_eq] at h

/-! ### Worst-case DDH -/

/-- The DDH re-randomization game ([BonehShoup2023], Exercises 10.8–10.9, pp. 425–426): draw
group parameters `d`, re-randomize the fixed triple `(u d, v d, w d)` with exact uniform exponents,
and run `distinguisher` on the result. -/
noncomputable def ddhRerandomizeGame (setup : ℕ → PMF F.Desc) (u v w : ∀ d : F.Desc, F.Carrier d)
    (distinguisher : F.DDHDistinguisher) (n : ℕ) : Game := do
  let d ← setup n
  let (u', v', w') ← F.ddhRerandomizeLaw d (u d) (v d) (w d)
  ProbComp.eval (distinguisher n d u' v' w')

/-- The worst-case DDH game: draw group parameters `d` and run `distinguisher` on the fixed triple
`(u d, v d, w d)`. -/
noncomputable def ddhWorstCaseGame (setup : ℕ → PMF F.Desc) (u v w : ∀ d : F.Desc, F.Carrier d)
    (distinguisher : F.DDHDistinguisher) (n : ℕ) : Game :=
  Game.withSetup (setup n) fun d => distinguisher n d (u d) (v d) (w d)

/-- Re-randomizing any family of real DDH triples `(α d • g, β d • g, (α d * β d) • g)` gives the
average-case `ddhRealGame` ([BonehShoup2023], Exercises 10.8–10.9, pp. 425–426). -/
@[simp] theorem ddhRerandomizeGame_real (setup : ℕ → PMF F.Desc)
    (α β : ∀ d : F.Desc, ZMod (F.order d)) (distinguisher : F.DDHDistinguisher) (n : ℕ) :
    F.ddhRerandomizeGame setup (fun d => α d • F.generator d) (fun d => β d • F.generator d)
      (fun d => (α d * β d) • F.generator d) distinguisher n =
      F.ddhRealGame setup distinguisher n := by
  simp only [ddhRerandomizeGame, ddhRealGame, Game.withSetup, PMF.monad_bind_eq_bind,
    ddhRerandomizeLaw_real, ddhRealTupleLaw_bind_eq]

/-- Re-randomizing any family of non-DDH triples `(α d • g, β d • g, γ d • g)` with
`γ d ≠ α d * β d` on the support of `setup n` gives the average-case `ddhRandomGame`
([BonehShoup2023], Exercises 10.8–10.9, pp. 425–426). -/
theorem ddhRerandomizeGame_random (setup : ℕ → PMF F.Desc)
    (α β γ : ∀ d : F.Desc, ZMod (F.order d)) (distinguisher : F.DDHDistinguisher) (n : ℕ)
    (hγ : ∀ d ∈ (setup n).support, γ d ≠ α d * β d) :
    F.ddhRerandomizeGame setup (fun d => α d • F.generator d) (fun d => β d • F.generator d)
      (fun d => γ d • F.generator d) distinguisher n = F.ddhRandomGame setup distinguisher n := by
  simp only [ddhRerandomizeGame, ddhRandomGame, Game.withSetup, PMF.monad_bind_eq_bind]
  refine Cslib.Probability.PMF.bind_congr_on_support _ _ _ fun d hd => ?_
  rw [ddhRerandomizeLaw_random _ _ (hγ d hd), ddhRandomTupleLaw_bind_eq]

/-- **DDH re-randomization advantage identity** ([BonehShoup2023], Exercises 10.8–10.9,
pp. 425–426): re-randomizing a real triple family and a non-DDH triple family leaves exactly the
average-case DDH advantage. -/
theorem advantage_ddhRerandomizeGame_eq (setup : ℕ → PMF F.Desc)
    (α β α' β' γ' : ∀ d : F.Desc, ZMod (F.order d)) (distinguisher : F.DDHDistinguisher) (n : ℕ)
    (hγ' : ∀ d ∈ (setup n).support, γ' d ≠ α' d * β' d) :
    Game.advantage
      (F.ddhRerandomizeGame setup (fun d => α d • F.generator d) (fun d => β d • F.generator d)
        (fun d => (α d * β d) • F.generator d) distinguisher n)
      (F.ddhRerandomizeGame setup (fun d => α' d • F.generator d) (fun d => β' d • F.generator d)
        (fun d => γ' d • F.generator d) distinguisher n) =
      Game.advantage (F.ddhRealGame setup distinguisher n)
        (F.ddhRandomGame setup distinguisher n) := by
  rw [ddhRerandomizeGame_real, F.ddhRerandomizeGame_random setup α' β' γ' distinguisher n hγ']

/-- **DDH re-randomization indistinguishability** ([BonehShoup2023], Exercises 10.8–10.9,
pp. 425–426): under `DDH`, no PPT distinguisher tells the re-randomization of a real triple family
from that of a non-DDH triple family. -/
theorem DDH.ddhRerandomizeGame {F : PrimeOrderGroupFamily} {setup : ℕ → PMF F.Desc}
    (hDDH : F.DDH setup) (α β α' β' γ' : ∀ d : F.Desc, ZMod (F.order d))
    (hγ' : ∀ᶠ n in Filter.atTop, ∀ d ∈ (setup n).support, γ' d ≠ α' d * β' d) :
    Game.Indistinguishable
      (F.ddhRerandomizeGame setup (fun d => α d • F.generator d) (fun d => β d • F.generator d)
        (fun d => (α d * β d) • F.generator d))
      (F.ddhRerandomizeGame setup (fun d => α' d • F.generator d) (fun d => β' d • F.generator d)
        (fun d => γ' d • F.generator d))
      DDHDistinguisher.IsPPT := by
  intro distinguisher hD
  have hddh := hDDH distinguisher hD
  negligible eventually (hγ'.mono fun n hn =>
    (F.advantage_ddhRerandomizeGame_eq setup α β α' β' γ' distinguisher n hn).le)

/-- **Sampling loss of the worst-case reduction**: replacing the exact uniform exponents of
`ddhRerandomizeGame` by `ddhSelfReduceDistinguisher` on the fixed triple changes the game by at
most `3 / 2 ^ n`. -/
theorem advantage_ddhRerandomizeGame_ddhWorstCaseGame_le (setup : ℕ → PMF F.Desc)
    (u v w : ∀ d : F.Desc, F.Carrier d) (distinguisher : F.DDHDistinguisher) (n : ℕ) :
    Game.advantage (F.ddhRerandomizeGame setup u v w distinguisher n)
      (F.ddhWorstCaseGame setup u v w (F.ddhSelfReduceDistinguisher distinguisher) n) ≤
      3 / 2 ^ n :=
  Game.advantage_bind_le_nnreal (setup n) _ _ fun d =>
    F.advantage_ddhRerandomizeLaw_ddhSelfReduceDistinguisher_le distinguisher n d (u d) (v d) (w d)

/-- **Quantitative worst-case-to-average-case DDH reduction**: the average-case DDH advantage of
`distinguisher` is at most the worst-case advantage of `ddhSelfReduceDistinguisher distinguisher`
between a real triple family and a non-DDH triple family, plus `6 / 2 ^ n`. -/
theorem advantage_ddhRealGame_le_ddhWorstCaseGame (setup : ℕ → PMF F.Desc)
    (α β α' β' γ' : ∀ d : F.Desc, ZMod (F.order d)) (distinguisher : F.DDHDistinguisher) (n : ℕ)
    (hγ' : ∀ d ∈ (setup n).support, γ' d ≠ α' d * β' d) :
    Game.advantage (F.ddhRealGame setup distinguisher n) (F.ddhRandomGame setup distinguisher n) ≤
      Game.advantage
        (F.ddhWorstCaseGame setup (fun d => α d • F.generator d) (fun d => β d • F.generator d)
          (fun d => (α d * β d) • F.generator d) (F.ddhSelfReduceDistinguisher distinguisher) n)
        (F.ddhWorstCaseGame setup (fun d => α' d • F.generator d) (fun d => β' d • F.generator d)
          (fun d => γ' d • F.generator d) (F.ddhSelfReduceDistinguisher distinguisher) n) +
      6 / 2 ^ n := by
  rw [← F.advantage_ddhRerandomizeGame_eq setup α β α' β' γ' distinguisher n hγ']
  have hhops {r₁ w₁ w₂ r₂ : Game} (h₁ : Game.advantage r₁ w₁ ≤ 3 / 2 ^ n)
      (h₂ : Game.advantage r₂ w₂ ≤ 3 / 2 ^ n) :
      Game.advantage r₁ r₂ ≤ Game.advantage w₁ w₂ + 6 / 2 ^ n :=
    calc Game.advantage r₁ r₂
        ≤ Game.advantage r₁ w₁ + (Game.advantage w₁ w₂ + Game.advantage w₂ r₂) :=
          (Game.advantage_triangle r₁ w₁ r₂).trans
            (add_le_add le_rfl (Game.advantage_triangle w₁ w₂ r₂))
      _ ≤ 3 / 2 ^ n + (Game.advantage w₁ w₂ + 3 / 2 ^ n) :=
          add_le_add h₁ (add_le_add le_rfl ((Game.advantage_comm w₂ r₂).trans_le h₂))
      _ = Game.advantage w₁ w₂ + 6 / 2 ^ n := by ring
  exact hhops (F.advantage_ddhRerandomizeGame_ddhWorstCaseGame_le setup _ _ _ distinguisher n)
    (F.advantage_ddhRerandomizeGame_ddhWorstCaseGame_le setup _ _ _ distinguisher n)

/-- **Average-case DDH from worst-case DDH**: if every PPT distinguisher has negligible advantage
between a fixed real triple family and a fixed non-DDH triple family, then `DDH` holds. -/
theorem ddh_of_worstCase {setup : ℕ → PMF F.Desc}
    (α β α' β' γ' : ∀ d : F.Desc, ZMod (F.order d))
    (hγ' : ∀ᶠ n in Filter.atTop, ∀ d ∈ (setup n).support, γ' d ≠ α' d * β' d)
    (hworst : Game.Indistinguishable
      (F.ddhWorstCaseGame setup (fun d => α d • F.generator d) (fun d => β d • F.generator d)
        (fun d => (α d * β d) • F.generator d))
      (F.ddhWorstCaseGame setup (fun d => α' d • F.generator d) (fun d => β' d • F.generator d)
        (fun d => γ' d • F.generator d))
      DDHDistinguisher.IsPPT) :
    F.DDH setup := by
  intro distinguisher hD
  have hworstNeg := hworst (F.ddhSelfReduceDistinguisher distinguisher)
    (F.isPPT_ddhSelfReduceDistinguisher hD)
  negligible eventually (hγ'.mono fun n hn =>
    F.advantage_ddhRealGame_le_ddhWorstCaseGame setup α β α' β' γ' distinguisher n hn)

/-! ### Worst-case DDH decider via Chernoff amplification ([BonehShoup2023], Exercise 10.10) -/

/-- **Chernoff-amplified worst-case DDH decider** ([BonehShoup2023], Section 10.11, Exercise 10.10,
p. 426): given a DDH distinguisher and an inverse-advantage bound `invEps`, run
`N = (n + 3) * (7 * invEps n) ^ 2` independent trials of `ddhSelfReduceDistinguisher` on the input
triple, on the reference DDH triple `(0, 0, 0)` and on the reference non-DDH triple `(0, 0, g)`,
and accept iff the input count `cIn` is at least as close to the real count as to the random one. -/
noncomputable def ddhAmplifiedDecider (distinguisher : F.DDHDistinguisher) (invEps : ℕ → ℕ) :
    F.DDHDistinguisher := fun n d u v w => do
  let N := (n + 3) * (7 * invEps n) ^ 2
  let cIn ← OracleComp.countTrue N (F.ddhSelfReduceDistinguisher distinguisher n d u v w)
  let cReal ← OracleComp.countTrue N (F.ddhSelfReduceDistinguisher distinguisher n d 0 0 0)
  let cRandom ← OracleComp.countTrue N
    (F.ddhSelfReduceDistinguisher distinguisher n d 0 0 (F.generator d))
  return decide ((cIn - cReal) + (cReal - cIn) ≤ (cIn - cRandom) + (cRandom - cIn))

/-- `ddhAmplifiedDecider` is uniform strict PPT whenever `distinguisher` is and `invEps` is
computable in polynomial time in unary ([BonehShoup2023], Exercise 10.10, p. 426). -/
theorem isPPT_ddhAmplifiedDecider {distinguisher : F.DDHDistinguisher} (hD : distinguisher.IsPPT)
    {invEps : ℕ → ℕ} (hinvEps : ComputableInPolyTime invEps encUnary encUnary) :
    (F.ddhAmplifiedDecider distinguisher invEps).IsPPT := by
  have hself := F.isPPT_ddhSelfReduceDistinguisher hD
  have hN {α : Type} {enc : α ↪ List Bool} {n : α → ℕ}
      (hn : ComputableInPolyTime n enc encUnary) :
      ComputableInPolyTime (fun a => (n a + 3) * (7 * invEps (n a)) ^ 2) enc encUnary :=
    (hn.unary_add' (.const 3)).unary_mul'
      ((ComputableInPolyTime.unary_pow 2).comp ((ComputableInPolyTime.const 7).unary_mul'
        (hinvEps.comp hn)))
  have hcmp : ComputableInPolyTime
      (fun q : ℕ × ℕ × ℕ => decide ((q.1 - q.2.1) + (q.2.1 - q.1) ≤ (q.1 - q.2.2) + (q.2.2 - q.1)))
      (encPair encUnary (encPair encUnary encUnary)) encBool := by
    fun_prop
  refine IsPPTOn.bind_with
    ((hself.comp (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)).countTrue
      (hN (by fun_prop))) ?_
  refine IsPPTOn.bind_with
    ((hself.comp (by fun_prop) (by fun_prop) (computableInPolyTime_encode_zero (by fun_prop))
      (computableInPolyTime_encode_zero (by fun_prop))
      (computableInPolyTime_encode_zero (by fun_prop))).countTrue (hN (by fun_prop))) ?_
  refine IsPPTOn.bind_with
    ((hself.comp (by fun_prop) (by fun_prop) (computableInPolyTime_encode_zero (by fun_prop))
      (computableInPolyTime_encode_zero (by fun_prop))
      (computableInPolyTime_encode_generator (by fun_prop))).countTrue (hN (by fun_prop))) ?_
  have hproj : ComputableInPolyTime (fun p : ((F.DDHInput × ℕ) × ℕ) × ℕ => (p.1.1.2, p.1.2, p.2))
      (encPair (encPair (encPair F.encDDHInput encUnary) encUnary) encUnary)
      (encPair encUnary (encPair encUnary encUnary)) := by
    fun_prop
  exact (hcmp.comp hproj).isPPTOn

private theorem cast_sub_add_sub_eq_abs (a b : ℕ) :
    (((a - b) + (b - a) : ℕ) : ℝ) = |(a : ℝ) - (b : ℝ)| := by
  rcases le_total a b with h | h
  · have hR : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast h
    rw [Nat.sub_eq_zero_of_le h, zero_add, Nat.cast_sub h, abs_of_nonpos (sub_nonpos.mpr hR),
      neg_sub]
  · have hR : (b : ℝ) ≤ (a : ℝ) := by exact_mod_cast h
    rw [Nat.sub_eq_zero_of_le h, add_zero, Nat.cast_sub h, abs_of_nonneg (sub_nonneg.mpr hR)]

private theorem abs_succProbability_sub_le_of_advantage_le {g₁ g₂ : Game} {ε : ℝ}
    (h : (Game.advantage g₁ g₂ : ℝ) ≤ ε) :
    |(g₁ true).toReal - (g₂ true).toReal| ≤ ε := by
  simpa only [Game.coe_advantage, Game.succProbability, ENNReal.coe_toNNReal_eq_toReal] using h

private theorem abs_sub_lt_abs_sub_of_close
    {x x₁ x₂ q q₁ q₂ p₁ p₂ ε : ℝ}
    (hgap : ε ≤ |p₁ - p₂|)
    (hq : |q - p₁| ≤ ε / 12) (hq₁ : |q₁ - p₁| ≤ ε / 12) (hq₂ : |q₂ - p₂| ≤ ε / 12)
    (hx : |x - q| < ε / 7) (hx₁ : |x₁ - q₁| < ε / 7) (hx₂ : |x₂ - q₂| < ε / 7) :
    |x - x₁| < |x - x₂| := by
  have hu : |x - p₁| < ε / 7 + ε / 12 :=
    (abs_sub_le x q p₁).trans_lt (add_lt_add_of_lt_of_le hx hq)
  have hv : |p₁ - x₁| < ε / 7 + ε / 12 := by
    rw [abs_sub_comm]
    exact (abs_sub_le x₁ q₁ p₁).trans_lt (add_lt_add_of_lt_of_le hx₁ hq₁)
  have hw : |x₂ - p₂| < ε / 7 + ε / 12 :=
    (abs_sub_le x₂ q₂ p₂).trans_lt (add_lt_add_of_lt_of_le hx₂ hq₂)
  have h1 := abs_sub_le x p₁ x₁
  have h2 : |p₁ - p₂| ≤ |x - p₁| + (|x - x₂| + |x₂ - p₂|) := by
    rw [abs_sub_comm x p₁]
    exact (abs_sub_le p₁ x p₂).trans (add_le_add_right (abs_sub_le x x₂ p₂) _)
  clear hq hq₁ hq₂ hx hx₁ hx₂
  linarith [abs_nonneg (x - p₁)]

private theorem toOuterMeasure_bind₃_failure_le_pow
    (μ₁ μ₂ μ₃ : PMF ℕ) (S₁ S₂ S₃ : Set ℕ) (f : ℕ → ℕ → ℕ → Bool) (b₀ : Bool) (n : ℕ)
    (h₁ : (μ₁.toOuterMeasure S₁ᶜ).toReal ≤ (1 / 2 : ℝ) ^ (n + 2))
    (h₂ : (μ₂.toOuterMeasure S₂ᶜ).toReal ≤ (1 / 2 : ℝ) ^ (n + 2))
    (h₃ : (μ₃.toOuterMeasure S₃ᶜ).toReal ≤ (1 / 2 : ℝ) ^ (n + 2))
    (hdet : ∀ {c₁ c₂ c₃}, c₁ ∈ S₁ → c₂ ∈ S₂ → c₃ ∈ S₃ → f c₁ c₂ c₃ = b₀) :
    ((μ₁.bind fun c₁ => μ₂.bind fun c₂ => μ₃.bind fun c₃ =>
      PMF.pure (f c₁ c₂ c₃)).toOuterMeasure {b | b ≠ b₀}).toReal ≤ (1 / 2 : ℝ) ^ n := by
  have hpow : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ (n + 2) := pow_nonneg (by norm_num) _
  refine ((PMF.toOuterMeasure_bind_failure_toReal_le μ₁
    (fun c₁ => μ₂.bind fun c₂ => μ₃.bind fun c₃ => PMF.pure (f c₁ c₂ c₃)) S₁ {b | b ≠ b₀}
    (error := (1 / 2 : ℝ) ^ (n + 2) + (1 / 2 : ℝ) ^ (n + 2)) (add_nonneg hpow hpow)
    fun c₁ _ hc₁ =>
      (PMF.toOuterMeasure_bind_failure_toReal_le μ₂
        (fun c₂ => μ₃.bind fun c₃ => PMF.pure (f c₁ c₂ c₃)) S₂ {b | b ≠ b₀}
        (error := (1 / 2 : ℝ) ^ (n + 2)) hpow fun c₂ _ hc₂ =>
          (PMF.toOuterMeasure_bind_failure_toReal_le μ₃
            (fun c₃ => PMF.pure (f c₁ c₂ c₃)) S₃ {b | b ≠ b₀}
            (error := 0) le_rfl fun c₃ _ hc₃ => by
              rw [hdet hc₁ hc₂ hc₃, PMF.toOuterMeasure_pure_apply]
              simp).trans ((add_zero _).le.trans h₃)).trans
        (add_le_add_left h₂ _)).trans (add_le_add_left h₁ _)).trans ?_
  calc (1 / 2 : ℝ) ^ (n + 2) + ((1 / 2 : ℝ) ^ (n + 2) + (1 / 2 : ℝ) ^ (n + 2))
      = (1 / 2 : ℝ) ^ n * (3 / 4) := by rw [pow_add]; ring
    _ ≤ (1 / 2 : ℝ) ^ n * 1 :=
      mul_le_mul_of_nonneg_left (by norm_num) (pow_nonneg (by norm_num) n)
    _ = (1 / 2 : ℝ) ^ n := mul_one _

/-- **Quantitative worst-case DDH decision bound** ([BonehShoup2023], Section 10.11, Exercise 10.10,
p. 426): if `distinguisher n` has DDH advantage at least `1 / invEps n` in the group `d` and the
sampling loss satisfies `3 / 2 ^ n ≤ 1 / (12 * invEps n)`, then on *every* triple
`(α • g, β • g, γ • g)` the decider answers differently from `decide (γ = α * β)` with probability
at most `(1 / 2) ^ n`. -/
theorem ddhAmplifiedDecider_error_le_pow (distinguisher : F.DDHDistinguisher)
    (invEps : ℕ → ℕ) (n : ℕ) (d : F.Desc) (α β γ : ZMod (F.order d)) (hpos : 0 < invEps n)
    (hadv : 1 / (invEps n : ℝ) ≤ ddhAdvantage (F.order d) (F.generator d) (distinguisher n d))
    (hmod : 3 / (2 ^ n : ℝ) ≤ 1 / (12 * (invEps n : ℝ))) :
    ((ProbComp.eval (F.ddhAmplifiedDecider distinguisher invEps n d (α • F.generator d)
      (β • F.generator d) (γ • F.generator d))).toOuterMeasure
      {b | b ≠ decide (γ = α * β)}).toReal ≤ (1 / 2 : ℝ) ^ n := by
  have : Fact (Nat.Prime (F.order d)) := ⟨F.prime_order d⟩
  let N := (n + 3) * (7 * invEps n) ^ 2
  have h7pos : 0 < 7 * invEps n := by positivity
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by positivity : 0 < N)
  let trial := F.ddhSelfReduceDistinguisher distinguisher n d
  let tIn := trial (α • F.generator d) (β • F.generator d) (γ • F.generator d)
  let tReal := trial 0 0 0
  let tRandom := trial 0 0 (F.generator d)
  let pReal :=
    (ProbComp.eval (ddhRealExperiment (F.order d) (F.generator d) (distinguisher n d)) true).toReal
  let pRandom :=
    (ProbComp.eval (ddhRandomExperiment (F.order d) (F.generator d) (distinguisher n d))
      true).toReal
  let ε : ℝ := 1 / (invEps n : ℝ)
  have h12eq : 1 / (12 * (invEps n : ℝ)) = ε / 12 := by dsimp [ε]; ring
  have h7eq' : 1 / ((7 * invEps n : ℕ) : ℝ) = ε / 7 := by dsimp [ε]; push_cast; ring
  have hadv' : ε ≤ |pReal - pRandom| := by
    simpa only [ddhAdvantage, Game.coe_advantage, Game.succProbability,
      ENNReal.coe_toNNReal_eq_toReal, pReal, pRandom, ε] using hadv
  have hmod' : 3 / (2 ^ n : ℝ) ≤ ε / 12 := h12eq ▸ hmod
  have hRealClose (α' β' : ZMod (F.order d)) :
      |(ProbComp.eval (trial (α' • F.generator d) (β' • F.generator d)
        ((α' * β') • F.generator d)) true).toReal - pReal| ≤ ε / 12 := by
    rw [abs_sub_comm]
    refine (abs_succProbability_sub_le_of_advantage_le ?_).trans hmod'
    simpa only [NNReal.coe_div, NNReal.coe_ofNat, NNReal.coe_pow] using
      NNReal.coe_le_coe.mpr
        (F.advantage_ddhRealExperiment_ddhSelfReduceDistinguisher_le distinguisher n d α' β')
  have hRandomClose {α' β' γ' : ZMod (F.order d)} (hγ' : γ' ≠ α' * β') :
      |(ProbComp.eval (trial (α' • F.generator d) (β' • F.generator d)
        (γ' • F.generator d)) true).toReal - pRandom| ≤ ε / 12 := by
    rw [abs_sub_comm]
    refine (abs_succProbability_sub_le_of_advantage_le ?_).trans hmod'
    simpa only [NNReal.coe_div, NNReal.coe_ofNat, NNReal.coe_pow] using
      NNReal.coe_le_coe.mpr
        (F.advantage_ddhRandomExperiment_ddhSelfReduceDistinguisher_le distinguisher n d hγ')
  have hRealRef : |(ProbComp.eval tReal true).toReal - pReal| ≤ ε / 12 := by
    simpa only [zero_smul, mul_zero] using hRealClose 0 0
  have hRandomRef : |(ProbComp.eval tRandom true).toReal - pRandom| ≤ ε / 12 := by
    simpa only [zero_smul, one_smul] using
      hRandomClose (by simp : (1 : ZMod (F.order d)) ≠ 0 * 0)
  let good (t : ProbComp Bool) : Set ℕ :=
    {c | |(c : ℝ) / N - (ProbComp.eval t true).toReal| < 1 / (7 * invEps n : ℕ)}
  have hconc (t : ProbComp Bool) :
      (((ProbComp.eval (OracleComp.countTrue N t)).toOuterMeasure (good t)ᶜ).toReal) ≤
        (1 / 2 : ℝ) ^ (n + 2) := by
    simpa only [good, N, Set.compl_ofPred, not_lt, show n + 3 = (n + 2) + 1 by omega] using
      ProbComp.countTrue_average_deviation_pow (n + 2) (7 * invEps n) h7pos t
  have hdet {cIn cReal cRandom : ℕ} (hcIn : cIn ∈ good tIn) (hcReal : cReal ∈ good tReal)
      (hcRandom : cRandom ∈ good tRandom) :
      decide ((cIn - cReal) + (cReal - cIn) ≤ (cIn - cRandom) + (cRandom - cIn)) =
        decide (γ = α * β) := by
    have hcIn' : |(cIn : ℝ) / N - (ProbComp.eval tIn true).toReal| < ε / 7 := by
      simpa only [good, Set.mem_ofPred_eq, h7eq'] using hcIn
    have hcReal' : |(cReal : ℝ) / N - (ProbComp.eval tReal true).toReal| < ε / 7 := by
      simpa only [good, Set.mem_ofPred_eq, h7eq'] using hcReal
    have hcRandom' : |(cRandom : ℝ) / N - (ProbComp.eval tRandom true).toReal| < ε / 7 := by
      simpa only [good, Set.mem_ofPred_eq, h7eq'] using hcRandom
    have hcmp_iff :
        ((cIn - cReal) + (cReal - cIn) ≤ (cIn - cRandom) + (cRandom - cIn)) ↔
          |(cIn : ℝ) / N - (cReal : ℝ) / N| ≤ |(cIn : ℝ) / N - (cRandom : ℝ) / N| := by
      rw [← @Nat.cast_le ℝ, cast_sub_add_sub_eq_abs, cast_sub_add_sub_eq_abs,
        ← div_le_div_iff_of_pos_right hNpos, ← abs_of_pos hNpos, ← abs_div, ← abs_div,
        abs_of_pos hNpos, sub_div, sub_div]
    by_cases hγ : γ = α * β
    · have hInRef : |(ProbComp.eval tIn true).toReal - pReal| ≤ ε / 12 := by
        simpa only [tIn, hγ] using hRealClose α β
      have hlt :=
        abs_sub_lt_abs_sub_of_close hadv' hInRef hRealRef hRandomRef hcIn' hcReal' hcRandom'
      simp only [hγ, decide_true, hcmp_iff, hlt.le]
    · have hlt := abs_sub_lt_abs_sub_of_close (abs_sub_comm pReal pRandom ▸ hadv')
        (hRandomClose hγ) hRandomRef hRealRef hcIn' hcRandom' hcReal'
      simp only [hγ, decide_false, hcmp_iff, not_le.mpr hlt]
  simp only [ddhAmplifiedDecider, ProbComp.eval_bind, ProbComp.eval_pure]
  exact toOuterMeasure_bind₃_failure_le_pow _ _ _ (good tIn) (good tReal) (good tRandom) _ _ n
    (hconc tIn) (hconc tReal) (hconc tRandom) hdet

/-- **Directional correctness of `ddhAmplifiedDecider`** ([BonehShoup2023], Section 10.11,
Exercise 10.10, p. 426): under the hypotheses of `ddhAmplifiedDecider_error_le_pow`, on every
triple `(α • g, β • g, γ • g)` the decider outputs `decide (γ = α * β)` with probability at least
`1 - (1 / 2) ^ n`. -/
theorem ddhAmplifiedDecider_correct_ge_one_sub_pow (distinguisher : F.DDHDistinguisher)
    (invEps : ℕ → ℕ) (n : ℕ) (d : F.Desc) (α β γ : ZMod (F.order d)) (hpos : 0 < invEps n)
    (hadv : 1 / (invEps n : ℝ) ≤ ddhAdvantage (F.order d) (F.generator d) (distinguisher n d))
    (hmod : 3 / (2 ^ n : ℝ) ≤ 1 / (12 * (invEps n : ℝ))) :
    1 - (1 / 2 : ℝ) ^ n ≤
      (ProbComp.eval (F.ddhAmplifiedDecider distinguisher invEps n d (α • F.generator d)
        (β • F.generator d) (γ • F.generator d)) (decide (γ = α * β))).toReal := by
  have herr := F.ddhAmplifiedDecider_error_le_pow distinguisher invEps n d α β γ hpos hadv hmod
  have hsum := Cslib.Probability.PMF.toOuterMeasure_toReal_add_compl
    (ProbComp.eval (F.ddhAmplifiedDecider distinguisher invEps n d (α • F.generator d)
      (β • F.generator d) (γ • F.generator d))) {decide (γ = α * β)}
  rw [PMF.toOuterMeasure_apply_singleton, Set.compl_singleton_eq] at hsum
  linarith

private theorem three_div_le_one_div_twelve_mul {a b : ℝ} (hb : 0 < b)
    (h : 1 / a ≤ 1 / (36 * b + 1)) : 3 / a ≤ 1 / (12 * b) := by
  have h1 : 1 / a ≤ 1 / (36 * b) :=
    h.trans (one_div_le_one_div_of_le (mul_pos (by norm_num) hb)
      (le_add_of_nonneg_right zero_le_one))
  simpa only [div_eq_mul_one_div 3 a, show 3 * (1 / (36 * b)) = 1 / (12 * b) by ring] using
    mul_le_mul_of_nonneg_left h1 (by norm_num : (0 : ℝ) ≤ 3)

/-- **Worst-case DDH decider with negligible error** ([BonehShoup2023], Exercise 10.10, p. 426):
if `invEps` is computable in polynomial time in unary and `distinguisher` eventually has DDH
advantage at least `1 / invEps n` in the group `d n`, then on *every* sequence of triples
`(α n • g, β n • g, γ n • g)` in `d n`, `ddhAmplifiedDecider` decides whether `γ n = α n * β n`
with negligible error. -/
theorem negligible_ddhAmplifiedDecider_error {distinguisher : F.DDHDistinguisher}
    {invEps : ℕ → ℕ} (hinvEps : ComputableInPolyTime invEps encUnary encUnary)
    (d : ℕ → F.Desc) (α β γ : ∀ n, ZMod (F.order (d n)))
    (hpos : ∀ᶠ n in Filter.atTop, 0 < invEps n)
    (hadv : ∀ᶠ n in Filter.atTop, 1 / (invEps n : ℝ) ≤
      ddhAdvantage (F.order (d n)) (F.generator (d n)) (distinguisher n (d n))) :
    Negligible fun n =>
      ((ProbComp.eval (F.ddhAmplifiedDecider distinguisher invEps n (d n)
        (α n • F.generator (d n)) (β n • F.generator (d n))
        (γ n • F.generator (d n)))).toOuterMeasure
        {b | b ≠ decide (γ n = α n * β n)}).toNNReal := by
  have hgeom : Negligible fun n => ((2⁻¹ : ℝ≥0) ^ n) := by negligible
  have hpoly : PolynomiallyBounded fun n => 36 * invEps n + 1 :=
    ((PolynomiallyBounded.const 36).mul hinvEps.tidy.polynomiallyBounded).add (.const 1)
  have hmod_ev : ∀ᶠ n in Filter.atTop, 3 / (2 ^ n : ℝ) ≤ 1 / (12 * (invEps n : ℝ)) := by
    filter_upwards [hpos, hgeom.eventually_le_inv_polynomial hpoly (fun _ => Nat.succ_pos _)]
      with n hn hlt
    refine three_div_le_one_div_twelve_mul (Nat.cast_pos.mpr hn) ?_
    simpa only [NNReal.coe_pow, NNReal.coe_inv, NNReal.coe_ofNat, inv_pow, one_div,
      Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using hlt
  negligible eventually (by
    filter_upwards [hpos, hadv, hmod_ev] with n hn hadv_n hmod_n
    exact F.ddhAmplifiedDecider_error_le_pow distinguisher invEps n (d n)
      (α n) (β n) (γ n) hn hadv_n hmod_n)

end Cslib.Crypto.PrimeOrderGroupFamily
