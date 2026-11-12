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
import CslibFrontier.Computability.Probabilistic.Repeat
import CslibFrontier.Crypto.Negligible.Basic
import CslibFrontier.Foundations.Data.Nat.Bits
import CslibFrontier.Languages.Probabilistic.Concentration
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF
import CslibFrontier.Probability.PMF.Uniform
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

Adversaries receive and return group elements. Their efficiency is stated on encodings: a CDH
adversary is admissible when one uniform strict PPT machine reads `encCDHInput`, the unary security
parameter, group parameters and encoded elements, and writes the encoding of its output element.
`encCDHInput_apply` and `encDDHInput_apply` give the word layouts.

We prove the implications `DDH ⇒ CDH ⇒ DiscreteLog` between the assumptions from the fixed-group
bounds `Cslib.Crypto.dlAdvantage_le_cdhAdvantage_dlToCDH` and
`Cslib.Crypto.ddhRandomExperiment_cdhToDDH_apply_true_le`, together with the distributional
rerandomisation lemma underlying the random self-reducibility of DDH ([BonehShoup2023],
Section 10.11, Exercises 10.8–10.9, pp. 425–426; `ddhRerandomizeLaw_real` and
`ddhRerandomizeLaw_ideal`) and its word-level form `encodeDDHRerandomize`. The Diffie–Hellman
assumptions are hypotheses, not theorems.

## Main definitions

* `Cslib.Crypto.PrimeOrderGroupFamily.CDHInput`, `Cslib.Crypto.PrimeOrderGroupFamily.DDHInput`:
  the inputs of CDH adversaries and DDH distinguishers.
* `Cslib.Crypto.PrimeOrderGroupFamily.encCDHInput`,
  `Cslib.Crypto.PrimeOrderGroupFamily.encDDHInput`: their encodings.
* `Cslib.Crypto.PrimeOrderGroupFamily.CDHAdversary`, `Cslib.Crypto.PrimeOrderGroupFamily.cdhGame`,
  `Cslib.Crypto.PrimeOrderGroupFamily.CDH`: the Computational Diffie–Hellman game and assumption.
* `Cslib.Crypto.PrimeOrderGroupFamily.dlToCDHAdversary`: the reduction from discrete logarithm to
  CDH.
* `Cslib.Crypto.PrimeOrderGroupFamily.DDHDistinguisher`,
  `Cslib.Crypto.PrimeOrderGroupFamily.ddhRealGame`,
  `Cslib.Crypto.PrimeOrderGroupFamily.ddhRandomGame`, `Cslib.Crypto.PrimeOrderGroupFamily.DDH`:
  the real and random Decisional Diffie–Hellman games and assumption.
* `Cslib.Crypto.PrimeOrderGroupFamily.cdhToDDHDistinguisher`: the reduction from CDH to DDH.
* `Cslib.Crypto.PrimeOrderGroupFamily.ddhRerandomize`,
  `Cslib.Crypto.PrimeOrderGroupFamily.ddhRerandomizeLaw`,
  `Cslib.Crypto.PrimeOrderGroupFamily.encodeDDHRerandomize`: algebraic and word-level DDH
  rerandomisation ([BonehShoup2023], Exercises 10.8–10.9, pp. 425–426).
* `Cslib.Crypto.PrimeOrderGroupFamily.sampleExp`: approximate uniform exponent sampling modulo
  `F.order d` via `ProbComp.sampleModNat` with statistical distance at most `1 / 2 ^ n`.
* `Cslib.Crypto.PrimeOrderGroupFamily.ddhRealRefTuple`,
  `Cslib.Crypto.PrimeOrderGroupFamily.ddhIdealRefTuple`: reference DDH and non-DDH tuples.

## Main results

* `Cslib.Crypto.PrimeOrderGroupFamily.encCDHInput_apply`,
  `Cslib.Crypto.PrimeOrderGroupFamily.encDDHInput_apply`: the input layouts.
* `Cslib.Crypto.PrimeOrderGroupFamily.succProbability_discreteLogGame_le_cdhGame`,
  `Cslib.Crypto.PrimeOrderGroupFamily.CDH.discreteLog`: `CDH` implies `DiscreteLog`.
* `Cslib.Crypto.PrimeOrderGroupFamily.succProbability_cdhGame_le_advantage_ddh_add`,
  `Cslib.Crypto.PrimeOrderGroupFamily.DDH.cdh`,
  `Cslib.Crypto.PrimeOrderGroupFamily.DDH.discreteLog`: `DDH` implies `CDH` and `DiscreteLog`
  when `1 / q` is negligible.
* `Cslib.Crypto.PrimeOrderGroupFamily.ddhRerandomizeLaw_real`,
  `Cslib.Crypto.PrimeOrderGroupFamily.ddhRerandomizeLaw_ideal`: the distributional rerandomisation
  lemma for DDH tuples ([BonehShoup2023], Exercises 10.8–10.9, pp. 425–426).
* `Cslib.Crypto.PrimeOrderGroupFamily.computableInPolyTime_encodeDDHRerandomize`,
  `Cslib.Crypto.PrimeOrderGroupFamily.isPPTOn_sampleExp`,
  `Cslib.Crypto.PrimeOrderGroupFamily.advantage_bind_sampleExp_le`,
  `Cslib.Crypto.PrimeOrderGroupFamily.isPPTOn_ddhSampleModExponents`,
  `Cslib.Crypto.PrimeOrderGroupFamily.dist_sampleModZModLaw_le`: efficient rerandomisation.

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

namespace CDHInput

variable {F}

/-- The words a machine reads for a CDH input: the security parameter, the group parameters and
the encodings of the two public elements. -/
def words (x : F.CDHInput) : ℕ × F.Desc × List Bool × List Bool :=
  (x.secParam, x.groupParameters, F.encode x.groupParameters x.leftPublic,
    F.encode x.groupParameters x.rightPublic)

/-- A CDH input is determined by its words, since element encodings are injective. -/
theorem words_injective : Function.Injective (words (F := F)) := by
  rintro ⟨n, d, u, v⟩ ⟨n', d', u', v'⟩ h
  simp only [words, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, hu, hv⟩ := h
  rw [F.encode_injective d hu, F.encode_injective d hv]

end CDHInput

namespace DDHInput

variable {F}

/-- The words a machine reads for a DDH input: the security parameter, the group parameters and
the encodings of the three elements. -/
def words (x : F.DDHInput) : ℕ × F.Desc × List Bool × List Bool × List Bool :=
  (x.secParam, x.groupParameters, F.encode x.groupParameters x.leftPublic,
    F.encode x.groupParameters x.rightPublic, F.encode x.groupParameters x.candidateShared)

/-- A DDH input is determined by its words, since element encodings are injective. -/
theorem words_injective : Function.Injective (words (F := F)) := by
  rintro ⟨⟨n, d, u, v⟩, w⟩ ⟨⟨n', d', u', v'⟩, w'⟩ h
  simp only [words, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, hu, hv, hw⟩ := h
  rw [F.encode_injective d hu, F.encode_injective d hv, F.encode_injective d hw]

end DDHInput

/-- The encoding of a CDH input: its `CDHInput.words` in order, each framed except the last
(`encCDHInput_apply`). -/
def encCDHInput : F.CDHInput ↪ List Bool :=
  (⟨CDHInput.words, CDHInput.words_injective⟩ : F.CDHInput ↪ _).trans
    (encPair encUnary (encPair F.encDesc (encPair encBits encBits)))

/-- The encoding of a DDH input: its `DDHInput.words` in order, each framed except the last
(`encDDHInput_apply`). -/
def encDDHInput : F.DDHInput ↪ List Bool :=
  (⟨DDHInput.words, DDHInput.words_injective⟩ : F.DDHInput ↪ _).trans
    (encPair encUnary (encPair F.encDesc (encPair encBits (encPair encBits encBits))))

/-- The CDH input layout: unary security parameter, group parameters and first element framed,
then the second element. -/
theorem encCDHInput_apply (x : F.CDHInput) :
    F.encCDHInput x = frame (encUnary x.secParam) ++ frame (F.encDesc x.groupParameters) ++
      frame (F.encode x.groupParameters x.leftPublic) ++
        F.encode x.groupParameters x.rightPublic := by
  simp [encCDHInput, CDHInput.words, encPair, encBits]

/-- The DDH input layout: unary security parameter, group parameters and the first two elements
framed, then the candidate shared element. -/
theorem encDDHInput_apply (x : F.DDHInput) :
    F.encDDHInput x = frame (encUnary x.secParam) ++ frame (F.encDesc x.groupParameters) ++
      frame (F.encode x.groupParameters x.leftPublic) ++
        frame (F.encode x.groupParameters x.rightPublic) ++
          F.encode x.groupParameters x.candidateShared := by
  simp [encDDHInput, DDHInput.words, encPair, encBits]

/-- A Diffie–Hellman tuple `(u, v, w)` of group elements, each given by its encoding word, as in
the tuple `(encode (α • g), encode (β • g), encode (γ • g))` of the DDH experiments. The words `u`
and `v` are framed; `w` is not. -/
abbrev encDDHTuple : List Bool × List Bool × List Bool ↪ List Bool :=
  encPair encBits (encPair encBits encBits)

namespace CDHInput

variable {F}

/-- Reading the words of a CDH input copies its encoding. -/
theorem computableInPolyTime_words :
    ComputableInPolyTime (words (F := F)) F.encCDHInput
      (encPair encUnary (encPair F.encDesc (encPair encBits encBits))) :=
  .of_eq fun _ => rfl

/-- Reading the security parameter of a computed CDH input. -/
@[fun_prop] theorem computableInPolyTime_secParam {α : Type} {enc : α ↪ List Bool}
    {g : α → F.CDHInput} (h : ComputableInPolyTime g enc F.encCDHInput) :
    ComputableInPolyTime (fun a => (g a).secParam) enc encUnary :=
  (computableInPolyTime_words.comp h).fst'

/-- Reading the group parameters of a computed CDH input. -/
@[fun_prop] theorem computableInPolyTime_groupParameters {α : Type} {enc : α ↪ List Bool}
    {g : α → F.CDHInput} (h : ComputableInPolyTime g enc F.encCDHInput) :
    ComputableInPolyTime (fun a => (g a).groupParameters) enc F.encDesc :=
  (computableInPolyTime_words.comp h).snd'.fst'

/-- Reading the encoded first element of a computed CDH input. -/
@[fun_prop] theorem computableInPolyTime_encode_leftPublic {α : Type} {enc : α ↪ List Bool}
    {g : α → F.CDHInput} (h : ComputableInPolyTime g enc F.encCDHInput) :
    ComputableInPolyTime (fun a => F.encode (g a).groupParameters (g a).leftPublic) enc encBits :=
  (computableInPolyTime_words.comp h).snd'.snd'.fst'

/-- Reading the encoded second element of a computed CDH input. -/
@[fun_prop] theorem computableInPolyTime_encode_rightPublic {α : Type} {enc : α ↪ List Bool}
    {g : α → F.CDHInput} (h : ComputableInPolyTime g enc F.encCDHInput) :
    ComputableInPolyTime (fun a => F.encode (g a).groupParameters (g a).rightPublic) enc encBits :=
  (computableInPolyTime_words.comp h).snd'.snd'.snd'

end CDHInput

namespace DDHInput

variable {F}

/-- Reading the words of a DDH input copies its encoding. -/
theorem computableInPolyTime_words :
    ComputableInPolyTime (words (F := F)) F.encDDHInput
      (encPair encUnary (encPair F.encDesc (encPair encBits (encPair encBits encBits)))) :=
  .of_eq fun _ => rfl

/-- Dropping the candidate shared element of a computed DDH input. -/
@[fun_prop] theorem computableInPolyTime_toCDHInput {α : Type} {enc : α ↪ List Bool}
    {g : α → F.DDHInput} (h : ComputableInPolyTime g enc F.encDDHInput) :
    ComputableInPolyTime (fun a => (g a).toCDHInput) enc F.encCDHInput :=
  have hwords : ComputableInPolyTime (toCDHInput (F := F)) F.encDDHInput F.encCDHInput :=
    ComputableInPolyTime.of_enc_eq
      (f := fun x : F.DDHInput => (x.words.1, x.words.2.1, x.words.2.2.1, x.words.2.2.2.1))
      (by have := computableInPolyTime_words (F := F); fun_prop) fun _ => rfl
  hwords.comp h

/-- Reading the encoded candidate shared element of a computed DDH input. -/
@[fun_prop] theorem computableInPolyTime_encode_candidateShared {α : Type} {enc : α ↪ List Bool}
    {g : α → F.DDHInput} (h : ComputableInPolyTime g enc F.encDDHInput) :
    ComputableInPolyTime (fun a => F.encode (g a).groupParameters (g a).candidateShared) enc
      encBits :=
  (computableInPolyTime_words.comp h).snd'.snd'.snd'.snd'

/-- Building a DDH input from computed parts. -/
theorem computableInPolyTime_mk {α : Type} {enc : α ↪ List Bool} {n : α → ℕ} {d : α → F.Desc}
    {u v w : (a : α) → F.Carrier (d a)} (hn : ComputableInPolyTime n enc encUnary)
    (hd : ComputableInPolyTime d enc F.encDesc)
    (hu : ComputableInPolyTime (fun a => F.encode (d a) (u a)) enc encBits)
    (hv : ComputableInPolyTime (fun a => F.encode (d a) (v a)) enc encBits)
    (hw : ComputableInPolyTime (fun a => F.encode (d a) (w a)) enc encBits) :
    ComputableInPolyTime (fun a => (⟨⟨n a, d a, u a, v a⟩, w a⟩ : F.DDHInput)) enc
      F.encDDHInput :=
  .of_enc_eq (hn.prod (hd.prod (hu.prod (hv.prod hw)))) fun _ => rfl

end DDHInput

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
and two elements of `F.Carrier d`, it outputs an element of `F.Carrier d`. `CDH` states its
efficiency on encodings. -/
abbrev CDHAdversary : Type :=
  ℕ → (d : F.Desc) → F.Carrier d → F.Carrier d → ProbComp (F.Carrier d)

/-- The Computational Diffie–Hellman experiment ([BonehShoup2023], Attack Game 10.5): choose
group parameters `d` using the arbitrary setup law, then run `Cslib.Crypto.cdhExperiment` in the
group `F.Carrier d`. No efficient sampler for setup is required. -/
noncomputable def cdhGame (setup : ℕ → PMF F.Desc) (adversary : F.CDHAdversary) (n : ℕ) :
    Game := do
  let d ← setup n
  ProbComp.eval (cdhExperiment (F.order d) (F.generator d) (adversary n d))

/-- The Computational Diffie–Hellman assumption for a family and a setup law: every CDH adversary
realized by a uniform strict PPT machine, which reads `encCDHInput` and writes the encoding of the
output element, wins `cdhGame` with negligible probability. -/
def CDH (setup : ℕ → PMF F.Desc) : Prop :=
  ∀ adversary : F.CDHAdversary,
    IsPPTOn F.encCDHInput encBits (fun x => F.encode x.groupParameters <$>
      adversary x.secParam x.groupParameters x.leftPublic x.rightPublic) →
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
    F.discreteLogGame setup adversary n = (do
      let d ← setup n
      ProbComp.eval
        (dlExperiment (F.order d) (F.generator d) (F.discreteLogAdversary adversary n d))) := by
  simp [discreteLogGame, dlExperiment, discreteLogAdversary, PMF.map, Function.comp_def]

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
  refine ENNReal.toNNReal_mono (PMF.apply_ne_top _ _) ?_
  refine PMF.bind_apply_mono_on_support _ _ fun d _ => ?_
  exact (ENNReal.toNNReal_le_toNNReal (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
    (dlAdvantage_le_cdhAdvantage_dlToCDH _ _ _)

/-- The discrete-logarithm-to-CDH reduction is uniform strict PPT when the discrete-logarithm
adversary is. -/
theorem isPPTOn_dlToCDHAdversary
    {adversary : ℕ → F.Desc × List Bool → ProbComp (List Bool)}
    (hA : IsPPTOn (encPair encUnary (encPair F.encDesc encBits)) encBits
      (fun input => adversary input.1 input.2)) :
    IsPPTOn F.encCDHInput encBits fun x => F.encode x.groupParameters <$>
      F.dlToCDHAdversary adversary x.secParam x.groupParameters x.leftPublic x.rightPublic := by
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
  have hcdh := h _ (F.isPPTOn_dlToCDHAdversary hA)
  negligible using F.succProbability_discreteLogGame_le_cdhGame setup adversary

/-! ### Decisional Diffie–Hellman (DDH) -/

/-- A DDH distinguisher over the family: given the security parameter, public group parameters
`d` and three elements of `F.Carrier d`, it outputs a bit. `DDH` states its efficiency on
encodings. -/
abbrev DDHDistinguisher : Type :=
  ℕ → (d : F.Desc) → F.Carrier d → F.Carrier d → F.Carrier d → ProbComp Bool

/-- The real DDH game ([BonehShoup2023], Attack Game 10.6, Experiment 0): choose group parameters
`d` using the arbitrary setup law, then run `Cslib.Crypto.ddhRealExperiment` in `F.Carrier d`. -/
noncomputable def ddhRealGame (setup : ℕ → PMF F.Desc) (distinguisher : F.DDHDistinguisher)
    (n : ℕ) : Game := do
  let d ← setup n
  ProbComp.eval (ddhRealExperiment (F.order d) (F.generator d) (distinguisher n d))

/-- The random DDH game ([BonehShoup2023], Attack Game 10.6, Experiment 1): choose group
parameters `d` using the arbitrary setup law, then run `Cslib.Crypto.ddhRandomExperiment` in
`F.Carrier d`. -/
noncomputable def ddhRandomGame (setup : ℕ → PMF F.Desc) (distinguisher : F.DDHDistinguisher)
    (n : ℕ) : Game := do
  let d ← setup n
  ProbComp.eval (ddhRandomExperiment (F.order d) (F.generator d) (distinguisher n d))

/-- The Decisional Diffie–Hellman assumption for a family and a setup law: every DDH
distinguisher realized by a uniform strict PPT machine reading `encDDHInput` has negligible
advantage between `ddhRealGame` and `ddhRandomGame`. -/
def DDH (setup : ℕ → PMF F.Desc) : Prop :=
  Game.Indistinguishable (F.ddhRealGame setup) (F.ddhRandomGame setup) fun distinguisher =>
    IsPPTOn F.encDDHInput encBool fun x =>
      distinguisher x.secParam x.groupParameters x.leftPublic x.rightPublic x.candidateShared

/-- A certified DDH distinguisher run on computed inputs is uniform strict PPT. -/
theorem isPPTOn_ddhDistinguisher_comp {distinguisher : F.DDHDistinguisher}
    (hD : IsPPTOn F.encDDHInput encBool fun x =>
      distinguisher x.secParam x.groupParameters x.leftPublic x.rightPublic x.candidateShared)
    {α : Type} {enc : α ↪ List Bool} {n : α → ℕ} {d : α → F.Desc}
    {u v w : (a : α) → F.Carrier (d a)} (hn : ComputableInPolyTime n enc encUnary)
    (hd : ComputableInPolyTime d enc F.encDesc)
    (hu : ComputableInPolyTime (fun a => F.encode (d a) (u a)) enc encBits)
    (hv : ComputableInPolyTime (fun a => F.encode (d a) (v a)) enc encBits)
    (hw : ComputableInPolyTime (fun a => F.encode (d a) (w a)) enc encBits) :
    IsPPTOn enc encBool fun a => distinguisher (n a) (d a) (u a) (v a) (w a) :=
  hD.preprocess (DDHInput.computableInPolyTime_mk hn hd hu hv hw)

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
whenever every supported group order is at least `m`. -/
theorem ddhRandomGame_cdhToDDHDistinguisher_true_le (setup : ℕ → PMF F.Desc)
    (adversary : F.CDHAdversary) (n m : ℕ) (hm : ∀ d ∈ (setup n).support, m ≤ F.order d) :
    F.ddhRandomGame setup (F.cdhToDDHDistinguisher adversary) n true ≤ (m : ℝ≥0∞)⁻¹ :=
  PMF.bind_apply_le_on_support _ fun d hd =>
    (ddhRandomExperiment_cdhToDDH_apply_true_le _ _ (F.smul_generator_injective d) _).trans
      (ENNReal.inv_le_inv.mpr (Nat.cast_le.mpr (hm d hd)))

/-- **Quantitative reduction from CDH to DDH**: when every supported group at parameter `n` has
order at least `m > 0`, any CDH adversary's success probability is at most the DDH distinguishing
advantage of `cdhToDDHDistinguisher` plus `1 / m`. -/
theorem succProbability_cdhGame_le_advantage_ddh_add (setup : ℕ → PMF F.Desc)
    (adversary : F.CDHAdversary) (n m : ℕ) (hm0 : 0 < m)
    (hm : ∀ d ∈ (setup n).support, m ≤ F.order d) :
    Game.succProbability (F.cdhGame setup adversary n) ≤
      Game.advantage (F.ddhRealGame setup (F.cdhToDDHDistinguisher adversary) n)
        (F.ddhRandomGame setup (F.cdhToDDHDistinguisher adversary) n) + 1 / m := by
  have hrandom :
      Game.succProbability (F.ddhRandomGame setup (F.cdhToDDHDistinguisher adversary) n) ≤
        1 / m := by
    have htop : (m : ℝ≥0∞)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr (Nat.cast_ne_zero.mpr hm0.ne')
    simpa only [one_div, ENNReal.toNNReal_inv, ENNReal.toNNReal_natCast] using
      ENNReal.toNNReal_mono htop
        (F.ddhRandomGame_cdhToDDHDistinguisher_true_le setup adversary n m hm)
  game_trans
    [F.ddhRealGame setup (F.cdhToDDHDistinguisher adversary) n,
     F.ddhRandomGame setup (F.cdhToDDHDistinguisher adversary) n]
    using [F.ddhRealGame_cdhToDDHDistinguisher setup adversary n, le_rfl, hrandom]

/-- The CDH-to-DDH reduction is uniform strict PPT when the CDH adversary is. -/
theorem isPPTOn_cdhToDDHDistinguisher {adversary : F.CDHAdversary}
    (hA : IsPPTOn F.encCDHInput encBits (fun x => F.encode x.groupParameters <$>
      adversary x.secParam x.groupParameters x.leftPublic x.rightPublic)) :
    IsPPTOn F.encDDHInput encBool fun x => F.cdhToDDHDistinguisher adversary x.secParam
      x.groupParameters x.leftPublic x.rightPublic x.candidateShared := by
  refine ((hA.preprocess (prepare := DDHInput.toCDHInput) (by fun_prop)).map_with
    (f := fun x z => decide (z = F.encode x.groupParameters x.candidateShared))
    (by fun_prop)).congr fun x => ?_
  simp [cdhToDDHDistinguisher, cdhToDDH, (F.encode_injective _).eq_iff]

/-- **DDH implies CDH** when every supported group at parameter `n` has order at least `m n > 0`
and `1 / m n` is negligible. -/
theorem DDH.cdh {F : PrimeOrderGroupFamily} {setup : ℕ → PMF F.Desc} (hDDH : F.DDH setup)
    {m : ℕ → ℕ} (hm0 : ∀ n, 0 < m n) (hm : ∀ n, ∀ d ∈ (setup n).support, m n ≤ F.order d)
    (hinv : Negligible fun n => (1 / m n : ℝ≥0)) : F.CDH setup := by
  intro adversary hA
  have hddh := hDDH _ (F.isPPTOn_cdhToDDHDistinguisher hA)
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

/-- The ideal DDH tuple distribution on `F.Carrier d`. -/
noncomputable def ddhIdealTupleLaw (d : F.Desc) :
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
    PMF.uniformOfFintype_bind_equiv (Equiv.addLeft β)
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
    exact PMF.uniformOfFintype_bind_equiv (Equiv.addLeft (r * α))
      (fun α' => (PMF.uniformOfFintype (ZMod (F.order d))).bind fun β' =>
        PMF.pure (α' • F.generator d, β' • F.generator d, (α' * β') • F.generator d))
  simp_rw [hs₁, PMF.bind_const]

/-- **Random self-reducibility of DDH (ideal case)**: re-randomizing any fixed non-DDH tuple
`(α • g, β • g, γ • g)` with `γ ≠ α * β` yields the exact uniform ideal DDH tuple distribution. -/
theorem ddhRerandomizeLaw_ideal (d : F.Desc) {α β γ : ZMod (F.order d)} (hγ : γ ≠ α * β) :
    F.ddhRerandomizeLaw d (α • F.generator d) (β • F.generator d) (γ • F.generator d) =
      F.ddhIdealTupleLaw d := by
  simp only [ddhRerandomizeLaw, ddhIdealTupleLaw, ddhRerandomize_smul_generator,
    PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure]
  have hs₂ (r α' : ZMod (F.order d)) :
      ((PMF.uniformOfFintype (ZMod (F.order d))).bind fun s₂ =>
        PMF.pure (α' • F.generator d, (β + s₂) • F.generator d,
          (α' * (β + s₂) + r * (γ - α * β)) • F.generator d)) =
      ((PMF.uniformOfFintype (ZMod (F.order d))).bind fun β' =>
        PMF.pure (α' • F.generator d, β' • F.generator d,
          (α' * β' + r * (γ - α * β)) • F.generator d)) :=
    PMF.uniformOfFintype_bind_equiv (Equiv.addLeft β)
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
    exact PMF.uniformOfFintype_bind_equiv (Equiv.addLeft (r * α))
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

/-! ### Efficient word-level DDH random self-reduction -/

/-- Word-level DDH tuple re-randomization ([BonehShoup2023], Exercises 10.8–10.9, pp. 425–426):
given `(d, (u, v, w), r, s₁, s₂)` on encoded group elements `u, v, w : List Bool` and
natural-number exponents `r, s₁, s₂ : ℕ`, evaluate the encoded tuple corresponding to
`ddhRerandomize`. -/
def encodeDDHRerandomize
    (input : F.Desc × (List Bool × List Bool × List Bool) × ℕ × ℕ × ℕ) :
    List Bool × List Bool × List Bool :=
  let (d, (u, v, w), r, s₁, s₂) := input
  let g := F.encode d (F.generator d)
  (F.add (d, F.smul (d, r, u), F.smul (d, s₁, g)),
    F.add (d, v, F.smul (d, s₂, g)),
    F.add (d,
      F.add (d,
        F.add (d, F.smul (d, r, w), F.smul (d, r * s₂, u)),
        F.smul (d, s₁, v)),
      F.smul (d, s₁ * s₂, g)))

/-- `encodeDDHRerandomize` evaluates `ddhRerandomize` on encoded group elements. -/
@[simp] theorem encodeDDHRerandomize_encode (d : F.Desc) (u v w : F.Carrier d) (r s₁ s₂ : ℕ) :
    F.encodeDDHRerandomize (d, (F.encode d u, F.encode d v, F.encode d w), r, s₁, s₂) =
      let (u', v', w') := F.ddhRerandomize d u v w
        (r : ZMod (F.order d)) (s₁ : ZMod (F.order d)) (s₂ : ZMod (F.order d))
      (F.encode d u', F.encode d v', F.encode d w') := by
  simp only [encodeDDHRerandomize, ddhRerandomize, F.smul_encode, F.add_encode, Nat.cast_mul]

/-- Evaluating `encodeDDHRerandomize` at `.val` of exponents in `ZMod (F.order d)` agrees with
`ddhRerandomize`. -/
theorem encodeDDHRerandomize_val (d : F.Desc) (u v w : F.Carrier d)
    (r s₁ s₂ : ZMod (F.order d)) :
    F.encodeDDHRerandomize (d, (F.encode d u, F.encode d v, F.encode d w), r.val, s₁.val, s₂.val) =
      let (u', v', w') := F.ddhRerandomize d u v w r s₁ s₂
      (F.encode d u', F.encode d v', F.encode d w') := by
  simp only [encodeDDHRerandomize_encode, ZMod.natCast_zmod_val]

/-- Word-level DDH tuple re-randomization is computable in polynomial time. -/
theorem computableInPolyTime_encodeDDHRerandomize :
    ComputableInPolyTime F.encodeDDHRerandomize
      (encPair F.encDesc
        (encPair encDDHTuple
          (encPair encNat (encPair encNat encNat))))
      encDDHTuple := by
  let encTuple := encPair encBits (encPair encBits encBits)
  let encExps := encPair encNat (encPair encNat encNat)
  have hd := ComputableInPolyTime.fst F.encDesc (encPair encTuple encExps)
  have h2 := ComputableInPolyTime.snd F.encDesc (encPair encTuple encExps)
  have htuple := (ComputableInPolyTime.fst encTuple encExps).comp h2
  have hexps := (ComputableInPolyTime.snd encTuple encExps).comp h2
  have hu := (ComputableInPolyTime.fst encBits (encPair encBits encBits)).comp htuple
  have hvw := (ComputableInPolyTime.snd encBits (encPair encBits encBits)).comp htuple
  have hv := (ComputableInPolyTime.fst encBits encBits).comp hvw
  have hw := (ComputableInPolyTime.snd encBits encBits).comp hvw
  have hr := (ComputableInPolyTime.fst encNat (encPair encNat encNat)).comp hexps
  have hs := (ComputableInPolyTime.snd encNat (encPair encNat encNat)).comp hexps
  have hs₁ := (ComputableInPolyTime.fst encNat encNat).comp hs
  have hs₂ := (ComputableInPolyTime.snd encNat encNat).comp hs
  have hg := F.computableInPolyTime_generator.comp hd
  have hru := F.computableInPolyTime_smul.comp (hd.prod (hr.prod hu))
  have hs₁g := F.computableInPolyTime_smul.comp (hd.prod (hs₁.prod hg))
  have hs₂g := F.computableInPolyTime_smul.comp (hd.prod (hs₂.prod hg))
  have hrw := F.computableInPolyTime_smul.comp (hd.prod (hr.prod hw))
  have hrs₂u := F.computableInPolyTime_smul.comp (hd.prod ((hr.binary_mul' hs₂).prod hu))
  have hs₁v := F.computableInPolyTime_smul.comp (hd.prod (hs₁.prod hv))
  have hs₁s₂g := F.computableInPolyTime_smul.comp (hd.prod ((hs₁.binary_mul' hs₂).prod hg))
  have hc₁ := F.computableInPolyTime_add.comp (hd.prod (hru.prod hs₁g))
  have hc₂ := F.computableInPolyTime_add.comp (hd.prod (hv.prod hs₂g))
  have hc₃₁ := F.computableInPolyTime_add.comp (hd.prod (hrw.prod hrs₂u))
  have hc₃₂ := F.computableInPolyTime_add.comp (hd.prod (hc₃₁.prod hs₁v))
  have hc₃ := F.computableInPolyTime_add.comp (hd.prod (hc₃₂.prod hs₁s₂g))
  exact hc₁.prod (hc₂.prod hc₃)

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

/-- Sample three independent nearly-uniform exponents modulo `F.order d` at statistical distance
at most `1 / 2 ^ n` each using `ProbComp.sampleModNat ((F.order d).size + n) (F.order d)`
(original). -/
noncomputable def ddhSampleModExponents (n : ℕ) (d : F.Desc) : ProbComp (ℕ × ℕ × ℕ) := do
  let r ← ProbComp.sampleModNat ((F.order d).size + n) (F.order d)
  let s₁ ← ProbComp.sampleModNat ((F.order d).size + n) (F.order d)
  let s₂ ← ProbComp.sampleModNat ((F.order d).size + n) (F.order d)
  return (r, s₁, s₂)

/-- `ddhSampleModExponents` is uniform strict PPT (original). -/
theorem isPPTOn_ddhSampleModExponents :
    IsPPTOn (encPair encUnary F.encDesc) (encPair encNat (encPair encNat encNat))
      (fun input => F.ddhSampleModExponents input.1 input.2) := by
  let encIn := encPair encUnary F.encDesc
  have hn := ComputableInPolyTime.fst encUnary F.encDesc
  have hd := ComputableInPolyTime.snd encUnary F.encDesc
  have horder := F.computableInPolyTime_order.comp hd
  have hbits := (ComputableInPolyTime.binary_size.comp horder).unary_add' hn
  have hsample := isPPTOn_sampleModNat hbits horder
  have hp1 := ComputableInPolyTime.fst (encPair encIn encNat) encNat
  have hq1 := ComputableInPolyTime.fst (encPair (encPair encIn encNat) encNat) encNat
  unfold ddhSampleModExponents
  refine hsample.bind_with ?_
  refine (hsample.preprocess (prepare := Prod.fst) (.fst encIn encNat)).bind_with ?_
  refine (hsample.preprocess
    (prepare := fun p : ((ℕ × F.Desc) × ℕ) × ℕ => p.1.1)
    ((ComputableInPolyTime.fst encIn encNat).comp hp1)).bind_with ?_
  exact (((ComputableInPolyTime.snd encIn encNat).comp (hp1.comp hq1)).prod
    (((ComputableInPolyTime.snd (encPair encIn encNat) encNat).comp hq1).prod
      (.snd (encPair (encPair encIn encNat) encNat) encNat))).isPPTOn

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

/-! ### Worst-case DDH decider via Chernoff amplification ([BonehShoup2023], Exercise 10.10) -/

/-- Canonical encoded real DDH tuple `(0 • g, 0 • g, (0 * 0) • g)` for group parameters `d`,
computed in polynomial time via `F.smul (d, 0, F.encode d (F.generator d))`
([BonehShoup2023], Section 10.11, Exercise 10.10, p. 426). -/
def ddhRealRefTuple (d : F.Desc) : List Bool × List Bool × List Bool :=
  let g := F.encode d (F.generator d)
  let z := F.smul (d, 0, g)
  (z, z, z)

/-- Canonical encoded non-DDH tuple `(0 • g, 0 • g, 1 • g)` for group parameters `d`
(since `1 ≠ 0 * 0` in `ZMod (F.order d)` for prime `F.order d`;
[BonehShoup2023], Section 10.11, Exercise 10.10, p. 426). -/
def ddhIdealRefTuple (d : F.Desc) : List Bool × List Bool × List Bool :=
  let g := F.encode d (F.generator d)
  let z := F.smul (d, 0, g)
  (z, z, g)

/-- `ddhRealRefTuple` equals the encoded tuple `((0 : ZMod q) • g, (0 : ZMod q) • g,
((0 : ZMod q) * 0) • g)`. -/
@[simp] theorem ddhRealRefTuple_eq_encode (d : F.Desc) :
    F.ddhRealRefTuple d =
      (F.encode d ((0 : ZMod (F.order d)) • F.generator d),
        F.encode d ((0 : ZMod (F.order d)) • F.generator d),
        F.encode d (((0 : ZMod (F.order d)) * 0) • F.generator d)) := by
  simp [ddhRealRefTuple, F.smul_encode]

/-- `ddhIdealRefTuple` equals the encoded tuple `((0 : ZMod q) • g, (0 : ZMod q) • g,
(1 : ZMod q) • g)`. -/
@[simp] theorem ddhIdealRefTuple_eq_encode (d : F.Desc) :
    F.ddhIdealRefTuple d =
      (F.encode d ((0 : ZMod (F.order d)) • F.generator d),
        F.encode d ((0 : ZMod (F.order d)) • F.generator d),
        F.encode d ((1 : ZMod (F.order d)) • F.generator d)) := by
  simp [ddhIdealRefTuple, F.smul_encode]

/-- `ddhRealRefTuple` is computable in polynomial time. -/
theorem computableInPolyTime_ddhRealRefTuple :
    ComputableInPolyTime F.ddhRealRefTuple F.encDesc
      encDDHTuple := by
  have hz := F.computableInPolyTime_smul.comp
    (ComputableInPolyTime.id'.prod ((ComputableInPolyTime.const 0).prod
      F.computableInPolyTime_generator))
  exact hz.prod (hz.prod hz)

/-- `ddhIdealRefTuple` is computable in polynomial time. -/
theorem computableInPolyTime_ddhIdealRefTuple :
    ComputableInPolyTime F.ddhIdealRefTuple F.encDesc
      encDDHTuple := by
  have hg := F.computableInPolyTime_generator
  have hz := F.computableInPolyTime_smul.comp
    (ComputableInPolyTime.id'.prod ((ComputableInPolyTime.const 0).prod hg))
  exact hz.prod (hz.prod hg)

end Cslib.Crypto.PrimeOrderGroupFamily
