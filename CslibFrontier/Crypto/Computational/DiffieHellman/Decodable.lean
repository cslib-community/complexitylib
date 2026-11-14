/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.DiffieHellman
public import CslibFrontier.Crypto.Computational.DiscreteLog.Decodable
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Probabilistic.PPT.Capture
import CslibFrontier.Computability.Probabilistic.PPT.Extension
import CslibFrontier.Crypto.Game.Order
import CslibFrontier.Probability.PMF
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Map
import CslibFrontier.Tactic.PolyTime.Init

/-!
# Word-level CDH and equivalence with typed CDH for decodable families

For an arbitrary `PrimeOrderGroupFamily`, the typed assumption `PrimeOrderGroupFamily.CDH`
quantifies over adversaries that output elements of `F.Carrier d`, whereas a word-level CDH
adversary outputs an arbitrary bit string `List Bool` and wins when that word equals
`F.encode d ((a * b) • F.generator d)` (`PrimeOrderGroupFamily.cdhWordGame` and
`PrimeOrderGroupFamily.WordCDH`).

`WordCDH` always implies `CDH` (`PrimeOrderGroupFamily.WordCDH.cdh`) via `IsPPTOn.exists_factor`
and injectivity of `F.encode d`. When the family is decodable
(`DecodablePrimeOrderGroupFamily`), decoding any candidate word with fallback `0`
(`DecodablePrimeOrderGroupFamily.wordToTypedCDHAdversary`) preserves uniform strict PPT
(`isPPT_wordToTypedCDHAdversary`) and never lowers success probability
(`succProbability_cdhWordGame_le_cdhGame`). Hence `CDH ↔ WordCDH`
(`DecodablePrimeOrderGroupFamily.cdh_iff_encoded`), and `DDH` implies word-level `WordCDH` when
`1 / order` is negligible (`DecodablePrimeOrderGroupFamily.DDH.wordCDH`).

## Main definitions

* `Cslib.Crypto.PrimeOrderGroupFamily.encWordCDHInput`: word layout encoding `(n, d, u, v)` for
  word-level CDH adversaries.
* `Cslib.Crypto.PrimeOrderGroupFamily.cdhWordGame`: word-level Computational Diffie–Hellman game.
* `Cslib.Crypto.PrimeOrderGroupFamily.WordCDH`: the word-level CDH assumption.
* `Cslib.Crypto.DecodablePrimeOrderGroupFamily.wordToTypedCDHAdversary`: decode a word-level CDH
  adversary's output into `F.Carrier d` with fallback `0`.

## Main results

* `Cslib.Crypto.PrimeOrderGroupFamily.WordCDH.cdh`: `WordCDH` implies `CDH` for every
  `PrimeOrderGroupFamily`.
* `Cslib.Crypto.DecodablePrimeOrderGroupFamily.isPPT_wordToTypedCDHAdversary`:
  `wordToTypedCDHAdversary` preserves uniform strict PPT.
* `Cslib.Crypto.DecodablePrimeOrderGroupFamily.cdh_iff_encoded`: for a decodable family,
  `F.CDH setup ↔ F.WordCDH setup`.
* `Cslib.Crypto.DecodablePrimeOrderGroupFamily.DDH.wordCDH`: for a decodable family, `F.DDH setup`
  implies `F.WordCDH setup` when every supported group has prime order at least `m n > 0` with
  `1 / m n` negligible.
-/

public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM
open scoped NNReal

namespace PrimeOrderGroupFamily

variable (F : PrimeOrderGroupFamily)

/-- Encoding of word-level CDH inputs `(n, d, u, v)`. -/
abbrev encWordCDHInput : (ℕ × F.Desc × List Bool × List Bool) ↪ List Bool :=
  encPair encUnary (encPair F.encDesc (encPair encBits encBits))

/-- The word-level Computational Diffie–Hellman game: draw `d ← setup n` and uniform exponents
`a, b : ZMod (F.order d)`, give `(d, encode (a • g), encode (b • g))` to `adversary n`, and accept
when it outputs `encode ((a * b) • g)`. -/
noncomputable def cdhWordGame (setup : ℕ → PMF F.Desc)
    (adversary : ℕ → F.Desc × List Bool × List Bool → ProbComp (List Bool)) (n : ℕ) : Game :=
  Game.withSetup (setup n) fun d => do
    let a ← $ᵗ ZMod (F.order d)
    let b ← $ᵗ ZMod (F.order d)
    let guess ← adversary n (d, F.encode d (a • F.generator d), F.encode d (b • F.generator d))
    return decide (guess = F.encode d ((a * b) • F.generator d))

/-- The word-level Computational Diffie–Hellman assumption: every uniform strict PPT adversary on
encoded CDH instances `encWordCDHInput` wins `cdhWordGame` with negligible probability. -/
def WordCDH (setup : ℕ → PMF F.Desc) : Prop :=
  ∀ adversary : ℕ → F.Desc × List Bool × List Bool → ProbComp (List Bool),
    IsPPTOn F.encWordCDHInput encBits (fun x => adversary x.1 x.2) →
      Negligible fun n => Game.succProbability (F.cdhWordGame setup adversary n)

/-- Word-level `WordCDH` always implies typed `CDH`: any PPT typed CDH adversary factors through a
word-level PPT program via `IsPPTOn.exists_factor` and `encBits = id`, and injectivity of
`F.encode` preserves the success event identically. -/
theorem WordCDH.cdh {F : PrimeOrderGroupFamily} {setup : ℕ → PMF F.Desc}
    (h : F.WordCDH setup) : F.CDH setup := by
  intro adversary hA
  obtain ⟨W, hW, hWA⟩ := hA.exists_factor F.encCDHInput_apply
    (decode := fun w => w) ComputableInPolyTime.id' fun _ => rfl
  have hnegl := h (fun n t => W (n, t)) hW
  refine hnegl.congr fun n => ?_
  congr 1
  simp only [cdhGame, cdhWordGame, Game.withSetup, cdhExperiment,
    ProbComp.eval_bind, ProbComp.eval_uniform, ProbComp.eval_pure]
  refine congrArg (PMF.bind (setup n)) (funext fun d => ?_)
  refine congrArg (PMF.bind (PMF.uniformOfFintype (ZMod (F.order d)))) (funext fun a => ?_)
  refine congrArg (PMF.bind (PMF.uniformOfFintype (ZMod (F.order d)))) (funext fun b => ?_)
  have hmap := hWA ⟨n, d, a • F.generator d, b • F.generator d⟩
  rw [← hmap, ProbComp.eval_map, PMF.bind_map]
  refine congrArg (PMF.bind (ProbComp.eval (adversary n d (a • F.generator d)
    (b • F.generator d)))) (funext fun z => ?_)
  simp [(F.encode_injective d).eq_iff]

end PrimeOrderGroupFamily

private theorem isPPT_wordToTypedHelper {F : PrimeOrderGroupFamily}
    {isElem : F.Desc × List Bool → Bool}
    (hisElem : ComputableInPolyTime isElem (encPair F.encDesc encBits) encBool)
    {decode : ∀ d : F.Desc, List Bool → Option (F.Carrier d)}
    (henc : ∀ d w,
      F.encode d ((decode d w).getD 0) = if isElem (d, w) then w else F.encode d 0)
    {adversary : ℕ → F.Desc × List Bool × List Bool → ProbComp (List Bool)}
    (hA : IsPPTOn F.encWordCDHInput encBits (fun x => adversary x.1 x.2)) :
    PrimeOrderGroupFamily.CDHAdversary.IsPPT (F := F)
      (fun n d u v => (fun guess => (decode d guess).getD 0) <$>
        adversary n (d, F.encode d u, F.encode d v)) := by
  have hprep : ComputableInPolyTime
      (fun x : F.CDHInput =>
        (x.secParam, x.groupParameters, F.encode _ x.leftPublic, F.encode _ x.rightPublic))
      F.encCDHInput F.encWordCDHInput :=
    (ComputableInPolyTime.id' (encIn := F.encCDHInput)).of_enc_eq fun x =>
      (F.encCDHInput_apply x).symm
  have hrun : IsPPTOn F.encCDHInput encBits fun x =>
      adversary x.secParam
        (x.groupParameters, F.encode _ x.leftPublic, F.encode _ x.rightPublic) :=
    hA.preprocess hprep
  have hgrp0 : ComputableInPolyTime (fun x : F.CDHInput => x.groupParameters)
      F.encCDHInput F.encDesc :=
    ((ComputableInPolyTime.fst F.encDesc (encPair encBits encBits)).comp
      ((ComputableInPolyTime.snd encUnary
        (encPair F.encDesc (encPair encBits encBits))).comp hprep)).of_enc_eq fun _ => rfl
  have hgrp : ComputableInPolyTime
      (fun p : F.CDHInput × List Bool => p.1.groupParameters)
      (encPair F.encCDHInput encBits) F.encDesc :=
    hgrp0.comp (by fun_prop)
  have hcond : ComputableInPolyTime
      (fun p : F.CDHInput × List Bool => isElem (p.1.groupParameters, p.2))
      (encPair F.encCDHInput encBits) encBool :=
    hisElem.comp (hgrp.prod (by fun_prop))
  have hthen : ComputableInPolyTime
      (fun p : F.CDHInput × List Bool => p.2)
      (encPair F.encCDHInput encBits) encBits := by
    fun_prop
  have helse : ComputableInPolyTime
      (fun p : F.CDHInput × List Bool => F.encode p.1.groupParameters 0)
      (encPair F.encCDHInput encBits) encBits :=
    PrimeOrderGroupFamily.computableInPolyTime_encode_zero hgrp
  have hmap : IsPPTOn F.encCDHInput encBits fun x =>
      (fun guess => if isElem (x.groupParameters, guess) then guess
        else F.encode x.groupParameters 0) <$>
      adversary x.secParam
        (x.groupParameters, F.encode _ x.leftPublic, F.encode _ x.rightPublic) :=
    IsPPTOn.map_with hrun (hcond.ite hthen helse)
  refine hmap.congr fun x => ?_
  simp only [Functor.map_map, henc]

namespace DecodablePrimeOrderGroupFamily

variable (F : DecodablePrimeOrderGroupFamily)

/-- Turn a word-level CDH adversary into a typed CDH adversary using `F.decode`, falling back to
`0 : F.Carrier d` on invalid words. -/
noncomputable def wordToTypedCDHAdversary
    (adversary : ℕ → F.Desc × List Bool × List Bool → ProbComp (List Bool)) :
    F.toPrimeOrderGroupFamily.CDHAdversary :=
  fun n d u v =>
    (fun guess => (F.decode d guess).getD 0) <$> adversary n (d, F.encode d u, F.encode d v)

/-- `wordToTypedCDHAdversary` preserves uniform strict PPT: encoding the decoded output with
fallback `0` equals echoing valid words `w` verbatim and outputting `F.encode d 0` otherwise. -/
theorem isPPT_wordToTypedCDHAdversary
    {adversary : ℕ → F.Desc × List Bool × List Bool → ProbComp (List Bool)}
    (hA : IsPPTOn F.toPrimeOrderGroupFamily.encWordCDHInput encBits
      (fun x => adversary x.1 x.2)) :
    (F.wordToTypedCDHAdversary adversary).IsPPT :=
  isPPT_wordToTypedHelper (F := F.toPrimeOrderGroupFamily) (isElem := F.isElem)
    F.computableInPolyTime_isElem (decode := F.decode)
    (fun d w => F.encode_decode_getD d w 0) hA

/-- Whenever a word-level adversary outputs `F.encode d ((a * b) • F.generator d)`,
`wordToTypedCDHAdversary` recovers `(a * b) • F.generator d` via `F.decode_encode`. -/
theorem succProbability_cdhWordGame_le_cdhGame (setup : ℕ → PMF F.Desc)
    (adversary : ℕ → F.Desc × List Bool × List Bool → ProbComp (List Bool)) (n : ℕ) :
    Game.succProbability (F.toPrimeOrderGroupFamily.cdhWordGame setup adversary n) ≤
      Game.succProbability
        (F.toPrimeOrderGroupFamily.cdhGame setup (F.wordToTypedCDHAdversary adversary) n) := by
  dsimp only [wordToTypedCDHAdversary, PrimeOrderGroupFamily.cdhGame,
    PrimeOrderGroupFamily.cdhWordGame, Game.withSetup, Cslib.Crypto.cdhExperiment]
  refine Game.succProbability_mono (PMF.bind_apply_mono_on_support _ _ fun d _ => ?_)
  simp only [ProbComp.eval_bind, ProbComp.eval_uniform, ProbComp.eval_pure]
  refine PMF.bind_apply_mono_on_support _ _ fun a _ => ?_
  refine PMF.bind_apply_mono_on_support _ _ fun b _ => ?_
  rw [ProbComp.eval_map, PMF.bind_map]
  refine PMF.bind_apply_mono_on_support _ _ fun guess _ => ?_
  by_cases h : guess = F.encode d ((a * b) • F.generator d)
  · simp [h, F.decode_encode]
  · simp [h]

/-- **Typed CDH is equivalent to word-level CDH** for every `DecodablePrimeOrderGroupFamily`. -/
theorem cdh_iff_encoded (setup : ℕ → PMF F.Desc) :
    F.toPrimeOrderGroupFamily.CDH setup ↔ F.toPrimeOrderGroupFamily.WordCDH setup := by
  refine ⟨fun hCDH adversary hA => ?_, PrimeOrderGroupFamily.WordCDH.cdh⟩
  have htyped := hCDH _ (F.isPPT_wordToTypedCDHAdversary hA)
  exact negligible_of_le htyped fun n =>
    F.succProbability_cdhWordGame_le_cdhGame setup adversary n

/-- **`DDH` implies word-level `WordCDH`** for a `DecodablePrimeOrderGroupFamily` when every
supported group at parameter `n` has order at least `m n > 0` and `1 / m n` is negligible. -/
theorem DDH.wordCDH {F : DecodablePrimeOrderGroupFamily} {setup : ℕ → PMF F.Desc}
    (hDDH : F.toPrimeOrderGroupFamily.DDH setup)
    {m : ℕ → ℕ} (hm0 : ∀ n, 0 < m n) (hm : ∀ n, ∀ d ∈ (setup n).support, m n ≤ F.order d)
    (hinv : Negligible fun n => (1 / m n : ℝ≥0)) :
    F.toPrimeOrderGroupFamily.WordCDH setup :=
  (F.cdh_iff_encoded setup).mp (hDDH.cdh hm0 hm hinv)

end DecodablePrimeOrderGroupFamily

end Cslib.Crypto
