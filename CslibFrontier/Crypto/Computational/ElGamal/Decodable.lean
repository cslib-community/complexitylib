/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.DiscreteLog.Decodable
public import CslibFrontier.Crypto.Computational.ElGamal.ProbComp
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Probability.PMF

/-!
# Decodable group-element ElGamal games and `INDCPAOn` without `valid` stand-ins

In `CslibFrontier/Crypto/Computational/ElGamal.lean`, `elGamalGroupCPAGameOn` and
`elGamalMsgCPAGameOn` parameterize the adversary's challenge check by a predicate
`valid : ℕ → List Bool → Msg → Msg → Bool` paired with `AdmitsGroupElements`, because a general
`PrimeOrderGroupFamily` has no efficient group-element membership test or decoder. Over a
`DecodablePrimeOrderGroupFamily`:

* `elGamalGroupCPAGame` checks `F.isElem (d, m₀) && F.isElem (d, m₁)` directly using the
  sampled group description `d`, removing the external `valid`, `hvalid`, and
  `AdmitsGroupElements` parameters (`DDH.negligible_elGamalGroupCPAGame`).
* For a polynomial-time group description family `d : ℕ → F.Desc`, `elGamalGroupValid F d`
  supplies the native `Encryption.INDCPAOn` admissibility predicate using `F.isElem (d n, ·)`,
  yielding `DDH.indcpaOn_elGamalGroupEncryptProb` without external validity premises.

The more general parameterized forms `elGamalMsgCPAGameOn` / `elGamalGroupCPAGameOn`,
`GeneralCipher.hashedElGamalCipherCPAGameOn`, and `DDH.indcpaOn_elGamalEncryptProb` remain for
arbitrary typed-message encoders (`encodeBit`), additional client-side challenge constraints such as
equal bit-length (`equalLengthWords`), and generic `PrimeOrderGroupFamily` statements where
`F.encDesc` need not have a decoder to recover `d` from `pk : List Bool`.

## Main definitions

* `Cslib.Crypto.DecodablePrimeOrderGroupFamily.elGamalGroupCPAGame`: group-element ElGamal CPA
  game checking `F.isElem (d, ·)` directly.
* `Cslib.Crypto.DecodablePrimeOrderGroupFamily.elGamalGroupToDDHDistinguisher`: DDH reduction
  for `elGamalGroupCPAGame`.
* `Cslib.Crypto.DecodablePrimeOrderGroupFamily.elGamalGroupValid`: native challenge-pair
  admissibility predicate `F.isElem (d n, m₀) && F.isElem (d n, m₁)`.

## Main results

* `Cslib.Crypto.DecodablePrimeOrderGroupFamily.DDH.negligible_elGamalGroupCPAGame`: DDH implies
  group-element ElGamal CPA security without an external `valid` predicate.
* `Cslib.Crypto.DecodablePrimeOrderGroupFamily.DDH.indcpaOn_elGamalGroupEncryptProb`: native
  `Encryption.INDCPAOn` security of `(F.elGamalKeyGenProb d, F.elGamalEncryptProb (fun _ m => m)
  d)` under DDH for `d : ℕ → F.Desc`.
-/

public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM Encryption

private theorem computableInPolyTime_elemGuard {F : PrimeOrderGroupFamily}
    {isElem : F.Desc × List Bool → Bool}
    (hisElem : ComputableInPolyTime isElem (encPair F.encDesc encBits) encBool) :
    ComputableInPolyTime
      (fun p : ℕ × F.Desc × List Bool × List Bool × List Bool =>
        isElem (p.2.1, p.2.2.2.1) && isElem (p.2.1, p.2.2.2.2))
      (F.encElGamalMsgGuardInput encBits) encBool := by
  have hp := ComputableInPolyTime.id' (encIn := F.encElGamalMsgGuardInput encBits)
  have hd := hp.snd'.fst'
  have hm₀ := hp.snd'.snd'.snd'.fst'
  have hm₁ := hp.snd'.snd'.snd'.snd'
  exact ComputableInPolyTime.bool_and.comp
    ((hisElem.comp (hd.prod hm₀)).prod (hisElem.comp (hd.prod hm₁)))

private theorem computableInPolyTime_groupValidHelper {F : PrimeOrderGroupFamily}
    {isElem : F.Desc × List Bool → Bool} {d : ℕ → F.Desc}
    (hisElem : ComputableInPolyTime isElem (encPair F.encDesc encBits) encBool)
    (hd : ComputableInPolyTime d encUnary F.encDesc) :
    ComputableInPolyTime
      (fun ⟨n, _pk, m₀, m₁⟩ => isElem (d n, m₀) && isElem (d n, m₁))
      (encChallengePairInput encBits) encBool := by
  have hp := ComputableInPolyTime.id' (encIn := encChallengePairInput encBits)
  have hdn := hd.comp hp.fst'
  have hm₀ := hp.snd'.snd'.fst'
  have hm₁ := hp.snd'.snd'.snd'
  exact ComputableInPolyTime.bool_and.comp
    ((hisElem.comp (hdn.prod hm₀)).prod (hisElem.comp (hdn.prod hm₁)))

namespace DecodablePrimeOrderGroupFamily

variable (F : DecodablePrimeOrderGroupFamily)

/-- Group-element ElGamal CPA experiment ([BonehShoup2023], Exercise 11.5(a), p. 459) over a
`DecodablePrimeOrderGroupFamily`, validating challenge messages directly with
`F.isElem (d, m₀) && F.isElem (d, m₁)` without an external `valid` predicate. -/
noncomputable abbrev elGamalGroupCPAGame (setup : ℕ → PMF F.Desc)
    (adversary : Encryption.WordAdversary) (bit : Bool) (n : ℕ) : Game :=
  F.toPrimeOrderGroupFamily.elGamalMsgCPAGameWith
    (fun _ d _ m₀ m₁ => F.isElem (d, m₀) && F.isElem (d, m₁))
    (fun _ m => m) setup adversary bit n

/-- DDH distinguisher constructed from an adversary in `elGamalGroupCPAGame`. -/
abbrev elGamalGroupToDDHDistinguisher
    (adversary : Encryption.WordAdversary) (bit : Bool) :
    F.toPrimeOrderGroupFamily.DDHDistinguisher :=
  F.toPrimeOrderGroupFamily.elGamalMsgToDDHDistinguisherWith
    (fun _ d _ m₀ m₁ => F.isElem (d, m₀) && F.isElem (d, m₁))
    (fun _ m => m) adversary bit

private theorem elemGuard_sound (d : F.Desc) (m₀ m₁ : List Bool)
    (h : (F.isElem (d, m₀) && F.isElem (d, m₁)) = true) :
    (∃ x₀ : F.Carrier d, m₀ = F.encode d x₀) ∧
      (∃ x₁ : F.Carrier d, m₁ = F.encode d x₁) := by
  simp only [Bool.and_eq_true] at h
  obtain ⟨x₀, _, hx₀⟩ := F.exists_decode_eq_some_of_isElem h.1
  obtain ⟨x₁, _, hx₁⟩ := F.exists_decode_eq_some_of_isElem h.2
  exact ⟨⟨x₀, hx₀.symm⟩, ⟨x₁, hx₁.symm⟩⟩

/-- **Quantitative reduction from decodable group-element ElGamal CPA to DDH**. -/
theorem advantage_elGamalGroupCPAGame_le (setup : ℕ → PMF F.Desc)
    (adversary : Encryption.WordAdversary) (n : ℕ) :
    Game.advantage (F.elGamalGroupCPAGame setup adversary false n)
      (F.elGamalGroupCPAGame setup adversary true n) ≤
      Game.advantage
        (F.ddhRealGame setup (F.elGamalGroupToDDHDistinguisher adversary false) n)
        (F.ddhRandomGame setup (F.elGamalGroupToDDHDistinguisher adversary false) n) +
      Game.advantage
        (F.ddhRealGame setup (F.elGamalGroupToDDHDistinguisher adversary true) n)
        (F.ddhRandomGame setup (F.elGamalGroupToDDHDistinguisher adversary true) n) :=
  F.toPrimeOrderGroupFamily.advantage_elGamalMsgCPAGameWith_le _ (fun _ m => m) setup adversary n
    fun d _ _ m₀ m₁ hv => F.elemGuard_sound d m₀ m₁ hv

/-- **Group-element ElGamal encryption is IND-CPA secure under DDH** for every
`DecodablePrimeOrderGroupFamily`, with challenge membership enforced directly by `F.isElem`. -/
theorem DDH.negligible_elGamalGroupCPAGame {F : DecodablePrimeOrderGroupFamily}
    {setup : ℕ → PMF F.Desc} (hDDH : F.toPrimeOrderGroupFamily.DDH setup)
    {adversary : Encryption.WordAdversary} (hA : adversary.IsPPT) :
    Negligible fun n =>
      Game.advantage (F.elGamalGroupCPAGame setup adversary false n)
        (F.elGamalGroupCPAGame setup adversary true n) :=
  hDDH.negligible_elGamalMsgCPAGameWith
    (computableInPolyTime_elemGuard F.computableInPolyTime_isElem)
    (fun _ d _ _ m₀ m₁ hv => F.elemGuard_sound d m₀ m₁ hv)
    (.snd F.encDesc encBits) hA

/-- Challenge-pair admissibility predicate for native `Encryption.INDCPAOn` of multiplicative
ElGamal over a parameterized group description family `d : ℕ → F.Desc`, testing whether both
candidate words represent group elements in `F.Carrier (d n)`. -/
def elGamalGroupValid (d : ℕ → F.Desc) (n : ℕ) (_pk m₀ m₁ : List Bool) : Bool :=
  F.isElem (d n, m₀) && F.isElem (d n, m₁)

/-- `elGamalGroupValid d` is computable in polynomial time whenever `d` is. -/
theorem computableInPolyTime_elGamalGroupValid {d : ℕ → F.Desc}
    (hd : ComputableInPolyTime d encUnary F.encDesc) :
    ComputableInPolyTime
      (fun ⟨n, pk, m₀, m₁⟩ => F.elGamalGroupValid d n pk m₀ m₁)
      (encChallengePairInput encBits) encBool :=
  computableInPolyTime_groupValidHelper F.computableInPolyTime_isElem hd

/-- On the point-mass setup `fun n => PMF.pure (d n)`, `elGamalGroupValid d` admits only group
elements under the identity word message encoding. -/
theorem admitsGroupElementsOn_elGamalGroupValid (d : ℕ → F.Desc) :
    F.toPrimeOrderGroupFamily.AdmitsGroupElementsOn (fun n => PMF.pure (d n))
      (fun _ m => m) (F.elGamalGroupValid d) := by
  intro n d' hd' _ m₀ m₁ hv
  simp only [PMF.support_pure, Set.mem_singleton_iff] at hd'
  subst hd'
  exact F.elemGuard_sound (d n) m₀ m₁ hv

/-- **Group-element multiplicative ElGamal satisfies `Encryption.INDCPAOn` under DDH** for any
`DecodablePrimeOrderGroupFamily` and polynomial-time group description family `d : ℕ → F.Desc`,
with admissibility defined directly by `F.elGamalGroupValid d` (no external `valid`, `hvalid`, or
`AdmitsGroupElements` arguments). -/
theorem DDH.indcpaOn_elGamalGroupEncryptProb {F : DecodablePrimeOrderGroupFamily}
    {d : ℕ → F.Desc} (hDDH : F.toPrimeOrderGroupFamily.DDH (fun n => PMF.pure (d n)))
    (hd : ComputableInPolyTime d encUnary F.encDesc) :
    INDCPAOn (F.elGamalGroupValid d) encBits (F.elGamalKeyGenProb d)
      (F.elGamalEncryptProb (fun _ m => m) d) :=
  hDDH.indcpaOn_elGamalEncryptProb_on
    (F.computableInPolyTime_elGamalGroupValid hd)
    (F.admitsGroupElementsOn_elGamalGroupValid d)
    (.snd F.encDesc encBits)

end DecodablePrimeOrderGroupFamily

end Cslib.Crypto
