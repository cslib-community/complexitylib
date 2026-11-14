/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.KEM.FujisakiOkamoto.NotBot.Hybrids
import CslibFrontier.Crypto.Game.Hybrid
import CslibFrontier.Crypto.Protocols.KEM.FujisakiOkamoto.NotBot.Challenge
import CslibFrontier.Crypto.Protocols.KEM.FujisakiOkamoto.NotBot.Correctness
import CslibFrontier.Crypto.Protocols.KEM.FujisakiOkamoto.NotBot.Fallback
import CslibFrontier.Crypto.Protocols.KEM.FujisakiOkamoto.NotBot.Lazy
import CslibFrontier.Crypto.Protocols.KEM.FujisakiOkamoto.NotBot.Pushforward

/-!
# ROM IND-CCA security of `FO-notbot`

The domain-separated implicit-rejection transform `FO-notbot = U-notbot ∘ T` of
[HofheinzHoevelmannsKiltz2017] (IACR ePrint 2017/604, full version dated 2 November 2021, §3.2.2,
Fig. 12) is IND-CCA secure in the random oracle model when the underlying explicit-coin PKE is
two-stage IND-CPA secure, `δ`-correct and `γ`-spread, and messages are uniform
(`Scheme.indCcaRomAdvantage_le`). For a randomized adversary each of whose coin values makes at
most `qG` queries to `G` and `qH` queries to `H` (and any number of decapsulation queries),

`Adv^{IND-CCA}(A) ≤ 2 · Adv^{IND-CPA}(B) + (2 qH + 2 (qG + qH)) / |M| + 2 (qG + qH + 1) δ
  + 2 (qG + qH) 2^{-γ}`,

where `B = romCpaReduction A` is one two-stage IND-CPA adversary that draws its own challenge
messages. The paper obtains its bound by composing Theorem 3.2 for `T` (IND-CPA to OW-PCVA, §3.1)
with Theorem 3.4 for `U-notbot` (§3.2.2); this proof composes the corresponding game hops
directly:

1. `advantage_eagerIndCcaGame_eagerFbGame_le` (module `NotBot.Fallback`): replacing the
   implicit-rejection keys `H(true, s, ·)` by an independent table costs `qH / |M|`.
2. `eagerCoupledGame_eq_eagerFbGame` (`NotBot.Pushforward`) and
   `eval_coupledGame_eq_eagerCoupledGame` (`NotBot.Lazy`): re-indexing the random oracles so that
   decapsulation reads a ciphertext table `Hq`, and its lazy realization.
3. `advantage_coupledGame_simGame_le` (`NotBot.Correctness`): dropping the decryption test from
   the simulator costs `(qG + qH + 1) δ`.
4. `advantage_simGame_le` (`NotBot.Challenge`): in the keyless simulator the real and random
   challenge keys are indistinguishable unless `m*` is queried or another message re-encrypts to
   `c*`. Querying `m*` is the one-wayness experiment `simFilterOwExperiment`, which
   `succProbability_simFilterOwExperiment_le` (module `Security`) bounds by the IND-CPA advantage of
   `romCpaReduction` plus `(qG + qH) / |M|`.

Steps 1–3 are applied to both challenge bits, which accounts for the factor `2` on their terms.
The hops are proved for each coin value of the adversary, and
`RandomizedROAdversary.advantage_play_le` averages them over the coins.
In `roIndCcaGame` and `eagerIndCcaGame`, both the real key (via `H`) and the independent ideal
challenge key are drawn from the arbitrary sampler `S.sampleKey : ProbComp K` (distinct from
`S.pke.keyGen`), and the proof holds for any `S.sampleKey`; taking `S.sampleKey` uniform on `K`
recovers the standard KEM IND-CCA key law of [HofheinzHoevelmannsKiltz2017], §2.2, Def. 2.4 /
Fig. 4.

## Main results

* `Cslib.Crypto.Protocols.FujisakiOkamoto.Scheme.advantage_eagerIndCcaGame_simGame_le`: the eager
  IND-CCA game and the keyless simulator game differ by at most `qH / |M| + (qG + qH + 1) δ`.
* `Cslib.Crypto.Protocols.FujisakiOkamoto.Scheme.indCcaRomAdvantage_le`: ROM IND-CCA security of
  `FO-notbot` from two-stage IND-CPA security, `δ`-correctness and `γ`-spreadness, through the one
  reduction `romCpaReduction A`.

## References

* [D. Hofheinz, K. Hövelmanns, E. Kiltz, *A Modular Analysis of the Fujisaki–Okamoto
  Transformation*][HofheinzHoevelmannsKiltz2017] (IACR ePrint 2017/604, full version dated
  2 November 2021).
-/

public section

namespace Cslib.Crypto.Protocols.FujisakiOkamoto

open Probability
open Probability.PMF
open scoped ENNReal NNReal

variable {PK SK M R CT K : Type}

namespace Scheme

variable [DecidableEq M] [DecidableEq CT]

/-- **Hybrid chain for one challenge bit**: under uniform messages, the eager IND-CCA game of
`FO-notbot` and the keyless simulator game differ by at most `qH / |M| + (qG + qH + 1) δ`. -/
theorem advantage_eagerIndCcaGame_simGame_le [Fintype M] [Nonempty M] [Finite R]
    [Fintype CT] [Finite K] (S : Scheme PK SK M R CT K) (A : ROAdversary PK M R CT K)
    {qG qH : ℕ} (hq : ROQueryBounds A qG qH)
    (hmsg : ProbComp.eval S.sampleMsg = PMF.uniformOfFintype M) {δ : ℝ}
    (hδ : S.pke.DeltaCorrect δ) (b : Bool) :
    (Game.advantage (S.eagerIndCcaGame A b) (ProbComp.eval (S.simGame A b)) : ℝ) ≤
      qH / Fintype.card M + ((qG + qH + 1 : ℕ) : ℝ) * δ := by
  have hp : ∀ m, ProbComp.eval S.sampleMsg m ≤ ((Fintype.card M : ℝ≥0)⁻¹ : ℝ≥0) := by
    intro m
    rw [hmsg, PMF.uniformOfFintype_apply, ENNReal.coe_inv (by simp), ENNReal.coe_natCast]
  have h₁ := S.advantage_eagerIndCcaGame_eagerFbGame_le A hq hp b
  have h₂ := S.advantage_coupledGame_simGame_le A hq hδ b
  rw [eval_coupledGame_eq_eagerCoupledGame, eagerCoupledGame_eq_eagerFbGame] at h₂
  calc (Game.advantage (S.eagerIndCcaGame A b) (ProbComp.eval (S.simGame A b)) : ℝ)
      ≤ Game.advantage (S.eagerIndCcaGame A b) (S.eagerFbGame A b) +
          Game.advantage (S.eagerFbGame A b) (ProbComp.eval (S.simGame A b)) := by
        exact_mod_cast Game.advantage_triangle _ _ _
    _ ≤ qH * ((Fintype.card M : ℝ≥0)⁻¹ : ℝ≥0) + ((qG + qH + 1 : ℕ) : ℝ) * δ := add_le_add h₁ h₂
    _ = qH / Fintype.card M + ((qG + qH + 1 : ℕ) : ℝ) * δ := by
        simp [div_eq_mul_inv]

/-- **ROM IND-CCA security of `FO-notbot` from two-stage IND-CPA**
([HofheinzHoevelmannsKiltz2017], Theorems 3.2 and 3.4, composed directly). Let the messages be
uniform, the PKE `δ`-correct and `γ`-spread, and let every coin value of the randomized adversary
`A` make at most `qG` queries to `G` and `qH` queries to `H` (decapsulation queries are unbounded).
Then the single IND-CPA reduction `romCpaReduction A` satisfies
`Adv^{IND-CCA}(A) ≤ 2 · Adv^{IND-CPA}(romCpaReduction A) + (2 qH + 2 (qG + qH)) / |M|
  + 2 (qG + qH + 1) δ + 2 (qG + qH) 2^{-γ}`.
Both advantages are two-world differences, twice HHK17's hidden-bit advantages, so the factor `2`
in front of the IND-CPA term is the same for both normalizations. Both the real key (via `H`) and
the independent ideal challenge key in `roIndCcaGame` are drawn from the arbitrary key sampler
`S.sampleKey : ProbComp K`; taking `S.sampleKey` uniform on `K` recovers the standard
uniform-ideal-key experiment of [HofheinzHoevelmannsKiltz2017], §2.2, Def. 2.4 / Fig. 4. This is a
concrete bound for one fixed scheme; it says nothing about the running time of the reduction. -/
theorem indCcaRomAdvantage_le [Fintype M] [Nonempty M] [Finite R] [Finite CT] [Finite K]
    (S : Scheme PK SK M R CT K) (A : RandomizedROAdversary PK M R CT K) {qG qH : ℕ}
    (hq : A.QueryBounds qG qH) (hmsg : ProbComp.eval S.sampleMsg = PMF.uniformOfFintype M)
    {δ γ : ℝ} (hδ : S.pke.DeltaCorrect δ) (hγ : S.pke.GammaSpread γ) :
    (S.indCcaRomAdvantage A : ℝ) ≤
      2 * (S.pke.cpaAdvantage (S.romCpaReduction A) : ℝ) +
        (2 * qH + 2 * (qG + qH)) / Fintype.card M + 2 * ((qG + qH + 1 : ℕ) : ℝ) * δ +
        2 * ((qG + qH) * (2 : ℝ) ^ (-γ)) := by
  have : Fintype CT := Fintype.ofFinite CT
  have hδ0 : 0 ≤ δ := ENNReal.toReal_nonneg.trans hδ
  set e : ℝ := 2 * (qH / Fintype.card M + ((qG + qH + 1 : ℕ) : ℝ) * δ) +
    2 * (((qG : ℝ) + qH) * (2 : ℝ) ^ (-γ)) with he
  have he0 : 0 ≤ e := by positivity
  have hcoin (ω : A.Coins) :
      (Experiment.advantage (S.roIndCcaGame (A.run ω) false) (S.roIndCcaGame (A.run ω) true) :
        ℝ) ≤ e + 2 * Pr[S.simFilterOwExperiment (fun _ _ _ => true) (A.run ω)] := by
    have hF := S.advantage_eagerIndCcaGame_simGame_le (A.run ω) (hq ω) hmsg hδ false
    have hT := S.advantage_eagerIndCcaGame_simGame_le (A.run ω) (hq ω) hmsg hδ true
    have hsim := S.advantage_simGame_le (A.run ω) (hq ω) hγ
    simp only [Experiment.advantage, eval_roIndCcaGame_eq_eagerIndCcaGame]
    calc _ ≤ _ := Game.advantage_four_le (S.eagerIndCcaGame (A.run ω))
          (fun b => ProbComp.eval (S.simGame (A.run ω) b)) hF hsim hT
      _ = _ := by rw [he]; ring
  have hmix := A.advantage_play_le S.roIndCcaGame (S.simFilterOwExperiment fun _ _ _ => true)
    he0 hcoin
  have how := S.succProbability_simFilterOwExperiment_le (fun _ _ _ => true) A hq hmsg
  have hcard : (0 : ℝ) < Fintype.card M := by exact_mod_cast Fintype.card_pos
  calc (S.indCcaRomAdvantage A : ℝ)
      ≤ e + 2 * ((S.pke.cpaAdvantage (S.romCpaReduction A) : ℝ) +
          ((qG : ℝ) + qH) / Fintype.card M) := by
        rw [indCcaRomAdvantage, romCpaReduction]; linarith
    _ = _ := by rw [he]; field_simp; ring

end Scheme

end Cslib.Crypto.Protocols.FujisakiOkamoto
