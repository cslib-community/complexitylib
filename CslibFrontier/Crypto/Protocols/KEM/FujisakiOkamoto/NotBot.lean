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
import CslibFrontier.Crypto.Protocols.KEM.FujisakiOkamoto.NotBot.Fallback
import CslibFrontier.Crypto.Protocols.KEM.FujisakiOkamoto.NotBot.Lazy
import CslibFrontier.Crypto.Protocols.KEM.FujisakiOkamoto.NotBot.Pushforward

/-!
# Concrete ROM IND-CCA advantage bound for `FO-notbot`

`Scheme.indCcaRomAdvantage_le` is the concrete per-instance ROM IND-CCA advantage bound for the
domain-separated implicit-rejection transform `FO-notbot = U-notbot ∘ T` of
[HofheinzHoevelmannsKiltz2017] (IACR ePrint 2017/604, full version dated 2 November 2021, §3.2.2,
Fig. 12), after Theorems 3.2 and 3.4 of that paper. It holds for one fixed finite scheme, with no
security parameter and no running-time bound on the reduction `romCpaReduction A`; it is the step
that the word-level asymptotic theorem for the `FO-notbot` family, `WordPKE.INDCPA.romINDCCA` in
`CslibFrontier.Crypto.Protocols.KEM.FujisakiOkamoto.WordSecurity`, consumes. For uniform messages,
a `δ`-correct explicit-coin PKE and a randomized adversary each of whose coin values makes at most
`qG` queries to `G` and `qH` queries to `H` (and any number of decapsulation queries),

`Adv^{IND-CCA}(A) ≤ 2 · Adv^{IND-CPA}(B) + (2 qH + 2 (qG + qH)) / |M| + 2 (qG + qH + 1) δ`,

where `B = romCpaReduction A` is one two-stage IND-CPA adversary that draws its own challenge
messages. As in the source, no `γ`-spreadness is needed (§1.1.2 table and the text below it, p. 6;
remark after the proof of Theorem 3.2, p. 13; `KEM-notbot` row of the §3.3 table, p. 22). The paper
obtains its bound by composing Theorem 3.2 for `T` (IND-CPA to OW-PCVA, §3.1, used in its OW-PCA
form without spreadness from the remark on p. 13) with Theorem 3.4 for `U-notbot` (§3.2.2); this
proof composes the corresponding game hops directly:

1. `advantage_eagerIndCcaGame_eagerFbGame_le` (module `NotBot.Fallback`): replacing the
   implicit-rejection keys `H(true, s, ·)` by an independent table costs `qH / |M|` (game G1 of the
   proof of Theorem 3.4).
2. `eagerCoupledGame_eq_eagerFbGame` (`NotBot.Pushforward`) and
   `eval_coupledGame_eq_eagerCoupledGame` (`NotBot.Lazy`): re-indexing the random oracles so that
   decapsulation reads a ciphertext table `Hq`, and its lazy realization `coupledGame`, whose
   key-derivation oracle reads `Hq(c)` for `H(false, m, c)` exactly when `c = Enc(pk, m; G(m))` and
   `Dec(sk, c) = some m` (game G2 of the proof of Theorem 3.4).
3. `advantage_coupledGame_le` (`NotBot.Challenge`): the real and random challenge keys are
   indistinguishable unless `G(m*)` is queried or the challenge itself fails to decrypt (game G3 of
   the proof of Theorem 3.4). With the decryption test, no other message reaches the challenge key,
   so no spreadness is needed. Removing the decryption test inside the one-wayness run costs
   `(qG + qH) δ` (games G1–G2 of the proof of Theorem 3.1), which leaves the one-wayness experiment
   `simFilterOwExperiment` of the keyless simulator; `succProbability_simFilterOwExperiment_le`
   (module `Security`) bounds it by the IND-CPA advantage of `romCpaReduction` plus
   `(qG + qH) / |M|`.

Step 1 is applied to both challenge bits, which accounts for the factor `2` on its term.
The hops are proved for each coin value of the adversary, and
`RandomizedROAdversary.advantage_play_le` averages them over the coins.
In `roIndCcaGame` and `eagerIndCcaGame`, both the real key (via `H`) and the independent ideal
challenge key are drawn from the arbitrary sampler `S.sampleKey : ProbComp K` (distinct from
`S.pke.keyGen`), and the proof holds for any `S.sampleKey`; taking `S.sampleKey` uniform on `K`
recovers the standard KEM IND-CCA key law of [HofheinzHoevelmannsKiltz2017], §2.2, Def. 2.4 /
Fig. 4.

## Main results

* `Cslib.Crypto.Protocols.FujisakiOkamoto.Scheme.advantage_eagerIndCcaGame_coupledGame_le`: the
  eager IND-CCA game and the lazy coupled game differ by at most `qH / |M|`.
* `Cslib.Crypto.Protocols.FujisakiOkamoto.Scheme.indCcaRomAdvantage_le`: the concrete
  per-instance ROM IND-CCA advantage bound for `FO-notbot` (after HHK17 Theorems 3.2 and 3.4), in
  terms of the two-stage IND-CPA advantage of the one reduction `romCpaReduction A` and
  `δ`-correctness, for one fixed finite scheme and without running-time bounds on the reduction.

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
`FO-notbot` and the lazy coupled game differ by at most `qH / |M|`. -/
theorem advantage_eagerIndCcaGame_coupledGame_le [Fintype M] [Nonempty M] [Finite R]
    [Fintype CT] [Finite K] (S : Scheme PK SK M R CT K) (A : ROAdversary PK M R CT K)
    {qG qH : ℕ} (hq : ROQueryBounds A qG qH)
    (hmsg : ProbComp.eval S.sampleMsg = PMF.uniformOfFintype M) (b : Bool) :
    (Game.advantage (S.eagerIndCcaGame A b) (ProbComp.eval (S.coupledGame A b)) : ℝ) ≤
      qH / Fintype.card M := by
  have hp : ∀ m, ProbComp.eval S.sampleMsg m ≤ ((Fintype.card M : ℝ≥0)⁻¹ : ℝ≥0) := by
    intro m
    rw [hmsg, PMF.uniformOfFintype_apply, ENNReal.coe_inv (by simp), ENNReal.coe_natCast]
  rw [eval_coupledGame_eq_eagerCoupledGame, eagerCoupledGame_eq_eagerFbGame]
  refine (S.advantage_eagerIndCcaGame_eagerFbGame_le A hq hp b).trans (le_of_eq ?_)
  simp [div_eq_mul_inv]

/-- **Concrete ROM IND-CCA advantage bound for `FO-notbot`**, the per-instance step after
[HofheinzHoevelmannsKiltz2017], Theorems 3.2 and 3.4 (composed directly), for one fixed finite
scheme and without running-time bounds on `romCpaReduction A`; the word-level asymptotic theorem
for the `FO-notbot` family consumes it. Let the messages be uniform and the PKE `δ`-correct, and
let every coin value of the randomized adversary `A` make at most `qG` queries to `G` and `qH`
queries to `H` (decapsulation queries are unbounded). Then the single IND-CPA reduction
`romCpaReduction A` satisfies
`Adv^{IND-CCA}(A) ≤ 2 · Adv^{IND-CPA}(romCpaReduction A) + (2 qH + 2 (qG + qH)) / |M|
  + 2 (qG + qH + 1) δ`.
As in the source, the PKE need not be `γ`-spread (§1.1.2 table, p. 6; remark after the proof of
Theorem 3.2, p. 13). Both advantages are two-world differences, twice HHK17's hidden-bit
advantages, so the factor `2` in front of the IND-CPA term is the same for both normalizations; in
the hidden-bit normalization the bound reads
`2 · Adv^{IND-CPA} + (qG + 2 qH) / |M| + (qG + qH + 1) δ`, which is within the `KEM-notbot` row
`qRO · δ + 3 qRO / |M| + 3 · Adv^{IND-CPA}` of the §3.3 table (p. 22) for `qRO = qG + qH + 1`.
Both the real key (via `H`) and the independent ideal challenge key in `roIndCcaGame` are drawn
from the arbitrary key sampler `S.sampleKey : ProbComp K`; taking `S.sampleKey` uniform on `K`
recovers the standard uniform-ideal-key experiment of [HofheinzHoevelmannsKiltz2017], §2.2,
Def. 2.4 / Fig. 4. -/
theorem indCcaRomAdvantage_le [Fintype M] [Nonempty M] [Finite R] [Finite CT] [Finite K]
    (S : Scheme PK SK M R CT K) (A : RandomizedROAdversary PK M R CT K) {qG qH : ℕ}
    (hq : A.QueryBounds qG qH) (hmsg : ProbComp.eval S.sampleMsg = PMF.uniformOfFintype M)
    {δ : ℝ} (hδ : S.pke.DeltaCorrect δ) :
    (S.indCcaRomAdvantage A : ℝ) ≤
      2 * (S.pke.cpaAdvantage (S.romCpaReduction A) : ℝ) +
        (2 * qH + 2 * (qG + qH)) / Fintype.card M + 2 * ((qG + qH + 1 : ℕ) : ℝ) * δ := by
  have : Fintype CT := Fintype.ofFinite CT
  have hδ0 : 0 ≤ δ := ENNReal.toReal_nonneg.trans hδ
  set e : ℝ := 2 * (qH / Fintype.card M) + 2 * ((qG + qH + 1 : ℕ) : ℝ) * δ with he
  have he0 : 0 ≤ e := by positivity
  have hcoin (ω : A.Coins) :
      (Experiment.advantage (S.roIndCcaGame (A.run ω) false) (S.roIndCcaGame (A.run ω) true) :
        ℝ) ≤ e + 2 * Pr[S.simFilterOwExperiment (fun _ _ _ => true) (A.run ω)] := by
    have hF := S.advantage_eagerIndCcaGame_coupledGame_le (A.run ω) (hq ω) hmsg false
    have hT := S.advantage_eagerIndCcaGame_coupledGame_le (A.run ω) (hq ω) hmsg true
    have hcpl := S.advantage_coupledGame_le (A.run ω) (hq ω) hδ
    simp only [Experiment.advantage, eval_roIndCcaGame_eq_eagerIndCcaGame]
    calc _ ≤ _ := Game.advantage_four_le (S.eagerIndCcaGame (A.run ω))
          (fun b => ProbComp.eval (S.coupledGame (A.run ω) b)) hF hcpl hT
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
