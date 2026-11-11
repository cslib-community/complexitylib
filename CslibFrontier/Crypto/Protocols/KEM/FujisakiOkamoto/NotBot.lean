/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.KEM.FujisakiOkamoto.NotBot.Hybrids
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
IND-CPA secure, `δ`-correct and `γ`-spread, and messages are uniform
(`Scheme.indCcaRomAdvantage_le`). For an adversary making at most `qG` queries to `G` and `qH`
queries to `H` (and any number of decapsulation queries),

`Adv^{IND-CCA}(A) ≤ 2 · Adv^{IND-CPA}(B) + (2 qH + 2 (qG + qH)) / |M| + 2 (qG + qH + 1) δ
  + 2 (qG + qH) 2^{-γ}`,

where `B = romCpaReduction A m₀ m₁` for some distinct messages `m₀ ≠ m₁`. The paper obtains its
bound by composing the §3.1 theorem for `T` (IND-CPA to OW-PCA) with the §3.2.2 theorem for
`U-notbot`; this proof composes the corresponding game hops directly:

1. `advantage_eagerIndCcaGame_eagerFbGame_le` (module `NotBot.Fallback`): replacing the
   implicit-rejection keys `H(true, s, ·)` by an independent table costs `qH / |M|`.
2. `eagerCoupledGame_eq_eagerFbGame` (`NotBot.Pushforward`) and
   `eval_coupledGame_eq_eagerCoupledGame` (`NotBot.Lazy`): re-indexing the random oracles so that
   decapsulation reads a ciphertext table `Hq`, and its lazy realization.
3. `advantage_coupledGame_simGame_le` (`NotBot.Correctness`): dropping the decryption test from
   the simulator costs `(qG + qH + 1) δ`.
4. `advantage_simGame_le` (`NotBot.Challenge`): in the keyless simulator the real and random
   challenge keys are indistinguishable unless `m*` is queried or another message re-encrypts to
   `c*`, which reduces to IND-CPA via `romCpaReduction`.

Steps 1–3 are applied to both challenge bits, which accounts for the factor `2` on their terms.
In `roIndCcaGame` and `eagerIndCcaGame`, both the real key (via `H`) and the independent ideal
challenge key are drawn from the arbitrary sampler `S.sampleKey : ProbComp K` (distinct from
`S.pke.keyGen`), and the proof holds for any `S.sampleKey`; taking `S.sampleKey` uniform on `K`
recovers the standard KEM IND-CCA key law of [HofheinzHoevelmannsKiltz2017], §2.2, Def. 2.4 /
Fig. 4.

## Main results

* `Cslib.Crypto.Protocols.FujisakiOkamoto.Scheme.advantage_eagerIndCcaGame_simGame_le`: the eager
  IND-CCA game and the keyless simulator game differ by at most `qH / |M| + (qG + qH + 1) δ`.
* `Cslib.Crypto.Protocols.FujisakiOkamoto.Scheme.indCcaRomAdvantage_le`: ROM IND-CCA security of
  `FO-notbot` from IND-CPA security, `δ`-correctness and `γ`-spreadness.

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

/-- **ROM IND-CCA security of `FO-notbot`** ([HofheinzHoevelmannsKiltz2017], §3.1 and §3.2.2,
composed directly): for uniform messages, a `δ`-correct and `γ`-spread PKE, and an adversary making
at most `qG` queries to `G` and `qH` queries to `H`, there are distinct messages `m₀ ≠ m₁` with
`Adv^{IND-CCA}(A) ≤ 2 · Adv^{IND-CPA}_{m₀, m₁}(romCpaReduction A m₀ m₁)
  + (2 qH + 2 (qG + qH)) / |M| + 2 (qG + qH + 1) δ + 2 (qG + qH) 2^{-γ}`.
Decapsulation queries are unbounded. Both the real key (via `H`) and the independent ideal
challenge key in `roIndCcaGame` are drawn from the arbitrary key sampler `S.sampleKey : ProbComp K`;
taking `S.sampleKey` uniform on `K` recovers the standard uniform-ideal-key experiment of
[HofheinzHoevelmannsKiltz2017], §2.2, Def. 2.4 / Fig. 4. -/
theorem indCcaRomAdvantage_le [Fintype M] [Nonempty M] [Finite R] [Finite CT] [Finite K]
    (S : Scheme PK SK M R CT K) (A : ROAdversary PK M R CT K) {qG qH : ℕ}
    (hq : ROQueryBounds A qG qH) (hM : 2 ≤ Fintype.card M)
    (hmsg : ProbComp.eval S.sampleMsg = PMF.uniformOfFintype M)
    {δ γ : ℝ} (hδ : S.pke.DeltaCorrect δ) (hγ : S.pke.GammaSpread γ) :
    ∃ m₀ m₁ : M, m₀ ≠ m₁ ∧
      (S.indCcaRomAdvantage A : ℝ) ≤
        2 * (S.pke.indCpaAdvantage m₀ m₁ (S.romCpaReduction A m₀ m₁) : ℝ) +
          (2 * qH + 2 * (qG + qH)) / Fintype.card M + 2 * ((qG + qH + 1 : ℕ) : ℝ) * δ +
          2 * ((qG + qH) * (2 : ℝ) ^ (-γ)) := by
  have : Fintype CT := Fintype.ofFinite CT
  obtain ⟨m₀, m₁, hne, hsim⟩ := S.advantage_simGame_le A hq hM hmsg hγ
  refine ⟨m₀, m₁, hne, ?_⟩
  have hF := S.advantage_eagerIndCcaGame_simGame_le A hq hmsg hδ false
  have hT := S.advantage_eagerIndCcaGame_simGame_le A hq hmsg hδ true
  rw [indCcaRomAdvantage_eq_eager]
  have htri : (Game.advantage (S.eagerIndCcaGame A false) (S.eagerIndCcaGame A true) : ℝ) ≤
      Game.advantage (S.eagerIndCcaGame A false) (ProbComp.eval (S.simGame A false)) +
        Game.advantage (ProbComp.eval (S.simGame A false)) (ProbComp.eval (S.simGame A true)) +
        Game.advantage (S.eagerIndCcaGame A true) (ProbComp.eval (S.simGame A true)) := by
    rw [Game.advantage_comm (S.eagerIndCcaGame A true)]
    have h := (Game.advantage_triangle (S.eagerIndCcaGame A false)
      (ProbComp.eval (S.simGame A false)) (S.eagerIndCcaGame A true)).trans
      (add_le_add le_rfl (Game.advantage_triangle (ProbComp.eval (S.simGame A false))
        (ProbComp.eval (S.simGame A true)) (S.eagerIndCcaGame A true)))
    rw [← add_assoc] at h
    exact_mod_cast h
  have hcard : (0 : ℝ) < Fintype.card M := by exact_mod_cast Fintype.card_pos
  calc _ ≤ _ := htri
    _ ≤ _ := add_le_add (add_le_add hF hsim) hT
    _ = _ := by field_simp; ring

end Scheme

end Cslib.Crypto.Protocols.FujisakiOkamoto
