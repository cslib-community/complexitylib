/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.KEM.FujisakiOkamoto.WordBridge
import CslibFrontier.Crypto.Protocols.KEM.FujisakiOkamoto.NotBot
import CslibFrontier.Crypto.Negligible.Dyadic

/-!
# ROM IND-CCA security of the word-level `FO-notbot` family from IND-CPA

This module proves that the word-level `FO-notbot` KEM of
`CslibFrontier.Crypto.Protocols.KEM.FujisakiOkamoto.WordGame` is IND-CCA secure in the random
oracle model when the underlying word-level PKE family is IND-CPA secure
(`WordPKE.INDCPA.romINDCCA`). This is an asymptotic form of the `FO-notbot = U-notbot ∘ T` result
of [HofheinzHoevelmannsKiltz2017] (IACR ePrint 2017/604, full version dated 2 November 2021),
which composes Theorem 3.2 (§3.1, IND-CPA to OW-PCVA, used in its OW-PCA form from the remark on
p. 13) and Theorem 3.4 (§3.2.2). As in the source, the PKE need not be `γ`-spread (§1.1.2 table
and the text below it, p. 6; remark after the proof of Theorem 3.2, p. 13; `KEM-notbot` row of the
§3.3 table, p. 22).

**Assumptions.** `P.INDCPA` is the hardness assumption: IND-CPA security of the PKE family
against uniform strict PPT adversaries, with challenge messages in its message space. The other
premises are properties of the PKE family and the key length: efficiency (`WordPKE.IsEfficient`
and a polynomial-time `keyLen`), ciphertexts in the ciphertext space (`WordPKE.CiphertextFits`),
`δ`-correctness at every parameter with `δ` negligible, and a message space of size
`2 ^ msgLen n` whose inverse is negligible. Nothing is assumed about the reduction.

**Proof.** For an adversary `A` with `IsOraclePPT encBool A`, the typed bridge
`WordPKE.IsEfficient.exists_typedAdversary` gives at each parameter a typed adversary with a
polynomial bound `q` on its `G` and `H` queries, whose typed game is the word game and whose typed
reduction has the IND-CPA advantage of `romCpaReductionWord A`. The concrete bound
`Scheme.indCcaRomAdvantage_le` then bounds the IND-CCA advantage at `n` by
`2 · Adv^{IND-CPA}(romCpaReductionWord A) n + 6 q / 2 ^ msgLen n + 2 (2 q + 1) δ n`. The
reduction is uniform strict PPT by `WordPKE.IsEfficient.isPPT_romCpaReductionWord`, so the
IND-CPA assumption makes its advantage negligible, and so is the sum.

**Scope.** Only the implicit-rejection transform `FO-notbot` is covered. `FO^⊥` would need a
polynomial-time certificate for its decapsulation filter `simBotCheck` and a word game for
`decapsBot`. The game is the word game `romIndCcaGameWord`, whose deviations from the source are
documented there.

## Main results

* `Cslib.Crypto.Protocols.FujisakiOkamoto.WordPKE.INDCPA.romINDCCA`: IND-CPA security of an
  efficient, `δ`-correct word-level PKE family implies ROM IND-CCA security of its `FO-notbot`
  KEM.

## References

* [D. Hofheinz, K. Hövelmanns, E. Kiltz, *A Modular Analysis of the Fujisaki–Okamoto
  Transformation*][HofheinzHoevelmannsKiltz2017] (IACR ePrint 2017/604, full version dated
  2 November 2021), Theorems 3.2 and 3.4; the requirements table of §1.1.2 (p. 6), the remark
  after the proof of Theorem 3.2 (p. 13) and the bounds table of §3.3 (p. 22).
-/

public section

namespace Cslib.Crypto.Protocols.FujisakiOkamoto

open Probability Turing.MultiTapeTM
open scoped NNReal

namespace WordPKE

/-- **ROM IND-CCA security of the word-level `FO-notbot` family from IND-CPA**
([HofheinzHoevelmannsKiltz2017], ePrint 2017/604 (2 Nov 2021), Theorems 3.2 and 3.4, composed).
Let `P` be an efficient word-level PKE family whose ciphertexts lie in its ciphertext space, which
is `δ`-correct with `δ` negligible and has messages of length `msgLen n` with `2 ^ (-msgLen n)`
negligible, and let `keyLen` be polynomial-time. If `P` is IND-CPA secure, its `FO-notbot` KEM
with keys of length `keyLen n` is IND-CCA secure in the random oracle model against uniform strict
oracle PPT adversaries, with any number of decapsulation queries. The proof applies the IND-CPA
assumption to the explicit reduction `romCpaReductionWord A`, certified by
`IsEfficient.isPPT_romCpaReductionWord`. As in the source, the PKE need not be `γ`-spread (§1.1.2
table, p. 6; remark after the proof of Theorem 3.2, p. 13; `KEM-notbot` row of the §3.3 table,
p. 22). -/
theorem INDCPA.romINDCCA {P : WordPKE} {keyLen : ℕ → ℕ} (hcpa : P.INDCPA)
    (hP : P.IsEfficient) (hkeyLen : ComputableInPolyTime keyLen encUnary encUnary)
    (hfit : P.CiphertextFits) {δ : ℕ → ℝ≥0} (hδ : P.DeltaCorrect δ) (hδneg : Negligible δ)
    (hmsg : Negligible fun n => ((2 : ℝ≥0) ^ P.msgLen n)⁻¹) :
    P.ROMINDCCA keyLen := by
  intro A hA
  obtain ⟨B, q, hq, hqueries, hbridge⟩ := hP.exists_typedAdversary hkeyLen hA
  let cpa : ℕ → ℝ≥0 := Encryption.advantage
    (Encryption.gameOn P.IsMessagePair P.keyGen P.encrypt (P.romCpaReductionWord keyLen A))
  have hcpa' : Negligible cpa :=
    hcpa (P.romCpaReductionWord keyLen A) (hP.isPPT_romCpaReductionWord hkeyLen hA)
  have hbound (n : ℕ) : Game.advantage (ProbComp.eval (P.romIndCcaGameWord keyLen A false n))
      (ProbComp.eval (P.romIndCcaGameWord keyLen A true n)) ≤
      2 * cpa n + ((6 * q n : ℕ) : ℝ≥0) * ((2 : ℝ≥0) ^ P.msgLen n)⁻¹ +
        ((2 * (2 * q n + 1) : ℕ) : ℝ≥0) * δ n := by
    obtain ⟨hgame, hadv⟩ := hbridge hfit n
    have hle := (P.finiteScheme keyLen n).indCcaRomAdvantage_le (B n) (hqueries n)
      (by simp [ProbComp.eval_uniform]) (hδ n)
    have hword : Game.advantage (ProbComp.eval (P.romIndCcaGameWord keyLen A false n))
        (ProbComp.eval (P.romIndCcaGameWord keyLen A true n)) =
        (P.finiteScheme keyLen n).indCcaRomAdvantage (B n) := by
      simp only [Scheme.indCcaRomAdvantage, Experiment.advantage, hgame]
    rw [← NNReal.coe_le_coe, hword]
    refine hle.trans (le_of_eq ?_)
    simp only [finiteScheme_pke] at hadv ⊢
    rw [← hadv]
    simp only [cpa, coe_nndist, Fintype.card_pi, Fintype.card_bool, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one,
      Nat.cast_mul, NNReal.coe_add, NNReal.coe_mul, NNReal.coe_ofNat, NNReal.coe_natCast,
      NNReal.coe_inv, NNReal.coe_pow, NNReal.coe_one]
    ring
  refine negligible_of_le ?_ hbound
  have h₁ : Negligible fun n => 2 * cpa n := hcpa'.const_mul 2
  have h₂ : Negligible fun n => ((6 * q n : ℕ) : ℝ≥0) * ((2 : ℝ≥0) ^ P.msgLen n)⁻¹ :=
    hmsg.polynomiallyBounded_mul (by fun_prop)
  have h₃ : Negligible fun n => ((2 * (2 * q n + 1) : ℕ) : ℝ≥0) * δ n :=
    hδneg.polynomiallyBounded_mul (by fun_prop)
  exact (h₁.add_fun h₂).add_fun h₃

end WordPKE

end Cslib.Crypto.Protocols.FujisakiOkamoto
