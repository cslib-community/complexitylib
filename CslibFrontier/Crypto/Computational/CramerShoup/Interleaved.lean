/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.CramerShoup
public import CslibFrontier.Crypto.Computational.Encryption.CCA.Interleaved

/-!
# Interleaved multi-challenge CCA security of Cramer–Shoup

Multiplicative Cramer–Shoup is secure in the fully adaptive interleaved-query multi-challenge CCA
game ([Boneh and Shoup, Section 12.1, Attack Game 12.1][BonehShoup2023]). The proof composes its
single-challenge 1CCA security, `DDH.indcca2On_cramerShoup` ([BonehShoup2023], Theorem 12.9), with
the generic hybrid reduction `Encryption.INDCCA2On.indcca2InterleavedOn` ([BonehShoup2023],
Theorem 12.1).

## Main results

* `Cslib.Crypto.PrimeOrderGroupFamily.DDH.indcca2InterleavedOn_cramerShoup`: Multiplicative
  Cramer–Shoup satisfies `Encryption.INDCCA2InterleavedOn` under DDH and collision resistance of
  its hash.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Section 12.1 (Attack Game 12.1 and Theorem 12.1, printed
  pp. 467–469), Section 12.5 (Theorem 12.9, printed pp. 490–491) and Exercise 12.27 (printed
  pp. 521–522).
-/

public section

namespace Cslib.Crypto.PrimeOrderGroupFamily

open Probability Turing.MultiTapeTM Encryption
open scoped NNReal

/-- **Fully adaptive interleaved-query multi-challenge CCA security of Multiplicative Cramer–Shoup
(`Encryption.INDCCA2InterleavedOn`)** ([BonehShoup2023], Theorem 12.1, Theorem 12.9, and Exercise
12.27, printed pp. 468, 490–491, 521–522): for any polynomial-time group description family
`d : ℕ → F.Desc`, the probabilistic polynomial-time Cramer–Shoup encryption scheme
`(cramerShoupKeyGenProb d, cramerShoupEncryptProb H d, cramerShoupDecryptOpt H isElem d)` satisfies
the fully adaptive interleaved-query multi-challenge `Encryption.INDCCA2InterleavedOn` notion with
respect to `cramerShoupValid isElem d` under DDH, collision resistance of `cramerShoupHashMod H`,
and a positive group-order lower bound `m n > 0` with `1 / m n` negligible. -/
theorem DDH.indcca2InterleavedOn_cramerShoup
    {F : PrimeOrderGroupFamily}
    {H : F.Desc × List Bool → List Bool}
    {isElem : F.Desc × List Bool → Bool}
    {d : ℕ → F.Desc}
    (hH : ComputableInPolyTime H (encPair F.encDesc encBits) encBits)
    (hisElem : ComputableInPolyTime isElem (encPair F.encDesc encBits) encBool)
    (hd : ComputableInPolyTime d encUnary F.encDesc)
    (hmem : ∀ d x, isElem (d, x) = true ↔ x ∈ Set.range (F.encode d))
    (hDDH : F.DDH (fun n => PMF.pure (d n)))
    (hCR : CollisionResistantFor F.encDesc (fun n => PMF.pure (d n)) (F.cramerShoupHashMod H))
    {m : ℕ → ℕ} (hm0 : ∀ n, 0 < m n)
    (hm : ∀ n, m n ≤ F.order (d n))
    (hinv : Negligible fun n => (1 / m n : ℝ≥0)) :
    INDCCA2InterleavedOn (F.cramerShoupValid isElem d) encBits encBits
      (F.cramerShoupKeyGenProb d) (F.cramerShoupEncryptProb H d)
      (F.cramerShoupDecryptOpt H isElem d) :=
  (hDDH.indcca2On_cramerShoup hH hisElem hd hmem hCR hm0 hm hinv).indcca2InterleavedOn
    (F.computableInPolyTime_cramerShoupValid hisElem hd)
    (F.isPPTOn_cramerShoupKeyGenProb hd)
    (F.isPPTOn_cramerShoupEncryptProb hH hd)
    (F.computableInPolyTime_cramerShoupDecryptOpt hH hisElem hd)

end Cslib.Crypto.PrimeOrderGroupFamily
