/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.CramerShoup.Interleaved
public import CslibFrontier.Crypto.Computational.DiscreteLog.Decodable

/-!
# Multiplicative Cramer–Shoup over decodable prime-order group families

The core Cramer–Shoup modules (`CramerShoup.Scheme`, `CramerShoup.Reductions`, `CramerShoup`, and
`CramerShoup.Interleaved`) accept an explicit group-membership test `isElem : F.Desc × List Bool →
Bool`, a polynomial-time certificate `hisElem`, and the range characterization `hmem` so that they
remain valid over any `PrimeOrderGroupFamily` and avoid colliding with concurrent work in `#5293`
(`fix/5293-cs-keyed-hash`).

When the underlying family is a `DecodablePrimeOrderGroupFamily`, `F.isElem`,
`F.computableInPolyTime_isElem`, and `F.isElem_eq_true_iff` supply all three arguments
automatically. This module exposes those specialized operations and IND-CCA2 security theorems
without `isElem`, `hisElem`, or `hmem` parameters.

## Main definitions

* `Cslib.Crypto.DecodablePrimeOrderGroupFamily.cramerShoupValid`: challenge-pair group-membership
  admissibility using `F.isElem`.
* `Cslib.Crypto.DecodablePrimeOrderGroupFamily.decodeCramerShoup`,
  `Cslib.Crypto.DecodablePrimeOrderGroupFamily.cramerShoupADDecryptOpt`,
  `Cslib.Crypto.DecodablePrimeOrderGroupFamily.cramerShoupDecryptOpt`: Cramer–Shoup decryption
  using `F.isElem`.

## Main results

* `Cslib.Crypto.DecodablePrimeOrderGroupFamily.DDH.indcca2ADOn_cramerShoup`: native
  `Encryption.INDCCA2ADOn` security without external `isElem` premises.
* `Cslib.Crypto.DecodablePrimeOrderGroupFamily.DDH.indcca2On_cramerShoup`: native
  `Encryption.INDCCA2On` security without external `isElem` premises.
* `Cslib.Crypto.DecodablePrimeOrderGroupFamily.DDH.indcca2MultiOn_cramerShoup`: batch-challenge
  multi-challenge `Encryption.INDCCA2MultiOn` security without external `isElem` premises.
* `Cslib.Crypto.DecodablePrimeOrderGroupFamily.DDH.indcca2InterleavedOn_cramerShoup`: interleaved
  multi-challenge `Encryption.INDCCA2InterleavedOn` security without external `isElem` premises.
-/

public section

namespace Cslib.Crypto.DecodablePrimeOrderGroupFamily

open Probability Turing.MultiTapeTM Encryption PrimeOrderGroupFamily
open scoped NNReal

variable (F : DecodablePrimeOrderGroupFamily)

/-- Challenge-pair group-membership admissibility predicate for native Cramer–Shoup CCA games over
a decodable family. -/
abbrev cramerShoupValid (d : ℕ → F.Desc) : ℕ → List Bool → List Bool → List Bool → Bool :=
  F.toPrimeOrderGroupFamily.cramerShoupValid F.isElem d

/-- Word-level Cramer–Shoup decryption with associated data using `F.isElem`. -/
abbrev decodeCramerShoup (H : F.Desc × List Bool → List Bool) (d : F.Desc)
    (sk : (ℕ × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ))) (ct ad : List Bool) : Option (List Bool) :=
  F.toPrimeOrderGroupFamily.decodeCramerShoup H F.isElem d sk ct ad

/-- Deterministic polynomial-time Cramer–Shoup decryption with associated data using `F.isElem`. -/
abbrev cramerShoupADDecryptOpt (H : F.Desc × List Bool → List Bool) (d : ℕ → F.Desc)
    (n : ℕ) (skBits ct ad : List Bool) : Option (List Bool) :=
  F.toPrimeOrderGroupFamily.cramerShoupADDecryptOpt H F.isElem d n skBits ct ad

/-- Deterministic polynomial-time Cramer–Shoup decryption using `F.isElem`. -/
abbrev cramerShoupDecryptOpt (H : F.Desc × List Bool → List Bool) (d : ℕ → F.Desc)
    (n : ℕ) (skBits ct : List Bool) : Option (List Bool) :=
  F.toPrimeOrderGroupFamily.cramerShoupDecryptOpt H F.isElem d n skBits ct

/-- Native `Encryption.INDCCA2ADOn` security for Multiplicative Cramer–Shoup over a
`DecodablePrimeOrderGroupFamily` (no external `isElem`, `hisElem`, or `hmem` parameters). -/
theorem DDH.indcca2ADOn_cramerShoup
    {F : DecodablePrimeOrderGroupFamily}
    {AD : Type} (encAD : AD ↪ List Bool)
    {H : F.Desc × List Bool → List Bool}
    {d : ℕ → F.Desc}
    (hH : ComputableInPolyTime H (encPair F.encDesc encBits) encBits)
    (hd : ComputableInPolyTime d encUnary F.encDesc)
    (hDDH : F.toPrimeOrderGroupFamily.DDH (fun n => PMF.pure (d n)))
    (hCR : CollisionResistantFor F.encDesc (fun n => PMF.pure (d n))
      (F.toPrimeOrderGroupFamily.cramerShoupHashMod H))
    {m : ℕ → ℕ} (hm0 : ∀ n, 0 < m n)
    (hm : ∀ n, m n ≤ F.order (d n))
    (hinv : Negligible fun n => (1 / m n : ℝ≥0)) :
    INDCCA2ADOn (F.cramerShoupValid d) encBits encAD encBits
      (F.cramerShoupKeyGenProb d) (F.cramerShoupADEncryptProb encAD H d)
      (F.cramerShoupADDecryptOpt H d) :=
  PrimeOrderGroupFamily.DDH.indcca2ADOn_cramerShoup (F := F.toPrimeOrderGroupFamily) encAD
    hH F.computableInPolyTime_isElem hd F.isElem_eq_true_iff hDDH hCR hm0 hm hinv

/-- Native `Encryption.INDCCA2On` security for Multiplicative Cramer–Shoup over a
`DecodablePrimeOrderGroupFamily` (no external `isElem`, `hisElem`, or `hmem` parameters). -/
theorem DDH.indcca2On_cramerShoup
    {F : DecodablePrimeOrderGroupFamily}
    {H : F.Desc × List Bool → List Bool}
    {d : ℕ → F.Desc}
    (hH : ComputableInPolyTime H (encPair F.encDesc encBits) encBits)
    (hd : ComputableInPolyTime d encUnary F.encDesc)
    (hDDH : F.toPrimeOrderGroupFamily.DDH (fun n => PMF.pure (d n)))
    (hCR : CollisionResistantFor F.encDesc (fun n => PMF.pure (d n))
      (F.toPrimeOrderGroupFamily.cramerShoupHashMod H))
    {m : ℕ → ℕ} (hm0 : ∀ n, 0 < m n)
    (hm : ∀ n, m n ≤ F.order (d n))
    (hinv : Negligible fun n => (1 / m n : ℝ≥0)) :
    INDCCA2On (F.cramerShoupValid d) encBits encBits
      (F.cramerShoupKeyGenProb d) (F.cramerShoupEncryptProb H d)
      (F.cramerShoupDecryptOpt H d) :=
  PrimeOrderGroupFamily.DDH.indcca2On_cramerShoup (F := F.toPrimeOrderGroupFamily)
    hH F.computableInPolyTime_isElem hd F.isElem_eq_true_iff hDDH hCR hm0 hm hinv

/-- Batch-challenge multi-challenge `Encryption.INDCCA2MultiOn` security for Multiplicative
Cramer–Shoup over a `DecodablePrimeOrderGroupFamily`. -/
theorem DDH.indcca2MultiOn_cramerShoup
    {F : DecodablePrimeOrderGroupFamily}
    {H : F.Desc × List Bool → List Bool}
    {d : ℕ → F.Desc}
    (hH : ComputableInPolyTime H (encPair F.encDesc encBits) encBits)
    (hd : ComputableInPolyTime d encUnary F.encDesc)
    (hDDH : F.toPrimeOrderGroupFamily.DDH (fun n => PMF.pure (d n)))
    (hCR : CollisionResistantFor F.encDesc (fun n => PMF.pure (d n))
      (F.toPrimeOrderGroupFamily.cramerShoupHashMod H))
    {m : ℕ → ℕ} (hm0 : ∀ n, 0 < m n)
    (hm : ∀ n, m n ≤ F.order (d n))
    (hinv : Negligible fun n => (1 / m n : ℝ≥0)) :
    INDCCA2MultiOn (F.cramerShoupValid d) encBits encBits
      (F.cramerShoupKeyGenProb d) (F.cramerShoupEncryptProb H d)
      (F.cramerShoupDecryptOpt H d) :=
  PrimeOrderGroupFamily.DDH.indcca2MultiOn_cramerShoup (F := F.toPrimeOrderGroupFamily)
    hH F.computableInPolyTime_isElem hd F.isElem_eq_true_iff hDDH hCR hm0 hm hinv

/-- Interleaved multi-challenge `Encryption.INDCCA2InterleavedOn` security for Multiplicative
Cramer–Shoup over a `DecodablePrimeOrderGroupFamily`. -/
theorem DDH.indcca2InterleavedOn_cramerShoup
    {F : DecodablePrimeOrderGroupFamily}
    {H : F.Desc × List Bool → List Bool}
    {d : ℕ → F.Desc}
    (hH : ComputableInPolyTime H (encPair F.encDesc encBits) encBits)
    (hd : ComputableInPolyTime d encUnary F.encDesc)
    (hDDH : F.toPrimeOrderGroupFamily.DDH (fun n => PMF.pure (d n)))
    (hCR : CollisionResistantFor F.encDesc (fun n => PMF.pure (d n))
      (F.toPrimeOrderGroupFamily.cramerShoupHashMod H))
    {m : ℕ → ℕ} (hm0 : ∀ n, 0 < m n)
    (hm : ∀ n, m n ≤ F.order (d n))
    (hinv : Negligible fun n => (1 / m n : ℝ≥0)) :
    INDCCA2InterleavedOn (F.cramerShoupValid d) encBits encBits
      (F.cramerShoupKeyGenProb d) (F.cramerShoupEncryptProb H d)
      (F.cramerShoupDecryptOpt H d) :=
  PrimeOrderGroupFamily.DDH.indcca2InterleavedOn_cramerShoup (F := F.toPrimeOrderGroupFamily)
    hH F.computableInPolyTime_isElem hd F.isElem_eq_true_iff hDDH hCR hm0 hm hinv

end Cslib.Crypto.DecodablePrimeOrderGroupFamily
