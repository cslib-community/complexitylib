/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Crypto.Computational.CramerShoup.Interleaved
import CslibFrontier.Crypto.Computational.DiscreteLog.SchnorrGroup
import Mathlib.Tactic.NormNum.Prime

/-! Clients of the keyed Cramer–Shoup API and of `PrimeOrderGroupFamily.withKey` under module
encapsulation: the asymptotic theorems with a keyed collision-resistance premise, the DDH transfer
to `withKey`, and a concrete keyed roundtrip on a Schnorr group. -/

open Cslib Cslib.Probability Cslib.Crypto Cslib.Crypto.Encryption
  Cslib.Crypto.PrimeOrderGroupFamily Turing.MultiTapeTM
open scoped NNReal

-- The native theorems need only DDH for the fixed groups and CR of the keyed hash family.
example {F : PrimeOrderGroupFamily}
    {H : F.withKey.Desc × List Bool → List Bool} {isElem : F.Desc × List Bool → Bool}
    {d : ℕ → F.Desc} {keyLen : ℕ → ℕ}
    (hH : ComputableInPolyTime H (encPair F.withKey.encDesc encBits) encBits)
    (hisElem : ComputableInPolyTime isElem (encPair F.encDesc encBits) encBool)
    (hd : ComputableInPolyTime d encUnary F.encDesc)
    (hkeyLen : ComputableInPolyTime keyLen encUnary encUnary)
    (hmem : ∀ d x, isElem (d, x) = true ↔ x ∈ Set.range (F.encode d))
    (hDDH : F.DDH (fun n => PMF.pure (d n)))
    (hCR : CollisionResistantFor F.withKey.encDesc
      (F.withKeySetup (fun n => PMF.pure (d n)) keyLen) (F.withKey.cramerShoupHashMod H))
    {m : ℕ → ℕ} (hm0 : ∀ n, 0 < m n) (hm : ∀ n, m n ≤ F.order (d n))
    (hinv : Negligible fun n => (1 / m n : ℝ≥0)) :
    INDCCA2On (F.cramerShoupValid isElem d) encBits encBits
      (F.cramerShoupKeyGenProb d keyLen) (F.cramerShoupEncryptProb H d)
      (F.cramerShoupDecryptOpt H isElem d) ∧
    INDCCA2InterleavedOn (F.cramerShoupValid isElem d) encBits encBits
      (F.cramerShoupKeyGenProb d keyLen) (F.cramerShoupEncryptProb H d)
      (F.cramerShoupDecryptOpt H isElem d) :=
  ⟨hDDH.indcca2On_cramerShoup hH hisElem hd hkeyLen hmem hCR hm0 hm hinv,
   hDDH.indcca2InterleavedOn_cramerShoup hH hisElem hd hkeyLen hmem hCR hm0 hm hinv⟩

-- DDH transfers to the family with an attached key, through a certified reduction.
example {F : PrimeOrderGroupFamily} {setup : ℕ → PMF F.Desc} {keyLen : ℕ → ℕ}
    (hDDH : F.DDH setup) (hkeyLen : ComputableInPolyTime keyLen encUnary encUnary)
    {D : F.withKey.DDHDistinguisher} (hD : D.IsPPT) :
    F.withKey.DDH (F.withKeySetup setup keyLen) ∧ (F.ddhSampleKey keyLen D).IsPPT :=
  ⟨hDDH.withKey hkeyLen, isPPT_ddhSampleKey hkeyLen hD⟩

-- A key drawn by `withKeySetup` has the scheduled length.
example {F : PrimeOrderGroupFamily} {setup : ℕ → PMF F.Desc} {keyLen : ℕ → ℕ} {n : ℕ}
    {d : F.Desc} {k : List Bool} (h : (d, k) ∈ (F.withKeySetup setup keyLen n).support) :
    k.length = keyLen n :=
  (F.mem_support_withKeySetup h).2

-- The hash key published by key generation is read back from the public key word.
example {F : PrimeOrderGroupFamily} (d : F.Desc) (hk u : List Bool)
    (sk : (ℕ × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ))) :
    cramerShoupPkHashKey (F.withKey.encodeCramerShoupPublicKey (d, hk) u sk) = hk := by
  simp
