/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Probabilistic.AffineHash
public import CslibFrontier.Crypto.Computational.InaccessibleEntropy.Basic
public import CslibFrontier.Crypto.Computational.OneWay
public import CslibFrontier.Foundations.Data.BitString.List.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Log
import CslibFrontier.Computability.Probabilistic.Sampling
import CslibFrontier.Crypto.Computational.OneWay.Collision
import CslibFrontier.Crypto.Computational.OneWay.Normalize
import CslibFrontier.Crypto.Negligible.Basic
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Map
import CslibFrontier.Tactic.PPT

/-!
# Inaccessible average max-entropy from any one-way function

Given any uniform `OneWay` function `f`, output-length normalization
(`OneWay.exists_fixedOutputLength`) produces a one-way function `g` sending `n`-bit inputs to
`m(n)`-bit outputs. Adapting `[HHRVW2020]`, Section 4.2, Theorem 4.5 (pp. 21–25), we combine `g`
with the constructible `3`-wise independent Boolean affine hash family `affineHash` on `m(n)`-bit
strings (`isThreeWiseIndependentHash_affineHash`) and a dyadic `(Nat.log 2 n + 1)`-bit prefix
index `r` truncated at `min r n`:
$$F_0(x, A, b, r) = \bigl(A, b, r, \mathrm{zeroPadPrefix}\;n\;r\;(A\,g(x) + b)\bigr).$$

Whereas `[HHRVW2020]`, Theorem 4.5 (p. 21) uses a polynomial light-image threshold
$2^{n - i} / n^c$ over $i \in [n]$ to obtain an entropy gap of $d \log n / n$ for every constant
$d > 0$ under Definition 3.9 (p. 15), this module formalizes a weaker constant-threshold
adaptation: we fix one adversary-independent family `rompelAccessibleSet` using the constant
light-image threshold `rompelLightImages gFin y₀ r = {y₀} ∪ {y | 4 * |g⁻¹(y)| ≤ 2^(n - min r n)}`
(`2^(n - min r n) / 4` in place of `2^(n - i) / n^c`) against uniform strict-PPT adversaries,
obtaining the smaller inverse-linear gap `1 / (64 * (n + 1))`:

1. **Claim 4.6** (`rompelBase_escape_le_four_mul_inversion`, pp. 21–22): sampling a prefix-colliding
   affine seed via `adjustAffineSeed` (`toReal_map_adjustAffineSeed_eq`) turns any adversary `A`
   into a uniform strict-PPT `g`-inverter (`rompelBaseInverter`) whose inversion success is at least
   `(1 / 4)` of `A`'s escape probability outside `L₀`.
2. **Claim 4.8** (`rompelBase_heavy_sibling_prob_ge`, p. 23): for `gFin x ≠ gFin x*` with
   `|gFin⁻¹(gFin x)| ≤ |gFin⁻¹(gFin x*)| ≤ 2^(n - r)`, `3`-wise independence and Markov's
   inequality show that uniform resampling from `F₀⁻¹(F₀(x, s, r))` hits `(x*, s, r)` with
   probability at least `2^(-n) / 8`.
3. **Claim 4.7** (`rompelBase_accessible_le_conditionalEntropy_sub`, pp. 21, 23–25): choosing the
   isolating truncation length `r₀ = n - 1 - Nat.log 2 |gFin⁻¹(gFin x*)| < n` separates heavy
   siblings from `L₀`, giving an unconditional finite-`n` gap of
   `(1 - collisionProbability) / (16 * 2 ^ (Nat.log 2 n + 1))` and at least `1 / (64 * (n + 1))`
   whenever `collisionProbability ≤ 1 / 2`.
4. **Constant-threshold adaptation of Theorem 4.5** (`OneWay.exists_inaccessibleEntropyFamily`,
   p. 21): combining `OneWay.exists_fixedOutputLength` and `OneWay.output_collision_negligible`
   constructs an `InaccessibleEntropyFamily` with gap denominator `denom n = 64 * (n + 1)`.

## Main definitions

* `Cslib.Crypto.rompelTruncWidth`, `Cslib.Crypto.rompelSeedWidth`, `Cslib.Crypto.rompelBaseInLen`,
  `Cslib.Crypto.rompelBaseOutLen`: input/output bit-width functions of $F_0$.
* `Cslib.Crypto.RompelBaseInput`, `Cslib.Crypto.RompelBaseOutput`: structured finite views of
  $F_0$'s inputs and outputs, with bit-string equivalences `rompelBaseInputEquiv` and
  `rompelBaseOutputEquiv`.
* `Cslib.Crypto.rompelBaseHashFin`, `Cslib.Crypto.rompelBaseEvalWord`: finite and word-level
  evaluators of $F_0$.
* `Cslib.Crypto.rompelLightImages`, `Cslib.Crypto.rompelAccessibleInputSet`,
  `Cslib.Crypto.rompelAccessibleSet`: light-sibling sets and accessible preimage sets $L_0$.
* `Cslib.Crypto.rompelBaseInverter`: uniform strict-PPT OWF inverter reduction from $F_0$ escape.

## Main results

* `Cslib.Crypto.computableInPolyTime_rompelBaseEvalWord`: plain polynomial-time certificate for
  `rompelBaseEvalWord`.
* `Cslib.Crypto.isPPT_rompelBaseInverter`: plain uniform strict-PPT certificate for
  `rompelBaseInverter`.
* `Cslib.Crypto.rompelBase_escape_le_four_mul_inversion`: Claim 4.6 (`[HHRVW2020]`, pp. 21–22).
* `Cslib.Crypto.rompelBase_heavy_sibling_prob_ge`: Claim 4.8 (`[HHRVW2020]`, p. 23).
* `Cslib.Crypto.rompelBase_accessible_le_conditionalEntropy_sub`: constant-threshold Claim 4.7
  (`[HHRVW2020]`, pp. 21, 23–25).
* `Cslib.Crypto.OneWay.exists_inaccessibleEntropyFamily`: constant-threshold adaptation of
  Theorem 4.5 (`[HHRVW2020]`, p. 21), giving inverse-linear gap `1 / (64 * (n + 1))`.

## References

* [I. Haitner, T. Holenstein, O. Reingold, S. Vadhan, H. Wee, *Inaccessible Entropy II: IE
  Functions and Universal One-Way Hashing*, Section 4.2, Theorem 4.5 and Claims 4.6–4.8,
  pp. 21–25][HHRVW2020]
* [J. Rompel, *One-Way Functions are Necessary and Sufficient for Secure Signatures*, Section 3,
  pp. 388–391][Rompel1990]
-/

public section

namespace Cslib.Crypto

open Cslib.Probability Cslib.BitString.LinearHash Finset Turing.MultiTapeTM
open scoped BigOperators ENNReal NNReal

/-! ### Bit-width schedule and structured input/output views -/

/-- Bit width $\lfloor \log_2 n \rfloor + 1$ of the truncation-length field in $F_0$, large enough
to represent every $r \in \{0, \dots, n\}$ injectively (`n < 2 ^ rompelTruncWidth n`). -/
@[expose] def rompelTruncWidth (n : ℕ) : ℕ := Nat.log 2 n + 1

/-- Affine seed bit width $n m + n$ for hashing $m$-bit images to $n$-bit digests. -/
@[expose] def rompelSeedWidth (n m : ℕ) : ℕ := n * m + n

/-- Total input bit width $n + (n m + n) + (\lfloor \log_2 n \rfloor + 1)$ of $F_0$. -/
@[expose] def rompelBaseInLen (n m : ℕ) : ℕ := n + rompelSeedWidth n m + rompelTruncWidth n

/-- Total output bit width $(n m + n) + (\lfloor \log_2 n \rfloor + 1) + n$ of $F_0$. -/
@[expose] def rompelBaseOutLen (n m : ℕ) : ℕ := rompelSeedWidth n m + rompelTruncWidth n + n

@[fun_prop]
theorem computableInPolyTime_rompelTruncWidth :
    ComputableInPolyTime rompelTruncWidth encUnary encUnary := by
  unfold rompelTruncWidth
  have hlog : ComputableInPolyTime (Nat.log 2) encUnary encUnary :=
    ComputableInPolyTime.binary_log_two.comp ComputableInPolyTime.unary_to_binary
  exact ComputableInPolyTime.unary_add' hlog (ComputableInPolyTime.const 1)

private theorem computableInPolyTime_rompelSeedWidth {α : Type} {encode : α ↪ List Bool}
    {n m : α → ℕ} (hn : ComputableInPolyTime n encode encUnary)
    (hm : ComputableInPolyTime m encode encUnary) :
    ComputableInPolyTime (fun a => rompelSeedWidth (n a) (m a)) encode encUnary :=
  ComputableInPolyTime.unary_add' (ComputableInPolyTime.unary_mul' hn hm) hn

theorem lt_two_pow_rompelTruncWidth (n : ℕ) : n < 2 ^ rompelTruncWidth n := by
  simpa only [rompelTruncWidth] using Nat.lt_pow_succ_log_self (by decide : 1 < 2) n

theorem two_pow_rompelTruncWidth_le (n : ℕ) : 2 ^ rompelTruncWidth n ≤ 2 * (n + 1) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · decide
  · have hle := Nat.pow_log_le_self 2 (Nat.ne_of_gt hn)
    calc
      2 ^ rompelTruncWidth n = 2 ^ Nat.log 2 n * 2 := by rw [rompelTruncWidth, Nat.pow_succ]
      _ ≤ n * 2 := Nat.mul_le_mul_right 2 hle
      _ ≤ 2 * (n + 1) := by omega

/-- Structured input `(preimage, hashRows, hashShift, truncBits)` to `[HHRVW2020]`'s base function
$F_0$ (Section 4.2, Theorem 4.5, p. 21). -/
structure RompelBaseInput (n m : ℕ) where
  /-- Uniform `n`-bit input $x$ to the normalized one-way function $g$. -/
  preimage : BitString n
  /-- Matrix rows of the Boolean affine hash `BitString m → BitString n`. -/
  hashRows : Fin n → BitString m
  /-- Shift vector of the Boolean affine hash $h_{A, b}$. -/
  hashShift : BitString n
  /-- `(Nat.log 2 n + 1)`-bit word encoding the saturating prefix length $r \le n$. -/
  truncBits : BitString (rompelTruncWidth n)
  deriving DecidableEq, Fintype

instance (n m : ℕ) : Nonempty (RompelBaseInput n m) := ⟨⟨0, 0, 0, 0⟩⟩

/-- Saturating prefix length $r = \min(n, \mathrm{binaryValue}(\mathrm{truncBits})) \le n$. -/
@[expose] def RompelBaseInput.truncIndex {n m : ℕ} (z : RompelBaseInput n m) : ℕ :=
  BitString.boundedBinaryValue n (List.ofFn z.truncBits)

theorem RompelBaseInput.truncIndex_le {n m : ℕ} (z : RompelBaseInput n m) : z.truncIndex ≤ n :=
  BitString.boundedBinaryValue_le n (List.ofFn z.truncBits)

/-- Pack a `RompelBaseInput n m` into a word of length `rompelBaseInLen n m`. -/
@[expose] def RompelBaseInput.packWord {n m : ℕ} (z : RompelBaseInput n m) : List Bool :=
  List.ofFn z.preimage ++ packAffineSeed (z.hashRows, z.hashShift) ++ List.ofFn z.truncBits

@[simp] theorem RompelBaseInput.length_packWord {n m : ℕ} (z : RompelBaseInput n m) :
    z.packWord.length = rompelBaseInLen n m := by
  simp [RompelBaseInput.packWord, rompelBaseInLen, rompelSeedWidth]; omega

/-- Unpack a word into a `RompelBaseInput n m`. -/
@[expose] def RompelBaseInput.unpackWord (n m : ℕ) (w : List Bool) : RompelBaseInput n m :=
  let sLen := rompelSeedWidth n m
  let rest := w.drop n
  let seed := unpackAffineSeed n m (rest.take sLen)
  { preimage := BitString.ofList n (w.take n)
    hashRows := seed.1
    hashShift := seed.2
    truncBits := BitString.ofList (rompelTruncWidth n) (rest.drop sLen) }

@[simp] theorem RompelBaseInput.unpackWord_packWord {n m : ℕ} (z : RompelBaseInput n m) :
    RompelBaseInput.unpackWord n m z.packWord = z := by
  have hx : (List.ofFn z.preimage).length = n := List.length_ofFn
  have hs : (packAffineSeed (z.hashRows, z.hashShift)).length = rompelSeedWidth n m :=
    length_packAffineSeed _
  cases z with | mk pre rows shift tbits =>
  simp only [RompelBaseInput.packWord, RompelBaseInput.unpackWord, List.append_assoc,
    List.take_left' hx, List.drop_left' hx, List.take_left' hs, List.drop_left' hs,
    unpackAffineSeed_packAffineSeed, BitString.ofList_ofFn]

theorem RompelBaseInput.packWord_unpackWord {n m : ℕ} {w : List Bool}
    (hw : w.length = rompelBaseInLen n m) :
    (RompelBaseInput.unpackWord n m w).packWord = w := by
  have hx : (w.take n).length = n := by simp [hw, rompelBaseInLen]; omega
  have hs : ((w.drop n).take (rompelSeedWidth n m)).length = rompelSeedWidth n m := by
    simp [hw, rompelBaseInLen]; omega
  have ht : ((w.drop n).drop (rompelSeedWidth n m)).length = rompelTruncWidth n := by
    simp [hw, rompelBaseInLen]
  simp only [RompelBaseInput.unpackWord, RompelBaseInput.packWord, Prod.mk.eta,
    packAffineSeed_unpackAffineSeed hs, BitString.ofFn_ofList hx, BitString.ofFn_ofList ht,
    List.append_assoc, List.take_append_drop]

/-- Exact bit-string equivalence between `RompelBaseInput n m` and
`BitString (rompelBaseInLen n m)`. -/
@[expose] def rompelBaseInputEquiv (n m : ℕ) :
    RompelBaseInput n m ≃ BitString (rompelBaseInLen n m) where
  toFun z := BitString.ofList (rompelBaseInLen n m) z.packWord
  invFun b := RompelBaseInput.unpackWord n m (List.ofFn b)
  left_inv z := by
    dsimp only
    rw [BitString.ofFn_ofList z.length_packWord, RompelBaseInput.unpackWord_packWord]
  right_inv b := by
    dsimp only
    rw [RompelBaseInput.packWord_unpackWord List.length_ofFn, BitString.ofList_ofFn]

@[simp] theorem ofFn_rompelBaseInputEquiv {n m : ℕ} (z : RompelBaseInput n m) :
    List.ofFn (rompelBaseInputEquiv n m z) = z.packWord :=
  BitString.ofFn_ofList z.length_packWord

/-- Structured output `(hashRows, hashShift, truncBits, prefixDigest)` of `[HHRVW2020]`'s base
function $F_0$ (Section 4.2, Theorem 4.5, p. 21). -/
structure RompelBaseOutput (n m : ℕ) where
  /-- Matrix rows of the Boolean affine hash $h_{A, b}$. -/
  hashRows : Fin n → BitString m
  /-- Shift vector of the Boolean affine hash $h_{A, b}$. -/
  hashShift : BitString n
  /-- `(Nat.log 2 n + 1)`-bit word encoding the saturating prefix length $r$. -/
  truncBits : BitString (rompelTruncWidth n)
  /-- Zero-padded `r`-bit prefix of $h_{A, b}(g(x))$. -/
  prefixDigest : BitString n
  deriving DecidableEq, Fintype

/-- Pack a `RompelBaseOutput n m` into a word of length `rompelBaseOutLen n m`. -/
@[expose] def RompelBaseOutput.packWord {n m : ℕ} (y : RompelBaseOutput n m) : List Bool :=
  packAffineSeed (y.hashRows, y.hashShift) ++ List.ofFn y.truncBits ++ List.ofFn y.prefixDigest

@[simp] theorem RompelBaseOutput.length_packWord {n m : ℕ} (y : RompelBaseOutput n m) :
    y.packWord.length = rompelBaseOutLen n m := by
  simp [RompelBaseOutput.packWord, rompelBaseOutLen, rompelSeedWidth]; omega

/-- Unpack a word into a `RompelBaseOutput n m`. -/
@[expose] def RompelBaseOutput.unpackWord (n m : ℕ) (w : List Bool) : RompelBaseOutput n m :=
  let sLen := rompelSeedWidth n m
  let tLen := rompelTruncWidth n
  let seed := unpackAffineSeed n m (w.take sLen)
  let rest := w.drop sLen
  { hashRows := seed.1
    hashShift := seed.2
    truncBits := BitString.ofList tLen (rest.take tLen)
    prefixDigest := BitString.ofList n (rest.drop tLen) }

@[simp] theorem RompelBaseOutput.unpackWord_packWord {n m : ℕ} (y : RompelBaseOutput n m) :
    RompelBaseOutput.unpackWord n m y.packWord = y := by
  have hs : (packAffineSeed (y.hashRows, y.hashShift)).length = rompelSeedWidth n m :=
    length_packAffineSeed _
  have ht : (List.ofFn y.truncBits).length = rompelTruncWidth n := List.length_ofFn
  cases y with | mk rows shift tbits dig =>
  simp only [RompelBaseOutput.packWord, RompelBaseOutput.unpackWord, List.append_assoc,
    List.take_left' hs, List.drop_left' hs, List.take_left' ht, List.drop_left' ht,
    unpackAffineSeed_packAffineSeed, BitString.ofList_ofFn]

theorem RompelBaseOutput.packWord_unpackWord {n m : ℕ} {w : List Bool}
    (hw : w.length = rompelBaseOutLen n m) :
    (RompelBaseOutput.unpackWord n m w).packWord = w := by
  have hs : (w.take (rompelSeedWidth n m)).length = rompelSeedWidth n m := by
    simp [hw, rompelBaseOutLen]; omega
  have ht : ((w.drop (rompelSeedWidth n m)).take (rompelTruncWidth n)).length =
      rompelTruncWidth n := by
    simp [hw, rompelBaseOutLen]; omega
  have hd : ((w.drop (rompelSeedWidth n m)).drop (rompelTruncWidth n)).length = n := by
    simp [hw, rompelBaseOutLen]
  simp only [RompelBaseOutput.unpackWord, RompelBaseOutput.packWord, Prod.mk.eta,
    packAffineSeed_unpackAffineSeed hs, BitString.ofFn_ofList ht, BitString.ofFn_ofList hd,
    List.append_assoc, List.take_append_drop]

/-- Exact bit-string equivalence between `RompelBaseOutput n m` and
`BitString (rompelBaseOutLen n m)`. -/
@[expose] def rompelBaseOutputEquiv (n m : ℕ) :
    RompelBaseOutput n m ≃ BitString (rompelBaseOutLen n m) where
  toFun y := BitString.ofList (rompelBaseOutLen n m) y.packWord
  invFun b := RompelBaseOutput.unpackWord n m (List.ofFn b)
  left_inv y := by
    dsimp only
    rw [BitString.ofFn_ofList y.length_packWord, RompelBaseOutput.unpackWord_packWord]
  right_inv b := by
    dsimp only
    rw [RompelBaseOutput.packWord_unpackWord List.length_ofFn, BitString.ofList_ofFn]

/-! ### Finite and word-level evaluators of $F_0$ -/

/-- Finite evaluator $F_0(x, A, b, r) = (A, b, r, \mathrm{zeroPadPrefix}\;n\;r\;(A\,g(x) + b))$
(`[HHRVW2020]`, Section 4.2, Theorem 4.5, p. 21). -/
@[expose] def rompelBaseHashFin {n m : ℕ} (gFin : BitString n → BitString m)
    (z : RompelBaseInput n m) : RompelBaseOutput n m where
  hashRows := z.hashRows
  hashShift := z.hashShift
  truncBits := z.truncBits
  prefixDigest := zeroPadPrefix n z.truncIndex
    (Cslib.BitString.LinearHash.affineHash (z.hashRows, z.hashShift) (gFin z.preimage))

theorem rompelBaseHashFin_eq_iff {n m : ℕ} (gFin : BitString n → BitString m)
    (z' z : RompelBaseInput n m) :
    rompelBaseHashFin gFin z' = rompelBaseHashFin gFin z ↔
      z'.hashRows = z.hashRows ∧ z'.hashShift = z.hashShift ∧ z'.truncBits = z.truncBits ∧
        prefixProj n z.truncIndex
          (Cslib.BitString.LinearHash.affineHash (z.hashRows, z.hashShift) (gFin z'.preimage)) =
          prefixProj n z.truncIndex
            (Cslib.BitString.LinearHash.affineHash (z.hashRows, z.hashShift)
              (gFin z.preimage)) := by
  constructor
  · intro h
    have h1 := congrArg RompelBaseOutput.hashRows h
    have h2 := congrArg RompelBaseOutput.hashShift h
    have h3 := congrArg RompelBaseOutput.truncBits h
    have h4 := congrArg RompelBaseOutput.prefixDigest h
    dsimp only [rompelBaseHashFin] at h1 h2 h3 h4
    have ht : z'.truncIndex = z.truncIndex := by rw [RompelBaseInput.truncIndex, h3]; rfl
    rw [h1, h2, ht, zeroPadPrefix_eq_iff_prefixProj_eq] at h4
    exact ⟨h1, h2, h3, h4⟩
  · rintro ⟨h1, h2, h3, h4⟩
    cases z' with | mk x' r' s' t' =>
    cases z with | mk x r s t =>
    dsimp only at h1 h2 h3
    subst h1; subst h2; subst h3
    simp only [rompelBaseHashFin, RompelBaseOutput.mk.injEq, true_and]
    exact (zeroPadPrefix_eq_iff_prefixProj_eq _ _).mpr h4

/-- Word-level evaluator of `[HHRVW2020]`'s base function $F_0$
(Section 4.2, Theorem 4.5, p. 21). -/
@[expose] def rompelBaseEvalWord (g : List Bool → List Bool) (outLen : ℕ → ℕ)
    (n : ℕ) (zWord : List Bool) : List Bool :=
  let m := outLen n
  let sLen := rompelSeedWidth n m
  let tLen := rompelTruncWidth n
  let x := BitString.listRow n 0 (zWord.take n)
  let rest := zWord.drop n
  let seed := BitString.listRow sLen 0 (rest.take sLen)
  let rBits := BitString.listRow tLen 0 (rest.drop sLen)
  let r := BitString.boundedBinaryValue n rBits
  let gx := BitString.listRow m 0 (g x)
  let fullHash := wordAffineHash n seed gx
  seed ++ rBits ++ (fullHash.take r ++ List.replicate (n - r) false)

@[simp] theorem length_rompelBaseEvalWord (g : List Bool → List Bool) (outLen : ℕ → ℕ)
    (n : ℕ) (zWord : List Bool) :
    (rompelBaseEvalWord g outLen n zWord).length = rompelBaseOutLen n (outLen n) := by
  let r := BitString.boundedBinaryValue n
    (BitString.listRow (rompelTruncWidth n) 0 ((zWord.drop n).drop (rompelSeedWidth n (outLen n))))
  have hr : r ≤ n := BitString.boundedBinaryValue_le n _
  simp only [rompelBaseEvalWord, rompelBaseOutLen, List.length_append, BitString.length_listRow,
    List.length_take, length_wordAffineHash, List.length_replicate]
  change rompelSeedWidth n (outLen n) + rompelTruncWidth n + (min r n + (n - r)) = _
  omega

/-- On packed inputs, `rompelBaseEvalWord` computes `rompelBaseHashFin` exactly. -/
theorem rompelBaseEvalWord_packWord (g : List Bool → List Bool) (outLen : ℕ → ℕ) (n : ℕ)
    (z : RompelBaseInput n (outLen n)) :
    rompelBaseEvalWord g outLen n z.packWord =
      (rompelBaseHashFin (wordToFinMap n (outLen n) g) z).packWord := by
  let m := outLen n
  have hx : (List.ofFn z.preimage).length = n := List.length_ofFn
  have hs : (packAffineSeed (z.hashRows, z.hashShift)).length = rompelSeedWidth n m :=
    length_packAffineSeed _
  have ht : (List.ofFn z.truncBits).length = rompelTruncWidth n := List.length_ofFn
  have hx_row : BitString.listRow n 0 (z.packWord.take n) = List.ofFn z.preimage := by
    simp [RompelBaseInput.packWord, List.append_assoc, List.take_left' hx, BitString.listRow_zero,
      BitString.ofList_ofFn]
  have hseed_row : BitString.listRow (rompelSeedWidth n m) 0
      ((z.packWord.drop n).take (rompelSeedWidth n m)) =
      packAffineSeed (z.hashRows, z.hashShift) := by
    simp [RompelBaseInput.packWord, List.append_assoc, List.drop_left' hx, List.take_left' hs,
      BitString.listRow_zero, BitString.ofFn_ofList hs]
  have hr_row : BitString.listRow (rompelTruncWidth n) 0
      ((z.packWord.drop n).drop (rompelSeedWidth n m)) = List.ofFn z.truncBits := by
    simp [RompelBaseInput.packWord, List.append_assoc, List.drop_left' hx, List.drop_left' hs,
      BitString.listRow_zero, BitString.ofList_ofFn]
  have hgx : BitString.listRow m 0 (g (List.ofFn z.preimage)) =
      List.ofFn (wordToFinMap n m g z.preimage) :=
    BitString.listRow_zero m (g (List.ofFn z.preimage))
  have hr_le : z.truncIndex ≤ n := z.truncIndex_le
  simp only [rompelBaseEvalWord, RompelBaseOutput.packWord, rompelBaseHashFin]
  change (let sLen := rompelSeedWidth n m
    let tLen := rompelTruncWidth n
    let x := BitString.listRow n 0 (z.packWord.take n)
    let rest := z.packWord.drop n
    let seed := BitString.listRow sLen 0 (rest.take sLen)
    let rBits := BitString.listRow tLen 0 (rest.drop sLen)
    let r := BitString.boundedBinaryValue n rBits
    let gx := BitString.listRow m 0 (g x)
    let fullHash := wordAffineHash n seed gx
    seed ++ rBits ++ (fullHash.take r ++ List.replicate (n - r) false)) = _
  dsimp only
  rw [hx_row, hseed_row, hr_row, hgx, wordAffineHash_eq_ofFn, unpackAffineSeed_packAffineSeed,
    ofFn_zeroPadPrefix, Nat.min_eq_left hr_le]
  rfl

theorem wordToFinMap_rompelBaseEvalWord (g : List Bool → List Bool) (outLen : ℕ → ℕ) (n : ℕ)
    (z : RompelBaseInput n (outLen n)) :
    wordToFinMap (rompelBaseInLen n (outLen n)) (rompelBaseOutLen n (outLen n))
        (rompelBaseEvalWord g outLen n) (rompelBaseInputEquiv n (outLen n) z) =
      rompelBaseOutputEquiv n (outLen n)
        (rompelBaseHashFin (wordToFinMap n (outLen n) g) z) := by
  rw [wordToFinMap, ofFn_rompelBaseInputEquiv, rompelBaseEvalWord_packWord, rompelBaseOutputEquiv]
  rfl

/-- Plain polynomial-time certificate for `rompelBaseEvalWord`. -/
@[fun_prop]
theorem computableInPolyTime_rompelBaseEvalWord {g : List Bool → List Bool} {outLen : ℕ → ℕ}
    (hg : ComputableInPolyTime g encBits encBits)
    (houtLen : ComputableInPolyTime outLen encUnary encUnary) :
    ComputableInPolyTime (fun p : ℕ × List Bool => rompelBaseEvalWord g outLen p.1 p.2)
      (encPair encUnary encBits) encBits := by
  have hn := ComputableInPolyTime.fst encUnary encBits
  have hz := ComputableInPolyTime.snd encUnary encBits
  have hm := houtLen.comp hn
  have hsLen := computableInPolyTime_rompelSeedWidth hn hm
  have htLen := computableInPolyTime_rompelTruncWidth.comp hn
  have hx := ComputableInPolyTime.bitsRowWithInput hn (ComputableInPolyTime.const 0)
    (ComputableInPolyTime.bitsTakeWithInput hz hn)
  have hrest := ComputableInPolyTime.bitsDropWithInput hz hn
  have hseed := ComputableInPolyTime.bitsRowWithInput hsLen (ComputableInPolyTime.const 0)
    (ComputableInPolyTime.bitsTakeWithInput hrest hsLen)
  have hrBits := ComputableInPolyTime.bitsRowWithInput htLen (ComputableInPolyTime.const 0)
    (ComputableInPolyTime.bitsDropWithInput hrest hsLen)
  have hr := ComputableInPolyTime.bitsBoundedBinaryValueWithInput hn hrBits
  have hgx := ComputableInPolyTime.bitsRowWithInput hm (ComputableInPolyTime.const 0) (hg.comp hx)
  have hfull := computableInPolyTime_wordAffineHash hn hseed hgx
  have hpad := ComputableInPolyTime.bitsAppend (ComputableInPolyTime.bitsTakeWithInput hfull hr)
    ((ComputableInPolyTime.bitsReplicate false).comp
      (ComputableInPolyTime.unary_sub' hn hr))
  exact ComputableInPolyTime.bitsAppend (ComputableInPolyTime.bitsAppend hseed hrBits) hpad

/-! ### Accessible preimage sets $L_0$ and the OWF inverter reduction (Claim 4.6) -/

/-- Light sibling images
$\widetilde{L}(y_0, r) = \{y_0\} \cup \{y \mid 4 |g^{-1}(y)| \le 2^{n - \min(r, n)}\}$
(constant-threshold adaptation of `[HHRVW2020]`, Section 4.2, Theorem 4.5, p. 21, replacing the
source threshold $2^{n - i} / n^c$ by $2^{n - \min(r, n)} / 4$). -/
@[expose] def rompelLightImages {n m : ℕ} (gFin : BitString n → BitString m)
    (y₀ : BitString m) (r : ℕ) : Finset (BitString m) :=
  insert y₀ (univ.filter fun y => 4 * #(fiberSet gFin y) ≤ 2 ^ (n - min r n))

theorem self_mem_rompelLightImages {n m : ℕ} (gFin : BitString n → BitString m)
    (y₀ : BitString m) (r : ℕ) : y₀ ∈ rompelLightImages gFin y₀ r :=
  mem_insert_self y₀ _

/-- Accessible preimage set
$L_0(z) = \{z' \in F_0^{-1}(F_0(z)) \mid g(x') \in \widetilde{L}(g(x), r)\}$ on
`RompelBaseInput n m` (`[HHRVW2020]`, Section 4.2, Theorem 4.5, p. 21). -/
@[expose] def rompelAccessibleInputSet {n m : ℕ} (gFin : BitString n → BitString m)
    (z : RompelBaseInput n m) : Finset (RompelBaseInput n m) :=
  (fiberSet (rompelBaseHashFin gFin) (rompelBaseHashFin gFin z)).filter fun z' =>
    gFin z'.preimage ∈ rompelLightImages gFin (gFin z.preimage) z.truncIndex

theorem self_mem_rompelAccessibleInputSet {n m : ℕ} (gFin : BitString n → BitString m)
    (z : RompelBaseInput n m) : z ∈ rompelAccessibleInputSet gFin z :=
  mem_filter.mpr ⟨self_mem_fiberSet _ z, self_mem_rompelLightImages _ _ _⟩

theorem rompelAccessibleInputSet_subset_fiber {n m : ℕ} (gFin : BitString n → BitString m)
    (z : RompelBaseInput n m) :
    rompelAccessibleInputSet gFin z ⊆
      fiberSet (rompelBaseHashFin gFin) (rompelBaseHashFin gFin z) :=
  filter_subset _ _

/-- Accessible preimage set $L_0$ transported to `BitString (rompelBaseInLen n (outLen n))`. -/
@[expose] def rompelAccessibleSet (g : List Bool → List Bool) (outLen : ℕ → ℕ) (n : ℕ)
    (b : BitString (rompelBaseInLen n (outLen n))) :
    Finset (BitString (rompelBaseInLen n (outLen n))) :=
  (rompelAccessibleInputSet (wordToFinMap n (outLen n) g)
    ((rompelBaseInputEquiv n (outLen n)).symm b)).map
      (rompelBaseInputEquiv n (outLen n)).toEmbedding

theorem self_mem_rompelAccessibleSet (g : List Bool → List Bool) (outLen : ℕ → ℕ) (n : ℕ)
    (b : BitString (rompelBaseInLen n (outLen n))) :
    b ∈ rompelAccessibleSet g outLen n b := by
  rw [rompelAccessibleSet, mem_map]
  exact ⟨(rompelBaseInputEquiv n (outLen n)).symm b,
    self_mem_rompelAccessibleInputSet _ _,
    (rompelBaseInputEquiv n (outLen n)).apply_symm_apply b⟩

theorem rompelAccessibleSet_subset_fiber (g : List Bool → List Bool) (outLen : ℕ → ℕ) (n : ℕ)
    (b : BitString (rompelBaseInLen n (outLen n))) :
    rompelAccessibleSet g outLen n b ⊆
      fiberSet (wordToFinMap (rompelBaseInLen n (outLen n)) (rompelBaseOutLen n (outLen n))
          (rompelBaseEvalWord g outLen n))
        (wordToFinMap (rompelBaseInLen n (outLen n)) (rompelBaseOutLen n (outLen n))
          (rompelBaseEvalWord g outLen n) b) := by
  intro b' hb'
  rw [rompelAccessibleSet, mem_map] at hb'
  obtain ⟨z', hz', rfl⟩ := hb'
  have hz'_fib := mem_fiberSet _ _ _ |>.mp (rompelAccessibleInputSet_subset_fiber _ _ hz')
  rw [mem_fiberSet]
  simp only [Equiv.coe_toEmbedding]
  conv_rhs => rw [← (rompelBaseInputEquiv n (outLen n)).apply_symm_apply b]
  rw [wordToFinMap_rompelBaseEvalWord, wordToFinMap_rompelBaseEvalWord, hz'_fib]

/-- Uniform strict-PPT inverter reduction (`[HHRVW2020]`, Section 4.2, Claim 4.6, pp. 21–22):
on challenge image `y`, sample uniform `x` and `rBits`, sample a prefix-colliding affine seed via
`wordAdjustAffineSeed`, run `A` on `x ++ seed ++ rBits`, and output the `n`-bit prefix. -/
noncomputable def rompelBaseInverter (g : List Bool → List Bool) (outLen : ℕ → ℕ)
    (A : ℕ → List Bool → ProbComp (List Bool)) (n : ℕ) (y : List Bool) :
    ProbComp (List Bool) := do
  let x ← Cslib.BitString.sampleList n
  let rBits ← Cslib.BitString.sampleList (rompelTruncWidth n)
  let rawSeed ← Cslib.BitString.sampleList (rompelSeedWidth n (outLen n))
  let seed := wordAdjustAffineSeed n (outLen n)
    (Cslib.BitString.boundedBinaryValue n rBits) y (g x) rawSeed
  let raw ← A n (x ++ seed ++ rBits)
  return raw.take n

/-- Plain uniform strict-PPT certificate for `rompelBaseInverter`. -/
theorem isPPT_rompelBaseInverter {g : List Bool → List Bool} {outLen : ℕ → ℕ}
    {A : ℕ → List Bool → ProbComp (List Bool)}
    (hg : ComputableInPolyTime g encBits encBits)
    (houtLen : ComputableInPolyTime outLen encUnary encUnary)
    (hA : IsPPT encBits A) :
    IsPPT encBits (rompelBaseInverter g outLen A) := by
  apply IsPPTOn.isPPT
  have hn0 := ComputableInPolyTime.fst encUnary encBits
  refine hn0.sampleList.bind_with ?_
  have hp1 := ComputableInPolyTime.fst (encPair encUnary encBits) encBits
  refine (computableInPolyTime_rompelTruncWidth.comp (hn0.comp hp1)).sampleList.bind_with ?_
  have hp2 := ComputableInPolyTime.fst (encPair (encPair encUnary encBits) encBits) encBits
  have hn2 := hn0.comp (hp1.comp hp2)
  refine (computableInPolyTime_rompelSeedWidth hn2 (houtLen.comp hn2)).sampleList.bind_with ?_
  have hp3 := ComputableInPolyTime.fst
    (encPair (encPair (encPair encUnary encBits) encBits) encBits) encBits
  have hrawSeed := ComputableInPolyTime.snd
    (encPair (encPair (encPair encUnary encBits) encBits) encBits) encBits
  have hrBits := (ComputableInPolyTime.snd
    (encPair (encPair encUnary encBits) encBits) encBits).comp hp3
  have hp2' := hp2.comp hp3
  have hx := (ComputableInPolyTime.snd (encPair encUnary encBits) encBits).comp hp2'
  have hp1' := hp1.comp hp2'
  have hn := hn0.comp hp1'
  have hy := (ComputableInPolyTime.snd encUnary encBits).comp hp1'
  have hm := houtLen.comp hn
  have hseed := computableInPolyTime_wordAdjustAffineSeed hn hm
    (ComputableInPolyTime.bitsBoundedBinaryValueWithInput hn hrBits) hy (hg.comp hx) hrawSeed
  have hinp := ComputableInPolyTime.bitsAppend (ComputableInPolyTime.bitsAppend hx hseed) hrBits
  refine (hA.on.preprocess (hn.prod hinp)).bind_with (ComputableInPolyTime.isPPTOn ?_)
  have hp4 := ComputableInPolyTime.fst
    (encPair (encPair (encPair (encPair encUnary encBits) encBits) encBits) encBits) encBits
  have hraw := ComputableInPolyTime.snd
    (encPair (encPair (encPair (encPair encUnary encBits) encBits) encBits) encBits) encBits
  exact ComputableInPolyTime.bitsTakeWithInput hraw (hn.comp hp4)

private def rompelTupleEquiv (n m : ℕ) :
    (BitString n × ((Fin n → BitString m) × BitString n) × BitString (rompelTruncWidth n)) ≃
      RompelBaseInput n m where
  toFun t := ⟨t.1, t.2.1.1, t.2.1.2, t.2.2⟩
  invFun z := (z.preimage, (z.hashRows, z.hashShift), z.truncBits)
  left_inv t := by rcases t with ⟨x, ⟨rows, shift⟩, rBits⟩; rfl
  right_inv z := by cases z; rfl

private def affineSeedWordEquiv (k n : ℕ) :
    ((Fin k → BitString n) × BitString k) ≃ BitString (k * n + k) where
  toFun s := Cslib.BitString.ofList (k * n + k) (packAffineSeed s)
  invFun b := unpackAffineSeed k n (List.ofFn b)
  left_inv s := by
    dsimp only
    rw [Cslib.BitString.ofFn_ofList (length_packAffineSeed s), unpackAffineSeed_packAffineSeed]
  right_inv b := by
    dsimp only
    rw [packAffineSeed_unpackAffineSeed List.length_ofFn, Cslib.BitString.ofList_ofFn]

private theorem uniformList_seed_eq_map (k n : ℕ) :
    Cslib.BitString.uniformList (k * n + k) =
      (PMF.uniformOfFintype ((Fin k → BitString n) × BitString k)).map packAffineSeed := by
  rw [Cslib.BitString.uniformList, ← PMF.uniformOfFintype_map_equiv (affineSeedWordEquiv k n),
    PMF.map_comp]
  refine congrArg (PMF.uniformOfFintype _).map (funext fun s => ?_)
  exact Cslib.BitString.ofFn_ofList (length_packAffineSeed s)

private theorem uniformList_rompelBaseInLen_eq (n m : ℕ) :
    Cslib.BitString.uniformList (rompelBaseInLen n m) =
      (PMF.uniformOfFintype (BitString n)).bind fun x =>
        (PMF.uniformOfFintype (BitString (rompelTruncWidth n))).bind fun rBits =>
          (PMF.uniformOfFintype ((Fin n → BitString m) × BitString n)).map fun s =>
            (RompelBaseInput.mk x s.1 s.2 rBits).packWord := by
  let e1 := Equiv.prodAssoc (BitString n) ((Fin n → BitString m) × BitString n)
    (BitString (rompelTruncWidth n))
  let e2 := Equiv.prodComm (BitString n × ((Fin n → BitString m) × BitString n))
    (BitString (rompelTruncWidth n))
  let eSwap : (BitString n × BitString (rompelTruncWidth n) ×
      ((Fin n → BitString m) × BitString n)) ≃ RompelBaseInput n m :=
    { toFun := fun t => ⟨t.1, t.2.2.1, t.2.2.2, t.2.1⟩
      invFun := fun z => (z.preimage, z.truncBits, (z.hashRows, z.hashShift))
      left_inv := fun t => by rcases t with ⟨x, rBits, ⟨rows, shift⟩⟩; rfl
      right_inv := fun z => by cases z; rfl }
  have hprod :
      ((PMF.uniformOfFintype (BitString n)).bind fun x =>
        (PMF.uniformOfFintype (BitString (rompelTruncWidth n))).bind fun rBits =>
          (PMF.uniformOfFintype ((Fin n → BitString m) × BitString n)).map fun s =>
            (x, rBits, s)) =
      PMF.uniformOfFintype
        (BitString n × BitString (rompelTruncWidth n) ×
          ((Fin n → BitString m) × BitString n)) := by
    rw [← PMF.uniformOfFintype_prod (BitString n)]
    refine PMF.bind_congr_on_support _ _ _ fun x _ => ?_
    rw [← PMF.uniformOfFintype_prod (BitString (rompelTruncWidth n)), PMF.map_bind]
    simp [PMF.map_comp, Function.comp_def]
  have heq :
      ((PMF.uniformOfFintype (BitString n)).bind fun x =>
        (PMF.uniformOfFintype (BitString (rompelTruncWidth n))).bind fun rBits =>
          (PMF.uniformOfFintype ((Fin n → BitString m) × BitString n)).map fun s =>
            (RompelBaseInput.mk x s.1 s.2 rBits).packWord) =
      ((PMF.uniformOfFintype (BitString n)).bind fun x =>
        (PMF.uniformOfFintype (BitString (rompelTruncWidth n))).bind fun rBits =>
          (PMF.uniformOfFintype ((Fin n → BitString m) × BitString n)).map fun s =>
            (x, rBits, s)).map (fun t => (eSwap t).packWord) := by
    simp [PMF.map_bind, PMF.map_comp, Function.comp_def, eSwap]
  rw [heq, hprod, Cslib.BitString.uniformList,
    ← PMF.uniformOfFintype_map_equiv (eSwap.trans (rompelBaseInputEquiv n m)), PMF.map_comp]
  refine congrArg (PMF.uniformOfFintype _).map (funext fun t => ?_)
  exact ofFn_rompelBaseInputEquiv (eSwap t)

private abbrev rompelEscPred (g : List Bool → List Bool) (outLen : ℕ → ℕ) (n : ℕ)
    (z : RompelBaseInput n (outLen n)) (raw : List Bool) : Prop :=
  raw.length = rompelBaseInLen n (outLen n) ∧
    rompelBaseEvalWord g outLen n raw = rompelBaseEvalWord g outLen n z.packWord ∧
    Cslib.BitString.ofList (rompelBaseInLen n (outLen n)) raw ∉
      rompelAccessibleSet g outLen n (rompelBaseInputEquiv n (outLen n) z)

open Classical in
private theorem rompelBase_escape_succProbability_eq (g : List Bool → List Bool) (outLen : ℕ → ℕ)
    (A : ℕ → List Bool → ProbComp (List Bool)) (n : ℕ) :
    (Game.succProbability (ProbComp.eval
      (accessibleEscapeGame (rompelBaseEvalWord g outLen)
        (fun k => rompelBaseInLen k (outLen k)) (rompelAccessibleSet g outLen) A n)) : ℝ) =
    ∑ x : BitString n, ((PMF.uniformOfFintype (BitString n)) x).toReal *
      ∑ rBits : BitString (rompelTruncWidth n),
        ((PMF.uniformOfFintype (BitString (rompelTruncWidth n))) rBits).toReal *
        ∑ s : (Fin n → BitString (outLen n)) × BitString n,
          ((PMF.uniformOfFintype ((Fin n → BitString (outLen n)) × BitString n)) s).toReal *
            ((ProbComp.eval (A n (RompelBaseInput.mk x s.1 s.2 rBits).packWord) >>= fun raw =>
              PMF.pure (decide (rompelEscPred g outLen n ⟨x, s.1, s.2, rBits⟩ raw)))
                true).toReal := by
  simp only [Game.succProbability, ENNReal.coe_toNNReal_eq_toReal, accessibleEscapeGame,
    ProbComp.eval_bind, Cslib.BitString.eval_sampleList, ProbComp.eval_pure]
  rw [uniformList_rompelBaseInLen_eq n (outLen n), PMF.bind_bind]
  simp only [PMF.bind_apply_toReal]
  refine sum_congr rfl fun x _ => congrArg (_ * ·) ?_
  rw [PMF.bind_bind]
  simp only [PMF.bind_apply_toReal]
  refine sum_congr rfl fun rBits _ => congrArg (_ * ·) ?_
  rw [PMF.bind_map, PMF.bind_apply_toReal]
  refine sum_congr rfl fun s _ => congrArg (_ * ·) ?_
  rfl

private theorem rompelBase_inversion_succProbability_eq (g : List Bool → List Bool)
    (outLen : ℕ → ℕ) (A : ℕ → List Bool → ProbComp (List Bool)) (n : ℕ)
    (hlen : ∀ w : List Bool, w.length = n → (g w).length = outLen n) :
    let gFin := wordToFinMap n (outLen n) g
    4 * (Game.succProbability (ProbComp.eval
      (inversionGame g (rompelBaseInverter g outLen A) n)) : ℝ) =
    ∑ x : BitString n, ((PMF.uniformOfFintype (BitString n)) x).toReal *
      ∑ rBits : BitString (rompelTruncWidth n),
        ((PMF.uniformOfFintype (BitString (rompelTruncWidth n))) rBits).toReal *
        ∑ y : BitString (outLen n),
          4 * (((PMF.uniformOfFintype (BitString n)).map gFin) y).toReal *
          ∑ s : (Fin n → BitString (outLen n)) × BitString n,
            (((PMF.uniformOfFintype ((Fin n → BitString (outLen n)) × BitString n)).map
              (adjustAffineSeed (Cslib.BitString.boundedBinaryValue n (List.ofFn rBits))
                (y + gFin x))) s).toReal *
            ((ProbComp.eval (A n (RompelBaseInput.mk x s.1 s.2 rBits).packWord) >>= fun raw =>
              PMF.pure (g (raw.take n) == List.ofFn y)) true).toReal := by
  intro gFin
  have hg_ofFn (x : BitString n) : g (List.ofFn x) = List.ofFn (gFin x) :=
    (Cslib.BitString.ofFn_ofList (hlen (List.ofFn x) List.length_ofFn)).symm
  have heval :
      ProbComp.eval (inversionGame g (rompelBaseInverter g outLen A) n) =
      ((PMF.uniformOfFintype (BitString n)).map gFin).bind fun y =>
        (PMF.uniformOfFintype (BitString n)).bind fun x =>
          (PMF.uniformOfFintype (BitString (rompelTruncWidth n))).bind fun rBits =>
            ((PMF.uniformOfFintype ((Fin n → BitString (outLen n)) × BitString n)).map
              (adjustAffineSeed (Cslib.BitString.boundedBinaryValue n (List.ofFn rBits))
                (y + gFin x))).bind fun s =>
              ProbComp.eval (A n (RompelBaseInput.mk x s.1 s.2 rBits).packWord) >>=
                fun raw => PMF.pure (g (raw.take n) == List.ofFn y) := by
    simp only [inversionGame, rompelBaseInverter, ProbComp.eval_bind,
      Cslib.BitString.eval_sampleList, ProbComp.eval_pure, PMF.bind_bind, PMF.pure_bind,
      PMF.monad_bind_eq_bind]
    dsimp only [gFin]
    rw [rompelSeedWidth, uniformList_seed_eq_map n (outLen n),
      Cslib.BitString.uniformList, PMF.bind_map, PMF.bind_map]
    refine PMF.bind_congr_on_support _ _ _ fun x₀ _ => ?_
    dsimp only [Function.comp_def]
    rw [PMF.bind_map]
    refine PMF.bind_congr_on_support _ _ _ fun x _ => ?_
    dsimp only [Function.comp_def]
    rw [Cslib.BitString.uniformList, PMF.bind_map]
    refine PMF.bind_congr_on_support _ _ _ fun rBits _ => ?_
    dsimp only [Function.comp_def]
    rw [PMF.bind_map, PMF.bind_map]
    refine PMF.bind_congr_on_support _ _ _ fun sRaw _ => ?_
    simp only [Function.comp_def, hg_ofFn, wordAdjustAffineSeed_eq_packAffineSeed,
      Cslib.BitString.ofList_ofFn, unpackAffineSeed_packAffineSeed, RompelBaseInput.packWord,
      Prod.mk.eta]
    rfl
  simp only [Game.succProbability, ENNReal.coe_toNNReal_eq_toReal, heval, PMF.bind_apply_toReal,
    mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun x _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun rBits _ => sum_congr rfl fun y _ => sum_congr rfl fun s _ => ?_
  ring

open Classical in
private theorem rompelBase_escape_seed_toReal_le (g : List Bool → List Bool) (outLen : ℕ → ℕ)
    (A : ℕ → List Bool → ProbComp (List Bool)) (n : ℕ)
    (hlen : ∀ w : List Bool, w.length = n → (g w).length = outLen n)
    (x : BitString n) (rBits : BitString (rompelTruncWidth n))
    (s : (Fin n → BitString (outLen n)) × BitString n) :
    let gFin := wordToFinMap n (outLen n) g
    let r := Cslib.BitString.boundedBinaryValue n (List.ofFn rBits)
    ((ProbComp.eval (A n (RompelBaseInput.mk x s.1 s.2 rBits).packWord) >>= fun raw =>
        PMF.pure (decide (rompelEscPred g outLen n ⟨x, s.1, s.2, rBits⟩ raw))) true).toReal ≤
      ∑ y ∈ (rompelLightImages gFin (gFin x) r)ᶜ,
        if prefixProj n r (Cslib.BitString.LinearHash.affineHash s y) =
            prefixProj n r (Cslib.BitString.LinearHash.affineHash s (gFin x)) then
          ((ProbComp.eval (A n (RompelBaseInput.mk x s.1 s.2 rBits).packWord) >>= fun raw =>
            PMF.pure (g (raw.take n) == List.ofFn y)) true).toReal
        else 0 := by
  intro gFin r
  let m := outLen n
  have hg_ofFn (x' : BitString n) : g (List.ofFn x') = List.ofFn (gFin x') :=
    (Cslib.BitString.ofFn_ofList (hlen (List.ofFn x') List.length_ofFn)).symm
  let pA := ProbComp.eval (A n (RompelBaseInput.mk x s.1 s.2 rBits).packWord)
  have hkey (raw : List Bool) (hesc : rompelEscPred g outLen n ⟨x, s.1, s.2, rBits⟩ raw) :
      let y := gFin (RompelBaseInput.unpackWord n m raw).preimage
      y ∈ (rompelLightImages gFin (gFin x) r)ᶜ ∧
        prefixProj n r (Cslib.BitString.LinearHash.affineHash s y) =
          prefixProj n r (Cslib.BitString.LinearHash.affineHash s (gFin x)) ∧
        (g (raw.take n) == List.ofFn y) = true := by
    rcases hesc with ⟨hlen_raw, heval_raw, hnot_acc⟩
    let z : RompelBaseInput n m := ⟨x, s.1, s.2, rBits⟩
    let z' := RompelBaseInput.unpackWord n m raw
    have hpack' : z'.packWord = raw := RompelBaseInput.packWord_unpackWord hlen_raw
    have hequiv' : rompelBaseInputEquiv n m z' =
        Cslib.BitString.ofList (rompelBaseInLen n m) raw := by
      simp [rompelBaseInputEquiv, hpack']
    have hhash : rompelBaseHashFin gFin z' = rompelBaseHashFin gFin z := by
      apply (rompelBaseOutputEquiv n m).injective
      rw [← wordToFinMap_rompelBaseEvalWord, ← wordToFinMap_rompelBaseEvalWord,
        wordToFinMap, wordToFinMap, ofFn_rompelBaseInputEquiv, ofFn_rompelBaseInputEquiv,
        hpack', heval_raw]
    have hcoll := (rompelBaseHashFin_eq_iff gFin z' z).mp hhash
    have hz'_not : z' ∉ rompelAccessibleInputSet gFin z := by
      intro hz'
      apply hnot_acc
      rw [← hequiv', rompelAccessibleSet, mem_map]
      refine ⟨z', ?_, rfl⟩
      dsimp only [gFin, m, z] at hz' ⊢
      simpa only [(rompelBaseInputEquiv n (outLen n)).symm_apply_apply] using hz'
    have hnot_light : gFin z'.preimage ∉ rompelLightImages gFin (gFin x) r := by
      intro hlight
      exact hz'_not (mem_filter.mpr ⟨mem_fiberSet _ _ _ |>.mpr hhash, hlight⟩)
    have htake : raw.take n = List.ofFn z'.preimage := by
      rw [← hpack', RompelBaseInput.packWord, List.append_assoc,
        List.take_left' (List.length_ofFn (f := z'.preimage))]
    exact ⟨mem_compl.mpr hnot_light, hcoll.2.2.2, by rw [htake, hg_ofFn, beq_self_eq_true]⟩
  have hbind (P : List Bool → Prop) [DecidablePred P] :
      ((pA >>= fun raw => PMF.pure (decide (P raw))) true).toReal =
        ∑' raw, (pA raw).toReal * if P raw then 1 else 0 := by
    rw [show (pA >>= _) = pA.bind _ from rfl, PMF.bind_apply_toReal_tsum]
    refine tsum_congr fun raw => congrArg ((pA raw).toReal * ·) ?_
    by_cases h : P raw <;> simp [h]
  have hsum (P : List Bool → Prop) [DecidablePred P] :
      Summable (fun raw => (pA raw).toReal * if P raw then 1 else 0) :=
    Summable.of_nonneg_of_le (fun _ => by split_ifs <;> positivity)
      (fun _ => by split_ifs <;> simp [ENNReal.toReal_nonneg]) (PMF.summable_toReal pA)
  have hrhs : (∑ y ∈ (rompelLightImages gFin (gFin x) r)ᶜ,
      if prefixProj n r (Cslib.BitString.LinearHash.affineHash s y) =
          prefixProj n r (Cslib.BitString.LinearHash.affineHash s (gFin x)) then
        ((pA >>= fun raw => PMF.pure (g (raw.take n) == List.ofFn y)) true).toReal
      else 0) =
      ∑' raw, ∑ y ∈ (rompelLightImages gFin (gFin x) r)ᶜ, (pA raw).toReal *
        (if prefixProj n r (Cslib.BitString.LinearHash.affineHash s y) =
            prefixProj n r (Cslib.BitString.LinearHash.affineHash s (gFin x)) ∧
            g (raw.take n) = List.ofFn y then 1 else 0) := by
    refine (sum_congr rfl fun y _ => ?_).trans (Summable.tsum_finsetSum (fun y _ => hsum _)).symm
    split_ifs with hpref
    · rw [show (pA >>= _) = pA.bind _ from rfl, PMF.bind_apply_toReal_tsum]
      refine tsum_congr fun raw => congrArg ((pA raw).toReal * ·) ?_
      by_cases hg_eq : g (raw.take n) = List.ofFn y <;> simp [hpref, hg_eq]
    · symm; convert tsum_zero with raw; simp [hpref]
  rw [hbind, hrhs]
  refine Summable.tsum_le_tsum (fun raw => ?_) (hsum _) (summable_sum fun y _ => hsum _)
  split_ifs with hesc
  · obtain ⟨hy_mem, hpref, hg_eq⟩ := hkey raw hesc
    rw [mul_one]
    refine le_trans ?_ (single_le_sum (f := fun y => (pA raw).toReal *
        (if prefixProj n r (Cslib.BitString.LinearHash.affineHash s y) =
            prefixProj n r (Cslib.BitString.LinearHash.affineHash s (gFin x)) ∧
            g (raw.take n) = List.ofFn y then 1 else 0))
      (fun y _ => by split_ifs <;> positivity) hy_mem)
    simp [hpref, beq_iff_eq.mp hg_eq]
  · rw [mul_zero]
    exact sum_nonneg fun y _ => by split_ifs <;> positivity

private theorem rompelBase_heavy_image_mass_ge {n m r : ℕ} (hr_le : r ≤ n)
    (gFin : BitString n → BitString m) {y₀ y : BitString m}
    (hy_not : y ∉ rompelLightImages gFin y₀ r) :
    (1 : ℝ) ≤ 4 * (((PMF.uniformOfFintype (BitString n)).map gFin) y).toReal * (2 : ℝ) ^ r := by
  have hy_heavy : 2 ^ (n - r) < 4 * #(fiberSet gFin y) := by
    by_contra! hle
    exact hy_not (mem_insert_of_mem (mem_filter.mpr ⟨mem_univ y, by rwa [Nat.min_eq_left hr_le]⟩))
  have hcard_sub : Nat.card {a : BitString n // gFin a = y} = #(fiberSet gFin y) :=
    Nat.card_eq_fintype_card.trans (card_fiberSet_eq_fintypeCard gFin y).symm
  rw [PMF.uniformOfFintype_map_apply, hcard_sub, ENNReal.toReal_div, ENNReal.toReal_natCast,
    ENNReal.toReal_natCast]
  have hcard_bs : (Fintype.card (BitString n) : ℝ) = (2 : ℝ) ^ n := by
    simp only [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool, Nat.cast_pow,
      Nat.cast_ofNat]
  have hpow_split : (2 : ℝ) ^ n = (2 : ℝ) ^ (n - r) * (2 : ℝ) ^ r := by
    rw [← pow_add, Nat.sub_add_cancel hr_le]
  have hheavy_real : (2 : ℝ) ^ (n - r) ≤ 4 * (#(fiberSet gFin y) : ℝ) := by
    exact_mod_cast hy_heavy.le
  rw [hcard_bs, hpow_split]
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (n - r) := by positivity
  have hpos_r : (0 : ℝ) < (2 : ℝ) ^ r := by positivity
  rw [show 4 * ((#(fiberSet gFin y) : ℝ) / ((2 : ℝ) ^ (n - r) * (2 : ℝ) ^ r)) * (2 : ℝ) ^ r =
      (4 * (#(fiberSet gFin y) : ℝ)) / (2 : ℝ) ^ (n - r) by field_simp]
  exact (one_le_div hpos).mpr hheavy_real

/-- **`[HHRVW2020]`, Section 4.2, Claim 4.6 (pp. 21–22)**: for any fixed-output-length function `g`
(`(g w).length = outLen n` on `n`-bit inputs) and any adversary `A`, escaping `rompelAccessibleSet`
with a fixed-width colliding preimage occurs with probability at most `4` times the inversion
success of `rompelBaseInverter g outLen A`. -/
theorem rompelBase_escape_le_four_mul_inversion (g : List Bool → List Bool) (outLen : ℕ → ℕ)
    (A : ℕ → List Bool → ProbComp (List Bool)) (n : ℕ)
    (hlen : ∀ w : List Bool, w.length = n → (g w).length = outLen n) :
    (Game.succProbability (ProbComp.eval
      (accessibleEscapeGame (rompelBaseEvalWord g outLen)
        (fun k => rompelBaseInLen k (outLen k)) (rompelAccessibleSet g outLen) A n)) : ℝ) ≤
      4 * (Game.succProbability (ProbComp.eval
        (inversionGame g (rompelBaseInverter g outLen A) n)) : ℝ) := by
  let m := outLen n
  let gFin : BitString n → BitString m := wordToFinMap n m g
  classical
  rw [rompelBase_escape_succProbability_eq g outLen A n,
    rompelBase_inversion_succProbability_eq g outLen A n hlen]
  refine sum_le_sum fun x _ => mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
  refine sum_le_sum fun rBits _ => mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
  let r := Cslib.BitString.boundedBinaryValue n (List.ofFn rBits)
  have hr_le : r ≤ n := Cslib.BitString.boundedBinaryValue_le n _
  have hr_min : min r n = r := Nat.min_eq_left hr_le
  calc
    (∑ s : (Fin n → BitString m) × BitString n,
        ((PMF.uniformOfFintype ((Fin n → BitString m) × BitString n)) s).toReal *
          ((ProbComp.eval (A n (RompelBaseInput.mk x s.1 s.2 rBits).packWord) >>= fun raw =>
            PMF.pure (decide (rompelEscPred g outLen n ⟨x, s.1, s.2, rBits⟩ raw))) true).toReal)
      ≤ ∑ s : (Fin n → BitString m) × BitString n,
          ((PMF.uniformOfFintype ((Fin n → BitString m) × BitString n)) s).toReal *
            ∑ y ∈ (rompelLightImages gFin (gFin x) r)ᶜ,
              if prefixProj n r (Cslib.BitString.LinearHash.affineHash s y) =
                  prefixProj n r (Cslib.BitString.LinearHash.affineHash s (gFin x)) then
                ((ProbComp.eval (A n (RompelBaseInput.mk x s.1 s.2 rBits).packWord) >>= fun raw =>
                  PMF.pure (g (raw.take n) == List.ofFn y)) true).toReal
              else 0 :=
      sum_le_sum fun s _ => mul_le_mul_of_nonneg_left
        (rompelBase_escape_seed_toReal_le g outLen A n hlen x rBits s) ENNReal.toReal_nonneg
    _ = ∑ y ∈ (rompelLightImages gFin (gFin x) r)ᶜ,
          ∑ s : (Fin n → BitString m) × BitString n,
            ((PMF.uniformOfFintype ((Fin n → BitString m) × BitString n)) s).toReal *
              (if prefixProj n r (Cslib.BitString.LinearHash.affineHash s y) =
                  prefixProj n r (Cslib.BitString.LinearHash.affineHash s (gFin x)) then
                ((ProbComp.eval (A n (RompelBaseInput.mk x s.1 s.2 rBits).packWord) >>= fun raw =>
                  PMF.pure (g (raw.take n) == List.ofFn y)) true).toReal
              else 0) := by
      simp only [mul_sum]
      exact sum_comm
    _ ≤ ∑ y : BitString m, 4 * (((PMF.uniformOfFintype (BitString n)).map gFin) y).toReal *
          ∑ s : (Fin n → BitString m) × BitString n,
            (((PMF.uniformOfFintype ((Fin n → BitString m) × BitString n)).map
              (adjustAffineSeed r (y + gFin x))) s).toReal *
            ((ProbComp.eval (A n (RompelBaseInput.mk x s.1 s.2 rBits).packWord) >>= fun raw =>
              PMF.pure (g (raw.take n) == List.ofFn y)) true).toReal := by
      refine le_trans (sum_le_sum fun y hy_compl => ?_)
        (sum_le_univ_sum_of_nonneg fun y => mul_nonneg (by positivity)
          (sum_nonneg fun s _ => mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg))
      have hy_not : y ∉ rompelLightImages gFin (gFin x) r := mem_compl.mp hy_compl
      have hy_ne : y ≠ gFin x := fun h => hy_not (h ▸ self_mem_rompelLightImages _ _ _)
      have hmass_y := rompelBase_heavy_image_mass_ge hr_le gFin hy_not
      rw [mul_sum]
      refine sum_le_sum fun s _ => ?_
      split_ifs with hpref
      · have hadj := toReal_map_adjustAffineSeed_eq r hy_ne hpref
        rw [hr_min] at hadj
        rw [hadj]
        have hu_nonneg : 0 ≤ ((PMF.uniformOfFintype ((Fin n → BitString m) × BitString n))
            s).toReal := ENNReal.toReal_nonneg
        have hp_nonneg : 0 ≤ ((ProbComp.eval (A n (RompelBaseInput.mk x s.1 s.2 rBits).packWord) >>=
            fun raw => PMF.pure (g (raw.take n) == List.ofFn y)) true).toReal :=
          ENNReal.toReal_nonneg
        nlinarith [mul_le_mul_of_nonneg_right hmass_y (mul_nonneg hu_nonneg hp_nonneg)]
      · rw [mul_zero]
        exact mul_nonneg (mul_nonneg (by positivity) ENNReal.toReal_nonneg)
          (mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)

/-! ### Sibling isolation via 3-wise independence (Claim 4.8) and the entropy gap (Claim 4.7) -/

private theorem card_prefixProj_eq_of_restrict (n m r : ℕ) (hr : r ≤ n)
    (T : Finset (BitString m)) (hT : #T ≤ 3) (y₁ : BitString m) (hy₁ : y₁ ∈ T)
    (P : (Fin n → BitString m) × BitString n → Prop) [DecidablePred P]
    (hP : ∀ s, P s ↔ ∀ u ∈ T,
      prefixProj n r (Cslib.BitString.LinearHash.affineHash s u) =
        prefixProj n r (Cslib.BitString.LinearHash.affineHash s y₁)) :
    (#(univ.filter P) : ℝ) =
      (2 : ℝ) ^ r * ((Fintype.card ((Fin n → BitString m) × BitString n) : ℝ) *
        (((2 : ℝ) ^ r) ^ #T)⁻¹) := by
  let S := (Fin n → BitString m) × BitString n
  let H (s : S) (y : BitString m) := prefixProj n r (Cslib.BitString.LinearHash.affineHash s y)
  have hh := isThreeWiseIndependentHash_prefixProj_affineHash n m r
  have hpart : univ.filter P =
      univ.biUnion fun w : BitString (min r n) =>
        univ.filter fun s : S => T.restrict (H s) = fun _ => w := by
    ext s
    simp only [mem_filter, mem_univ, true_and, mem_biUnion, hP s]
    refine ⟨fun hs => ⟨H s y₁, funext fun ⟨u, hu⟩ => hs u hu⟩,
      fun ⟨w, hw⟩ u hu =>
        (congrFun hw ⟨u, hu⟩).trans (congrFun hw ⟨y₁, hy₁⟩).symm⟩
  have hcard_part :
      #(univ.filter P) =
        ∑ w : BitString (min r n),
          #(univ.filter fun s : S => T.restrict (H s) = fun _ => w) := by
    rw [hpart, Finset.card_biUnion]
    intro w₁ _ w₂ _ hw₁₂
    dsimp only [Function.onFun]
    rw [disjoint_left]
    intro s hs₁ hs₂
    have h1 := congrFun (mem_filter.mp hs₁).2 ⟨y₁, hy₁⟩
    have h2 := congrFun (mem_filter.mp hs₂).2 ⟨y₁, hy₁⟩
    exact hw₁₂ (h1.symm.trans h2)
  rw [hcard_part, Nat.cast_sum]
  have hterm (w : BitString (min r n)) :
      (#(univ.filter fun s : S => T.restrict (H s) = fun _ => w) : ℝ) =
        (Fintype.card S : ℝ) * (((2 : ℝ) ^ r) ^ #T)⁻¹ := by
    have hd := congrArg (fun q : ℚ≥0 => (q : ℝ))
      (hh.dens_filter_restrict_eq (T := T) hT (fun _ => w))
    rw [Finset.dens_eq_card_div_card] at hd
    simp only [NNRat.cast_div, NNRat.cast_natCast, NNRat.cast_inv, NNRat.cast_pow,
      Fintype.card_fun, Fintype.card_fin, Fintype.card_bool, Nat.min_eq_left hr, Nat.cast_pow,
      Nat.cast_ofNat] at hd
    have hS : (Fintype.card S : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    exact (div_eq_iff hS).mp hd |>.trans (mul_comm _ _)
  simp only [hterm, sum_const, card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool,
    Nat.min_eq_left hr, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
  rfl

private theorem card_prefixProj_pair_eq (n m r : ℕ) (hr : r ≤ n)
    {y₁ y₂ : BitString m} (h₁₂ : y₁ ≠ y₂) :
    (#(univ.filter fun s : (Fin n → BitString m) × BitString n =>
        prefixProj n r (Cslib.BitString.LinearHash.affineHash s y₂) =
          prefixProj n r (Cslib.BitString.LinearHash.affineHash s y₁)) : ℝ) =
      (Fintype.card ((Fin n → BitString m) × BitString n) : ℝ) / (2 : ℝ) ^ r := by
  let T : Finset (BitString m) := {y₁, y₂}
  have hT_card : #T = 2 := card_pair h₁₂
  rw [card_prefixProj_eq_of_restrict n m r hr T (by omega) y₁ (by simp [T]) _
    (fun s => by simp only [T, mem_insert, mem_singleton, forall_eq_or_imp, forall_eq, true_and]),
    hT_card]
  have hpos : (2 : ℝ) ^ r ≠ 0 := by positivity
  field_simp

private theorem card_prefixProj_triple_eq (n m r : ℕ) (hr : r ≤ n)
    {y₁ y₂ y₃ : BitString m} (h₁₂ : y₁ ≠ y₂) (h₁₃ : y₁ ≠ y₃) (h₂₃ : y₂ ≠ y₃) :
    (#(univ.filter fun s : (Fin n → BitString m) × BitString n =>
        prefixProj n r (Cslib.BitString.LinearHash.affineHash s y₂) =
          prefixProj n r (Cslib.BitString.LinearHash.affineHash s y₁) ∧
          prefixProj n r (Cslib.BitString.LinearHash.affineHash s y₃) =
            prefixProj n r (Cslib.BitString.LinearHash.affineHash s y₁)) : ℝ) =
      (Fintype.card ((Fin n → BitString m) × BitString n) : ℝ) / ((2 : ℝ) ^ r) ^ 2 := by
  let T : Finset (BitString m) := {y₁, y₂, y₃}
  have hT_card : #T = 3 := by
    rw [card_insert_of_notMem (by simp [h₁₂, h₁₃]), card_pair h₂₃]
  rw [card_prefixProj_eq_of_restrict n m r hr T (by omega) y₁ (by simp [T]) _
    (fun s => by simp only [T, mem_insert, mem_singleton, forall_eq_or_imp, forall_eq, true_and]),
    hT_card]
  have hpos : (2 : ℝ) ^ r ≠ 0 := by positivity
  field_simp

private theorem card_subset_rompelBaseHashFin_fiber_eq {n m : ℕ}
    (gFin : BitString n → BitString m) (x : BitString n)
    (s : (Fin n → BitString m) × BitString n) (rBits : BitString (rompelTruncWidth n))
    (A : Finset (RompelBaseInput n m))
    (hA : A ⊆ fiberSet (rompelBaseHashFin gFin)
      (rompelBaseHashFin gFin ⟨x, s.1, s.2, rBits⟩)) :
    #A = #(univ.filter fun x' : BitString n =>
      RompelBaseInput.mk x' s.1 s.2 rBits ∈ A) := by
  refine card_bij (fun z' _ => z'.preimage)
    (fun z' hz' => ?_)
    (fun z₁ hz₁ z₂ hz₂ hpre => ?_)
    (fun x' hx' => ⟨⟨x', s.1, s.2, rBits⟩, (mem_filter.mp hx').2, rfl⟩)
  · have heq := (rompelBaseHashFin_eq_iff gFin z' ⟨x, s.1, s.2, rBits⟩).mp
      (mem_fiberSet _ _ _ |>.mp (hA hz'))
    have hz'eq : RompelBaseInput.mk z'.preimage s.1 s.2 rBits = z' := by
      cases z'; dsimp only at heq ⊢; congr
      · exact heq.1.symm
      · exact heq.2.1.symm
      · exact heq.2.2.1.symm
    exact mem_filter.mpr ⟨mem_univ _, hz'eq ▸ hz'⟩
  · have h₁ := (rompelBaseHashFin_eq_iff gFin z₁ ⟨x, s.1, s.2, rBits⟩).mp
      (mem_fiberSet _ _ _ |>.mp (hA hz₁))
    have h₂ := (rompelBaseHashFin_eq_iff gFin z₂ ⟨x, s.1, s.2, rBits⟩).mp
      (mem_fiberSet _ _ _ |>.mp (hA hz₂))
    cases z₁; cases z₂; dsimp only at hpre h₁ h₂; congr
    · exact h₁.1.trans h₂.1.symm
    · exact h₁.2.1.trans h₂.2.1.symm
    · exact h₁.2.2.1.trans h₂.2.2.1.symm

private theorem rompelBase_sum_otherColl_le {n m r : ℕ} (hr : r ≤ n)
    (gFin : BitString n → BitString m) {x xStar : BitString n} (hne : gFin x ≠ gFin xStar) :
    (∑ s ∈ univ.filter (fun s : (Fin n → BitString m) × BitString n =>
        prefixProj n r (Cslib.BitString.LinearHash.affineHash s (gFin xStar)) =
          prefixProj n r (Cslib.BitString.LinearHash.affineHash s (gFin x))),
      (#((univ.filter fun x' : BitString n => gFin x' ≠ gFin x ∧ gFin x' ≠ gFin xStar).filter
        fun x' => prefixProj n r (Cslib.BitString.LinearHash.affineHash s (gFin x')) =
          prefixProj n r (Cslib.BitString.LinearHash.affineHash s (gFin x))) : ℝ)) ≤
      (2 : ℝ) ^ (n - r) *
        (#(univ.filter fun s : (Fin n → BitString m) × BitString n =>
          prefixProj n r (Cslib.BitString.LinearHash.affineHash s (gFin xStar)) =
            prefixProj n r (Cslib.BitString.LinearHash.affineHash s (gFin x))) : ℝ) := by
  let S := (Fin n → BitString m) × BitString n
  let H (s : S) (y : BitString m) := prefixProj n r (Cslib.BitString.LinearHash.affineHash s y)
  let E : Finset S := univ.filter fun s => H s (gFin xStar) = H s (gFin x)
  let otherDom : Finset (BitString n) :=
    univ.filter fun x' => gFin x' ≠ gFin x ∧ gFin x' ≠ gFin xStar
  let otherColl (s : S) : Finset (BitString n) :=
    otherDom.filter fun x' => H s (gFin x') = H s (gFin x)
  have hexchange_nat : (∑ s ∈ E, #(otherColl s)) =
      ∑ x' ∈ otherDom, #(univ.filter fun s : S =>
        H s (gFin xStar) = H s (gFin x) ∧ H s (gFin x') = H s (gFin x)) := by
    simp only [otherColl, card_eq_sum_ones, sum_filter]
    rw [sum_comm]
    refine sum_congr rfl fun x' _ => ?_
    simp only [E, sum_filter, ite_and]
  have hexchange : (∑ s ∈ E, (#(otherColl s) : ℝ)) =
      ∑ x' ∈ otherDom, (#(univ.filter fun s : S =>
        H s (gFin xStar) = H s (gFin x) ∧ H s (gFin x') = H s (gFin x)) : ℝ) := by
    exact_mod_cast hexchange_nat
  rw [hexchange]
  have htriple (x' : BitString n) (hx' : x' ∈ otherDom) :
      (#(univ.filter fun s : S =>
        H s (gFin xStar) = H s (gFin x) ∧ H s (gFin x') = H s (gFin x)) : ℝ) =
      (Fintype.card S : ℝ) / ((2 : ℝ) ^ r) ^ 2 := by
    obtain ⟨h₁₃, h₂₃⟩ := (mem_filter.mp hx').2
    exact card_prefixProj_triple_eq n m r hr hne h₁₃.symm h₂₃.symm
  rw [sum_congr rfl htriple, sum_const, nsmul_eq_mul, card_prefixProj_pair_eq n m r hr hne]
  have hdom_le : (#otherDom : ℝ) ≤ (2 : ℝ) ^ n := by
    have : #otherDom ≤ Fintype.card (BitString n) := card_le_univ _
    simpa using (Nat.cast_le (α := ℝ)).mpr this
  have hpow_split : (2 : ℝ) ^ n = (2 : ℝ) ^ (n - r) * (2 : ℝ) ^ r := by
    rw [← pow_add, Nat.sub_add_cancel hr]
  calc
    (#otherDom : ℝ) * ((Fintype.card S : ℝ) / ((2 : ℝ) ^ r) ^ 2)
      ≤ (2 : ℝ) ^ n * ((Fintype.card S : ℝ) / ((2 : ℝ) ^ r) ^ 2) :=
        mul_le_mul_of_nonneg_right hdom_le (by positivity)
    _ = (2 : ℝ) ^ (n - r) * ((Fintype.card S : ℝ) / (2 : ℝ) ^ r) := by
        rw [hpow_split]; field_simp

/-- **`[HHRVW2020]`, Section 4.2, Claim 4.8 (p. 23)**: for distinct images `gFin x ≠ gFin xStar`
with `#(fiberSet gFin (gFin x)) ≤ #(fiberSet gFin (gFin xStar)) ≤ 2 ^ (n - r)` (`r ≤ n`),
uniformly sampling an affine seed `s` and then a uniform preimage from the `F₀`-fiber of
`(x, s, rBits)` (at truncation index `r`) yields `(xStar, s, rBits)` with probability at least
`((2 : ℝ) ^ n)⁻¹ / 8`. -/
theorem rompelBase_heavy_sibling_prob_ge {n m : ℕ} (gFin : BitString n → BitString m)
    {x xStar : BitString n} {rBits : BitString (rompelTruncWidth n)}
    (hne : gFin x ≠ gFin xStar)
    (hfib_le : #(fiberSet gFin (gFin x)) ≤ #(fiberSet gFin (gFin xStar)))
    (hstar_le : #(fiberSet gFin (gFin xStar)) ≤
      2 ^ (n - Cslib.BitString.boundedBinaryValue n (List.ofFn rBits))) :
    (((2 : ℝ) ^ n)⁻¹ / 8) ≤
      ∑ s : (Fin n → BitString m) × BitString n,
        ((PMF.uniformOfFintype ((Fin n → BitString m) × BitString n)) s).toReal *
          ((if RompelBaseInput.mk xStar s.1 s.2 rBits ∈
              fiberSet (rompelBaseHashFin gFin)
                (rompelBaseHashFin gFin ⟨x, s.1, s.2, rBits⟩) then (1 : ℝ) else 0) /
            #(fiberSet (rompelBaseHashFin gFin)
              (rompelBaseHashFin gFin ⟨x, s.1, s.2, rBits⟩))) := by
  let r := Cslib.BitString.boundedBinaryValue n (List.ofFn rBits)
  have hr : r ≤ n := Cslib.BitString.boundedBinaryValue_le n (List.ofFn rBits)
  have hstar_r : #(fiberSet gFin (gFin xStar)) ≤ 2 ^ (n - r) := hstar_le
  let S := (Fin n → BitString m) × BitString n
  let H (s : S) (y : BitString m) := prefixProj n r (Cslib.BitString.LinearHash.affineHash s y)
  let collInputs (s : S) : Finset (BitString n) :=
    univ.filter fun x' => H s (gFin x') = H s (gFin x)
  have hmem_input (s : S) (x' : BitString n) :
      RompelBaseInput.mk x' s.1 s.2 rBits ∈
        fiberSet (rompelBaseHashFin gFin) (rompelBaseHashFin gFin ⟨x, s.1, s.2, rBits⟩) ↔
      H s (gFin x') = H s (gFin x) := by
    rw [mem_fiberSet, rompelBaseHashFin_eq_iff]
    simp only [H, r, RompelBaseInput.truncIndex, true_and]
    rfl
  have hfib_card (s : S) :
      #(fiberSet (rompelBaseHashFin gFin) (rompelBaseHashFin gFin ⟨x, s.1, s.2, rBits⟩)) =
        #(collInputs s) := by
    rw [card_subset_rompelBaseHashFin_fiber_eq gFin x s rBits _ Subset.rfl]
    simp only [collInputs, hmem_input s]
  let E : Finset S := univ.filter fun s => H s (gFin xStar) = H s (gFin x)
  let otherDom : Finset (BitString n) :=
    univ.filter fun x' => gFin x' ≠ gFin x ∧ gFin x' ≠ gFin xStar
  let otherColl (s : S) : Finset (BitString n) :=
    otherDom.filter fun x' => H s (gFin x') = H s (gFin x)
  have hE_card : (#E : ℝ) = (Fintype.card S : ℝ) / (2 : ℝ) ^ r :=
    card_prefixProj_pair_eq n m r hr hne
  have hsum_other : (∑ s ∈ E, (#(otherColl s) : ℝ)) ≤ (2 : ℝ) ^ (n - r) * (#E : ℝ) :=
    rompelBase_sum_otherColl_le hr gFin hne
  -- Markov's inequality on `E`: at least half of `s ∈ E` have `#(otherColl s) ≤ 2 * 2 ^ (n - r)`:
  let Egood : Finset S := E.filter fun s => #(otherColl s) ≤ 2 * 2 ^ (n - r)
  let Ebad : Finset S := E.filter fun s => ¬ (#(otherColl s) ≤ 2 * 2 ^ (n - r))
  have hpart_E : (#Egood : ℝ) + (#Ebad : ℝ) = (#E : ℝ) := by
    exact_mod_cast card_filter_add_card_filter_not (s := E)
      (p := fun s => #(otherColl s) ≤ 2 * 2 ^ (n - r))
  have hbad_le : 2 * (2 : ℝ) ^ (n - r) * (#Ebad : ℝ) ≤ (∑ s ∈ E, (#(otherColl s) : ℝ)) := by
    calc
      2 * (2 : ℝ) ^ (n - r) * (#Ebad : ℝ)
        = ∑ _s ∈ Ebad, (2 * (2 : ℝ) ^ (n - r)) := by rw [sum_const, nsmul_eq_mul, mul_comm]
      _ ≤ ∑ s ∈ Ebad, (#(otherColl s) : ℝ) := by
          refine sum_le_sum fun s hs => ?_
          have hgt : 2 * 2 ^ (n - r) < #(otherColl s) := by
            have := (mem_filter.mp hs).2; omega
          exact_mod_cast hgt.le
      _ ≤ ∑ s ∈ E, (#(otherColl s) : ℝ) :=
          sum_le_sum_of_subset_of_nonneg (filter_subset _ E) (fun _ _ _ => Nat.cast_nonneg _)
  have hEgood_ge : (#E : ℝ) / 2 ≤ (#Egood : ℝ) := by
    have hpos : (0 : ℝ) < (2 : ℝ) ^ (n - r) := by positivity
    have h2bad : 2 * (#Ebad : ℝ) ≤ (#E : ℝ) := by nlinarith
    linarith
  -- Bound `#(collInputs s) ≤ 4 * 2 ^ (n - r)` for `s ∈ Egood`:
  have hcoll_le (s : S) (hs : s ∈ Egood) : #(collInputs s) ≤ 4 * 2 ^ (n - r) := by
    have hsub : collInputs s ⊆
        (fiberSet gFin (gFin x) ∪ fiberSet gFin (gFin xStar)) ∪ otherColl s := by
      intro x' hx'
      have hx'_coll := (mem_filter.mp hx').2
      by_cases h₁ : gFin x' = gFin x
      · exact mem_union_left _ (mem_union_left _ (mem_fiberSet _ _ _ |>.mpr h₁))
      · by_cases h₂ : gFin x' = gFin xStar
        · exact mem_union_left _ (mem_union_right _ (mem_fiberSet _ _ _ |>.mpr h₂))
        · exact mem_union_right _ (mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _, h₁, h₂⟩, hx'_coll⟩)
    have hcard_u : #(collInputs s) ≤
        #(fiberSet gFin (gFin x)) + #(fiberSet gFin (gFin xStar)) + #(otherColl s) := by
      calc
        #(collInputs s) ≤ #((fiberSet gFin (gFin x) ∪ fiberSet gFin (gFin xStar)) ∪ otherColl s) :=
          card_le_card hsub
        _ ≤ #(fiberSet gFin (gFin x) ∪ fiberSet gFin (gFin xStar)) + #(otherColl s) :=
          card_union_le _ _
        _ ≤ #(fiberSet gFin (gFin x)) + #(fiberSet gFin (gFin xStar)) + #(otherColl s) :=
          Nat.add_le_add_right (card_union_le _ _) _
    have hother_le : #(otherColl s) ≤ 2 * 2 ^ (n - r) := (mem_filter.mp hs).2
    have hfx_le : #(fiberSet gFin (gFin x)) ≤ 2 ^ (n - r) := hfib_le.trans hstar_r
    omega
  -- Conclude the lower bound by restricting the sum to `s ∈ Egood`:
  have hS_pos : (0 : ℝ) < Fintype.card S := by exact_mod_cast Fintype.card_pos (α := S)
  calc
    (((2 : ℝ) ^ n)⁻¹ / 8)
      = ((Fintype.card S : ℝ)⁻¹) * ((#E : ℝ) / 2) * ((4 * (2 : ℝ) ^ (n - r))⁻¹) := by
        rw [hE_card]
        have hpow_split : (2 : ℝ) ^ n = (2 : ℝ) ^ (n - r) * (2 : ℝ) ^ r := by
          rw [← pow_add, Nat.sub_add_cancel hr]
        rw [hpow_split]
        field_simp
        norm_num
    _ ≤ ((Fintype.card S : ℝ)⁻¹) * (#Egood : ℝ) * ((4 * (2 : ℝ) ^ (n - r))⁻¹) := by
        refine mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hEgood_ge (by positivity)) (by positivity)
    _ = ∑ _s ∈ Egood, ((Fintype.card S : ℝ)⁻¹ * (4 * (2 : ℝ) ^ (n - r))⁻¹) := by
        rw [sum_const, nsmul_eq_mul]; ring
    _ ≤ ∑ s ∈ Egood,
          ((PMF.uniformOfFintype S) s).toReal *
            ((if RompelBaseInput.mk xStar s.1 s.2 rBits ∈
                fiberSet (rompelBaseHashFin gFin)
                  (rompelBaseHashFin gFin ⟨x, s.1, s.2, rBits⟩) then (1 : ℝ) else 0) /
              #(fiberSet (rompelBaseHashFin gFin)
                (rompelBaseHashFin gFin ⟨x, s.1, s.2, rBits⟩))) := by
        refine sum_le_sum fun s hs => ?_
        have hsE : s ∈ E := (mem_filter.mp hs).1
        have hstar_in : H s (gFin xStar) = H s (gFin x) := (mem_filter.mp hsE).2
        have hmem_s := (hmem_input s xStar).mpr hstar_in
        simp only [PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast,
          hmem_s, ↓reduceIte, hfib_card s, one_div]
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have hpos_coll : (0 : ℝ) < #(collInputs s) := by
          have : x ∈ collInputs s := mem_filter.mpr ⟨mem_univ _, rfl⟩
          exact_mod_cast card_pos.mpr ⟨x, this⟩
        exact inv_anti₀ hpos_coll (by exact_mod_cast hcoll_le s hs)
    _ ≤ _ := sum_le_univ_sum_of_nonneg fun s =>
        mul_nonneg ENNReal.toReal_nonneg (div_nonneg (by split_ifs <;> positivity)
          (Nat.cast_nonneg _))

open Classical in
private noncomputable abbrev rompelSdiffWeight {n m : ℕ} (gFin : BitString n → BitString m)
    (x xStar : BitString n) (s : (Fin n → BitString m) × BitString n)
    (rBits : BitString (rompelTruncWidth n)) : ℝ :=
  (if RompelBaseInput.mk xStar s.1 s.2 rBits ∈
      fiberSet (rompelBaseHashFin gFin) (rompelBaseHashFin gFin ⟨x, s.1, s.2, rBits⟩) \
        rompelAccessibleInputSet gFin ⟨x, s.1, s.2, rBits⟩ then (1 : ℝ) else 0) /
    #(fiberSet (rompelBaseHashFin gFin) (rompelBaseHashFin gFin ⟨x, s.1, s.2, rBits⟩))

private theorem rompelBase_goodPair_term_ge {n m : ℕ} (gFin : BitString n → BitString m)
    {x xStar : BitString n} (hne : gFin x ≠ gFin xStar)
    (hfib_le : #(fiberSet gFin (gFin x)) ≤ #(fiberSet gFin (gFin xStar))) :
    (((2 : ℝ) ^ n)⁻¹ / (8 * (2 ^ rompelTruncWidth n : ℝ))) ≤
      ∑ rBits : BitString (rompelTruncWidth n), ((2 ^ rompelTruncWidth n : ℝ)⁻¹) *
        ∑ s : (Fin n → BitString m) × BitString n,
          ((PMF.uniformOfFintype ((Fin n → BitString m) × BitString n)) s).toReal *
            rompelSdiffWeight gFin x xStar s rBits := by
  have hx_not_in : x ∉ fiberSet gFin (gFin xStar) := by
    rw [mem_fiberSet]; exact hne
  have hsum_le : 1 + #(fiberSet gFin (gFin xStar)) ≤ 2 ^ n := by
    have hcard_ins : #(insert x (fiberSet gFin (gFin xStar))) ≤
        #(univ : Finset (BitString n)) := card_le_univ _
    rw [card_insert_of_notMem hx_not_in] at hcard_ins
    simpa [add_comm] using hcard_ins
  have hfib_pos : 1 ≤ #(fiberSet gFin (gFin xStar)) := card_fiberSet_pos gFin xStar
  let k := Nat.log 2 #(fiberSet gFin (gFin xStar))
  have hk_lt_n : k < n :=
    (Nat.log_lt_iff_lt_pow (by decide : 1 < 2) (by omega)).mpr (by omega)
  have hpow_k_le : 2 ^ k ≤ #(fiberSet gFin (gFin xStar)) :=
    Nat.pow_log_le_self 2 (by omega)
  have hlt_pow_succ : #(fiberSet gFin (gFin xStar)) < 2 ^ (k + 1) :=
    Nat.lt_pow_succ_log_self (by decide : 1 < 2) _
  let r₀ := n - 1 - k
  have hr₀_le : r₀ ≤ n := by omega
  have hsub_r₀ : n - r₀ = k + 1 := by omega
  have hr₀_lt_trunc : r₀ < 2 ^ rompelTruncWidth n :=
    lt_of_le_of_lt hr₀_le (lt_two_pow_rompelTruncWidth n)
  let rBits₀ : BitString (rompelTruncWidth n) := Cslib.BitString.ofList (rompelTruncWidth n)
    (Cslib.BitString.binaryWord (rompelTruncWidth n) r₀)
  have hbv_r₀ : Cslib.BitString.boundedBinaryValue n (List.ofFn rBits₀) = r₀ := by
    rw [Cslib.BitString.ofFn_ofList (Cslib.BitString.length_binaryWord hr₀_lt_trunc),
      Cslib.BitString.boundedBinaryValue_eq, Cslib.BitString.binaryValue_binaryWord,
      Nat.min_eq_right hr₀_le]
  have hstar_le : #(fiberSet gFin (gFin xStar)) ≤
      2 ^ (n - Cslib.BitString.boundedBinaryValue n (List.ofFn rBits₀)) := by
    rw [hbv_r₀, hsub_r₀]
    exact hlt_pow_succ.le
  have hnot_light : gFin xStar ∉ rompelLightImages gFin (gFin x) r₀ := by
    intro hmem
    rcases mem_insert.mp hmem with heq | hfilt
    · exact hne heq.symm
    · have hle4 := (mem_filter.mp hfilt).2
      rw [Nat.min_eq_left hr₀_le, hsub_r₀, Nat.pow_succ] at hle4
      omega
  have hclaim48 := rompelBase_heavy_sibling_prob_ge gFin (rBits := rBits₀) hne hfib_le hstar_le
  refine le_trans ?_ (single_le_sum (a := rBits₀)
    (fun rBits _ => mul_nonneg (by positivity) (sum_nonneg fun s _ =>
      mul_nonneg ENNReal.toReal_nonneg (div_nonneg (by split_ifs <;> positivity)
        (Nat.cast_nonneg _)))) (mem_univ rBits₀))
  rw [show ((2 : ℝ) ^ n)⁻¹ / (8 * (2 ^ rompelTruncWidth n : ℝ)) =
      (2 ^ rompelTruncWidth n : ℝ)⁻¹ * (((2 : ℝ) ^ n)⁻¹ / 8) by ring]
  refine mul_le_mul_of_nonneg_left (hclaim48.trans ?_) (by positivity)
  refine sum_le_sum fun s _ => mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
  have hsdiff_iff :
      RompelBaseInput.mk xStar s.1 s.2 rBits₀ ∈
        fiberSet (rompelBaseHashFin gFin) (rompelBaseHashFin gFin ⟨x, s.1, s.2, rBits₀⟩) \
          rompelAccessibleInputSet gFin ⟨x, s.1, s.2, rBits₀⟩ ↔
      RompelBaseInput.mk xStar s.1 s.2 rBits₀ ∈
        fiberSet (rompelBaseHashFin gFin) (rompelBaseHashFin gFin ⟨x, s.1, s.2, rBits₀⟩) := by
    rw [mem_sdiff]
    refine ⟨And.left, fun hfib => ⟨hfib, fun hacc => ?_⟩⟩
    have hl := (mem_filter.mp hacc).2
    rw [RompelBaseInput.truncIndex, hbv_r₀] at hl
    exact hnot_light hl
  simp only [hsdiff_iff, le_rfl]

private theorem rompelBase_escape_density_sum_eq {n m : ℕ} (gFin : BitString n → BitString m) :
    (∑ z : RompelBaseInput n m, ((PMF.uniformOfFintype (RompelBaseInput n m)) z).toReal *
      ((#(fiberSet (rompelBaseHashFin gFin) (rompelBaseHashFin gFin z) \
          rompelAccessibleInputSet gFin z) : ℝ) /
        #(fiberSet (rompelBaseHashFin gFin) (rompelBaseHashFin gFin z)))) =
    ∑ p : BitString n × BitString n, ((2 ^ n : ℝ)⁻¹) *
      ∑ rBits : BitString (rompelTruncWidth n), ((2 ^ rompelTruncWidth n : ℝ)⁻¹) *
        ∑ s : (Fin n → BitString m) × BitString n,
          ((PMF.uniformOfFintype ((Fin n → BitString m) × BitString n)) s).toReal *
            rompelSdiffWeight gFin p.1 p.2 s rBits := by
  let S := (Fin n → BitString m) × BitString n
  let R := BitString (rompelTruncWidth n)
  have hcard_Z : (Fintype.card (RompelBaseInput n m) : ℝ) =
      (2 ^ n : ℝ) * (2 ^ rompelTruncWidth n : ℝ) * (Fintype.card S : ℝ) := by
    have heq := Fintype.card_congr (rompelTupleEquiv n m)
    rw [← heq]
    dsimp only [S]
    simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool,
      Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    ring
  have hsdiff_sum (x : BitString n) (rBits : R) (s : S) :
      (#(fiberSet (rompelBaseHashFin gFin) (rompelBaseHashFin gFin ⟨x, s.1, s.2, rBits⟩) \
          rompelAccessibleInputSet gFin ⟨x, s.1, s.2, rBits⟩) : ℝ) =
        ∑ xStar : BitString n,
          if RompelBaseInput.mk xStar s.1 s.2 rBits ∈
              fiberSet (rompelBaseHashFin gFin) (rompelBaseHashFin gFin ⟨x, s.1, s.2, rBits⟩) \
                rompelAccessibleInputSet gFin ⟨x, s.1, s.2, rBits⟩ then (1 : ℝ) else 0 := by
    rw [card_subset_rompelBaseHashFin_fiber_eq gFin x s rBits _ sdiff_subset,
      card_eq_sum_ones, Nat.cast_sum, Nat.cast_one, sum_filter]
  conv_lhs => rw [← (rompelTupleEquiv n m).sum_comp, Fintype.sum_prod_type]
  conv_rhs => rw [Fintype.sum_prod_type]
  refine sum_congr rfl fun x _ => ?_
  conv_lhs => rw [Fintype.sum_prod_type, sum_comm]
  calc
    (∑ rBits : R, ∑ s : S,
        ((PMF.uniformOfFintype (RompelBaseInput n m))
          (rompelTupleEquiv n m (x, s, rBits))).toReal *
          ((#(fiberSet (rompelBaseHashFin gFin)
              (rompelBaseHashFin gFin (rompelTupleEquiv n m (x, s, rBits))) \
              rompelAccessibleInputSet gFin (rompelTupleEquiv n m (x, s, rBits))) : ℝ) /
            #(fiberSet (rompelBaseHashFin gFin)
              (rompelBaseHashFin gFin (rompelTupleEquiv n m (x, s, rBits))))))
      = ∑ rBits : R, ∑ s : S, ∑ xStar : BitString n,
          ((2 ^ n : ℝ)⁻¹) * ((2 ^ rompelTruncWidth n : ℝ)⁻¹) *
            ((PMF.uniformOfFintype S) s).toReal * rompelSdiffWeight gFin x xStar s rBits := by
      refine sum_congr rfl fun rBits _ => sum_congr rfl fun s _ => ?_
      have hunif : ((PMF.uniformOfFintype (RompelBaseInput n m))
          (rompelTupleEquiv n m (x, s, rBits))).toReal =
          ((2 ^ n : ℝ)⁻¹) * ((2 ^ rompelTruncWidth n : ℝ)⁻¹) *
            ((PMF.uniformOfFintype S) s).toReal := by
        simp only [PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast, hcard_Z]
        ring
      rw [hunif]
      simp only [rompelTupleEquiv, Equiv.coe_fn_mk, rompelSdiffWeight]
      rw [hsdiff_sum x rBits s, sum_div, mul_sum]
    _ = ∑ xStar : BitString n, ((2 ^ n : ℝ)⁻¹) *
          ∑ rBits : R, ((2 ^ rompelTruncWidth n : ℝ)⁻¹) *
            ∑ s : S, ((PMF.uniformOfFintype S) s).toReal *
              rompelSdiffWeight gFin x xStar s rBits := by
      rw [sum_congr rfl fun rBits _ => sum_comm, sum_comm]
      refine sum_congr rfl fun xStar _ => ?_
      rw [mul_sum]
      refine sum_congr rfl fun rBits _ => ?_
      rw [mul_sum, mul_sum]
      refine sum_congr rfl fun s _ => ?_
      ring

private theorem rompelBase_goodPairs_frac_ge {n m : ℕ} (gFin : BitString n → BitString m) :
    (1 - PMF.collisionProbability ((PMF.uniformOfFintype (BitString n)).map gFin)) / 2 ≤
      (#(univ.filter fun p : BitString n × BitString n => gFin p.1 ≠ gFin p.2 ∧
          #(fiberSet gFin (gFin p.1)) ≤ #(fiberSet gFin (gFin p.2))) : ℝ) /
        ((2 ^ n : ℝ) * (2 ^ n : ℝ)) := by
  let goodPairs : Finset (BitString n × BitString n) :=
    univ.filter fun p => gFin p.1 ≠ gFin p.2 ∧
      #(fiberSet gFin (gFin p.1)) ≤ #(fiberSet gFin (gFin p.2))
  let eqPairs : Finset (BitString n × BitString n) := univ.filter fun p => gFin p.1 = gFin p.2
  let neqPairs : Finset (BitString n × BitString n) := eqPairsᶜ
  have hneq_le_two_good : #neqPairs ≤ 2 * #goodPairs := by
    let swapEmb := (Equiv.prodComm (BitString n) (BitString n)).toEmbedding
    have hsub : neqPairs ⊆ goodPairs ∪ goodPairs.map swapEmb := by
      intro ⟨x₁, x₂⟩ hp
      have hne12 : gFin x₁ ≠ gFin x₂ := by
        simpa only [neqPairs, eqPairs, mem_compl, mem_filter, mem_univ, true_and] using hp
      rcases le_total #(fiberSet gFin (gFin x₁)) #(fiberSet gFin (gFin x₂)) with hle | hge
      · exact mem_union_left _ (mem_filter.mpr ⟨mem_univ _, hne12, hle⟩)
      · refine mem_union_right _ (mem_map.mpr ⟨(x₂, x₁), ?_, rfl⟩)
        exact mem_filter.mpr ⟨mem_univ _, hne12.symm, hge⟩
    have h1 := card_le_card hsub
    have h2 := card_union_le goodPairs (goodPairs.map swapEmb)
    have h3 : #(goodPairs.map swapEmb) = #goodPairs := card_map swapEmb
    omega
  have hcoll_eq : PMF.collisionProbability ((PMF.uniformOfFintype (BitString n)).map gFin) =
      (#eqPairs : ℝ) / ((2 ^ n : ℝ) * (2 ^ n : ℝ)) := by
    rw [PMF.collisionProbability_map]
    have hpt (a : BitString n) :
        ((PMF.uniformOfFintype (BitString n)) a).toReal = ((2 : ℝ) ^ n)⁻¹ := by
      simp only [PMF.uniformOfFintype_apply, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool,
        Nat.cast_pow, Nat.cast_ofNat, ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_ofNat]
    simp only [hpt]
    have hsum : (∑ a : BitString n, ∑ b : BitString n,
        if gFin a = gFin b then ((2 : ℝ) ^ n)⁻¹ * ((2 : ℝ) ^ n)⁻¹ else 0) =
        ∑ p : BitString n × BitString n,
          if gFin p.1 = gFin p.2 then ((2 : ℝ) ^ n)⁻¹ * ((2 : ℝ) ^ n)⁻¹ else 0 :=
      (Fintype.sum_prod_type fun p : BitString n × BitString n =>
        if gFin p.1 = gFin p.2 then ((2 : ℝ) ^ n)⁻¹ * ((2 : ℝ) ^ n)⁻¹ else 0).symm
    rw [hsum, ← sum_filter, sum_const, nsmul_eq_mul]
    change (#eqPairs : ℝ) * (((2 : ℝ) ^ n)⁻¹ * ((2 : ℝ) ^ n)⁻¹) = _
    ring
  have hpart_nat : #eqPairs + #neqPairs = 2 ^ n * 2 ^ n := by
    dsimp only [neqPairs]
    rw [card_add_card_compl, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin,
      Fintype.card_bool]
  have hpart_pairs : (#eqPairs : ℝ) + (#neqPairs : ℝ) = (2 ^ n : ℝ) * (2 ^ n : ℝ) := by
    exact_mod_cast hpart_nat
  rw [hcoll_eq]
  have hpos : (0 : ℝ) < (2 ^ n : ℝ) * (2 ^ n : ℝ) := by positivity
  have hneq_real : (#neqPairs : ℝ) ≤ 2 * (#goodPairs : ℝ) := by exact_mod_cast hneq_le_two_good
  rw [div_le_div_iff₀ (by norm_num) hpos]
  have h1 : (1 - (#eqPairs : ℝ) / ((2 ^ n : ℝ) * (2 ^ n : ℝ))) * ((2 ^ n : ℝ) * (2 ^ n : ℝ)) =
      (#neqPairs : ℝ) := by
    field_simp
    linarith
  nlinarith

/-- **`[HHRVW2020]`, Section 4.2, Claim 4.7 (pp. 21, 23–25)**: unconditional finite-`n` lower bound
on the entropy gap between `PMF.conditionalEntropy` of `rompelBaseHashFin gFin` and
`accessibleSetExpectation (rompelAccessibleInputSet gFin)`. -/
theorem rompelBase_accessibleInput_le_conditionalEntropy_sub {n m : ℕ}
    (gFin : BitString n → BitString m) :
    accessibleSetExpectation (rompelAccessibleInputSet gFin) ≤
      PMF.conditionalEntropy
        ((PMF.uniformOfFintype (RompelBaseInput n m)).map fun z =>
          (rompelBaseHashFin gFin z, z)) -
        (1 - PMF.collisionProbability ((PMF.uniformOfFintype (BitString n)).map gFin)) /
          (16 * (2 ^ rompelTruncWidth n : ℝ)) := by
  have hbase := conditionalEntropy_sub_accessibleSetExpectation_ge
    (rompelBaseHashFin gFin) (rompelAccessibleInputSet gFin)
    (self_mem_rompelAccessibleInputSet gFin) (rompelAccessibleInputSet_subset_fiber gFin)
  suffices hprob :
      (1 - PMF.collisionProbability ((PMF.uniformOfFintype (BitString n)).map gFin)) /
          (16 * (2 ^ rompelTruncWidth n : ℝ)) ≤
        ∑ z : RompelBaseInput n m, ((PMF.uniformOfFintype (RompelBaseInput n m)) z).toReal *
          ((#(fiberSet (rompelBaseHashFin gFin) (rompelBaseHashFin gFin z) \
              rompelAccessibleInputSet gFin z) : ℝ) /
            #(fiberSet (rompelBaseHashFin gFin) (rompelBaseHashFin gFin z))) by
    linarith
  let S := (Fin n → BitString m) × BitString n
  let R := BitString (rompelTruncWidth n)
  let goodPairs : Finset (BitString n × BitString n) :=
    univ.filter fun p => gFin p.1 ≠ gFin p.2 ∧
      #(fiberSet gFin (gFin p.1)) ≤ #(fiberSet gFin (gFin p.2))
  rw [rompelBase_escape_density_sum_eq gFin]
  calc
    (1 - PMF.collisionProbability ((PMF.uniformOfFintype (BitString n)).map gFin)) /
        (16 * (2 ^ rompelTruncWidth n : ℝ))
      = (((1 - PMF.collisionProbability
          ((PMF.uniformOfFintype (BitString n)).map gFin)) / 2)) *
          ((8 * (2 ^ rompelTruncWidth n : ℝ))⁻¹) := by ring
    _ ≤ ((#goodPairs : ℝ) / ((2 ^ n : ℝ) * (2 ^ n : ℝ))) *
          ((8 * (2 ^ rompelTruncWidth n : ℝ))⁻¹) :=
        mul_le_mul_of_nonneg_right (rompelBase_goodPairs_frac_ge gFin) (by positivity)
    _ = ∑ _p ∈ goodPairs,
          ((2 ^ n : ℝ)⁻¹ * (((2 : ℝ) ^ n)⁻¹ / (8 * (2 ^ rompelTruncWidth n : ℝ)))) := by
        rw [sum_const, nsmul_eq_mul]
        field_simp
    _ ≤ ∑ p ∈ goodPairs, ((2 ^ n : ℝ)⁻¹) *
          ∑ rBits : R, ((2 ^ rompelTruncWidth n : ℝ)⁻¹) *
            ∑ s : S, ((PMF.uniformOfFintype S) s).toReal *
              rompelSdiffWeight gFin p.1 p.2 s rBits := by
        refine sum_le_sum fun p hp => mul_le_mul_of_nonneg_left ?_ (by positivity)
        obtain ⟨hne, hfib_le⟩ := (mem_filter.mp hp).2
        exact rompelBase_goodPair_term_ge gFin hne hfib_le
    _ ≤ _ := sum_le_univ_sum_of_nonneg fun p => mul_nonneg (by positivity)
        (sum_nonneg fun rBits _ => mul_nonneg (by positivity)
          (sum_nonneg fun s _ => mul_nonneg ENNReal.toReal_nonneg
            (div_nonneg (by split_ifs <;> positivity) (Nat.cast_nonneg _))))

/-- Bit-string transport of `rompelBase_accessibleInput_le_conditionalEntropy_sub` (`[HHRVW2020]`,
Section 4.2, Claim 4.7, pp. 21, 23–25): when the output collision probability of `g` on `n`-bit
inputs is at most `1 / 2`, the entropy gap on `BitString (rompelBaseInLen n (outLen n))` is at least
`1 / (64 * (n + 1))`. -/
theorem rompelBase_accessible_le_conditionalEntropy_sub (g : List Bool → List Bool)
    (outLen : ℕ → ℕ) (n : ℕ)
    (hlen : ∀ w : List Bool, w.length = n → (g w).length = outLen n)
    (hcoll : PMF.collisionProbability ((Cslib.BitString.uniformList n).map g) ≤ 1 / 2) :
    accessibleSetExpectation (rompelAccessibleSet g outLen n) ≤
      PMF.conditionalEntropy
        ((PMF.uniformOfFintype (BitString (rompelBaseInLen n (outLen n)))).map fun b =>
          (wordToFinMap (rompelBaseInLen n (outLen n)) (rompelBaseOutLen n (outLen n))
            (rompelBaseEvalWord g outLen n) b, b)) -
        1 / (64 * (n + 1 : ℝ)) := by
  let m := outLen n
  let gFin : BitString n → BitString m := wordToFinMap n m g
  let eIn := rompelBaseInputEquiv n m
  let eOut := rompelBaseOutputEquiv n m
  -- Transport `accessibleSetExpectation` across `eIn`:
  have hacc : accessibleSetExpectation (rompelAccessibleSet g outLen n) =
      accessibleSetExpectation (rompelAccessibleInputSet gFin) := by
    rw [accessibleSetExpectation, accessibleSetExpectation, ← eIn.sum_comp]
    refine sum_congr rfl fun z _ => ?_
    have hunif : ((PMF.uniformOfFintype (BitString (rompelBaseInLen n m))) (eIn z)).toReal =
        ((PMF.uniformOfFintype (RompelBaseInput n m)) z).toReal := by
      simp [PMF.uniformOfFintype_apply, Fintype.card_congr eIn]
    have hcard_L : #(rompelAccessibleSet g outLen n (eIn z)) =
        #(rompelAccessibleInputSet gFin z) := by
      simp [rompelAccessibleSet, eIn, gFin, m]
    rw [hunif, hcard_L]
  -- Transport `conditionalEntropy` across `eOut × eIn`:
  have hcond :
      PMF.conditionalEntropy
        ((PMF.uniformOfFintype (BitString (rompelBaseInLen n m))).map fun b =>
          (wordToFinMap (rompelBaseInLen n m) (rompelBaseOutLen n m)
            (rompelBaseEvalWord g outLen n) b, b)) =
      PMF.conditionalEntropy
        ((PMF.uniformOfFintype (RompelBaseInput n m)).map fun z =>
          (rompelBaseHashFin gFin z, z)) := by
    have hjoint :
        ((PMF.uniformOfFintype (BitString (rompelBaseInLen n m))).map fun b =>
          (wordToFinMap (rompelBaseInLen n m) (rompelBaseOutLen n m)
            (rompelBaseEvalWord g outLen n) b, b)) =
        ((PMF.uniformOfFintype (RompelBaseInput n m)).map fun z =>
          (rompelBaseHashFin gFin z, z)).map (Equiv.prodCongr eOut eIn) := by
      dsimp only [eIn, eOut, gFin, m]
      rw [← PMF.uniformOfFintype_map_equiv (rompelBaseInputEquiv n (outLen n)),
        PMF.map_comp, PMF.map_comp]
      refine congrArg (PMF.uniformOfFintype _).map (funext fun z => ?_)
      simp [wordToFinMap_rompelBaseEvalWord]
    have hmarg :
        (((PMF.uniformOfFintype (BitString (rompelBaseInLen n m))).map fun b =>
          (wordToFinMap (rompelBaseInLen n m) (rompelBaseOutLen n m)
            (rompelBaseEvalWord g outLen n) b, b)).map Prod.fst) =
        (((PMF.uniformOfFintype (RompelBaseInput n m)).map fun z =>
          (rompelBaseHashFin gFin z, z)).map Prod.fst).map eOut := by
      simp only [hjoint, PMF.map_comp]
      rfl
    rw [PMF.conditionalEntropy, PMF.conditionalEntropy, hmarg, hjoint,
      PMF.entropy_map_of_injective _ (Equiv.prodCongr eOut eIn).injective,
      PMF.entropy_map_of_injective _ eOut.injective]
  -- Relate word-level and finite collision probabilities:
  have hcoll_fin : PMF.collisionProbability ((PMF.uniformOfFintype (BitString n)).map gFin) ≤
      1 / 2 := by
    have hmap : (Cslib.BitString.uniformList n).map g =
        ((PMF.uniformOfFintype (BitString n)).map gFin).map List.ofFn := by
      rw [Cslib.BitString.uniformList, PMF.map_comp, PMF.map_comp]
      refine congrArg (PMF.uniformOfFintype _).map (funext fun x => ?_)
      simpa only [Function.comp_def, gFin, wordToFinMap] using
        (Cslib.BitString.ofFn_ofList (hlen (List.ofFn x) List.length_ofFn)).symm
    rwa [hmap, PMF.collisionProbability_map_of_injective _ _ List.ofFn_injective] at hcoll
  -- Combine with `rompelBase_accessibleInput_le_conditionalEntropy_sub` and
  -- `two_pow_rompelTruncWidth_le`:
  have hgap := rompelBase_accessibleInput_le_conditionalEntropy_sub gFin
  have htrunc_le : (2 ^ rompelTruncWidth n : ℝ) ≤ 2 * (n + 1 : ℝ) := by
    exact_mod_cast two_pow_rompelTruncWidth_le n
  have hfrac : 1 / (64 * (n + 1 : ℝ)) ≤
      (1 - PMF.collisionProbability ((PMF.uniformOfFintype (BitString n)).map gFin)) /
        (16 * (2 ^ rompelTruncWidth n : ℝ)) := by
    calc
      1 / (64 * (n + 1 : ℝ)) = (1 / 2) / (16 * (2 * (n + 1 : ℝ))) := by field_simp; ring
      _ ≤ (1 / 2) / (16 * (2 ^ rompelTruncWidth n : ℝ)) := by
        apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
        linarith
      _ ≤ (1 - PMF.collisionProbability ((PMF.uniformOfFintype (BitString n)).map gFin)) /
            (16 * (2 ^ rompelTruncWidth n : ℝ)) := by
        apply div_le_div_of_nonneg_right (by linarith) (by positivity)
  rw [hacc, hcond]
  linarith

/-! ### Constant-threshold adaptation of Theorem 4.5 -/

/-- **Constant-threshold adaptation of `[HHRVW2020]`, Section 4.2, Theorem 4.5 (p. 21)**: every
uniform `OneWay` function yields a uniform polynomial-time `InaccessibleEntropyFamily` with gap
denominator `denom n = 64 * (n + 1)`.

Whereas `[HHRVW2020]`, Theorem 4.5 (p. 21) uses light-image threshold $2^{n - i} / n^c$ to achieve
gap $d \log n / n$ for every constant $d > 0$ under Definition 3.9 (p. 15), this adaptation uses a
single adversary-independent accessible-set family (`rompelAccessibleSet`), dyadic
`(Nat.log 2 n + 1)`-bit saturating prefix encoding, and the constant threshold
$2^{n - \min(r, n)} / 4$ (`rompelLightImages`), yielding the smaller inverse-linear gap
$1 / (64 (n + 1))$ against uniform strict-PPT adversaries. -/
theorem OneWay.exists_inaccessibleEntropyFamily {f : List Bool → List Bool} (hf : OneWay f) :
    Nonempty InaccessibleEntropyFamily := by
  obtain ⟨g, outLen, hg, hlen, houtLen⟩ := hf.exists_fixedOutputLength
  have hcoll_ev := (hg.output_collision_negligible).eventually_le_inv_polynomial
    (p := fun _ => 2) (by fun_prop) (fun _ => by omega)
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp hcoll_ev
  have hid := ComputableInPolyTime.id' (encIn := encUnary)
  have hsLen := computableInPolyTime_rompelSeedWidth hid houtLen
  have hinLen : ComputableInPolyTime (fun n => rompelBaseInLen n (outLen n)) encUnary encUnary :=
    ComputableInPolyTime.unary_add' (ComputableInPolyTime.unary_add' hid hsLen)
      computableInPolyTime_rompelTruncWidth
  have houtLen₀ :
      ComputableInPolyTime (fun n => rompelBaseOutLen n (outLen n)) encUnary encUnary :=
    ComputableInPolyTime.unary_add'
      (ComputableInPolyTime.unary_add' hsLen computableInPolyTime_rompelTruncWidth) hid
  refine ⟨{
    inLen := fun n => rompelBaseInLen n (outLen n)
    outLen := fun n => rompelBaseOutLen n (outLen n)
    denom := fun n => 64 * (n + 1)
    evalWord := rompelBaseEvalWord g outLen
    accSet := rompelAccessibleSet g outLen
    polyTime_inLen := hinLen
    polyTime_outLen := houtLen₀
    polyTime_denom := by fun_prop
    denom_pos := fun n => by omega
    polyTime_evalWord := computableInPolyTime_rompelBaseEvalWord hg.polyTime houtLen
    length_evalWord := fun n z _ => length_rompelBaseEvalWord g outLen n z
    self_mem_accSet := self_mem_rompelAccessibleSet g outLen
    accSet_subset_fiber := rompelAccessibleSet_subset_fiber g outLen
    eventually_entropy_gap := ⟨N₀, fun n hn => by
      have hc_nn := hN₀ n hn
      have hc : PMF.collisionProbability ((Cslib.BitString.uniformList n).map g) ≤ 1 / 2 := by
        have hnonneg := PMF.collisionProbability_nonneg ((Cslib.BitString.uniformList n).map g)
        rw [Real.coe_toNNReal _ hnonneg] at hc_nn
        norm_num at hc_nn ⊢
        exact hc_nn
      simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] using
        rompelBase_accessible_le_conditionalEntropy_sub g outLen n (fun w hw => hw ▸ hlen w) hc⟩
    escape_negligible := fun A hA => by
      have hinv_ppt := isPPT_rompelBaseInverter hg.polyTime houtLen hA
      have hinv_neg := (hg.inversion_negligible _ hinv_ppt).const_mul 4
      refine negligible_of_le hinv_neg fun n => ?_
      exact_mod_cast rompelBase_escape_le_four_mul_inversion g outLen A n
        (fun w hw => hw ▸ hlen w)
  }⟩

end Cslib.Crypto
