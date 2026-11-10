/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Probabilistic.LinearHash
public import CslibFrontier.Crypto.Computational.InaccessibleEntropy.Basic
public import CslibFrontier.Probability.BitString.AffineHash.ThreeWise
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.Map
import CslibFrontier.Probability.PMF.ToReal
import CslibFrontier.Probability.PMF.Uniform
import CslibFrontier.Probability.Uniform
import CslibFrontier.Tactic.PPT

/-!
# Accessible-entropy reduction and 1-bit shrinking output hashing

Following `[HHRVW2020]`, Sections 5.1.2–5.1.3 (Lemmas 5.4 and 5.5, pp. 27–29), this module
transforms a function $F_1 : \{0, 1\}^{n_1} \to \{0, 1\}^{m_1}$ whose real sample entropy exceeds
$K_{\min}$ except on a small bad set, and whose accessible set $L_1(z)$ has $\log_2 |L_1(z)| <
A_{\max}$ except on a small bad set, into a **strictly $1$-bit shrinking** function
$F_3^{(j)} : \{0, 1\}^{N_3} \to \{0, 1\}^{N_3 - 1}$ ($1 \le n_1$) that is collision-resistant on
random inputs whenever $A_{\max} \ll j \ll K_{\min}$:

1. **Input-hash entropy reduction $F_2^{(j)}$** (`inputHashFin`, `inputHashEvalWord`, Lemma 5.4,
   pp. 27–28): using a fixed-width $n_1 \times n_1$ Boolean matrix `inRows` so that the input width
   `inputHashInLen n₁ = n₁ + n₁ * n₁` and output width `inputHashOutLen n₁ m₁ = m₁ + n₁ * n₁ + n₁`
   are independent of the truncation parameter $j$, define
   $$F_2^{(j)}(z, \mathrm{inRows}) =
     \bigl(F_1(z),\; \mathrm{inRows},\;
       \mathrm{zeroPadPrefix}\;n_1\;j\;(\mathrm{hash}\;\mathrm{inRows}\;z)\bigr).$$
   By `LinearHash.isTwoUniversal_prefix` and `IsTwoUniversal.collision_with_set_le`, any input $z$
   has probability at most $|L_1(z)| / 2^{\min(j, n_1)}$ over `inRows` of colliding under
   $F_2^{(j)}$ with a distinct $z' \in L_1(z)$ (`inputHashFin_accessible_collision_le`).
   Meanwhile, partitioning inputs around `{z | realSampleEntropy f₁ z ≤ K_min}` bounds the total
   image size $|F_2^{(j)}(\{0, 1\}^{n_2})|$ directly (`card_image_inputHashFin_le`, Equation (5.6),
   p. 29).
2. **Output-hash 1-bit shrinkage $F_3^{(j)}$** (`shrunkHashFin`, `shrunkHashEvalWord`, Lemma 5.5,
   Equations (5.6)–(5.7), p. 29): hashing $F_2^{(j)}(w)$ to `outHashLen n₁ = inputHashInLen n₁ - 1`
   bits via a public Boolean matrix `outRows` yields
   `shrunkHashInLen n₁ m₁ = shrunkHashOutLen n₁ m₁ + 1` whenever $1 \le n_1$
   (`shrunkHashOutLen_add_one`), while `LinearHash.isTwoUniversal` bounds false-positive output-hash
   collisions (`shrunkHashFin_false_positive_le`, Equation (5.7), p. 29).
3. **Random-input collision-to-escape reduction** (`randomCollisionGame`,
   `shrunkHashEscapeInverter`, `isPPT_shrunkHashEscapeInverter`, `shrunkHash_randomCollision_le`):
   padding a challenge $z$ with uniform `(inRows, outRows)` — via a uniform strict-PPT reduction
   independent of $j$ — reduces random-input collisions of $F_3^{(j)}$ to escaping $L_1$ plus the
   two concentration tails and two universal-hash error terms.

## Main definitions

* `Cslib.Crypto.inputHashInLen`, `Cslib.Crypto.inputHashOutLen`, `Cslib.Crypto.outHashLen`,
  `Cslib.Crypto.shrunkHashInLen`, `Cslib.Crypto.shrunkHashOutLen`: bit-width schedule of $F_2^{(j)}$
  and $F_3^{(j)}$.
* `Cslib.Crypto.InputHashedInput`, `Cslib.Crypto.InputHashedOutput`,
  `Cslib.Crypto.ShrunkHashInput`, `Cslib.Crypto.ShrunkHashOutput`: structured finite inputs/outputs
  with bit-string equivalences.
* `Cslib.Crypto.inputHashFin`, `Cslib.Crypto.inputHashEvalWord`: finite and word-level evaluators
  of $F_2^{(j)}$.
* `Cslib.Crypto.shrunkHashFin`, `Cslib.Crypto.shrunkHashEvalWord`: finite and word-level evaluators
  of $F_3^{(j)}$.
* `Cslib.Crypto.randomCollisionGame`: security experiment for collision resistance on random inputs.
* `Cslib.Crypto.shrunkHashEscapeInverter`: uniform strict-PPT reduction from $F_3^{(j)}$ collisions
  to $F_1$ accessible escape.

## Main results

* `Cslib.Crypto.inputHashFin_accessible_collision_le`: Lemma 5.4 accessible-collision bound.
* `Cslib.Crypto.card_image_inputHashFin_le`: Equation (5.6) image-cardinality bound for $F_2^{(j)}$.
* `Cslib.Crypto.shrunkHashOutLen_add_one`: exact $1$-bit shrinkage when $1 \le n_1$.
* `Cslib.Crypto.shrunkHashFin_false_positive_le`: Equation (5.7) false-positive bound for
  $F_3^{(j)}$.
* `Cslib.Crypto.computableInPolyTime_shrunkHashEvalWord`: plain polynomial-time certificate for
  `shrunkHashEvalWord`.
* `Cslib.Crypto.isPPT_shrunkHashEscapeInverter`: plain uniform strict-PPT certificate for
  `shrunkHashEscapeInverter`.
* `Cslib.Crypto.shrunkHash_randomCollision_le`: combined concrete random-input collision bound for
  Lemmas 5.4 and 5.5.

## References

* [I. Haitner, T. Holenstein, O. Reingold, S. Vadhan, H. Wee, *Inaccessible Entropy II: IE
  Functions and Universal One-Way Hashing*, Sections 5.1.2–5.1.3, Lemmas 5.4–5.5 and Equations
  (5.6)–(5.7), pp. 27–29][HHRVW2020]
-/

public section

namespace Cslib.Crypto

open Cslib.Probability Cslib.BitString.LinearHash Finset Turing.MultiTapeTM
open scoped BigOperators ENNReal NNReal

/-! ### Bit-width schedule and structured views for $F_2^{(j)}$ and $F_3^{(j)}$ -/

/-- Input bit width $n_2 = n_1 + n_1^2$ of $F_2^{(j)}$, independent of $j$. -/
@[expose] def inputHashInLen (n₁ : ℕ) : ℕ := n₁ + n₁ * n₁

/-- Output bit width $m_2 = m_1 + n_1^2 + n_1$ of $F_2^{(j)}$, independent of $j$. -/
@[expose] def inputHashOutLen (n₁ m₁ : ℕ) : ℕ := m₁ + n₁ * n₁ + n₁

/-- Digest bit width $n_2 - 1$ of the output hash in $F_3^{(j)}$. -/
@[expose] def outHashLen (n₁ : ℕ) : ℕ := inputHashInLen n₁ - 1

/-- Input bit width $N_3 = n_2 + (n_2 - 1) m_2$ of $F_3^{(j)}$. -/
@[expose] def shrunkHashInLen (n₁ m₁ : ℕ) : ℕ :=
  inputHashInLen n₁ + outHashLen n₁ * inputHashOutLen n₁ m₁

/-- Output bit width $M_3 = (n_2 - 1) m_2 + (n_2 - 1)$ of $F_3^{(j)}$. -/
@[expose] def shrunkHashOutLen (n₁ m₁ : ℕ) : ℕ :=
  outHashLen n₁ * inputHashOutLen n₁ m₁ + outHashLen n₁

/-- When $1 \le n_1$, $F_3^{(j)}$ shrinks its input by **strictly one bit**. -/
theorem shrunkHashOutLen_add_one {n₁ : ℕ} (hn₁ : 1 ≤ n₁) (m₁ : ℕ) :
    shrunkHashOutLen n₁ m₁ + 1 = shrunkHashInLen n₁ m₁ := by
  simp only [shrunkHashOutLen, shrunkHashInLen, outHashLen, inputHashInLen]
  omega

/-- Structured input `(base, inRows)` to $F_2^{(j)}$ (`[HHRVW2020]`, Section 5.1.2, Lemma 5.4,
pp. 27–28). -/
structure InputHashedInput (n₁ : ℕ) where
  /-- Base $n_1$-bit input $z$ to $F_1$. -/
  base : BitString n₁
  /-- Public $n_1 \times n_1$ Boolean matrix rows of the two-universal input hash. -/
  inRows : Fin n₁ → BitString n₁

instance (n₁ : ℕ) : Nonempty (InputHashedInput n₁) := ⟨⟨0, 0⟩⟩

/-- Pack an `InputHashedInput n₁` into a word of length `inputHashInLen n₁`. -/
@[expose] def InputHashedInput.packWord {n₁ : ℕ} (w : InputHashedInput n₁) : List Bool :=
  List.ofFn w.base ++ List.ofFn (Cslib.BitString.blocksEquiv.symm w.inRows)

@[simp] theorem InputHashedInput.length_packWord {n₁ : ℕ} (w : InputHashedInput n₁) :
    w.packWord.length = inputHashInLen n₁ := by
  simp [InputHashedInput.packWord, inputHashInLen]

/-- Unpack a word into an `InputHashedInput n₁`. -/
@[expose] def InputHashedInput.unpackWord (n₁ : ℕ) (u : List Bool) : InputHashedInput n₁ where
  base := Cslib.BitString.ofList n₁ (u.take n₁)
  inRows := Cslib.BitString.blocksEquiv
    (Cslib.BitString.ofList (n₁ * n₁) ((u.drop n₁).take (n₁ * n₁)))

@[simp] theorem InputHashedInput.unpackWord_packWord {n₁ : ℕ} (w : InputHashedInput n₁) :
    InputHashedInput.unpackWord n₁ w.packWord = w := by
  have hb : (List.ofFn w.base).length = n₁ := List.length_ofFn
  have hr : (List.ofFn (Cslib.BitString.blocksEquiv.symm w.inRows)).length = n₁ * n₁ :=
    List.length_ofFn
  cases w with | mk z rows =>
  simp only [InputHashedInput.packWord, InputHashedInput.unpackWord,
    List.take_left' hb, List.drop_left' hb, List.take_of_length_le hr.le,
    Cslib.BitString.ofList_ofFn, Equiv.apply_symm_apply]

theorem InputHashedInput.packWord_unpackWord {n₁ : ℕ} {u : List Bool}
    (hu : u.length = inputHashInLen n₁) :
    (InputHashedInput.unpackWord n₁ u).packWord = u := by
  have hb : (u.take n₁).length = n₁ := by simp [hu, inputHashInLen]
  have hd : (u.drop n₁).length = n₁ * n₁ := by simp [hu, inputHashInLen]
  simp only [InputHashedInput.unpackWord, InputHashedInput.packWord,
    List.take_of_length_le hd.le, Equiv.symm_apply_apply,
    Cslib.BitString.ofFn_ofList hb, Cslib.BitString.ofFn_ofList hd, List.take_append_drop]

/-- Exact bit-string equivalence between `InputHashedInput n₁` and
`BitString (inputHashInLen n₁)`. -/
@[expose] def inputHashedInputEquiv (n₁ : ℕ) :
    InputHashedInput n₁ ≃ BitString (inputHashInLen n₁) where
  toFun w := Cslib.BitString.ofList (inputHashInLen n₁) w.packWord
  invFun b := InputHashedInput.unpackWord n₁ (List.ofFn b)
  left_inv w := by
    dsimp only
    rw [Cslib.BitString.ofFn_ofList w.length_packWord, InputHashedInput.unpackWord_packWord]
  right_inv b := by
    dsimp only
    rw [InputHashedInput.packWord_unpackWord List.length_ofFn, Cslib.BitString.ofList_ofFn]

instance (n₁ : ℕ) : Fintype (InputHashedInput n₁) :=
  Fintype.ofEquiv (BitString (inputHashInLen n₁)) (inputHashedInputEquiv n₁).symm

/-- Structured output `(baseOut, inRows, inDigest)` of $F_2^{(j)}$ (`[HHRVW2020]`, Section 5.1.2,
Lemma 5.4, pp. 27–28). -/
structure InputHashedOutput (n₁ m₁ : ℕ) where
  /-- Base output $F_1(z) \in \{0, 1\}^{m_1}$. -/
  baseOut : BitString m₁
  /-- Public $n_1 \times n_1$ Boolean matrix rows of the input hash. -/
  inRows : Fin n₁ → BitString n₁
  /-- Zero-padded $\min(j, n_1)$-bit prefix of $\mathrm{hash}\;\mathrm{inRows}\;z$. -/
  inDigest : BitString n₁

/-- Pack an `InputHashedOutput n₁ m₁` into a word of length `inputHashOutLen n₁ m₁`. -/
@[expose] def InputHashedOutput.packWord {n₁ m₁ : ℕ} (y : InputHashedOutput n₁ m₁) : List Bool :=
  List.ofFn y.baseOut ++ List.ofFn (Cslib.BitString.blocksEquiv.symm y.inRows) ++
    List.ofFn y.inDigest

@[simp] theorem InputHashedOutput.length_packWord {n₁ m₁ : ℕ} (y : InputHashedOutput n₁ m₁) :
    y.packWord.length = inputHashOutLen n₁ m₁ := by
  simp only [InputHashedOutput.packWord, inputHashOutLen, List.length_append, List.length_ofFn]

/-- Unpack a word into an `InputHashedOutput n₁ m₁`. -/
@[expose] def InputHashedOutput.unpackWord (n₁ m₁ : ℕ) (u : List Bool) :
    InputHashedOutput n₁ m₁ :=
  let rest := u.drop m₁
  { baseOut := Cslib.BitString.ofList m₁ (u.take m₁)
    inRows := Cslib.BitString.blocksEquiv
      (Cslib.BitString.ofList (n₁ * n₁) (rest.take (n₁ * n₁)))
    inDigest := Cslib.BitString.ofList n₁ (rest.drop (n₁ * n₁)) }

@[simp] theorem InputHashedOutput.unpackWord_packWord {n₁ m₁ : ℕ} (y : InputHashedOutput n₁ m₁) :
    InputHashedOutput.unpackWord n₁ m₁ y.packWord = y := by
  have hy : (List.ofFn y.baseOut).length = m₁ := List.length_ofFn
  have hr : (List.ofFn (Cslib.BitString.blocksEquiv.symm y.inRows)).length = n₁ * n₁ :=
    List.length_ofFn
  cases y with | mk bOut rows dig =>
  simp only [InputHashedOutput.packWord, InputHashedOutput.unpackWord, List.append_assoc,
    List.take_left' hy, List.drop_left' hy, List.take_left' hr, List.drop_left' hr,
    Cslib.BitString.ofList_ofFn, Equiv.apply_symm_apply]

theorem InputHashedOutput.packWord_unpackWord {n₁ m₁ : ℕ} {u : List Bool}
    (hu : u.length = inputHashOutLen n₁ m₁) :
    (InputHashedOutput.unpackWord n₁ m₁ u).packWord = u := by
  have hb : (u.take m₁).length = m₁ := by simp [hu, inputHashOutLen]; omega
  have hr : ((u.drop m₁).take (n₁ * n₁)).length = n₁ * n₁ := by simp [hu, inputHashOutLen]; omega
  have hd : ((u.drop m₁).drop (n₁ * n₁)).length = n₁ := by simp [hu, inputHashOutLen]
  simp only [InputHashedOutput.unpackWord, InputHashedOutput.packWord, Equiv.symm_apply_apply,
    Cslib.BitString.ofFn_ofList hb, Cslib.BitString.ofFn_ofList hr, Cslib.BitString.ofFn_ofList hd,
    List.append_assoc, List.take_append_drop]

/-- Exact bit-string equivalence between `InputHashedOutput n₁ m₁` and
`BitString (inputHashOutLen n₁ m₁)`. -/
@[expose] def inputHashedOutputEquiv (n₁ m₁ : ℕ) :
    InputHashedOutput n₁ m₁ ≃ BitString (inputHashOutLen n₁ m₁) where
  toFun y := Cslib.BitString.ofList (inputHashOutLen n₁ m₁) y.packWord
  invFun b := InputHashedOutput.unpackWord n₁ m₁ (List.ofFn b)
  left_inv y := by
    dsimp only
    rw [Cslib.BitString.ofFn_ofList y.length_packWord, InputHashedOutput.unpackWord_packWord]
  right_inv b := by
    dsimp only
    rw [InputHashedOutput.packWord_unpackWord List.length_ofFn, Cslib.BitString.ofList_ofFn]

/-- Structured input `(inner, outRows)` to $F_3^{(j)}$ (`[HHRVW2020]`, Section 5.1.3, Lemma 5.5,
p. 29). -/
structure ShrunkHashInput (n₁ m₁ : ℕ) where
  /-- Input $(z, \mathrm{inRows})$ to $F_2^{(j)}$. -/
  inner : InputHashedInput n₁
  /-- Public $(n_2 - 1) \times m_2$ Boolean matrix rows of the output hash. -/
  outRows : Fin (outHashLen n₁) → BitString (inputHashOutLen n₁ m₁)

instance (n₁ m₁ : ℕ) : Nonempty (ShrunkHashInput n₁ m₁) := ⟨⟨⟨0, 0⟩, 0⟩⟩

/-- Pack a `ShrunkHashInput n₁ m₁` into a word of length `shrunkHashInLen n₁ m₁`. -/
@[expose] def ShrunkHashInput.packWord {n₁ m₁ : ℕ} (v : ShrunkHashInput n₁ m₁) : List Bool :=
  v.inner.packWord ++ List.ofFn (Cslib.BitString.blocksEquiv.symm v.outRows)

@[simp] theorem ShrunkHashInput.length_packWord {n₁ m₁ : ℕ} (v : ShrunkHashInput n₁ m₁) :
    v.packWord.length = shrunkHashInLen n₁ m₁ := by
  simp [ShrunkHashInput.packWord, shrunkHashInLen]

/-- Unpack a word into a `ShrunkHashInput n₁ m₁`. -/
@[expose] def ShrunkHashInput.unpackWord (n₁ m₁ : ℕ) (raw : List Bool) : ShrunkHashInput n₁ m₁ :=
  let inLen₂ := inputHashInLen n₁
  let outSeedLen := outHashLen n₁ * inputHashOutLen n₁ m₁
  { inner := InputHashedInput.unpackWord n₁ (raw.take inLen₂)
    outRows := Cslib.BitString.blocksEquiv
      (Cslib.BitString.ofList outSeedLen ((raw.drop inLen₂).take outSeedLen)) }

@[simp] theorem ShrunkHashInput.unpackWord_packWord {n₁ m₁ : ℕ} (v : ShrunkHashInput n₁ m₁) :
    ShrunkHashInput.unpackWord n₁ m₁ v.packWord = v := by
  have hi : v.inner.packWord.length = inputHashInLen n₁ := v.inner.length_packWord
  have ho : (List.ofFn (Cslib.BitString.blocksEquiv.symm v.outRows)).length =
      outHashLen n₁ * inputHashOutLen n₁ m₁ := List.length_ofFn
  cases v with | mk inn oRows =>
  simp only [ShrunkHashInput.packWord, ShrunkHashInput.unpackWord,
    List.take_left' hi, List.drop_left' hi, List.take_of_length_le ho.le,
    InputHashedInput.unpackWord_packWord, Cslib.BitString.ofList_ofFn, Equiv.apply_symm_apply]

theorem ShrunkHashInput.packWord_unpackWord {n₁ m₁ : ℕ} {raw : List Bool}
    (hraw : raw.length = shrunkHashInLen n₁ m₁) :
    (ShrunkHashInput.unpackWord n₁ m₁ raw).packWord = raw := by
  have hi : (raw.take (inputHashInLen n₁)).length = inputHashInLen n₁ := by
    simp [hraw, shrunkHashInLen]
  have hd : (raw.drop (inputHashInLen n₁)).length = outHashLen n₁ * inputHashOutLen n₁ m₁ := by
    simp [hraw, shrunkHashInLen]
  simp only [ShrunkHashInput.unpackWord, ShrunkHashInput.packWord,
    InputHashedInput.packWord_unpackWord hi, List.take_of_length_le hd.le,
    Equiv.symm_apply_apply, Cslib.BitString.ofFn_ofList hd, List.take_append_drop]

/-- Structured output `(outRows, outDigest)` of $F_3^{(j)}$ (`[HHRVW2020]`, Section 5.1.3,
Lemma 5.5, p. 29). -/
structure ShrunkHashOutput (n₁ m₁ : ℕ) where
  /-- Public $(n_2 - 1) \times m_2$ Boolean matrix rows of the output hash. -/
  outRows : Fin (outHashLen n₁) → BitString (inputHashOutLen n₁ m₁)
  /-- $(n_2 - 1)$-bit two-universal digest of $F_2^{(j)}(\mathrm{inner})$. -/
  outDigest : BitString (outHashLen n₁)

/-- Pack a `ShrunkHashOutput n₁ m₁` into a word of length `shrunkHashOutLen n₁ m₁`. -/
@[expose] def ShrunkHashOutput.packWord {n₁ m₁ : ℕ} (y : ShrunkHashOutput n₁ m₁) : List Bool :=
  List.ofFn (Cslib.BitString.blocksEquiv.symm y.outRows) ++ List.ofFn y.outDigest

@[simp] theorem ShrunkHashOutput.length_packWord {n₁ m₁ : ℕ} (y : ShrunkHashOutput n₁ m₁) :
    y.packWord.length = shrunkHashOutLen n₁ m₁ := by
  simp [ShrunkHashOutput.packWord, shrunkHashOutLen]

/-- Unpack a word into a `ShrunkHashOutput n₁ m₁`. -/
@[expose] def ShrunkHashOutput.unpackWord (n₁ m₁ : ℕ) (u : List Bool) : ShrunkHashOutput n₁ m₁ :=
  let outSeedLen := outHashLen n₁ * inputHashOutLen n₁ m₁
  { outRows := Cslib.BitString.blocksEquiv
      (Cslib.BitString.ofList outSeedLen (u.take outSeedLen))
    outDigest := Cslib.BitString.ofList (outHashLen n₁) (u.drop outSeedLen) }

@[simp] theorem ShrunkHashOutput.unpackWord_packWord {n₁ m₁ : ℕ} (y : ShrunkHashOutput n₁ m₁) :
    ShrunkHashOutput.unpackWord n₁ m₁ y.packWord = y := by
  have ho : (List.ofFn (Cslib.BitString.blocksEquiv.symm y.outRows)).length =
      outHashLen n₁ * inputHashOutLen n₁ m₁ := List.length_ofFn
  cases y with | mk oRows oDig =>
  simp only [ShrunkHashOutput.packWord, ShrunkHashOutput.unpackWord,
    List.take_left' ho, List.drop_left' ho, Cslib.BitString.ofList_ofFn, Equiv.apply_symm_apply]

/-! ### Step 2: Input-hash entropy reduction $F_2^{(j)}$ (Lemma 5.4 and Equation (5.6)) -/

/-- Finite evaluator $F_2^{(j)}(z, \mathrm{inRows}) = (F_1(z), \mathrm{inRows},
\mathrm{zeroPadPrefix}\;n_1\;j\;(\mathrm{hash}\;\mathrm{inRows}\;z))$ (`[HHRVW2020]`, Section 5.1.2,
Lemma 5.4, pp. 27–28). -/
@[expose] def inputHashFin {n₁ m₁ : ℕ} (f₁ : BitString n₁ → BitString m₁) (j : ℕ)
    (w : InputHashedInput n₁) : InputHashedOutput n₁ m₁ where
  baseOut := f₁ w.base
  inRows := w.inRows
  inDigest := zeroPadPrefix n₁ j (Cslib.BitString.LinearHash.hash w.inRows w.base)

open Classical in
/-- If an event on hash seeds forces a collision of `x` with another candidate, a two-universal
family bounds its probability by `|candidates| / |Output|`. -/
private theorem sum_ite_toReal_le_card_div_of_imp {Seed X Y : Type} [Fintype Seed] [Fintype Y]
    {seed : PMF Seed} {hash : Seed → X → Y} (hhash : IsTwoUniversal seed hash)
    (cand : Finset X) (x : X) {P : Seed → Prop} {_ : DecidablePred P}
    (hP : ∀ s, P s → ∃ y ∈ cand, y ≠ x ∧ hash s y = hash s x) :
    (∑ s, if P s then (seed s).toReal else 0) ≤ (#cand : ℝ) / Fintype.card Y := by
  calc (∑ s, if P s then (seed s).toReal else 0)
      ≤ ∑ s, if ∃ y ∈ cand, y ≠ x ∧ hash s y = hash s x then (seed s).toReal else 0 :=
        sum_le_sum fun s _ => by
          split_ifs with h₁ h₂
          · exact le_rfl
          · exact absurd (hP s h₁) h₂
          · exact ENNReal.toReal_nonneg
          · exact le_rfl
    _ ≤ ((cand.erase x).card : ℝ) / Fintype.card Y := hhash.collision_with_set_le cand x
    _ ≤ (#cand : ℝ) / Fintype.card Y := by
      gcongr
      exact erase_subset _ _

open Classical in
/-- **`[HHRVW2020]`, Section 5.1.2, Lemma 5.4(ii) (p. 28)**: by two-universality of matrix prefixes
(`LinearHash.isTwoUniversal_prefix`), the probability over `inRows` that some distinct
$z' \in L$ collides with $z$ under `inputHashFin f₁ j` is at most $|L| / 2^{\min(j, n_1)}$. -/
theorem inputHashFin_accessible_collision_le {n₁ m₁ : ℕ} (f₁ : BitString n₁ → BitString m₁)
    (j : ℕ) (L : Finset (BitString n₁)) (z : BitString n₁) :
    (∑ rows : Fin n₁ → BitString n₁,
        if ∃ z' ∈ L, z' ≠ z ∧ inputHashFin f₁ j ⟨z', rows⟩ = inputHashFin f₁ j ⟨z, rows⟩ then
          ((PMF.uniformOfFintype (Fin n₁ → BitString n₁)) rows).toReal
        else 0) ≤
      (#L : ℝ) / (2 : ℝ) ^ (min j n₁) := by
  have hcard : (Fintype.card (BitString (min j n₁)) : ℝ) = (2 : ℝ) ^ (min j n₁) := by
    simp [BitString]
  rw [← hcard]
  exact sum_ite_toReal_le_card_div_of_imp
    (Cslib.BitString.LinearHash.isTwoUniversal_prefix (n := n₁) (Nat.min_le_right j n₁)) L z
    fun rows h => by
      obtain ⟨z', hz', hne, heq⟩ := h
      have hdig := congrArg InputHashedOutput.inDigest heq
      dsimp only [inputHashFin] at hdig
      exact ⟨z', hz', hne, (zeroPadPrefix_eq_iff_prefixProj_eq _ _).mp hdig⟩

private def unpadPrefix (k r : ℕ) (p : BitString (min r k)) : BitString k :=
  fun i => if h : i.val < min r k then p ⟨i.val, h⟩ else false

private theorem zeroPadPrefix_eq_unpadPrefix (k r : ℕ) (v : BitString k) :
    zeroPadPrefix k r v = unpadPrefix k r (prefixProj k r v) := by
  funext i
  by_cases hi : i.val < min r k
  · have hir : i.val < r := lt_of_lt_of_le hi (Nat.min_le_left r k)
    simp only [zeroPadPrefix, hir, ↓reduceIte, unpadPrefix, hi, ↓reduceDIte, prefixProj,
      AddMonoidHom.coe_mk, ZeroHom.coe_mk, Function.comp_apply, Fin.castLE_mk]
  · have hir : ¬ i.val < r := fun h => hi (Nat.lt_min.mpr ⟨h, i.isLt⟩)
    simp only [zeroPadPrefix, hir, ↓reduceIte, unpadPrefix, hi, ↓reduceDIte]

open Classical in
/-- **`[HHRVW2020]`, Section 5.1.3, Lemma 5.5, Equation (5.6) (p. 29)**: partitioning inputs around
`{z | realSampleEntropy f₁ z ≤ K}` bounds the image cardinality of `inputHashFin f₁ j` by
$(\Pr[H_z \le K] + 2^{\min(j, n_1) - K}) \cdot 2^{n_2}$. -/
theorem card_image_inputHashFin_le {n₁ m₁ : ℕ} (f₁ : BitString n₁ → BitString m₁)
    (j : ℕ) (K : ℝ) :
    (#(univ.image (inputHashFin f₁ j)) : ℝ) ≤
      (((PMF.uniformOfFintype (BitString n₁)).toOuterMeasure
          {z | realSampleEntropy f₁ z ≤ K}).toReal +
        (2 : ℝ) ^ ((min j n₁ : ℝ) - K)) * (2 : ℝ) ^ (inputHashInLen n₁) := by
  classical
  let badInputs : Finset (BitString n₁) := univ.filter fun z => realSampleEntropy f₁ z ≤ K
  let goodInputs : Finset (BitString n₁) := univ.filter fun z => ¬ realSampleEntropy f₁ z ≤ K
  let badPairs : Finset (InputHashedInput n₁) := univ.filter fun w => w.base ∈ badInputs
  let goodPairs : Finset (InputHashedInput n₁) := univ.filter fun w => w.base ∈ goodInputs
  let goodImages : Finset (BitString m₁) := goodInputs.image f₁
  -- Bound `#badPairs = #badInputs * 2^(n₁ * n₁)`:
  have hcard_rows : Fintype.card (Fin n₁ → BitString n₁) = 2 ^ (n₁ * n₁) := by
    simp [BitString, pow_mul]
  have hbadPairs_card : #badPairs = #badInputs * 2 ^ (n₁ * n₁) := by
    have hbij : #badPairs = #(badInputs ×ˢ (univ : Finset (Fin n₁ → BitString n₁))) := by
      refine Finset.card_bij (fun w _ => (w.base, w.inRows)) ?_ ?_ ?_
      · intro w hw
        exact mem_product.mpr ⟨(mem_filter.mp hw).2, mem_univ _⟩
      · intro w₁ _ w₂ _ heq
        cases w₁; cases w₂
        simpa only [Prod.mk.injEq, InputHashedInput.mk.injEq] using heq
      · rintro ⟨z, rows⟩ hmem
        exact ⟨⟨z, rows⟩, mem_filter.mpr ⟨mem_univ _, (mem_product.mp hmem).1⟩, rfl⟩
    rw [hbij, card_product, card_univ, hcard_rows]
  -- Bound `#goodImages ≤ 2^(n₁ - K)` via disjoint fibers of size `> 2^K`:
  have hgoodImages_card : (#goodImages : ℝ) ≤ (2 : ℝ) ^ n₁ * ((2 : ℝ) ^ K)⁻¹ := by
    have hfib_ge (y : BitString m₁) (hy : y ∈ goodImages) :
        (2 : ℝ) ^ K ≤ (#(fiberSet f₁ y) : ℝ) := by
      obtain ⟨z, hz, rfl⟩ := mem_image.mp hy
      have hgt : K < realSampleEntropy f₁ z := not_le.mp (mem_filter.mp hz).2
      have hpos : (0 : ℝ) < #(fiberSet f₁ (f₁ z)) := by exact_mod_cast card_fiberSet_pos f₁ z
      exact (Real.le_logb_iff_rpow_le (by norm_num : (1 : ℝ) < 2) hpos).mp hgt.le
    have hdisj : (goodImages : Set (BitString m₁)).PairwiseDisjoint (fiberSet f₁) := by
      intro y₁ _ y₂ _ hne
      refine disjoint_left.mpr fun z hz₁ hz₂ => hne ?_
      rw [← (mem_fiberSet f₁ y₁ z).mp hz₁, ← (mem_fiberSet f₁ y₂ z).mp hz₂]
    have hsum_le : (#goodImages : ℝ) * (2 : ℝ) ^ K ≤ (2 : ℝ) ^ n₁ := by
      calc
        (#goodImages : ℝ) * (2 : ℝ) ^ K = ∑ _y ∈ goodImages, (2 : ℝ) ^ K := by
          rw [sum_const, nsmul_eq_mul]
        _ ≤ ∑ y ∈ goodImages, (#(fiberSet f₁ y) : ℝ) := sum_le_sum hfib_ge
        _ = ((goodImages.biUnion (fiberSet f₁)).card : ℝ) := by
          rw [card_biUnion hdisj, Nat.cast_sum]
        _ ≤ (Fintype.card (BitString n₁) : ℝ) := by exact_mod_cast card_le_univ _
        _ = (2 : ℝ) ^ n₁ := by simp [BitString]
    have hpow_pos : (0 : ℝ) < (2 : ℝ) ^ K := Real.rpow_pos_of_pos (by norm_num) K
    exact (le_mul_inv_iff₀ hpow_pos).mpr hsum_le
  -- Bound `#(goodPairs.image (inputHashFin f₁ j))`:
  have hgoodIm_card :
      #(goodPairs.image (inputHashFin f₁ j)) ≤
        #goodImages * 2 ^ (n₁ * n₁) * 2 ^ (min j n₁) := by
    let box := goodImages ×ˢ (univ : Finset (Fin n₁ → BitString n₁)) ×ˢ
      (univ : Finset (BitString (min j n₁)))
    let packBox : BitString m₁ × (Fin n₁ → BitString n₁) × BitString (min j n₁) →
        InputHashedOutput n₁ m₁ :=
      fun ⟨y, rows, p⟩ => ⟨y, rows, unpadPrefix n₁ j p⟩
    have hsub : goodPairs.image (inputHashFin f₁ j) ⊆ box.image packBox := by
      intro out hout
      obtain ⟨w, hw, rfl⟩ := mem_image.mp hout
      refine mem_image.mpr ⟨(f₁ w.base, w.inRows,
        prefixProj n₁ j (Cslib.BitString.LinearHash.hash w.inRows w.base)), ?_, ?_⟩
      · exact mem_product.mpr ⟨mem_image_of_mem f₁ (mem_filter.mp hw).2,
          mem_product.mpr ⟨mem_univ _, mem_univ _⟩⟩
      · simp only [packBox, inputHashFin, zeroPadPrefix_eq_unpadPrefix]
    have hbox_card : #box = #goodImages * 2 ^ (n₁ * n₁) * 2 ^ (min j n₁) := by
      have hp : Fintype.card (BitString (min j n₁)) = 2 ^ (min j n₁) := by simp [BitString]
      simp only [box, card_product, card_univ, hcard_rows, hp, mul_assoc]
    exact (card_le_card hsub).trans (card_image_le.trans hbox_card.le)
  -- Combine `badPairs` and `goodPairs`:
  have hunion : (univ : Finset (InputHashedInput n₁)) = badPairs ∪ goodPairs := by
    ext w
    simp only [mem_univ, mem_union, badPairs, goodPairs, badInputs, goodInputs, mem_filter,
      true_and, true_iff]
    exact Classical.em _
  have hbad_prob : (#badInputs : ℝ) / (2 : ℝ) ^ n₁ =
      ((PMF.uniformOfFintype (BitString n₁)).toOuterMeasure
        {z | realSampleEntropy f₁ z ≤ K}).toReal := by
    rw [PMF.toOuterMeasure_uniformOfFintype_toReal]
    have hc : (Fintype.card (BitString n₁) : ℝ) = (2 : ℝ) ^ n₁ := by simp [BitString]
    rw [hc]
    rfl
  have htotal_nat :
      #(univ.image (inputHashFin f₁ j)) ≤
        #badInputs * 2 ^ (n₁ * n₁) + #goodImages * 2 ^ (n₁ * n₁) * 2 ^ (min j n₁) := by
    rw [hunion, image_union]
    refine (card_union_le _ _).trans (Nat.add_le_add ?_ hgoodIm_card)
    exact card_image_le.trans hbadPairs_card.le
  have hpow_inLen₂ : (2 : ℝ) ^ (inputHashInLen n₁) = (2 : ℝ) ^ n₁ * (2 : ℝ) ^ (n₁ * n₁) := by
    rw [inputHashInLen, pow_add]
  have hrpow_diff : (2 : ℝ) ^ ((min j n₁ : ℝ) - K) =
      (2 : ℝ) ^ (min j n₁) * ((2 : ℝ) ^ K)⁻¹ := by
    rw [Real.rpow_sub (by norm_num : (0 : ℝ) < 2), ← Nat.cast_min, Real.rpow_natCast,
      div_eq_mul_inv]
  have hn₁_pos : (0 : ℝ) < (2 : ℝ) ^ n₁ := by positivity
  calc
    (#(univ.image (inputHashFin f₁ j)) : ℝ)
      ≤ (#badInputs : ℝ) * (2 : ℝ) ^ (n₁ * n₁) +
          (#goodImages : ℝ) * (2 : ℝ) ^ (n₁ * n₁) * (2 : ℝ) ^ (min j n₁) := by
        exact_mod_cast htotal_nat
    _ = ((#badInputs : ℝ) / (2 : ℝ) ^ n₁) * ((2 : ℝ) ^ n₁ * (2 : ℝ) ^ (n₁ * n₁)) +
          (#goodImages : ℝ) * (2 : ℝ) ^ (n₁ * n₁) * (2 : ℝ) ^ (min j n₁) := by
        have hcancel : ((#badInputs : ℝ) / (2 : ℝ) ^ n₁) * (2 : ℝ) ^ n₁ = #badInputs :=
          div_mul_cancel₀ _ hn₁_pos.ne'
        rw [← mul_assoc, hcancel]
    _ ≤ ((#badInputs : ℝ) / (2 : ℝ) ^ n₁) * ((2 : ℝ) ^ n₁ * (2 : ℝ) ^ (n₁ * n₁)) +
          ((2 : ℝ) ^ n₁ * ((2 : ℝ) ^ K)⁻¹) * (2 : ℝ) ^ (n₁ * n₁) * (2 : ℝ) ^ (min j n₁) := by
        gcongr
    _ = (((PMF.uniformOfFintype (BitString n₁)).toOuterMeasure
          {z | realSampleEntropy f₁ z ≤ K}).toReal +
        (2 : ℝ) ^ ((min j n₁ : ℝ) - K)) * (2 : ℝ) ^ (inputHashInLen n₁) := by
        rw [hbad_prob, hpow_inLen₂, hrpow_diff]
        ring

/-! ### Step 3: Output-hash 1-bit shrinkage $F_3^{(j)}$ (Lemma 5.5 and Equation (5.7)) -/

/-- Finite evaluator $F_3^{(j)}(w, \mathrm{outRows}) = (\mathrm{outRows},
\mathrm{hash}\;\mathrm{outRows}\;(\mathrm{enc}(F_2^{(j)}(w))))$ (`[HHRVW2020]`, Section 5.1.3,
Lemma 5.5, p. 29). -/
@[expose] def shrunkHashFin {n₁ m₁ : ℕ} (f₁ : BitString n₁ → BitString m₁) (j : ℕ)
    (v : ShrunkHashInput n₁ m₁) : ShrunkHashOutput n₁ m₁ where
  outRows := v.outRows
  outDigest := Cslib.BitString.LinearHash.hash v.outRows
    (inputHashedOutputEquiv n₁ m₁ (inputHashFin f₁ j v.inner))

open Classical in
/-- **`[HHRVW2020]`, Section 5.1.3, Lemma 5.5, Equation (5.7) (p. 29)**: for every fixed input $w$,
the probability over `outRows` that some $w'$ with $F_2^{(j)}(w') \ne F_2^{(j)}(w)$ collides with
$w$ under `shrunkHashFin f₁ j` is at most $|F_2^{(j)}(\{0, 1\}^{n_2})| / 2^{n_2 - 1}$. -/
theorem shrunkHashFin_false_positive_le {n₁ m₁ : ℕ} (f₁ : BitString n₁ → BitString m₁)
    (j : ℕ) (w : InputHashedInput n₁) :
    (∑ outRows : Fin (outHashLen n₁) → BitString (inputHashOutLen n₁ m₁),
        if ∃ w' : InputHashedInput n₁,
            inputHashFin f₁ j w' ≠ inputHashFin f₁ j w ∧
            shrunkHashFin f₁ j ⟨w', outRows⟩ = shrunkHashFin f₁ j ⟨w, outRows⟩ then
          ((PMF.uniformOfFintype (Fin (outHashLen n₁) → BitString (inputHashOutLen n₁ m₁)))
            outRows).toReal
        else 0) ≤
      (#(univ.image (inputHashFin f₁ j)) : ℝ) / (2 : ℝ) ^ (outHashLen n₁) := by
  let encOut := inputHashedOutputEquiv n₁ m₁
  let cand := univ.image (inputHashFin f₁ j)
  have htwo : IsTwoUniversal
      (PMF.uniformOfFintype (Fin (outHashLen n₁) → BitString (inputHashOutLen n₁ m₁)))
      (fun outRows y => Cslib.BitString.LinearHash.hash outRows (encOut y)) :=
    (Cslib.BitString.LinearHash.isTwoUniversal
      (inputHashOutLen n₁ m₁) (outHashLen n₁)).precompose encOut.injective
  have hcard : (Fintype.card (BitString (outHashLen n₁)) : ℝ) = (2 : ℝ) ^ (outHashLen n₁) := by
    simp [BitString]
  rw [← hcard]
  exact sum_ite_toReal_le_card_div_of_imp htwo cand (inputHashFin f₁ j w) fun outRows h => by
    obtain ⟨w', hne, heq⟩ := h
    have hdig := congrArg ShrunkHashOutput.outDigest heq
    dsimp only [shrunkHashFin] at hdig
    exact ⟨inputHashFin f₁ j w', mem_image_of_mem _ (mem_univ w'), hne, hdig⟩

/-! ### Word-level evaluators and polynomial-time certificates -/

/-- Word-level evaluator of $F_2^{(j)}$ (`[HHRVW2020]`, Section 5.1.2, Lemma 5.4, pp. 27–28). -/
@[expose] def inputHashEvalWord (n₁ m₁ : ℕ) (evalWord₁ : List Bool → List Bool)
    (j : ℕ) (u : List Bool) : List Bool :=
  let zWord := Cslib.BitString.listRow n₁ 0 (u.take n₁)
  let inSeed := Cslib.BitString.listRow (n₁ * n₁) 0 ((u.drop n₁).take (n₁ * n₁))
  let baseBits := Cslib.BitString.listRow m₁ 0 (evalWord₁ zWord)
  let fullDigest := wordHash n₁ inSeed zWord
  let r := n₁ - (n₁ - j)
  baseBits ++ inSeed ++ (fullDigest.take r ++ List.replicate (n₁ - r) false)

/-- Word-level evaluator of $F_3^{(j)}$ (`[HHRVW2020]`, Section 5.1.3, Lemma 5.5, p. 29). -/
@[expose] def shrunkHashEvalWord (n₁ m₁ : ℕ) (evalWord₁ : List Bool → List Bool)
    (j : ℕ) (raw : List Bool) : List Bool :=
  let inLen₂ := inputHashInLen n₁
  let outLen₂ := inputHashOutLen n₁ m₁
  let outH := outHashLen n₁
  let innerWord := raw.take inLen₂
  let outSeed := Cslib.BitString.listRow (outH * outLen₂) 0
    ((raw.drop inLen₂).take (outH * outLen₂))
  let y₂ := inputHashEvalWord n₁ m₁ evalWord₁ j innerWord
  outSeed ++ wordHash outH outSeed y₂

@[simp] theorem length_inputHashEvalWord (n₁ m₁ : ℕ) (evalWord₁ : List Bool → List Bool)
    (j : ℕ) (u : List Bool) :
    (inputHashEvalWord n₁ m₁ evalWord₁ j u).length = inputHashOutLen n₁ m₁ := by
  have hr : n₁ - (n₁ - j) ≤ n₁ := Nat.sub_le _ _
  simp only [inputHashEvalWord, inputHashOutLen, List.length_append,
    Cslib.BitString.length_listRow, List.length_take, length_wordHash, List.length_replicate]
  omega

@[simp] theorem length_shrunkHashEvalWord (n₁ m₁ : ℕ) (evalWord₁ : List Bool → List Bool)
    (j : ℕ) (raw : List Bool) :
    (shrunkHashEvalWord n₁ m₁ evalWord₁ j raw).length = shrunkHashOutLen n₁ m₁ := by
  simp only [shrunkHashEvalWord, shrunkHashOutLen, List.length_append,
    Cslib.BitString.length_listRow, length_wordHash]

/-- Plain polynomial-time certificate for `inputHashEvalWord`. -/
@[fun_prop]
theorem computableInPolyTime_inputHashEvalWord {α : Type} {encode : α ↪ List Bool}
    {n₁ m₁ n j : α → ℕ} {evalWord₁ : ℕ → List Bool → List Bool} {u : α → List Bool}
    (hn₁ : ComputableInPolyTime n₁ encode encUnary)
    (hm₁ : ComputableInPolyTime m₁ encode encUnary)
    (hn : ComputableInPolyTime n encode encUnary)
    (hj : ComputableInPolyTime j encode encUnary)
    (heval₁ : ComputableInPolyTime (fun p : ℕ × List Bool => evalWord₁ p.1 p.2)
      (encPair encUnary encBits) encBits)
    (hu : ComputableInPolyTime u encode encBits) :
    ComputableInPolyTime
      (fun a => inputHashEvalWord (n₁ a) (m₁ a) (evalWord₁ (n a)) (j a) (u a))
      encode encBits := by
  simp only [inputHashEvalWord]
  fun_prop

/-- Plain polynomial-time certificate for `shrunkHashEvalWord`. -/
@[fun_prop]
theorem computableInPolyTime_shrunkHashEvalWord {α : Type} {encode : α ↪ List Bool}
    {n₁ m₁ n j : α → ℕ} {evalWord₁ : ℕ → List Bool → List Bool} {raw : α → List Bool}
    (hn₁ : ComputableInPolyTime n₁ encode encUnary)
    (hm₁ : ComputableInPolyTime m₁ encode encUnary)
    (hn : ComputableInPolyTime n encode encUnary)
    (hj : ComputableInPolyTime j encode encUnary)
    (heval₁ : ComputableInPolyTime (fun p : ℕ × List Bool => evalWord₁ p.1 p.2)
      (encPair encUnary encBits) encBits)
    (hraw : ComputableInPolyTime raw encode encBits) :
    ComputableInPolyTime
      (fun a => shrunkHashEvalWord (n₁ a) (m₁ a) (evalWord₁ (n a)) (j a) (raw a))
      encode encBits := by
  simp only [shrunkHashEvalWord, inputHashInLen, inputHashOutLen, outHashLen]
  fun_prop

theorem inputHashEvalWord_packWord {n₁ m₁ : ℕ} (evalWord₁ : List Bool → List Bool)
    (j : ℕ) (w : InputHashedInput n₁) :
    inputHashEvalWord n₁ m₁ evalWord₁ j w.packWord =
      (inputHashFin (wordToFinMap n₁ m₁ evalWord₁) j w).packWord := by
  have hz : (List.ofFn w.base).length = n₁ := List.length_ofFn
  have hr : (List.ofFn (Cslib.BitString.blocksEquiv.symm w.inRows)).length = n₁ * n₁ :=
    List.length_ofFn
  have hzRow : Cslib.BitString.listRow n₁ 0 (List.ofFn w.base) = List.ofFn w.base := by
    rw [Cslib.BitString.listRow_zero, Cslib.BitString.ofList_ofFn]
  have hrRow : Cslib.BitString.listRow (n₁ * n₁) 0
      (List.ofFn (Cslib.BitString.blocksEquiv.symm w.inRows)) =
      List.ofFn (Cslib.BitString.blocksEquiv.symm w.inRows) := by
    rw [Cslib.BitString.listRow_zero, Cslib.BitString.ofList_ofFn]
  have hev : Cslib.BitString.listRow m₁ 0 (evalWord₁ (List.ofFn w.base)) =
      List.ofFn (wordToFinMap n₁ m₁ evalWord₁ w.base) := by
    rw [Cslib.BitString.listRow_zero, wordToFinMap]
  have hwh : wordHash n₁ (List.ofFn (Cslib.BitString.blocksEquiv.symm w.inRows))
      (List.ofFn w.base) =
      List.ofFn (Cslib.BitString.LinearHash.hash w.inRows w.base) := by
    rw [wordHash_eq_ofFn, Cslib.BitString.ofList_ofFn, ← Cslib.BitString.blocksEquiv_apply,
      Equiv.apply_symm_apply]
  have hmin : n₁ - (n₁ - j) = min j n₁ := by omega
  simp only [inputHashEvalWord, InputHashedInput.packWord, List.take_left' hz, List.drop_left' hz,
    List.take_of_length_le hr.le, hzRow, hrRow, hev, hwh, hmin,
    ← ofFn_zeroPadPrefix n₁ j (Cslib.BitString.LinearHash.hash w.inRows w.base),
    inputHashFin, InputHashedOutput.packWord, List.append_assoc]

theorem shrunkHashEvalWord_packWord {n₁ m₁ : ℕ} (evalWord₁ : List Bool → List Bool)
    (j : ℕ) (v : ShrunkHashInput n₁ m₁) :
    shrunkHashEvalWord n₁ m₁ evalWord₁ j v.packWord =
      (shrunkHashFin (wordToFinMap n₁ m₁ evalWord₁) j v).packWord := by
  have hi : v.inner.packWord.length = inputHashInLen n₁ := v.inner.length_packWord
  have ho : (List.ofFn (Cslib.BitString.blocksEquiv.symm v.outRows)).length =
      outHashLen n₁ * inputHashOutLen n₁ m₁ := List.length_ofFn
  have hoRow : Cslib.BitString.listRow (outHashLen n₁ * inputHashOutLen n₁ m₁) 0
      (List.ofFn (Cslib.BitString.blocksEquiv.symm v.outRows)) =
      List.ofFn (Cslib.BitString.blocksEquiv.symm v.outRows) := by
    rw [Cslib.BitString.listRow_zero, Cslib.BitString.ofList_ofFn]
  set y₂Fin := inputHashFin (wordToFinMap n₁ m₁ evalWord₁) j v.inner
  have hy₂ : y₂Fin.packWord = List.ofFn (inputHashedOutputEquiv n₁ m₁ y₂Fin) :=
    (Cslib.BitString.ofFn_ofList y₂Fin.length_packWord).symm
  have hwh : wordHash (outHashLen n₁) (List.ofFn (Cslib.BitString.blocksEquiv.symm v.outRows))
      (List.ofFn (inputHashedOutputEquiv n₁ m₁ y₂Fin)) =
      List.ofFn (Cslib.BitString.LinearHash.hash v.outRows
        (inputHashedOutputEquiv n₁ m₁ y₂Fin)) := by
    rw [wordHash_eq_ofFn, Cslib.BitString.ofList_ofFn, ← Cslib.BitString.blocksEquiv_apply,
      Equiv.apply_symm_apply]
  dsimp only [y₂Fin] at hy₂ hwh
  simp only [shrunkHashEvalWord, ShrunkHashInput.packWord, List.take_left' hi, List.drop_left' hi,
    List.take_of_length_le ho.le, hoRow, inputHashEvalWord_packWord evalWord₁ j v.inner,
    hy₂, hwh, shrunkHashFin, ShrunkHashOutput.packWord]

/-! ### Random-input collision game and combined reduction to $L_1$-escape -/

/-- Security experiment for collision resistance on random inputs (`[HHRVW2020]`, Section 3.1,
p. 13, and Section 5.1.3, Lemma 5.5, p. 29): draw a uniform `(inLen n)`-bit input `xWord`, run `A`,
and accept when `A` returns a distinct `(inLen n)`-bit input with the same `evalWord n` image. -/
@[expose] noncomputable def randomCollisionGame (evalWord : ℕ → List Bool → List Bool)
    (inLen : ℕ → ℕ) (A : ℕ → List Bool → ProbComp (List Bool)) (n : ℕ) : ProbComp Bool := do
  let xWord ← Cslib.BitString.sampleList (inLen n)
  let xWord' ← A n xWord
  return decide (xWord'.length = inLen n ∧ xWord' ≠ xWord ∧ evalWord n xWord' = evalWord n xWord)

/-- Uniform strict-PPT reduction from random-input collisions of $F_3^{(j)}$ to $F_1$ accessible
escape (`[HHRVW2020]`, Lemmas 5.4(ii) and 5.5, pp. 28–29). Note that the reduction does **not**
depend on the grid truncation length $j$: it pads the $n_1$-bit challenge `zWord` with uniform
`(inSeed, outSeed)`, runs `A`, and extracts the $n_1$-bit prefix. -/
@[expose] noncomputable def shrunkHashEscapeInverter (n₁ m₁ : ℕ → ℕ)
    (A : ℕ → List Bool → ProbComp (List Bool)) (n : ℕ) (zWord : List Bool) :
    ProbComp (List Bool) := do
  let inSeed ← Cslib.BitString.sampleList (n₁ n * n₁ n)
  let outSeed ← Cslib.BitString.sampleList (outHashLen (n₁ n) * inputHashOutLen (n₁ n) (m₁ n))
  let zPad := Cslib.BitString.listRow (n₁ n) 0 zWord
  let raw ← A n (zPad ++ inSeed ++ outSeed)
  return raw.take (n₁ n)

/-- Plain uniform strict-PPT certificate for `shrunkHashEscapeInverter`. -/
theorem isPPT_shrunkHashEscapeInverter {n₁ m₁ : ℕ → ℕ}
    {A : ℕ → List Bool → ProbComp (List Bool)}
    (hn₁ : ComputableInPolyTime n₁ encUnary encUnary)
    (hm₁ : ComputableInPolyTime m₁ encUnary encUnary)
    (hA : IsPPT encBits A) :
    IsPPT encBits (shrunkHashEscapeInverter n₁ m₁ A) := by
  apply IsPPTOn.isPPT
  refine (ComputableInPolyTime.sampleList (by fun_prop)).bind_with ?_
  refine (ComputableInPolyTime.sampleList
    (by unfold outHashLen inputHashOutLen inputHashInLen; fun_prop)).bind_with ?_
  exact (hA.preprocess (ComputableInPolyTime.tidy (by fun_prop))
    (ComputableInPolyTime.tidy (by fun_prop))).bind_with
    (ComputableInPolyTime.isPPTOn (by fun_prop))

private def shrunkTupleEquiv (n₁ m₁ : ℕ) :
    (BitString n₁ × (Fin n₁ → BitString n₁) ×
      (Fin (outHashLen n₁) → BitString (inputHashOutLen n₁ m₁))) ≃
      BitString (shrunkHashInLen n₁ m₁) where
  toFun t := Cslib.BitString.ofList (shrunkHashInLen n₁ m₁)
    (ShrunkHashInput.mk ⟨t.1, t.2.1⟩ t.2.2).packWord
  invFun b :=
    let v := ShrunkHashInput.unpackWord n₁ m₁ (List.ofFn b)
    (v.inner.base, v.inner.inRows, v.outRows)
  left_inv t := by
    rcases t with ⟨z, iRows, oRows⟩
    dsimp only
    rw [Cslib.BitString.ofFn_ofList (ShrunkHashInput.mk ⟨z, iRows⟩ oRows).length_packWord,
      ShrunkHashInput.unpackWord_packWord]
  right_inv b := by
    dsimp only
    have hpack := ShrunkHashInput.packWord_unpackWord (n₁ := n₁) (m₁ := m₁) (raw := List.ofFn b)
      List.length_ofFn
    let v := ShrunkHashInput.unpackWord n₁ m₁ (List.ofFn b)
    have hv : ShrunkHashInput.mk ⟨v.inner.base, v.inner.inRows⟩ v.outRows = v := by
      rcases v with ⟨⟨_, _⟩, _⟩; rfl
    rw [hv, hpack, Cslib.BitString.ofList_ofFn]

private theorem uniformList_shrunkHashInLen_eq (n₁ m₁ : ℕ) :
    Cslib.BitString.uniformList (shrunkHashInLen n₁ m₁) =
      (PMF.uniformOfFintype (BitString n₁)).bind fun z =>
        (PMF.uniformOfFintype (Fin n₁ → BitString n₁)).bind fun iRows =>
          (PMF.uniformOfFintype
            (Fin (outHashLen n₁) → BitString (inputHashOutLen n₁ m₁))).map fun oRows =>
              (ShrunkHashInput.mk ⟨z, iRows⟩ oRows).packWord := by
  have hprod :
      ((PMF.uniformOfFintype (BitString n₁)).bind fun z =>
        (PMF.uniformOfFintype (Fin n₁ → BitString n₁)).bind fun iRows =>
          (PMF.uniformOfFintype
            (Fin (outHashLen n₁) → BitString (inputHashOutLen n₁ m₁))).map fun oRows =>
              (z, iRows, oRows)) =
      PMF.uniformOfFintype (BitString n₁ × (Fin n₁ → BitString n₁) ×
        (Fin (outHashLen n₁) → BitString (inputHashOutLen n₁ m₁))) := by
    rw [← PMF.uniformOfFintype_prod (BitString n₁)]
    refine PMF.bind_congr_on_support _ _ _ fun z _ => ?_
    rw [← PMF.uniformOfFintype_prod (Fin n₁ → BitString n₁), PMF.map_bind]
    simp only [PMF.map_comp, Function.comp_def]
  have heq :
      ((PMF.uniformOfFintype (BitString n₁)).bind fun z =>
        (PMF.uniformOfFintype (Fin n₁ → BitString n₁)).bind fun iRows =>
          (PMF.uniformOfFintype
            (Fin (outHashLen n₁) → BitString (inputHashOutLen n₁ m₁))).map fun oRows =>
              (ShrunkHashInput.mk ⟨z, iRows⟩ oRows).packWord) =
      ((PMF.uniformOfFintype (BitString n₁)).bind fun z =>
        (PMF.uniformOfFintype (Fin n₁ → BitString n₁)).bind fun iRows =>
          (PMF.uniformOfFintype
            (Fin (outHashLen n₁) → BitString (inputHashOutLen n₁ m₁))).map fun oRows =>
              (z, iRows, oRows)).map
        (fun t => (ShrunkHashInput.mk ⟨t.1, t.2.1⟩ t.2.2).packWord) := by
    simp only [PMF.map_bind, PMF.map_comp, Function.comp_def]
  rw [heq, hprod, Cslib.BitString.uniformList,
    ← PMF.uniformOfFintype_map_equiv (shrunkTupleEquiv n₁ m₁), PMF.map_comp]
  refine congrArg (PMF.uniformOfFintype _).map (funext fun t => ?_)
  exact Cslib.BitString.ofFn_ofList (ShrunkHashInput.mk ⟨t.1, t.2.1⟩ t.2.2).length_packWord

private abbrev shrunkBadIn {w₁ out₁ : ℕ} (f₁ : BitString w₁ → BitString out₁) (j₀ : ℕ)
    (L : BitString w₁ → Finset (BitString w₁)) (z : BitString w₁)
    (iRows : Fin w₁ → BitString w₁) : Prop :=
  ∃ z' ∈ L z, z' ≠ z ∧ inputHashFin f₁ j₀ ⟨z', iRows⟩ = inputHashFin f₁ j₀ ⟨z, iRows⟩

private abbrev shrunkBadOut {w₁ out₁ : ℕ} (f₁ : BitString w₁ → BitString out₁) (j₀ : ℕ)
    (w : InputHashedInput w₁)
    (oRows : Fin (outHashLen w₁) → BitString (inputHashOutLen w₁ out₁)) : Prop :=
  ∃ w' : InputHashedInput w₁,
    inputHashFin f₁ j₀ w' ≠ inputHashFin f₁ j₀ w ∧
    shrunkHashFin f₁ j₀ ⟨w', oRows⟩ = shrunkHashFin f₁ j₀ ⟨w, oRows⟩

private abbrev shrunkCollPred (w₁ out₁ j₀ : ℕ) (evalWord₁ : List Bool → List Bool)
    (v : ShrunkHashInput w₁ out₁) (raw : List Bool) : Prop :=
  raw.length = shrunkHashInLen w₁ out₁ ∧ raw ≠ v.packWord ∧
    shrunkHashEvalWord w₁ out₁ evalWord₁ j₀ raw =
      shrunkHashEvalWord w₁ out₁ evalWord₁ j₀ v.packWord

private abbrev shrunkEscPred (w₁ : ℕ) (evalWord₁ : List Bool → List Bool)
    (L : BitString w₁ → Finset (BitString w₁)) (z : BitString w₁) (raw : List Bool) : Prop :=
  let xRaw := raw.take w₁
  xRaw.length = w₁ ∧ evalWord₁ xRaw = evalWord₁ (List.ofFn z) ∧
    Cslib.BitString.ofList w₁ xRaw ∉ L z

private theorem shrunkCollPred_imp_shrunkEscPred {w₁ out₁ j₀ : ℕ}
    (evalWord₁ : List Bool → List Bool)
    (L : BitString w₁ → Finset (BitString w₁))
    (hlen₁ : ∀ u : List Bool, u.length = w₁ → (evalWord₁ u).length = out₁)
    (z : BitString w₁) (iRows : Fin w₁ → BitString w₁)
    (oRows : Fin (outHashLen w₁) → BitString (inputHashOutLen w₁ out₁))
    (hnot_in : ¬ shrunkBadIn (wordToFinMap w₁ out₁ evalWord₁) j₀ L z iRows)
    (hnot_out : ¬ shrunkBadOut (wordToFinMap w₁ out₁ evalWord₁) j₀ ⟨z, iRows⟩ oRows)
    (raw : List Bool) (hcoll : shrunkCollPred w₁ out₁ j₀ evalWord₁ ⟨⟨z, iRows⟩, oRows⟩ raw) :
    shrunkEscPred w₁ evalWord₁ L z raw := by
  let f₁ := wordToFinMap w₁ out₁ evalWord₁
  rcases hcoll with ⟨hlen_raw, hne_raw, heval_raw⟩
  let v : ShrunkHashInput w₁ out₁ := ⟨⟨z, iRows⟩, oRows⟩
  let v' := ShrunkHashInput.unpackWord w₁ out₁ raw
  have hpack' : v'.packWord = raw := ShrunkHashInput.packWord_unpackWord hlen_raw
  have hv_ne : v' ≠ v := fun h => hne_raw (by rw [← hpack', h])
  have hf₃_eq : shrunkHashFin f₁ j₀ v' = shrunkHashFin f₁ j₀ v := by
    have hp : (shrunkHashFin f₁ j₀ v').packWord = (shrunkHashFin f₁ j₀ v).packWord := by
      rw [← shrunkHashEvalWord_packWord evalWord₁ j₀ v',
        ← shrunkHashEvalWord_packWord evalWord₁ j₀ v, hpack', heval_raw]
    have h1 := ShrunkHashOutput.unpackWord_packWord (shrunkHashFin f₁ j₀ v')
    have h2 := ShrunkHashOutput.unpackWord_packWord (shrunkHashFin f₁ j₀ v)
    exact h1.symm.trans (by rw [hp, h2])
  have hoRows_eq : v'.outRows = oRows := congrArg ShrunkHashOutput.outRows hf₃_eq
  have hf₂_eq : inputHashFin f₁ j₀ v'.inner = inputHashFin f₁ j₀ ⟨z, iRows⟩ := by
    by_contra hne₂
    have hv'_mk : ShrunkHashInput.mk v'.inner oRows = v' := by rw [← hoRows_eq]
    exact hnot_out ⟨v'.inner, hne₂, by rw [hv'_mk, hf₃_eq]⟩
  have hiRows_eq : v'.inner.inRows = iRows := congrArg InputHashedOutput.inRows hf₂_eq
  have hz_ne : v'.inner.base ≠ z := by
    intro hz_eq
    apply hv_ne
    rcases v' with ⟨⟨b', ir'⟩, or'⟩
    dsimp only at hz_eq hiRows_eq hoRows_eq
    subst hz_eq; subst hiRows_eq; subst hoRows_eq; rfl
  have htake_eq : raw.take w₁ = List.ofFn v'.inner.base := by
    have h1 : raw.take w₁ = (v'.inner.packWord ++
        List.ofFn (Cslib.BitString.blocksEquiv.symm v'.outRows)).take w₁ := by
      rw [← hpack', ShrunkHashInput.packWord]
    have h2 : (v'.inner.packWord ++
        List.ofFn (Cslib.BitString.blocksEquiv.symm v'.outRows)).take w₁ =
        v'.inner.packWord.take w₁ :=
      List.take_append_of_le_length
        (by rw [InputHashedInput.length_packWord, inputHashInLen]; omega)
    rw [h1, h2, InputHashedInput.packWord, List.take_left' List.length_ofFn]
  have hf₁_eq : f₁ v'.inner.base = f₁ z := congrArg InputHashedOutput.baseOut hf₂_eq
  have heval₁_eq : evalWord₁ (List.ofFn v'.inner.base) = evalWord₁ (List.ofFn z) := by
    rw [← Cslib.BitString.ofFn_ofList (hlen₁ _ List.length_ofFn),
      ← Cslib.BitString.ofFn_ofList (hlen₁ (List.ofFn z) List.length_ofFn)]
    exact congrArg List.ofFn hf₁_eq
  have hnot_L₁ : v'.inner.base ∉ L z := by
    intro hmem
    have hinn_mk : InputHashedInput.mk v'.inner.base iRows = v'.inner := by rw [← hiRows_eq]
    exact hnot_in ⟨v'.inner.base, hmem, hz_ne, by rw [hinn_mk, hf₂_eq]⟩
  refine ⟨?_, ?_, ?_⟩
  · simp only [htake_eq, List.length_ofFn]
  · simp only [htake_eq, heval₁_eq]
  · simp only [htake_eq, Cslib.BitString.ofList_ofFn]
    exact hnot_L₁

open Classical in
private theorem shrunkHash_pointwise_toReal_le {w₁ out₁ j₀ : ℕ}
    (evalWord₁ : List Bool → List Bool)
    (L : BitString w₁ → Finset (BitString w₁))
    (hlen₁ : ∀ u : List Bool, u.length = w₁ → (evalWord₁ u).length = out₁)
    (pA : PMF (List Bool)) (z : BitString w₁) (iRows : Fin w₁ → BitString w₁)
    (oRows : Fin (outHashLen w₁) → BitString (inputHashOutLen w₁ out₁)) :
    ((pA >>= fun raw =>
        PMF.pure (decide (shrunkCollPred w₁ out₁ j₀ evalWord₁ ⟨⟨z, iRows⟩, oRows⟩ raw)))
      true).toReal ≤
      ((pA >>= fun raw => PMF.pure (decide (shrunkEscPred w₁ evalWord₁ L z raw))) true).toReal +
      (if shrunkBadIn (wordToFinMap w₁ out₁ evalWord₁) j₀ L z iRows then 1 else 0) +
      (if shrunkBadOut (wordToFinMap w₁ out₁ evalWord₁) j₀ ⟨z, iRows⟩ oRows then 1 else 0) := by
  have hle_one :
      ((pA >>= fun raw =>
          PMF.pure (decide (shrunkCollPred w₁ out₁ j₀ evalWord₁ ⟨⟨z, iRows⟩, oRows⟩ raw)))
        true).toReal ≤ 1 :=
    PMF.toReal_apply_le_one _ true
  have hesc_nonneg :
      0 ≤ ((pA >>= fun raw =>
          PMF.pure (decide (shrunkEscPred w₁ evalWord₁ L z raw))) true).toReal :=
    ENNReal.toReal_nonneg
  by_cases hin : shrunkBadIn (wordToFinMap w₁ out₁ evalWord₁) j₀ L z iRows
  · by_cases hout : shrunkBadOut (wordToFinMap w₁ out₁ evalWord₁) j₀ ⟨z, iRows⟩ oRows <;>
      simp only [hin, hout, ↓reduceIte] <;> linarith
  · by_cases hout : shrunkBadOut (wordToFinMap w₁ out₁ evalWord₁) j₀ ⟨z, iRows⟩ oRows
    · simp only [hin, hout, ↓reduceIte]; linarith
    · simp only [hin, hout, ↓reduceIte, add_zero, PMF.monad_bind_eq_bind]
      refine ENNReal.toReal_mono (PMF.apply_ne_top _ _)
        (PMF.bind_apply_mono_on_support pA true fun raw _ => ?_)
      by_cases hc : shrunkCollPred w₁ out₁ j₀ evalWord₁ ⟨⟨z, iRows⟩, oRows⟩ raw
      · have he := shrunkCollPred_imp_shrunkEscPred evalWord₁ L hlen₁ z iRows oRows hin hout raw hc
        simp [hc, he]
      · simp [hc]

private noncomputable abbrev shrunkExpect (w₁ out₁ : ℕ)
    (g : BitString w₁ → (Fin w₁ → BitString w₁) →
      (Fin (outHashLen w₁) → BitString (inputHashOutLen w₁ out₁)) → ℝ) : ℝ :=
  ∑ z : BitString w₁, ((PMF.uniformOfFintype (BitString w₁)) z).toReal *
    ∑ iRows : Fin w₁ → BitString w₁,
      ((PMF.uniformOfFintype (Fin w₁ → BitString w₁)) iRows).toReal *
      ∑ oRows : Fin (outHashLen w₁) → BitString (inputHashOutLen w₁ out₁),
        ((PMF.uniformOfFintype _) oRows).toReal * g z iRows oRows

open Classical in
private theorem shrunkHash_randomCollision_succProbability_eq (n₁ m₁ j : ℕ → ℕ)
    (evalWord₁ : ℕ → List Bool → List Bool)
    (A : ℕ → List Bool → ProbComp (List Bool)) (n : ℕ) :
    (Game.succProbability (ProbComp.eval
      (randomCollisionGame
        (fun k => shrunkHashEvalWord (n₁ k) (m₁ k) (evalWord₁ k) (j k))
        (fun k => shrunkHashInLen (n₁ k) (m₁ k)) A n)) : ℝ) =
      shrunkExpect (n₁ n) (m₁ n) fun z iRows oRows =>
        ((ProbComp.eval (A n (ShrunkHashInput.mk ⟨z, iRows⟩ oRows).packWord) >>= fun raw =>
          PMF.pure (decide (shrunkCollPred (n₁ n) (m₁ n) (j n) (evalWord₁ n)
            ⟨⟨z, iRows⟩, oRows⟩ raw))) true).toReal := by
  simp only [Game.succProbability, ENNReal.coe_toNNReal_eq_toReal, randomCollisionGame,
    ProbComp.eval_bind, Cslib.BitString.eval_sampleList, ProbComp.eval_pure]
  rw [uniformList_shrunkHashInLen_eq (n₁ n) (m₁ n), PMF.bind_bind]
  simp only [PMF.bind_apply_toReal]
  refine sum_congr rfl fun z _ => congrArg (_ * ·) ?_
  rw [PMF.bind_bind]
  simp only [PMF.bind_apply_toReal]
  refine sum_congr rfl fun iRows _ => congrArg (_ * ·) ?_
  rw [PMF.bind_map, PMF.bind_apply_toReal]
  rfl

open Classical in
private theorem shrunkHash_escape_succProbability_eq (n₁ m₁ : ℕ → ℕ)
    (evalWord₁ : ℕ → List Bool → List Bool)
    (L₁ : (n : ℕ) → BitString (n₁ n) → Finset (BitString (n₁ n)))
    (A : ℕ → List Bool → ProbComp (List Bool)) (n : ℕ) :
    (Game.succProbability (ProbComp.eval
      (accessibleEscapeGame evalWord₁ n₁ L₁ (shrunkHashEscapeInverter n₁ m₁ A) n)) : ℝ) =
      shrunkExpect (n₁ n) (m₁ n) fun z iRows oRows =>
        ((ProbComp.eval (A n (ShrunkHashInput.mk ⟨z, iRows⟩ oRows).packWord) >>= fun raw =>
          PMF.pure (decide
            (shrunkEscPred (n₁ n) (evalWord₁ n) (L₁ n) z raw))) true).toReal := by
  have hin_map : Cslib.BitString.uniformList (n₁ n * n₁ n) =
      (PMF.uniformOfFintype (Fin (n₁ n) → BitString (n₁ n))).map
        (fun iRows => List.ofFn (Cslib.BitString.blocksEquiv.symm iRows)) := by
    rw [Cslib.BitString.uniformList,
      ← PMF.uniformOfFintype_map_equiv Cslib.BitString.blocksEquiv.symm, PMF.map_comp]
    rfl
  have hout_map : Cslib.BitString.uniformList (outHashLen (n₁ n) * inputHashOutLen (n₁ n) (m₁ n)) =
      (PMF.uniformOfFintype
        (Fin (outHashLen (n₁ n)) → BitString (inputHashOutLen (n₁ n) (m₁ n)))).map
        (fun oRows => List.ofFn (Cslib.BitString.blocksEquiv.symm oRows)) := by
    rw [Cslib.BitString.uniformList,
      ← PMF.uniformOfFintype_map_equiv Cslib.BitString.blocksEquiv.symm, PMF.map_comp]
    rfl
  have heval :
      ProbComp.eval (accessibleEscapeGame evalWord₁ n₁ L₁
        (shrunkHashEscapeInverter n₁ m₁ A) n) =
      (PMF.uniformOfFintype (BitString (n₁ n))).bind fun z =>
        (PMF.uniformOfFintype (Fin (n₁ n) → BitString (n₁ n))).bind fun iRows =>
          (PMF.uniformOfFintype
            (Fin (outHashLen (n₁ n)) → BitString (inputHashOutLen (n₁ n) (m₁ n)))).bind fun oRows =>
              ProbComp.eval (A n (ShrunkHashInput.mk ⟨z, iRows⟩ oRows).packWord) >>= fun raw =>
                PMF.pure (decide (shrunkEscPred (n₁ n) (evalWord₁ n) (L₁ n) z raw)) := by
    simp only [accessibleEscapeGame, shrunkHashEscapeInverter, ProbComp.eval_bind,
      Cslib.BitString.eval_sampleList, ProbComp.eval_pure, PMF.monad_bind_eq_bind,
      PMF.bind_bind]
    rw [Cslib.BitString.uniformList, PMF.bind_map]
    refine congrArg (PMF.uniformOfFintype (BitString (n₁ n))).bind (funext fun z => ?_)
    change ((Cslib.BitString.uniformList (n₁ n * n₁ n)).bind _) = _
    rw [hin_map, PMF.bind_map]
    refine congrArg (PMF.uniformOfFintype _).bind (funext fun iRows => ?_)
    change ((Cslib.BitString.uniformList
      (outHashLen (n₁ n) * inputHashOutLen (n₁ n) (m₁ n))).bind _) = _
    rw [hout_map, PMF.bind_map]
    refine congrArg (PMF.uniformOfFintype _).bind (funext fun oRows => ?_)
    have hzRow : Cslib.BitString.listRow (n₁ n) 0 (List.ofFn z) = List.ofFn z := by
      rw [Cslib.BitString.listRow_zero, Cslib.BitString.ofList_ofFn]
    simp only [Function.comp_def, hzRow, Cslib.BitString.ofList_ofFn, PMF.pure_bind,
      ShrunkHashInput.packWord, InputHashedInput.packWord, shrunkEscPred]
  simp only [Game.succProbability, ENNReal.coe_toNNReal_eq_toReal, heval, PMF.bind_apply_toReal]

open Classical in
private theorem shrunkBadIn_sum_le {w₁ out₁ j₀ : ℕ} (f₁ : BitString w₁ → BitString out₁)
    (L : BitString w₁ → Finset (BitString w₁)) (A_max : ℝ) :
    shrunkExpect w₁ out₁ (fun z iRows _ => if shrunkBadIn f₁ j₀ L z iRows then 1 else 0) ≤
      ((PMF.uniformOfFintype (BitString w₁)).toOuterMeasure
        {z | A_max ≤ Real.logb 2 #(L z)}).toReal +
      (2 : ℝ) ^ (A_max - (min j₀ w₁ : ℝ)) := by
  have hinner_z (z : BitString w₁) :
      (∑ iRows : Fin w₁ → BitString w₁,
        ((PMF.uniformOfFintype (Fin w₁ → BitString w₁)) iRows).toReal *
        ∑ oRows : Fin (outHashLen w₁) → BitString (inputHashOutLen w₁ out₁),
          ((PMF.uniformOfFintype _) oRows).toReal *
            (if shrunkBadIn f₁ j₀ L z iRows then 1 else 0)) ≤
      (if A_max ≤ Real.logb 2 #(L z) then 1 else 0) +
        (2 : ℝ) ^ (A_max - (min j₀ w₁ : ℝ)) := by
    have hsimp : (∑ iRows : Fin w₁ → BitString w₁,
        ((PMF.uniformOfFintype (Fin w₁ → BitString w₁)) iRows).toReal *
        ∑ oRows : Fin (outHashLen w₁) → BitString (inputHashOutLen w₁ out₁),
          ((PMF.uniformOfFintype _) oRows).toReal *
            (if shrunkBadIn f₁ j₀ L z iRows then 1 else 0)) =
        ∑ iRows : Fin w₁ → BitString w₁,
          if shrunkBadIn f₁ j₀ L z iRows then
            ((PMF.uniformOfFintype (Fin w₁ → BitString w₁)) iRows).toReal
          else 0 := by
      refine sum_congr rfl fun iRows _ => ?_
      by_cases hb : shrunkBadIn f₁ j₀ L z iRows <;> simp [hb]
    rw [hsimp]
    by_cases hA_ge : A_max ≤ Real.logb 2 #(L z)
    · simp only [hA_ge, ↓reduceIte]
      have hle1 : (∑ iRows : Fin w₁ → BitString w₁,
          if shrunkBadIn f₁ j₀ L z iRows then
            ((PMF.uniformOfFintype (Fin w₁ → BitString w₁)) iRows).toReal
          else 0) ≤ 1 :=
        (sum_le_sum fun iRows _ => by
          split_ifs <;> first | exact le_rfl | exact ENNReal.toReal_nonneg).trans_eq
          (PMF.sum_toReal _)
      have hpos : (0 : ℝ) ≤ (2 : ℝ) ^ (A_max - (min j₀ w₁ : ℝ)) :=
        Real.rpow_nonneg (by norm_num) _
      linarith
    · simp only [hA_ge, ↓reduceIte, zero_add]
      have hcard_le : (#(L z) : ℝ) ≤ (2 : ℝ) ^ A_max := by
        rcases Nat.eq_zero_or_pos #(L z) with h0 | hpos
        · rw [h0, Nat.cast_zero]; exact Real.rpow_nonneg (by norm_num) _
        · exact (Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 2)
            (by exact_mod_cast hpos)).mp (not_le.mp hA_ge).le
      refine (inputHashFin_accessible_collision_le f₁ j₀ (L z) z).trans ?_
      rw [Real.rpow_sub (by norm_num : (0 : ℝ) < 2), ← Nat.cast_min, Real.rpow_natCast]
      gcongr
  calc
    shrunkExpect w₁ out₁ (fun z iRows _ => if shrunkBadIn f₁ j₀ L z iRows then 1 else 0)
      ≤ ∑ z : BitString w₁, ((PMF.uniformOfFintype (BitString w₁)) z).toReal *
          ((if A_max ≤ Real.logb 2 #(L z) then 1 else 0) +
            (2 : ℝ) ^ (A_max - (min j₀ w₁ : ℝ))) :=
        sum_le_sum fun z _ => mul_le_mul_of_nonneg_left (hinner_z z) ENNReal.toReal_nonneg
    _ = (∑ z : BitString w₁,
          if z ∈ {z : BitString w₁ | A_max ≤ Real.logb 2 #(L z)} then
            ((PMF.uniformOfFintype (BitString w₁)) z).toReal
          else 0) +
        (∑ z : BitString w₁, ((PMF.uniformOfFintype (BitString w₁)) z).toReal) *
          (2 : ℝ) ^ (A_max - (min j₀ w₁ : ℝ)) := by
        simp only [mul_add, sum_add_distrib, ← sum_mul]
        congr 1
        refine sum_congr rfl fun z _ => ?_
        by_cases h : A_max ≤ Real.logb 2 #(L z) <;> simp [h]
    _ = ((PMF.uniformOfFintype (BitString w₁)).toOuterMeasure
          {z | A_max ≤ Real.logb 2 #(L z)}).toReal +
        (2 : ℝ) ^ (A_max - (min j₀ w₁ : ℝ)) := by
        rw [← PMF.toOuterMeasure_apply_toReal, PMF.sum_toReal, one_mul]

open Classical in
private theorem shrunkBadOut_sum_le {w₁ out₁ j₀ : ℕ} (hw₁ : 1 ≤ w₁)
    (f₁ : BitString w₁ → BitString out₁) (K_min : ℝ) :
    shrunkExpect w₁ out₁ (fun z iRows oRows =>
        if shrunkBadOut f₁ j₀ ⟨z, iRows⟩ oRows then 1 else 0) ≤
      2 * (((PMF.uniformOfFintype (BitString w₁)).toOuterMeasure
          {z | realSampleEntropy f₁ z ≤ K_min}).toReal +
        (2 : ℝ) ^ ((min j₀ w₁ : ℝ) - K_min)) := by
  have hpow_ratio : (2 : ℝ) ^ (inputHashInLen w₁) / (2 : ℝ) ^ (outHashLen w₁) = 2 := by
    have hout_succ : outHashLen w₁ + 1 = inputHashInLen w₁ := by
      simp only [outHashLen, inputHashInLen]; omega
    rw [← hout_succ, pow_succ', mul_div_cancel_right₀ _ (by positivity)]
  let C := 2 * (((PMF.uniformOfFintype (BitString w₁)).toOuterMeasure
      {z | realSampleEntropy f₁ z ≤ K_min}).toReal + (2 : ℝ) ^ ((min j₀ w₁ : ℝ) - K_min))
  have hper_w (z : BitString w₁) (iRows : Fin w₁ → BitString w₁) :
      (∑ oRows : Fin (outHashLen w₁) → BitString (inputHashOutLen w₁ out₁),
        ((PMF.uniformOfFintype _) oRows).toReal *
          (if shrunkBadOut f₁ j₀ ⟨z, iRows⟩ oRows then 1 else 0)) ≤ C := by
    have hsimp :
        (∑ oRows : Fin (outHashLen w₁) → BitString (inputHashOutLen w₁ out₁),
          ((PMF.uniformOfFintype _) oRows).toReal *
            (if shrunkBadOut f₁ j₀ ⟨z, iRows⟩ oRows then 1 else 0)) =
        ∑ oRows : Fin (outHashLen w₁) → BitString (inputHashOutLen w₁ out₁),
          if shrunkBadOut f₁ j₀ ⟨z, iRows⟩ oRows then
            ((PMF.uniformOfFintype _) oRows).toReal
          else 0 := by
      refine sum_congr rfl fun oRows _ => ?_
      by_cases hb : shrunkBadOut f₁ j₀ ⟨z, iRows⟩ oRows <;> simp [hb]
    rw [hsimp]
    refine (shrunkHashFin_false_positive_le f₁ j₀ ⟨z, iRows⟩).trans ?_
    calc
      (#(univ.image (inputHashFin f₁ j₀)) : ℝ) / (2 : ℝ) ^ (outHashLen w₁)
        ≤ ((((PMF.uniformOfFintype (BitString w₁)).toOuterMeasure
              {z | realSampleEntropy f₁ z ≤ K_min}).toReal +
            (2 : ℝ) ^ ((min j₀ w₁ : ℝ) - K_min)) * (2 : ℝ) ^ (inputHashInLen w₁)) /
            (2 : ℝ) ^ (outHashLen w₁) := by
            gcongr; exact card_image_inputHashFin_le f₁ j₀ K_min
      _ = C := by rw [mul_div_assoc, hpow_ratio, mul_comm]
  calc
    shrunkExpect w₁ out₁ (fun z iRows oRows =>
        if shrunkBadOut f₁ j₀ ⟨z, iRows⟩ oRows then 1 else 0)
      ≤ ∑ z : BitString w₁, ((PMF.uniformOfFintype (BitString w₁)) z).toReal *
          ∑ iRows : Fin w₁ → BitString w₁,
            ((PMF.uniformOfFintype (Fin w₁ → BitString w₁)) iRows).toReal * C := by
        dsimp only [shrunkExpect]
        gcongr with z _ iRows _
        exact hper_w z iRows
    _ = C := by simp only [← sum_mul, PMF.sum_toReal, one_mul]

/-- **Combined concrete bound for `[HHRVW2020]`, Sections 5.1.2–5.1.3, Lemmas 5.4 and 5.5
(pp. 27–29)**: when $1 \le n_1(n)$, random-input collision success on `shrunkHashEvalWord` at
truncation parameter $j(n)$ is bounded by the $L_1$-escape probability of
`shrunkHashEscapeInverter` plus the two concentration tails (`A_max ≤ log₂ |L₁(z)|` and
`realSampleEntropy f₁ z ≤ K_min`) and the two universal-hash error terms
`2 ^ (A_max - min (j n) (n₁ n))` and `2 * 2 ^ (min (j n) (n₁ n) - K_min)`. -/
theorem shrunkHash_randomCollision_le (n₁ m₁ j : ℕ → ℕ)
    (evalWord₁ : ℕ → List Bool → List Bool)
    (L₁ : (n : ℕ) → BitString (n₁ n) → Finset (BitString (n₁ n)))
    (A : ℕ → List Bool → ProbComp (List Bool)) (n : ℕ)
    (hn₁ : 1 ≤ n₁ n)
    (hlen₁ : ∀ u : List Bool, u.length = n₁ n → (evalWord₁ n u).length = m₁ n)
    (A_max K_min : ℝ) :
    let f₁ := wordToFinMap (n₁ n) (m₁ n) (evalWord₁ n)
    (Game.succProbability (ProbComp.eval
      (randomCollisionGame
        (fun k => shrunkHashEvalWord (n₁ k) (m₁ k) (evalWord₁ k) (j k))
        (fun k => shrunkHashInLen (n₁ k) (m₁ k)) A n)) : ℝ) ≤
      (Game.succProbability (ProbComp.eval
        (accessibleEscapeGame evalWord₁ n₁ L₁ (shrunkHashEscapeInverter n₁ m₁ A) n)) : ℝ) +
      ((PMF.uniformOfFintype (BitString (n₁ n))).toOuterMeasure
        {z | A_max ≤ Real.logb 2 #(L₁ n z)}).toReal +
      (2 : ℝ) ^ (A_max - (min (j n) (n₁ n) : ℝ)) +
      2 * (((PMF.uniformOfFintype (BitString (n₁ n))).toOuterMeasure
          {z | realSampleEntropy f₁ z ≤ K_min}).toReal +
        (2 : ℝ) ^ ((min (j n) (n₁ n) : ℝ) - K_min)) := by
  intro f₁
  classical
  let w₁ := n₁ n
  let out₁ := m₁ n
  let j₀ := j n
  rw [shrunkHash_randomCollision_succProbability_eq n₁ m₁ j evalWord₁ A n,
    shrunkHash_escape_succProbability_eq n₁ m₁ evalWord₁ L₁ A n]
  have hbadIn := shrunkBadIn_sum_le (out₁ := out₁) (j₀ := j₀) f₁ (L₁ n) A_max
  have hbadOut := shrunkBadOut_sum_le (j₀ := j₀) hn₁ f₁ K_min
  have hle :
      shrunkExpect w₁ out₁ (fun z iRows oRows =>
        ((ProbComp.eval (A n (ShrunkHashInput.mk ⟨z, iRows⟩ oRows).packWord) >>= fun raw =>
          PMF.pure (decide (shrunkCollPred w₁ out₁ j₀ (evalWord₁ n)
            ⟨⟨z, iRows⟩, oRows⟩ raw))) true).toReal) ≤
      shrunkExpect w₁ out₁ (fun z iRows oRows =>
        ((ProbComp.eval (A n (ShrunkHashInput.mk ⟨z, iRows⟩ oRows).packWord) >>= fun raw =>
            PMF.pure (decide (shrunkEscPred w₁ (evalWord₁ n) (L₁ n) z raw))) true).toReal +
          (if shrunkBadIn f₁ j₀ (L₁ n) z iRows then 1 else 0) +
          (if shrunkBadOut f₁ j₀ ⟨z, iRows⟩ oRows then 1 else 0)) := by
    dsimp only [shrunkExpect]
    gcongr with z _ iRows _ oRows _
    exact shrunkHash_pointwise_toReal_le (evalWord₁ n) (L₁ n) hlen₁ _ z iRows oRows
  have hsplit :
      shrunkExpect w₁ out₁ (fun z iRows oRows =>
        ((ProbComp.eval (A n (ShrunkHashInput.mk ⟨z, iRows⟩ oRows).packWord) >>= fun raw =>
            PMF.pure (decide (shrunkEscPred w₁ (evalWord₁ n) (L₁ n) z raw))) true).toReal +
          (if shrunkBadIn f₁ j₀ (L₁ n) z iRows then 1 else 0) +
          (if shrunkBadOut f₁ j₀ ⟨z, iRows⟩ oRows then 1 else 0)) =
      shrunkExpect w₁ out₁ (fun z iRows oRows =>
        ((ProbComp.eval (A n (ShrunkHashInput.mk ⟨z, iRows⟩ oRows).packWord) >>= fun raw =>
          PMF.pure (decide (shrunkEscPred w₁ (evalWord₁ n) (L₁ n) z raw))) true).toReal) +
      shrunkExpect w₁ out₁ (fun z iRows _ => if shrunkBadIn f₁ j₀ (L₁ n) z iRows then 1 else 0) +
      shrunkExpect w₁ out₁ (fun z iRows oRows =>
        if shrunkBadOut f₁ j₀ ⟨z, iRows⟩ oRows then 1 else 0) := by
    simp only [shrunkExpect, mul_add, sum_add_distrib]
  linarith [hle, hsplit, hbadIn, hbadOut]

end Cslib.Crypto
