/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.HashFamily
public import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Roots

/-!
# Polynomial-evaluation hashes for variable-length messages

Over a finite field `F`, a message `m = (m₁, …, m_{ℓ'-1})` of length less than `ℓ` is hashed with a
key `k ∈ F` by appending a field element that encodes its length and evaluating a polynomial with
these `ℓ'` coefficients at `k` ([KatzLindell2020], Section 4.5.2). The four coefficient layouts
studied there are:

* `Cslib.Crypto.PolynomialEvaluation.hash`: `m₁ X ^ ℓ' + ⋯ + m_{ℓ'} X`, the layout of
  [KatzLindell2020], Theorem 4.17, which is `ℓ / |F|`-difference universal whenever the length
  encoding is injective.
* `Cslib.Crypto.PolynomialEvaluation.fixedTopHash`: `m₁ X ^ ℓ + ⋯ + m_{ℓ'} X ^ (ℓ - ℓ' + 1)`
  ([KatzLindell2020], Exercise 4.22(a)).
* `Cslib.Crypto.PolynomialEvaluation.constantTermHash`: `m₁ X ^ (ℓ' - 1) + ⋯ + m_{ℓ'}`
  ([KatzLindell2020], Exercise 4.22(b)).
* `Cslib.Crypto.PolynomialEvaluation.ascendingHash`: `m₁ X + ⋯ + m_{ℓ'} X ^ ℓ'`
  ([KatzLindell2020], Exercise 4.22(c)).

Difference universality is `Cslib.Probability.IsDeltaUniversalHash` for a uniform key, the
Δ-universal property of [KatzLindell2020], Definition 4.14. Every layout without a constant term
yields polynomials of degree at most `ℓ`, so it is `ℓ / |F|`-difference universal as soon as
distinct messages give distinct polynomials (`isDeltaUniversalHash_of_polynomial`). The exercise
layouts differ in when that happens:

* layouts (a) and (c) are injective, hence `ℓ / |F|`-difference universal, when the encoding is
  injective and never sends a positive length to zero; if the length `1` is sent to zero, the
  messages `[]` and `[e 0]` collide under every key;
* layout (b) has a constant term and fails for every encoding: the hashes of `[]` and `[0]` differ
  by the key-independent constant `e 0 - e 1`.

Every evaluation is computed by Horner's rule.

## Main definitions

* `Cslib.Crypto.PolynomialEvaluation.coefficients`: the message with its length code appended.
* `Cslib.Crypto.PolynomialEvaluation.ascendingEval`: evaluate `c₁ X + c₂ X ^ 2 + ⋯ + c_t X ^ t`.

## Main results

* `Cslib.Crypto.PolynomialEvaluation.isDeltaUniversalHash_hash`: [KatzLindell2020], Theorem 4.17.
* `Cslib.Crypto.PolynomialEvaluation.isDeltaUniversalHash_fixedTopHash`,
  `Cslib.Crypto.PolynomialEvaluation.not_isDeltaUniversalHash_fixedTopHash`: Exercise 4.22(a).
* `Cslib.Crypto.PolynomialEvaluation.not_isDeltaUniversalHash_constantTermHash`: Exercise 4.22(b).
* `Cslib.Crypto.PolynomialEvaluation.isDeltaUniversalHash_ascendingHash`,
  `Cslib.Crypto.PolynomialEvaluation.not_isDeltaUniversalHash_ascendingHash`: Exercise 4.22(c).

## References

* [J. Katz, Y. Lindell, *Introduction to Modern Cryptography*, 3rd ed.][KatzLindell2020],
  Section 4.5.2, printed p. 131, and Exercise 4.22, printed p. 143.
-/

public section

namespace Cslib.Crypto.PolynomialEvaluation

open Cslib.Probability Polynomial
open scoped ENNReal

variable {F : Type*} [Field F] {ℓ : ℕ}

/-- Messages of length less than `ℓ`, the set `F^{<ℓ}` of [KatzLindell2020], Section 4.5.2. -/
abbrev Message (F : Type*) (ℓ : ℕ) := {m : List F // m.length < ℓ}

/-- The coefficient list `(m₁, …, m_{ℓ'-1}, e (ℓ' - 1))` of a message: the message followed by the
encoding of its length. -/
@[expose]
def coefficients (encodeLength : Fin ℓ → F) (m : Message F ℓ) : List F :=
  m.1 ++ [encodeLength ⟨m.1.length, m.2⟩]

/-- Horner evaluation of `c₁ X + c₂ X ^ 2 + ⋯ + c_t X ^ t` at `k`: the coefficient list starts at
the linear term, so there is no constant term. -/
@[expose]
def ascendingEval (k : F) : List F → F
  | [] => 0
  | c :: cs => k * (c + ascendingEval k cs)

/-- The hash of [KatzLindell2020], Theorem 4.17: `m₁ k ^ ℓ' + ⋯ + m_{ℓ'} k`. -/
@[expose]
def hash (encodeLength : Fin ℓ → F) (k : F) (m : Message F ℓ) : F :=
  ascendingEval k (coefficients encodeLength m).reverse

/-- Exercise 4.22(a): `m₁ k ^ ℓ + ⋯ + m_{ℓ'} k ^ (ℓ - ℓ' + 1)`, the hash of Theorem 4.17 shifted so
that the first coefficient always multiplies `k ^ ℓ`. -/
@[expose]
def fixedTopHash (encodeLength : Fin ℓ → F) (k : F) (m : Message F ℓ) : F :=
  k ^ (ℓ - (m.1.length + 1)) * hash encodeLength k m

/-- Exercise 4.22(b): `m₁ k ^ (ℓ' - 1) + ⋯ + m_{ℓ'}`, with the length code as constant term. -/
@[expose]
def constantTermHash (encodeLength : Fin ℓ → F) (k : F) (m : Message F ℓ) : F :=
  (coefficients encodeLength m).foldl (fun acc c => acc * k + c) 0

/-- Exercise 4.22(c): `m₁ k + m₂ k ^ 2 + ⋯ + m_{ℓ'} k ^ ℓ'`. -/
@[expose]
def ascendingHash (encodeLength : Fin ℓ → F) (k : F) (m : Message F ℓ) : F :=
  ascendingEval k (coefficients encodeLength m)

/-! ### Polynomials without constant term -/

/-- A family of polynomials without constant term, of degree at most `ℓ`, that separates its
inputs is `ℓ / |F|`-difference universal: a difference `d` of two distinct evaluations occurs only
at the roots of the nonzero polynomial `P x - P x' - d`. -/
theorem isDeltaUniversalHash_of_polynomial [Fintype F] {X : Type*}
    (P : X → F[X]) (hinj : Function.Injective P) (hcoeff : ∀ x, (P x).coeff 0 = 0)
    (hdeg : ∀ x, (P x).natDegree ≤ ℓ) :
    IsDeltaUniversalHash (PMF.uniformOfFintype F) (fun k x => (P x).eval k)
      (ℓ / Fintype.card F) := by
  classical
  refine IsDeltaUniversalHash.of_card_le fun x x' hx d => ?_
  have hD : P x - P x' - C d ≠ 0 := fun h0 => by
    have hc := congrArg (coeff · 0) h0
    simp only [coeff_sub, coeff_C_zero, hcoeff, sub_zero, zero_sub, coeff_zero, neg_eq_zero] at hc
    subst hc
    exact sub_ne_zero.mpr (hinj.ne hx) (by simpa using h0)
  calc (Finset.univ.filter fun k => (P x).eval k - (P x').eval k = d).card
      ≤ (P x - P x' - C d).roots.toFinset.card := by
        refine Finset.card_le_card fun k hk => ?_
        rw [Multiset.mem_toFinset, mem_roots hD, IsRoot.def, eval_sub, eval_sub, eval_C,
          sub_eq_zero]
        exact (Finset.mem_filter.mp hk).2
    _ ≤ (P x - P x' - C d).roots.card := Multiset.toFinset_card_le _
    _ ≤ (P x - P x' - C d).natDegree := card_roots' _
    _ ≤ ℓ := (natDegree_sub_le _ _).trans <| max_le
        ((natDegree_sub_le _ _).trans (max_le (hdeg x) (hdeg x')))
        (by rw [natDegree_C]; exact Nat.zero_le _)

/-- A family that sends two distinct inputs to evaluations with a key-independent difference is
not `ε`-difference universal for any `ε < 1`. -/
theorem not_isDeltaUniversalHash_of_sub_const [Fintype F] {X : Type*} {h : F → X → F}
    {x x' : X} (hx : x ≠ x') (d : F) (hd : ∀ k, h k x - h k x' = d) {ε : ℝ≥0∞} (hε : ε < 1) :
    ¬ IsDeltaUniversalHash (PMF.uniformOfFintype F) h ε := fun hh => by
  have hset : {k | h k x - h k x' = d} = Set.univ := Set.eq_univ_of_forall hd
  have := hh x x' hx d
  rw [hset, (PMF.toOuterMeasure_apply_eq_one_iff _ _).mpr (Set.subset_univ _)] at this
  exact absurd (this.trans_lt hε) (lt_irrefl 1)

/-! ### The coefficient polynomial -/

/-- The polynomial `c₁ X + c₂ X ^ 2 + ⋯ + c_t X ^ t` evaluated by `ascendingEval`. -/
private noncomputable def ascendingPoly : List F → F[X]
  | [] => 0
  | c :: cs => X * (C c + ascendingPoly cs)

private theorem eval_ascendingPoly (k : F) (cs : List F) :
    (ascendingPoly cs).eval k = ascendingEval k cs := by
  induction cs with
  | nil => simp [ascendingPoly, ascendingEval]
  | cons c cs ih => simp [ascendingPoly, ascendingEval, ih]

private theorem coeff_zero_ascendingPoly (cs : List F) : (ascendingPoly cs).coeff 0 = 0 := by
  cases cs <;> simp [ascendingPoly]

private theorem coeff_one_ascendingPoly (c : F) (cs : List F) :
    (ascendingPoly (c :: cs)).coeff 1 = c := by
  simp [ascendingPoly, coeff_zero_ascendingPoly]

private theorem natDegree_ascendingPoly_le (cs : List F) :
    (ascendingPoly cs).natDegree ≤ cs.length := by
  induction cs with
  | nil => simp [ascendingPoly]
  | cons c cs ih =>
    refine (natDegree_mul_le (p := X)).trans ?_
    have hsum := (natDegree_add_le (C c) (ascendingPoly cs)).trans
      (max_le (by rw [natDegree_C]; exact Nat.zero_le _) ih)
    have hX := natDegree_X_le (R := F)
    simp only [List.length_cons]
    omega

private theorem ascendingPoly_append_singleton (cs : List F) (a : F) :
    ascendingPoly (cs ++ [a]) = ascendingPoly cs + C a * X ^ (cs.length + 1) := by
  induction cs with
  | nil => simp [ascendingPoly]
  | cons c cs ih =>
    simp only [List.cons_append, ascendingPoly, ih, List.length_cons]
    ring

/-- Coefficient lists of equal length with equal polynomials are equal. -/
private theorem ascendingPoly_inj {cs cs' : List F} (hlen : cs.length = cs'.length)
    (h : ascendingPoly cs = ascendingPoly cs') : cs = cs' := by
  induction cs generalizing cs' with
  | nil => exact (List.length_eq_zero_iff.mp hlen.symm).symm
  | cons c cs ih =>
    obtain _ | ⟨c', cs'⟩ := cs'
    · simp at hlen
    have hsum := mul_left_cancel₀ X_ne_zero h
    have hc : c = c' := by
      simpa [coeff_zero_ascendingPoly] using congrArg (coeff · 0) hsum
    subst hc
    rw [ih (by simpa using hlen) (add_left_cancel hsum)]

omit [Field F] in
private theorem reverse_coefficients (encodeLength : Fin ℓ → F) (m : Message F ℓ) :
    (coefficients encodeLength m).reverse =
      encodeLength ⟨m.1.length, m.2⟩ :: m.1.reverse := by
  simp [coefficients]

omit [Field F] in
/-- Messages with the same length and the same coefficients are equal. -/
private theorem message_eq_of_coefficients (encodeLength : Fin ℓ → F) {m m' : Message F ℓ}
    (h : coefficients encodeLength m = coefficients encodeLength m') : m = m' :=
  Subtype.ext (List.append_inj_left' h rfl)

omit [Field F] in
private theorem length_coefficients (encodeLength : Fin ℓ → F) (m : Message F ℓ) :
    (coefficients encodeLength m).length = m.1.length + 1 := by
  simp [coefficients]

/-! ### Theorem 4.17 -/

/-- The polynomial of [KatzLindell2020], Theorem 4.17. -/
private noncomputable def hashPoly (encodeLength : Fin ℓ → F) (m : Message F ℓ) : F[X] :=
  ascendingPoly (coefficients encodeLength m).reverse

private theorem coeff_one_hashPoly (encodeLength : Fin ℓ → F) (m : Message F ℓ) :
    (hashPoly encodeLength m).coeff 1 = encodeLength ⟨m.1.length, m.2⟩ := by
  rw [hashPoly, reverse_coefficients, coeff_one_ascendingPoly]

private theorem natDegree_hashPoly_le (encodeLength : Fin ℓ → F) (m : Message F ℓ) :
    (hashPoly encodeLength m).natDegree ≤ m.1.length + 1 := by
  simpa only [hashPoly, List.length_reverse, length_coefficients] using
    natDegree_ascendingPoly_le (coefficients encodeLength m).reverse

/-- Two messages of the same length with the same polynomial are equal. -/
private theorem eq_of_hashPoly_eq (encodeLength : Fin ℓ → F) {m m' : Message F ℓ}
    (hlen : m.1.length = m'.1.length) (h : hashPoly encodeLength m = hashPoly encodeLength m') :
    m = m' := by
  refine message_eq_of_coefficients encodeLength (List.reverse_injective ?_)
  exact ascendingPoly_inj (by simp [length_coefficients, hlen]) h

private theorem hashPoly_injective {encodeLength : Fin ℓ → F}
    (hencode : Function.Injective encodeLength) :
    Function.Injective (hashPoly encodeLength) := fun m m' h => by
  have hlen : m.1.length = m'.1.length := by
    have hc := congrArg (coeff · 1) h
    simp only [coeff_one_hashPoly] at hc
    exact congrArg Fin.val (hencode hc)
  exact eq_of_hashPoly_eq encodeLength hlen h

/-- **[KatzLindell2020], Theorem 4.17.** For an injective length encoding, the polynomial hash
`m₁ k ^ ℓ' + ⋯ + m_{ℓ'} k` on `F^{<ℓ}` is `ℓ / |F|`-difference universal. -/
theorem isDeltaUniversalHash_hash [Fintype F] {encodeLength : Fin ℓ → F}
    (hencode : Function.Injective encodeLength) :
    IsDeltaUniversalHash (PMF.uniformOfFintype F) (hash encodeLength) (ℓ / Fintype.card F) := by
  have h := isDeltaUniversalHash_of_polynomial (hashPoly encodeLength)
    (hashPoly_injective hencode) (fun _ => coeff_zero_ascendingPoly _)
    (fun m => (natDegree_hashPoly_le encodeLength m).trans m.2)
  have heq : hash encodeLength = fun k m => (hashPoly encodeLength m).eval k := by
    funext k m
    rw [hashPoly, eval_ascendingPoly, hash]
  rwa [heq]

/-! ### Exercise 4.22(a) -/

/-- The polynomial of Exercise 4.22(a). -/
private noncomputable def fixedTopPoly (encodeLength : Fin ℓ → F) (m : Message F ℓ) : F[X] :=
  X ^ (ℓ - (m.1.length + 1)) * hashPoly encodeLength m

/-- The lowest coefficient of the Exercise 4.22(a) polynomial sits at `ℓ - |m|`. -/
private theorem coeff_fixedTopPoly (encodeLength : Fin ℓ → F) (m : Message F ℓ) (j : ℕ)
    (hj : j ≤ ℓ - (m.1.length + 1)) : (fixedTopPoly encodeLength m).coeff j = 0 := by
  rw [fixedTopPoly, coeff_X_pow_mul']
  split_ifs with h
  · rw [show j - (ℓ - (m.1.length + 1)) = 0 by omega, hashPoly, coeff_zero_ascendingPoly]
  · rfl

private theorem coeff_fixedTopPoly_length (encodeLength : Fin ℓ → F) (m : Message F ℓ) :
    (fixedTopPoly encodeLength m).coeff (ℓ - m.1.length) = encodeLength ⟨m.1.length, m.2⟩ := by
  have hm := m.2
  rw [fixedTopPoly, coeff_X_pow_mul']
  simp only [show ℓ - (m.1.length + 1) ≤ ℓ - m.1.length by omega, ↓reduceIte,
    show ℓ - m.1.length - (ℓ - (m.1.length + 1)) = 1 by omega, coeff_one_hashPoly]

/-- A longer message has a nonzero coefficient where a shorter one has none. -/
private theorem fixedTopPoly_ne_of_lt {encodeLength : Fin ℓ → F}
    (hpos : ∀ d : Fin ℓ, d.val ≠ 0 → encodeLength d ≠ 0) {m m' : Message F ℓ}
    (hlt : m.1.length < m'.1.length) : fixedTopPoly encodeLength m ≠ fixedTopPoly encodeLength m' :=
  fun h => by
    have hc := congrArg (coeff · (ℓ - m'.1.length)) h
    have hm' := m'.2
    simp only [coeff_fixedTopPoly_length,
      coeff_fixedTopPoly encodeLength m (ℓ - m'.1.length) (by omega)] at hc
    exact hpos _ (by simp only; omega) hc.symm

private theorem fixedTopPoly_injective {encodeLength : Fin ℓ → F}
    (hpos : ∀ d : Fin ℓ, d.val ≠ 0 → encodeLength d ≠ 0) :
    Function.Injective (fixedTopPoly encodeLength) := fun m m' h => by
  rcases lt_trichotomy m.1.length m'.1.length with hlt | hlen | hgt
  · exact absurd h (fixedTopPoly_ne_of_lt hpos hlt)
  · refine eq_of_hashPoly_eq encodeLength hlen
      (mul_left_cancel₀ (pow_ne_zero (ℓ - (m.1.length + 1)) X_ne_zero) ?_)
    rw [fixedTopPoly, fixedTopPoly, ← hlen] at h
    exact h
  · exact absurd h.symm (fixedTopPoly_ne_of_lt hpos hgt)

/-- **[KatzLindell2020], Exercise 4.22(a), positive part.** If the length encoding sends no
positive length to zero, the layout `m₁ k ^ ℓ + ⋯ + m_{ℓ'} k ^ (ℓ - ℓ' + 1)` is
`ℓ / |F|`-difference universal. -/
theorem isDeltaUniversalHash_fixedTopHash [Fintype F]
    {encodeLength : Fin ℓ → F} (hpos : ∀ d : Fin ℓ, d.val ≠ 0 → encodeLength d ≠ 0) :
    IsDeltaUniversalHash (PMF.uniformOfFintype F) (fixedTopHash encodeLength)
      (ℓ / Fintype.card F) := by
  have hdeg (m : Message F ℓ) : (fixedTopPoly encodeLength m).natDegree ≤ ℓ := by
    have hm := m.2
    have h1 := natDegree_hashPoly_le encodeLength m
    have h2 := natDegree_X_pow_le (R := F) (ℓ - (m.1.length + 1))
    exact natDegree_mul_le.trans (by omega)
  have h := isDeltaUniversalHash_of_polynomial (fixedTopPoly encodeLength)
    (fixedTopPoly_injective hpos) (fun m => coeff_fixedTopPoly encodeLength m 0 (Nat.zero_le _))
    hdeg
  have heq : fixedTopHash encodeLength = fun k m => (fixedTopPoly encodeLength m).eval k := by
    funext k m
    rw [fixedTopPoly, hashPoly, eval_mul, eval_pow, eval_X, eval_ascendingPoly, fixedTopHash, hash]
  rwa [heq]

/-- The empty message, available when `0 < ℓ`. -/
private def emptyMessage (h : 1 < ℓ) : Message F ℓ := ⟨[], by simp only [List.length_nil]; omega⟩

/-- A one-element message, available when `1 < ℓ`. -/
private def singletonMessage (h : 1 < ℓ) (a : F) : Message F ℓ := ⟨[a], by simpa using h⟩

/-- **[KatzLindell2020], Exercise 4.22(a), negative part.** If the length `1` is encoded as zero
and `ℓ ≥ 2`, the messages `[]` and `[e 0]` collide under every key, so the layout is not
`ε`-difference universal for any `ε < 1`; in particular not `ℓ / |F|`-difference universal when
`ℓ < |F|`. -/
theorem not_isDeltaUniversalHash_fixedTopHash [Fintype F] {encodeLength : Fin ℓ → F}
    (h1 : 1 < ℓ) (hzero : encodeLength ⟨1, h1⟩ = 0) {ε : ℝ≥0∞} (hε : ε < 1) :
    ¬ IsDeltaUniversalHash (PMF.uniformOfFintype F) (fixedTopHash encodeLength) ε := by
  refine not_isDeltaUniversalHash_of_sub_const (x := emptyMessage h1)
    (x' := singletonMessage h1 (encodeLength ⟨0, by omega⟩))
    (by simp [emptyMessage, singletonMessage]) 0 (fun k => ?_) hε
  have hpow : k ^ (ℓ - 1) = k ^ (ℓ - 2) * k := by
    rw [← pow_succ]; congr 1; omega
  simp [fixedTopHash, hash, coefficients, ascendingEval, emptyMessage, singletonMessage, hzero,
    hpow]
  ring

/-! ### Exercise 4.22(b) -/

/-- **[KatzLindell2020], Exercise 4.22(b).** For `ℓ ≥ 2` and every length encoding, the layout
`m₁ k ^ (ℓ' - 1) + ⋯ + m_{ℓ'}` sends `[]` and `[0]` to hashes whose difference is the
key-independent constant `e 0 - e 1`, so it is not `ε`-difference universal for any `ε < 1`. -/
theorem not_isDeltaUniversalHash_constantTermHash [Fintype F] (encodeLength : Fin ℓ → F)
    (h1 : 1 < ℓ) {ε : ℝ≥0∞} (hε : ε < 1) :
    ¬ IsDeltaUniversalHash (PMF.uniformOfFintype F) (constantTermHash encodeLength) ε :=
  not_isDeltaUniversalHash_of_sub_const (x := emptyMessage h1) (x' := singletonMessage h1 0)
    (by simp [emptyMessage, singletonMessage])
    (encodeLength ⟨0, by omega⟩ - encodeLength ⟨1, h1⟩)
    (fun k => by simp [constantTermHash, coefficients, emptyMessage, singletonMessage]) hε

/-! ### Exercise 4.22(c) -/

/-- The polynomial of Exercise 4.22(c). -/
private noncomputable def ascendingHashPoly (encodeLength : Fin ℓ → F) (m : Message F ℓ) : F[X] :=
  ascendingPoly (coefficients encodeLength m)

private theorem ascendingHashPoly_eq (encodeLength : Fin ℓ → F) (m : Message F ℓ) :
    ascendingHashPoly encodeLength m =
      ascendingPoly m.1 + C (encodeLength ⟨m.1.length, m.2⟩) * X ^ (m.1.length + 1) :=
  ascendingPoly_append_singleton _ _

/-- The top coefficient of the Exercise 4.22(c) polynomial is the length code. -/
private theorem coeff_ascendingHashPoly_length (encodeLength : Fin ℓ → F) (m : Message F ℓ) :
    (ascendingHashPoly encodeLength m).coeff (m.1.length + 1) =
      encodeLength ⟨m.1.length, m.2⟩ := by
  have hdeg := natDegree_ascendingPoly_le m.1
  rw [ascendingHashPoly_eq, coeff_add, coeff_eq_zero_of_natDegree_lt (by omega), coeff_C_mul,
    coeff_X_pow_self, mul_one, zero_add]

/-- The Exercise 4.22(c) polynomial has degree at most `|m| + 1`. -/
private theorem coeff_ascendingHashPoly_of_lt (encodeLength : Fin ℓ → F) (m : Message F ℓ)
    {j : ℕ} (hj : m.1.length + 1 < j) : (ascendingHashPoly encodeLength m).coeff j = 0 := by
  have hdeg := natDegree_ascendingPoly_le (coefficients encodeLength m)
  rw [length_coefficients] at hdeg
  exact coeff_eq_zero_of_natDegree_lt (by rw [ascendingHashPoly]; omega)

private theorem ascendingHashPoly_ne_of_lt {encodeLength : Fin ℓ → F}
    (hpos : ∀ d : Fin ℓ, d.val ≠ 0 → encodeLength d ≠ 0) {m m' : Message F ℓ}
    (hlt : m.1.length < m'.1.length) :
    ascendingHashPoly encodeLength m ≠ ascendingHashPoly encodeLength m' := fun h => by
  have hc := congrArg (coeff · (m'.1.length + 1)) h
  simp only [coeff_ascendingHashPoly_of_lt encodeLength m (j := m'.1.length + 1) (by omega),
    coeff_ascendingHashPoly_length] at hc
  exact hpos _ (by simp only; omega) hc.symm

private theorem ascendingHashPoly_injective {encodeLength : Fin ℓ → F}
    (hpos : ∀ d : Fin ℓ, d.val ≠ 0 → encodeLength d ≠ 0) :
    Function.Injective (ascendingHashPoly encodeLength) := fun m m' h => by
  rcases lt_trichotomy m.1.length m'.1.length with hlt | hlen | hgt
  · exact absurd h (ascendingHashPoly_ne_of_lt hpos hlt)
  · exact message_eq_of_coefficients encodeLength
      (ascendingPoly_inj (by simp [length_coefficients, hlen]) h)
  · exact absurd h.symm (ascendingHashPoly_ne_of_lt hpos hgt)

/-- **[KatzLindell2020], Exercise 4.22(c), positive part.** If the length encoding sends no
positive length to zero, the layout `m₁ k + ⋯ + m_{ℓ'} k ^ ℓ'` is `ℓ / |F|`-difference
universal. -/
theorem isDeltaUniversalHash_ascendingHash [Fintype F]
    {encodeLength : Fin ℓ → F} (hpos : ∀ d : Fin ℓ, d.val ≠ 0 → encodeLength d ≠ 0) :
    IsDeltaUniversalHash (PMF.uniformOfFintype F) (ascendingHash encodeLength)
      (ℓ / Fintype.card F) := by
  have hdeg (m : Message F ℓ) : (ascendingHashPoly encodeLength m).natDegree ≤ ℓ := by
    have h := natDegree_ascendingPoly_le (coefficients encodeLength m)
    rw [length_coefficients] at h
    exact h.trans m.2
  have h := isDeltaUniversalHash_of_polynomial (ascendingHashPoly encodeLength)
    (ascendingHashPoly_injective hpos) (fun _ => coeff_zero_ascendingPoly _) hdeg
  have heq : ascendingHash encodeLength =
      fun k m => (ascendingHashPoly encodeLength m).eval k := by
    funext k m
    rw [ascendingHashPoly, eval_ascendingPoly, ascendingHash]
  rwa [heq]

/-- **[KatzLindell2020], Exercise 4.22(c), negative part.** If the length `1` is encoded as zero
and `ℓ ≥ 2`, the messages `[]` and `[e 0]` collide under every key. -/
theorem not_isDeltaUniversalHash_ascendingHash [Fintype F] {encodeLength : Fin ℓ → F}
    (h1 : 1 < ℓ) (hzero : encodeLength ⟨1, h1⟩ = 0) {ε : ℝ≥0∞} (hε : ε < 1) :
    ¬ IsDeltaUniversalHash (PMF.uniformOfFintype F) (ascendingHash encodeLength) ε :=
  not_isDeltaUniversalHash_of_sub_const (x := emptyMessage h1)
    (x' := singletonMessage h1 (encodeLength ⟨0, by omega⟩))
    (by simp [emptyMessage, singletonMessage]) 0
    (fun k => by
      simp [ascendingHash, coefficients, ascendingEval, emptyMessage, singletonMessage, hzero]) hε

end Cslib.Crypto.PolynomialEvaluation
