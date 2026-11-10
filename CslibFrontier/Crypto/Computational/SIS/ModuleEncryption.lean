/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.SIS.Module
import CslibFrontier.Languages.Probabilistic.Norm
import CslibFrontier.Probability.PMF
import CslibFrontier.Probability.PMF.Uniform
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Ring-LWE and Module-LWE Public-Key Encryption

This module formalizes a Module-LWE public-key encryption scheme over the negacyclic polynomial
ring `R_q = ℤ_q[X] / (X^n + 1)` and modules `R_q^k` ([Regev2009], [LyubashevskyPeikertRegev2010],
[DucasEtAl2018]), in which the public key is a Module-LWE sample and the ciphertext is a second
Module-LWE sample masked by the encoded message:

1. **Commutative ring structure of negacyclic multiplication (`negacyclicMul_comm`,
   `rotMatrix_negacyclicMul`, `negacyclicMul_assoc`, `innerPoly`)**:
   Over any commutative ring `R`, negacyclic polynomial multiplication `negacyclicMul` is
   commutative and associative, `rotMatrix` is multiplicative (`rotMatrix (negacyclicMul a b) =
   rotMatrix a * rotMatrix b`), and the polynomial inner product
   `innerPoly b r = ∑ j, negacyclicMul (b j) (r j)` satisfies the adjoint identity
   `innerPoly (moduleSISMap A s) r = innerPoly (moduleSISMap Aᵀ r) s`
   (`innerPoly_moduleSISMap_eq`).
2. **Polynomial-ring message encoding and centered-lift rounding (`encodePolyMsg`,
   `decodePolyMsg`, `decodePolyMsg_encodePolyMsg_add_noise`)**:
   A message bit-vector `m : Fin n → Bool` is encoded into `Fin n → ZMod q` by mapping
   `false ↦ 0` and `true ↦ ⌊q / 2⌋`, and decoded by lifting each coefficient to its centered
   representative in `(-q/2, q/2]` (`GeneralSIS.liftCentered`) and testing whether its magnitude
   exceeds `⌊q / 4⌋`. Whenever `4 * B + 2 < q` and every coefficient of an integer error
   polynomial `err` has magnitude at most `B`, decoding `encodePolyMsg q m + err` recovers `m`
   (`decodePolyMsg_encodePolyMsg_add_noise`).
3. **Module-LWE public-key encryption and bounded-noise correctness (`moduleLWEKeyGen`,
   `moduleLWEEncrypt`, `moduleLWEDecrypt`, `moduleLWEDecrypt_moduleLWEEncrypt_eq`)**:
   - Key generation maps `(A, s, e)` to the public key `(A, b) = (A, moduleSISMap A s + e)`.
   - Encryption of `m : Fin n → Bool` under `pk = (A, b)` with ephemeral secret `r` and noises
     `(e₁, e₂)` outputs `(u, v) = (moduleSISMap Aᵀ r + e₁, innerPoly b r + e₂ + encodePolyMsg q m)`.
   - Decryption under secret key `s` computes `decodePolyMsg (v - innerPoly u s)`.
   By the ring-bilinearity identity `innerPoly_moduleSISMap_add_sub`, the `A · s · r` terms cancel
   and leave `encodePolyMsg q m + (innerPoly e r - innerPoly e₁ s + e₂)`. When the centered
   coefficients of `s, r` are bounded by `B_s, B_r` and those of `e, e₁, e₂` are bounded by `B_e`
   with `4 * (k * n * B_e * B_r + k * n * B_e * B_s + B_e) + 2 < q` (in particular when
   `B_s ≤ B_r` and `4 * (2 * k * n * B_e * B_r + B_e) + 2 < q`), decryption recovers `m`
   deterministically (`moduleLWEDecrypt_moduleLWEEncrypt_eq`).
4. **Public-key pseudorandomness from `DecisionModuleLWE` and Module-LWE advantage bounds for
   ciphertexts**:
   - Replacing the honest public key `(A, A · s + e)` with a uniform pair `(A, b)` is directly an
     instance of `DecisionModuleLWE k k n q noise` (`moduleLWEPublicKeyLaw_eq_sampleLaw`,
     `publicKey_indistinguishable_of_decisionModuleLWE`).
   - Under a uniform public key `(A, b)`, stacking `b` above `Aᵀ` via `extendPublicKeyMatrix` and
     `v` above `u` via `extendCiphertext` embeds `(pk, moduleLWEEncrypt pk r e₁ e₂ m)` into a
     `(k + 1) × k` Module-LWE sample masked by `(0, Fin.cons (encodePolyMsg q m) 0)`
     (`extendCiphertext_moduleLWEEncrypt`, `uniformKeyEncryptionLaw_eq_sampleLaw_map`). Replacing
     that `(k + 1) × k` Module-LWE sample with a uniform sample yields a completely uniform
     `(pk, ct)` distribution independent of `m` (`uniformSample_mask_eq_uniform`), bounding
     single-encryption distinguishing advantage by two `ModuleLWE` advantages
     (`advantage_realEncryptionView_uniform_le`, `advantage_realEncryptionView_msg_le`).
   - The two ciphertext bounds are inequalities between `Game.advantage` values at one fixed
     `(k, n, q)`, for an arbitrary function `D` into `Game` with no efficiency condition. Only
     `publicKey_indistinguishable_of_decisionModuleLWE` has a `DecisionModuleLWE` hypothesis; this
     module does not derive `ComputationallyIndistinguishable` encryption views from it.

The statements of item 4 draw the secret `s` and the ephemeral secret `r` uniformly from `R_q^k`,
whereas the correctness theorems of item 3 assume centered bounds `B_s` and `B_r` on them. When
`0 < k * n`, bounds that hold for every `s` and `r` satisfy `q / 2 ≤ B_s` and `q / 2 ≤ B_r`, and
the hypothesis on `q` then forces `B_e = 0`, that is, `e`, `e₁` and `e₂` are zero. Hence, for
`0 < k * n` and nonzero noise, no choice of bounds makes the correctness theorems apply to every
`s` and `r` drawn in item 4.

## Main definitions

* `Cslib.Crypto.innerPoly`: polynomial inner product `∑ j, negacyclicMul (b j) (r j)` over
  `R[X] / (X^n + 1)`.
* `Cslib.Crypto.encodePolyMsg`, `Cslib.Crypto.decodePolyMsg`: `n`-bit polynomial message encoding
  and centered-lift threshold decoding modulo `q`.
* `Cslib.Crypto.ModuleLWEPublicKey`, `Cslib.Crypto.ModuleLWECiphertext`: public-key and ciphertext
  types for rank-`k` Module-LWE encryption.
* `Cslib.Crypto.moduleLWEKeyGen`, `Cslib.Crypto.moduleLWEEncrypt`,
  `Cslib.Crypto.moduleLWEDecrypt`: key generation, encryption and decryption.
* `Cslib.Crypto.moduleLWEErrorPoly`: combined decryption noise polynomial
  `innerPoly e r - innerPoly e₁ s + e₂`.
* `Cslib.Crypto.extendPublicKeyMatrix`, `Cslib.Crypto.extendCiphertext`: embedding of `(A, b)` and
  `(u, v)` into a `(k + 1) × k` Module-LWE instance.
* `Cslib.Crypto.moduleLWEPublicKeyLaw`, `Cslib.Crypto.encryptionViewOfKeyLaw`,
  `Cslib.Crypto.realEncryptionView`: explicit secret/ephemeral laws, defaulting to uniform.
* `Cslib.Crypto.uniformKeyEncryptionLaw`,
  `Cslib.Crypto.hybridEncryptionView`,
  `Cslib.Crypto.uniformEncryptionView`: public-key and encryption view distributions.

## Main results

* `Cslib.Crypto.negacyclicMul_comm`, `Cslib.Crypto.rotMatrix_negacyclicMul`,
  `Cslib.Crypto.negacyclicMul_assoc`: commutativity and associativity of negacyclic polynomial
  multiplication.
* `Cslib.Crypto.sum_abs_rotMatrix_apply`, `Cslib.Crypto.abs_negacyclicMul_le_sum_abs_mul`: rows of
  the negacyclic matrix are signed rearrangements, giving the `ℓ₁`-`ℓ∞` product bound.
* `Cslib.Crypto.innerPoly_moduleSISMap_eq`, `Cslib.Crypto.innerPoly_moduleSISMap_add_sub`:
  adjoint identity for `moduleSISMap` and noisy bilinear cancellation.
* `Cslib.Crypto.decodePolyMsg_encodePolyMsg_add_noise`: bounded-error recovery for
  `decodePolyMsg`.
* `Cslib.Crypto.moduleLWEDecrypt_moduleLWEEncrypt_eq`,
  `Cslib.Crypto.moduleLWEDecrypt_moduleLWEEncrypt_eq_of_bounds`: deterministic bounded-noise
  decryption correctness.
* `Cslib.Crypto.publicKey_indistinguishable_of_decisionModuleLWE`,
  `Cslib.Crypto.uniformKeyEncryptionLaw_eq_sampleLaw_map`,
  `Cslib.Crypto.uniformSample_mask_eq_uniform`,
  `Cslib.Crypto.advantage_realEncryptionView_uniform_le`,
  `Cslib.Crypto.advantage_realEncryptionView_msg_le`: public-key pseudorandomness under
  `DecisionModuleLWE`, and distribution identities and `ModuleLWE` advantage bounds for `(pk, ct)`
  views against an arbitrary function into `Game`.

## References

* [V. Lyubashevsky, C. Peikert, and O. Regev, *On Ideal Lattices and Learning with Errors over
  Rings*][LyubashevskyPeikertRegev2010]
* [O. Regev, *On Lattices, Learning with Errors, Random Linear Codes, and
  Cryptography*][Regev2009]
* [L. Ducas et al., *CRYSTALS-Dilithium: A Lattice-Based Digital Signature
  Scheme*][DucasEtAl2018]
-/

@[expose] public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM
open scoped _root_.Matrix ENNReal NNReal

/-! ### Part 1: Commutativity, Associativity and Bilinearity over `R[X] / (X^n + 1)` -/

/-- Index involution on `Fin n` swapping `j` with `i - j mod n` in a negacyclic convolution at
output degree `i`. -/
private def negacyclicSwap {n : ℕ} (i j : Fin n) : Fin n :=
  if h : j.val ≤ i.val then
    ⟨i.val - j.val, by omega⟩
  else
    ⟨n + i.val - j.val, by omega⟩

private lemma negacyclicSwap_val {n : ℕ} (i j : Fin n) :
    (negacyclicSwap i j).val = if j.val ≤ i.val then i.val - j.val else n + i.val - j.val := by
  unfold negacyclicSwap
  split_ifs <;> rfl

private theorem negacyclicSwap_involutive {n : ℕ} (i : Fin n) :
    Function.Involutive (negacyclicSwap i) := by
  intro j
  ext
  rw [negacyclicSwap_val, negacyclicSwap_val]
  split_ifs <;> omega

private def negacyclicSwapEquiv {n : ℕ} (i : Fin n) : Fin n ≃ Fin n where
  toFun := negacyclicSwap i
  invFun := negacyclicSwap i
  left_inv j := negacyclicSwap_involutive i j
  right_inv j := negacyclicSwap_involutive i j

@[simp]
private lemma negacyclicSwapEquiv_apply {n : ℕ} (i j : Fin n) :
    negacyclicSwapEquiv i j = negacyclicSwap i j := rfl

private lemma rotMatrix_apply_eq_negacyclicSwap {n : ℕ} {R : Type*} [Ring R]
    (a : Fin n → R) (i j : Fin n) :
    rotMatrix a i j =
      if j.val ≤ i.val then a (negacyclicSwap i j) else -a (negacyclicSwap i j) := by
  simp only [rotMatrix, Matrix.of_apply, negacyclicSwap]
  split_ifs <;> rfl

/-- **Commutativity of negacyclic polynomial multiplication**: `a * b = b * a` in
`R[X] / (X^n + 1)` over any commutative ring `R`. -/
theorem negacyclicMul_comm {n : ℕ} {R : Type*} [CommRing R] (a b : Fin n → R) :
    negacyclicMul a b = negacyclicMul b a := by
  funext i
  simp only [negacyclicMul, Matrix.mulVec, dotProduct]
  rw [← (negacyclicSwapEquiv i).sum_comp]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [negacyclicSwapEquiv_apply, rotMatrix_apply_eq_negacyclicSwap,
    negacyclicSwap_involutive i j]
  rw [negacyclicSwap_val]
  split_ifs <;> first | omega | ring

/-- Cyclic index addition `(l + k) mod n` on `Fin n`. -/
private def cyclicAdd {n : ℕ} (k l : Fin n) : Fin n :=
  if h : l.val + k.val < n then
    ⟨l.val + k.val, h⟩
  else
    ⟨l.val + k.val - n, by omega⟩

/-- Cyclic index subtraction `(j - k) mod n` on `Fin n`. -/
private def cyclicSub {n : ℕ} (k j : Fin n) : Fin n :=
  if h : k.val ≤ j.val then
    ⟨j.val - k.val, by omega⟩
  else
    ⟨n + j.val - k.val, by omega⟩

private lemma cyclicAdd_val {n : ℕ} (k l : Fin n) :
    (cyclicAdd k l).val = if l.val + k.val < n then l.val + k.val else l.val + k.val - n := by
  unfold cyclicAdd
  split_ifs <;> rfl

private lemma cyclicSub_val {n : ℕ} (k j : Fin n) :
    (cyclicSub k j).val = if k.val ≤ j.val then j.val - k.val else n + j.val - k.val := by
  unfold cyclicSub
  split_ifs <;> rfl

private theorem cyclicSub_cyclicAdd {n : ℕ} (k l : Fin n) :
    cyclicSub k (cyclicAdd k l) = l := by
  ext
  rw [cyclicSub_val, cyclicAdd_val]
  split_ifs <;> omega

private theorem cyclicAdd_cyclicSub {n : ℕ} (k j : Fin n) :
    cyclicAdd k (cyclicSub k j) = j := by
  ext
  rw [cyclicAdd_val, cyclicSub_val]
  split_ifs <;> omega

private def cyclicShiftEquiv {n : ℕ} (k : Fin n) : Fin n ≃ Fin n where
  toFun := cyclicAdd k
  invFun := cyclicSub k
  left_inv l := cyclicSub_cyclicAdd k l
  right_inv j := cyclicAdd_cyclicSub k j

@[simp]
private lemma cyclicShiftEquiv_apply {n : ℕ} (k l : Fin n) :
    cyclicShiftEquiv k l = cyclicAdd k l := rfl

private lemma rotMatrix_apply_eq_cyclicSub {n : ℕ} {R : Type*} [Ring R]
    (a : Fin n → R) (i j : Fin n) :
    rotMatrix a i j = if j.val ≤ i.val then a (cyclicSub j i) else -a (cyclicSub j i) := by
  simp only [rotMatrix, Matrix.of_apply, cyclicSub]
  split_ifs <;> rfl

private lemma cyclicSub_cyclicAdd_eq {n : ℕ} (i k l : Fin n) :
    cyclicSub (cyclicAdd k l) i = cyclicSub l (cyclicSub k i) := by
  ext
  rw [cyclicSub_val, cyclicAdd_val, cyclicSub_val, cyclicSub_val]
  split_ifs <;> omega

/-- **Multiplicativity of `rotMatrix`**: the negacyclic multiplication matrix of `negacyclicMul a b`
is the matrix product `rotMatrix a * rotMatrix b`. -/
theorem rotMatrix_negacyclicMul {n : ℕ} {R : Type*} [CommRing R] (a b : Fin n → R) :
    rotMatrix (negacyclicMul a b) = rotMatrix a * rotMatrix b := by
  ext i k
  simp only [Matrix.mul_apply]
  rw [← (cyclicShiftEquiv k).sum_comp]
  rw [rotMatrix_apply_eq_cyclicSub (negacyclicMul a b) i k]
  simp only [negacyclicMul, Matrix.mulVec, dotProduct, ← Finset.sum_neg_distrib]
  by_cases hik : k.val ≤ i.val
  · simp only [hik, ↓reduceIte]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp only [cyclicShiftEquiv_apply, rotMatrix_apply_eq_cyclicSub, cyclicSub_cyclicAdd,
      cyclicSub_cyclicAdd_eq]
    rw [cyclicSub_val, cyclicAdd_val]
    split_ifs <;> first | omega | ring
  · simp only [hik, ↓reduceIte]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp only [cyclicShiftEquiv_apply, rotMatrix_apply_eq_cyclicSub, cyclicSub_cyclicAdd,
      cyclicSub_cyclicAdd_eq]
    rw [cyclicSub_val, cyclicAdd_val]
    split_ifs <;> first | omega | ring

/-- **Associativity of negacyclic polynomial multiplication**: `(a * b) * c = a * (b * c)` in
`R[X] / (X^n + 1)` over any commutative ring `R`. -/
theorem negacyclicMul_assoc {n : ℕ} {R : Type*} [CommRing R] (a b c : Fin n → R) :
    negacyclicMul (negacyclicMul a b) c = negacyclicMul a (negacyclicMul b c) := by
  rw [negacyclicMul, rotMatrix_negacyclicMul, ← Matrix.mulVec_mulVec, ← rotMatrix_mulVec,
    ← rotMatrix_mulVec]

/-- Negacyclic multiplication commutes with negation on the right. -/
@[simp] theorem negacyclicMul_neg {n : ℕ} {R : Type*} [Ring R] (a b : Fin n → R) :
    negacyclicMul a (-b) = -negacyclicMul a b := by
  simp only [negacyclicMul, Matrix.mulVec_neg]

/-- Negacyclic multiplication commutes with negation on the left. -/
@[simp] theorem neg_negacyclicMul {n : ℕ} {R : Type*} [Ring R] (a b : Fin n → R) :
    negacyclicMul (-a) b = -negacyclicMul a b := by
  simp only [negacyclicMul, rotMatrix_neg, Matrix.neg_mulVec]

/-- Negacyclic multiplication distributes over subtraction on the right. -/
theorem negacyclicMul_sub {n : ℕ} {R : Type*} [Ring R] (a b c : Fin n → R) :
    negacyclicMul a (b - c) = negacyclicMul a b - negacyclicMul a c := by
  simp only [negacyclicMul, Matrix.mulVec_sub]

/-- Negacyclic multiplication distributes over subtraction on the left. -/
theorem sub_negacyclicMul {n : ℕ} {R : Type*} [Ring R] (a b c : Fin n → R) :
    negacyclicMul (a - b) c = negacyclicMul a c - negacyclicMul b c := by
  simp only [negacyclicMul, rotMatrix_sub, Matrix.sub_mulVec]

/-- Negacyclic multiplication distributes over finite sums on the left. -/
theorem sum_negacyclicMul {n : ℕ} {R : Type*} [Ring R] {ι : Type*} (s : Finset ι)
    (f : ι → Fin n → R) (b : Fin n → R) :
    negacyclicMul (∑ i ∈ s, f i) b = ∑ i ∈ s, negacyclicMul (f i) b := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, add_negacyclicMul, ih, Finset.sum_insert hi]

/-- Negacyclic multiplication distributes over finite sums on the right. -/
theorem negacyclicMul_sum {n : ℕ} {R : Type*} [Ring R] {ι : Type*} (s : Finset ι)
    (a : Fin n → R) (f : ι → Fin n → R) :
    negacyclicMul a (∑ i ∈ s, f i) = ∑ i ∈ s, negacyclicMul a (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, negacyclicMul_add, ih, Finset.sum_insert hi]

/-- Each row of `rotMatrix a` is a signed rearrangement of `a`, so its absolute values sum to
the `ℓ₁` norm of `a`. -/
theorem sum_abs_rotMatrix_apply {n : ℕ} (a : Fin n → ℤ) (i : Fin n) :
    ∑ j, |rotMatrix a i j| = ∑ j, |a j| :=
  calc ∑ j, |rotMatrix a i j| = ∑ j, |a (negacyclicSwap i j)| :=
        Finset.sum_congr rfl fun j _ => by
          rw [rotMatrix_apply_eq_negacyclicSwap]
          split_ifs <;> simp only [abs_neg]
    _ = ∑ j, |a j| := (negacyclicSwapEquiv i).sum_comp fun j => |a j|

/-- **`ℓ₁`-`ℓ∞` bound for negacyclic multiplication**: if `‖b‖_∞ ≤ β`, then every coefficient of
`negacyclicMul a b` has absolute value at most `‖a‖₁ · β`. -/
theorem abs_negacyclicMul_le_sum_abs_mul {n β : ℕ} {a b : Fin n → ℤ} (hb : ∀ j, |b j| ≤ β)
    (i : Fin n) : |negacyclicMul a b i| ≤ (∑ j, |a j|) * β :=
  calc |negacyclicMul a b i|
      = |∑ j : Fin n, rotMatrix a i j * b j| := rfl
    _ ≤ ∑ j : Fin n, |rotMatrix a i j * b j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j : Fin n, |rotMatrix a i j| * β := Finset.sum_le_sum fun j _ => by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hb j) (abs_nonneg _)
    _ = (∑ j, |a j|) * β := by rw [← Finset.sum_mul, sum_abs_rotMatrix_apply]

/-- Polynomial inner product `⟨b, r⟩ = ∑ j : Fin k, negacyclicMul (b j) (r j)` over
`R[X] / (X^n + 1)`. -/
def innerPoly {k n : ℕ} {R : Type*} [Ring R]
    (b r : Fin k → Fin n → R) : Fin n → R :=
  ∑ j : Fin k, negacyclicMul (b j) (r j)

/-- Over `ZMod q`, `innerPoly` agrees with `ringSISMap`. -/
@[simp] theorem innerPoly_eq_ringSISMap {k n q : ℕ}
    (a z : Fin k → Fin n → ZMod q) :
    innerPoly a z = ringSISMap a z :=
  rfl

/-- `innerPoly` is symmetric over any commutative ring `R`. -/
theorem innerPoly_comm {k n : ℕ} {R : Type*} [CommRing R]
    (a b : Fin k → Fin n → R) :
    innerPoly a b = innerPoly b a := by
  simp only [innerPoly, negacyclicMul_comm]

@[simp] theorem innerPoly_zero_left {k n : ℕ} {R : Type*} [Ring R]
    (r : Fin k → Fin n → R) :
    innerPoly 0 r = 0 := by
  simp [innerPoly]

@[simp] theorem innerPoly_zero_right {k n : ℕ} {R : Type*} [Ring R]
    (b : Fin k → Fin n → R) :
    innerPoly b 0 = 0 := by
  simp [innerPoly]

/-- `innerPoly` is additive in its first argument. -/
theorem innerPoly_add_left {k n : ℕ} {R : Type*} [Ring R]
    (a b r : Fin k → Fin n → R) :
    innerPoly (a + b) r = innerPoly a r + innerPoly b r := by
  simp only [innerPoly, Pi.add_apply, add_negacyclicMul, Finset.sum_add_distrib]

/-- `innerPoly` is additive in its second argument. -/
theorem innerPoly_add_right {k n : ℕ} {R : Type*} [Ring R]
    (b r s : Fin k → Fin n → R) :
    innerPoly b (r + s) = innerPoly b r + innerPoly b s := by
  simp only [innerPoly, Pi.add_apply, negacyclicMul_add, Finset.sum_add_distrib]

/-- `innerPoly` commutes with subtraction in its first argument. -/
theorem innerPoly_sub_left {k n : ℕ} {R : Type*} [Ring R]
    (a b r : Fin k → Fin n → R) :
    innerPoly (a - b) r = innerPoly a r - innerPoly b r := by
  simp only [innerPoly, Pi.sub_apply, sub_negacyclicMul, Finset.sum_sub_distrib]

/-- `innerPoly` commutes with subtraction in its second argument. -/
theorem innerPoly_sub_right {k n : ℕ} {R : Type*} [Ring R]
    (b r s : Fin k → Fin n → R) :
    innerPoly b (r - s) = innerPoly b r - innerPoly b s := by
  simp only [innerPoly, Pi.sub_apply, negacyclicMul_sub, Finset.sum_sub_distrib]

/-- `innerPoly` commutes with ring homomorphisms applied to polynomial coefficients. -/
theorem map_innerPoly {k n : ℕ} {R S : Type*} [Ring R] [Ring S] (f : R →+* S)
    (a b : Fin k → Fin n → R) :
    f ∘ innerPoly a b = innerPoly (fun j => f ∘ a j) (fun j => f ∘ b j) := by
  funext i
  simp only [Function.comp_apply, innerPoly, Finset.sum_apply, map_sum, ← map_negacyclicMul]

/-- **Infinity-norm bound for `innerPoly`**: if every coefficient of `a` has absolute value at most
`α` and every coefficient of `b` has absolute value at most `β`, then every coefficient of
`innerPoly a b` has absolute value at most `k * n * α * β`. -/
theorem abs_innerPoly_le {k n α β : ℕ} {a b : Fin k → Fin n → ℤ}
    (ha : ∀ j i, |a j i| ≤ α) (hb : ∀ j i, |b j i| ≤ β) (i : Fin n) :
    |innerPoly a b i| ≤ k * n * α * β := by
  calc |innerPoly a b i|
      = |∑ j : Fin k, negacyclicMul (a j) (b j) i| := by simp [innerPoly]
    _ ≤ ∑ j : Fin k, |negacyclicMul (a j) (b j) i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin k, ((n : ℤ) * α * β) :=
      Finset.sum_le_sum fun j _ => abs_negacyclicMul_le (ha j) (hb j) i
    _ = k * n * α * β := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

/-- **Adjoint identity for `moduleSISMap` and `innerPoly`**:
`⟨A · s, r⟩ = ⟨Aᵀ · r, s⟩` over `ℤ_q[X] / (X^n + 1)`. -/
theorem innerPoly_moduleSISMap_eq {d k n q : ℕ}
    (A : Matrix (Fin d) (Fin k) (Fin n → ZMod q))
    (s : Fin k → Fin n → ZMod q)
    (r : Fin d → Fin n → ZMod q) :
    innerPoly (moduleSISMap A s) r = innerPoly (moduleSISMap A.transpose r) s := by
  simp only [innerPoly, moduleSISMap, Matrix.transpose_apply, sum_negacyclicMul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  rw [negacyclicMul_assoc, negacyclicMul_comm (s j) (r i), ← negacyclicMul_assoc]

/-- **Fundamental noisy ring-bilinearity cancellation**:
`⟨A · s + e, r⟩ - ⟨Aᵀ · r + e₁, s⟩ = ⟨e, r⟩ - ⟨e₁, s⟩`. -/
theorem innerPoly_moduleSISMap_add_sub {d k n q : ℕ}
    (A : Matrix (Fin d) (Fin k) (Fin n → ZMod q))
    (s e₁ : Fin k → Fin n → ZMod q)
    (r e : Fin d → Fin n → ZMod q) :
    innerPoly (moduleSISMap A s + e) r - innerPoly (moduleSISMap A.transpose r + e₁) s =
      innerPoly e r - innerPoly e₁ s := by
  rw [innerPoly_add_left, innerPoly_add_left, innerPoly_moduleSISMap_eq, add_sub_add_left_eq_sub]

/-! ### Part 2: Polynomial-Ring Message Encoding and Centered-Lift Rounding -/

/-- Encode an `n`-bit message polynomial `m : Fin n → Bool` into `Fin n → ZMod q` by mapping
`false ↦ 0` and `true ↦ (q / 2 : ZMod q)`. -/
def encodePolyMsg {n : ℕ} (q : ℕ) (m : Fin n → Bool) : Fin n → ZMod q :=
  fun i => if m i then ((q / 2 : ℕ) : ZMod q) else 0

@[simp] theorem encodePolyMsg_apply {n : ℕ} (q : ℕ) (m : Fin n → Bool) (i : Fin n) :
    encodePolyMsg q m i = if m i then ((q / 2 : ℕ) : ZMod q) else 0 :=
  rfl

/-- Decode a noisy ring element `w : Fin n → ZMod q` into `Fin n → Bool` by lifting each
coefficient to its centered representative `GeneralSIS.liftCentered w i` in `(-q/2, q/2]` and
testing whether its magnitude exceeds `q / 4` (`false` when `|liftCentered w i| ≤ q / 4`, `true`
when `|liftCentered w i| > q / 4`). -/
def decodePolyMsg {n q : ℕ} (w : Fin n → ZMod q) : Fin n → Bool :=
  fun i => decide (q / 4 < (GeneralSIS.liftCentered w i).natAbs)

@[simp] theorem decodePolyMsg_apply_eq_false_iff {n q : ℕ} (w : Fin n → ZMod q) (i : Fin n) :
    decodePolyMsg w i = false ↔ (GeneralSIS.liftCentered w i).natAbs ≤ q / 4 := by
  simp [decodePolyMsg]

@[simp] theorem decodePolyMsg_apply_eq_true_iff {n q : ℕ} (w : Fin n → ZMod q) (i : Fin n) :
    decodePolyMsg w i = true ↔ q / 4 < (GeneralSIS.liftCentered w i).natAbs := by
  simp [decodePolyMsg]

/-- **Bounded-error decoding correctness for `encodePolyMsg` and `decodePolyMsg`**: if
`4 * B + 2 < q` and every coefficient of the integer error polynomial `err : Fin n → ℤ` satisfies
`(err i).natAbs ≤ B`, then `decodePolyMsg` recovers `m` from
`encodePolyMsg q m + fun i => (err i : ZMod q)`. -/
theorem decodePolyMsg_encodePolyMsg_add_noise {n q B : ℕ} (hB : 4 * B + 2 < q)
    (m : Fin n → Bool) {err : Fin n → ℤ} (herr : ∀ i, (err i).natAbs ≤ B) :
    decodePolyMsg (encodePolyMsg q m + fun i => (err i : ZMod q)) = m := by
  have : NeZero q := ⟨by omega⟩
  funext i
  have hbi : (err i).natAbs ≤ B := herr i
  cases hmi : m i
  · rw [decodePolyMsg_apply_eq_false_iff]
    have hval :
        GeneralSIS.liftCentered (encodePolyMsg q m + fun j => (err j : ZMod q)) i = err i := by
      rw [GeneralSIS.liftCentered, ZMod.valMinAbs_spec]
      refine ⟨?_, by omega, by omega⟩
      simp only [encodePolyMsg, hmi, Bool.false_eq_true, ↓reduceIte, Pi.add_apply, zero_add]
    rw [hval]
    omega
  · rw [decodePolyMsg_apply_eq_true_iff]
    by_cases hwrap : (((q / 2 : ℕ) : ℤ) + err i) * 2 ≤ (q : ℤ)
    · have hval :
          GeneralSIS.liftCentered (encodePolyMsg q m + fun j => (err j : ZMod q)) i =
            ((q / 2 : ℕ) : ℤ) + err i := by
        rw [GeneralSIS.liftCentered, ZMod.valMinAbs_spec]
        refine ⟨?_, by omega, hwrap⟩
        simp only [encodePolyMsg, hmi, ↓reduceIte, Pi.add_apply, Int.cast_add, Int.cast_natCast]
      rw [hval]
      omega
    · have hval :
          GeneralSIS.liftCentered (encodePolyMsg q m + fun j => (err j : ZMod q)) i =
            ((q / 2 : ℕ) : ℤ) + err i - (q : ℤ) := by
        rw [GeneralSIS.liftCentered, ZMod.valMinAbs_spec]
        refine ⟨?_, by omega, by omega⟩
        simp only [encodePolyMsg, hmi, ↓reduceIte, Pi.add_apply, Int.cast_sub, Int.cast_add,
          Int.cast_natCast, ZMod.natCast_self, sub_zero]
      rw [hval]
      omega

/-- Bounded-error decoding correctness stated with `|err i| ≤ B`. -/
theorem decodePolyMsg_encodePolyMsg_add_noise_of_abs_le {n q B : ℕ} (hB : 4 * B + 2 < q)
    (m : Fin n → Bool) {err : Fin n → ℤ} (herr : ∀ i, |err i| ≤ B) :
    decodePolyMsg (encodePolyMsg q m + fun i => (err i : ZMod q)) = m :=
  decodePolyMsg_encodePolyMsg_add_noise hB m fun i => by
    have hi := abs_le.mp (herr i)
    omega

/-- Noiseless round-trip identity for `encodePolyMsg` and `decodePolyMsg` whenever `2 < q`. -/
@[simp] theorem decodePolyMsg_encodePolyMsg {n q : ℕ} (hq : 2 < q) (m : Fin n → Bool) :
    decodePolyMsg (encodePolyMsg q m) = m := by
  have h := decodePolyMsg_encodePolyMsg_add_noise (q := q) (B := 0) (by omega) m
    (err := 0) (fun _ => le_rfl)
  have h0 : (fun i : Fin n => ((0 : Fin n → ℤ) i : ZMod q)) = 0 := by
    funext i
    simp only [Pi.zero_apply, Int.cast_zero]
  rw [h0, add_zero] at h
  exact h

/-! ### Part 3: Ring-LWE / Module-LWE Public-Key Encryption and Decryption Correctness -/

/-- A Module-LWE public key `(A, b)` of module rank `k` over `ℤ_q[X] / (X^n + 1)` consists of a
`k × k` polynomial matrix `A` and a length-`k` polynomial vector `b = A · s + e`. -/
abbrev ModuleLWEPublicKey (k n q : ℕ) : Type :=
  Matrix (Fin k) (Fin k) (Fin n → ZMod q) × (Fin k → Fin n → ZMod q)

/-- A Module-LWE ciphertext `(u, v)` of module rank `k` over `ℤ_q[X] / (X^n + 1)` consists of a
length-`k` polynomial vector `u` and a single ring element `v`. -/
abbrev ModuleLWECiphertext (k n q : ℕ) : Type :=
  (Fin k → Fin n → ZMod q) × (Fin n → ZMod q)

/-- Deterministic Module-LWE public-key generation: given public matrix `A`, secret key `s`, and
error vector `e`, output `(A, moduleSISMap A s + e)`. -/
def moduleLWEKeyGen {k n q : ℕ}
    (A : Matrix (Fin k) (Fin k) (Fin n → ZMod q))
    (s e : Fin k → Fin n → ZMod q) : ModuleLWEPublicKey k n q :=
  (A, moduleSISMap A s + e)

@[simp] theorem moduleLWEKeyGen_fst {k n q : ℕ}
    (A : Matrix (Fin k) (Fin k) (Fin n → ZMod q))
    (s e : Fin k → Fin n → ZMod q) :
    (moduleLWEKeyGen A s e).1 = A :=
  rfl

@[simp] theorem moduleLWEKeyGen_snd {k n q : ℕ}
    (A : Matrix (Fin k) (Fin k) (Fin n → ZMod q))
    (s e : Fin k → Fin n → ZMod q) :
    (moduleLWEKeyGen A s e).2 = moduleSISMap A s + e :=
  rfl

/-- `moduleLWEKeyGen A s e` is `(A, ModuleLWE.sample A s e)`. -/
theorem moduleLWEKeyGen_eq_sample {k n q : ℕ}
    (A : Matrix (Fin k) (Fin k) (Fin n → ZMod q))
    (s e : Fin k → Fin n → ZMod q) :
    moduleLWEKeyGen A s e = (A, ModuleLWE.sample A s e) :=
  rfl

/-- Deterministic Module-LWE encryption of `m : Fin n → Bool` under public key `pk = (A, b)` with
ephemeral secret `r : Fin k → Fin n → ZMod q` and noises `e₁ : Fin k → Fin n → ZMod q` and
`e₂ : Fin n → ZMod q`:
`u = moduleSISMap Aᵀ r + e₁` and `v = innerPoly b r + e₂ + encodePolyMsg q m`. -/
def moduleLWEEncrypt {k n q : ℕ}
    (pk : ModuleLWEPublicKey k n q)
    (r e₁ : Fin k → Fin n → ZMod q)
    (e₂ : Fin n → ZMod q)
    (m : Fin n → Bool) : ModuleLWECiphertext k n q :=
  (moduleSISMap pk.1.transpose r + e₁, innerPoly pk.2 r + e₂ + encodePolyMsg q m)

@[simp] theorem moduleLWEEncrypt_fst {k n q : ℕ}
    (pk : ModuleLWEPublicKey k n q)
    (r e₁ : Fin k → Fin n → ZMod q)
    (e₂ : Fin n → ZMod q)
    (m : Fin n → Bool) :
    (moduleLWEEncrypt pk r e₁ e₂ m).1 = moduleSISMap pk.1.transpose r + e₁ :=
  rfl

@[simp] theorem moduleLWEEncrypt_snd {k n q : ℕ}
    (pk : ModuleLWEPublicKey k n q)
    (r e₁ : Fin k → Fin n → ZMod q)
    (e₂ : Fin n → ZMod q)
    (m : Fin n → Bool) :
    (moduleLWEEncrypt pk r e₁ e₂ m).2 = innerPoly pk.2 r + e₂ + encodePolyMsg q m :=
  rfl

/-- Deterministic Module-LWE decryption of ciphertext `ct = (u, v)` using secret key `s`:
compute `v - innerPoly u s` and apply `decodePolyMsg`. -/
def moduleLWEDecrypt {k n q : ℕ}
    (s : Fin k → Fin n → ZMod q)
    (ct : ModuleLWECiphertext k n q) : Fin n → Bool :=
  decodePolyMsg (ct.2 - innerPoly ct.1 s)

/-- **Algebraic noise cancellation in decryption**: for
`ct = moduleLWEEncrypt (moduleLWEKeyGen A s e) r e₁ e₂ m`, the decryption phase
`ct.2 - innerPoly ct.1 s` equals `encodePolyMsg q m + (innerPoly e r - innerPoly e₁ s + e₂)`. -/
theorem moduleLWEDecrypt_phase_eq {k n q : ℕ}
    (A : Matrix (Fin k) (Fin k) (Fin n → ZMod q))
    (s e r e₁ : Fin k → Fin n → ZMod q)
    (e₂ : Fin n → ZMod q)
    (m : Fin n → Bool) :
    (moduleLWEEncrypt (moduleLWEKeyGen A s e) r e₁ e₂ m).2 -
        innerPoly (moduleLWEEncrypt (moduleLWEKeyGen A s e) r e₁ e₂ m).1 s =
      encodePolyMsg q m + (innerPoly e r - innerPoly e₁ s + e₂) := by
  simp only [moduleLWEEncrypt_fst, moduleLWEEncrypt_snd, moduleLWEKeyGen_fst, moduleLWEKeyGen_snd]
  have hcancel := innerPoly_moduleSISMap_add_sub A s e₁ r e
  abel_nf at hcancel ⊢
  linear_combination hcancel

/-- Combined integer decryption error polynomial `innerPoly e r - innerPoly e₁ s + e₂` over
`ℤ[X] / (X^n + 1)`. -/
def moduleLWEErrorPoly {k n : ℕ}
    (s r e e₁ : Fin k → Fin n → ℤ)
    (e₂ : Fin n → ℤ) : Fin n → ℤ :=
  innerPoly e r - innerPoly e₁ s + e₂

/-- Casting `moduleLWEErrorPoly` to `ZMod q` agrees with the modular error expression
`innerPoly e r - innerPoly e₁ s + e₂` on the centered integer lifts. -/
theorem intCast_moduleLWEErrorPoly_liftCentered {k n q : ℕ}
    (s r e e₁ : Fin k → Fin n → ZMod q)
    (e₂ : Fin n → ZMod q) :
    (fun i => (moduleLWEErrorPoly
        (fun j => GeneralSIS.liftCentered (s j))
        (fun j => GeneralSIS.liftCentered (r j))
        (fun j => GeneralSIS.liftCentered (e j))
        (fun j => GeneralSIS.liftCentered (e₁ j))
        (GeneralSIS.liftCentered e₂) i : ZMod q)) =
      innerPoly e r - innerPoly e₁ s + e₂ := by
  have her := map_innerPoly (Int.castRingHom (ZMod q))
    (fun j => GeneralSIS.liftCentered (e j))
    (fun j => GeneralSIS.liftCentered (r j))
  have hes := map_innerPoly (Int.castRingHom (ZMod q))
    (fun j => GeneralSIS.liftCentered (e₁ j))
    (fun j => GeneralSIS.liftCentered (s j))
  change (Int.cast : ℤ → ZMod q) ∘ _ =
    innerPoly (fun j => (Int.cast : ℤ → ZMod q) ∘ GeneralSIS.liftCentered (e j))
      (fun j => (Int.cast : ℤ → ZMod q) ∘ GeneralSIS.liftCentered (r j)) at her
  change (Int.cast : ℤ → ZMod q) ∘ _ =
    innerPoly (fun j => (Int.cast : ℤ → ZMod q) ∘ GeneralSIS.liftCentered (e₁ j))
      (fun j => (Int.cast : ℤ → ZMod q) ∘ GeneralSIS.liftCentered (s j)) at hes
  simp only [GeneralSIS.intCast_comp_liftCentered] at her hes
  funext i
  simp only [moduleLWEErrorPoly, Pi.add_apply, Pi.sub_apply, Int.cast_add, Int.cast_sub]
  have her_i := congrFun her i
  have hes_i := congrFun hes i
  simp only [Function.comp_apply] at her_i hes_i
  rw [her_i, hes_i]
  simp only [GeneralSIS.liftCentered, ZMod.coe_valMinAbs]

/-- **Infinity-norm bound on `moduleLWEErrorPoly`**: if `‖s‖_∞ ≤ B_s`, `‖r‖_∞ ≤ B_r`, and
`‖e‖_∞, ‖e₁‖_∞, ‖e₂‖_∞ ≤ B_e`, then every coefficient of `moduleLWEErrorPoly s r e e₁ e₂` has
absolute value at most `k * n * B_e * B_r + k * n * B_e * B_s + B_e`. -/
theorem abs_moduleLWEErrorPoly_le {k n B_s B_r B_e : ℕ}
    {s r e e₁ : Fin k → Fin n → ℤ} {e₂ : Fin n → ℤ}
    (hs : ∀ j i, |s j i| ≤ B_s)
    (hr : ∀ j i, |r j i| ≤ B_r)
    (he : ∀ j i, |e j i| ≤ B_e)
    (he₁ : ∀ j i, |e₁ j i| ≤ B_e)
    (he₂ : ∀ i, |e₂ i| ≤ B_e)
    (i : Fin n) :
    |moduleLWEErrorPoly s r e e₁ e₂ i| ≤
      (k * n * B_e * B_r + k * n * B_e * B_s + B_e : ℕ) := by
  have her := abs_innerPoly_le he hr i
  have hes := abs_innerPoly_le he₁ hs i
  have he₂i := he₂ i
  simp only [moduleLWEErrorPoly, Pi.add_apply, Pi.sub_apply, Nat.cast_add, Nat.cast_mul]
  have h1 := abs_add_le (innerPoly e r i - innerPoly e₁ s i) (e₂ i)
  have h2 := abs_sub (innerPoly e r i) (innerPoly e₁ s i)
  linarith

/-- **Bounded-noise decryption correctness (general `B_s, B_r, B_e` bounds)**: when `s, r, e, e₁`
and `e₂` satisfy the centered `ℓ_∞` bounds `B_s, B_r, B_e` and
`4 * (k * n * B_e * B_r + k * n * B_e * B_s + B_e) + 2 < q`, decrypting an encryption of `m`
recovers `m`. -/
theorem moduleLWEDecrypt_moduleLWEEncrypt_eq_of_bounds {k n q B_s B_r B_e : ℕ}
    (hq : 4 * (k * n * B_e * B_r + k * n * B_e * B_s + B_e) + 2 < q)
    (A : Matrix (Fin k) (Fin k) (Fin n → ZMod q))
    {s r e e₁ : Fin k → Fin n → ZMod q}
    {e₂ : Fin n → ZMod q}
    (hs : ModuleSIS.inInfNormBound B_s s)
    (hr : ModuleSIS.inInfNormBound B_r r)
    (he : ModuleSIS.inInfNormBound B_e e)
    (he₁ : ModuleSIS.inInfNormBound B_e e₁)
    (he₂ : GeneralSIS.inInfNormBound B_e e₂)
    (m : Fin n → Bool) :
    moduleLWEDecrypt s (moduleLWEEncrypt (moduleLWEKeyGen A s e) r e₁ e₂ m) = m := by
  rw [moduleLWEDecrypt, moduleLWEDecrypt_phase_eq,
    ← intCast_moduleLWEErrorPoly_liftCentered s r e e₁ e₂]
  exact decodePolyMsg_encodePolyMsg_add_noise_of_abs_le hq m
    (abs_moduleLWEErrorPoly_le hs hr he he₁ he₂)

/-- **Bounded-noise decryption correctness**: when `s` and `r` have centered `ℓ_∞` norm bounded by
`B_s` and `B_r` with `B_s ≤ B_r`, `e, e₁, e₂` have centered `ℓ_∞` norm bounded by `B_e`, and
`4 * (2 * k * n * B_e * B_r + B_e) + 2 < q`, decrypting
`moduleLWEEncrypt (moduleLWEKeyGen A s e) r e₁ e₂ m` recovers `m`. -/
theorem moduleLWEDecrypt_moduleLWEEncrypt_eq {k n q B_s B_r B_e : ℕ}
    (hBs : B_s ≤ B_r)
    (hq : 4 * (2 * k * n * B_e * B_r + B_e) + 2 < q)
    (A : Matrix (Fin k) (Fin k) (Fin n → ZMod q))
    {s r e e₁ : Fin k → Fin n → ZMod q}
    {e₂ : Fin n → ZMod q}
    (hs : ModuleSIS.inInfNormBound B_s s)
    (hr : ModuleSIS.inInfNormBound B_r r)
    (he : ModuleSIS.inInfNormBound B_e e)
    (he₁ : ModuleSIS.inInfNormBound B_e e₁)
    (he₂ : GeneralSIS.inInfNormBound B_e e₂)
    (m : Fin n → Bool) :
    moduleLWEDecrypt s (moduleLWEEncrypt (moduleLWEKeyGen A s e) r e₁ e₂ m) = m := by
  have hle : k * n * B_e * B_s ≤ k * n * B_e * B_r := Nat.mul_le_mul_left (k * n * B_e) hBs
  have hsum : k * n * B_e * B_r + k * n * B_e * B_s ≤ 2 * k * n * B_e * B_r := by
    calc k * n * B_e * B_r + k * n * B_e * B_s
        ≤ k * n * B_e * B_r + k * n * B_e * B_r := Nat.add_le_add_left hle _
      _ = 2 * k * n * B_e * B_r := by ring
  exact moduleLWEDecrypt_moduleLWEEncrypt_eq_of_bounds (by omega) A hs hr he he₁ he₂ m

/-! ### Part 4: Public-Key Pseudorandomness and Module-LWE Advantage Bounds for Ciphertexts -/

/-- Draw a secret from `secretLaw`, a uniform matrix, and independent polynomial errors, then
output the existing key generator's public key. The default secret law is uniform, exactly as
required by the `ModuleLWE.sampleLaw` identity and advantage bounds below. -/
noncomputable def moduleLWEPublicKeyLaw (k n q : ℕ) [NeZero q]
    (noise : PMF (Fin n → ZMod q))
    (secretLaw : PMF (Fin k → Fin n → ZMod q) := PMF.uniformOfFintype _) :
    PMF (ModuleLWEPublicKey k n q) := do
  let secret ← secretLaw
  let A ← PMF.uniformOfFintype (Matrix (Fin k) (Fin k) (Fin n → ZMod q))
  let error ← PMF.pi (fun _ : Fin k => noise)
  return moduleLWEKeyGen A secret error

/-- The honest public-key distribution is identical to `ModuleLWE.sampleLaw k k n q noise`. -/
@[simp] theorem moduleLWEPublicKeyLaw_eq_sampleLaw (k n q : ℕ) [NeZero q]
    (noise : PMF (Fin n → ZMod q)) :
    moduleLWEPublicKeyLaw k n q noise = ModuleLWE.sampleLaw k k n q noise :=
  rfl

/-- **Public-key pseudorandomness (`DecisionModuleLWE` Hop 1)**: under
`DecisionModuleLWE k k n q noise`, the encoded honest public-key ensemble is computationally
indistinguishable from the encoded uniform public-key ensemble
`ModuleLWE.uniformEnsemble k k n q`. -/
theorem publicKey_indistinguishable_of_decisionModuleLWE (k n q : ℕ → ℕ)
    [∀ security, NeZero (q security)]
    (noise : (security : ℕ) → PMF (Fin (n security) → ZMod (q security)))
    (h : DecisionModuleLWE k k n q noise) :
    ComputationallyIndistinguishable
      (fun s => (moduleLWEPublicKeyLaw (k s) (n s) (q s) (noise s)).map ModuleLWE.encodeSample)
      (ModuleLWE.uniformEnsemble k k n q) :=
  h

/-- Embed a public key `pk = (A, b)` into a `(k + 1) × k` module matrix by placing `b` as row `0`
and the rows of `Aᵀ` as rows `Fin.succ i`. -/
def extendPublicKeyMatrix {k n q : ℕ} (pk : ModuleLWEPublicKey k n q) :
    Matrix (Fin (k + 1)) (Fin k) (Fin n → ZMod q) :=
  Matrix.of (Fin.cons pk.2 pk.1.transpose)

/-- Recover a public key `(A, b)` from a `(k + 1) × k` module matrix by reading row `0` as `b` and
the transpose of the remaining `k` rows as `A`. -/
def unextendPublicKeyMatrix {k n q : ℕ}
    (M : Matrix (Fin (k + 1)) (Fin k) (Fin n → ZMod q)) : ModuleLWEPublicKey k n q :=
  ((Matrix.of fun i j => M i.succ j).transpose, M 0)

@[simp] theorem unextendPublicKeyMatrix_extendPublicKeyMatrix {k n q : ℕ}
    (pk : ModuleLWEPublicKey k n q) :
    unextendPublicKeyMatrix (extendPublicKeyMatrix pk) = pk := by
  rcases pk with ⟨A, b⟩
  ext i j x
  · rfl
  · rfl

@[simp] theorem extendPublicKeyMatrix_unextendPublicKeyMatrix {k n q : ℕ}
    (M : Matrix (Fin (k + 1)) (Fin k) (Fin n → ZMod q)) :
    extendPublicKeyMatrix (unextendPublicKeyMatrix M) = M := by
  ext i j x
  refine Fin.cases ?_ ?_ i
  · rfl
  · intro _
    rfl

/-- Equivalence between `ModuleLWEPublicKey k n q` and `(k + 1) × k` module matrices. -/
def extendPublicKeyEquiv (k n q : ℕ) :
    ModuleLWEPublicKey k n q ≃ Matrix (Fin (k + 1)) (Fin k) (Fin n → ZMod q) where
  toFun := extendPublicKeyMatrix
  invFun := unextendPublicKeyMatrix
  left_inv := unextendPublicKeyMatrix_extendPublicKeyMatrix
  right_inv := extendPublicKeyMatrix_unextendPublicKeyMatrix

/-- Embed a ciphertext `ct = (u, v)` into a length-`(k + 1)` polynomial vector by placing `v` at
coordinate `0` and `u` at coordinates `Fin.succ i`. -/
def extendCiphertext {k n q : ℕ} (ct : ModuleLWECiphertext k n q) :
    Fin (k + 1) → Fin n → ZMod q :=
  Fin.cons ct.2 ct.1

/-- Recover a ciphertext `(u, v)` from a length-`(k + 1)` polynomial vector. -/
def unextendCiphertext {k n q : ℕ} (w : Fin (k + 1) → Fin n → ZMod q) :
    ModuleLWECiphertext k n q :=
  (fun i => w i.succ, w 0)

@[simp] theorem unextendCiphertext_extendCiphertext {k n q : ℕ}
    (ct : ModuleLWECiphertext k n q) :
    unextendCiphertext (extendCiphertext ct) = ct := by
  rcases ct with ⟨u, v⟩
  rfl

@[simp] theorem extendCiphertext_unextendCiphertext {k n q : ℕ}
    (w : Fin (k + 1) → Fin n → ZMod q) :
    extendCiphertext (unextendCiphertext w) = w := by
  funext i
  refine Fin.cases ?_ ?_ i
  · rfl
  · intro _
    rfl

/-- Equivalence between `ModuleLWECiphertext k n q` and `Fin (k + 1) → Fin n → ZMod q`. -/
def extendCiphertextEquiv (k n q : ℕ) :
    ModuleLWECiphertext k n q ≃ (Fin (k + 1) → Fin n → ZMod q) where
  toFun := extendCiphertext
  invFun := unextendCiphertext
  left_inv := unextendCiphertext_extendCiphertext
  right_inv := extendCiphertext_unextendCiphertext

/-- **Structural embedding of encryption into `(k + 1) × k` Module-LWE**:
`extendCiphertext (moduleLWEEncrypt pk r e₁ e₂ m)` is the `(k + 1) × k` Module-LWE sample
`ModuleLWE.sample (extendPublicKeyMatrix pk) r (Fin.cons e₂ e₁)` masked by
`Fin.cons (encodePolyMsg q m) 0`. -/
theorem extendCiphertext_moduleLWEEncrypt {k n q : ℕ}
    (pk : ModuleLWEPublicKey k n q)
    (r e₁ : Fin k → Fin n → ZMod q)
    (e₂ : Fin n → ZMod q)
    (m : Fin n → Bool) :
    extendCiphertext (moduleLWEEncrypt pk r e₁ e₂ m) =
      ModuleLWE.sample (extendPublicKeyMatrix pk) r (Fin.cons e₂ e₁) +
        Fin.cons (encodePolyMsg q m) 0 := by
  funext i
  refine Fin.cases ?_ ?_ i
  · rfl
  · intro i'
    simp only [extendCiphertext, moduleLWEEncrypt, ModuleLWE.sample, Pi.add_apply,
      Fin.cons_succ, Pi.zero_apply, add_zero]
    rfl

/-- Equivalence masking the second component of a `(k + 1) × k` Module-LWE sample by
`Fin.cons (encodePolyMsg q m) 0`. -/
def maskExtendedSampleEquiv {k n q : ℕ} (m : Fin n → Bool) :
    (Matrix (Fin (k + 1)) (Fin k) (Fin n → ZMod q) × (Fin (k + 1) → Fin n → ZMod q)) ≃
      (Matrix (Fin (k + 1)) (Fin k) (Fin n → ZMod q) × (Fin (k + 1) → Fin n → ZMod q)) :=
  (Equiv.refl _).prodCongr (Equiv.addRight (Fin.cons (encodePolyMsg q m) 0))

/-- Distribution of the extended `(k + 1) × k` pair
`(extendPublicKeyMatrix pk, extendCiphertext (moduleLWEEncrypt pk r e₁ e₂ m))` when `pk` is drawn
uniformly, `r` is drawn uniformly, `e₁ ← PMF.pi (fun _ => noise)`, and `e₂ ← noise`. -/
noncomputable def uniformKeyEncryptionLaw (k n q : ℕ) [NeZero q]
    (noise : PMF (Fin n → ZMod q)) (m : Fin n → Bool) :
    PMF (Matrix (Fin (k + 1)) (Fin k) (Fin n → ZMod q) ×
      (Fin (k + 1) → Fin n → ZMod q)) := do
  let r ← PMF.uniformOfFintype (Fin k → Fin n → ZMod q)
  let pk ← PMF.uniformOfFintype (ModuleLWEPublicKey k n q)
  let e₂ ← noise
  let e₁ ← PMF.pi (fun _ : Fin k => noise)
  return (extendPublicKeyMatrix pk, extendCiphertext (moduleLWEEncrypt pk r e₁ e₂ m))

/-- **Second `DecisionModuleLWE` hop identity**: under a uniform public key `pk`, the extended
encryption distribution `uniformKeyEncryptionLaw k n q noise m` is the pushforward of
`ModuleLWE.sampleLaw (k + 1) k n q noise` by `maskExtendedSampleEquiv m`. -/
theorem uniformKeyEncryptionLaw_eq_sampleLaw_map (k n q : ℕ) [NeZero q]
    (noise : PMF (Fin n → ZMod q)) (m : Fin n → Bool) :
    uniformKeyEncryptionLaw k n q noise m =
      (ModuleLWE.sampleLaw (k + 1) k n q noise).map (maskExtendedSampleEquiv m) := by
  unfold uniformKeyEncryptionLaw ModuleLWE.sampleLaw
  simp only [pmf_norm]
  congr 1 with r : 1
  have hpk :
      PMF.uniformOfFintype (Matrix (Fin (k + 1)) (Fin k) (Fin n → ZMod q)) =
        (PMF.uniformOfFintype (ModuleLWEPublicKey k n q)).map (extendPublicKeyEquiv k n q) :=
    (PMF.uniformOfFintype_map_equiv (extendPublicKeyEquiv k n q)).symm
  rw [hpk, PMF.bind_map, PMF.pi_fin_succ k noise]
  congr 1 with pk : 1
  simp only [pmf_norm, extendPublicKeyEquiv, Equiv.coe_fn_mk, extendCiphertext_moduleLWEEncrypt]
  rfl

/-- Masking the second component of a uniform `(k + 1) × k` Module-LWE sample by
`maskExtendedSampleEquiv m` leaves the uniform distribution invariant, so the resulting
distribution is independent of `m`. -/
theorem uniformSample_mask_eq_uniform (k n q : ℕ) [NeZero q] (m : Fin n → Bool) :
    (PMF.uniformOfFintype
      (Matrix (Fin (k + 1)) (Fin k) (Fin n → ZMod q) ×
        (Fin (k + 1) → Fin n → ZMod q))).map (maskExtendedSampleEquiv m) =
      PMF.uniformOfFintype
        (Matrix (Fin (k + 1)) (Fin k) (Fin n → ZMod q) ×
          (Fin (k + 1) → Fin n → ZMod q)) :=
  PMF.uniformOfFintype_map_equiv (maskExtendedSampleEquiv m)

/-- Complete encryption view `(pk, ct)` under an arbitrary public-key distribution `pkLaw`,
drawing `r` from `ephemeralLaw`, `e₂ ← noise`, and `e₁ ← PMF.pi (fun _ => noise)`.
The default ephemeral law is uniform, as used by the advantage bounds below. -/
noncomputable def encryptionViewOfKeyLaw {k n q : ℕ} [NeZero q]
    (pkLaw : PMF (ModuleLWEPublicKey k n q))
    (noise : PMF (Fin n → ZMod q)) (m : Fin n → Bool)
    (ephemeralLaw : PMF (Fin k → Fin n → ZMod q) := PMF.uniformOfFintype _) :
    PMF (ModuleLWEPublicKey k n q × ModuleLWECiphertext k n q) := do
  let pk ← pkLaw
  let r ← ephemeralLaw
  let e₂ ← noise
  let e₁ ← PMF.pi (fun _ : Fin k => noise)
  return (pk, moduleLWEEncrypt pk r e₁ e₂ m)

/-- Real encryption view `(pk, ct)` with explicit long-term and ephemeral secret laws.
Both default to uniform. The `ModuleLWE.sampleLaw` identities and advantage bounds of Part 4
concern those defaults; this parameterization does not extend them to other secret distributions.
The correctness theorem `moduleLWEDecrypt_moduleLWEEncrypt_eq_of_bounds` assumes centered bounds
on both secrets; together with its hypothesis on `q`, these hold for every value of uniform
secrets only when `k * n * B_e = 0`. -/
noncomputable def realEncryptionView (k n q : ℕ) [NeZero q]
    (noise : PMF (Fin n → ZMod q)) (m : Fin n → Bool)
    (secretLaw : PMF (Fin k → Fin n → ZMod q) := PMF.uniformOfFintype _)
    (ephemeralLaw : PMF (Fin k → Fin n → ZMod q) := PMF.uniformOfFintype _) :
    PMF (ModuleLWEPublicKey k n q × ModuleLWECiphertext k n q) :=
  encryptionViewOfKeyLaw (moduleLWEPublicKeyLaw k n q noise secretLaw) noise m ephemeralLaw

/-- Hybrid encryption view `(pk, ct)` under a uniform public key `pk`. -/
noncomputable def hybridEncryptionView (k n q : ℕ) [NeZero q]
    (noise : PMF (Fin n → ZMod q)) (m : Fin n → Bool) :
    PMF (ModuleLWEPublicKey k n q × ModuleLWECiphertext k n q) :=
  encryptionViewOfKeyLaw (PMF.uniformOfFintype (ModuleLWEPublicKey k n q)) noise m

/-- Ideal uniform encryption view `(pk, ct)`, completely independent of the message `m`. -/
noncomputable def uniformEncryptionView (k n q : ℕ) [NeZero q] :
    PMF (ModuleLWEPublicKey k n q × ModuleLWECiphertext k n q) :=
  PMF.uniformOfFintype (ModuleLWEPublicKey k n q × ModuleLWECiphertext k n q)

/-- Equivalence unextending a masked `(k + 1) × k` Module-LWE pair `(M, w)` into a `(pk, ct)`
pair. -/
def unextendMaskedSampleEquiv {k n q : ℕ} (m : Fin n → Bool) :
    (Matrix (Fin (k + 1)) (Fin k) (Fin n → ZMod q) × (Fin (k + 1) → Fin n → ZMod q)) ≃
      (ModuleLWEPublicKey k n q × ModuleLWECiphertext k n q) :=
  (maskExtendedSampleEquiv m).trans
    ((extendPublicKeyEquiv k n q).symm.prodCongr (extendCiphertextEquiv k n q).symm)

/-- Unextending a masked `(k + 1) × k` Module-LWE pair `(M, w)` into a `(pk, ct)` pair. -/
def unextendMaskedSample {k n q : ℕ} (m : Fin n → Bool)
    (pair : Matrix (Fin (k + 1)) (Fin k) (Fin n → ZMod q) × (Fin (k + 1) → Fin n → ZMod q)) :
    ModuleLWEPublicKey k n q × ModuleLWECiphertext k n q :=
  unextendMaskedSampleEquiv m pair

/-- `hybridEncryptionView k n q noise m` is the pushforward of
`ModuleLWE.sampleLaw (k + 1) k n q noise` under `unextendMaskedSample m`. -/
theorem hybridEncryptionView_eq_sampleLaw_map (k n q : ℕ) [NeZero q]
    (noise : PMF (Fin n → ZMod q)) (m : Fin n → Bool) :
    hybridEncryptionView k n q noise m =
      (ModuleLWE.sampleLaw (k + 1) k n q noise).map (unextendMaskedSample m) := by
  have hcomm :
      hybridEncryptionView k n q noise m =
        (uniformKeyEncryptionLaw k n q noise m).map
          (fun p => (unextendPublicKeyMatrix p.1, unextendCiphertext p.2)) := by
    unfold hybridEncryptionView encryptionViewOfKeyLaw uniformKeyEncryptionLaw
    simp only [pmf_norm, unextendPublicKeyMatrix_extendPublicKeyMatrix,
      unextendCiphertext_extendCiphertext]
    rw [PMF.bind_comm]
  rw [hcomm, uniformKeyEncryptionLaw_eq_sampleLaw_map, PMF.map_comp]
  rfl

/-- Pushing forward the uniform `(k + 1) × k` sample distribution under `unextendMaskedSample m`
yields `uniformEncryptionView k n q` for every message `m`. -/
theorem uniformSample_map_unextendMaskedSample (k n q : ℕ) [NeZero q] (m : Fin n → Bool) :
    (PMF.uniformOfFintype
      (Matrix (Fin (k + 1)) (Fin k) (Fin n → ZMod q) ×
        (Fin (k + 1) → Fin n → ZMod q))).map (unextendMaskedSample m) =
      uniformEncryptionView k n q :=
  PMF.uniformOfFintype_map_equiv (unextendMaskedSampleEquiv m)

/-- **Two-hop `ModuleLWE` advantage bound for `(pk, ct)`**: for any semantic distinguisher
`D : ModuleLWEPublicKey k n q × ModuleLWECiphertext k n q → Game` and any message `m`, the
distinguishing advantage between `realEncryptionView k n q noise m` and
`uniformEncryptionView k n q` is bounded by the sum of:
1. the `k × k` `ModuleLWE` advantage (replacing the public key with uniform), and
2. the `(k + 1) × k` `ModuleLWE` advantage (replacing the ciphertext with uniform). -/
theorem advantage_realEncryptionView_uniform_le {k n q : ℕ} [NeZero q]
    (noise : PMF (Fin n → ZMod q)) (m : Fin n → Bool)
    (D : ModuleLWEPublicKey k n q × ModuleLWECiphertext k n q → Game) :
    Game.advantage ((realEncryptionView k n q noise m).bind D)
        ((uniformEncryptionView k n q).bind D) ≤
      Game.advantage
        ((ModuleLWE.sampleLaw k k n q noise).bind fun pk =>
          (encryptionViewOfKeyLaw (PMF.pure pk) noise m).bind D)
        ((PMF.uniformOfFintype (ModuleLWEPublicKey k n q)).bind fun pk =>
          (encryptionViewOfKeyLaw (PMF.pure pk) noise m).bind D) +
      Game.advantage
        ((ModuleLWE.sampleLaw (k + 1) k n q noise).bind (D ∘ unextendMaskedSample m))
        ((PMF.uniformOfFintype
          (Matrix (Fin (k + 1)) (Fin k) (Fin n → ZMod q) ×
            (Fin (k + 1) → Fin n → ZMod q))).bind (D ∘ unextendMaskedSample m)) := by
  have hreal :
      (realEncryptionView k n q noise m).bind D =
        (ModuleLWE.sampleLaw k k n q noise).bind fun pk =>
          (encryptionViewOfKeyLaw (PMF.pure pk) noise m).bind D := by
    simp only [pmf_norm, realEncryptionView, moduleLWEPublicKeyLaw_eq_sampleLaw,
      encryptionViewOfKeyLaw]
  have hhyb1 :
      (hybridEncryptionView k n q noise m).bind D =
        (PMF.uniformOfFintype (ModuleLWEPublicKey k n q)).bind fun pk =>
          (encryptionViewOfKeyLaw (PMF.pure pk) noise m).bind D := by
    simp only [pmf_norm, hybridEncryptionView, encryptionViewOfKeyLaw]
  have hhyb2 :
      (hybridEncryptionView k n q noise m).bind D =
        (ModuleLWE.sampleLaw (k + 1) k n q noise).bind (D ∘ unextendMaskedSample m) := by
    rw [hybridEncryptionView_eq_sampleLaw_map, PMF.bind_map]
  have hunif :
      (uniformEncryptionView k n q).bind D =
        (PMF.uniformOfFintype
          (Matrix (Fin (k + 1)) (Fin k) (Fin n → ZMod q) ×
            (Fin (k + 1) → Fin n → ZMod q))).bind (D ∘ unextendMaskedSample m) := by
    rw [← uniformSample_map_unextendMaskedSample k n q m, PMF.bind_map]
  rw [hreal, hunif, ← hhyb1, ← hhyb2]
  exact Game.advantage_triangle _ ((hybridEncryptionView k n q noise m).bind D) _

/-- **Two-message CPA distinguishing bound via `uniformEncryptionView`**: for any two messages
`m₀, m₁ : Fin n → Bool` and any semantic distinguisher `D`, the advantage between
`realEncryptionView k n q noise m₀` and `realEncryptionView k n q noise m₁` is bounded by their
respective distances to the message-independent `uniformEncryptionView k n q`. -/
theorem advantage_realEncryptionView_msg_le {k n q : ℕ} [NeZero q]
    (noise : PMF (Fin n → ZMod q)) (m₀ m₁ : Fin n → Bool)
    (D : ModuleLWEPublicKey k n q × ModuleLWECiphertext k n q → Game) :
    Game.advantage ((realEncryptionView k n q noise m₀).bind D)
        ((realEncryptionView k n q noise m₁).bind D) ≤
      Game.advantage ((realEncryptionView k n q noise m₀).bind D)
        ((uniformEncryptionView k n q).bind D) +
      Game.advantage ((realEncryptionView k n q noise m₁).bind D)
        ((uniformEncryptionView k n q).bind D) := by
  calc Game.advantage ((realEncryptionView k n q noise m₀).bind D)
          ((realEncryptionView k n q noise m₁).bind D)
      ≤ Game.advantage ((realEncryptionView k n q noise m₀).bind D)
          ((uniformEncryptionView k n q).bind D) +
        Game.advantage ((uniformEncryptionView k n q).bind D)
          ((realEncryptionView k n q noise m₁).bind D) :=
        Game.advantage_triangle _ _ _
    _ = _ := by rw [Game.advantage_comm ((uniformEncryptionView k n q).bind D)]

end Cslib.Crypto
