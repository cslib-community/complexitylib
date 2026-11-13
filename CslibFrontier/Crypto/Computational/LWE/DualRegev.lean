/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.LWE.Decoding
public import CslibFrontier.Crypto.Computational.LWE.KeyGen
public import CslibFrontier.Crypto.Game.Statistical
public import CslibFrontier.Probability.BitString.SubsetSum.Matrix
import CslibFrontier.Probability.PMF.Uniform

/-!
# Dual-Regev public-key encryption and preimage-sampleable trapdoors

The dual of Regev's scheme [GentryPeikertVaikuntanathan2008, Section 7.1] in the presentation of
[Peikert2016, Section 5.2.2], at modulus `q = 2 ^ w`. We store the public matrix in the
orientation of `LWE.publicMatrix`: `A` has `m` rows of `n` residues (it is the transpose of the
papers' `n × m` matrix). The secret key is a short integer vector `e`, and the public key is
`(A, u)` with syndrome `u = eᵀ A`. With a secret `s`, integer errors `x` and `x₀`, a bit `μ` is
encrypted as `(A s + x, ⟨u, s⟩ + x₀ + μ * 2 ^ (w - 1))`, and decryption rounds
`c₀ - ⟨e, b⟩ = μ * 2 ^ (w - 1) + x₀ - ⟨e, x⟩`.

`GPVTrapdoor` is the interface of a preimage-sampleable trapdoor function
[GentryPeikertVaikuntanathan2008, Section 5]: trapdoor generation together with a preimage
sampler that returns a short preimage `e` of any syndrome `u`. Only the support condition used
for correctness is part of `GPVTrapdoor.SamplesShortPreimages`; the distributional requirements of
a preimage-sampleable function (near-uniform public matrices and the discrete-Gaussian law of
preimages) are not formalized here. Dual-Regev keys extracted with such a sampler, as in the
identity-based encryption scheme of [GentryPeikertVaikuntanathan2008, Section 7.2], decrypt with
zero error under the stated noise margin.

The key generator `keyGen` draws a uniform binary secret. Its public key is statistically close to
a uniform pair by the leftover hash lemma for `e ↦ eᵀ A`. Native serialized codecs, PPT
certificates, and the IND-CPA security reduction to decision LWE with `m + 1` samples are in
`LWE.DualRegev.Security`.

## Main definitions

* `DualRegev.PublicKey`, `DualRegev.Ciphertext`: keys `(A, u)` and ciphertexts `(b, c₀)`.
* `DualRegev.publicKeyOf`, `DualRegev.encryptWithCoins`, `DualRegev.decrypt`: the deterministic
  algorithms.
* `DualRegev.noise`: the integer decryption noise `x₀ - ⟨e, x⟩`.
* `DualRegev.keyGen`, `DualRegev.encrypt`: programs with a binary secret and centered-binomial
  errors.
* `DualRegev.GPVTrapdoor`, `DualRegev.GPVTrapdoor.SamplesShortPreimages`,
  `DualRegev.GPVTrapdoor.extract`: the trapdoor interface, its correctness condition, and key
  extraction for a syndrome.

## Main results

* `DualRegev.encryptWithCoins_residual`: the exact decryption residual.
* `DualRegev.decrypt_encryptWithCoins`, `DualRegev.keyGen_encrypt_correct`: zero decryption error.
* `DualRegev.GPVTrapdoor.decrypt_encryptWithCoins_extract`: zero decryption error for keys
  extracted with a short-preimage sampler.
* `DualRegev.dist_keyGen_uniform_le`: the generated public key is within
  `sqrt(2 ^ (w * n) / 2 ^ m) / 2` of a uniform pair.

## References

* [C. Gentry, C. Peikert and V. Vaikuntanathan, *Trapdoors for Hard Lattices and New Cryptographic
  Constructions*, Sections 5 and 7][GentryPeikertVaikuntanathan2008]; section numbers follow the
  full version, IACR ePrint 2007/432.
* [C. Peikert, *A Decade of Lattice Cryptography*, Section 5.2.2][Peikert2016]
-/

@[expose] public section

namespace Cslib.Crypto.DualRegev

open Probability Probability.PMF
open scoped _root_.Matrix

/-- A public key `(A, u)`: `m` rows of `n` residues and a syndrome in `n` residues. -/
abbrev PublicKey (n m w : ℕ) := Matrix (Fin m) (Fin n) (ZMod (2 ^ w)) × (Fin n → ZMod (2 ^ w))

/-- A ciphertext `(b, c₀)`: `m` residues and one padded residue. -/
abbrev Ciphertext (m w : ℕ) := (Fin m → ZMod (2 ^ w)) × ZMod (2 ^ w)

/-- Integer vectors reduced modulo `2 ^ w`. -/
def castVector {m : ℕ} (w : ℕ) (v : Fin m → ℤ) : Fin m → ZMod (2 ^ w) :=
  fun i => (v i : ZMod (2 ^ w))

/-- The public key `(A, eᵀ A)` of a secret `e`. -/
def publicKeyOf {n m w : ℕ} (A : Matrix (Fin m) (Fin n) (ZMod (2 ^ w))) (e : Fin m → ℤ) :
    PublicKey n m w :=
  (A, castVector w e ᵥ* A)

/-- Encrypt `μ` with secret `s` and integer errors `x`, `x₀` as
`(A s + x, ⟨u, s⟩ + x₀ + μ * 2 ^ (w - 1))`. -/
def encryptWithCoins {n m w : ℕ} (pk : PublicKey n m w) (μ : Bool) (s : Fin n → ZMod (2 ^ w))
    (x : Fin m → ℤ) (x₀ : ℤ) : Ciphertext m w :=
  (pk.1 *ᵥ s + castVector w x, pk.2 ⬝ᵥ s + (x₀ : ZMod (2 ^ w)) + LWE.encodeBit w μ)

/-- Decrypt by rounding `c₀ - ⟨e, b⟩`. -/
def decrypt {m w : ℕ} (e : Fin m → ℤ) (c : Ciphertext m w) : Bool :=
  LWE.decode w (c.2 - castVector w e ⬝ᵥ c.1)

/-- The integer decryption noise `x₀ - ⟨e, x⟩`. -/
def noise {m : ℕ} (e x : Fin m → ℤ) (x₀ : ℤ) : ℤ :=
  x₀ - ∑ i, e i * x i

/-- The decryption residual: `c₀ - ⟨e, b⟩ = μ * 2 ^ (w - 1) + x₀ - ⟨e, x⟩` modulo `2 ^ w`. -/
theorem encryptWithCoins_residual {n m w : ℕ} (A : Matrix (Fin m) (Fin n) (ZMod (2 ^ w)))
    (e : Fin m → ℤ) (μ : Bool) (s : Fin n → ZMod (2 ^ w)) (x : Fin m → ℤ) (x₀ : ℤ) :
    (encryptWithCoins (publicKeyOf A e) μ s x x₀).2 -
        castVector w e ⬝ᵥ (encryptWithCoins (publicKeyOf A e) μ s x x₀).1 =
      (((μ.toNat : ℤ) * 2 ^ (w - 1) + noise e x x₀ : ℤ) : ZMod (2 ^ w)) := by
  simp only [encryptWithCoins, publicKeyOf, dotProduct_add, ← Matrix.dotProduct_mulVec]
  simp [noise, LWE.encodeBit, castVector, dotProduct]
  ring

/-- Bounded secrets and errors give decryption noise of magnitude at most `m * (β * η) + η`. -/
theorem natAbs_noise_le {m β η : ℕ} (e x : Fin m → ℤ) (x₀ : ℤ)
    (he : ∀ i, (e i).natAbs ≤ β) (hx : ∀ i, (x i).natAbs ≤ η) (hx₀ : x₀.natAbs ≤ η) :
    (noise e x x₀).natAbs ≤ m * (β * η) + η := by
  refine (Int.natAbs_sub_le _ _).trans ?_
  have hsum : (∑ i, e i * x i).natAbs ≤ m * (β * η) := by
    refine (Int.natAbs_sum_le _ _).trans ?_
    calc ∑ i, (e i * x i).natAbs ≤ ∑ _i : Fin m, β * η :=
          Finset.sum_le_sum fun i _ => by
            rw [Int.natAbs_mul]
            exact Nat.mul_le_mul (he i) (hx i)
      _ = m * (β * η) := by simp
  omega

/-- Zero decryption error under the strict margin `4 * (m * (β * η) + η) < 2 ^ w`. -/
theorem decrypt_encryptWithCoins {n m w β η : ℕ} (A : Matrix (Fin m) (Fin n) (ZMod (2 ^ w)))
    (e : Fin m → ℤ) (μ : Bool) (s : Fin n → ZMod (2 ^ w)) (x : Fin m → ℤ) (x₀ : ℤ)
    (hw : 0 < w) (he : ∀ i, (e i).natAbs ≤ β) (hx : ∀ i, (x i).natAbs ≤ η)
    (hx₀ : x₀.natAbs ≤ η) (hmargin : 4 * (m * (β * η) + η) < 2 ^ w) :
    decrypt e (encryptWithCoins (publicKeyOf A e) μ s x x₀) = μ := by
  rw [decrypt, encryptWithCoins_residual]
  exact LWE.decode_eq_of_error hw μ _
    ((Nat.mul_le_mul_left 4 (natAbs_noise_le e x x₀ he hx hx₀)).trans_lt hmargin)

/-- Sample a uniform matrix and a uniform binary secret, and output `(A, eᵀ A)` and `e`. -/
noncomputable def keyGen (n m w : ℕ) : ProbComp (PublicKey n m w × (Fin m → ℤ)) := do
  let A ← LWE.sampleMatrix m n w
  let bits ← OracleComp.replicateFin m (ProbComp.uniform Bool)
  let e : Fin m → ℤ := fun i => (bits i).toNat
  return (publicKeyOf A e, e)

/-- Encrypt with a uniform secret and independent centered-binomial errors of parameter `η`. -/
noncomputable def encrypt {n m w : ℕ} (η : ℕ) (pk : PublicKey n m w) (μ : Bool) :
    ProbComp (Ciphertext m w) := do
  let s ← LWE.sampleVector n w
  let x ← OracleComp.replicateFin m (ProbComp.sampleCenteredBinomial η)
  let x₀ ← ProbComp.sampleCenteredBinomial η
  return encryptWithCoins pk μ s x x₀

/-- Generated keys have the form `(A, eᵀ A)` with a binary secret. -/
theorem mem_support_keyGen {n m w : ℕ} {pk : PublicKey n m w} {e : Fin m → ℤ}
    (hkeys : (pk, e) ∈ (ProbComp.eval (keyGen n m w)).support) :
    pk = publicKeyOf pk.1 e ∧ ∀ i, (e i).natAbs ≤ 1 := by
  simp only [keyGen, ProbComp.eval_bind, ProbComp.eval_pure, PMF.mem_support_bind_iff,
    PMF.mem_support_pure_iff, Prod.mk.injEq] at hkeys
  obtain ⟨A, -, bits, -, rfl, rfl⟩ := hkeys
  exact ⟨rfl, fun i => by simpa using Bool.toNat_le (bits i)⟩

/-- Supported ciphertexts are encryptions with errors bounded by `η`. -/
theorem mem_support_encrypt {n m w η : ℕ} {pk : PublicKey n m w} {μ : Bool} {c : Ciphertext m w}
    (hc : c ∈ (ProbComp.eval (encrypt η pk μ)).support) :
    ∃ s x x₀, (∀ i, (x i).natAbs ≤ η) ∧ x₀.natAbs ≤ η ∧ c = encryptWithCoins pk μ s x x₀ := by
  simp only [encrypt, ProbComp.eval_bind, ProbComp.eval_pure, PMF.mem_support_bind_iff,
    PMF.mem_support_pure_iff, ProbComp.mem_support_replicateFin_iff] at hc
  obtain ⟨s, -, x, hx, x₀, hx₀, rfl⟩ := hc
  exact ⟨s, x, x₀, fun i => (ProbComp.mem_support_sampleCenteredBinomial_iff η (x i)).mp (hx i),
    (ProbComp.mem_support_sampleCenteredBinomial_iff η x₀).mp hx₀, rfl⟩

/-- Every generated key and supported ciphertext decrypt correctly when
`4 * (m * η + η) < 2 ^ w`. -/
theorem keyGen_encrypt_correct {n m w η : ℕ} (hw : 0 < w) (hmargin : 4 * (m * η + η) < 2 ^ w)
    {keys : PublicKey n m w × (Fin m → ℤ)} (hkeys : keys ∈ (ProbComp.eval (keyGen n m w)).support)
    (μ : Bool) {c : Ciphertext m w} (hc : c ∈ (ProbComp.eval (encrypt η keys.1 μ)).support) :
    decrypt keys.2 c = μ := by
  obtain ⟨hpk, he⟩ := mem_support_keyGen hkeys
  obtain ⟨s, x, x₀, hx, hx₀, rfl⟩ := mem_support_encrypt hc
  rw [hpk]
  exact decrypt_encryptWithCoins _ _ μ s x x₀ hw he hx hx₀ (by simpa using hmargin)

/-- The public key of a uniform binary secret is statistically close to a uniform pair. -/
theorem dist_keyGen_uniform_le (n m w : ℕ) :
    dist ((ProbComp.eval (keyGen n m w)).map Prod.fst)
        (do
          let A ← PMF.uniformOfFintype (Matrix (Fin m) (Fin n) (ZMod (2 ^ w)))
          let u ← PMF.uniformOfFintype (Fin n → ZMod (2 ^ w))
          return (A, u)) ≤
      Real.sqrt ((2 : ℝ) ^ (w * n) / (2 : ℝ) ^ m) / 2 := by
  classical
  let rowBool : (Fin m → Bool) ≃ Matrix (Fin 1) (Fin m) Bool :=
    { toFun := fun b => Matrix.of fun _ => b
      invFun := fun M => M 0
      left_inv := fun _ => rfl
      right_inv := fun M => by ext i j; fin_cases i; rfl }
  let rowResidue : (Fin n → ZMod (2 ^ w)) ≃ Matrix (Fin 1) (Fin n) (ZMod (2 ^ w)) :=
    { toFun := fun u => Matrix.of fun _ => u
      invFun := fun M => M 0
      left_inv := fun _ => rfl
      right_inv := fun M => by ext i j; fin_cases i; rfl }
  let cont : Matrix (Fin m) (Fin n) (ZMod (2 ^ w)) →
      Matrix (Fin 1) (Fin n) (ZMod (2 ^ w)) → PMF (PublicKey n m w) :=
    fun A r => PMF.pure (A, r 0)
  have hL : (ProbComp.eval (keyGen n m w)).map Prod.fst =
      (PMF.uniformOfFintype (Matrix (Fin m) (Fin n) (ZMod (2 ^ w)))).bind fun A =>
        (PMF.uniformOfFintype (Matrix (Fin 1) (Fin m) Bool)).bind fun r =>
          cont A (r.map (fun bit => (bit.toNat : ZMod (2 ^ w))) * A) := by
    rw [← PMF.uniformOfFintype_map_equiv rowBool]
    simp only [keyGen, ProbComp.eval_bind, ProbComp.eval_pure, LWE.eval_sampleMatrix,
      ProbComp.eval_replicateFin, ProbComp.eval_uniform, PMF.pi_uniformOfFintype, PMF.map_bind,
      PMF.pure_map, PMF.bind_map]
    congr 1 with A : 1
    simp only [Function.comp_def]
    congr 1 with b : 1
    refine congrArg PMF.pure (Prod.ext rfl ?_)
    funext j
    simp only [publicKeyOf, castVector, Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Int.cast_natCast, Matrix.map_apply]
    rfl
  have hR : (do
        let A ← PMF.uniformOfFintype (Matrix (Fin m) (Fin n) (ZMod (2 ^ w)))
        let u ← PMF.uniformOfFintype (Fin n → ZMod (2 ^ w))
        return ((A, u) : PublicKey n m w)) =
      (PMF.uniformOfFintype (Matrix (Fin m) (Fin n) (ZMod (2 ^ w)))).bind fun A =>
        (PMF.uniformOfFintype (Matrix (Fin 1) (Fin n) (ZMod (2 ^ w)))).bind (cont A) := by
    rw [← PMF.uniformOfFintype_map_equiv rowResidue]
    simp only [PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.bind_map]
    congr 1 with A : 1
  rw [hL, hR]
  simpa [pow_mul] using
    BitString.SubsetSum.dist_bind_mul_le (q := 2 ^ w) (m := m) (d := n) (Rows := Fin 1) cont

/-! ### Preimage-sampleable trapdoors -/

/-- The algorithm interface of a preimage-sampleable trapdoor function
[GentryPeikertVaikuntanathan2008, Section 5]: `trapGen` outputs a public matrix with a trapdoor,
and `samplePre` uses the trapdoor to sample an integer preimage `e` of a syndrome `u`, meaning
`eᵀ A = u`. No one-wayness or distributional requirement is imposed. -/
structure GPVTrapdoor (n m w : ℕ) (Trapdoor : Type) where
  /-- Generate a public matrix together with its trapdoor. -/
  trapGen : ProbComp (Matrix (Fin m) (Fin n) (ZMod (2 ^ w)) × Trapdoor)
  /-- Sample a preimage of a syndrome using the trapdoor. -/
  samplePre : Trapdoor → (Fin n → ZMod (2 ^ w)) → ProbComp (Fin m → ℤ)

namespace GPVTrapdoor

variable {n m w : ℕ} {Trapdoor : Type}

/-- On every generated matrix and every syndrome, each sampled preimage `e` satisfies `eᵀ A = u`
and has entries of magnitude at most `bound`. -/
def SamplesShortPreimages (T : GPVTrapdoor n m w Trapdoor) (bound : ℕ) : Prop :=
  ∀ keys ∈ (ProbComp.eval T.trapGen).support, ∀ u : Fin n → ZMod (2 ^ w),
    ∀ e ∈ (ProbComp.eval (T.samplePre keys.2 u)).support,
      castVector w e ᵥ* keys.1 = u ∧ ∀ i, (e i).natAbs ≤ bound

/-- Extract the dual-Regev secret key for syndrome `u`: the key-extraction step of the
identity-based scheme, where `u` is the hash of an identity. -/
noncomputable def extract (T : GPVTrapdoor n m w Trapdoor)
    (keys : Matrix (Fin m) (Fin n) (ZMod (2 ^ w)) × Trapdoor) (u : Fin n → ZMod (2 ^ w)) :
    ProbComp (Fin m → ℤ) :=
  T.samplePre keys.2 u

/-- Extracted keys decrypt every dual-Regev encryption under `(A, u)` with zero error when
`4 * (m * (bound * η) + η) < 2 ^ w`. -/
theorem decrypt_encryptWithCoins_extract {bound η : ℕ} (T : GPVTrapdoor n m w Trapdoor)
    (hT : T.SamplesShortPreimages bound)
    {keys : Matrix (Fin m) (Fin n) (ZMod (2 ^ w)) × Trapdoor}
    (hkeys : keys ∈ (ProbComp.eval T.trapGen).support) (u : Fin n → ZMod (2 ^ w))
    {e : Fin m → ℤ} (he : e ∈ (ProbComp.eval (T.extract keys u)).support)
    (μ : Bool) (s : Fin n → ZMod (2 ^ w)) (x : Fin m → ℤ) (x₀ : ℤ) (hw : 0 < w)
    (hx : ∀ i, (x i).natAbs ≤ η) (hx₀ : x₀.natAbs ≤ η)
    (hmargin : 4 * (m * (bound * η) + η) < 2 ^ w) :
    decrypt e (encryptWithCoins (keys.1, u) μ s x x₀) = μ := by
  obtain ⟨hu, hshort⟩ := hT keys hkeys u e he
  have hpk : ((keys.1, u) : PublicKey n m w) = publicKeyOf keys.1 e := by
    rw [publicKeyOf, hu]
  rw [hpk]
  exact decrypt_encryptWithCoins _ _ μ s x x₀ hw hshort hx hx₀ hmargin

end GPVTrapdoor

end Cslib.Crypto.DualRegev
