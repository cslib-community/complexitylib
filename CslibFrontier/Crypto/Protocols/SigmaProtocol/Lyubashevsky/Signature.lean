/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.SigmaProtocol.Identification
public import CslibFrontier.Crypto.Protocols.SigmaProtocol.Abort.FiatShamir
public import CslibFrontier.Crypto.Protocols.SigmaProtocol.Lyubashevsky
import CslibFrontier.Probability.PMF

/-!
# Lyubashevsky Fiat–Shamir-with-aborts signatures and SIS reductions

This module connects Lyubashevsky's lattice-based identification protocol ([Lyubashevsky2009],
[Lyubashevsky2012]) and general Sigma protocols with aborts (`Abort.lean`) to the homogeneous
Short Integer Solution (`SIS`) problem and to Fiat–Shamir-with-aborts signature schemes:

1. **SIS collision and witness-invariance reduction.** Special soundness of `lyubashevsky`
   extracts a kernel vector `u = (z - z', ĉ' - ĉ)` of `[A | T]`. When the public key `(A, T)` is
   generated from a short secret key `S` satisfying `lyubashevskyRelation η S (A, T)` (`A S = T`
   and `|S_{i,j}| ≤ η`), folding the challenge half through `S` via
   `extractSISFromRelaxedWitness S u = (z - z') + S (ĉ' - ĉ)` produces a short vector in the
   homogeneous kernel of `A` modulo `q`. Because the protocol's accepted transcripts are
   statistically independent of which witness `S` was used (`lyubashevsky_nonAbortSpecialHVZK`),
   any extracted response difference `z - z'` that does not coincide with `S (ĉ - ĉ')` yields a
   nonzero short integer solution for `A` with norm bound `2 (γ - β) + k η`
   (`isSISSolution_extractSISFromRelaxedWitness`, `lyubashevskyForkToSIS`). For a single secret
   column `s` and integer challenge difference `Δc`, `isSISSolution_sub_smul_secret` gives the
   corresponding `2 γ + |Δc| η` reduction directly.
2. **Identification security from the relaxed `[A | T]` relation.** For any key generator, the
   generic rewinding reduction of `Identification.lean` bounds direct impersonation attacks
   against `lyubashevsky` by `1 / 2 ^ k + √ε'`, where `ε'` is the probability that rewinding finds
   a short integer solution for `[A | T]` (`lyubashevsky_succProbability_directAttack_le`). This
   module does not compose that bound with the reduction of item 1 from `[A | T]` to `A`, so it
   gives no impersonation bound in terms of a SIS solver for `A`.
3. **Fiat–Shamir with aborts (`FiatShamirWithAborts`).** The generic API is publicly reexported
   from `Abort.FiatShamir`. For any aborting Sigma protocol
   `P : SigmaProtocol X Y T C (Option Z)` and random-oracle hash function `h : M × T → C`, a
   single signing attempt (`fsAbortSignAttempt`) commits to `t`, queries `c = h (msg, t)`, and
   outputs `some (t, z)` when `P.respond` succeeds or `none` on an abort. Bounded signing
   (`fsAbortSignBounded`) repeats up to `K` independent attempts, reducing the abort probability to
   `(p_abort) ^ K` (`fsAbortSignBounded_apply_none`). Non-abort completeness ensures that every
   produced signature passes `fsAbortVerify` (`fsAbortVerify_of_fsAbortSignAttempt_eq_some`,
   `fsAbortVerify_of_fsAbortSignBounded_eq_some`), and two valid signatures sharing a commitment
   at distinct random-oracle challenges yield an extracted witness (`fsAbortForkExtract`) and, for
   `lyubashevsky`, a short integer solution (`lyubashevskySignatureForkToRelaxedSIS`,
   `lyubashevskySignatureForkToSIS`).

## Main definitions

* `Cslib.Crypto.Protocols.SigmaProtocol.extractSISFromRelaxedWitness`,
  `Cslib.Crypto.Protocols.SigmaProtocol.extractSISFromTwoTranscripts`: fold a relaxed `[A | T]`
  kernel vector into a homogeneous `A`-kernel vector using the secret key `S`.
* `Cslib.Crypto.Protocols.SigmaProtocol.lyubashevskyKeyGen`: key generation for Lyubashevsky
  identification and signatures.
* `Cslib.Crypto.Protocols.SigmaProtocol.FiatShamirWithAborts`: bundled Fiat–Shamir-with-aborts
  signature operations for an aborting Sigma protocol.
* `Cslib.Crypto.Protocols.SigmaProtocol.fsAbortSignStep`,
  `Cslib.Crypto.Protocols.SigmaProtocol.fsAbortSignAttempt`,
  `Cslib.Crypto.Protocols.SigmaProtocol.fsAbortSignBounded`,
  `Cslib.Crypto.Protocols.SigmaProtocol.fsAbortVerify`: single-attempt and bounded `K`-attempt
  signing and verification with aborts.
* `Cslib.Crypto.Protocols.SigmaProtocol.lyubashevskySignAttempt`,
  `Cslib.Crypto.Protocols.SigmaProtocol.lyubashevskySignBounded`,
  `Cslib.Crypto.Protocols.SigmaProtocol.lyubashevskyVerifySig`: specialization to Lyubashevsky's
  lattice protocol.

## Main results

* `Cslib.Crypto.Protocols.SigmaProtocol.isSISSolution_sub_smul_secret`,
  `Cslib.Crypto.Protocols.SigmaProtocol.isSISSolution_sub_secret`: scalar-challenge SIS collision
  reduction.
* `Cslib.Crypto.Protocols.SigmaProtocol.isSISSolution_extractSISFromRelaxedWitness`,
  `Cslib.Crypto.Protocols.SigmaProtocol.lyubashevskyForkToSIS`: matrix-challenge SIS collision
  reduction for `lyubashevsky`.
* `Cslib.Crypto.Protocols.SigmaProtocol.lyubashevsky_succProbability_directAttack_le`: direct
  impersonation bound for Lyubashevsky identification.
* `Cslib.Crypto.Protocols.SigmaProtocol.fsAbortVerify_of_fsAbortSignAttempt_eq_some`,
  `Cslib.Crypto.Protocols.SigmaProtocol.fsAbortVerify_of_fsAbortSignBounded_eq_some`,
  `Cslib.Crypto.Protocols.SigmaProtocol.fsAbortSignBounded_apply_none`: correctness and exact
  retry abort probability for Fiat–Shamir with aborts.
* `Cslib.Crypto.Protocols.SigmaProtocol.fsAbortForkExtract`,
  `Cslib.Crypto.Protocols.SigmaProtocol.lyubashevskySignatureForkToRelaxedSIS`,
  `Cslib.Crypto.Protocols.SigmaProtocol.lyubashevskySignatureForkToSIS`: forking extraction for
  Fiat–Shamir-with-aborts and Lyubashevsky signatures.

## References

* [V. Lyubashevsky, *Fiat-Shamir with Aborts: Applications to Lattice and Factoring-Based
  Signatures*][Lyubashevsky2009]
* [V. Lyubashevsky, *Lattice Signatures without Trapdoors*][Lyubashevsky2012]
* [L. Ducas et al., *CRYSTALS-Dilithium: A Lattice-Based Digital Signature
  Scheme*][DucasEtAl2018]
-/

@[expose] public section

namespace Cslib.Crypto.Protocols.SigmaProtocol

open Probability Probability.PMF
open scoped ENNReal _root_.Matrix

/-! ### Homogeneous SIS reduction from relaxed witnesses -/

section SISReduction

variable {n m k q : ℕ}

/-- **Scalar-challenge SIS reduction.** If `A s = t (mod q)` with `‖s‖∞ ≤ η`, and `v` satisfies
`A v = Δc • t (mod q)` with `‖v‖∞ ≤ B` and `v ≠ Δc • s`, then `v - Δc • s` is a short integer
solution for `A` with bound `B + |Δc| η`. -/
theorem isSISSolution_sub_smul_secret {B η : ℕ}
    {A : Matrix (Fin n) (Fin m) (ZMod q)} {t : Fin n → ZMod q}
    {s v : Fin m → ℤ} {Δc : ℤ}
    (hsA : A *ᵥ (Int.cast ∘ s) = t) (hs : s ∈ intBox (Fin m) η)
    (hvA : A *ᵥ (Int.cast ∘ v) = (Δc : ZMod q) • t) (hv : v ∈ intBox (Fin m) B)
    (hne : v ≠ Δc • s) :
    SIS.IsSolution A (B + Δc.natAbs * η) (v - Δc • s) := by
  refine ⟨sub_ne_zero.mpr hne, fun i => ?_, ?_⟩
  · have hvi := mem_intBox.mp hv i
    have hsi := mem_intBox.mp hs i
    simp only [Pi.sub_apply, zsmul_eq_mul]
    calc |v i - (Δc * s) i| = |v i - Δc * s i| := rfl
      _ ≤ |v i| + |Δc * s i| := abs_sub _ _
      _ = |v i| + |Δc| * |s i| := by rw [abs_mul]
      _ ≤ (B : ℤ) + |Δc| * (η : ℤ) :=
        add_le_add hvi (mul_le_mul_of_nonneg_left hsi (abs_nonneg Δc))
      _ = ((B + Δc.natAbs * η : ℕ) : ℤ) := by
        rw [Nat.cast_add, Nat.cast_mul, Int.natCast_natAbs]
  · have hcast : (Int.cast ∘ (v - Δc • s) : Fin m → ZMod q) =
        (Int.cast ∘ v) - (Δc : ZMod q) • (Int.cast ∘ s) :=
      funext fun i => by simp [Pi.sub_apply, Pi.smul_apply]
    rw [hcast, Matrix.mulVec_sub, Matrix.mulVec_smul, hvA, hsA, sub_self]

/-- **Unit-challenge SIS reduction.** When `Δc = 1` (for example with binary challenges), any
`v ≠ s` with `A v = t (mod q)` and `‖v‖∞ ≤ B` yields a short integer solution `v - s` for `A`
with bound `B + η`. -/
theorem isSISSolution_sub_secret {B η : ℕ}
    {A : Matrix (Fin n) (Fin m) (ZMod q)} {t : Fin n → ZMod q}
    {s v : Fin m → ℤ}
    (hsA : A *ᵥ (Int.cast ∘ s) = t) (hs : s ∈ intBox (Fin m) η)
    (hvA : A *ᵥ (Int.cast ∘ v) = t) (hv : v ∈ intBox (Fin m) B)
    (hne : v ≠ s) :
    SIS.IsSolution A (B + η) (v - s) := by
  simpa using isSISSolution_sub_smul_secret (Δc := 1) hsA hs (by simpa using hvA) hv
    (by simpa using hne)

/-- Fold an extracted kernel vector `u : Fin m ⊕ Fin k → ℤ` of `[A | T]` into a kernel vector of
`A` using the secret witness `S : Matrix (Fin m) (Fin k) ℤ` satisfying `A S = T`. -/
def extractSISFromRelaxedWitness (S : Matrix (Fin m) (Fin k) ℤ)
    (u : Fin m ⊕ Fin k → ℤ) : Fin m → ℤ :=
  (u ∘ Sum.inl) + S *ᵥ (u ∘ Sum.inr)

/-- Extract a homogeneous `A`-kernel candidate directly from a secret key `S` and two transcripts
`(c, z)` and `(c', z')`: `(z - z') + S (ĉ' - ĉ) = (z - z') - S (ĉ - ĉ')`. -/
def extractSISFromTwoTranscripts (S : Matrix (Fin m) (Fin k) ℤ)
    (c : BitString k) (z : Option (Fin m → ℤ))
    (c' : BitString k) (z' : Option (Fin m → ℤ)) : Fin m → ℤ :=
  (z.getD 0 - z'.getD 0) + S *ᵥ (lyubashevskyChallenge c' - lyubashevskyChallenge c)

/-- `extractSISFromTwoTranscripts` is `extractSISFromRelaxedWitness` applied to
`lyubashevskyExtract`. -/
@[simp] theorem extractSISFromRelaxedWitness_lyubashevskyExtract
    (S : Matrix (Fin m) (Fin k) ℤ)
    (y : Matrix (Fin n) (Fin m) (ZMod q) × Matrix (Fin n) (Fin k) (ZMod q))
    (w : Fin n → ZMod q) (c : BitString k) (z : Option (Fin m → ℤ))
    (c' : BitString k) (z' : Option (Fin m → ℤ)) :
    extractSISFromRelaxedWitness S (lyubashevskyExtract n m k q y w c z c' z') =
      extractSISFromTwoTranscripts S c z c' z' :=
  rfl

/-- Equivalent subtraction form `(z - z') - S (ĉ - ĉ')` for `extractSISFromTwoTranscripts`. -/
theorem extractSISFromTwoTranscripts_eq_sub (S : Matrix (Fin m) (Fin k) ℤ)
    (c : BitString k) (z : Option (Fin m → ℤ))
    (c' : BitString k) (z' : Option (Fin m → ℤ)) :
    extractSISFromTwoTranscripts S c z c' z' =
      (z.getD 0 - z'.getD 0) - S *ᵥ (lyubashevskyChallenge c - lyubashevskyChallenge c') := by
  simp only [extractSISFromTwoTranscripts, sub_eq_add_neg, ← Matrix.mulVec_neg, neg_add_rev,
    neg_neg]

/-- If `A S = T (mod q)` and `[A | T] u = 0 (mod q)`, then `extractSISFromRelaxedWitness S u` lies
in the kernel of `A` modulo `q`. -/
theorem mulVec_extractSISFromRelaxedWitness_eq_zero
    {S : Matrix (Fin m) (Fin k) ℤ}
    {y : Matrix (Fin n) (Fin m) (ZMod q) × Matrix (Fin n) (Fin k) (ZMod q)}
    {u : Fin m ⊕ Fin k → ℤ}
    (hSy : y.1 * S.map Int.cast = y.2)
    (hu : Matrix.fromCols y.1 y.2 *ᵥ (Int.cast ∘ u) = 0) :
    y.1 *ᵥ (Int.cast ∘ extractSISFromRelaxedWitness S u) = 0 := by
  have hmul : (Int.cast ∘ (S *ᵥ (u ∘ Sum.inr)) : Fin m → ZMod q) =
      S.map Int.cast *ᵥ (Int.cast ∘ (u ∘ Sum.inr)) :=
    funext (RingHom.map_mulVec (Int.castRingHom (ZMod q)) S (u ∘ Sum.inr))
  have hadd : (Int.cast ∘ extractSISFromRelaxedWitness S u : Fin m → ZMod q) =
      (Int.cast ∘ (u ∘ Sum.inl)) + S.map Int.cast *ᵥ (Int.cast ∘ (u ∘ Sum.inr)) := by
    rw [extractSISFromRelaxedWitness,
      show (Int.cast ∘ ((u ∘ Sum.inl) + S *ᵥ (u ∘ Sum.inr)) : Fin m → ZMod q) =
        Int.cast ∘ (u ∘ Sum.inl) + Int.cast ∘ (S *ᵥ (u ∘ Sum.inr)) from
          funext fun i => Int.cast_add _ _,
      hmul]
  rw [hadd, Matrix.mulVec_add, Matrix.mulVec_mulVec, hSy]
  have hcols : Matrix.fromCols y.1 y.2 *ᵥ (Int.cast ∘ u) =
      y.1 *ᵥ (Int.cast ∘ (u ∘ Sum.inl)) + y.2 *ᵥ (Int.cast ∘ (u ∘ Sum.inr)) := by
    rw [Matrix.fromCols_mulVec]
    rfl
  rw [← hcols, hu]

/-- Sup-norm bound on `S *ᵥ v` when the entries of `S` are at most `η` and the entries of `v` are
at most `1`. -/
private theorem abs_mulVec_le_of_abs_le_one {η : ℕ} {S : Matrix (Fin m) (Fin k) ℤ}
    (hS : ∀ i j, |S i j| ≤ η) {v : Fin k → ℤ} (hv : ∀ j, |v j| ≤ 1) (i : Fin m) :
    |(S *ᵥ v) i| ≤ k * η := by
  calc |(S *ᵥ v) i| = |∑ j, S i j * v j| := rfl
    _ ≤ ∑ j, |S i j * v j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin k, (η : ℤ) := Finset.sum_le_sum fun j _ => by
      rw [abs_mul]
      exact (mul_le_of_le_one_right (abs_nonneg _) (hv j)).trans (hS i j)
    _ = ((k * η : ℕ) : ℤ) := by simp

/-- **Homogeneous SIS solution from a relaxed witness.** If `S` is a secret key for `y = (A, T)`
with entry bound `η`, and `u` is a kernel vector of `[A | T]` with `‖u_inl‖∞ ≤ B`,
`‖u_inr‖∞ ≤ 1`, and `u_inl + S u_inr ≠ 0`, then `extractSISFromRelaxedWitness S u` is a short
integer solution for `A` with bound `B + k η`. -/
theorem isSISSolution_extractSISFromRelaxedWitness {B η : ℕ}
    {S : Matrix (Fin m) (Fin k) ℤ}
    {y : Matrix (Fin n) (Fin m) (ZMod q) × Matrix (Fin n) (Fin k) (ZMod q)}
    {u : Fin m ⊕ Fin k → ℤ}
    (hSy : lyubashevskyRelation η S y)
    (hu : Matrix.fromCols y.1 y.2 *ᵥ (Int.cast ∘ u) = 0)
    (hinl : ∀ i, |u (Sum.inl i)| ≤ B)
    (hinr : ∀ j, |u (Sum.inr j)| ≤ 1)
    (hne : extractSISFromRelaxedWitness S u ≠ 0) :
    SIS.IsSolution y.1 (B + k * η) (extractSISFromRelaxedWitness S u) := by
  refine ⟨hne, fun i => ?_, mulVec_extractSISFromRelaxedWitness_eq_zero hSy.1 hu⟩
  simp only [extractSISFromRelaxedWitness, Pi.add_apply, Function.comp_apply]
  calc |u (Sum.inl i) + (S *ᵥ (u ∘ Sum.inr)) i|
      ≤ |u (Sum.inl i)| + |(S *ᵥ (u ∘ Sum.inr)) i| := abs_add_le _ _
    _ ≤ (B : ℤ) + ((k * η : ℕ) : ℤ) :=
      add_le_add (hinl i) (abs_mulVec_le_of_abs_le_one hSy.2 hinr i)
    _ = ((B + k * η : ℕ) : ℤ) := by push_cast; rfl

/-- **Lyubashevsky forking to homogeneous SIS.** Given a statement `y = (A, T)` with secret witness
`S` in `lyubashevskyRelation η S y` and two accepting transcripts `(w, c, some z)` and
`(w, c', some z')` of `lyubashevsky n m k q γ β`, if the response difference `z - z'` differs from
the secret's response difference `S (ĉ - ĉ')`, then `extractSISFromTwoTranscripts` produces a short
integer solution for `A` with bound `2 (γ - β) + k η`. -/
theorem lyubashevskyForkToSIS {γ β η : ℕ}
    {S : Matrix (Fin m) (Fin k) ℤ}
    {y : Matrix (Fin n) (Fin m) (ZMod q) × Matrix (Fin n) (Fin k) (ZMod q)}
    {w : Fin n → ZMod q} {c c' : BitString k} {z z' : Fin m → ℤ}
    (hSy : lyubashevskyRelation η S y)
    (hz : (lyubashevsky n m k q γ β).Accepts y w c (some z))
    (hz' : (lyubashevsky n m k q γ β).Accepts y w c' (some z'))
    (hne : z - z' ≠ S *ᵥ (lyubashevskyChallenge c - lyubashevskyChallenge c')) :
    SIS.IsSolution y.1 (2 * (γ - β) + k * η)
      (extractSISFromTwoTranscripts S c (some z) c' (some z')) := by
  rw [lyubashevsky_accepts_some_iff] at hz hz'
  have hu : Matrix.fromCols y.1 y.2 *ᵥ
      (Int.cast ∘ lyubashevskyExtract n m k q y w c (some z) c' (some z')) = 0 := by
    rw [Matrix.fromCols_mulVec]
    simp only [lyubashevskyExtract, Option.getD_some]
    change y.1 *ᵥ (Int.cast ∘ (z - z')) + y.2 *ᵥ
      (Int.cast ∘ (lyubashevskyChallenge c' - lyubashevskyChallenge c)) = 0
    have hsub₁ : (Int.cast ∘ (z - z') : Fin m → ZMod q) = Int.cast ∘ z - Int.cast ∘ z' :=
      funext fun i => Int.cast_sub _ _
    have hsub₂ :
        (Int.cast ∘ (lyubashevskyChallenge c' - lyubashevskyChallenge c) : Fin k → ZMod q) =
          Int.cast ∘ lyubashevskyChallenge c' - Int.cast ∘ lyubashevskyChallenge c :=
      funext fun j => Int.cast_sub _ _
    rw [hsub₁, hsub₂, Matrix.mulVec_sub, Matrix.mulVec_sub, hz.2, hz'.2]
    abel
  have hinl (i : Fin m) :
      |lyubashevskyExtract n m k q y w c (some z) c' (some z') (Sum.inl i)| ≤
        ((2 * (γ - β) : ℕ) : ℤ) := by
    simp only [lyubashevskyExtract, Option.getD_some, Sum.elim_inl, Pi.sub_apply]
    have hzi := mem_intBox.mp hz.1 i
    have hzi' := mem_intBox.mp hz'.1 i
    calc |z i - z' i| ≤ |z i| + |z' i| := abs_sub _ _
      _ ≤ ((γ - β : ℕ) : ℤ) + ((γ - β : ℕ) : ℤ) := add_le_add hzi hzi'
      _ = ((2 * (γ - β) : ℕ) : ℤ) := by push_cast; ring
  have hinr (j : Fin k) :
      |lyubashevskyExtract n m k q y w c (some z) c' (some z') (Sum.inr j)| ≤ 1 := by
    simp only [lyubashevskyExtract, Sum.elim_inr, Pi.sub_apply, lyubashevskyChallenge]
    split_ifs <;> simp
  have hne' : extractSISFromRelaxedWitness S
      (lyubashevskyExtract n m k q y w c (some z) c' (some z')) ≠ 0 := by
    rw [extractSISFromRelaxedWitness_lyubashevskyExtract, extractSISFromTwoTranscripts_eq_sub,
      Option.getD_some, Option.getD_some]
    exact sub_ne_zero.mpr hne
  exact isSISSolution_extractSISFromRelaxedWitness hSy hu hinl hinr hne'

end SISReduction

/-! ### Lyubashevsky key generation and identification security -/

section Identification

variable {n m k q : ℕ}

/-- Key generation for Lyubashevsky's identification and signature schemes: draw a uniform matrix
`A ∈ ℤ_q^{n×m}` and `k` independent columns of `S` uniformly from `[-η, η]^m`, and set `T = A S`. -/
noncomputable def lyubashevskyKeyGen (n m k q η : ℕ) [NeZero q] :
    PMF (Matrix (Fin m) (Fin k) ℤ ×
      (Matrix (Fin n) (Fin m) (ZMod q) × Matrix (Fin n) (Fin k) (ZMod q))) := do
  let A ← PMF.uniformOfFintype (Matrix (Fin n) (Fin m) (ZMod q))
  let cols ← PMF.iid (uniformOfFinset (intBox (Fin m) η) (intBox_nonempty η)) k
  let S : Matrix (Fin m) (Fin k) ℤ := Matrix.of fun i j => cols j i
  return (S, (A, A * S.map Int.cast))

/-- Every key pair produced by `lyubashevskyKeyGen` satisfies `lyubashevskyRelation η`. -/
theorem mem_support_lyubashevskyKeyGen [NeZero q] {η : ℕ}
    {key : Matrix (Fin m) (Fin k) ℤ ×
      (Matrix (Fin n) (Fin m) (ZMod q) × Matrix (Fin n) (Fin k) (ZMod q))}
    (h : key ∈ (lyubashevskyKeyGen n m k q η).support) :
    lyubashevskyRelation η key.1 key.2 := by
  simp only [lyubashevskyKeyGen, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
    PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at h
  obtain ⟨A, -, cols, hcols, rfl⟩ := h
  refine ⟨rfl, fun i j => ?_⟩
  have hj := (PMF.mem_support_iid_iff _ _).mp hcols j
  rw [mem_support_uniformOfFinset_iff, mem_intBox] at hj
  simpa using hj i

/-- **Lyubashevsky identification against direct attacks.** For any key generator and direct
impersonator `A`, the impersonator's success probability against `lyubashevsky n m k q γ β` is at
most `1 / 2 ^ k + √ε'`, where `ε'` is the probability that rewinding `A` extracts a short integer
solution for `[A | T]` with bound `max (2 (γ - β)) 1`. -/
theorem lyubashevsky_succProbability_directAttack_le {γ β : ℕ}
    (keyGen : PMF (Matrix (Fin m) (Fin k) ℤ ×
      (Matrix (Fin n) (Fin m) (ZMod q) × Matrix (Fin n) (Fin k) (ZMod q))))
    (A : Impersonator
      (Matrix (Fin n) (Fin m) (ZMod q) × Matrix (Fin n) (Fin k) (ZMod q))
      (Fin n → ZMod q) (BitString k) (Option (Fin m → ℤ))) :
    (Game.succProbability ((lyubashevsky n m k q γ β).directAttack keyGen A) : ℝ) ≤
      1 / 2 ^ k + √(Game.succProbability
        (oneWayGame (keyGen.map fun key => ((0 : Fin m ⊕ Fin k → ℤ), key.2))
          (fun u y => SIS.IsSolution (Matrix.fromCols y.1 y.2) (max (2 * (γ - β)) 1) u)
          (A.rewind (lyubashevskyExtract n m k q)))) := by
  let P' : SigmaProtocol (Fin m ⊕ Fin k → ℤ)
      (Matrix (Fin n) (Fin m) (ZMod q) × Matrix (Fin n) (Fin k) (ZMod q))
      (Fin n → ZMod q) (BitString k) (Option (Fin m → ℤ)) :=
    { State := Fin m → ℤ
      commit := fun _ y => (lyubashevsky n m k q γ β).commit 0 y
      respond := fun _ y r c => (lyubashevsky n m k q γ β).respond 0 y r c
      verify := (lyubashevsky n m k q γ β).verify }
  have hP' : P'.SpecialSoundness
      (fun u y => SIS.IsSolution (Matrix.fromCols y.1 y.2) (max (2 * (γ - β)) 1) u)
      (lyubashevskyExtract n m k q) :=
    lyubashevsky_specialSoundness (n := n) (m := m) (k := k) (q := q) (γ := γ) (β := β)
  have hdir : (lyubashevsky n m k q γ β).directAttack keyGen A =
      P'.directAttack (keyGen.map fun key => ((0 : Fin m ⊕ Fin k → ℤ), key.2)) A := by
    simp only [directAttack, P', PMF.monad_bind_eq_bind, PMF.bind_map]
    rfl
  rw [hdir]
  have h := succProbability_directAttack_le
    (hP'.specialSoundOn (keyGen.map fun key => ((0 : Fin m ⊕ Fin k → ℤ), key.2))) A
  simpa [Fintype.card_pi, Fintype.card_bool] using h

end Identification

/-! ### Fiat–Shamir with aborts -/

section FiatShamirWithAborts

universe u
variable {X Y T C Z M : Type u}

/-! ### Specialization to Lyubashevsky's lattice signature scheme -/

variable {n m k q γ β : ℕ} {M : Type}

/-- Single signing attempt for Lyubashevsky's lattice signature scheme. -/
noncomputable def lyubashevskySignAttempt (n m k q γ β : ℕ)
    (h : M × (Fin n → ZMod q) → BitString k)
    (S : Matrix (Fin m) (Fin k) ℤ)
    (y : Matrix (Fin n) (Fin m) (ZMod q) × Matrix (Fin n) (Fin k) (ZMod q))
    (msg : M) : PMF (Option ((Fin n → ZMod q) × (Fin m → ℤ))) :=
  fsAbortSignAttempt (lyubashevsky n m k q γ β) h S y msg

/-- Bounded `K`-attempt signing for Lyubashevsky's lattice signature scheme. -/
noncomputable def lyubashevskySignBounded (n m k q γ β : ℕ)
    (h : M × (Fin n → ZMod q) → BitString k) (K : ℕ)
    (S : Matrix (Fin m) (Fin k) ℤ)
    (y : Matrix (Fin n) (Fin m) (ZMod q) × Matrix (Fin n) (Fin k) (ZMod q))
    (msg : M) : PMF (Option ((Fin n → ZMod q) × (Fin m → ℤ))) :=
  fsAbortSignBounded (lyubashevsky n m k q γ β) h K S y msg

/-- Verification of a Lyubashevsky signature `(w, z)` on `msg` under random oracle `h`. -/
noncomputable def lyubashevskyVerifySig (n m k q γ β : ℕ)
    (h : M × (Fin n → ZMod q) → BitString k)
    (y : Matrix (Fin n) (Fin m) (ZMod q) × Matrix (Fin n) (Fin k) (ZMod q))
    (msg : M) (sig : (Fin n → ZMod q) × (Fin m → ℤ)) : Bool :=
  fsAbortVerify (lyubashevsky n m k q γ β) h y msg sig

/-- Every non-aborting single attempt of `lyubashevskySignAttempt` produces a valid signature. -/
theorem lyubashevskyVerifySig_of_lyubashevskySignAttempt_eq_some
    (h : M × (Fin n → ZMod q) → BitString k)
    {S : Matrix (Fin m) (Fin k) ℤ}
    {y : Matrix (Fin n) (Fin m) (ZMod q) × Matrix (Fin n) (Fin k) (ZMod q)}
    (hSy : y.1 * S.map Int.cast = y.2) {msg : M}
    {sig : (Fin n → ZMod q) × (Fin m → ℤ)}
    (hsig : some sig ∈ (lyubashevskySignAttempt n m k q γ β h S y msg).support) :
    lyubashevskyVerifySig n m k q γ β h y msg sig = true :=
  fsAbortVerify_of_fsAbortSignAttempt_eq_some lyubashevsky_nonAbortComplete h hSy hsig

/-- Every signature output by `lyubashevskySignBounded` verifies. -/
theorem lyubashevskyVerifySig_of_lyubashevskySignBounded_eq_some
    (h : M × (Fin n → ZMod q) → BitString k) {K : ℕ}
    {S : Matrix (Fin m) (Fin k) ℤ}
    {y : Matrix (Fin n) (Fin m) (ZMod q) × Matrix (Fin n) (Fin k) (ZMod q)}
    (hSy : y.1 * S.map Int.cast = y.2) {msg : M}
    {sig : (Fin n → ZMod q) × (Fin m → ℤ)}
    (hsig : some sig ∈ (lyubashevskySignBounded n m k q γ β h K S y msg).support) :
    lyubashevskyVerifySig n m k q γ β h y msg sig = true :=
  fsAbortVerify_of_fsAbortSignBounded_eq_some lyubashevsky_nonAbortComplete h hSy hsig

/-- Abort probability of `K`-attempt Lyubashevsky signing. -/
theorem lyubashevskySignBounded_apply_none
    (h : M × (Fin n → ZMod q) → BitString k) (K : ℕ)
    (S : Matrix (Fin m) (Fin k) ℤ)
    (y : Matrix (Fin n) (Fin m) (ZMod q) × Matrix (Fin n) (Fin k) (ZMod q))
    (msg : M) :
    lyubashevskySignBounded n m k q γ β h K S y msg none =
      (lyubashevskySignAttempt n m k q γ β h S y msg none) ^ K :=
  fsAbortSignBounded_apply_none (lyubashevsky n m k q γ β) h K S y msg

/-- **Forking extraction for Lyubashevsky signatures (relaxed `[A | T]` relation).** Two valid
Lyubashevsky signatures `(w, z₁)` and `(w, z₂)` on the same commitment `w` with distinct
random-oracle challenges `h₁ (msg₁, w) ≠ h₂ (msg₂, w)` yield a short integer solution for
`[A | T]` with bound `max (2 (γ - β)) 1`. -/
theorem lyubashevskySignatureForkToRelaxedSIS
    {h₁ h₂ : M × (Fin n → ZMod q) → BitString k}
    {y : Matrix (Fin n) (Fin m) (ZMod q) × Matrix (Fin n) (Fin k) (ZMod q)}
    {msg₁ msg₂ : M} {w : Fin n → ZMod q} {z₁ z₂ : Fin m → ℤ}
    (hc : h₁ (msg₁, w) ≠ h₂ (msg₂, w))
    (hv₁ : lyubashevskyVerifySig n m k q γ β h₁ y msg₁ (w, z₁) = true)
    (hv₂ : lyubashevskyVerifySig n m k q γ β h₂ y msg₂ (w, z₂) = true) :
    SIS.IsSolution (Matrix.fromCols y.1 y.2) (max (2 * (γ - β)) 1)
      (lyubashevskyExtract n m k q y w (h₁ (msg₁, w)) (some z₁) (h₂ (msg₂, w)) (some z₂)) :=
  fsAbortForkExtract lyubashevsky_specialSoundness hc hv₁ hv₂

/-- **Forking extraction for Lyubashevsky signatures (homogeneous `A` SIS relation).** When `y`
has a secret key `S` in `lyubashevskyRelation η S y`, two valid signatures `(w, z₁)` and `(w, z₂)`
whose response difference `z₁ - z₂` differs from `S (ĉ₁ - ĉ₂)` yield a short integer solution for
`y.1` (`A`) with bound `2 (γ - β) + k η`. -/
theorem lyubashevskySignatureForkToSIS {η : ℕ}
    {h₁ h₂ : M × (Fin n → ZMod q) → BitString k}
    {S : Matrix (Fin m) (Fin k) ℤ}
    {y : Matrix (Fin n) (Fin m) (ZMod q) × Matrix (Fin n) (Fin k) (ZMod q)}
    {msg₁ msg₂ : M} {w : Fin n → ZMod q} {z₁ z₂ : Fin m → ℤ}
    (hSy : lyubashevskyRelation η S y)
    (hv₁ : lyubashevskyVerifySig n m k q γ β h₁ y msg₁ (w, z₁) = true)
    (hv₂ : lyubashevskyVerifySig n m k q γ β h₂ y msg₂ (w, z₂) = true)
    (hne : z₁ - z₂ ≠
      S *ᵥ (lyubashevskyChallenge (h₁ (msg₁, w)) - lyubashevskyChallenge (h₂ (msg₂, w)))) :
    SIS.IsSolution y.1 (2 * (γ - β) + k * η)
      (extractSISFromTwoTranscripts S (h₁ (msg₁, w)) (some z₁) (h₂ (msg₂, w)) (some z₂)) :=
  lyubashevskyForkToSIS hSy hv₁ hv₂ hne

end FiatShamirWithAborts

end Cslib.Crypto.Protocols.SigmaProtocol
