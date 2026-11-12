/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.MLDSA.Decompose
public import CslibFrontier.Crypto.Computational.SIS.ModuleEncryption
public import CslibFrontier.Languages.Probabilistic.Basic
import Mathlib.Tactic.Linarith

/-!
# ML-DSA: parameters, signing with aborts, verification and correctness

This module states the CRYSTALS-Dilithium signature scheme ([DucasEtAl2018]), standardized as
ML-DSA in [NISTFIPS204], over `R_q = ℤ_q[X] / (X^n + 1)` (coefficient vectors `Fin n → ZMod q`
with `Cslib.Crypto.negacyclicMul`), and proves its correctness.

The model is the *uncompressed-public-key* scheme: the public key is `(A, t)` with
`t = A s₁ + s₂`, a signature is `(z, c)`, and verification recomputes
`w₁' = HighBits(A z - c t)` and checks `c = H(w₁', M)`. It omits the parts of [NISTFIPS204]
that only shrink keys and signatures or derive randomness from seeds: `Power2Round` of `t`, the
hint vector (`MakeHint` / `UseHint`), the byte encodings, the `ExpandA` / `ExpandS` /
`ExpandMask` expansions and the message representative `μ`. The hash-to-ball map
`SampleInBall ∘ H` is an arbitrary function `Hash`, and the masking vector `y` of each attempt is
drawn from an arbitrary `ProbComp` sampler.

* **Parameters.** `Params` bundles `(n, q, k, ℓ, η, γ₁, γ₂, τ, β)`; `Params.mldsa44`,
  `Params.mldsa65` and `Params.mldsa87` are the three parameter sets of [NISTFIPS204]
  (Section 4), and `Params.Valid` collects the side conditions that correctness uses.
* **Challenges.** `InBall τ c` says that `c` has coefficients in `{-1, 0, 1}` (read through
  centered representatives) and exactly `τ` nonzero coefficients. Multiplying an `η`-short
  polynomial by such a challenge gives a `τ η`-short polynomial (`abs_valMinAbs_negacyclicMul_le`).
* **Signing.** One attempt (`signAttempt`) computes `w = A y`, `c = H(HighBits(w), M)`,
  `z = y + c s₁`, and accepts iff `‖z‖_∞ < γ₁ - β` and `‖LowBits(w - c s₂)‖_∞ < γ₂ - β`.
  `sign` repeats attempts with fresh masks, at most `K` times (rejection sampling).
* **Correctness.** Every accepted signature verifies (`verify_signAttempt`, `verify_sign`): the
  verifier's `A z - c t` equals `w - c s₂`, whose high bits equal those of `w` because `c s₂` is
  `β`-short and the low bits of `w - c s₂` are below `γ₂ - β`
  (`Cslib.Crypto.MLDSA.highBits_add_of_abs_lowBits_lt`).

## Main definitions

* `Cslib.Crypto.MLDSA.Params`, `Cslib.Crypto.MLDSA.Params.Valid`,
  `Cslib.Crypto.MLDSA.Params.mldsa44`, `Cslib.Crypto.MLDSA.Params.mldsa65`,
  `Cslib.Crypto.MLDSA.Params.mldsa87`: parameters.
* `Cslib.Crypto.MLDSA.InBall`: the challenge set `B_τ`.
* `Cslib.Crypto.MLDSA.PublicKey`, `Cslib.Crypto.MLDSA.SecretKey`,
  `Cslib.Crypto.MLDSA.SecretKey.publicKey`: keys, with `t = A s₁ + s₂`.
* `Cslib.Crypto.MLDSA.signAttempt`, `Cslib.Crypto.MLDSA.sign`, `Cslib.Crypto.MLDSA.verify`:
  signing with aborts and verification.

## Main results

* `Cslib.Crypto.MLDSA.abs_valMinAbs_negacyclicMul_le`: challenge times short is short.
* `Cslib.Crypto.MLDSA.verify_signAttempt`, `Cslib.Crypto.MLDSA.verify_sign`: correctness.
* `Cslib.Crypto.MLDSA.Params.valid_mldsa44`, `Cslib.Crypto.MLDSA.Params.valid_mldsa65`,
  `Cslib.Crypto.MLDSA.Params.valid_mldsa87`: the standard parameter sets are valid.

## References

* [L. Ducas et al., *CRYSTALS-Dilithium: A Lattice-Based Digital Signature
  Scheme*][DucasEtAl2018]
* [National Institute of Standards and Technology, *Module-Lattice-Based Digital Signature
  Standard*][NISTFIPS204]
-/

@[expose] public section

namespace Cslib.Crypto.MLDSA

open Cslib.Probability

/-! ### Parameters -/

/-- ML-DSA parameters: ring degree `n`, modulus `q`, module ranks `k × ℓ`, secret bound `η`,
masking range `γ₁`, low-order rounding range `γ₂` (the rounding range of `HighBits` is `2 γ₂`),
challenge weight `τ` and rejection margin `β` (`τ η` in [NISTFIPS204]). -/
structure Params where
  /-- Ring degree. -/
  n : ℕ
  /-- Modulus. -/
  q : ℕ
  /-- Number of rows of the public matrix. -/
  k : ℕ
  /-- Number of columns of the public matrix. -/
  ℓ : ℕ
  /-- Infinity-norm bound of the secret vectors. -/
  η : ℕ
  /-- Masking range. -/
  γ₁ : ℕ
  /-- Low-order rounding range. -/
  γ₂ : ℕ
  /-- Number of nonzero challenge coefficients. -/
  τ : ℕ
  /-- Rejection margin. -/
  β : ℕ

namespace Params

/-- ML-DSA-44 ([NISTFIPS204], Section 4). -/
def mldsa44 : Params where
  n := 256
  q := 8380417
  k := 4
  ℓ := 4
  η := 2
  γ₁ := 2 ^ 17
  γ₂ := (8380417 - 1) / 88
  τ := 39
  β := 78

/-- ML-DSA-65 ([NISTFIPS204], Section 4). -/
def mldsa65 : Params where
  n := 256
  q := 8380417
  k := 6
  ℓ := 5
  η := 4
  γ₁ := 2 ^ 19
  γ₂ := (8380417 - 1) / 32
  τ := 49
  β := 196

/-- ML-DSA-87 ([NISTFIPS204], Section 4). -/
def mldsa87 : Params where
  n := 256
  q := 8380417
  k := 8
  ℓ := 7
  η := 2
  γ₁ := 2 ^ 19
  γ₂ := (8380417 - 1) / 32
  τ := 60
  β := 120

/-- The side conditions used by correctness: `q > 1`, `γ₂ > 0`, the rounding range `2 γ₂`
divides `q - 1`, the margin covers challenge-times-secret products (`τ η ≤ β`), and these
products have centered representatives (`2 β < q`). These conditions do not require
`β < γ₁` or `β < γ₂`; without them every signing attempt aborts and correctness holds
vacuously. The standard parameter sets satisfy both. -/
structure Valid (P : Params) : Prop where
  one_lt_q : 1 < P.q
  γ₂_pos : 0 < P.γ₂
  two_mul_γ₂_dvd : 2 * P.γ₂ ∣ P.q - 1
  τ_mul_η_le_β : P.τ * P.η ≤ P.β
  two_mul_β_lt_q : 2 * P.β < P.q

theorem valid_mldsa44 : mldsa44.Valid := ⟨by decide, by decide, by decide, by decide, by decide⟩

theorem valid_mldsa65 : mldsa65.Valid := ⟨by decide, by decide, by decide, by decide, by decide⟩

theorem valid_mldsa87 : mldsa87.Valid := ⟨by decide, by decide, by decide, by decide, by decide⟩

end Params

/-! ### Challenges -/

section Challenge

variable {n q : ℕ}

/-- The challenge set `B_τ`: coefficients whose centered representatives lie in `{-1, 0, 1}`,
exactly `τ` of them nonzero. -/
def InBall (τ : ℕ) (c : Fin n → ZMod q) : Prop :=
  (∀ i, |(c i).valMinAbs| ≤ 1) ∧ (Finset.univ.filter fun i => c i ≠ 0).card = τ

instance (τ : ℕ) (c : Fin n → ZMod q) : Decidable (InBall τ c) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The centered `ℓ₁` norm of a challenge in `B_τ` is at most `τ`. -/
theorem sum_abs_valMinAbs_le {τ : ℕ} {c : Fin n → ZMod q} (hc : InBall τ c) :
    ∑ j, |(c j).valMinAbs| ≤ τ := by
  calc ∑ j, |(c j).valMinAbs| ≤ ∑ j, if c j ≠ 0 then (1 : ℤ) else 0 :=
        Finset.sum_le_sum fun j _ => by
          split_ifs with h
          · exact hc.1 j
          · rw [not_not.mp h, ZMod.valMinAbs_zero, abs_zero]
    _ = τ := by rw [Finset.sum_boole, hc.2]

/-- **Challenge times short is short.** If `c ∈ B_τ` and `‖s‖_∞ ≤ η`, with `2 τ η < q` so that
the product has centered representatives, then `‖c s‖_∞ ≤ τ η` in `R_q`. -/
theorem abs_valMinAbs_negacyclicMul_le [NeZero q] {τ η : ℕ} {c s : Fin n → ZMod q}
    (hc : InBall τ c) (hs : ∀ j, |(s j).valMinAbs| ≤ η) (hq : 2 * (τ * η) < q) (i : Fin n) :
    |(negacyclicMul c s i).valMinAbs| ≤ τ * η := by
  set ĉ : Fin n → ℤ := fun j => (c j).valMinAbs
  set ŝ : Fin n → ℤ := fun j => (s j).valMinAbs
  have hlift : negacyclicMul c s i = ((negacyclicMul ĉ ŝ i : ℤ) : ZMod q) := by
    have h := congrFun (map_negacyclicMul (Int.castRingHom (ZMod q)) ĉ ŝ) i
    simp only [Function.comp_apply, eq_intCast] at h
    rw [h]
    congr 1 <;> funext j <;> exact (ZMod.coe_valMinAbs _).symm
  have hbound : |negacyclicMul ĉ ŝ i| ≤ τ * η := by
    calc |negacyclicMul ĉ ŝ i| ≤ (∑ j, |ĉ j|) * η := abs_negacyclicMul_le_sum_abs_mul hs i
      _ ≤ τ * η := mul_le_mul_of_nonneg_right (sum_abs_valMinAbs_le hc) (by positivity)
  have hq' : (2 * (τ * η) : ℤ) < q := by exact_mod_cast hq
  rw [hlift, (ZMod.valMinAbs_spec _ _).mpr ⟨rfl, ?_⟩]
  · exact hbound
  · rw [abs_le] at hbound
    simp only [Set.mem_Ioc]
    constructor <;> linarith [hbound.1, hbound.2]

end Challenge

/-! ### Keys, signing and verification -/

variable (P : Params)

/-- An ML-DSA public key `(A, t)` with `A ∈ R_q^{k × ℓ}` and `t ∈ R_q^k`. -/
structure PublicKey where
  /-- The public matrix. -/
  A : Matrix (Fin P.k) (Fin P.ℓ) (Fin P.n → ZMod P.q)
  /-- The public vector `t = A s₁ + s₂`. -/
  t : Fin P.k → Fin P.n → ZMod P.q

/-- An ML-DSA secret key: the public matrix and the short secrets `s₁ ∈ R_q^ℓ`, `s₂ ∈ R_q^k`. -/
structure SecretKey where
  /-- The public matrix. -/
  A : Matrix (Fin P.k) (Fin P.ℓ) (Fin P.n → ZMod P.q)
  /-- The first secret vector. -/
  s₁ : Fin P.ℓ → Fin P.n → ZMod P.q
  /-- The second secret vector. -/
  s₂ : Fin P.k → Fin P.n → ZMod P.q

/-- The public key of a secret key: `(A, A s₁ + s₂)`. -/
def SecretKey.publicKey {P : Params} (sk : SecretKey P) : PublicKey P :=
  ⟨sk.A, moduleSISMap sk.A sk.s₁ + sk.s₂⟩

/-- A signature `(z, c)` with response `z ∈ R_q^ℓ` and challenge `c ∈ R_q`. -/
abbrev Signature := (Fin P.ℓ → Fin P.n → ZMod P.q) × (Fin P.n → ZMod P.q)

/-- The commitment hash `(w₁, M) ↦ c`, standing for `SampleInBall ∘ H` of [NISTFIPS204]: it maps
a high-bits vector `w₁ ∈ ℤ^{k × n}` and a message to a challenge polynomial. -/
abbrev Hash := (Fin P.k → Fin P.n → ℤ) × List Bool → (Fin P.n → ZMod P.q)

/-- Coefficientwise `HighBits` of a vector in `R_q^k`. -/
def highBitsVec (w : Fin P.k → Fin P.n → ZMod P.q) : Fin P.k → Fin P.n → ℤ :=
  fun i j => highBits P.q P.γ₂ (w i j)

/-- The `ℓ∞` acceptance bound on responses: `‖z‖_∞ < γ₁ - β`. -/
def ResponseShort (z : Fin P.ℓ → Fin P.n → ZMod P.q) : Prop :=
  ∀ i j, |(z i j).valMinAbs| < (P.γ₁ : ℤ) - P.β

instance (z : Fin P.ℓ → Fin P.n → ZMod P.q) : Decidable (ResponseShort P z) :=
  inferInstanceAs (Decidable (∀ _ _, _))

/-- The low-bits acceptance bound: `‖LowBits(r)‖_∞ < γ₂ - β`. -/
def LowBitsShort (r : Fin P.k → Fin P.n → ZMod P.q) : Prop :=
  ∀ i j, |lowBits P.q P.γ₂ (r i j)| < (P.γ₂ : ℤ) - P.β

instance (r : Fin P.k → Fin P.n → ZMod P.q) : Decidable (LowBitsShort P r) :=
  inferInstanceAs (Decidable (∀ _ _, _))

/-- The verifier's commitment `A z - c t`. -/
def verifierCommitment (pk : PublicKey P) (z : Fin P.ℓ → Fin P.n → ZMod P.q)
    (c : Fin P.n → ZMod P.q) : Fin P.k → Fin P.n → ZMod P.q :=
  moduleSISMap pk.A z - fun i => negacyclicMul c (pk.t i)

/-- One signing attempt with mask `y`: `w = A y`, `c = H(HighBits(w), M)`, `z = y + c s₁`;
output `(z, c)` when `‖z‖_∞ < γ₁ - β` and `‖LowBits(w - c s₂)‖_∞ < γ₂ - β`, and abort otherwise. -/
def signAttempt (H : Hash P) (sk : SecretKey P) (msg : List Bool)
    (y : Fin P.ℓ → Fin P.n → ZMod P.q) : Option (Signature P) :=
  let w := moduleSISMap sk.A y
  let c := H (highBitsVec P w, msg)
  let z := y + fun j => negacyclicMul c (sk.s₁ j)
  if ResponseShort P z ∧ LowBitsShort P (w - fun i => negacyclicMul c (sk.s₂ i)) then
    some (z, c)
  else none

/-- Signing by rejection sampling: draw a mask from `mask` and run `signAttempt`, retrying after
an abort, at most `K` times in total; `none` means that all `K` attempts aborted. -/
def sign (H : Hash P) (sk : SecretKey P) (mask : ProbComp (Fin P.ℓ → Fin P.n → ZMod P.q))
    (msg : List Bool) : ℕ → ProbComp (Option (Signature P))
  | 0 => pure none
  | K + 1 => do
    let y ← mask
    match signAttempt P H sk msg y with
    | some σ => pure (some σ)
    | none => sign H sk mask msg K

/-- Verification: accept `(z, c)` on `M` iff `‖z‖_∞ < γ₁ - β`, `c ∈ B_τ`, and
`c = H(HighBits(A z - c t), M)`. -/
def verify (H : Hash P) (pk : PublicKey P) (msg : List Bool) (σ : Signature P) : Bool :=
  decide (ResponseShort P σ.1) && decide (InBall P.τ σ.2) &&
    decide (H (highBitsVec P (verifierCommitment P pk σ.1 σ.2), msg) = σ.2)

/-! ### Correctness -/

variable {P}

/-- The verifier's commitment for an honest response:
`A (y + c s₁) - c (A s₁ + s₂) = A y - c s₂`. -/
theorem verifierCommitment_publicKey (sk : SecretKey P) (y : Fin P.ℓ → Fin P.n → ZMod P.q)
    (c : Fin P.n → ZMod P.q) :
    verifierCommitment P sk.publicKey (y + fun j => negacyclicMul c (sk.s₁ j)) c =
      moduleSISMap sk.A y - fun i => negacyclicMul c (sk.s₂ i) := by
  funext i
  simp only [verifierCommitment, SecretKey.publicKey, moduleSISMap, Pi.sub_apply, Pi.add_apply,
    negacyclicMul_add, Finset.sum_add_distrib, negacyclicMul_sum]
  have h : ∀ j, negacyclicMul (sk.A i j) (negacyclicMul c (sk.s₁ j)) =
      negacyclicMul c (negacyclicMul (sk.A i j) (sk.s₁ j)) := fun j => by
    rw [← negacyclicMul_assoc, negacyclicMul_comm (sk.A i j) c, negacyclicMul_assoc]
  simp only [h]
  abel

/-- **Correctness of one attempt.** If `‖s₂‖_∞ ≤ η` and the hash takes values in `B_τ`, every
signature output by `signAttempt` verifies under the matching public key. -/
theorem verify_signAttempt (hP : P.Valid) {H : Hash P} (hH : ∀ x, InBall P.τ (H x))
    {sk : SecretKey P} (hs₂ : ∀ i j, |(sk.s₂ i j).valMinAbs| ≤ P.η) {msg : List Bool}
    {y : Fin P.ℓ → Fin P.n → ZMod P.q} {σ : Signature P}
    (h : signAttempt P H sk msg y = some σ) : verify P H sk.publicKey msg σ = true := by
  have : NeZero P.q := ⟨by have := hP.one_lt_q; omega⟩
  simp only [signAttempt] at h
  split_ifs at h with hacc
  cases h
  obtain ⟨hz, hlow⟩ := hacc
  set w := moduleSISMap sk.A y
  set c := H (highBitsVec P w, msg)
  simp only [verify, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨hz, hH _⟩, ?_⟩
  rw [verifierCommitment_publicKey]
  -- `HighBits(w - c s₂) = HighBits(w)`, since `c s₂` is `β`-short.
  have hq : 2 * (P.τ * P.η) < P.q := by
    have := hP.τ_mul_η_le_β; have := hP.two_mul_β_lt_q; omega
  have hhigh : highBitsVec P (w - fun i => negacyclicMul c (sk.s₂ i)) = highBitsVec P w := by
    funext i j
    have hs : |(negacyclicMul c (sk.s₂ i) j).valMinAbs| ≤ P.β := by
      have := abs_valMinAbs_negacyclicMul_le (hH (highBitsVec P w, msg)) (hs₂ i) hq j
      have hτη : ((P.τ * P.η : ℕ) : ℤ) ≤ P.β := by exact_mod_cast hP.τ_mul_η_le_β
      push_cast at hτη
      linarith
    have := highBits_add_of_abs_lowBits_lt hP.γ₂_pos hP.two_mul_γ₂_dvd hP.one_lt_q hs (hlow i j)
    simp only [Pi.sub_apply, sub_add_cancel] at this
    exact this.symm
  rw [hhigh]

/-- **Correctness of signing.** Under the hypotheses of `verify_signAttempt`, every signature that
`sign` can output verifies, whatever the mask sampler and the retry bound. -/
theorem verify_sign (hP : P.Valid) {H : Hash P} (hH : ∀ x, InBall P.τ (H x))
    {sk : SecretKey P} (hs₂ : ∀ i j, |(sk.s₂ i j).valMinAbs| ≤ P.η)
    (mask : ProbComp (Fin P.ℓ → Fin P.n → ZMod P.q)) (msg : List Bool) (K : ℕ)
    {σ : Signature P} (h : some σ ∈ (ProbComp.eval (sign P H sk mask msg K)).support) :
    verify P H sk.publicKey msg σ = true := by
  induction K with
  | zero => simp [sign] at h
  | succ K ih =>
    simp only [sign, ProbComp.eval_bind, PMF.support_bind, Set.mem_iUnion] at h
    obtain ⟨y, _, hy⟩ := h
    cases hatt : signAttempt P H sk msg y with
    | none =>
      rw [hatt] at hy
      exact ih hy
    | some σ' =>
      rw [hatt] at hy
      simp only [ProbComp.eval_pure, PMF.support_pure, Set.mem_singleton_iff,
        Option.some.injEq] at hy
      subst hy
      exact verify_signAttempt hP hH hs₂ hatt

end Cslib.Crypto.MLDSA
