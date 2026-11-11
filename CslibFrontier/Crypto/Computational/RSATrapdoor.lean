/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.PowMod
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
public import CslibFrontier.Computability.Probabilistic.Parameter
public import CslibFrontier.Crypto.Game
import CslibFrontier.Crypto.Negligible.Basic
import CslibFrontier.Probability.PMF
import CslibFrontier.Tactic.PPT
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic

/-!
# The RSA trapdoor permutation

The RSA trapdoor permutation family over products `N = p * q` of distinct primes:
key parameters (`RSADesc` and `RSAPublicKey`), modular exponentiation evaluation `rsaEval` and
trapdoor inversion `rsaInvert`, correctness of inversion on all `x < N`, bijectivity on
`Fin N` and `(ZMod N)ˣ`, polynomial-time computability of both evaluation and trapdoor inversion,
and the computational RSA inversion game and assumption.

## Main definitions

* `Cslib.Crypto.RSAPublicKey`, `Cslib.Crypto.RSADesc`: public `(N, e)` and full trapdoor
  `(p, q, e, d)` RSA parameters.
* `Cslib.Crypto.rsaEval`, `Cslib.Crypto.rsaInvert`: RSA evaluation `x ^ e % N` and trapdoor
  inversion `y ^ d % N`.
* `Cslib.Crypto.rsaInversionGame`, `Cslib.Crypto.RSAOneWay`: the RSA inversion experiment and
  one-wayness assumption.

## Main results

* `Cslib.Crypto.rsaInvert_rsaEval`, `Cslib.Crypto.rsaEval_rsaInvert`: `rsaInvert N d` and
  `rsaEval N e` are mutual inverses on `{x // x < N}`.
* `Cslib.Crypto.rsaEval_bijective_fin`, `Cslib.Crypto.rsaEval_bijective_units`: RSA evaluation is
  bijective on `Fin N` and `(ZMod N)ˣ`.
* `Cslib.Crypto.computableInPolyTime_rsaEval`, `Cslib.Crypto.computableInPolyTime_rsaInvert`:
  both evaluation and trapdoor inversion are computable in polynomial time.

## Implementation notes

The evaluation and trapdoor-inversion functions `rsaEval` and `rsaInvert` are defined on
arbitrary natural numbers and proved mutually inverse on all residues `x < N`
(`rsaInvert_rsaEval`, `rsaEval_rsaInvert`), inducing bijections both on `Fin N`
(`rsaEval_bijective_fin`, including nonunits) and on the multiplicative unit group `(ZMod N)ˣ`
(`rsaEval_bijective_units`). The inversion experiment `rsaInversionGame` samples `x` uniformly
from `Fin desc.modulus` (differing from Katz–Lindell Definition 9.46, which samples uniformly
from `(ZMod N)ˣ`; for valid RSA moduli `N = p * q`, the nonunit fraction in `Fin N` is at most
`(p + q) / N`) under an arbitrary generator family `RSAGen := ℕ → PMF RSADesc` (efficient key
generation and bit-length bounds in `n` are not bundled), and `RSAOneWay` quantifies over
uniform native strict-PPT inverters (`IsPPTOn`) receiving `(1^n, ((N, e), y))` with binary
`encNat` encodings.

## References

* [J. Katz, Y. Lindell, *Introduction to Modern Cryptography*][KatzLindell2020],
  Section 9.2.4, Definition 9.46 (The RSA Assumption) and Section 15.1.1, Definition 15.1
  (Trapdoor Permutations; RSA example on p. 526).
-/

@[expose] public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM

/-- Public RSA parameters `(N, e)` with `0 < N`. -/
abbrev RSAPublicKey := { pk : ℕ × ℕ // 0 < pk.1 }

namespace RSAPublicKey

/-- The RSA modulus `N = p * q`. -/
abbrev N (pk : RSAPublicKey) : ℕ := pk.1.1

/-- The public exponent `e`. -/
abbrev e (pk : RSAPublicKey) : ℕ := pk.1.2

/-- Positivity of the modulus. -/
theorem hN (pk : RSAPublicKey) : 0 < pk.N := pk.2

end RSAPublicKey

/-- Encoding of `RSAPublicKey` as a binary word. -/
def encRSAPublicKey : RSAPublicKey ↪ List Bool where
  toFun pk := encPair encNat encNat pk.1
  inj' := (encPair encNat encNat).injective.comp Subtype.val_injective

/-- Validity predicate for full RSA parameters `((p, q), (e, d))`. -/
def RSADescValid (raw : (ℕ × ℕ) × (ℕ × ℕ)) : Prop :=
  let p := raw.1.1
  let q := raw.1.2
  let e := raw.2.1
  let d := raw.2.2
  p.Prime ∧ q.Prime ∧ p ≠ q ∧
    Nat.Coprime e ((p - 1) * (q - 1)) ∧
    e * d ≡ 1 [MOD (p - 1) * (q - 1)]

/-- Full RSA parameters including the prime factors `p, q` and private exponent `d`. -/
abbrev RSADesc := { raw : (ℕ × ℕ) × (ℕ × ℕ) // RSADescValid raw }

namespace RSADesc

/-- First prime factor. -/
abbrev p (desc : RSADesc) : ℕ := desc.1.1.1

/-- Second prime factor. -/
abbrev q (desc : RSADesc) : ℕ := desc.1.1.2

/-- Public exponent. -/
abbrev e (desc : RSADesc) : ℕ := desc.1.2.1

/-- Private trapdoor exponent. -/
abbrev d (desc : RSADesc) : ℕ := desc.1.2.2

/-- Primality of `p`. -/
theorem hp (desc : RSADesc) : desc.p.Prime := desc.2.1

/-- Primality of `q`. -/
theorem hq (desc : RSADesc) : desc.q.Prime := desc.2.2.1

/-- Distinctness of `p` and `q`. -/
theorem hpq (desc : RSADesc) : desc.p ≠ desc.q := desc.2.2.2.1

/-- `e` is coprime to `φ(N) = (p - 1) * (q - 1)`. -/
theorem he (desc : RSADesc) : Nat.Coprime desc.e ((desc.p - 1) * (desc.q - 1)) :=
  desc.2.2.2.2.1

/-- `e * d ≡ 1 [MOD φ(N)]`. -/
theorem hed (desc : RSADesc) : desc.e * desc.d ≡ 1 [MOD (desc.p - 1) * (desc.q - 1)] :=
  desc.2.2.2.2.2

/-- The RSA modulus `N = p * q`. -/
abbrev modulus (desc : RSADesc) : ℕ := desc.p * desc.q

/-- Euler's totient `φ(N) = (p - 1) * (q - 1)`. -/
abbrev totient (desc : RSADesc) : ℕ := (desc.p - 1) * (desc.q - 1)

/-- The RSA modulus is positive. -/
theorem modulus_pos (desc : RSADesc) : 0 < desc.modulus :=
  Nat.mul_pos desc.hp.pos desc.hq.pos

/-- The RSA modulus is strictly greater than `1`. -/
theorem modulus_gt_one (desc : RSADesc) : 1 < desc.modulus := by
  have hp2 : 2 ≤ desc.p := desc.hp.two_le
  have hq2 : 2 ≤ desc.q := desc.hq.two_le
  nlinarith

/-- The totient `(p - 1) * (q - 1)` is strictly greater than `1`. -/
theorem totient_gt_one (desc : RSADesc) : 1 < desc.totient := by
  have hp2 : 2 ≤ desc.p := desc.hp.two_le
  have hq2 : 2 ≤ desc.q := desc.hq.two_le
  have hpq := desc.hpq
  set a := desc.p - 1
  set b := desc.q - 1
  change 1 < a * b
  by_cases hp : desc.p = 2
  · have ha : a = 1 := by omega
    have hb : 1 < b := by omega
    rw [ha, one_mul]
    exact hb
  · have ha : 1 < a := by omega
    have hb : 0 < b := by omega
    nlinarith

/-- Extract the public key `(N, e)`. -/
def publicKey (desc : RSADesc) : RSAPublicKey :=
  ⟨(desc.modulus, desc.e), desc.modulus_pos⟩

/-- Extract the trapdoor key `(N, d)`. -/
def trapdoorKey (desc : RSADesc) : RSAPublicKey :=
  ⟨(desc.modulus, desc.d), desc.modulus_pos⟩

end RSADesc

/-- Encoding of `RSADesc` as a binary word. -/
def encRSADesc : RSADesc ↪ List Bool where
  toFun desc := encPair (encPair encNat encNat) (encPair encNat encNat) desc.1
  inj' := (encPair (encPair encNat encNat) (encPair encNat encNat)).injective.comp
    Subtype.val_injective

/-- RSA evaluation: `x ^ e % N`. -/
def rsaEval (N e x : ℕ) : ℕ := x ^ e % N

/-- RSA trapdoor inversion: `y ^ d % N`. -/
def rsaInvert (N d y : ℕ) : ℕ := y ^ d % N

private theorem pow_mod_prime_of_modEq {p k x : ℕ} (hp : p.Prime)
    (hk : k ≡ 1 [MOD p - 1]) (hkpos : 0 < k) :
    x ^ k ≡ x [MOD p] := by
  by_cases hdiv : p ∣ x
  · rw [Nat.ModEq, Nat.mod_eq_zero_of_dvd (dvd_pow hdiv (Nat.ne_of_gt hkpos)),
      Nat.mod_eq_zero_of_dvd hdiv]
  · have : Fact p.Prime := ⟨hp⟩
    rw [← ZMod.natCast_eq_natCast_iff, Nat.cast_pow]
    have hx0 : (x : ZMod p) ≠ 0 := by
      intro h0
      exact hdiv ((ZMod.natCast_eq_zero_iff x p).mp h0)
    have hdiv_k : p - 1 ∣ k - 1 := (Nat.modEq_iff_dvd' hkpos).mp hk.symm
    rcases hdiv_k with ⟨m, hm⟩
    have hkeq : k = 1 + (p - 1) * m := by omega
    rw [hkeq, pow_add, pow_one, pow_mul, ZMod.pow_card_sub_one_eq_one hx0, one_pow, mul_one]

/-- Core modular identity: `x ^ (e * d) ≡ x [MOD p * q]` for all `x : ℕ`. -/
theorem rsa_pow_mul_modEq (desc : RSADesc) (x : ℕ) :
    x ^ (desc.e * desc.d) ≡ x [MOD desc.modulus] := by
  have hcop : Nat.Coprime desc.p desc.q :=
    (Nat.coprime_primes desc.hp desc.hq).mpr desc.hpq
  rw [← Nat.modEq_and_modEq_iff_modEq_mul hcop]
  have htot1 : 1 < desc.totient := desc.totient_gt_one
  have hed_pos : 0 < desc.e * desc.d := by
    have hmod : (desc.e * desc.d) % desc.totient = 1 := by
      have h : desc.e * desc.d ≡ 1 [MOD desc.totient] := desc.hed
      rw [Nat.ModEq, Nat.mod_eq_of_lt htot1] at h
      exact h
    have hle : (desc.e * desc.d) % desc.totient ≤ desc.e * desc.d := Nat.mod_le _ _
    omega
  have hed_p : desc.e * desc.d ≡ 1 [MOD desc.p - 1] :=
    desc.hed.of_dvd (dvd_mul_right (desc.p - 1) (desc.q - 1))
  have hed_q : desc.e * desc.d ≡ 1 [MOD desc.q - 1] :=
    desc.hed.of_dvd (dvd_mul_left (desc.q - 1) (desc.p - 1))
  exact ⟨pow_mod_prime_of_modEq desc.hp hed_p hed_pos,
    pow_mod_prime_of_modEq desc.hq hed_q hed_pos⟩

/-- Trapdoor inversion recovers any `x < N` from `rsaEval N e x`. -/
theorem rsaInvert_rsaEval (desc : RSADesc) {x : ℕ} (hx : x < desc.modulus) :
    rsaInvert desc.modulus desc.d (rsaEval desc.modulus desc.e x) = x := by
  unfold rsaInvert rsaEval
  rw [← Nat.pow_mod, ← pow_mul]
  have hmod := rsa_pow_mul_modEq desc x
  rw [Nat.ModEq, Nat.mod_eq_of_lt hx] at hmod
  exact hmod

/-- RSA evaluation recovers any `y < N` from `rsaInvert N d y`. -/
theorem rsaEval_rsaInvert (desc : RSADesc) {y : ℕ} (hy : y < desc.modulus) :
    rsaEval desc.modulus desc.e (rsaInvert desc.modulus desc.d y) = y := by
  unfold rsaEval rsaInvert
  rw [← Nat.pow_mod, ← pow_mul, mul_comm]
  have hmod := rsa_pow_mul_modEq desc y
  rw [Nat.ModEq, Nat.mod_eq_of_lt hy] at hmod
  exact hmod

/-- RSA evaluation is a bijection on `Fin N`. -/
theorem rsaEval_bijective_fin (desc : RSADesc) :
    Function.Bijective (fun x : Fin desc.modulus =>
      (⟨rsaEval desc.modulus desc.e x.1, Nat.mod_lt _ desc.modulus_pos⟩ : Fin desc.modulus)) := by
  refine Function.bijective_iff_has_inverse.mpr ⟨fun y =>
    ⟨rsaInvert desc.modulus desc.d y.1, Nat.mod_lt _ desc.modulus_pos⟩, ?_, ?_⟩
  · intro x
    ext
    exact rsaInvert_rsaEval desc x.2
  · intro y
    ext
    exact rsaEval_rsaInvert desc y.2

/-- RSA evaluation `x ↦ x ^ e` is a bijection on `(ZMod N)ˣ`. -/
theorem rsaEval_bijective_units (desc : RSADesc) :
    Function.Bijective (fun x : (ZMod desc.modulus)ˣ => x ^ desc.e) := by
  have : NeZero desc.modulus := ⟨Nat.ne_of_gt desc.modulus_pos⟩
  refine Function.bijective_iff_has_inverse.mpr ⟨fun y => y ^ desc.d, ?_, ?_⟩
  · intro x
    ext
    simp only [Units.val_pow_eq_pow_val, ← pow_mul]
    have hmod := rsa_pow_mul_modEq desc (x : ZMod desc.modulus).val
    rw [← ZMod.natCast_eq_natCast_iff, Nat.cast_pow, ZMod.natCast_zmod_val] at hmod
    exact hmod
  · intro y
    ext
    simp only [Units.val_pow_eq_pow_val, ← pow_mul, mul_comm desc.d desc.e]
    have hmod := rsa_pow_mul_modEq desc (y : ZMod desc.modulus).val
    rw [← ZMod.natCast_eq_natCast_iff, Nat.cast_pow, ZMod.natCast_zmod_val] at hmod
    exact hmod

/-- RSA evaluation `x ↦ x ^ e % N` is computable in polynomial time whenever `N`, `e`, and `x` are
computable in polynomial time and `0 < N a`. -/
theorem computableInPolyTime_rsaEval {α : Type} {enc : α ↪ List Bool} {N e x : α → ℕ}
    (hN : ComputableInPolyTime N enc encNat) (he : ComputableInPolyTime e enc encNat)
    (hx : ComputableInPolyTime x enc encNat) (hpos : ∀ a, 0 < N a) :
    ComputableInPolyTime (fun a => rsaEval (N a) (e a) (x a)) enc encNat :=
  ComputableInPolyTime.binary_powMod hx he hN hpos

/-- RSA trapdoor inversion `y ↦ y ^ d % N` is computable in polynomial time whenever `N`, `d`, and
`y` are computable in polynomial time and `0 < N a`. -/
theorem computableInPolyTime_rsaInvert {α : Type} {enc : α ↪ List Bool} {N d y : α → ℕ}
    (hN : ComputableInPolyTime N enc encNat) (hd : ComputableInPolyTime d enc encNat)
    (hy : ComputableInPolyTime y enc encNat) (hpos : ∀ a, 0 < N a) :
    ComputableInPolyTime (fun a => rsaInvert (N a) (d a) (y a)) enc encNat :=
  ComputableInPolyTime.binary_powMod hy hd hN hpos

/-- An RSA parameter generator indexed by the security parameter `n`. -/
abbrev RSAGen := ℕ → PMF RSADesc

/-- The RSA inversion experiment: sample `desc ← gen n` and a uniform challenge `x ← Fin N`,
compute `y = x ^ e % N`, and test whether the inverter recovers `x` from `(pk, y)`. -/
noncomputable def rsaInversionGame (gen : RSAGen) (A : ℕ → RSAPublicKey × ℕ → ProbComp ℕ)
    (n : ℕ) : Game := do
  let desc ← gen n
  have : NeZero desc.modulus := ⟨Nat.ne_of_gt desc.modulus_pos⟩
  let x ← PMF.uniformOfFintype (Fin desc.modulus)
  let y := rsaEval desc.modulus desc.e x.1
  let x' ← ProbComp.eval (A n (desc.publicKey, y))
  return decide (x' = x.1)

/-- The RSA assumption for `gen`: every uniform PPT inverter has negligible probability of
inverting `x ↦ x ^ e % N` on a uniform `x < N`. -/
def RSAOneWay (gen : RSAGen) : Prop :=
  ∀ A : ℕ → RSAPublicKey × ℕ → ProbComp ℕ,
    IsPPTOn (encPair encUnary (encPair encRSAPublicKey encNat)) encNat
      (fun input => A input.1 input.2) →
    Negligible (fun n => Game.succProbability (rsaInversionGame gen A n))

end Cslib.Crypto
