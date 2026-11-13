/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.PowMod
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
public import CslibFrontier.Computability.Probabilistic.Parameter
public import CslibFrontier.Crypto.Game
public import CslibFrontier.Crypto.Game.Inversion
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Captured
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Decoder.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat.WordsRoundTrip
import CslibFrontier.Computability.Probabilistic.PPT.Capture
import CslibFrontier.Computability.Probabilistic.PPT.Extension
import CslibFrontier.Crypto.Negligible.Basic
import CslibFrontier.Probability.PMF
import CslibFrontier.Probability.PMF.Bind
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
  inversion `y ^ d % N`; `Cslib.Crypto.RSAPublicKey.eval` is evaluation on residues `Fin N`.
* `Cslib.Crypto.RSAInput`, `Cslib.Crypto.encRSAInput`: the input of an RSA inverter and its
  encoding.
* `Cslib.Crypto.RSAInverter`, `Cslib.Crypto.RSAInverter.IsPPT`,
  `Cslib.Crypto.rsaInversionGame`, `Cslib.Crypto.RSAOneWay`: the RSA inversion experiment and
  one-wayness assumption.

## Main results

* `Cslib.Crypto.rsaInvert_rsaEval`, `Cslib.Crypto.rsaEval_rsaInvert`: `rsaInvert N d` and
  `rsaEval N e` are mutual inverses on `{x // x < N}`.
* `Cslib.Crypto.rsaEval_bijective_fin`, `Cslib.Crypto.rsaEval_bijective_units`: RSA evaluation is
  bijective on `Fin N` and `(ZMod N)ˣ`.
* `Cslib.Crypto.computableInPolyTime_rsaEval`, `Cslib.Crypto.computableInPolyTime_rsaInvert`:
  both evaluation and trapdoor inversion are computable in polynomial time.
* `Cslib.Crypto.rsaOneWay_iff_encoded`: `RSAOneWay` is the word-level RSA assumption.

## Implementation notes

The evaluation and trapdoor-inversion functions `rsaEval` and `rsaInvert` are defined on
arbitrary natural numbers and proved mutually inverse on all residues `x < N`
(`rsaInvert_rsaEval`, `rsaEval_rsaInvert`), inducing bijections both on `Fin N`
(`rsaEval_bijective_fin`, including nonunits) and on the multiplicative unit group `(ZMod N)ˣ`
(`rsaEval_bijective_units`). The inversion experiment `rsaInversionGame` runs
`Cslib.Crypto.inversionExperiment` on `x` drawn uniformly from `Fin N` (differing from
Katz–Lindell Definition 9.46, which samples uniformly from `(ZMod N)ˣ`; for valid RSA moduli
`N = p * q`, the nonunit fraction in `Fin N` is at most `(p + q) / N`) under an arbitrary
generator family `RSAGen := ℕ → PMF RSADesc` (efficient key generation and bit-length bounds in
`n` are not bundled).

An `RSAInverter` receives the public key and a challenge residue `y : Fin N` and returns a
residue. `RSAInverter.IsPPT` asks for one uniform strict PPT machine that reads `encRSAInput`, the
unary security parameter followed by `N`, `e` and `y` in binary, and writes the returned residue
in binary. Since RSA evaluation is a bijection on `Fin N`, accepting any preimage is the same as
recovering the challenge (`rsaInversionGame_eq`). `rsaOneWay_iff_encoded` shows that `RSAOneWay`
is the assumption over word-level inverters that read the same layout on keys with `0 < N` and may
output any natural number: a word-level answer is reduced modulo `N`, and a typed inverter extends
to all words (`IsPPTOn.exists_extension`).

## References

* [J. Katz, Y. Lindell, *Introduction to Modern Cryptography*][KatzLindell2020],
  Section 9.2.4, Definition 9.46 (The RSA Assumption) and Section 15.1.1, Definition 15.1
  (Trapdoor Permutations; RSA example on p. 526).
-/

@[expose] public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM

/-- RSA evaluation: `x ^ e % N`. -/
def rsaEval (N e x : ℕ) : ℕ := x ^ e % N

/-- RSA trapdoor inversion: `y ^ d % N`. -/
def rsaInvert (N d y : ℕ) : ℕ := y ^ d % N

/-- Public RSA parameters: the modulus `N` and the public exponent `e`. -/
structure RSAPublicKey where
  /-- The RSA modulus `N = p * q`. -/
  N : ℕ
  /-- The public exponent `e`. -/
  e : ℕ

/-- The encoding of an RSA public key: `N` and `e` in binary, `N` framed
(`encRSAPublicKey_apply`). -/
enc_structure encRSAPublicKey : RSAPublicKey where
  N : encNat, e : encNat

namespace RSAPublicKey

/-- RSA evaluation `x ↦ x ^ e % N` on residues modulo `N`. -/
def eval (pk : RSAPublicKey) (x : Fin pk.N) : Fin pk.N :=
  ⟨rsaEval pk.N pk.e x, Nat.mod_lt _ x.pos⟩

@[simp] theorem val_eval (pk : RSAPublicKey) (x : Fin pk.N) :
    (pk.eval x : ℕ) = rsaEval pk.N pk.e x :=
  rfl

/-- The encoding of a residue modulo `N` by its value in binary. -/
def encResidue (pk : RSAPublicKey) : Fin pk.N ↪ List Bool :=
  Fin.valEmbedding.trans encNat

@[simp] theorem encResidue_apply (pk : RSAPublicKey) (x : Fin pk.N) :
    pk.encResidue x = encNat x :=
  rfl

end RSAPublicKey

/-- Full RSA parameters: distinct primes `p` and `q`, a public exponent `e` coprime to
`(p - 1) * (q - 1)`, and a private exponent `d` inverting `e` modulo `(p - 1) * (q - 1)`. -/
structure RSADesc where
  /-- First prime factor. -/
  p : ℕ
  /-- Second prime factor. -/
  q : ℕ
  /-- Public exponent. -/
  e : ℕ
  /-- Private trapdoor exponent. -/
  d : ℕ
  /-- Primality of `p`. -/
  hp : p.Prime
  /-- Primality of `q`. -/
  hq : q.Prime
  /-- Distinctness of `p` and `q`. -/
  hpq : p ≠ q
  /-- `e` is coprime to `φ(N) = (p - 1) * (q - 1)`. -/
  he : Nat.Coprime e ((p - 1) * (q - 1))
  /-- `e * d ≡ 1 [MOD φ(N)]`. -/
  hed : e * d ≡ 1 [MOD (p - 1) * (q - 1)]

namespace RSADesc

/-- The RSA modulus `N = p * q`. -/
abbrev modulus (desc : RSADesc) : ℕ := desc.p * desc.q

/-- Euler's totient `φ(N) = (p - 1) * (q - 1)`. -/
abbrev totient (desc : RSADesc) : ℕ := (desc.p - 1) * (desc.q - 1)

/-- The RSA modulus is positive. -/
theorem modulus_pos (desc : RSADesc) : 0 < desc.modulus :=
  Nat.mul_pos desc.hp.pos desc.hq.pos

instance (desc : RSADesc) : NeZero desc.modulus :=
  ⟨desc.modulus_pos.ne'⟩

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

/-- The public key `(N, e)`. -/
abbrev publicKey (desc : RSADesc) : RSAPublicKey :=
  ⟨desc.modulus, desc.e⟩

end RSADesc

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
theorem rsaEval_bijective_fin (desc : RSADesc) : Function.Bijective desc.publicKey.eval := by
  refine Function.bijective_iff_has_inverse.mpr ⟨fun y =>
    ⟨rsaInvert desc.modulus desc.d y, Nat.mod_lt _ desc.modulus_pos⟩, ?_, ?_⟩
  · intro x
    ext
    exact rsaInvert_rsaEval desc x.2
  · intro y
    ext
    exact rsaEval_rsaInvert desc y.2

/-- RSA evaluation `x ↦ x ^ e` is a bijection on `(ZMod N)ˣ`. -/
theorem rsaEval_bijective_units (desc : RSADesc) :
    Function.Bijective (fun x : (ZMod desc.modulus)ˣ => x ^ desc.e) := by
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

/-! ### The RSA assumption -/

/-- An RSA parameter generator indexed by the security parameter `n`. -/
abbrev RSAGen := ℕ → PMF RSADesc

/-- The input of an RSA inverter: the security parameter, a public key `(N, e)` and a challenge
residue modulo `N`, which is `x ^ e % N` in the experiment. -/
structure RSAInput where
  /-- The security parameter, given to machines in unary. -/
  secParam : ℕ
  /-- The public key `(N, e)`. -/
  publicKey : RSAPublicKey
  /-- The challenge residue modulo `N`. -/
  challenge : Fin publicKey.N

/-- The encoding of an RSA inverter's input: the unary security parameter, the public key and the
challenge in binary, each framed except the last (`encRSAInput_apply`). -/
enc_structure encRSAInput : RSAInput where
  secParam : encUnary, publicKey : encRSAPublicKey,
  challenge : publicKey.encResidue using publicKey.encResidue.injective

/-- The challenge of a computed RSA input, as a binary natural number. -/
@[fun_prop] theorem RSAInput.computableInPolyTime_challenge_val {α : Type}
    {enc : α ↪ List Bool} {g : α → RSAInput} (h : ComputableInPolyTime g enc encRSAInput) :
    ComputableInPolyTime (fun a => ((g a).challenge : ℕ)) enc encNat :=
  (encRSAInput_challenge_polyTime h).of_enc_eq fun _ => rfl

/-- An RSA inverter: given the security parameter, a public key `(N, e)` and a residue modulo `N`,
it outputs a residue modulo `N`. `RSAInverter.IsPPT` states its efficiency on encodings. -/
abbrev RSAInverter : Type :=
  ℕ → (pk : RSAPublicKey) → Fin pk.N → ProbComp (Fin pk.N)

/-- An RSA inverter is PPT when one uniform strict PPT machine reads `encRSAInput` and writes the
returned residue in binary. -/
def RSAInverter.IsPPT (inverter : RSAInverter) : Prop :=
  IsPPTOn encRSAInput encNat fun x =>
    Fin.val <$> inverter x.secParam x.publicKey x.challenge

/-- The RSA inversion experiment: sample `desc ← gen n` and run
`Cslib.Crypto.inversionExperiment` for RSA evaluation on a uniform residue `x` modulo `N`. The
inverter receives `(pk, x ^ e % N)` and wins when it returns a preimage. -/
noncomputable def rsaInversionGame (gen : RSAGen) (inverter : RSAInverter) (n : ℕ) : Game := do
  let desc ← gen n
  ProbComp.eval (inversionExperiment (ProbComp.uniform (Fin desc.modulus)) desc.publicKey.eval
    (inverter n desc.publicKey))

/-- RSA evaluation is a bijection on `Fin N`, so an inverter wins `rsaInversionGame` exactly when
it recovers the challenge. -/
theorem rsaInversionGame_eq (gen : RSAGen) (inverter : RSAInverter) (n : ℕ) :
    rsaInversionGame gen inverter n = (do
      let desc ← gen n
      let x ← PMF.uniformOfFintype (Fin desc.modulus)
      let x' ← ProbComp.eval (inverter n desc.publicKey (desc.publicKey.eval x))
      return decide (x' = x)) := by
  unfold rsaInversionGame
  congr 1
  funext desc
  rw [inversionExperiment_eq_of_injective _ (rsaEval_bijective_fin desc).injective]
  simp only [ProbComp.eval_bind, ProbComp.eval_uniform, ProbComp.eval_pure]
  rfl

/-- The RSA assumption for `gen`: every PPT inverter recovers a uniform residue from its RSA
image with negligible probability. -/
def RSAOneWay (gen : RSAGen) : Prop :=
  ∀ inverter : RSAInverter, inverter.IsPPT →
    Negligible fun n => Game.succProbability (rsaInversionGame gen inverter n)

/-- **`RSAOneWay` is the word-level RSA assumption.** Quantifying over inverters that read
`(1ⁿ, (N, e), y)` with binary numbers on keys with `0 < N`, each with one uniform strict PPT
machine, and may answer with any natural number gives the same assumption as quantifying over typed
inverters. A word-level answer is reduced modulo `N`, which can only help; conversely, a typed
inverter extends to all words by rerunning its machine and decoding its output
(`IsPPTOn.exists_extension`). -/
theorem rsaOneWay_iff_encoded (gen : RSAGen) :
    RSAOneWay gen ↔ ∀ W : ℕ → {pk : RSAPublicKey // 0 < pk.N} × ℕ → ProbComp ℕ,
      IsPPTOn (encPair encUnary (encPair
          ((Function.Embedding.subtype fun pk : RSAPublicKey => 0 < pk.N).trans encRSAPublicKey)
          encNat)) encNat (fun x => W x.1 x.2) →
      Negligible fun n => Game.succProbability (do
        let desc ← gen n
        let x ← PMF.uniformOfFintype (Fin desc.modulus)
        let x' ← ProbComp.eval
          (W n (⟨desc.publicKey, desc.modulus_pos⟩, rsaEval desc.modulus desc.e x))
        return decide (x' = x)) := by
  constructor
  · intro h W hW
    let A : RSAInverter := fun n pk y =>
      (fun z => (⟨z % pk.N, Nat.mod_lt _ y.pos⟩ : Fin pk.N)) <$> W n (⟨pk, y.pos⟩, y)
    have hA : A.IsPPT := by
      refine ((hW.preprocess (prepare := fun x : RSAInput =>
          (x.secParam, ⟨x.publicKey, x.challenge.pos⟩, (x.challenge : ℕ)))
          (.of_eq fun _ => rfl)).map_with
        (f := fun x z => z % x.publicKey.N)
        (ComputableInPolyTime.binary_mod' (by fun_prop) (by fun_prop))).congr fun x => ?_
      simp only [A, Functor.map_map]
    refine negligible_of_le (h A hA) fun n => ?_
    rw [rsaInversionGame_eq]
    refine ENNReal.toNNReal_mono (PMF.apply_ne_top _ _) ?_
    refine PMF.bind_apply_mono_on_support _ _ fun desc _ => ?_
    refine PMF.bind_apply_mono_on_support _ _ fun x _ => ?_
    simp only [A, ProbComp.eval_map, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
      PMF.bind_map, RSAPublicKey.val_eval]
    refine PMF.bind_apply_mono_on_support _ _ fun z _ => ?_
    by_cases hz : z = (x : ℕ)
    · subst hz
      simp [Nat.mod_eq_of_lt x.isLt]
    · simp [hz]
  · intro h A hA
    obtain ⟨E, hEppt, hE⟩ := hA.exists_extension ComputableInPolyTime.bitsToNat ofBits_encNat
    set E' := encPair encUnary (encPair
      ((Function.Embedding.subtype fun pk : RSAPublicKey => 0 < pk.N).trans encRSAPublicKey)
      encNat)
    have hold := h (fun n t => E (E' (n, t)))
      (hEppt.preprocess ComputableInPolyTime.id'.encoding_comp)
    refine negligible_of_le hold fun n => le_of_eq ?_
    rw [rsaInversionGame_eq]
    have hrun (desc : RSADesc) (x : Fin desc.modulus) :
        ProbComp.eval
            (E (E' (n, ⟨desc.publicKey, desc.modulus_pos⟩, rsaEval desc.modulus desc.e x))) =
          (ProbComp.eval (A n desc.publicKey (desc.publicKey.eval x))).map Fin.val := by
      rw [← ProbComp.eval_map]
      exact hE ⟨n, desc.publicKey, desc.publicKey.eval x⟩
    simp only [hrun, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.bind_map,
      Function.comp_def, Fin.val_inj]

end Cslib.Crypto
