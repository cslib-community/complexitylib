/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.DiscreteLog
public import Complexity.Probability.BitString
public import Complexity.Languages.Probabilistic.BitString
public import Cslib.Foundations.Data.BitString
import Complexity.Crypto.Negligible.Basic
import Complexity.Crypto.Protocols.SigmaProtocol.Identification
import Complexity.Foundations.Data.BitString.Counter
import Complexity.Foundations.Data.Nat.Bits
import Complexity.Probability.PMF
import Complexity.Foundations.FieldTheory.Finite.Basic
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.PowMod
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Complexity.Tactic.PPT

/-!
# Schnorr identification under the discrete-logarithm assumption

Schnorr's identification scheme ([BonehShoup2023], Section 19.1) over a `PrimeOrderGroupFamily`:
the key is a description `d`, drawn from a setup law, a uniform secret `α` and the public key
`u = α • g`. An impersonator sees the description and the encoded public key and sends a
commitment word `t`; the verifier draws a uniform challenge word `c` of `k n` bits; the
impersonator answers with a word `z`. Challenges and responses are read as binary numbers modulo
the group order `q`, and the verifier accepts when `t` encodes `z • g - c • u`; on genuine group
elements this is Schnorr's check `z • g = t + c • u`.

Rewinding an impersonator gives a discrete-logarithm adversary, `SchnorrImpersonator.rewind`. It
runs the impersonator to its commitment, answers two independent uniform challenges from the same
state, and computes `(c - c')⁻¹ (z - z')` modulo `q`, inverting by Fermat's little theorem. For each
security parameter, if `2 ^ k ≤ q` for every description the setup can produce,

  `ε ≤ 1 / 2 ^ k + √ε'`,

where `ε` is the impersonator's success probability and `ε'` the discrete-logarithm success
probability of the rewinding adversary (`succProbability_schnorrDirectGame_le`, Theorem 19.1).
The rewinding adversary is uniform strict PPT whenever the impersonator is and `k` is computable
in polynomial time. Under the discrete-logarithm assumption, with negligible `1 / 2 ^ k`, every
uniform strict PPT impersonator therefore succeeds with negligible probability
(`negligible_schnorrDirectGame`).

The impersonator may use fresh randomness in its second stage; its state is a word. Challenges
are bit strings because strict PPT machines sample them exactly; they cannot sample `ZMod q`
exactly, which matters for the honest prover and for simulation but not for this reduction.

## Main definitions

* `Cslib.Crypto.PrimeOrderGroupFamily.SchnorrImpersonator`: a two-stage word adversary.
* `Cslib.Crypto.PrimeOrderGroupFamily.schnorrDirectGame`: the direct impersonation attack.
* `Cslib.Crypto.PrimeOrderGroupFamily.SchnorrImpersonator.rewind`: the rewinding
  discrete-logarithm adversary.

## Main results

* `Cslib.Crypto.PrimeOrderGroupFamily.succProbability_schnorrDirectGame_le`: `ε ≤ 1 / 2 ^ k + √ε'`
  at each security parameter.
* `Cslib.Crypto.PrimeOrderGroupFamily.extractNat_cast`,
  `Cslib.Crypto.PrimeOrderGroupFamily.computableInPolyTime_extractNat`: the extracted witness is
  `(c - c')⁻¹ (z - z')` modulo `q`, and is computable in polynomial time.
* `Cslib.Crypto.PrimeOrderGroupFamily.isPPTOn_rewind`: the rewinding adversary is uniform strict
  PPT.
* `Cslib.Crypto.PrimeOrderGroupFamily.negligible_schnorrDirectGame`: Schnorr identification is
  secure against direct attacks under the discrete-logarithm assumption.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Section 19.1.
* [C.-P. Schnorr, *Efficient Signature Generation by Smart Cards*][Schnorr1991]
-/

@[expose] public section

namespace Cslib.Crypto.PrimeOrderGroupFamily

open Probability Turing.MultiTapeTM Protocols

variable {F : PrimeOrderGroupFamily}

variable (F) in
/-- A uniform impersonator against Schnorr identification. Its first stage sees the security
parameter, the group description and the encoded public key, and returns a commitment word and a
state word; its second stage sees the security parameter, the state and the challenge word. -/
structure SchnorrImpersonator where
  /-- Commit, keeping a state word. -/
  commit : ℕ → F.Desc × List Bool → ProbComp (List Bool × List Bool)
  /-- Respond to a challenge word from the state word. -/
  respond : ℕ → List Bool × List Bool → ProbComp (List Bool)

/-- Both stages of an impersonator are uniform strict PPT in their whole inputs. -/
def SchnorrImpersonator.IsPPT (A : F.SchnorrImpersonator) : Prop :=
  IsPPTOn (encPair encUnary (encPair F.encDesc encBits)) (encPair encBits encBits)
      (fun input => A.commit input.1 input.2) ∧
    IsPPTOn (encPair encUnary (encPair encBits encBits)) encBits
      (fun input => A.respond input.1 input.2)

variable (F) in
/-- The direct impersonation attack on Schnorr identification ([BonehShoup2023], Attack
Game 18.1), with challenges of `k n` bits. The verifier accepts when the commitment encodes
`z • g - c • u`. -/
noncomputable def schnorrDirectGame (setup : ℕ → PMF F.Desc) (k : ℕ → ℕ)
    (A : F.SchnorrImpersonator) (n : ℕ) : Game := do
  let d ← setup n
  let α ← PMF.uniformOfFintype (ZMod (F.order d))
  let ts ← ProbComp.eval (A.commit n (d, F.encode d (α • F.generator d)))
  let c ← BitString.uniformList (k n)
  let z ← ProbComp.eval (A.respond n (ts.2, c))
  return decide (ts.1 = F.encode d ((ofBits z : ZMod (F.order d)) • F.generator d -
    (ofBits c : ZMod (F.order d)) • (α • F.generator d)))

/-- The extracted witness `(c - c')⁻¹ (z - z')` modulo `q`, computed on natural numbers with the
inverse as a `(q - 2)`nd power. -/
def extractNat (q c z c' z' : ℕ) : ℕ :=
  ((c % q + q - c' % q) % q) ^ (q - 2) % q * ((z % q + q - z' % q) % q) % q

/-- The rewinding discrete-logarithm adversary (proof of [BonehShoup2023], Theorem 19.1): run the
impersonator to its commitment, answer two independent uniform `k n`-bit challenges from the same
state, and output the extracted witness in binary. -/
noncomputable def SchnorrImpersonator.rewind (k : ℕ → ℕ) (A : F.SchnorrImpersonator) (n : ℕ)
    (input : F.Desc × List Bool) : ProbComp (List Bool) := do
  let ts ← A.commit n input
  let c ← BitString.sampleList (k n)
  let c' ← BitString.sampleList (k n)
  let z ← A.respond n (ts.2, c)
  let z' ← A.respond n (ts.2, c')
  return (extractNat (F.order input.1) (ofBits c) (ofBits z) (ofBits c') (ofBits z')).bits

/-! ### The exact bound -/

/-- Distinct `k`-bit challenges are distinct modulo `q` when `2 ^ k ≤ q`. -/
private theorem challenge_ne {q k : ℕ} (hkq : 2 ^ k ≤ q) {c c' : BitString k} (hc : c ≠ c') :
    (ofBits (List.ofFn c) : ZMod q) ≠ ofBits (List.ofFn c') := by
  intro h
  rw [ZMod.natCast_eq_natCast_iff', ofBits, ofBits, ← BitString.lsbValue_eq_foldr_bit,
    ← BitString.lsbValue_eq_foldr_bit,
    Nat.mod_eq_of_lt ((BitString.lsbValue_lt _).trans_le (by simpa using hkq)),
    Nat.mod_eq_of_lt ((BitString.lsbValue_lt _).trans_le (by simpa using hkq))] at h
  exact hc (List.ofFn_injective (BitString.lsbValue_injective (by simp) h))

/-- Fermat's little theorem gives the inverse in `extractNat`: modulo a prime `q`, it is
`(c - c')⁻¹ (z - z')` whenever `c` and `c'` are distinct modulo `q`. -/
theorem extractNat_cast {q : ℕ} [Fact q.Prime] {c z c' z' : ℕ}
    (hc : (c : ZMod q) ≠ c') :
    (extractNat q c z c' z' : ZMod q) = ((c : ZMod q) - c')⁻¹ * ((z : ZMod q) - z') := by
  have hsub (a b : ℕ) : (((a % q + q - b % q) % q : ℕ) : ZMod q) = (a : ZMod q) - b := by
    rw [ZMod.natCast_mod, Nat.cast_sub ((Nat.mod_lt _ (Fact.out : q.Prime).pos).le.trans
      (Nat.le_add_left _ _)), Nat.cast_add, ZMod.natCast_mod, ZMod.natCast_mod, ZMod.natCast_self,
      add_zero]
  have hne : (c : ZMod q) - c' ≠ 0 := sub_ne_zero.mpr hc
  have hinv : ((c : ZMod q) - c') ^ (q - 2) = ((c : ZMod q) - c')⁻¹ :=
    ZMod.pow_card_sub_two_eq_inv hne
  simp only [extractNat, Nat.cast_mul, ZMod.natCast_mod, Nat.cast_pow, hsub, hinv]

/-- Schnorr's protocol on encoded commitments and binary responses, with statements carrying their
group description; only its verifier is used. -/
private noncomputable def wordProtocol (F : PrimeOrderGroupFamily) (m : ℕ) :
    SigmaProtocol ℕ ((d : F.Desc) × F.Carrier d) (List Bool) (BitString m) (List Bool) where
  State := Unit
  commit _ _ := PMF.pure ([], ())
  respond _ _ _ _ := []
  verify y t c z := decide (t = F.encode y.1 ((ofBits z : ZMod (F.order y.1)) • F.generator y.1 -
    (ofBits (List.ofFn c) : ZMod (F.order y.1)) • y.2))

/-- Schnorr key generation at a security parameter, with the description in the statement. -/
private noncomputable def wordKeyGen (F : PrimeOrderGroupFamily) (setup : ℕ → PMF F.Desc)
    (n : ℕ) : PMF (ℕ × (d : F.Desc) × F.Carrier d) := do
  let d ← setup n
  let α ← PMF.uniformOfFintype (ZMod (F.order d))
  return (α.val, ⟨d, α • F.generator d⟩)

/-- The relation: `x` is a discrete logarithm of the public key. -/
private def wordRelation (F : PrimeOrderGroupFamily) (x : ℕ) (y : (d : F.Desc) × F.Carrier d) :
    Prop :=
  (x : ZMod (F.order y.1)) • F.generator y.1 = y.2

private noncomputable instance (F : PrimeOrderGroupFamily) :
    DecidableRel (wordRelation F) := fun _ _ => Classical.propDecidable _

/-- The extractor of `wordProtocol`. -/
private def wordExtract (F : PrimeOrderGroupFamily) (m : ℕ) (y : (d : F.Desc) × F.Carrier d)
    (_ : List Bool) (c : BitString m) (z : List Bool) (c' : BitString m) (z' : List Bool) : ℕ :=
  extractNat (F.order y.1) (ofBits (List.ofFn c)) (ofBits z) (ofBits (List.ofFn c')) (ofBits z')

/-- An impersonator as a typed impersonator for `wordProtocol`. -/
private noncomputable def SchnorrImpersonator.typed (A : F.SchnorrImpersonator) (n m : ℕ) :
    SigmaProtocol.Impersonator ((d : F.Desc) × F.Carrier d) (List Bool) (BitString m)
      (List Bool) where
  State := List Bool
  commit y := ProbComp.eval (A.commit n (y.1, F.encode y.1 y.2))
  respond s c := ProbComp.eval (A.respond n (s, List.ofFn c))

private theorem schnorrDirectGame_eq (setup : ℕ → PMF F.Desc) (k : ℕ → ℕ)
    (A : F.SchnorrImpersonator) (n : ℕ) :
    F.schnorrDirectGame setup k A n =
      (wordProtocol F (k n)).directAttack (wordKeyGen F setup n) (A.typed n (k n)) := by
  simp only [schnorrDirectGame, SigmaProtocol.directAttack, wordKeyGen, wordProtocol,
    SchnorrImpersonator.typed, BitString.uniformList, Probability.PMF.monad_bind_eq_bind,
    Probability.PMF.monad_pure_eq_pure, PMF.bind_bind, PMF.pure_bind, PMF.bind_map,
    Function.comp_def]

private theorem specialSoundOn (setup : ℕ → PMF F.Desc) {k : ℕ → ℕ} {n : ℕ}
    (hkq : ∀ d ∈ (setup n).support, 2 ^ k n ≤ F.order d) :
    (wordProtocol F (k n)).SpecialSoundOn (wordKeyGen F setup n) (wordRelation F)
      (wordExtract F (k n)) := by
  rintro ⟨x, d, u⟩ hkey t c z c' z' hc hz hz'
  have hd : d ∈ (setup n).support := by
    simp only [wordKeyGen, Probability.PMF.monad_bind_eq_bind,
      Probability.PMF.monad_pure_eq_pure, PMF.mem_support_bind_iff, PMF.mem_support_pure_iff,
      Prod.mk.injEq, Sigma.mk.injEq] at hkey
    obtain ⟨d', hd', -, -, -, hdd, -⟩ := hkey
    exact hdd ▸ hd'
  simp only [SigmaProtocol.Accepts, wordProtocol, decide_eq_true_eq] at hz hz'
  have heq := F.encode_injective d (hz.symm.trans hz')
  have hcne := challenge_ne (hkq d hd) hc
  simp only [wordRelation, wordExtract, extractNat_cast hcne, mul_smul]
  rw [sub_smul, sub_eq_sub_iff_sub_eq_sub.mp heq, ← sub_smul,
    inv_smul_smul₀ (sub_ne_zero.mpr hcne)]

/-- Reading back the binary digits of a number recovers it. -/
private theorem ofBits_bits (r : ℕ) : ofBits r.bits = r := Nat.foldr_bit_bits r

/-- The rewinding adversary wins the discrete-logarithm game exactly when its output is a witness
for the generated statement. -/
private theorem decide_wordRelation (d : F.Desc) (α : ZMod (F.order d)) (r : ℕ) :
    decide (wordRelation F r ⟨d, α • F.generator d⟩) =
      decide (((ofBits r.bits : ℕ) : ZMod (F.order d)) = α) := by
  rw [ofBits_bits]
  exact decide_eq_decide.mpr ⟨fun h => F.smul_generator_injective d h, fun h => by
    simp only [wordRelation, h]⟩

private theorem oneWayGame_eq (setup : ℕ → PMF F.Desc) (k : ℕ → ℕ) (A : F.SchnorrImpersonator)
    (n : ℕ) :
    SigmaProtocol.oneWayGame (wordKeyGen F setup n) (wordRelation F)
        ((A.typed n (k n)).rewind (wordExtract F (k n))) =
      F.discreteLogGame setup (A.rewind k) n := by
  simp only [SigmaProtocol.oneWayGame, wordKeyGen, discreteLogGame,
    SigmaProtocol.Impersonator.rewind, SchnorrImpersonator.rewind, SchnorrImpersonator.typed,
    ProbComp.eval_bind, ProbComp.eval_pure, BitString.eval_sampleList, BitString.uniformList,
    Probability.PMF.monad_bind_eq_bind, Probability.PMF.monad_pure_eq_pure, PMF.bind_bind,
    PMF.pure_bind, PMF.bind_map, Function.comp_def, wordExtract, decide_wordRelation]

/-- **Schnorr identification against direct attacks, exact form** ([BonehShoup2023],
Theorem 19.1): at each security parameter where every possible group has at least `2 ^ k n`
elements, an impersonator's success probability is at most `1 / 2 ^ k n + √ε'`, where `ε'` is the
discrete-logarithm success probability of the rewinding adversary. -/
theorem succProbability_schnorrDirectGame_le (setup : ℕ → PMF F.Desc) (k : ℕ → ℕ)
    (A : F.SchnorrImpersonator) (n : ℕ) (hkq : ∀ d ∈ (setup n).support, 2 ^ k n ≤ F.order d) :
    (Game.succProbability (F.schnorrDirectGame setup k A n) : ℝ) ≤
      1 / 2 ^ k n + √(Game.succProbability (F.discreteLogGame setup (A.rewind k) n)) := by
  have h := SigmaProtocol.succProbability_directAttack_le (specialSoundOn setup hkq)
    (A.typed n (k n))
  rw [oneWayGame_eq] at h
  rw [schnorrDirectGame_eq]
  simpa only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, Nat.cast_pow,
    Nat.cast_ofNat] using h

/-! ### Efficiency of the rewinding adversary -/

/-- The extracted witness is computable in polynomial time from the group description and the
four binary numbers. -/
private theorem computableTidilyInPolyTime_extractNat {α : Type} {input : α ↪ List Bool}
    {d : α → F.Desc} {c z c' z' : α → ℕ} (hd : ComputableTidilyInPolyTime d input F.encDesc)
    (hc : ComputableTidilyInPolyTime c input encNat)
    (hz : ComputableTidilyInPolyTime z input encNat)
    (hc' : ComputableTidilyInPolyTime c' input encNat)
    (hz' : ComputableTidilyInPolyTime z' input encNat) :
    ComputableTidilyInPolyTime (fun a => extractNat (F.order (d a)) (c a) (z a) (c' a) (z' a))
      input encNat := by
  have hq : ComputableTidilyInPolyTime (fun a => F.order (d a)) input encNat :=
    F.computableInPolyTime_order.tidy.comp hd
  have hdiff {x y : α → ℕ} (hx : ComputableTidilyInPolyTime x input encNat)
      (hy : ComputableTidilyInPolyTime y input encNat) :
      ComputableTidilyInPolyTime
        (fun a => (x a % F.order (d a) + F.order (d a) - y a % F.order (d a)) % F.order (d a))
        input encNat :=
    .binary_mod' (.binary_sub' (.binary_add' (.binary_mod' hx hq) hq) (.binary_mod' hy hq)) hq
  have hpow := (ComputableInPolyTime.binary_powMod (ComputableInPolyTime.of_tidy (hdiff hc hc'))
    (ComputableInPolyTime.of_tidy (.binary_sub' hq (.const 2)))
    (ComputableInPolyTime.of_tidy hq) fun a => (F.prime_order (d a)).pos).tidy
  exact .binary_mod' (.binary_mul' hpow (hdiff hz hz')) hq

attribute [local fun_prop] computableTidilyInPolyTime_extractNat

/-- The extracted witness `extractNat` is computable in polynomial time from the group description
and the four binary numbers. -/
theorem computableInPolyTime_extractNat {α : Type} {input : α ↪ List Bool}
    {d : α → F.Desc} {c z c' z' : α → ℕ} (hd : ComputableInPolyTime d input F.encDesc)
    (hc : ComputableInPolyTime c input encNat) (hz : ComputableInPolyTime z input encNat)
    (hc' : ComputableInPolyTime c' input encNat) (hz' : ComputableInPolyTime z' input encNat) :
    ComputableInPolyTime (fun a => extractNat (F.order (d a)) (c a) (z a) (c' a) (z' a))
      input encNat :=
  .of_tidy (computableTidilyInPolyTime_extractNat hd.tidy hc.tidy hz.tidy hc'.tidy hz'.tidy)

/-- **The rewinding adversary is uniform strict PPT** when the impersonator is and the challenge
length is computable in polynomial time. -/
theorem isPPTOn_rewind {k : ℕ → ℕ} (hk : ComputableInPolyTime k encUnary encUnary)
    {A : F.SchnorrImpersonator} (hA : A.IsPPT) :
    IsPPTOn (encPair encUnary (encPair F.encDesc encBits)) encBits
      (fun input => A.rewind k input.1 input.2) := by
  have hk' := hk.tidy
  have hrespond := hA.2
  unfold SchnorrImpersonator.rewind
  refine hA.1.bind_with ?_
  refine (ComputableInPolyTime.sampleList (by fun_prop)).bind_with ?_
  refine (ComputableInPolyTime.sampleList (by fun_prop)).bind_with ?_
  refine (hrespond.preprocess
    (prepare := fun p : (((ℕ × F.Desc × List Bool) × List Bool × List Bool) × List Bool) ×
      List Bool => (p.1.1.1.1, (p.1.1.2.2, p.1.2))) (by fun_prop)).bind_with ?_
  refine (hrespond.preprocess
    (prepare := fun p : ((((ℕ × F.Desc × List Bool) × List Bool × List Bool) × List Bool) ×
      List Bool) × List Bool => (p.1.1.1.1.1, (p.1.1.1.2.2, p.1.2))) (by fun_prop)).bind_with ?_
  exact ComputableTidilyInPolyTime.isPPTOn (by fun_prop)

/-! ### Security under the discrete-logarithm assumption -/

open scoped NNReal in
/-- **Schnorr identification is secure against direct attacks under the discrete-logarithm
assumption** ([BonehShoup2023], Theorem 19.1). Suppose the challenge length `k` is computable in
polynomial time, every group the setup can produce at parameter `n` has at least `2 ^ k n`
elements, and `1 / 2 ^ k n` is negligible. Then every uniform strict PPT impersonator succeeds
with negligible probability. -/
theorem negligible_schnorrDirectGame {setup : ℕ → PMF F.Desc} (hDL : F.DiscreteLog setup)
    {k : ℕ → ℕ} (hk : ComputableInPolyTime k encUnary encUnary)
    (hkq : ∀ n, ∀ d ∈ (setup n).support, 2 ^ k n ≤ F.order d)
    (hchallenge : Negligible fun n => 1 / 2 ^ k n) {A : F.SchnorrImpersonator} (hA : A.IsPPT) :
    Negligible fun n => Game.succProbability (F.schnorrDirectGame setup k A n) := by
  refine negligible_of_le (hchallenge.add (Negligible.sqrt (hDL _ (isPPTOn_rewind hk hA))))
    fun n => ?_
  rw [← NNReal.coe_le_coe, Pi.add_apply, NNReal.coe_add, Real.coe_sqrt, NNReal.coe_div,
    NNReal.coe_one, NNReal.coe_pow, NNReal.coe_ofNat]
  exact succProbability_schnorrDirectGame_le setup k A n (hkq n)

end Cslib.Crypto.PrimeOrderGroupFamily
