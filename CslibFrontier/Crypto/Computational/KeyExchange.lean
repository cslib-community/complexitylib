/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.DiffieHellman
public import CslibFrontier.Probability.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Crypto.Negligible.Basic
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF

/-!
# Key exchange secure against eavesdroppers

A two-party key-exchange protocol is described here by the law of its honest execution: the
transcript of messages that an eavesdropper sees, the key output by Alice and the key output by
Bob. It is correct when the two keys agree on every execution.

Security against a passive eavesdropper ([KatzLindell2020], Section 11.3, Definition 11.1,
p. 392) compares a real experiment, in which the adversary receives the transcript and Alice's
key, with an ideal experiment, in which it receives the transcript and an independently drawn
ideal key. The book phrases the experiment with a hidden uniform bit and asks that the adversary
guess it with probability at most `1 / 2 + negl(n)`; this is the same as requiring negligible
advantage between the real and the ideal experiment. The ideal key may depend on the transcript
through `idealKey : ℕ → T → PMF K`; Definition 11.1 itself draws a uniform `n`-bit word
(`KeyExchange.EavSecureBits`), while Theorem 11.3 uses a uniform element of the group named in the
transcript.

We formalize:

* the Diffie–Hellman protocol ([KatzLindell2020], Construction 11.2, pp. 392–393) over a
  `PrimeOrderGroupFamily`, its correctness, and Theorem 11.3 (p. 394): under the Decisional
  Diffie–Hellman assumption the protocol is secure against eavesdroppers when the ideal key is a
  uniform group element. The real and ideal experiments are exactly the real and ideal DDH
  experiments run on a re-associated adversary, so the reduction is tight;
* the man-in-the-middle attack of Exercise 11.3 (p. 399): an active adversary that replaces both
  public shares shares Alice's key with Alice and Bob's key with Bob, while each party's view has
  exactly the law of an honest execution;
* the protocol of Exercise 11.4 (p. 400), built from one-time XOR masks: Alice and Bob output the
  same key, yet the XOR of the three transcript words is the key, so the protocol is not secure
  against eavesdroppers.

Honest-party efficiency is not part of `KeyExchange`: the Diffie–Hellman parties compute their
messages and keys with the polynomial-time group operations of the family, and the XOR parties
compute pointwise XOR, but no theorem here depends on it.

## Main definitions

* `Cslib.Crypto.KeyExchange`, `Cslib.Crypto.KeyExchange.Outcome`: protocols as honest-execution
  laws.
* `Cslib.Crypto.KeyExchange.realGame`, `Cslib.Crypto.KeyExchange.idealGame`,
  `Cslib.Crypto.KeyExchange.EavSecure`, `Cslib.Crypto.KeyExchange.EavSecureBits`: security against
  eavesdroppers ([KatzLindell2020], Definition 11.1).
* `Cslib.Crypto.PrimeOrderGroupFamily.dhKeyExchange`,
  `Cslib.Crypto.PrimeOrderGroupFamily.dhIdealKey`: the Diffie–Hellman protocol and its group-element
  ideal key (Construction 11.2, Theorem 11.3).
* `Cslib.Crypto.PrimeOrderGroupFamily.dhMitmExecution`: the man-in-the-middle attack
  (Exercise 11.3).
* `Cslib.Crypto.KeyExchange.xorKeyExchange`, `Cslib.Crypto.KeyExchange.xorEavesdropper`: the XOR
  protocol of Exercise 11.4 and the eavesdropper that recovers its key.

## Main results

* `Cslib.Crypto.PrimeOrderGroupFamily.dhKeyExchange_correct`: Alice and Bob output the same key.
* `Cslib.Crypto.PrimeOrderGroupFamily.realGame_dhKeyExchange`,
  `Cslib.Crypto.PrimeOrderGroupFamily.idealGame_dhKeyExchange`: the experiments are the DDH
  experiments.
* `Cslib.Crypto.PrimeOrderGroupFamily.DDH.dhKeyExchange_eavSecure`: DDH implies security against
  eavesdroppers ([KatzLindell2020], Theorem 11.3).
* `Cslib.Crypto.PrimeOrderGroupFamily.dhMitmExecution_keys`,
  `Cslib.Crypto.PrimeOrderGroupFamily.map_aliceView_dhMitmExecution`,
  `Cslib.Crypto.PrimeOrderGroupFamily.map_bobView_dhMitmExecution`: the attack of Exercise 11.3.
* `Cslib.Crypto.KeyExchange.xorKeyExchange_correct`,
  `Cslib.Crypto.KeyExchange.not_eavSecureBits_xorKeyExchange`: the analysis of Exercise 11.4.

## References

* [J. Katz, Y. Lindell, *Introduction to Modern Cryptography*, 3rd ed.][KatzLindell2020],
  Section 11.3 (pp. 390–396) and Exercises 11.3–11.4 (pp. 399–400).
-/

public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM
open scoped ENNReal NNReal Cslib.Probability.PMF

/-- The result of one honest execution of a two-party key-exchange protocol: the transcript seen
by an eavesdropper and the keys output by Alice and by Bob. -/
structure KeyExchange.Outcome (T K : Type) where
  /-- All messages sent between the parties. -/
  transcript : T
  /-- The key output by Alice. -/
  aliceKey : K
  /-- The key output by Bob. -/
  bobKey : K

/-- A two-party key-exchange protocol with transcripts in `T` and keys in `K`, described by the
law of its honest execution at each security parameter. -/
structure KeyExchange (T K : Type) where
  /-- The law of the transcript and both keys when Alice and Bob run the protocol honestly. -/
  execute : ℕ → PMF (KeyExchange.Outcome T K)

namespace KeyExchange

variable {T K : Type}

/-- A key-exchange protocol is correct when Alice and Bob output the same key on every honest
execution ([KatzLindell2020], Section 11.3, p. 391). -/
@[expose]
def Correct (protocol : KeyExchange T K) : Prop :=
  ∀ n, ∀ outcome ∈ (protocol.execute n).support, outcome.aliceKey = outcome.bobKey

/-- The real eavesdropping experiment: run the protocol honestly and give the adversary the
transcript and Alice's key. This is `KE^eav` with hidden bit `0` ([KatzLindell2020], p. 391). -/
@[expose]
noncomputable def realGame (protocol : KeyExchange T K)
    (adversary : ℕ → T × K → ProbComp Bool) (n : ℕ) : Game := do
  let outcome ← protocol.execute n
  ProbComp.eval (adversary n (outcome.transcript, outcome.aliceKey))

/-- The ideal eavesdropping experiment: run the protocol honestly and give the adversary the
transcript and a fresh key drawn from `idealKey n transcript`. This is `KE^eav` with hidden bit
`1` ([KatzLindell2020], p. 391). -/
@[expose]
noncomputable def idealGame (protocol : KeyExchange T K) (idealKey : ℕ → T → PMF K)
    (adversary : ℕ → T × K → ProbComp Bool) (n : ℕ) : Game := do
  let outcome ← protocol.execute n
  let key ← idealKey n outcome.transcript
  ProbComp.eval (adversary n (outcome.transcript, key))

/-- Eavesdropper input `(1ⁿ, transcript, key)`: the security parameter in unary, then the
transcript encoded by `encT` and the key encoded by `encK`. -/
abbrev encEavInput (encT : T ↪ List Bool) (encK : K ↪ List Bool) : ℕ × T × K ↪ List Bool :=
  encPair encUnary (encPair encT encK)

/-- Security against eavesdroppers with ideal-key law `idealKey`: every uniform strict PPT
adversary has negligible advantage between `realGame` and `idealGame`. -/
@[expose]
def EavSecure (protocol : KeyExchange T K) (encT : T ↪ List Bool) (encK : K ↪ List Bool)
    (idealKey : ℕ → T → PMF K) : Prop :=
  Game.Indistinguishable protocol.realGame (protocol.idealGame idealKey)
    fun adversary => IsPPTOn (encEavInput encT encK) encBool
      (fun input => adversary input.1 input.2)

/-- Security against eavesdroppers for bit-word keys ([KatzLindell2020], Definition 11.1, p. 392):
the ideal key is a uniform `n`-bit word, independent of the transcript. -/
abbrev EavSecureBits (protocol : KeyExchange T (List Bool)) (encT : T ↪ List Bool) : Prop :=
  protocol.EavSecure encT encBits fun n _ => BitString.uniformList n

end KeyExchange

/-! ### The Diffie–Hellman protocol -/

namespace PrimeOrderGroupFamily

variable (F : PrimeOrderGroupFamily)

/-- Multiplying an encoded element by the representative `x.val` of an exponent
`x : ZMod (F.order d)` encodes `x • h`. -/
theorem smul_val_encode (d : F.Desc) (x : ZMod (F.order d)) (h : F.Carrier d) :
    F.smul (d, x.val, F.encode d h) = F.encode d (x • h) := by
  rw [F.smul_encode, ZMod.natCast_zmod_val]

/-- Diffie–Hellman transcript `(d, hA, hB)`: the group description, then Alice's and Bob's
public shares as bit words. -/
abbrev encDHTranscript : F.Desc × List Bool × List Bool ↪ List Bool :=
  encPair F.encDesc (encPair encBits encBits)

/-- The Diffie–Hellman key-exchange protocol ([KatzLindell2020], Construction 11.2, pp. 392–393).
Alice draws the group description `d` and a uniform exponent `x`, and sends `d` and
`hA = x • g`; Bob draws a uniform exponent `y` and sends `hB = y • g`. Alice outputs `x • hB` and
Bob outputs `y • hA`, each computed with the family's multiplication on encodings. -/
@[expose]
noncomputable def dhKeyExchange (setup : ℕ → PMF F.Desc) :
    KeyExchange (F.Desc × List Bool × List Bool) (List Bool) where
  execute n := do
    let d ← setup n
    let x ← PMF.uniformOfFintype (ZMod (F.order d))
    let y ← PMF.uniformOfFintype (ZMod (F.order d))
    let hA := F.encode d (x • F.generator d)
    let hB := F.encode d (y • F.generator d)
    return {
      transcript := (d, hA, hB)
      aliceKey := F.smul (d, x.val, hB)
      bobKey := F.smul (d, y.val, hA) }

/-- Every honest Diffie–Hellman execution is `(d, x • g, y • g)` with both keys equal to
`(x * y) • g`. -/
theorem mem_support_dhKeyExchange {setup : ℕ → PMF F.Desc} {n : ℕ}
    {outcome : KeyExchange.Outcome (F.Desc × List Bool × List Bool) (List Bool)}
    (h : outcome ∈ ((F.dhKeyExchange setup).execute n).support) :
    ∃ d ∈ (setup n).support, ∃ x y : ZMod (F.order d),
      outcome = {
        transcript := (d, F.encode d (x • F.generator d), F.encode d (y • F.generator d))
        aliceKey := F.encode d ((x * y) • F.generator d)
        bobKey := F.encode d ((x * y) • F.generator d) } := by
  simp only [dhKeyExchange, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
    PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at h
  obtain ⟨d, hd, x, -, y, -, rfl⟩ := h
  refine ⟨d, hd, x, y, ?_⟩
  rw [F.smul_val_encode, F.smul_val_encode, smul_smul, smul_smul, mul_comm y x]

/-- Alice and Bob output the same key, `(x * y) • g` ([KatzLindell2020], p. 393). -/
theorem dhKeyExchange_correct (setup : ℕ → PMF F.Desc) : (F.dhKeyExchange setup).Correct := by
  intro n outcome h
  obtain ⟨d, -, x, y, rfl⟩ := F.mem_support_dhKeyExchange h
  rfl

/-- The ideal key of [KatzLindell2020], Theorem 11.3 (p. 394): a uniform element of the group
named in the transcript. -/
@[expose]
noncomputable def dhIdealKey (_n : ℕ) (transcript : F.Desc × List Bool × List Bool) :
    PMF (List Bool) := do
  let (d, _, _) := transcript
  let z ← PMF.uniformOfFintype (ZMod (F.order d))
  return F.encode d (z • F.generator d)

/-- Re-associate an eavesdropper on Diffie–Hellman transcripts as a DDH distinguisher: the DDH
tuple `(d, u, v, w)` is passed on as the transcript `(d, u, v)` with key `w`. -/
@[expose]
def dhEavToDDH (adversary : ℕ → (F.Desc × List Bool × List Bool) × List Bool → ProbComp Bool)
    (n : ℕ) (input : F.Desc × List Bool × List Bool × List Bool) : ProbComp Bool :=
  let (d, u, v, w) := input
  adversary n ((d, u, v), w)

/-- The real eavesdropping experiment on Diffie–Hellman is the real DDH experiment. -/
theorem realGame_dhKeyExchange (setup : ℕ → PMF F.Desc)
    (adversary : ℕ → (F.Desc × List Bool × List Bool) × List Bool → ProbComp Bool) (n : ℕ) :
    (F.dhKeyExchange setup).realGame adversary n =
      F.ddhRealGame setup (F.dhEavToDDH adversary) n := by
  simp only [KeyExchange.realGame, dhKeyExchange, ddhRealGame, dhEavToDDH,
    PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.bind_bind, PMF.pure_bind,
    smul_val_encode, smul_smul]

/-- With the uniform group element as ideal key, the ideal eavesdropping experiment on
Diffie–Hellman is the ideal DDH experiment. -/
theorem idealGame_dhKeyExchange (setup : ℕ → PMF F.Desc)
    (adversary : ℕ → (F.Desc × List Bool × List Bool) × List Bool → ProbComp Bool) (n : ℕ) :
    (F.dhKeyExchange setup).idealGame F.dhIdealKey adversary n =
      F.ddhIdealGame setup (F.dhEavToDDH adversary) n := by
  simp only [KeyExchange.idealGame, dhKeyExchange, dhIdealKey, ddhIdealGame, dhEavToDDH,
    PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.bind_bind, PMF.pure_bind]

/-- The re-association `dhEavToDDH` is uniform strict PPT when the eavesdropper is. -/
theorem isPPTOn_dhEavToDDH
    {adversary : ℕ → (F.Desc × List Bool × List Bool) × List Bool → ProbComp Bool}
    (hA : IsPPTOn (KeyExchange.encEavInput F.encDHTranscript encBits) encBool
      (fun input => adversary input.1 input.2)) :
    IsPPTOn (encPair encUnary (encPair F.encDesc (encPair encBits (encPair encBits encBits))))
      encBool (fun input => F.dhEavToDDH adversary input.1 input.2) := by
  have h2 := ComputableInPolyTime.snd encUnary
    (encPair F.encDesc (encPair encBits (encPair encBits encBits)))
  have h3 :=
    (ComputableInPolyTime.snd F.encDesc (encPair encBits (encPair encBits encBits))).comp h2
  have h4 := (ComputableInPolyTime.snd encBits (encPair encBits encBits)).comp h3
  exact hA.preprocess
    (prepare := fun input : ℕ × F.Desc × List Bool × List Bool × List Bool =>
      (input.1, ((input.2.1, input.2.2.1, input.2.2.2.1), input.2.2.2.2)))
    ((ComputableInPolyTime.fst _ _).prod
      ((((ComputableInPolyTime.fst _ _).comp h2).prod
        (((ComputableInPolyTime.fst _ _).comp h3).prod
          ((ComputableInPolyTime.fst _ _).comp h4))).prod
        ((ComputableInPolyTime.snd _ _).comp h4)))

/-- **Diffie–Hellman key exchange is secure against eavesdroppers under DDH**
([KatzLindell2020], Theorem 11.3, p. 394): if the Decisional Diffie–Hellman assumption holds for
`setup`, then no uniform strict PPT eavesdropper distinguishes the transcript and Alice's key from
the transcript and a uniform element of the same group. -/
theorem DDH.dhKeyExchange_eavSecure {F : PrimeOrderGroupFamily} {setup : ℕ → PMF F.Desc}
    (hDDH : F.DDH setup) :
    (F.dhKeyExchange setup).EavSecure F.encDHTranscript encBits F.dhIdealKey := by
  intro adversary hA
  simpa only [realGame_dhKeyExchange, idealGame_dhKeyExchange] using
    hDDH _ (F.isPPTOn_dhEavToDDH hA)

/-! ### The man-in-the-middle attack -/

/-- The outcome of the man-in-the-middle attack of [KatzLindell2020], Exercise 11.3 (p. 399):
the messages Alice and Bob each receive together with their own share, the keys they output, and
the keys the adversary computes for its sessions with each of them. -/
structure DHMitmOutcome where
  /-- Alice's view of the transcript: `(d, hA, hB')` with the substituted share `hB'`. -/
  aliceView : F.Desc × List Bool × List Bool
  /-- The key output by Alice. -/
  aliceKey : List Bool
  /-- Bob's view of the transcript: `(d, hA', hB)` with the substituted share `hA'`. -/
  bobView : F.Desc × List Bool × List Bool
  /-- The key output by Bob. -/
  bobKey : List Bool
  /-- The key the adversary computes for its session with Alice. -/
  adversaryAliceKey : List Bool
  /-- The key the adversary computes for its session with Bob. -/
  adversaryBobKey : List Bool

/-- The man-in-the-middle attack on Diffie–Hellman ([KatzLindell2020], Exercise 11.3, p. 399).
Alice and Bob run Construction 11.2 honestly with exponents `x` and `y`. The adversary draws its
own exponents `x'` and `y'`, delivers `hB' = y' • g` to Alice in place of `hB` and `hA' = x' • g`
to Bob in place of `hA`, and computes `y' • hA` and `x' • hB`. -/
@[expose]
noncomputable def dhMitmExecution (setup : ℕ → PMF F.Desc) (n : ℕ) : PMF F.DHMitmOutcome := do
  let d ← setup n
  let x ← PMF.uniformOfFintype (ZMod (F.order d))
  let y ← PMF.uniformOfFintype (ZMod (F.order d))
  let x' ← PMF.uniformOfFintype (ZMod (F.order d))
  let y' ← PMF.uniformOfFintype (ZMod (F.order d))
  let hA := F.encode d (x • F.generator d)
  let hB := F.encode d (y • F.generator d)
  let hA' := F.encode d (x' • F.generator d)
  let hB' := F.encode d (y' • F.generator d)
  return {
    aliceView := (d, hA, hB')
    aliceKey := F.smul (d, x.val, hB')
    bobView := (d, hA', hB)
    bobKey := F.smul (d, y.val, hA')
    adversaryAliceKey := F.smul (d, y'.val, hA)
    adversaryBobKey := F.smul (d, x'.val, hB) }

/-- In the man-in-the-middle attack the adversary knows the key Alice outputs and the key Bob
outputs. -/
theorem dhMitmExecution_keys (setup : ℕ → PMF F.Desc) (n : ℕ) :
    ∀ outcome ∈ (F.dhMitmExecution setup n).support,
      outcome.adversaryAliceKey = outcome.aliceKey ∧ outcome.adversaryBobKey = outcome.bobKey := by
  intro outcome h
  simp only [dhMitmExecution, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
    PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at h
  obtain ⟨d, -, x, -, y, -, x', -, y', -, rfl⟩ := h
  simp only [smul_val_encode, smul_smul, mul_comm, and_self]

/-- Alice cannot detect the attack: her view and her key have exactly the law of an honest
Diffie–Hellman execution. -/
theorem map_aliceView_dhMitmExecution (setup : ℕ → PMF F.Desc) (n : ℕ) :
    (F.dhMitmExecution setup n).map (fun outcome => (outcome.aliceView, outcome.aliceKey)) =
      ((F.dhKeyExchange setup).execute n).map
        (fun outcome => (outcome.transcript, outcome.aliceKey)) := by
  simp only [dhMitmExecution, dhKeyExchange, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
    PMF.map_bind, PMF.pure_map, PMF.bind_const]

/-- Bob cannot detect the attack: his view and his key have exactly the law of an honest
Diffie–Hellman execution. -/
theorem map_bobView_dhMitmExecution (setup : ℕ → PMF F.Desc) (n : ℕ) :
    (F.dhMitmExecution setup n).map (fun outcome => (outcome.bobView, outcome.bobKey)) =
      ((F.dhKeyExchange setup).execute n).map
        (fun outcome => (outcome.transcript, outcome.bobKey)) := by
  simp only [dhMitmExecution, dhKeyExchange, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
    PMF.map_bind, PMF.pure_map, PMF.bind_const]
  refine congrArg (PMF.bind (setup n)) (funext fun d => ?_)
  exact PMF.bind_comm _ _ _

end PrimeOrderGroupFamily

/-! ### A protocol built from XOR masks -/

namespace KeyExchange

/-- The protocol of [KatzLindell2020], Exercise 11.4 (p. 400). Alice draws uniform `n`-bit words
`k` and `r` and sends `s = k ⊕ r`; Bob draws a uniform `n`-bit word `t` and sends `u = s ⊕ t`;
Alice sends `w = u ⊕ r`. Alice outputs `k` and Bob outputs `w ⊕ t`. -/
@[expose]
noncomputable def xorKeyExchange : KeyExchange (List Bool × List Bool × List Bool) (List Bool) where
  execute n := do
    let k ← BitString.uniformList n
    let r ← BitString.uniformList n
    let t ← BitString.uniformList n
    let s := List.zipWith Bool.xor k r
    let u := List.zipWith Bool.xor s t
    let w := List.zipWith Bool.xor u r
    return { transcript := (s, u, w), aliceKey := k, bobKey := List.zipWith Bool.xor w t }

/-- For equal-length words, Bob's key `w ⊕ t` equals `k`, and so does `w ⊕ (s ⊕ u)`. -/
private theorem xor_identities : ∀ k r t : List Bool, r.length = k.length → t.length = k.length →
    let s := List.zipWith Bool.xor k r
    let u := List.zipWith Bool.xor s t
    let w := List.zipWith Bool.xor u r
    List.zipWith Bool.xor w t = k ∧ List.zipWith Bool.xor w (List.zipWith Bool.xor s u) = k
  | [], _, _, _, _ => by simp
  | _ :: _, [], _, hr, _ => by simp at hr
  | _ :: _, _ :: _, [], _, ht => by simp at ht
  | a :: k, b :: r, c :: t, hr, ht => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hr ht
    obtain ⟨h₁, h₂⟩ := xor_identities k r t hr ht
    simp only [List.zipWith_cons_cons, h₁, h₂, List.cons.injEq, and_true]
    cases a <;> cases b <;> cases c <;> decide

/-- Every honest execution of the XOR protocol comes from `n`-bit words `k`, `r` and `t`. -/
theorem mem_support_xorKeyExchange {n : ℕ}
    {outcome : Outcome (List Bool × List Bool × List Bool) (List Bool)}
    (h : outcome ∈ (xorKeyExchange.execute n).support) :
    ∃ k r t : List Bool, k.length = n ∧ r.length = n ∧ t.length = n ∧
      outcome = {
        transcript := (List.zipWith Bool.xor k r,
          List.zipWith Bool.xor (List.zipWith Bool.xor k r) t,
          List.zipWith Bool.xor (List.zipWith Bool.xor (List.zipWith Bool.xor k r) t) r)
        aliceKey := k
        bobKey := List.zipWith Bool.xor
          (List.zipWith Bool.xor (List.zipWith Bool.xor (List.zipWith Bool.xor k r) t) r) t } := by
  simp only [xorKeyExchange, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
    PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at h
  obtain ⟨k, hk, r, hr, t, ht, rfl⟩ := h
  exact ⟨k, r, t, BitString.length_of_mem_support_uniformList hk,
    BitString.length_of_mem_support_uniformList hr,
    BitString.length_of_mem_support_uniformList ht, rfl⟩

/-- Alice and Bob output the same key ([KatzLindell2020], Exercise 11.4, p. 400). -/
theorem xorKeyExchange_correct : xorKeyExchange.Correct := by
  intro n outcome h
  obtain ⟨k, r, t, hk, hr, ht, rfl⟩ := mem_support_xorKeyExchange h
  exact ((xor_identities k r t (hr.trans hk.symm) (ht.trans hk.symm)).1).symm

/-- The eavesdropper that accepts exactly when the candidate key is the XOR `w ⊕ (s ⊕ u)` of the
three transcript words. -/
@[expose]
def xorEavesdropper (_n : ℕ) (input : (List Bool × List Bool × List Bool) × List Bool) :
    ProbComp Bool :=
  let ((s, u, w), key) := input
  return decide (key = List.zipWith Bool.xor w (List.zipWith Bool.xor s u))

/-- On the real key the eavesdropper always accepts. -/
theorem realGame_xorEavesdropper (n : ℕ) :
    xorKeyExchange.realGame xorEavesdropper n = PMF.pure true := by
  simp only [realGame, PMF.monad_bind_eq_bind]
  rw [← PMF.bind_const (xorKeyExchange.execute n) (PMF.pure true)]
  refine PMF.bind_congr_on_support _ _ _ fun outcome h => ?_
  obtain ⟨k, r, t, hk, hr, ht, rfl⟩ := mem_support_xorKeyExchange h
  simp only [xorEavesdropper, ProbComp.eval_pure,
    (xor_identities k r t (hr.trans hk.symm) (ht.trans hk.symm)).2, decide_true]

/-- On a uniform `n`-bit key the eavesdropper accepts with probability at most `1 / 2 ^ n`. -/
theorem idealGame_xorEavesdropper_true_le (n : ℕ) :
    xorKeyExchange.idealGame (fun n _ => BitString.uniformList n) xorEavesdropper n true ≤
      1 / 2 ^ n := by
  simp only [idealGame, xorEavesdropper, ProbComp.eval_pure, PMF.monad_bind_eq_bind,
    PMF.bind_apply, PMF.pure_apply, eq_comm (a := true), decide_eq_true_eq, mul_ite, mul_one,
    mul_zero, tsum_ite_eq]
  calc ∑' outcome, xorKeyExchange.execute n outcome * BitString.uniformList n
        (List.zipWith Bool.xor outcome.transcript.2.2
          (List.zipWith Bool.xor outcome.transcript.1 outcome.transcript.2.1))
      ≤ ∑' outcome, xorKeyExchange.execute n outcome * (1 / 2 ^ n) :=
        tsum_le_tsum fun _ => mul_le_mul_of_nonneg_left (BitString.uniformList_apply_le _ _)
          zero_le
    _ = 1 / 2 ^ n := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

/-- From `n = 1` on, the eavesdropper's advantage is at least `1 / 2`. -/
theorem half_le_advantage_xorEavesdropper {n : ℕ} (hn : n ≠ 0) :
    (1 / 2 : ℝ≥0) ≤ Game.advantage (xorKeyExchange.realGame xorEavesdropper n)
      (xorKeyExchange.idealGame (fun n _ => BitString.uniformList n) xorEavesdropper n) := by
  have hle : xorKeyExchange.idealGame (fun n _ => BitString.uniformList n) xorEavesdropper n
      true ≤ 2⁻¹ :=
    (idealGame_xorEavesdropper_true_le n).trans (by
      rw [one_div]
      exact ENNReal.inv_le_inv.mpr (le_self_pow₀ (by norm_num) hn))
  have hreal := ENNReal.toReal_mono (by simp) hle
  rw [← NNReal.coe_le_coe, Game.coe_advantage, realGame_xorEavesdropper]
  simp only [Game.coe_succProbability, PMF.pure_apply, ite_true, ENNReal.toReal_one,
    ENNReal.toReal_inv, ENNReal.toReal_ofNat] at hreal ⊢
  rw [abs_of_nonneg (by linarith)]
  push_cast
  linarith

/-- Transcript `(s, u, w)` of the XOR protocol: three bit words. -/
abbrev encXorTranscript : List Bool × List Bool × List Bool ↪ List Bool :=
  encPair encBits (encPair encBits encBits)

/-- The XOR eavesdropper is uniform strict PPT. -/
theorem isPPTOn_xorEavesdropper :
    IsPPTOn (encEavInput encXorTranscript encBits) encBool
      (fun input => xorEavesdropper input.1 input.2) := by
  have hkey : ComputableInPolyTime
      (fun input : ℕ × (List Bool × List Bool × List Bool) × List Bool => input.2.2)
      (encEavInput encXorTranscript encBits) encBits := by
    dsimp only [encEavInput, encXorTranscript]
    fun_prop
  have hrec : ComputableInPolyTime
      (fun input : ℕ × (List Bool × List Bool × List Bool) × List Bool =>
        List.zipWith Bool.xor input.2.1.2.2 (List.zipWith Bool.xor input.2.1.1 input.2.1.2.1))
      (encEavInput encXorTranscript encBits) encBits := by
    dsimp only [encEavInput, encXorTranscript]
    fun_prop
  exact (hkey.decide_eq' hrec).isPPTOn

/-- **The XOR protocol is not secure against eavesdroppers** ([KatzLindell2020], Exercise 11.4,
p. 400): the XOR of the three transcript words is the key, so the eavesdropper
`xorEavesdropper` has advantage at least `1 / 2` at every parameter `n ≥ 1`. -/
theorem not_eavSecureBits_xorKeyExchange : ¬ xorKeyExchange.EavSecureBits encXorTranscript := by
  intro h
  refine not_negligible_const (c := (1 / 2 : ℝ≥0)) (by norm_num) ?_
  exact negligible_of_le ((h xorEavesdropper isPPTOn_xorEavesdropper).shift 1)
    fun n => half_le_advantage_xorEavesdropper n.succ_ne_zero

end KeyExchange

end Cslib.Crypto
