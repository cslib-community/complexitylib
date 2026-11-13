/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.DiffieHellman
public import CslibFrontier.Crypto.Game.Experiment
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
Bob. Keys may live in a set named by the transcript, such as the group chosen in Diffie–Hellman,
so the key type is a family `K : T → Type`. The protocol is correct when the two keys agree on
every execution.

Security against a passive eavesdropper ([KatzLindell2020], Section 11.3, Definition 11.1,
p. 392) compares a real experiment, in which the adversary receives the view made of the transcript
and Alice's key, with an ideal experiment, in which the view pairs the transcript with an
independently drawn ideal key. The book phrases the experiment with a hidden uniform bit and asks
that the adversary guess it with probability at most `1 / 2 + negl(n)`; this is the same as
requiring negligible advantage between the real and the ideal experiment. Both experiments are
"draw a view, then run the eavesdropper on it" (`Game.withSetup`), for the view laws `realView`
and `idealView` of an execution law. The ideal key may depend on the transcript through
`idealKey : ℕ → (t : T) → PMF (K t)`; Definition 11.1 itself draws a uniform `n`-bit word
(`KeyExchange.EavSecureBits`), while Theorem 11.3 uses a uniform element of the group named in the
transcript.

Eavesdroppers are typed: an `Eavesdropper T K` receives the security parameter and a `View T K`.
Encodings appear only in its efficiency predicate `Eavesdropper.IsPPT`, which reads the view
through `encView`.

We formalize:

* the Diffie–Hellman protocol ([KatzLindell2020], Construction 11.2, pp. 392–393) over a
  `PrimeOrderGroupFamily`, its correctness, and Theorem 11.3 (p. 394): under the Decisional
  Diffie–Hellman assumption the protocol is secure against eavesdroppers when the ideal key is a
  uniform group element. At a fixed group, the real and ideal experiments are exactly the real and
  random DDH experiments run on the typed distinguisher `dhEavToDDH`, which passes the three group
  elements to the eavesdropper as its view; the family statements follow by drawing the group
  first, so the reduction is tight;
* the man-in-the-middle attack of Exercise 11.3 (p. 399): at a fixed group, an active adversary
  that replaces both public shares shares Alice's key with Alice and Bob's key with Bob, while
  each party's view has exactly the law of the eavesdropper's view of an honest execution;
* the protocol of Exercise 11.4 (p. 400), built from one-time XOR masks: Alice and Bob output the
  same key, yet the XOR of the three transcript words is the key, so the protocol is not secure
  against eavesdroppers.

Honest-party efficiency is not part of `KeyExchange`: the Diffie–Hellman parties compute their
messages and keys with the polynomial-time group operations of the family, and the XOR parties
compute pointwise XOR, but no theorem here depends on it.

## Main definitions

* `Cslib.Crypto.KeyExchange`, `Cslib.Crypto.KeyExchange.Outcome`: protocols as honest-execution
  laws.
* `Cslib.Crypto.KeyExchange.View`, `Cslib.Crypto.KeyExchange.encView`,
  `Cslib.Crypto.KeyExchange.Eavesdropper`, `Cslib.Crypto.KeyExchange.Eavesdropper.IsPPT`: typed
  eavesdroppers and their efficiency on encoded views.
* `Cslib.Crypto.KeyExchange.realView`, `Cslib.Crypto.KeyExchange.idealView`,
  `Cslib.Crypto.KeyExchange.realGame`, `Cslib.Crypto.KeyExchange.idealGame`,
  `Cslib.Crypto.KeyExchange.EavSecure`, `Cslib.Crypto.KeyExchange.EavSecureBits`: security against
  eavesdroppers ([KatzLindell2020], Definition 11.1).
* `Cslib.Crypto.PrimeOrderGroupFamily.DHTranscript`,
  `Cslib.Crypto.PrimeOrderGroupFamily.dhExecution`,
  `Cslib.Crypto.PrimeOrderGroupFamily.dhKeyExchange`,
  `Cslib.Crypto.PrimeOrderGroupFamily.dhIdealKey`: the Diffie–Hellman protocol at a fixed group
  and over a setup law, and its group-element ideal key (Construction 11.2, Theorem 11.3).
* `Cslib.Crypto.PrimeOrderGroupFamily.dhEavToDDH`: the reduction to DDH.
* `Cslib.Crypto.PrimeOrderGroupFamily.dhMitmExecution`: the man-in-the-middle attack
  (Exercise 11.3).
* `Cslib.Crypto.KeyExchange.xorKeyExchange`, `Cslib.Crypto.KeyExchange.xorEavesdropper`: the XOR
  protocol of Exercise 11.4 and the eavesdropper that recovers its key.

## Main results

* `Cslib.Crypto.KeyExchange.withSetup_realView_bind`,
  `Cslib.Crypto.KeyExchange.withSetup_idealView_bind`: a protocol that draws public parameters
  first is attacked by drawing them, then running the fixed experiment.
* `Cslib.Crypto.PrimeOrderGroupFamily.dhKeyExchange_correct`: Alice and Bob output the same key.
* `Cslib.Crypto.PrimeOrderGroupFamily.withSetup_realView_dhExecution`,
  `Cslib.Crypto.PrimeOrderGroupFamily.withSetup_idealView_dhExecution`: at a fixed group the
  experiments are the DDH experiments; `realGame_dhKeyExchange` and `idealGame_dhKeyExchange` are
  the family versions.
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
by an eavesdropper and the keys output by Alice and by Bob, which lie in the key set `K transcript`
named by the transcript. -/
structure KeyExchange.Outcome (T : Type) (K : T → Type) where
  /-- All messages sent between the parties. -/
  transcript : T
  /-- The key output by Alice. -/
  aliceKey : K transcript
  /-- The key output by Bob. -/
  bobKey : K transcript

/-- A two-party key-exchange protocol with transcripts in `T` and keys in `K transcript`, described
by the law of its honest execution at each security parameter. -/
structure KeyExchange (T : Type) (K : T → Type) where
  /-- The law of the transcript and both keys when Alice and Bob run the protocol honestly. -/
  execute : ℕ → PMF (KeyExchange.Outcome T K)

namespace KeyExchange

variable {T : Type} {K : T → Type}

/-- A key-exchange protocol is correct when Alice and Bob output the same key on every honest
execution ([KatzLindell2020], Section 11.3, p. 391). -/
@[expose]
def Correct (protocol : KeyExchange T K) : Prop :=
  ∀ n, ∀ outcome ∈ (protocol.execute n).support, outcome.aliceKey = outcome.bobKey

/-- What an eavesdropper is given: a transcript and a candidate key for it. -/
structure View (T : Type) (K : T → Type) where
  /-- All messages sent between the parties. -/
  transcript : T
  /-- The candidate key: Alice's key in the real experiment, an ideal key in the ideal one. -/
  key : K transcript

/-- The encoding of a view: the transcript encoded by `encT`, framed, then the key encoded by
`encK transcript` (`encView_apply`). -/
enc_structure encView (encT : T ↪ List Bool) (encK : (t : T) → K t ↪ List Bool) : View T K where
  transcript : encT, key : (encK transcript) using ((encK transcript).injective)

/-- The real view: run the protocol honestly and pair the transcript with Alice's key. This is
what the adversary sees in `KE^eav` with hidden bit `0` ([KatzLindell2020], p. 391). -/
@[expose]
noncomputable def realView (execution : PMF (Outcome T K)) : PMF (View T K) := do
  let outcome ← execution
  return ⟨outcome.transcript, outcome.aliceKey⟩

/-- The ideal view: run the protocol honestly and pair the transcript with a fresh key drawn from
`idealKey transcript`. This is what the adversary sees in `KE^eav` with hidden bit `1`
([KatzLindell2020], p. 391). -/
@[expose]
noncomputable def idealView (idealKey : (t : T) → PMF (K t)) (execution : PMF (Outcome T K)) :
    PMF (View T K) := do
  let outcome ← execution
  let key ← idealKey outcome.transcript
  return ⟨outcome.transcript, key⟩

/-- An eavesdropper: given the security parameter and a view, it outputs a bit.
`Eavesdropper.IsPPT` states its efficiency on encodings. -/
abbrev Eavesdropper (T : Type) (K : T → Type) : Type :=
  ℕ → View T K → ProbComp Bool

/-- Eavesdropper input `(1ⁿ, view)`: the security parameter in unary, then the view encoded by
`encView encT encK`. For a constant key encoding these are the words of
`encPair encUnary (encPair encT encK)` on `(n, (transcript, key))`. -/
abbrev encEavInput (encT : T ↪ List Bool) (encK : (t : T) → K t ↪ List Bool) :
    ℕ × View T K ↪ List Bool :=
  encPair encUnary (encView encT encK)

/-- An eavesdropper is PPT when one uniform strict PPT machine reads `encEavInput encT encK` and
writes the adversary's bit. -/
@[expose]
def Eavesdropper.IsPPT (encT : T ↪ List Bool) (encK : (t : T) → K t ↪ List Bool)
    (adversary : Eavesdropper T K) : Prop :=
  IsPPTOn (encEavInput encT encK) encBool fun input => adversary input.1 input.2

/-- The real eavesdropping experiment `KE^eav` with hidden bit `0`: draw the real view, then run
the eavesdropper on it. -/
@[expose]
noncomputable def realGame (protocol : KeyExchange T K) (adversary : Eavesdropper T K) (n : ℕ) :
    Game :=
  Game.withSetup (realView (protocol.execute n)) (adversary n)

/-- The ideal eavesdropping experiment `KE^eav` with hidden bit `1`: draw the ideal view with key
law `idealKey n`, then run the eavesdropper on it. -/
@[expose]
noncomputable def idealGame (protocol : KeyExchange T K) (idealKey : ℕ → (t : T) → PMF (K t))
    (adversary : Eavesdropper T K) (n : ℕ) : Game :=
  Game.withSetup (idealView (idealKey n) (protocol.execute n)) (adversary n)

/-- Security against eavesdroppers with ideal-key law `idealKey`: every uniform strict PPT
eavesdropper has negligible advantage between `realGame` and `idealGame`. -/
@[expose]
def EavSecure (protocol : KeyExchange T K) (encT : T ↪ List Bool)
    (encK : (t : T) → K t ↪ List Bool) (idealKey : ℕ → (t : T) → PMF (K t)) : Prop :=
  Game.Indistinguishable protocol.realGame (protocol.idealGame idealKey)
    (Eavesdropper.IsPPT encT encK)

/-- Security against eavesdroppers for bit-word keys ([KatzLindell2020], Definition 11.1, p. 392):
the ideal key is a uniform `n`-bit word, independent of the transcript. -/
abbrev EavSecureBits (protocol : KeyExchange T fun _ => List Bool) (encT : T ↪ List Bool) :
    Prop :=
  protocol.EavSecure encT (fun _ => encBits) fun n _ => BitString.uniformList n

/-- For a protocol that first draws public parameters `p` from `setup`, then runs the execution
`execution p`, the real experiment draws `p` and then runs the fixed real experiment of
`execution p`. -/
theorem withSetup_realView_bind {P : Type} (setup : PMF P) (execution : P → PMF (Outcome T K))
    (exp : View T K → Experiment) :
    Game.withSetup (realView (setup.bind execution)) exp =
      setup.bind fun p => Game.withSetup (realView (execution p)) exp := by
  simp only [Game.withSetup, realView, PMF.monad_bind_eq_bind, PMF.bind_bind]

/-- For a protocol that first draws public parameters `p` from `setup`, then runs the execution
`execution p`, the ideal experiment draws `p` and then runs the fixed ideal experiment of
`execution p`. -/
theorem withSetup_idealView_bind {P : Type} (setup : PMF P) (execution : P → PMF (Outcome T K))
    (idealKey : (t : T) → PMF (K t)) (exp : View T K → Experiment) :
    Game.withSetup (idealView idealKey (setup.bind execution)) exp =
      setup.bind fun p => Game.withSetup (idealView idealKey (execution p)) exp := by
  simp only [Game.withSetup, idealView, PMF.monad_bind_eq_bind, PMF.bind_bind]

end KeyExchange

/-! ### The Diffie–Hellman protocol -/

namespace PrimeOrderGroupFamily

open KeyExchange (Eavesdropper View realView idealView)

variable (F : PrimeOrderGroupFamily)

/-- A Diffie–Hellman transcript: the group parameters chosen by Alice and the public shares
`hA = x • g` of Alice and `hB = y • g` of Bob in that group. -/
structure DHTranscript where
  /-- The group parameters sent by Alice. -/
  groupParameters : F.Desc
  /-- Alice's public share `hA = x • g`. -/
  aliceShare : F.Carrier groupParameters
  /-- Bob's public share `hB = y • g`. -/
  bobShare : F.Carrier groupParameters

/-- The encoding of a Diffie–Hellman transcript: the group parameters and the words
`F.encode d hA`, `F.encode d hB` of the shares, each framed except the last
(`encDHTranscript_apply`). -/
enc_structure encDHTranscript (F : PrimeOrderGroupFamily) : DHTranscript F where
  groupParameters : F.encDesc,
  aliceShare : (F.encode groupParameters) using (F.encode_injective groupParameters),
  bobShare : (F.encode groupParameters) using (F.encode_injective groupParameters)

/-- A Diffie–Hellman key is an element of the group named in the transcript. -/
abbrev DHKey (transcript : F.DHTranscript) : Type :=
  F.Carrier transcript.groupParameters

/-- A Diffie–Hellman key is encoded as an element of the group named in the transcript. -/
@[expose]
def encDHKey (transcript : F.DHTranscript) : F.DHKey transcript ↪ List Bool :=
  ⟨F.encode transcript.groupParameters, F.encode_injective _⟩

@[simp]
theorem encDHKey_apply (transcript : F.DHTranscript) (key : F.DHKey transcript) :
    F.encDHKey transcript key = F.encode transcript.groupParameters key :=
  rfl

variable {F} in
/-- A computed Diffie–Hellman key is encoded by the word of the computed group element. -/
@[fun_prop] theorem computableInPolyTime_encDHKey {α : Type} {enc : α ↪ List Bool}
    {t : α → F.DHTranscript} {key : (a : α) → F.DHKey (t a)}
    (h : ComputableInPolyTime (fun a => F.encode (t a).groupParameters (key a)) enc encBits) :
    ComputableInPolyTime (fun a => F.encDHKey (t a) (key a)) enc encBits :=
  h

/-- The honest Diffie–Hellman execution in the group `d` ([KatzLindell2020], Construction 11.2,
pp. 392–393). Alice draws a uniform exponent `x` and sends `d` and `hA = x • g`; Bob draws a
uniform exponent `y` and sends `hB = y • g`. Alice outputs `x • hB` and Bob outputs `y • hA`. -/
@[expose]
noncomputable def dhExecution (d : F.Desc) : PMF (KeyExchange.Outcome F.DHTranscript F.DHKey) := do
  let x ← PMF.uniformOfFintype (ZMod (F.order d))
  let y ← PMF.uniformOfFintype (ZMod (F.order d))
  let hA := x • F.generator d
  let hB := y • F.generator d
  return { transcript := ⟨d, hA, hB⟩, aliceKey := x • hB, bobKey := y • hA }

/-- The Diffie–Hellman key-exchange protocol ([KatzLindell2020], Construction 11.2): Alice draws
the group parameters `d` from `setup n`, then the parties run `dhExecution d`. -/
@[expose]
noncomputable def dhKeyExchange (setup : ℕ → PMF F.Desc) :
    KeyExchange F.DHTranscript F.DHKey where
  execute n := (setup n).bind F.dhExecution

/-- Every honest Diffie–Hellman execution in the group `d` is `(d, x • g, y • g)` with both keys
equal to `(x * y) • g`. -/
theorem mem_support_dhExecution {d : F.Desc} {outcome : KeyExchange.Outcome F.DHTranscript F.DHKey}
    (h : outcome ∈ (F.dhExecution d).support) :
    ∃ x y : ZMod (F.order d), outcome = {
      transcript := ⟨d, x • F.generator d, y • F.generator d⟩
      aliceKey := (x * y) • F.generator d
      bobKey := (x * y) • F.generator d } := by
  simp only [dhExecution, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
    PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at h
  obtain ⟨x, -, y, -, rfl⟩ := h
  refine ⟨x, y, ?_⟩
  rw [smul_smul, smul_smul, mul_comm y x]

/-- Alice and Bob output the same key, `(x * y) • g` ([KatzLindell2020], p. 393). -/
theorem dhKeyExchange_correct (setup : ℕ → PMF F.Desc) : (F.dhKeyExchange setup).Correct := by
  intro n outcome h
  obtain ⟨d, -, h⟩ := (PMF.mem_support_bind_iff _ _ _).1 h
  obtain ⟨x, y, rfl⟩ := F.mem_support_dhExecution h
  rfl

/-- The ideal key of [KatzLindell2020], Theorem 11.3 (p. 394): a uniform element of the group
named in the transcript. -/
@[expose]
noncomputable def dhIdealKey (transcript : F.DHTranscript) : PMF (F.DHKey transcript) :=
  (PMF.uniformOfFintype (ZMod (F.order transcript.groupParameters))).map
    fun z => z • F.generator transcript.groupParameters

/-- Run an eavesdropper on Diffie–Hellman views as a DDH distinguisher: the elements `(u, v, w)`
of the group `d` are passed on as the transcript `(d, u, v)` with key `w`. -/
@[expose]
def dhEavToDDH (adversary : Eavesdropper F.DHTranscript F.DHKey) : F.DDHDistinguisher :=
  fun n d u v w => adversary n ⟨⟨d, u, v⟩, w⟩

/-- At a fixed group, the real eavesdropping experiment on Diffie–Hellman is the real DDH
experiment. -/
theorem withSetup_realView_dhExecution (adversary : Eavesdropper F.DHTranscript F.DHKey) (n : ℕ)
    (d : F.Desc) :
    Game.withSetup (realView (F.dhExecution d)) (adversary n) =
      ProbComp.eval
        (ddhRealExperiment (F.order d) (F.generator d) (F.dhEavToDDH adversary n d)) := by
  simp only [Game.withSetup, realView, dhExecution, eval_ddhRealExperiment, dhEavToDDH,
    PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.bind_bind, PMF.pure_bind, smul_smul]

/-- At a fixed group and with the uniform group element as ideal key, the ideal eavesdropping
experiment on Diffie–Hellman is the random DDH experiment. -/
theorem withSetup_idealView_dhExecution (adversary : Eavesdropper F.DHTranscript F.DHKey) (n : ℕ)
    (d : F.Desc) :
    Game.withSetup (idealView F.dhIdealKey (F.dhExecution d)) (adversary n) =
      ProbComp.eval
        (ddhRandomExperiment (F.order d) (F.generator d) (F.dhEavToDDH adversary n d)) := by
  simp only [Game.withSetup, idealView, dhExecution, dhIdealKey, eval_ddhRandomExperiment,
    dhEavToDDH, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.bind_bind, PMF.pure_bind,
    PMF.bind_map, Function.comp_def]

/-- The real eavesdropping experiment on Diffie–Hellman is the real DDH experiment. -/
theorem realGame_dhKeyExchange (setup : ℕ → PMF F.Desc)
    (adversary : Eavesdropper F.DHTranscript F.DHKey) (n : ℕ) :
    (F.dhKeyExchange setup).realGame adversary n =
      F.ddhRealGame setup (F.dhEavToDDH adversary) n := by
  simp only [KeyExchange.realGame, dhKeyExchange, KeyExchange.withSetup_realView_bind,
    withSetup_realView_dhExecution, ddhRealGame, PMF.monad_bind_eq_bind]

/-- With the uniform group element as ideal key, the ideal eavesdropping experiment on
Diffie–Hellman is the random DDH experiment. -/
theorem idealGame_dhKeyExchange (setup : ℕ → PMF F.Desc)
    (adversary : Eavesdropper F.DHTranscript F.DHKey) (n : ℕ) :
    (F.dhKeyExchange setup).idealGame (fun _ => F.dhIdealKey) adversary n =
      F.ddhRandomGame setup (F.dhEavToDDH adversary) n := by
  simp only [KeyExchange.idealGame, dhKeyExchange, KeyExchange.withSetup_idealView_bind,
    withSetup_idealView_dhExecution, ddhRandomGame, PMF.monad_bind_eq_bind]

open scoped KeyExchange in
/-- The distinguisher `dhEavToDDH` is uniform strict PPT when the eavesdropper is. -/
theorem isPPT_dhEavToDDH {adversary : Eavesdropper F.DHTranscript F.DHKey}
    (hA : adversary.IsPPT F.encDHTranscript F.encDHKey) :
    (F.dhEavToDDH adversary).IsPPT :=
  IsPPTOn.preprocess hA (prepare := fun x : F.DDHInput =>
    (x.secParam, (⟨⟨x.groupParameters, x.leftPublic, x.rightPublic⟩, x.candidateShared⟩ :
      View F.DHTranscript F.DHKey)))
    (by fun_prop)

/-- **Diffie–Hellman key exchange is secure against eavesdroppers under DDH**
([KatzLindell2020], Theorem 11.3, p. 394): if the Decisional Diffie–Hellman assumption holds for
`setup`, then no uniform strict PPT eavesdropper distinguishes the transcript and Alice's key from
the transcript and a uniform element of the same group. -/
theorem DDH.dhKeyExchange_eavSecure {F : PrimeOrderGroupFamily} {setup : ℕ → PMF F.Desc}
    (hDDH : F.DDH setup) :
    (F.dhKeyExchange setup).EavSecure F.encDHTranscript F.encDHKey fun _ => F.dhIdealKey := by
  intro adversary hA
  simpa only [realGame_dhKeyExchange, idealGame_dhKeyExchange] using
    hDDH _ (F.isPPT_dhEavToDDH hA)

/-! ### The man-in-the-middle attack -/

/-- The outcome of the man-in-the-middle attack of [KatzLindell2020], Exercise 11.3 (p. 399):
the view of Alice and of Bob, each made of the transcript that party sees and the key it outputs,
and the keys the adversary computes for its sessions with each of them. -/
structure DHMitmOutcome where
  /-- Alice's view: the transcript `(d, hA, hB')` with the substituted share `hB'`, and her key. -/
  aliceView : View F.DHTranscript F.DHKey
  /-- Bob's view: the transcript `(d, hA', hB)` with the substituted share `hA'`, and his key. -/
  bobView : View F.DHTranscript F.DHKey
  /-- The key the adversary computes for its session with Alice. -/
  adversaryAliceKey : F.DHKey aliceView.transcript
  /-- The key the adversary computes for its session with Bob. -/
  adversaryBobKey : F.DHKey bobView.transcript

/-- The man-in-the-middle attack on Diffie–Hellman in the group `d` ([KatzLindell2020],
Exercise 11.3, p. 399). Alice and Bob run Construction 11.2 honestly with exponents `x` and `y`.
The adversary draws its own exponents `x'` and `y'`, delivers `hB' = y' • g` to Alice in place of
`hB` and `hA' = x' • g` to Bob in place of `hA`, and computes `y' • hA` and `x' • hB`. Over a setup
law, the attack draws `d` first. -/
@[expose]
noncomputable def dhMitmExecution (d : F.Desc) : PMF F.DHMitmOutcome := do
  let x ← PMF.uniformOfFintype (ZMod (F.order d))
  let y ← PMF.uniformOfFintype (ZMod (F.order d))
  let x' ← PMF.uniformOfFintype (ZMod (F.order d))
  let y' ← PMF.uniformOfFintype (ZMod (F.order d))
  let hA := x • F.generator d
  let hB := y • F.generator d
  let hA' := x' • F.generator d
  let hB' := y' • F.generator d
  return {
    aliceView := ⟨⟨d, hA, hB'⟩, x • hB'⟩
    bobView := ⟨⟨d, hA', hB⟩, y • hA'⟩
    adversaryAliceKey := y' • hA
    adversaryBobKey := x' • hB }

/-- In the man-in-the-middle attack the adversary knows the key Alice outputs and the key Bob
outputs. -/
theorem dhMitmExecution_keys (d : F.Desc) :
    ∀ outcome ∈ (F.dhMitmExecution d).support,
      outcome.adversaryAliceKey = outcome.aliceView.key ∧
        outcome.adversaryBobKey = outcome.bobView.key := by
  intro outcome h
  simp only [dhMitmExecution, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
    PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at h
  obtain ⟨x, -, y, -, x', -, y', -, rfl⟩ := h
  exact ⟨smul_comm _ _ _, smul_comm _ _ _⟩

/-- Alice cannot detect the attack: her view has exactly the law of the eavesdropper's view of an
honest Diffie–Hellman execution. -/
theorem map_aliceView_dhMitmExecution (d : F.Desc) :
    (F.dhMitmExecution d).map DHMitmOutcome.aliceView = realView (F.dhExecution d) := by
  simp only [dhMitmExecution, realView, dhExecution, PMF.monad_bind_eq_bind,
    PMF.monad_pure_eq_pure, PMF.map_bind, PMF.pure_map, PMF.bind_const, PMF.bind_bind,
    PMF.pure_bind]

/-- Bob cannot detect the attack: his view has exactly the law of the eavesdropper's view of an
honest Diffie–Hellman execution. -/
theorem map_bobView_dhMitmExecution (d : F.Desc) :
    (F.dhMitmExecution d).map DHMitmOutcome.bobView = realView (F.dhExecution d) := by
  simp only [dhMitmExecution, realView, dhExecution, PMF.monad_bind_eq_bind,
    PMF.monad_pure_eq_pure, PMF.map_bind, PMF.pure_map, PMF.bind_const, PMF.bind_bind,
    PMF.pure_bind]
  refine (PMF.bind_comm _ _ _).trans ?_
  refine congrArg (PMF.bind _) (funext fun x => congrArg (PMF.bind _) (funext fun y => ?_))
  rw [smul_comm y x]

end PrimeOrderGroupFamily

/-! ### A protocol built from XOR masks -/

namespace KeyExchange

/-- A transcript of the protocol of [KatzLindell2020], Exercise 11.4: three bit words. -/
structure XorTranscript where
  /-- Alice's first message `s = k ⊕ r`. -/
  aliceFirst : List Bool
  /-- Bob's reply `u = s ⊕ t`. -/
  bobReply : List Bool
  /-- Alice's second message `w = u ⊕ r`. -/
  aliceSecond : List Bool

/-- The encoding of an XOR transcript: its three words, each framed except the last
(`encXorTranscript_apply`). -/
enc_structure encXorTranscript : XorTranscript where
  aliceFirst : encBits, bobReply : encBits, aliceSecond : encBits

/-- The XOR `w ⊕ (s ⊕ u)` of the three words of an XOR transcript. -/
@[expose]
def XorTranscript.xorAll (transcript : XorTranscript) : List Bool :=
  List.zipWith Bool.xor transcript.aliceSecond
    (List.zipWith Bool.xor transcript.aliceFirst transcript.bobReply)

/-- The protocol of [KatzLindell2020], Exercise 11.4 (p. 400). Alice draws uniform `n`-bit words
`k` and `r` and sends `s = k ⊕ r`; Bob draws a uniform `n`-bit word `t` and sends `u = s ⊕ t`;
Alice sends `w = u ⊕ r`. Alice outputs `k` and Bob outputs `w ⊕ t`. -/
@[expose]
noncomputable def xorKeyExchange : KeyExchange XorTranscript fun _ => List Bool where
  execute n := do
    let k ← BitString.uniformList n
    let r ← BitString.uniformList n
    let t ← BitString.uniformList n
    let s := List.zipWith Bool.xor k r
    let u := List.zipWith Bool.xor s t
    let w := List.zipWith Bool.xor u r
    return { transcript := ⟨s, u, w⟩, aliceKey := k, bobKey := List.zipWith Bool.xor w t }

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
theorem mem_support_xorKeyExchange {n : ℕ} {outcome : Outcome XorTranscript fun _ => List Bool}
    (h : outcome ∈ (xorKeyExchange.execute n).support) :
    ∃ k r t : List Bool, k.length = n ∧ r.length = n ∧ t.length = n ∧
      outcome = {
        transcript := ⟨List.zipWith Bool.xor k r,
          List.zipWith Bool.xor (List.zipWith Bool.xor k r) t,
          List.zipWith Bool.xor (List.zipWith Bool.xor (List.zipWith Bool.xor k r) t) r⟩
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
def xorEavesdropper : Eavesdropper XorTranscript fun _ => List Bool :=
  fun _ view => return decide (view.key = view.transcript.xorAll)

/-- On the real key the eavesdropper always accepts. -/
theorem realGame_xorEavesdropper (n : ℕ) :
    xorKeyExchange.realGame xorEavesdropper n = PMF.pure true := by
  simp only [realGame, Game.withSetup, realView, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
    PMF.bind_bind, PMF.pure_bind]
  rw [← PMF.bind_const (xorKeyExchange.execute n) (PMF.pure true)]
  refine PMF.bind_congr_on_support _ _ _ fun outcome h => ?_
  obtain ⟨k, r, t, hk, hr, ht, rfl⟩ := mem_support_xorKeyExchange h
  simp only [xorEavesdropper, XorTranscript.xorAll, ProbComp.eval_pure,
    (xor_identities k r t (hr.trans hk.symm) (ht.trans hk.symm)).2, decide_true]

/-- On a uniform `n`-bit key the eavesdropper accepts with probability at most `1 / 2 ^ n`. -/
theorem idealGame_xorEavesdropper_true_le (n : ℕ) :
    xorKeyExchange.idealGame (fun n _ => BitString.uniformList n) xorEavesdropper n true ≤
      1 / 2 ^ n := by
  simp only [idealGame, Game.withSetup, idealView, xorEavesdropper, ProbComp.eval_pure,
    PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.bind_bind, PMF.pure_bind, PMF.bind_apply,
    PMF.pure_apply, eq_comm (a := true), decide_eq_true_eq, mul_ite, mul_one, mul_zero,
    tsum_ite_eq]
  calc ∑' outcome, xorKeyExchange.execute n outcome *
        BitString.uniformList n outcome.transcript.xorAll
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

/-- The XOR eavesdropper is uniform strict PPT. -/
theorem isPPT_xorEavesdropper : xorEavesdropper.IsPPT encXorTranscript fun _ => encBits := by
  have hkey : ComputableInPolyTime (fun input : ℕ × View XorTranscript (fun _ => List Bool) =>
      input.2.key) (encEavInput encXorTranscript fun _ => encBits) encBits :=
    encView_key_polyTime encXorTranscript (fun _ => encBits) (.snd _ _)
  have hrec : ComputableInPolyTime (fun input : ℕ × View XorTranscript (fun _ => List Bool) =>
      input.2.transcript.xorAll) (encEavInput encXorTranscript fun _ => encBits) encBits := by
    unfold XorTranscript.xorAll
    fun_prop
  exact (hkey.decide_eq' hrec).isPPTOn

/-- **The XOR protocol is not secure against eavesdroppers** ([KatzLindell2020], Exercise 11.4,
p. 400): the XOR of the three transcript words is the key, so the eavesdropper
`xorEavesdropper` has advantage at least `1 / 2` at every parameter `n ≥ 1`. -/
theorem not_eavSecureBits_xorKeyExchange : ¬ xorKeyExchange.EavSecureBits encXorTranscript := by
  intro h
  refine not_negligible_const (c := (1 / 2 : ℝ≥0)) (by norm_num) ?_
  exact negligible_of_le ((h xorEavesdropper isPPT_xorEavesdropper).shift 1)
    fun n => half_le_advantage_xorEavesdropper n.succ_ne_zero

end KeyExchange

end Cslib.Crypto
