/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.MPC.DDHOT
public import CslibFrontier.Crypto.Computational.DiffieHellman
public import CslibFrontier.Crypto.Computational.ElGamal
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import CslibFrontier.Computability.Probabilistic.Sampling
import CslibFrontier.Crypto.Computational.DiffieHellman.SampleExp
import CslibFrontier.Crypto.Game.FourHop
import CslibFrontier.Crypto.Negligible.Dyadic
import CslibFrontier.Tactic.PPT
import CslibFrontier.Tactic.PolyTime

/-!
# Asymptotic Security and Strict-PPT Realization of DDH-OT over Prime-Order Group Families

This module instantiates the finite two-party oblivious transfer protocol
`Cslib.Crypto.Protocols.MPC.ddhOTProtocol` over any `Cslib.Crypto.PrimeOrderGroupFamily`,
constructs strict-PPT (`IsPPTOn`) word-level realizations, simulators, and reductions using
`PrimeOrderGroupFamily.sampleExp`, and lifts the concrete finite theorems of
`CslibFrontier.Crypto.Protocols.MPC.DDHOT` to asymptotic semi-honest security under
`PrimeOrderGroupFamily.DDH`.

## Main definitions

* `Cslib.Crypto.Protocols.MPC.encDDHOTSenderView`,
  `Cslib.Crypto.Protocols.MPC.encDDHOTReceiverView`: injective bit-string encodings of `ddhOT`
  party views over `F.Carrier desc`.
* `Cslib.Crypto.Protocols.MPC.ddhOTRealWordWithDesc`,
  `Cslib.Crypto.Protocols.MPC.ddhOTRealWordRun`: uniform strict-PPT word-level execution of DDH-OT.
* `Cslib.Crypto.Protocols.MPC.ddhOTSenderSimWord`,
  `Cslib.Crypto.Protocols.MPC.ddhOTReceiverSimWord`: uniform strict-PPT word-level simulators for
  corrupted sender (`{0}`) and corrupted receiver (`{1}`).
* `Cslib.Crypto.Protocols.MPC.ddhOTWordReduction`: uniform strict-PPT reduction from word-level or
  typed DDH-OT receiver indistinguishability to `PrimeOrderGroupFamily.DDH`.

## Main results

* `Cslib.Crypto.Protocols.MPC.isPPTOn_ddhOTRealWordWithDesc`,
  `Cslib.Crypto.Protocols.MPC.isPPTOn_ddhOTRealWordRun`,
  `Cslib.Crypto.Protocols.MPC.isPPTOn_ddhOTSenderSimWord`,
  `Cslib.Crypto.Protocols.MPC.isPPTOn_ddhOTReceiverSimWord`,
  `Cslib.Crypto.Protocols.MPC.isPPTOn_ddhOTWordReduction`: strict-PPT certificates.
* `Cslib.Crypto.Protocols.MPC.ddhOT_asymptotic_sender_private`,
  `Cslib.Crypto.Protocols.MPC.ddhOTWord_asymptotic_sender_private`: perfect typed sender privacy and
  `12 / 2 ^ n` statistical word-level sender privacy.
* `Cslib.Crypto.Protocols.MPC.ddhOT_asymptotic_receiver_private`,
  `Cslib.Crypto.Protocols.MPC.ddhOTWord_asymptotic_receiver_private`: asymptotic semi-honest privacy
  against a corrupted receiver under `PrimeOrderGroupFamily.DDH`.

## References

* [M. Naor, B. Pinkas, *Efficient Oblivious Transfer Protocols*][NaorPinkas2001], Section 3.
* [O. Goldreich, *Foundations of Cryptography, Volume 2*][Goldreich2004], Section 7.2.2.1.
-/

public section

namespace Cslib.Crypto.Protocols.MPC

open Cslib.Crypto Cslib.Probability Cslib.ProbComp Turing.MultiTapeTM
open scoped NNReal

variable (F : PrimeOrderGroupFamily)

/-! ### Prime-order group bridges -/

@[instance_reducible]
private noncomputable def carrierFintype (desc : F.Desc) : Fintype (F.Carrier desc) :=
  haveI : Finite (F.Carrier desc) :=
    Nat.finite_of_card_ne_zero (by rw [F.card_carrier desc]; exact (F.prime_order desc).ne_zero)
  Fintype.ofFinite (F.Carrier desc)

private theorem order_smul_eq_zero (desc : F.Desc) (y : F.Carrier desc) :
    F.order desc • y = 0 := by
  rw [← Nat.cast_smul_eq_nsmul (ZMod (F.order desc))]
  simp

private theorem smul_natCast_eq_nsmul (desc : F.Desc) (a : ℕ) (x : F.Carrier desc) :
    ((a : ZMod (F.order desc)).val) • x = (a : ZMod (F.order desc)) • x := by
  conv_rhs => rw [← ZMod.natCast_zmod_val (a : ZMod (F.order desc))]
  exact (Nat.cast_smul_eq_nsmul (ZMod (F.order desc)) _ x).symm

private theorem smul_generator_val_surjective (desc : F.Desc) (y : F.Carrier desc) :
    ∃ k : ZMod (F.order desc), k.val • F.generator desc = y := by
  obtain ⟨k, hk⟩ := F.smul_generator_surjective desc y
  refine ⟨k, ?_⟩
  rw [← Nat.cast_smul_eq_nsmul (ZMod (F.order desc)), ZMod.natCast_zmod_val]
  exact hk

private theorem uniform_zmod_map_smul_generator (desc : F.Desc)
    [Fintype (F.Carrier desc)] :
    (PMF.uniformOfFintype (ZMod (F.order desc))).map (fun k => k.val • F.generator desc) =
      PMF.uniformOfFintype (F.Carrier desc) := by
  have : NeZero (F.order desc) := ⟨(F.prime_order desc).ne_zero⟩
  have hbij : Function.Bijective (fun k : ZMod (F.order desc) => k.val • F.generator desc) := by
    have heq : (fun k : ZMod (F.order desc) => k.val • F.generator desc) =
        (fun k : ZMod (F.order desc) => k • F.generator desc) := by
      funext k
      rw [← Nat.cast_smul_eq_nsmul (ZMod (F.order desc)), ZMod.natCast_zmod_val]
    rw [heq]
    exact F.smul_generator_bijective desc
  have hcard : Fintype.card (F.Carrier desc) = Fintype.card (ZMod (F.order desc)) := by
    rw [Fintype.card_eq_nat_card, F.card_carrier desc, ZMod.card]
  ext y
  rw [PMF.map_apply, PMF.uniformOfFintype_apply, hcard]
  obtain ⟨k, rfl⟩ := hbij.surjective y
  rw [tsum_eq_single k (fun k' hk' => by simp [hbij.injective.ne hk'.symm])]
  simp [PMF.uniformOfFintype_apply]

/-! ### Multi-draw `sampleExp` hybrid bounds -/

private theorem advantage_bind_sampleExp_3_le (n : ℕ) (desc : F.Desc)
    (k : ZMod (F.order desc) → ZMod (F.order desc) → ZMod (F.order desc) → Game) :
    Game.advantage
      ((ProbComp.eval (F.sampleExp n desc)).bind fun a =>
        (ProbComp.eval (F.sampleExp n desc)).bind fun b =>
          (ProbComp.eval (F.sampleExp n desc)).bind fun c =>
            k (a : ZMod (F.order desc)) (b : ZMod (F.order desc)) (c : ZMod (F.order desc)))
      ((PMF.uniformOfFintype (ZMod (F.order desc))).bind fun α =>
        (PMF.uniformOfFintype (ZMod (F.order desc))).bind fun β =>
          (PMF.uniformOfFintype (ZMod (F.order desc))).bind fun γ => k α β γ) ≤
      3 / 2 ^ n := by
  have h1 := F.advantage_bind_sampleExp_le n desc (fun α =>
    (ProbComp.eval (F.sampleExp n desc)).bind fun b =>
      (ProbComp.eval (F.sampleExp n desc)).bind fun c =>
        k α (b : ZMod (F.order desc)) (c : ZMod (F.order desc)))
  have h2 := Game.advantage_bind_le_nnreal (PMF.uniformOfFintype (ZMod (F.order desc))) _ _
    fun α => F.advantage_bind_sampleExp_pair_le n desc (k α)
  refine (Game.advantage_triangle _ _ _).trans ((add_le_add h1 h2).trans ?_)
  rw [← add_div, show (1 : ℝ≥0) + 2 = 3 by norm_num]

private theorem advantage_bind_sampleExp_6_le (n : ℕ) (desc : F.Desc)
    (k : ZMod (F.order desc) → ZMod (F.order desc) → ZMod (F.order desc) →
      ZMod (F.order desc) → ZMod (F.order desc) → ZMod (F.order desc) → Game) :
    Game.advantage
      ((ProbComp.eval (F.sampleExp n desc)).bind fun a =>
        (ProbComp.eval (F.sampleExp n desc)).bind fun b =>
          (ProbComp.eval (F.sampleExp n desc)).bind fun c =>
            (ProbComp.eval (F.sampleExp n desc)).bind fun d =>
              (ProbComp.eval (F.sampleExp n desc)).bind fun e =>
                (ProbComp.eval (F.sampleExp n desc)).bind fun f =>
                  k (a : ZMod (F.order desc)) (b : ZMod (F.order desc))
                    (c : ZMod (F.order desc)) (d : ZMod (F.order desc))
                    (e : ZMod (F.order desc)) (f : ZMod (F.order desc)))
      ((PMF.uniformOfFintype (ZMod (F.order desc))).bind fun α =>
        (PMF.uniformOfFintype (ZMod (F.order desc))).bind fun β =>
          (PMF.uniformOfFintype (ZMod (F.order desc))).bind fun γ =>
            (PMF.uniformOfFintype (ZMod (F.order desc))).bind fun δ =>
              (PMF.uniformOfFintype (ZMod (F.order desc))).bind fun ε =>
                (PMF.uniformOfFintype (ZMod (F.order desc))).bind fun ζ => k α β γ δ ε ζ) ≤
      6 / 2 ^ n := by
  let mid : Game :=
    (PMF.uniformOfFintype (ZMod (F.order desc))).bind fun α =>
      (PMF.uniformOfFintype (ZMod (F.order desc))).bind fun β =>
        (PMF.uniformOfFintype (ZMod (F.order desc))).bind fun γ =>
          (ProbComp.eval (F.sampleExp n desc)).bind fun d =>
            (ProbComp.eval (F.sampleExp n desc)).bind fun e =>
              (ProbComp.eval (F.sampleExp n desc)).bind fun f =>
                k α β γ (d : ZMod (F.order desc)) (e : ZMod (F.order desc))
                  (f : ZMod (F.order desc))
  have h1 := advantage_bind_sampleExp_3_le F n desc (fun α β γ =>
    (ProbComp.eval (F.sampleExp n desc)).bind fun d =>
      (ProbComp.eval (F.sampleExp n desc)).bind fun e =>
        (ProbComp.eval (F.sampleExp n desc)).bind fun f =>
          k α β γ (d : ZMod (F.order desc)) (e : ZMod (F.order desc)) (f : ZMod (F.order desc)))
  have h2 : Game.advantage mid _ ≤ 3 / 2 ^ n :=
    Game.advantage_bind_le_nnreal _ _ _ fun α =>
      Game.advantage_bind_le_nnreal _ _ _ fun β =>
        Game.advantage_bind_le_nnreal _ _ _ fun γ =>
          advantage_bind_sampleExp_3_le F n desc (k α β γ)
  refine (Game.advantage_triangle _ mid _).trans ((add_le_add h1 h2).trans ?_)
  rw [← add_div, show (3 : ℝ≥0) + 3 = 6 by norm_num]

private noncomputable def bind6 {α β : Type} (p : PMF α)
    (f : α → α → α → α → α → α → PMF β) : PMF β :=
  p.bind fun x₀ => p.bind fun x₁ => p.bind fun x₂ =>
    p.bind fun x₃ => p.bind fun x₄ => p.bind fun x₅ => f x₀ x₁ x₂ x₃ x₄ x₅

private theorem bind6_eq {α β : Type} (p : PMF α)
    {f g : α → α → α → α → α → α → PMF β}
    (h : ∀ x₀ x₁ x₂ x₃ x₄ x₅, f x₀ x₁ x₂ x₃ x₄ x₅ = g x₀ x₁ x₂ x₃ x₄ x₅) :
    bind6 p f = bind6 p g := by
  have hfg : f = g := by funext x₀ x₁ x₂ x₃ x₄ x₅; exact h x₀ x₁ x₂ x₃ x₄ x₅
  rw [hfg]

private theorem advantage_bind6_sampleExp_le (n : ℕ) (desc : F.Desc)
    (k : ZMod (F.order desc) → ZMod (F.order desc) → ZMod (F.order desc) →
      ZMod (F.order desc) → ZMod (F.order desc) → ZMod (F.order desc) → Game) :
    Game.advantage
      (bind6 (ProbComp.eval (F.sampleExp n desc))
        (fun a b c d e f => k a b c d e f))
      (bind6 (PMF.uniformOfFintype (ZMod (F.order desc))) k) ≤ 6 / 2 ^ n :=
  advantage_bind_sampleExp_6_le F n desc k

/-! ### Bit-string encodings for inputs, views, and outputs -/

/-- Bit-string embedding of word-level DDH-OT inputs `((m₀, m₁), σ)`. -/
@[expose] def encDDHOTWordPair : ((List Bool × List Bool) × Bool) ↪ List Bool :=
  encPair (encPair encBits encBits) encBool

/-- Bit-string embedding of `(n, ((m₀, m₁), σ))`. -/
@[expose] def encDDHOTWordInput : (ℕ × (List Bool × List Bool) × Bool) ↪ List Bool :=
  encPair encUnary encDDHOTWordPair

/-- Bit-string embedding of `(n, desc, ((m₀, m₁), σ))`. -/
@[expose] def encDDHOTWordWithDesc : (ℕ × F.Desc × (List Bool × List Bool) × Bool) ↪ List Bool :=
  encPair encUnary (encPair F.encDesc encDDHOTWordPair)

/-- Raw word-level encoding of a DDH-OT sender view `((m₀, m₁), (a, r₀, s₀, r₁, s₁), (v₀, v₁))`. -/
@[expose] def encDDHOTSenderViewRaw :
    ((List Bool × List Bool) × (ℕ × ℕ × ℕ × ℕ × ℕ) × (List Bool × List Bool)) ↪ List Bool :=
  encPair (encPair encBits encBits)
    (encPair (encPair encNat (encPair encNat (encPair encNat (encPair encNat encNat))))
      (encPair encBits encBits))

/-- Raw word-level encoding of a DDH-OT receiver view `(σ, b, u, (ct₀, ct₁))`. -/
@[expose] def encDDHOTReceiverViewRaw :
    (Bool × ℕ × List Bool × ((List Bool × List Bool) × (List Bool × List Bool))) ↪ List Bool :=
  encPair encBool
    (encPair encNat
      (encPair encBits (encPair (encPair encBits encBits) (encPair encBits encBits))))

/-- Bit-string embedding of `(senderView_w, receiverView_w, out_w)`. -/
@[expose] def encDDHOTRunOut : (List Bool × List Bool × List Bool) ↪ List Bool :=
  encPair encBits (encPair encBits encBits)

/-- Bit-string embedding `(1ⁿ, w₁, w₂)` for a security parameter in unary paired with two
bit-string words (used for sender-simulator inputs and distinguisher inputs). -/
abbrev encDDHOTWordPairInput : ℕ × List Bool × List Bool ↪ List Bool :=
  encPair encUnary (encPair encBits encBits)

/-- Output word component of a DDH-OT word-level execution triple `(sv, rv, ov)`. -/
abbrev ddhOTRunOut (r : List Bool × List Bool × List Bool) : List Bool :=
  r.2.2

/-- Receiver view word component of a DDH-OT word-level execution triple `(sv, rv, ov)`. -/
abbrev ddhOTRunReceiverView (r : List Bool × List Bool × List Bool) : List Bool :=
  r.2.1

/-- Encode a typed DDH-OT input tuple `(x 0, x 1)` into `((m₀_w, m₁_w), σ)`. -/
@[expose] def encodeDDHOTInputWord (desc : F.Desc)
    (x : (i : Fin 2) → OTIn (F.Carrier desc) i) : (List Bool × List Bool) × Bool :=
  ((F.encode desc (x 0).1, F.encode desc (x 0).2), x 1)

/-- Encode a typed DDH-OT sender view into a `List Bool` via `encDDHOTSenderViewRaw`. -/
@[expose] def encodeDDHOTSenderViewWord (desc : F.Desc)
    (v : PartyView (OTIn (F.Carrier desc)) (DDHOTCoins (F.order desc))
      (ddhOTSchedule (F.Carrier desc)) 0) : List Bool :=
  let (m₀, m₁) := v.input
  let (a, r₀, s₀, r₁, s₁) := v.coins
  let (_, msg, _) := v.received
  let (e₀, e₁) := msg rfl
  encDDHOTSenderViewRaw
    ((F.encode desc m₀, F.encode desc m₁),
     (a.val, r₀.val, s₀.val, r₁.val, s₁.val),
     (F.encode desc e₀, F.encode desc e₁))

theorem encodeDDHOTSenderViewWord_injective (desc : F.Desc) :
    Function.Injective (encodeDDHOTSenderViewWord F desc) := by
  intro v w h
  have hr := encDDHOTSenderViewRaw.injective h
  rcases v with ⟨vin, vcoins, vrec⟩
  rcases w with ⟨win, wcoins, wrec⟩
  have hin : vin = win := Prod.ext
    (F.encode_injective desc (congrArg (fun p => p.1.1) hr))
    (F.encode_injective desc (congrArg (fun p => p.1.2) hr))
  have hcoins : vcoins = wcoins := Prod.ext
    (ZMod.val_injective _ (congrArg (fun p => p.2.1.1) hr))
    (Prod.ext
      (ZMod.val_injective _ (congrArg (fun p => p.2.1.2.1) hr))
      (Prod.ext
        (ZMod.val_injective _ (congrArg (fun p => p.2.1.2.2.1) hr))
        (Prod.ext
          (ZMod.val_injective _ (congrArg (fun p => p.2.1.2.2.2.1) hr))
          (ZMod.val_injective _ (congrArg (fun p => p.2.1.2.2.2.2) hr)))))
  have hrec2 : vrec.2.1 = wrec.2.1 := funext fun _ => Prod.ext
    (F.encode_injective desc (congrArg (fun p => p.2.2.1) hr))
    (F.encode_injective desc (congrArg (fun p => p.2.2.2) hr))
  exact PartyView.ext hin hcoins
    (Prod.ext (Round.received_message_eq_of_ne (by decide) _ _)
      (Prod.ext hrec2 (Prod.ext (Round.received_message_eq_of_ne (by decide) _ _) rfl)))

/-- Injective bit-string encoding of a DDH-OT sender view over `F.Carrier desc`. -/
@[expose] def encDDHOTSenderView (desc : F.Desc) :
    PartyView (OTIn (F.Carrier desc)) (DDHOTCoins (F.order desc))
      (ddhOTSchedule (F.Carrier desc)) 0 ↪ List Bool :=
  ⟨encodeDDHOTSenderViewWord F desc, encodeDDHOTSenderViewWord_injective F desc⟩

/-- Encode a typed DDH-OT receiver view into a `List Bool` via `encDDHOTReceiverViewRaw`. -/
@[expose] def encodeDDHOTReceiverViewWord (desc : F.Desc)
    (v : PartyView (OTIn (F.Carrier desc)) (DDHOTCoins (F.order desc))
      (ddhOTSchedule (F.Carrier desc)) 1) : List Bool :=
  let (uMsg, _, repMsg, _) := v.received
  let ((ct₀₀, ct₀₁), (ct₁₀, ct₁₁)) := repMsg rfl
  encDDHOTReceiverViewRaw
    (v.input, v.coins.val, F.encode desc (uMsg rfl),
     ((F.encode desc ct₀₀, F.encode desc ct₀₁),
      (F.encode desc ct₁₀, F.encode desc ct₁₁)))

theorem encodeDDHOTReceiverViewWord_injective (desc : F.Desc) :
    Function.Injective (encodeDDHOTReceiverViewWord F desc) := by
  intro v w h
  have hr := encDDHOTReceiverViewRaw.injective h
  rcases v with ⟨vin, vcoins, vrec⟩
  rcases w with ⟨win, wcoins, wrec⟩
  have hin : vin = win := congrArg (fun p => p.1) hr
  have hcoins : vcoins = wcoins := ZMod.val_injective _ (congrArg (fun p => p.2.1) hr)
  have hrec1 : vrec.1 = wrec.1 := funext fun _ =>
    F.encode_injective desc (congrArg (fun p => p.2.2.1) hr)
  have hrec3 : vrec.2.2.1 = wrec.2.2.1 := funext fun _ => Prod.ext
    (Prod.ext
      (F.encode_injective desc (congrArg (fun p => p.2.2.2.1.1) hr))
      (F.encode_injective desc (congrArg (fun p => p.2.2.2.1.2) hr)))
    (Prod.ext
      (F.encode_injective desc (congrArg (fun p => p.2.2.2.2.1) hr))
      (F.encode_injective desc (congrArg (fun p => p.2.2.2.2.2) hr)))
  exact PartyView.ext hin hcoins
    (Prod.ext hrec1
      (Prod.ext (Round.received_message_eq_of_ne (by decide) _ _) (Prod.ext hrec3 rfl)))

/-- Injective bit-string encoding of a DDH-OT receiver view over `F.Carrier desc`. -/
@[expose] def encDDHOTReceiverView (desc : F.Desc) :
    PartyView (OTIn (F.Carrier desc)) (DDHOTCoins (F.order desc))
      (ddhOTSchedule (F.Carrier desc)) 1 ↪ List Bool :=
  ⟨encodeDDHOTReceiverViewWord F desc, encodeDDHOTReceiverViewWord_injective F desc⟩

/-- Encode DDH-OT outputs `((), y 1)` by encoding the receiver's group output. -/
@[expose] def encodeDDHOTOutputsWord (desc : F.Desc)
    (y : (i : Fin 2) → OTOut (F.Carrier desc) i) : List Bool :=
  F.encode desc (y 1)

theorem encodeDDHOTOutputsWord_injective (desc : F.Desc) :
    Function.Injective (encodeDDHOTOutputsWord F desc) := by
  intro y z h
  funext i
  fin_cases i
  · rfl
  · exact F.encode_injective desc h

/-- Pair representation `(encodeSenderView, encodeOutputs)` for corrupted sender (`{0}`). -/
@[expose] def encodeDDHOTSenderJointPair (desc : F.Desc)
    (r : ((i : ↥({0} : Finset (Fin 2))) → PartyView (OTIn (F.Carrier desc))
        (DDHOTCoins (F.order desc)) (ddhOTSchedule (F.Carrier desc)) ↑i) ×
      ((i : Fin 2) → OTOut (F.Carrier desc) i)) : List Bool × List Bool :=
  (encodeDDHOTSenderViewWord F desc (r.1 ⟨0, by decide⟩), encodeDDHOTOutputsWord F desc r.2)

/-- Pair representation `(encodeReceiverView, encodeOutputs)` for corrupted receiver (`{1}`). -/
@[expose] def encodeDDHOTReceiverJointPair (desc : F.Desc)
    (r : ((i : ↥({1} : Finset (Fin 2))) → PartyView (OTIn (F.Carrier desc))
        (DDHOTCoins (F.order desc)) (ddhOTSchedule (F.Carrier desc)) ↑i) ×
      ((i : Fin 2) → OTOut (F.Carrier desc) i)) : List Bool × List Bool :=
  (encodeDDHOTReceiverViewWord F desc (r.1 ⟨1, by decide⟩), encodeDDHOTOutputsWord F desc r.2)

/-! ### Word-level DDH-OT operations, runner, simulators, and reduction -/

/-- Word-level ElGamal-rerandomized branch encryption matching `ddhOTEncryptBranch`. -/
@[expose] def ddhOTEncryptBranchWord (desc : F.Desc) (u_w w_w m_w : List Bool)
    (r s a : ℕ) : List Bool × List Bool :=
  (F.add (desc, F.encodeElGamalPublicKey (desc, r), F.smul (desc, s, u_w)),
   F.add (desc,
     F.add (desc, F.smul (desc, r, w_w), F.smul (desc, s, F.smul (desc, a, w_w))),
     m_w))

private theorem ddhOTEncryptBranchWord_encode (desc : F.Desc)
    (u w m : F.Carrier desc) (r s a : ℕ) :
    ddhOTEncryptBranchWord F desc (F.encode desc u) (F.encode desc w) (F.encode desc m) r s a =
      let ct := ddhOTEncryptBranch (F.generator desc) u w m
        (r : ZMod (F.order desc)) (s : ZMod (F.order desc)) (a : ZMod (F.order desc))
      (F.encode desc ct.1, F.encode desc ct.2) := by
  simp only [ddhOTEncryptBranchWord, ddhOTEncryptBranch, F.encodeElGamalPublicKey_eq_encode,
    F.smul_encode, F.add_encode, smul_natCast_eq_nsmul]

private theorem computableInPolyTime_ddhOTEncryptBranchWord :
    ComputableInPolyTime
      (fun p : F.Desc × List Bool × List Bool × List Bool × ℕ × ℕ × ℕ =>
        ddhOTEncryptBranchWord F p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2.1
          p.2.2.2.2.2.2)
      (encPair F.encDesc (encPair encBits (encPair encBits (encPair encBits
        (encPair encNat (encPair encNat encNat))))))
      (encPair encBits encBits) := by
  let eArgs := encPair encBits (encPair encBits (encPair encBits
    (encPair encNat (encPair encNat encNat))))
  let eIn := encPair F.encDesc eArgs
  have hd : ComputableInPolyTime (fun p : F.Desc × _ => p.1) eIn F.encDesc := .fst' .id'
  have hu : ComputableInPolyTime (fun p : F.Desc × _ => p.2.1) eIn encBits := by fun_prop
  have hw : ComputableInPolyTime (fun p : F.Desc × _ => p.2.2.1) eIn encBits := by fun_prop
  have hm : ComputableInPolyTime (fun p : F.Desc × _ => p.2.2.2.1) eIn encBits := by fun_prop
  have hr : ComputableInPolyTime (fun p : F.Desc × _ => p.2.2.2.2.1) eIn encNat := by fun_prop
  have hs : ComputableInPolyTime (fun p : F.Desc × _ => p.2.2.2.2.2.1) eIn encNat := by fun_prop
  have ha : ComputableInPolyTime (fun p : F.Desc × _ => p.2.2.2.2.2.2) eIn encNat := by fun_prop
  have hr_g := F.computableInPolyTime_encodeElGamalPublicKey.comp' (hd.prod hr)
  have hs_u := F.computableInPolyTime_smul.comp' (hd.prod (hs.prod hu))
  have hc1 := F.computableInPolyTime_add.comp' (hd.prod (hr_g.prod hs_u))
  have hr_w := F.computableInPolyTime_smul.comp' (hd.prod (hr.prod hw))
  have ha_w := F.computableInPolyTime_smul.comp' (hd.prod (ha.prod hw))
  have hs_aw := F.computableInPolyTime_smul.comp' (hd.prod (hs.prod ha_w))
  have hsum1 := F.computableInPolyTime_add.comp' (hd.prod (hr_w.prod hs_aw))
  have hc2 := F.computableInPolyTime_add.comp' (hd.prod (hsum1.prod hm))
  exact hc1.prod hc2

/-- Word-level execution of DDH-OT on `(n, desc, ((m₀_w, m₁_w), σ))`, returning
`(senderView_w, receiverView_w, out_w)`. -/
noncomputable def ddhOTRealWordWithDesc
    (inp : ℕ × F.Desc × (List Bool × List Bool) × Bool) :
    ProbComp (List Bool × List Bool × List Bool) :=
  let (n, desc, (m₀_w, m₁_w), σ) := inp
  do
    let a ← F.sampleExp n desc
    let r₀ ← F.sampleExp n desc
    let s₀ ← F.sampleExp n desc
    let r₁ ← F.sampleExp n desc
    let s₁ ← F.sampleExp n desc
    let b ← F.sampleExp n desc
    let q := F.order desc
    let u_w := F.encodeElGamalPublicKey (desc, a)
    let v_w := F.encodeElGamalPublicKey (desc, b)
    let u_sub_v_w := F.decodeElGamal (desc, 1, v_w, u_w)
    let w_w := if σ then (u_sub_v_w, v_w) else (v_w, u_sub_v_w)
    let ct₀ := ddhOTEncryptBranchWord F desc u_w w_w.1 m₀_w r₀ s₀ a
    let ct₁ := ddhOTEncryptBranchWord F desc u_w w_w.2 m₁_w r₁ s₁ a
    let senderView_w := encDDHOTSenderViewRaw
      ((m₀_w, m₁_w), (a % q, r₀ % q, s₀ % q, r₁ % q, s₁ % q), w_w)
    let receiverView_w := encDDHOTReceiverViewRaw (σ, b % q, u_w, (ct₀, ct₁))
    let out_w := if σ then m₁_w else m₀_w
    return (senderView_w, receiverView_w, out_w)

/-- Word-level execution of DDH-OT for group schedule `d : ℕ → F.Desc`. -/
noncomputable def ddhOTRealWordRun (d : ℕ → F.Desc)
    (inp : ℕ × (List Bool × List Bool) × Bool) :
    ProbComp (List Bool × List Bool × List Bool) :=
  ddhOTRealWordWithDesc F (inp.1, d inp.1, inp.2)

/-- Correctness on `ddhOTRealWordWithDesc`: every supported run outputs `F.encode desc (if σ
then m₁ else m₀)`, and the receiver's `F.decodeElGamal` decryption of its selected ciphertext
equals `F.encode desc (if σ then m₁ else m₀)`. -/
theorem ddhOTRealWordWithDesc_correctness (n : ℕ) (desc : F.Desc) (m₀ m₁ : F.Carrier desc)
    (σ : Bool) {res : List Bool × List Bool × List Bool}
    (hres : res ∈ (ProbComp.eval
      (ddhOTRealWordWithDesc F (n, desc, (F.encode desc m₀, F.encode desc m₁), σ))).support) :
    ddhOTRunOut res = F.encode desc (if σ then m₁ else m₀) := by
  simp only [ddhOTRealWordWithDesc, ProbComp.eval_bind, ProbComp.eval_pure,
    PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hres
  rcases hres with ⟨a, _, r₀, _, s₀, _, r₁, _, s₁, _, b, _, rfl⟩
  cases σ <;> rfl

private theorem isPPTOn_sampleExp_fn {P : Type} (eP : P ↪ List Bool)
    (n_fn : P → ℕ) (d_fn : P → F.Desc)
    (hn : ComputableInPolyTime n_fn eP encUnary)
    (hd : ComputableInPolyTime d_fn eP F.encDesc) :
    IsPPTOn eP encNat (fun p => F.sampleExp (n_fn p) (d_fn p)) :=
  F.isPPTOn_sampleExp hn hd

private theorem isPPTOn_bind3_sampleExp {P B : Type} (eP : P ↪ List Bool) (eB : B ↪ List Bool)
    (n_fn : P → ℕ) (d_fn : P → F.Desc)
    (hn : ComputableInPolyTime n_fn eP encUnary)
    (hd : ComputableInPolyTime d_fn eP F.encDesc)
    {k : ((P × ℕ) × ℕ) × ℕ → ProbComp B}
    (hk : IsPPTOn (encPair (encPair (encPair eP encNat) encNat) encNat) eB k)
    {prog : P → ProbComp B}
    (hprog : ∀ p, ProbComp.eval (prog p) = ProbComp.eval (do
      let x₀ ← F.sampleExp (n_fn p) (d_fn p)
      let x₁ ← F.sampleExp (n_fn p) (d_fn p)
      let x₂ ← F.sampleExp (n_fn p) (d_fn p)
      k (((p, x₀), x₁), x₂))) :
    IsPPTOn eP eB prog := by
  let e1 := encPair eP encNat
  let e2 := encPair e1 encNat
  have hs0 : IsPPTOn eP encNat (fun p => F.sampleExp (n_fn p) (d_fn p)) :=
    F.isPPTOn_sampleExp hn hd
  have hs1 : IsPPTOn e1 encNat (fun p => F.sampleExp (n_fn p.1) (d_fn p.1)) :=
    F.isPPTOn_sampleExp (hn.comp' (.fst' .id')) (hd.comp' (.fst' .id'))
  have hs2 : IsPPTOn e2 encNat (fun p => F.sampleExp (n_fn p.1.1) (d_fn p.1.1)) :=
    F.isPPTOn_sampleExp (hn.comp' (.fst' (.fst' .id'))) (hd.comp' (.fst' (.fst' .id')))
  have hres : IsPPTOn eP eB (fun p => do
      let x₀ ← F.sampleExp (n_fn p) (d_fn p)
      let x₁ ← F.sampleExp (n_fn p) (d_fn p)
      let x₂ ← F.sampleExp (n_fn p) (d_fn p)
      k (((p, x₀), x₁), x₂)) :=
    hs0.bind_with (hs1.bind_with (hs2.bind_with hk))
  exact hres.congr fun p => (hprog p).symm

private abbrev sample6Enc {A : Type} (eA : A ↪ List Bool) :=
  encPair (encPair (encPair (encPair (encPair (encPair
    (encPair encUnary (encPair F.encDesc eA)) encNat) encNat) encNat) encNat) encNat) encNat

private theorem isPPTOn_bind6_sampleExp {A B : Type} (eA : A ↪ List Bool) (eB : B ↪ List Bool)
    {f : ((((((ℕ × F.Desc × A) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ → B}
    (hf : ComputableInPolyTime f (sample6Enc F eA) eB)
    {prog : ℕ × F.Desc × A → ProbComp B}
    (hprog : ∀ inp, ProbComp.eval (prog inp) =
      ProbComp.eval (do
        let x₀ ← F.sampleExp inp.1 inp.2.1
        let x₁ ← F.sampleExp inp.1 inp.2.1
        let x₂ ← F.sampleExp inp.1 inp.2.1
        let x₃ ← F.sampleExp inp.1 inp.2.1
        let x₄ ← F.sampleExp inp.1 inp.2.1
        let x₅ ← F.sampleExp inp.1 inp.2.1
        return f ((((((inp, x₀), x₁), x₂), x₃), x₄), x₅))) :
    IsPPTOn (encPair encUnary (encPair F.encDesc eA)) eB prog := by
  let e0 := encPair encUnary (encPair F.encDesc eA)
  let e3 := encPair (encPair (encPair e0 encNat) encNat) encNat
  have h1 : IsPPTOn e3 eB (fun p => do
      let x₃ ← F.sampleExp p.1.1.1.1 p.1.1.1.2.1
      let x₄ ← F.sampleExp p.1.1.1.1 p.1.1.1.2.1
      let x₅ ← F.sampleExp p.1.1.1.1 p.1.1.1.2.1
      return f (((p, x₃), x₄), x₅)) :=
    isPPTOn_bind3_sampleExp F e3 eB (fun p => p.1.1.1.1) (fun p => p.1.1.1.2.1)
      (by fun_prop) (by fun_prop) hf.isPPTOn (fun _ => rfl)
  exact isPPTOn_bind3_sampleExp F e0 eB (fun inp => inp.1) (fun inp => inp.2.1)
    (.fst' .id') (by fun_prop) h1 hprog

private theorem isPPTOn_withDesc_schedule {A B : Type} (eA : A ↪ List Bool) (eB : B ↪ List Bool)
    {d : ℕ → F.Desc} (hd : ComputableInPolyTime d encUnary F.encDesc)
    {prog : ℕ × F.Desc × A → ProbComp B}
    (hprog : IsPPTOn (encPair encUnary (encPair F.encDesc eA)) eB prog) :
    IsPPTOn (encPair encUnary eA) eB (fun inp : ℕ × A => prog (inp.1, d inp.1, inp.2)) :=
  hprog.preprocess
    ((ComputableInPolyTime.fst encUnary eA).prod ((hd.comp' (.fst' .id')).prod (.snd' .id')))

private theorem isPPTOn_bind6_sampleExp_schedule {A B : Type} (eA : A ↪ List Bool)
    (eB : B ↪ List Bool) {d : ℕ → F.Desc} (hd : ComputableInPolyTime d encUnary F.encDesc)
    {f : ((((((ℕ × F.Desc × A) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ → B}
    (hf : ComputableInPolyTime f (sample6Enc F eA) eB)
    {prog : ℕ × F.Desc × A → ProbComp B}
    (hprog : ∀ inp, ProbComp.eval (prog inp) =
      ProbComp.eval (do
        let x₀ ← F.sampleExp inp.1 inp.2.1
        let x₁ ← F.sampleExp inp.1 inp.2.1
        let x₂ ← F.sampleExp inp.1 inp.2.1
        let x₃ ← F.sampleExp inp.1 inp.2.1
        let x₄ ← F.sampleExp inp.1 inp.2.1
        let x₅ ← F.sampleExp inp.1 inp.2.1
        return f ((((((inp, x₀), x₁), x₂), x₃), x₄), x₅))) :
    IsPPTOn (encPair encUnary eA) eB (fun inp : ℕ × A => prog (inp.1, d inp.1, inp.2)) :=
  isPPTOn_withDesc_schedule F eA eB hd (isPPTOn_bind6_sampleExp F eA eB hf hprog)

private theorem computableInPolyTime_mod_order {P : Type} (eP : P ↪ List Bool)
    {x : P → ℕ} {desc : P → F.Desc}
    (hx : ComputableInPolyTime x eP encNat)
    (hdesc : ComputableInPolyTime desc eP F.encDesc) :
    ComputableInPolyTime (fun p => x p % F.order (desc p)) eP encNat :=
  ComputableInPolyTime.of_tidy
    (ComputableTidilyInPolyTime.binary_mod' hx.tidy
      (F.computableInPolyTime_order.comp' hdesc).tidy)

private theorem computableInPolyTime_elgamalMask {P : Type} (eP : P ↪ List Bool)
    {desc : P → F.Desc} {r s : P → ℕ} {u_w : P → List Bool}
    (hd : ComputableInPolyTime desc eP F.encDesc)
    (hr : ComputableInPolyTime r eP encNat)
    (hs : ComputableInPolyTime s eP encNat)
    (hu : ComputableInPolyTime u_w eP encBits) :
    ComputableInPolyTime
      (fun p => F.add (desc p, F.encodeElGamalPublicKey (desc p, r p),
        F.smul (desc p, s p, u_w p))) eP encBits :=
  F.computableInPolyTime_add.comp'
    (hd.prod ((F.computableInPolyTime_encodeElGamalPublicKey.comp' (hd.prod hr)).prod
      (F.computableInPolyTime_smul.comp' (hd.prod (hs.prod hu)))))

private theorem computableInPolyTime_senderCoinsAndKeys {A : Type} (eA : A ↪ List Bool) :
    ComputableInPolyTime
      (fun p : ((((((ℕ × F.Desc × A) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ =>
        let desc := p.1.1.1.1.1.1.2.1
        let q := F.order desc
        let a := p.1.1.1.1.1.2
        let r₀ := p.1.1.1.1.2
        let s₀ := p.1.1.1.2
        let r₁ := p.1.1.2
        let s₁ := p.1.2
        let b := p.2
        let u_w := F.encodeElGamalPublicKey (desc, a)
        let v_w := F.encodeElGamalPublicKey (desc, b)
        let u_sub_v_w := F.decodeElGamal (desc, 1, v_w, u_w)
        ((a % q, r₀ % q, s₀ % q, r₁ % q, s₁ % q), (u_w, v_w, u_sub_v_w)))
      (sample6Enc F eA)
      (encPair
        (encPair encNat (encPair encNat (encPair encNat (encPair encNat encNat))))
        (encPair encBits (encPair encBits encBits))) := by
  let e6 := sample6Enc F eA
  have hd : ComputableInPolyTime (fun p => p.1.1.1.1.1.1.2.1) e6 F.encDesc := by fun_prop
  have ha : ComputableInPolyTime (fun p => p.1.1.1.1.1.2) e6 encNat := by fun_prop
  have hr0 : ComputableInPolyTime (fun p => p.1.1.1.1.2) e6 encNat := by fun_prop
  have hs0 : ComputableInPolyTime (fun p => p.1.1.1.2) e6 encNat := by fun_prop
  have hr1 : ComputableInPolyTime (fun p => p.1.1.2) e6 encNat := by fun_prop
  have hs1 : ComputableInPolyTime (fun p => p.1.2) e6 encNat := by fun_prop
  have hb : ComputableInPolyTime (fun p => p.2) e6 encNat := by fun_prop
  have ha_mod := computableInPolyTime_mod_order F e6 ha hd
  have hr0_mod := computableInPolyTime_mod_order F e6 hr0 hd
  have hs0_mod := computableInPolyTime_mod_order F e6 hs0 hd
  have hr1_mod := computableInPolyTime_mod_order F e6 hr1 hd
  have hs1_mod := computableInPolyTime_mod_order F e6 hs1 hd
  have hu := F.computableInPolyTime_encodeElGamalPublicKey.comp' (hd.prod ha)
  have hv := F.computableInPolyTime_encodeElGamalPublicKey.comp' (hd.prod hb)
  have husv := F.computableInPolyTime_decodeElGamal.comp'
    (hd.prod ((ComputableInPolyTime.const 1).prod (hv.prod hu)))
  exact (ha_mod.prod (hr0_mod.prod (hs0_mod.prod (hr1_mod.prod hs1_mod)))).prod
    (hu.prod (hv.prod husv))

/-- Strict-PPT certificate for `ddhOTRealWordWithDesc`. -/
theorem isPPTOn_ddhOTRealWordWithDesc :
    IsPPTOn (encDDHOTWordWithDesc F) encDDHOTRunOut (ddhOTRealWordWithDesc F) := by
  let e6 := sample6Enc F encDDHOTWordPair
  have hfin : ComputableInPolyTime
      (fun p : ((((((ℕ × F.Desc × (List Bool × List Bool) × Bool) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ =>
        let inp := p.1.1.1.1.1.1
        let a := p.1.1.1.1.1.2
        let r₀ := p.1.1.1.1.2
        let s₀ := p.1.1.1.2
        let r₁ := p.1.1.2
        let s₁ := p.1.2
        let b := p.2
        let desc := inp.2.1
        let m₀_w := inp.2.2.1.1
        let m₁_w := inp.2.2.1.2
        let σ := inp.2.2.2
        let q := F.order desc
        let u_w := F.encodeElGamalPublicKey (desc, a)
        let v_w := F.encodeElGamalPublicKey (desc, b)
        let u_sub_v_w := F.decodeElGamal (desc, 1, v_w, u_w)
        let w_w := if σ then (u_sub_v_w, v_w) else (v_w, u_sub_v_w)
        let ct₀ := ddhOTEncryptBranchWord F desc u_w w_w.1 m₀_w r₀ s₀ a
        let ct₁ := ddhOTEncryptBranchWord F desc u_w w_w.2 m₁_w r₁ s₁ a
        let senderView_w := encDDHOTSenderViewRaw
          ((m₀_w, m₁_w), (a % q, r₀ % q, s₀ % q, r₁ % q, s₁ % q), w_w)
        let receiverView_w := encDDHOTReceiverViewRaw (σ, b % q, u_w, (ct₀, ct₁))
        let out_w := if σ then m₁_w else m₀_w
        (senderView_w, receiverView_w, out_w))
      e6 encDDHOTRunOut := by
    have hcore := computableInPolyTime_senderCoinsAndKeys F encDDHOTWordPair
    have hd : ComputableInPolyTime (fun p => p.1.1.1.1.1.1.2.1) e6 F.encDesc := by fun_prop
    have hm0 : ComputableInPolyTime (fun p => p.1.1.1.1.1.1.2.2.1.1) e6 encBits := by fun_prop
    have hm1 : ComputableInPolyTime (fun p => p.1.1.1.1.1.1.2.2.1.2) e6 encBits := by fun_prop
    have hσ : ComputableInPolyTime (fun p => p.1.1.1.1.1.1.2.2.2) e6 encBool := by fun_prop
    have ha : ComputableInPolyTime (fun p => p.1.1.1.1.1.2) e6 encNat := by fun_prop
    have hr0 : ComputableInPolyTime (fun p => p.1.1.1.1.2) e6 encNat := by fun_prop
    have hs0 : ComputableInPolyTime (fun p => p.1.1.1.2) e6 encNat := by fun_prop
    have hr1 : ComputableInPolyTime (fun p => p.1.1.2) e6 encNat := by fun_prop
    have hs1 : ComputableInPolyTime (fun p => p.1.2) e6 encNat := by fun_prop
    have hb : ComputableInPolyTime (fun p => p.2) e6 encNat := by fun_prop
    have hb_mod := computableInPolyTime_mod_order F e6 hb hd
    have hu := hcore.snd'.fst'
    have hv := hcore.snd'.snd'.fst'
    have husv := hcore.snd'.snd'.snd'
    have hw := ComputableInPolyTime.ite' hσ (husv.prod hv) (hv.prod husv)
    have hbranch := computableInPolyTime_ddhOTEncryptBranchWord F
    have hct0 := hbranch.comp'
      (hd.prod (hu.prod (hw.fst'.prod (hm0.prod (hr0.prod (hs0.prod ha))))))
    have hct1 := hbranch.comp'
      (hd.prod (hu.prod (hw.snd'.prod (hm1.prod (hr1.prod (hs1.prod ha))))))
    have hsv := ((hm0.prod hm1).prod (hcore.fst'.prod hw)).encoding_comp
    have hrv := (hσ.prod (hb_mod.prod (hu.prod (hct0.prod hct1)))).encoding_comp
    have hout := ComputableInPolyTime.ite' hσ hm1 hm0
    exact hsv.prod (hrv.prod hout)
  refine isPPTOn_bind6_sampleExp F encDDHOTWordPair encDDHOTRunOut hfin (fun inp => ?_)
  rcases inp with ⟨n, desc, ⟨m₀_w, m₁_w⟩, σ⟩
  dsimp only [ddhOTRealWordWithDesc]

/-- Strict-PPT certificate for `ddhOTRealWordRun` whenever `d` is computable in polynomial
time. -/
theorem isPPTOn_ddhOTRealWordRun {d : ℕ → F.Desc}
    (hd : ComputableInPolyTime d encUnary F.encDesc) :
    IsPPTOn encDDHOTWordInput encDDHOTRunOut (ddhOTRealWordRun F d) :=
  isPPTOn_withDesc_schedule F encDDHOTWordPair encDDHOTRunOut hd
    (isPPTOn_ddhOTRealWordWithDesc F)

/-- Word-level simulator for a corrupted sender (`{0}`), sampling exponents with `sampleExp`. -/
noncomputable def ddhOTSenderSimWordWithDesc
    (inp : ℕ × F.Desc × List Bool × List Bool) : ProbComp (List Bool) :=
  let (n, desc, m₀_w, m₁_w) := inp
  do
    let a ← F.sampleExp n desc
    let r₀ ← F.sampleExp n desc
    let s₀ ← F.sampleExp n desc
    let r₁ ← F.sampleExp n desc
    let s₁ ← F.sampleExp n desc
    let b ← F.sampleExp n desc
    let q := F.order desc
    let u_w := F.encodeElGamalPublicKey (desc, a)
    let v_w := F.encodeElGamalPublicKey (desc, b)
    let u_sub_v_w := F.decodeElGamal (desc, 1, v_w, u_w)
    return encDDHOTSenderViewRaw
      ((m₀_w, m₁_w), (a % q, r₀ % q, s₀ % q, r₁ % q, s₁ % q), (v_w, u_sub_v_w))

/-- Word-level corrupted-sender simulator for group schedule `d : ℕ → F.Desc`. -/
noncomputable def ddhOTSenderSimWord (d : ℕ → F.Desc)
    (inp : ℕ × List Bool × List Bool) : ProbComp (List Bool) :=
  ddhOTSenderSimWordWithDesc F (inp.1, d inp.1, inp.2)

/-- Strict-PPT certificate for `ddhOTSenderSimWord` whenever `d` is computable in polynomial
time. -/
theorem isPPTOn_ddhOTSenderSimWord {d : ℕ → F.Desc}
    (hd : ComputableInPolyTime d encUnary F.encDesc) :
    IsPPTOn encDDHOTWordPairInput encBits (ddhOTSenderSimWord F d) := by
  let e6 := sample6Enc F (encPair encBits encBits)
  have hfin : ComputableInPolyTime
      (fun p : ((((((ℕ × F.Desc × List Bool × List Bool) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ =>
        let inp := p.1.1.1.1.1.1
        let a := p.1.1.1.1.1.2
        let r₀ := p.1.1.1.1.2
        let s₀ := p.1.1.1.2
        let r₁ := p.1.1.2
        let s₁ := p.1.2
        let b := p.2
        let desc := inp.2.1
        let m₀_w := inp.2.2.1
        let m₁_w := inp.2.2.2
        let q := F.order desc
        let u_w := F.encodeElGamalPublicKey (desc, a)
        let v_w := F.encodeElGamalPublicKey (desc, b)
        let u_sub_v_w := F.decodeElGamal (desc, 1, v_w, u_w)
        encDDHOTSenderViewRaw
          ((m₀_w, m₁_w), (a % q, r₀ % q, s₀ % q, r₁ % q, s₁ % q), (v_w, u_sub_v_w)))
      e6 encBits := by
    have hcore := computableInPolyTime_senderCoinsAndKeys F (encPair encBits encBits)
    have hm0 : ComputableInPolyTime (fun p => p.1.1.1.1.1.1.2.2.1) e6 encBits := by fun_prop
    have hm1 : ComputableInPolyTime (fun p => p.1.1.1.1.1.1.2.2.2) e6 encBits := by fun_prop
    exact ((hm0.prod hm1).prod
      (hcore.fst'.prod (hcore.snd'.snd'.fst'.prod hcore.snd'.snd'.snd'))).encoding_comp
  exact isPPTOn_bind6_sampleExp_schedule F (encPair encBits encBits) encBits hd hfin (fun inp => by
    rcases inp with ⟨n, desc, m₀_w, m₁_w⟩
    dsimp only [ddhOTSenderSimWordWithDesc])

/-- Word-level simulator for a corrupted receiver (`{1}`), sampling uniform group elements via
`sampleExp` and `encodeElGamalPublicKey`. -/
noncomputable def ddhOTReceiverSimWordWithDesc
    (inp : ℕ × F.Desc × Bool × List Bool) : ProbComp (List Bool) :=
  let (n, desc, σ, m_σ_w) := inp
  do
    let a ← F.sampleExp n desc
    let b ← F.sampleExp n desc
    let r ← F.sampleExp n desc
    let s ← F.sampleExp n desc
    let α' ← F.sampleExp n desc
    let γ' ← F.sampleExp n desc
    let u_w := F.encodeElGamalPublicKey (desc, a)
    let u'_w := F.encodeElGamalPublicKey (desc, α')
    let w'_w := F.encodeElGamalPublicKey (desc, γ')
    let e_σ_w := F.add (desc, F.encodeElGamalPublicKey (desc, r), F.smul (desc, s, u_w))
    let c_σ_w := F.add (desc, F.smul (desc, b, e_σ_w), m_σ_w)
    let reply_w := if σ then ((u'_w, w'_w), (e_σ_w, c_σ_w)) else ((e_σ_w, c_σ_w), (u'_w, w'_w))
    return encDDHOTReceiverViewRaw (σ, b % F.order desc, u_w, reply_w)

/-- Word-level corrupted-receiver simulator for group schedule `d : ℕ → F.Desc`. -/
noncomputable def ddhOTReceiverSimWord (d : ℕ → F.Desc)
    (inp : ℕ × Bool × List Bool) : ProbComp (List Bool) :=
  ddhOTReceiverSimWordWithDesc F (inp.1, d inp.1, inp.2)

/-- Strict-PPT certificate for `ddhOTReceiverSimWord` whenever `d` is computable in polynomial
time. -/
theorem isPPTOn_ddhOTReceiverSimWord {d : ℕ → F.Desc}
    (hd : ComputableInPolyTime d encUnary F.encDesc) :
    IsPPTOn (encPair encUnary (encPair encBool encBits)) encBits (ddhOTReceiverSimWord F d) := by
  let e6 := sample6Enc F (encPair encBool encBits)
  have hfin : ComputableInPolyTime
      (fun p : ((((((ℕ × F.Desc × Bool × List Bool) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ =>
        let inp := p.1.1.1.1.1.1
        let a := p.1.1.1.1.1.2
        let b := p.1.1.1.1.2
        let r := p.1.1.1.2
        let s := p.1.1.2
        let α' := p.1.2
        let γ' := p.2
        let desc := inp.2.1
        let σ := inp.2.2.1
        let m_σ_w := inp.2.2.2
        let u_w := F.encodeElGamalPublicKey (desc, a)
        let u'_w := F.encodeElGamalPublicKey (desc, α')
        let w'_w := F.encodeElGamalPublicKey (desc, γ')
        let e_σ_w := F.add (desc, F.encodeElGamalPublicKey (desc, r), F.smul (desc, s, u_w))
        let c_σ_w := F.add (desc, F.smul (desc, b, e_σ_w), m_σ_w)
        let reply_w := if σ then ((u'_w, w'_w), (e_σ_w, c_σ_w)) else ((e_σ_w, c_σ_w), (u'_w, w'_w))
        encDDHOTReceiverViewRaw (σ, b % F.order desc, u_w, reply_w))
      e6 encBits := by
    have hd' : ComputableInPolyTime (fun p => p.1.1.1.1.1.1.2.1) e6 F.encDesc := by fun_prop
    have hσ : ComputableInPolyTime (fun p => p.1.1.1.1.1.1.2.2.1) e6 encBool := by fun_prop
    have hm : ComputableInPolyTime (fun p => p.1.1.1.1.1.1.2.2.2) e6 encBits := by fun_prop
    have ha : ComputableInPolyTime (fun p => p.1.1.1.1.1.2) e6 encNat := by fun_prop
    have hb : ComputableInPolyTime (fun p => p.1.1.1.1.2) e6 encNat := by fun_prop
    have hr : ComputableInPolyTime (fun p => p.1.1.1.2) e6 encNat := by fun_prop
    have hs : ComputableInPolyTime (fun p => p.1.1.2) e6 encNat := by fun_prop
    have hα : ComputableInPolyTime (fun p => p.1.2) e6 encNat := by fun_prop
    have hγ : ComputableInPolyTime (fun p => p.2) e6 encNat := by fun_prop
    have hb_mod := computableInPolyTime_mod_order F e6 hb hd'
    have hu := F.computableInPolyTime_encodeElGamalPublicKey.comp' (hd'.prod ha)
    have hu' := F.computableInPolyTime_encodeElGamalPublicKey.comp' (hd'.prod hα)
    have hw' := F.computableInPolyTime_encodeElGamalPublicKey.comp' (hd'.prod hγ)
    have he := computableInPolyTime_elgamalMask F e6 hd' hr hs hu
    have hc := F.computableInPolyTime_add.comp'
      (hd'.prod ((F.computableInPolyTime_smul.comp' (hd'.prod (hb.prod he))).prod hm))
    have hreply := ComputableInPolyTime.ite' hσ
      ((hu'.prod hw').prod (he.prod hc)) ((he.prod hc).prod (hu'.prod hw'))
    exact (hσ.prod (hb_mod.prod (hu.prod hreply))).encoding_comp
  exact isPPTOn_bind6_sampleExp_schedule F (encPair encBool encBits) encBits hd hfin (fun inp => by
    rcases inp with ⟨n, desc, σ, m_σ_w⟩
    dsimp only [ddhOTReceiverSimWordWithDesc])

/-- Word-level DDH distinguisher reduced from a DDH-OT distinguisher `D` on word-encoded input
family `x_word : ℕ → (List Bool × List Bool) × Bool`. -/
noncomputable def ddhOTWordReduction
    (x_word : ℕ → (List Bool × List Bool) × Bool)
    (D : ℕ → List Bool × List Bool → ProbComp Bool)
    (n : ℕ) (chal : F.Desc × List Bool × List Bool × List Bool) : ProbComp Bool :=
  let (desc, u_w, u'_w, w_ddh_w) := chal
  let ((m₀_w, m₁_w), σ) := x_word n
  do
    let b ← F.sampleExp n desc
    let r ← F.sampleExp n desc
    let s ← F.sampleExp n desc
    let e_σ_w := F.add (desc, F.encodeElGamalPublicKey (desc, r), F.smul (desc, s, u_w))
    let m_σ_w := if σ then m₁_w else m₀_w
    let m_other_w := if σ then m₀_w else m₁_w
    let c_σ_w := F.add (desc, F.smul (desc, b, e_σ_w), m_σ_w)
    let c_other_w := F.add (desc, F.decodeElGamal (desc, b, u'_w, w_ddh_w), m_other_w)
    let reply_w := if σ then ((u'_w, c_other_w), (e_σ_w, c_σ_w))
      else ((e_σ_w, c_σ_w), (u'_w, c_other_w))
    let view_w := encDDHOTReceiverViewRaw (σ, b % F.order desc, u_w, reply_w)
    D n (view_w, m_σ_w)

/-- Strict-PPT certificate for `ddhOTWordReduction` whenever `x_word` is computable in polynomial
time and `D` is uniform strict PPT. -/
theorem isPPTOn_ddhOTWordReduction
    {x_word : ℕ → (List Bool × List Bool) × Bool}
    {D : ℕ → List Bool × List Bool → ProbComp Bool}
    (hx : ComputableInPolyTime x_word encUnary encDDHOTWordPair)
    (hD : IsPPTOn encDDHOTWordPairInput encBool (fun p => D p.1 p.2)) :
    IsPPTOn F.encDDHInput encBool
      (fun input => ddhOTWordReduction F x_word D input.1 input.2) := by
  let e0 := F.encDDHInput
  let e3' := encPair (encPair (encPair e0 encNat) encNat) encNat
  have hprep : ComputableInPolyTime
      (fun p : (((ℕ × F.Desc × List Bool × List Bool × List Bool) × ℕ) × ℕ) × ℕ =>
        let inp := p.1.1.1
        let n := inp.1
        let desc := inp.2.1
        let u_w := inp.2.2.1
        let u'_w := inp.2.2.2.1
        let w_ddh_w := inp.2.2.2.2
        let b := p.1.1.2
        let r := p.1.2
        let s := p.2
        let xw := x_word n
        let m₀_w := xw.1.1
        let m₁_w := xw.1.2
        let σ := xw.2
        let e_σ_w := F.add (desc, F.encodeElGamalPublicKey (desc, r), F.smul (desc, s, u_w))
        let m_σ_w := if σ then m₁_w else m₀_w
        let m_other_w := if σ then m₀_w else m₁_w
        let c_σ_w := F.add (desc, F.smul (desc, b, e_σ_w), m_σ_w)
        let c_other_w := F.add (desc, F.decodeElGamal (desc, b, u'_w, w_ddh_w), m_other_w)
        let reply_w := if σ then ((u'_w, c_other_w), (e_σ_w, c_σ_w))
          else ((e_σ_w, c_σ_w), (u'_w, c_other_w))
        let view_w := encDDHOTReceiverViewRaw (σ, b % F.order desc, u_w, reply_w)
        (n, (view_w, m_σ_w)))
      e3' (encPair encUnary (encPair encBits encBits)) := by
    have hn : ComputableInPolyTime (fun p => p.1.1.1.1) e3' encUnary := by fun_prop
    have hd : ComputableInPolyTime (fun p => p.1.1.1.2.1) e3' F.encDesc := by fun_prop
    have hu : ComputableInPolyTime (fun p => p.1.1.1.2.2.1) e3' encBits := by fun_prop
    have hu' : ComputableInPolyTime (fun p => p.1.1.1.2.2.2.1) e3' encBits := by fun_prop
    have hw : ComputableInPolyTime (fun p => p.1.1.1.2.2.2.2) e3' encBits := by fun_prop
    have hb : ComputableInPolyTime (fun p => p.1.1.2) e3' encNat := by fun_prop
    have hr : ComputableInPolyTime (fun p => p.1.2) e3' encNat := by fun_prop
    have hs : ComputableInPolyTime (fun p => p.2) e3' encNat := by fun_prop
    have hxw := hx.comp' hn
    have hm0 := hxw.fst'.fst'
    have hm1 := hxw.fst'.snd'
    have hσ := hxw.snd'
    have hb_mod := computableInPolyTime_mod_order F e3' hb hd
    have he := computableInPolyTime_elgamalMask F e3' hd hr hs hu
    have hm_σ := ComputableInPolyTime.ite' hσ hm1 hm0
    have hm_other := ComputableInPolyTime.ite' hσ hm0 hm1
    have hb_e := F.computableInPolyTime_smul.comp' (hd.prod (hb.prod he))
    have hc_σ := F.computableInPolyTime_add.comp' (hd.prod (hb_e.prod hm_σ))
    have hdec := F.computableInPolyTime_decodeElGamal.comp' (hd.prod (hb.prod (hu'.prod hw)))
    have hc_other := F.computableInPolyTime_add.comp' (hd.prod (hdec.prod hm_other))
    have hreply := ComputableInPolyTime.ite' hσ
      ((hu'.prod hc_other).prod (he.prod hc_σ)) ((he.prod hc_σ).prod (hu'.prod hc_other))
    have hview := (hσ.prod (hb_mod.prod (hu.prod hreply))).encoding_comp
    exact hn.prod (hview.prod hm_σ)
  refine isPPTOn_bind3_sampleExp F e0 encBool (fun p => p.1) (fun p => p.2.1)
    (.fst' .id') (.fst' (.snd' .id')) (hD.preprocess hprep) (fun p => ?_)
  rcases p with ⟨n, desc, u_w, u'_w, w_ddh_w⟩
  dsimp only [ddhOTWordReduction]

/-! ### Exact and statistical bridges between word-level and typed DDH-OT -/

private theorem decodeElGamal_sub_one (desc : F.Desc) (u v : F.Carrier desc) :
    F.decodeElGamal (desc, 1, F.encode desc v, F.encode desc u) = F.encode desc (u - v) := by
  simp only [F.decodeElGamal_encode, PrimeOrderGroupFamily.elGamalDecrypt, Nat.cast_one, one_smul]

private theorem ddhOTRealWordRun_eval_bind (d : ℕ → F.Desc) (n : ℕ)
    (x : (i : Fin 2) → OTIn (F.Carrier (d n)) i)
    (k : ZMod (F.order (d n)) → ZMod (F.order (d n)) → ZMod (F.order (d n)) →
      ZMod (F.order (d n)) → ZMod (F.order (d n)) → ZMod (F.order (d n)) → Game)
    (f : List Bool × List Bool × List Bool → ProbComp Bool)
    (hf : ∀ (a r₀ s₀ r₁ s₁ b : ℕ),
      let desc := d n
      let q := F.order desc
      let x₀ : F.Carrier desc × F.Carrier desc := x 0
      let σ : Bool := x 1
      let u_w := F.encodeElGamalPublicKey (desc, a)
      let v_w := F.encodeElGamalPublicKey (desc, b)
      let u_sub_v_w := F.decodeElGamal (desc, 1, v_w, u_w)
      let w_w := if σ then (u_sub_v_w, v_w) else (v_w, u_sub_v_w)
      let ct₀ := ddhOTEncryptBranchWord F desc u_w w_w.1 (F.encode desc x₀.1) r₀ s₀ a
      let ct₁ := ddhOTEncryptBranchWord F desc u_w w_w.2 (F.encode desc x₀.2) r₁ s₁ a
      let senderView_w := encDDHOTSenderViewRaw
        ((F.encode desc x₀.1, F.encode desc x₀.2),
         (a % q, r₀ % q, s₀ % q, r₁ % q, s₁ % q), w_w)
      let receiverView_w := encDDHOTReceiverViewRaw (σ, b % q, u_w, (ct₀, ct₁))
      let out_w := if σ then F.encode desc x₀.2 else F.encode desc x₀.1
      ProbComp.eval (f (senderView_w, receiverView_w, out_w)) =
        k (a : ZMod q) (r₀ : ZMod q) (s₀ : ZMod q) (r₁ : ZMod q) (s₁ : ZMod q) (b : ZMod q)) :
    ProbComp.eval (ddhOTRealWordRun F d (n, encodeDDHOTInputWord F (d n) x) >>= f) =
      bind6 (ProbComp.eval (F.sampleExp n (d n)))
        (fun a r₀ s₀ r₁ s₁ b => k a r₀ s₀ r₁ s₁ b) := by
  simp only [ddhOTRealWordRun, ddhOTRealWordWithDesc, encodeDDHOTInputWord,
    ProbComp.eval_bind, ProbComp.eval_pure, PMF.bind_bind, PMF.pure_bind]
  exact bind6_eq _ hf

private theorem ddhOTRealWordRun_advantage_bind6_le (d : ℕ → F.Desc) (n : ℕ)
    (x : (i : Fin 2) → OTIn (F.Carrier (d n)) i)
    (k : ZMod (F.order (d n)) → ZMod (F.order (d n)) → ZMod (F.order (d n)) →
      ZMod (F.order (d n)) → ZMod (F.order (d n)) → ZMod (F.order (d n)) → Game)
    (f : List Bool × List Bool × List Bool → ProbComp Bool) (rhs : Game)
    (hf : ∀ (a r₀ s₀ r₁ s₁ b : ℕ),
      let desc := d n
      let q := F.order desc
      let x₀ : F.Carrier desc × F.Carrier desc := x 0
      let σ : Bool := x 1
      let u_w := F.encodeElGamalPublicKey (desc, a)
      let v_w := F.encodeElGamalPublicKey (desc, b)
      let u_sub_v_w := F.decodeElGamal (desc, 1, v_w, u_w)
      let w_w := if σ then (u_sub_v_w, v_w) else (v_w, u_sub_v_w)
      let ct₀ := ddhOTEncryptBranchWord F desc u_w w_w.1 (F.encode desc x₀.1) r₀ s₀ a
      let ct₁ := ddhOTEncryptBranchWord F desc u_w w_w.2 (F.encode desc x₀.2) r₁ s₁ a
      let senderView_w := encDDHOTSenderViewRaw
        ((F.encode desc x₀.1, F.encode desc x₀.2),
         (a % q, r₀ % q, s₀ % q, r₁ % q, s₁ % q), w_w)
      let receiverView_w := encDDHOTReceiverViewRaw (σ, b % q, u_w, (ct₀, ct₁))
      let out_w := if σ then F.encode desc x₀.2 else F.encode desc x₀.1
      ProbComp.eval (f (senderView_w, receiverView_w, out_w)) =
        k (a : ZMod q) (r₀ : ZMod q) (s₀ : ZMod q) (r₁ : ZMod q) (s₁ : ZMod q) (b : ZMod q))
    (hrhs : rhs = bind6 (PMF.uniformOfFintype (ZMod (F.order (d n)))) k) :
    Game.advantage (ProbComp.eval (ddhOTRealWordRun F d (n, encodeDDHOTInputWord F (d n) x) >>= f))
      rhs ≤ 6 / 2 ^ n := by
  rw [ddhOTRealWordRun_eval_bind F d n x k f hf, hrhs]
  exact advantage_bind6_sampleExp_le F n (d n) k

private theorem ddhOTRealWordRun_sender_advantage_le (d : ℕ → F.Desc) (n : ℕ)
    [DecidableEq (F.Carrier (d n))]
    (x : (i : Fin 2) → OTIn (F.Carrier (d n)) i)
    (D : ℕ → List Bool × List Bool → ProbComp Bool) :
    Game.advantage
      (ProbComp.eval (ddhOTRealWordRun F d (n, encodeDDHOTInputWord F (d n) x) >>=
        fun r => D n (r.1, r.2.2)))
      (((ddhOTProtocol (F.generator (d n)) (F.order (d n))).realJoint noOracleWorld {0} x).bind
        fun r => ProbComp.eval (D n (encodeDDHOTSenderJointPair F (d n) r))) ≤ 6 / 2 ^ n := by
  let desc := d n
  let q := F.order desc
  let g := F.generator desc
  have : NeZero q := ⟨(F.prime_order desc).ne_zero⟩
  let k : ZMod q → ZMod q → ZMod q → ZMod q → ZMod q → ZMod q → Game :=
    fun a r₀ s₀ r₁ s₁ b =>
      let c₀ : DDHOTSenderCoins q := (a, r₀, s₀, r₁, s₁)
      let w := ddhOTReceiverMsg g (x 1) b (c₀.1.val • g)
      ProbComp.eval (D n
        (encodeDDHOTSenderViewWord F desc (ddhOTSenderView (x 0) c₀ w),
          F.encode desc (otOutputs x 1)))
  have hreal_exact :
      (((ddhOTProtocol g q).realJoint noOracleWorld {0} x).bind fun r =>
        ProbComp.eval (D n (encodeDDHOTSenderJointPair F desc r))) =
      bind6 (PMF.uniformOfFintype (ZMod q)) k := by
    rw [realJoint_ddhOT_sender, PMF.bind_bind]
    simp only [sampleDDHOTSenderCoins, ProbComp.eval_bind, ProbComp.eval_uniform,
      ProbComp.eval_pure, PMF.pure_bind, PMF.bind_map, PMF.bind_bind]
    exact bind6_eq _ fun _ _ _ _ _ _ => rfl
  refine ddhOTRealWordRun_advantage_bind6_le F d n x k _ _ (fun a r₀ s₀ r₁ s₁ b => ?_)
    hreal_exact
  dsimp only [k, encodeDDHOTSenderViewWord, encodeDDHOTSenderJointPair, ddhOTSenderView,
    encodeDDHOTOutputsWord, otOutputs, ddhOTReceiverMsg]
  rw [F.encodeElGamalPublicKey_eq_encode, F.encodeElGamalPublicKey_eq_encode,
    decodeElGamal_sub_one, smul_natCast_eq_nsmul, smul_natCast_eq_nsmul]
  simp only [ZMod.val_natCast]
  rcases Bool.eq_false_or_eq_true (x 1) with hσ | hσ <;>
    simp only [hσ, Bool.false_eq_true, ↓reduceIte] <;> rfl

private theorem ddhOTSenderSimWord_advantage_le (d : ℕ → F.Desc) (n : ℕ)
    (x : (i : Fin 2) → OTIn (F.Carrier (d n)) i)
    (D : ℕ → List Bool × List Bool → ProbComp Bool) :
    Game.advantage
      (ProbComp.eval ((do
        let v_w ← ddhOTSenderSimWord F d (n, (encodeDDHOTInputWord F (d n) x).1)
        return (v_w, F.encode (d n) (otOutputs x 1))) >>= fun r => D n r))
      (ProbComp.eval (idealJoint (otFunctionality (F.Carrier (d n))) {0}
        (ddhOTSenderSim (F.generator (d n)) (F.order (d n))) x >>= fun r =>
          D n (encodeDDHOTSenderJointPair F (d n) r))) ≤ 6 / 2 ^ n := by
  let desc := d n
  let q := F.order desc
  let g := F.generator desc
  have : NeZero q := ⟨(F.prime_order desc).ne_zero⟩
  let k : ZMod q → ZMod q → ZMod q → ZMod q → ZMod q → ZMod q → Game :=
    fun a r₀ s₀ r₁ s₁ b =>
      let c₀ : DDHOTSenderCoins q := (a, r₀, s₀, r₁, s₁)
      let u := a.val • g
      let v := b.val • g
      let view_w := encodeDDHOTSenderViewWord F desc (ddhOTSenderView (x 0) c₀ (v, u - v))
      let out_w := F.encode desc (otOutputs x 1)
      ProbComp.eval (D n (view_w, out_w))
  have hsim_w :
      ProbComp.eval ((do
        let v_w ← ddhOTSenderSimWord F d (n, (encodeDDHOTInputWord F desc x).1)
        return (v_w, F.encode desc (otOutputs x 1))) >>= fun r => D n r) =
      bind6 (ProbComp.eval (F.sampleExp n desc))
        (fun a r₀ s₀ r₁ s₁ b => k a r₀ s₀ r₁ s₁ b) := by
    simp only [ddhOTSenderSimWord, ddhOTSenderSimWordWithDesc, encodeDDHOTInputWord,
      ProbComp.eval_bind, ProbComp.eval_pure, PMF.bind_bind, PMF.pure_bind]
    refine bind6_eq _ fun a r₀ s₀ r₁ s₁ b => ?_
    dsimp only [k, encodeDDHOTSenderViewWord, ddhOTSenderView]
    rw [F.encodeElGamalPublicKey_eq_encode, F.encodeElGamalPublicKey_eq_encode,
      decodeElGamal_sub_one, smul_natCast_eq_nsmul, smul_natCast_eq_nsmul]
    simp only [ZMod.val_natCast]
    rfl
  have hsim_exact :
      ProbComp.eval (idealJoint (otFunctionality (F.Carrier desc)) {0}
        (ddhOTSenderSim g q) x >>= fun r => D n (encodeDDHOTSenderJointPair F desc r)) =
      bind6 (PMF.uniformOfFintype (ZMod q)) k := by
    simp only [idealJoint, otFunctionality, Functionality.ofDeterministic, ddhOTSenderSim,
      sampleDDHOTSenderCoins, ProbComp.eval_bind, ProbComp.eval_uniform, ProbComp.eval_pure,
      PMF.pure_bind, PMF.bind_bind]
    exact bind6_eq _ fun _ _ _ _ _ _ => rfl
  rw [hsim_w, hsim_exact]
  exact advantage_bind6_sampleExp_le F n desc k

private theorem ddhOTRealWordRun_receiver_advantage_le (d : ℕ → F.Desc) (n : ℕ)
    [DecidableEq (F.Carrier (d n))]
    (x : (i : Fin 2) → OTIn (F.Carrier (d n)) i)
    (D : ℕ → List Bool × List Bool → ProbComp Bool) :
    Game.advantage
      (ProbComp.eval (ddhOTRealWordRun F d (n, encodeDDHOTInputWord F (d n) x) >>=
        fun r => D n (r.2.1, r.2.2)))
      (((ddhOTProtocol (F.generator (d n)) (F.order (d n))).realJoint noOracleWorld {1} x).bind
        fun r => ProbComp.eval (D n (encodeDDHOTReceiverJointPair F (d n) r))) ≤ 6 / 2 ^ n := by
  let desc := d n
  let q := F.order desc
  let g := F.generator desc
  have : NeZero q := ⟨(F.prime_order desc).ne_zero⟩
  let k : ZMod q → ZMod q → ZMod q → ZMod q → ZMod q → ZMod q → Game :=
    fun a r₀ s₀ r₁ s₁ b =>
      let c₀ : DDHOTSenderCoins q := (a, r₀, s₀, r₁, s₁)
      let u := a.val • g
      let reply := ddhOTSenderReply g (x 0) c₀ (ddhOTReceiverMsg g (x 1) b u)
      ProbComp.eval (D n
        (encodeDDHOTReceiverViewWord F desc (ddhOTReceiverView (x 1) b u reply),
          F.encode desc (otOutputs x 1)))
  refine ddhOTRealWordRun_advantage_bind6_le F d n x k _ _ (fun a r₀ s₀ r₁ s₁ b => ?_) ?_
  · dsimp only [k, desc, q, g, otOutputs, ddhOTSenderReply]
    cases x 1 <;>
      · simp only [↓reduceIte, Bool.false_eq_true]
        dsimp only [encodeDDHOTReceiverViewWord, ddhOTReceiverView]
        rw [F.encodeElGamalPublicKey_eq_encode, F.encodeElGamalPublicKey_eq_encode,
          decodeElGamal_sub_one, smul_natCast_eq_nsmul, ddhOTReceiverMsg_add]
        simp only [↓reduceIte, Bool.false_eq_true, ddhOTReceiverMsg,
          ddhOTEncryptBranchWord_encode, smul_natCast_eq_nsmul]
        simp only [ZMod.val_natCast]
        rfl
  · change (((ddhOTProtocol g q).realJoint noOracleWorld {1} x).bind fun r =>
        ProbComp.eval (D n (encodeDDHOTReceiverJointPair F desc r))) =
      bind6 (PMF.uniformOfFintype (ZMod q)) k
    have h1 : ProbComp.eval ((ddhOTProtocol g q).sampleCoins (Fin.succ 0)) =
        (PMF.uniformOfFintype (ZMod q) : PMF (DDHOTCoins q (Fin.succ 0))) :=
      ProbComp.eval_uniform (α := ZMod q)
    have hpi :
        ProbComp.eval (OracleComp.pi (ddhOTProtocol g q).sampleCoins) =
          (ProbComp.eval (sampleDDHOTSenderCoins q)).bind fun c₀ =>
            (PMF.uniformOfFintype (ZMod q)).bind fun b =>
              PMF.pure (Fin.cases c₀ (fun _ => b) : (i : Fin 2) → DDHOTCoins q i) := by
      simp only [OracleComp.pi_succ, OracleComp.pi_zero, ProbComp.eval_bind,
        ProbComp.eval_map, ProbComp.eval_pure, h1]
      refine congrArg (PMF.bind _) (funext fun c₀ => ?_)
      simp only [PMF.map, Function.comp_def]
      erw [PMF.bind_bind]
      refine congrArg (PMF.bind _) (funext fun b => ?_)
      erw [PMF.pure_bind, PMF.pure_bind]
      refine congrArg PMF.pure (funext (β := DDHOTCoins q) fun i => ?_)
      fin_cases i <;> rfl
    have hsteps (c₀ : DDHOTSenderCoins q) (b : ZMod q) :
        ((ddhOTProtocol g q).steps.evalWith noOracleWorld
          (fun i => (x i, (Fin.cases c₀ (fun _ => b) i : DDHOTCoins q i)))) =
          PMF.pure (
            let u := c₀.1.val • g
            let w := ddhOTReceiverMsg g (x 1) b u
            let reply := ddhOTSenderReply g (x 0) c₀ w
            fun i : Fin 2 =>
              (Round.deliverMessage u i,
                (Round.deliverMessage w i, (Round.deliverMessage reply i, ())))) := by
      dsimp only [ddhOTProtocol]
      refine (Steps.evalWith_message _ _ _ _).trans ?_
      refine (congrArg (PMF.map _) (Steps.evalWith_message _ _ _ _)).trans ?_
      refine (congrArg (PMF.map _ ∘ PMF.map _) (Steps.evalWith_message _ _ _ _)).trans ?_
      simp only [Function.comp_apply, Steps.evalWith_done, PMF.pure_map]
      rfl
    rw [Protocol.realJoint, Protocol.evalWith_eq, hpi, PMF.bind_bind]
    simp only [PMF.bind_bind, hsteps, PMF.pure_bind, PMF.pure_map, sampleDDHOTSenderCoins,
      ProbComp.eval_bind, ProbComp.eval_uniform, ProbComp.eval_pure, PMF.bind_map]
    refine bind6_eq _ fun a r₀ s₀ r₁ s₁ b => ?_
    have hout : ddhOTReceiverOutput (x 1) b
        (ddhOTSenderReply g (x 0) (a, r₀, s₀, r₁, s₁)
          (ddhOTReceiverMsg g (x 1) b (a.val • g))) =
        otOutputs x 1 := by
      rcases Bool.eq_false_or_eq_true (x 1) with hσ | hσ
      · simp only [otOutputs, hσ, ↓reduceIte]
        dsimp only [ddhOTSenderReply]
        rw [ddhOTReceiverMsg_add]
        simp only [↓reduceIte, ddhOTReceiverOutput, ddhOTReceiverMsg]
        exact (ddhOTReceiverOutput_encryptBranch g (x 0).2 a b r₁ s₁).trans rfl
      · simp only [otOutputs, hσ, Bool.false_eq_true, ↓reduceIte]
        dsimp only [ddhOTSenderReply]
        rw [ddhOTReceiverMsg_add]
        simp only [Bool.false_eq_true, ↓reduceIte, ddhOTReceiverOutput, ddhOTReceiverMsg]
        exact (ddhOTReceiverOutput_encryptBranch g (x 0).1 a b r₀ s₀).trans rfl
    have hpair :
        encodeDDHOTReceiverJointPair F desc
          ((Prod.map (Finset.restrict {1}) id)
            (fun i =>
              { input := x i
                coins := Fin.cases (a, r₀, s₀, r₁, s₁) (fun _ => b) i
                received :=
                  (Round.deliverMessage (a.val • g) i,
                    Round.deliverMessage (ddhOTReceiverMsg g (x 1) b (a.val • g)) i,
                    Round.deliverMessage
                      (ddhOTSenderReply g (x 0) (a, r₀, s₀, r₁, s₁)
                        (ddhOTReceiverMsg g (x 1) b (a.val • g))) i, ()) },
              fun i => (ddhOTProtocol g q).outputOfView i
                ⟨x i, Fin.cases (a, r₀, s₀, r₁, s₁) (fun _ => b) i,
                  (Round.deliverMessage (a.val • g) i,
                    Round.deliverMessage (ddhOTReceiverMsg g (x 1) b (a.val • g)) i,
                    Round.deliverMessage
                      (ddhOTSenderReply g (x 0) (a, r₀, s₀, r₁, s₁)
                        (ddhOTReceiverMsg g (x 1) b (a.val • g))) i, ())⟩)) =
        (encodeDDHOTReceiverViewWord F desc
            (ddhOTReceiverView (x 1) b (a.val • g)
              (ddhOTSenderReply g (x 0) (a, r₀, s₀, r₁, s₁)
                (ddhOTReceiverMsg g (x 1) b (a.val • g)))),
          F.encode desc (otOutputs x 1)) :=
      Prod.ext rfl (congrArg (F.encode desc) hout)
    exact congrArg (fun p => ProbComp.eval (D n p)) hpair

private theorem ddhOTReceiverSimWord_advantage_le (d : ℕ → F.Desc) (n : ℕ)
    [Fintype (F.Carrier (d n))]
    (x : (i : Fin 2) → OTIn (F.Carrier (d n)) i)
    (D : ℕ → List Bool × List Bool → ProbComp Bool) :
    Game.advantage
      (ProbComp.eval ((do
        let σ := x 1
        let m_σ_w := F.encode (d n) (otOutputs x 1)
        let v_w ← ddhOTReceiverSimWord F d (n, σ, m_σ_w)
        return (v_w, m_σ_w)) >>= fun r => D n r))
      (ProbComp.eval (idealJoint (otFunctionality (F.Carrier (d n))) {1}
        (ddhOTReceiverSim (F.generator (d n)) (F.order (d n))) x >>= fun r =>
          D n (encodeDDHOTReceiverJointPair F (d n) r))) ≤ 6 / 2 ^ n := by
  let desc := d n
  let q := F.order desc
  let g := F.generator desc
  have : NeZero q := ⟨(F.prime_order desc).ne_zero⟩
  let σ : Bool := x 1
  let m_σ : F.Carrier desc := otOutputs x 1
  let k : ZMod q → ZMod q → ZMod q → ZMod q → ZMod q → ZMod q → Game :=
    fun a b r s α' γ' =>
      let u := a.val • g
      let e_σ := r.val • g + s.val • u
      let c_σ := b.val • e_σ + m_σ
      let u' := α'.val • g
      let w' := γ'.val • g
      let reply := if σ then ((u', w'), e_σ, c_σ) else ((e_σ, c_σ), u', w')
      let view_w := encodeDDHOTReceiverViewWord F desc (ddhOTReceiverView σ b u reply)
      ProbComp.eval (D n (view_w, F.encode desc m_σ))
  have hsim_w :
      ProbComp.eval ((do
        let m_σ_w := F.encode desc m_σ
        let v_w ← ddhOTReceiverSimWord F d (n, σ, m_σ_w)
        return (v_w, m_σ_w)) >>= fun r => D n r) =
      bind6 (ProbComp.eval (F.sampleExp n desc))
        (fun a b r s α' γ' => k a b r s α' γ') := by
    simp only [ddhOTReceiverSimWord, ddhOTReceiverSimWordWithDesc, ProbComp.eval_bind,
      ProbComp.eval_pure, PMF.bind_bind, PMF.pure_bind]
    refine bind6_eq _ fun a b r s α' γ' => ?_
    dsimp only [k, desc, q, g, encodeDDHOTReceiverViewWord, ddhOTReceiverView]
    rw [F.encodeElGamalPublicKey_eq_encode, F.encodeElGamalPublicKey_eq_encode,
      F.encodeElGamalPublicKey_eq_encode, F.encodeElGamalPublicKey_eq_encode,
      F.smul_encode, F.add_encode, F.smul_encode, F.add_encode]
    simp only [smul_natCast_eq_nsmul]
    simp only [ZMod.val_natCast]
    dsimp only [σ]
    rcases Bool.eq_false_or_eq_true (x 1) with hσ | hσ
    · simp only [hσ, ↓reduceIte]
    · simp only [hσ, Bool.false_eq_true, ↓reduceIte]
  have hsim_exact :
      ProbComp.eval (idealJoint (otFunctionality (F.Carrier desc)) {1}
        (ddhOTReceiverSim g q) x >>= fun r => D n (encodeDDHOTReceiverJointPair F desc r)) =
      bind6 (PMF.uniformOfFintype (ZMod q)) k := by
    dsimp only [bind6]
    simp only [idealJoint, otFunctionality, Functionality.ofDeterministic, ddhOTReceiverSim,
      ProbComp.eval_bind, ProbComp.eval_uniform, ProbComp.eval_pure, PMF.pure_bind,
      PMF.bind_bind]
    refine congrArg (PMF.uniformOfFintype (ZMod q)).bind (funext fun a => ?_)
    refine congrArg (PMF.uniformOfFintype (ZMod q)).bind (funext fun b => ?_)
    refine congrArg (PMF.uniformOfFintype (ZMod q)).bind (funext fun r => ?_)
    refine congrArg (PMF.uniformOfFintype (ZMod q)).bind (funext fun s => ?_)
    rw [← uniform_zmod_map_smul_generator F desc]
    simp only [PMF.bind_map]
    refine congrArg (PMF.uniformOfFintype (ZMod q)).bind (funext fun α' => ?_)
    rfl
  rw [hsim_w, hsim_exact]
  exact advantage_bind6_sampleExp_le F n desc k

private theorem ddhOTWordReduction_eq_typed (d : ℕ → F.Desc) (n : ℕ)
    (x : (i : Fin 2) → OTIn (F.Carrier (d n)) i)
    (D : ℕ → List Bool × List Bool → ProbComp Bool)
    (u u' w_ddh : F.Carrier (d n)) :
    Game.advantage
      (ProbComp.eval (ddhOTWordReduction F (fun _ => encodeDDHOTInputWord F (d n) x) D n
        (d n, F.encode (d n) u, F.encode (d n) u', F.encode (d n) w_ddh)))
      (ProbComp.eval (ddhOTReduction (F.generator (d n)) (F.order (d n)) x
        (fun r => D n (encodeDDHOTReceiverJointPair F (d n) r)) (u, u', w_ddh))) ≤ 3 / 2 ^ n := by
  let desc := d n
  let q := F.order desc
  let g := F.generator desc
  have : NeZero q := ⟨(F.prime_order desc).ne_zero⟩
  let D_typed :
      ((i : ↥({1} : Finset (Fin 2))) → PartyView (OTIn (F.Carrier desc)) (DDHOTCoins q)
        (ddhOTSchedule (F.Carrier desc)) ↑i) × ((i : Fin 2) → OTOut (F.Carrier desc) i) →
      ProbComp Bool := fun r => D n (encodeDDHOTReceiverJointPair F desc r)
  let σ : Bool := x 1
  let k : ZMod q → ZMod q → ZMod q → Game := fun b r s =>
    let e_σ := r.val • g + s.val • u
    let m_σ : F.Carrier desc := if σ then (x 0).2 else (x 0).1
    let m_other : F.Carrier desc := if σ then (x 0).1 else (x 0).2
    let c_σ := b.val • e_σ + m_σ
    let c_other := w_ddh - b.val • u' + m_other
    let reply := if σ then ((u', c_other), e_σ, c_σ) else ((e_σ, c_σ), u', c_other)
    ProbComp.eval (D_typed (singletonView (ddhOTReceiverView σ b u reply), otOutputs x))
  have hw :
      ProbComp.eval (ddhOTWordReduction F (fun _ => encodeDDHOTInputWord F desc x) D n
        (desc, F.encode desc u, F.encode desc u', F.encode desc w_ddh)) =
      (ProbComp.eval (F.sampleExp n desc)).bind fun b =>
        (ProbComp.eval (F.sampleExp n desc)).bind fun r =>
          (ProbComp.eval (F.sampleExp n desc)).bind fun s =>
            k (b : ZMod q) (r : ZMod q) (s : ZMod q) := by
    simp only [ddhOTWordReduction, encodeDDHOTInputWord, ProbComp.eval_bind]
    refine congrArg (ProbComp.eval (F.sampleExp n desc)).bind (funext fun b => ?_)
    refine congrArg (ProbComp.eval (F.sampleExp n desc)).bind (funext fun r => ?_)
    refine congrArg (ProbComp.eval (F.sampleExp n desc)).bind (funext fun s => ?_)
    dsimp only [k, D_typed, desc, q, g, σ, encodeDDHOTReceiverJointPair,
      encodeDDHOTReceiverViewWord, encodeDDHOTOutputsWord, ddhOTReceiverView, singletonView,
      otOutputs]
    rcases Bool.eq_false_or_eq_true (x 1) with hσ | hσ
    · simp only [hσ, ↓reduceIte, F.encodeElGamalPublicKey_eq_encode, F.smul_encode, F.add_encode,
        F.decodeElGamal_encode, PrimeOrderGroupFamily.elGamalDecrypt]
      simp only [smul_natCast_eq_nsmul]
      simp only [ZMod.val_natCast]
      rfl
    · simp only [hσ, Bool.false_eq_true, ↓reduceIte, F.encodeElGamalPublicKey_eq_encode,
        F.smul_encode, F.add_encode, F.decodeElGamal_encode, PrimeOrderGroupFamily.elGamalDecrypt]
      simp only [smul_natCast_eq_nsmul]
      simp only [ZMod.val_natCast]
      rfl
  have htyped :
      ProbComp.eval (ddhOTReduction g q x D_typed (u, u', w_ddh)) =
      (PMF.uniformOfFintype (ZMod q)).bind fun b =>
        (PMF.uniformOfFintype (ZMod q)).bind fun r =>
          (PMF.uniformOfFintype (ZMod q)).bind fun s => k b r s := by
    simp only [ddhOTReduction, ProbComp.eval_bind, ProbComp.eval_uniform]
    rfl
  rw [hw, htyped]
  exact advantage_bind_sampleExp_3_le F n desc k

private theorem ddhOTWordReduction_smul_eq_typed (d : ℕ → F.Desc) (n : ℕ)
    (x : (i : Fin 2) → OTIn (F.Carrier (d n)) i)
    (D : ℕ → List Bool × List Bool → ProbComp Bool)
    (α β γ : ZMod (F.order (d n))) :
    Game.advantage
      (ProbComp.eval (ddhOTWordReduction F (fun _ => encodeDDHOTInputWord F (d n) x) D n
        (d n, F.encode (d n) (α • F.generator (d n)),
          F.encode (d n) (β • F.generator (d n)),
          F.encode (d n) (γ • F.generator (d n)))))
      (ProbComp.eval (ddhOTReduction (F.generator (d n)) (F.order (d n)) x
        (fun r => D n (encodeDDHOTReceiverJointPair F (d n) r))
        (α.val • F.generator (d n), β.val • F.generator (d n),
          γ.val • F.generator (d n)))) ≤ 3 / 2 ^ n := by
  have hsmul (c : ZMod (F.order (d n))) :
      c • F.generator (d n) = c.val • F.generator (d n) := by
    conv_lhs => rw [← ZMod.natCast_zmod_val c, Nat.cast_smul_eq_nsmul]
  simpa only [hsmul] using ddhOTWordReduction_eq_typed F d n x D
    (α.val • F.generator (d n)) (β.val • F.generator (d n)) (γ.val • F.generator (d n))

private theorem ddhRealGame_ddhOTWordReduction_le (d : ℕ → F.Desc) (n : ℕ)
    (x_word : ℕ → (List Bool × List Bool) × Bool)
    (x : (i : Fin 2) → OTIn (F.Carrier (d n)) i)
    (hx_eq : x_word n = encodeDDHOTInputWord F (d n) x)
    (D : ℕ → List Bool × List Bool → ProbComp Bool) :
    Game.advantage
      (F.ddhRealGame (fun k => PMF.pure (d k)) (ddhOTWordReduction F x_word D) n)
      (DDH.realGame (F.generator (d n)) (F.order (d n))
        (ddhOTReduction (F.generator (d n)) (F.order (d n)) x
          (fun r => D n (encodeDDHOTReceiverJointPair F (d n) r)))) ≤ 3 / 2 ^ n := by
  simp only [PrimeOrderGroupFamily.ddhRealGame, DDH.realGame, PMF.monad_bind_eq_bind,
    PMF.pure_bind, ProbComp.eval_bind, ProbComp.eval_uniform]
  refine Game.advantage_bind_le_nnreal _ _ _ fun α => ?_
  refine Game.advantage_bind_le_nnreal _ _ _ fun β => ?_
  have hword :
      ddhOTWordReduction F x_word D n
          (d n, F.encode (d n) (α • F.generator (d n)),
            F.encode (d n) (β • F.generator (d n)),
            F.encode (d n) ((α * β) • F.generator (d n))) =
        ddhOTWordReduction F (fun _ => encodeDDHOTInputWord F (d n) x) D n
          (d n, F.encode (d n) (α • F.generator (d n)),
            F.encode (d n) (β • F.generator (d n)),
            F.encode (d n) ((α * β) • F.generator (d n))) := by
    dsimp only [ddhOTWordReduction]
    rw [hx_eq]
  rw [hword]
  exact ddhOTWordReduction_smul_eq_typed F d n x D α β (α * β)

private theorem ddhIdealGame_ddhOTWordReduction_le (d : ℕ → F.Desc) (n : ℕ)
    (x_word : ℕ → (List Bool × List Bool) × Bool)
    (x : (i : Fin 2) → OTIn (F.Carrier (d n)) i)
    (hx_eq : x_word n = encodeDDHOTInputWord F (d n) x)
    (D : ℕ → List Bool × List Bool → ProbComp Bool) :
    Game.advantage
      (F.ddhIdealGame (fun k => PMF.pure (d k)) (ddhOTWordReduction F x_word D) n)
      (DDH.randomGame (F.generator (d n)) (F.order (d n))
        (ddhOTReduction (F.generator (d n)) (F.order (d n)) x
          (fun r => D n (encodeDDHOTReceiverJointPair F (d n) r)))) ≤ 3 / 2 ^ n := by
  simp only [PrimeOrderGroupFamily.ddhIdealGame, DDH.randomGame, PMF.monad_bind_eq_bind,
    PMF.pure_bind, ProbComp.eval_bind, ProbComp.eval_uniform]
  refine Game.advantage_bind_le_nnreal _ _ _ fun α => ?_
  refine Game.advantage_bind_le_nnreal _ _ _ fun β => ?_
  refine Game.advantage_bind_le_nnreal _ _ _ fun γ => ?_
  have hword :
      ddhOTWordReduction F x_word D n
          (d n, F.encode (d n) (α • F.generator (d n)),
            F.encode (d n) (β • F.generator (d n)),
            F.encode (d n) (γ • F.generator (d n))) =
        ddhOTWordReduction F (fun _ => encodeDDHOTInputWord F (d n) x) D n
          (d n, F.encode (d n) (α • F.generator (d n)),
            F.encode (d n) (β • F.generator (d n)),
            F.encode (d n) (γ • F.generator (d n))) := by
    dsimp only [ddhOTWordReduction]
    rw [hx_eq]
  rw [hword]
  exact ddhOTWordReduction_smul_eq_typed F d n x D α β γ

/-! ### Concrete and asymptotic privacy theorems -/

/-- **Exact typed sender privacy**: for any group schedule `d`, any input `x`, and any
distinguisher `D`, the corrupted-sender (`{0}`) semi-honest advantage of `ddhOTProtocol` is
identically `0`. -/
theorem ddhOT_family_sender_advantage_zero (d : ℕ → F.Desc)
    (x : (n : ℕ) → (i : Fin 2) → OTIn (F.Carrier (d n)) i)
    [∀ n, DecidableEq (F.Carrier (d n))] (n : ℕ)
    (D : ((i : ↥({0} : Finset (Fin 2))) →
        PartyView (OTIn (F.Carrier (d n))) (DDHOTCoins (F.order (d n)))
          (ddhOTSchedule (F.Carrier (d n))) ↑i) ×
      ((i : Fin 2) → OTOut (F.Carrier (d n)) i) → ProbComp Bool) :
    semiHonestAdvantage (ddhOTProtocol (F.generator (d n)) (F.order (d n))) noOracleWorld
      (otFunctionality (F.Carrier (d n))) {0}
      (ddhOTSenderSim (F.generator (d n)) (F.order (d n))) (x n) D = 0 := by
  have : NeZero (F.order (d n)) := ⟨(F.prime_order (d n)).ne_zero⟩
  exact semiHonestAdvantage_ddhOT_sender (F.generator (d n)) (F.order (d n))
    (order_smul_eq_zero F (d n)) (x n) D

/-- **Asymptotic typed sender privacy**: `semiHonestAdvantage` for `ddhOTProtocol` against a
corrupted sender `{0}` vanishes identically, hence is negligible. -/
theorem ddhOT_asymptotic_sender_private (d : ℕ → F.Desc)
    (x : (n : ℕ) → (i : Fin 2) → OTIn (F.Carrier (d n)) i)
    [∀ n, DecidableEq (F.Carrier (d n))]
    (D : ℕ → List Bool × List Bool → ProbComp Bool) :
    Negligible fun n =>
      semiHonestAdvantage (ddhOTProtocol (F.generator (d n)) (F.order (d n))) noOracleWorld
        (otFunctionality (F.Carrier (d n))) {0}
        (ddhOTSenderSim (F.generator (d n)) (F.order (d n))) (x n)
        (fun r => D n (encodeDDHOTSenderJointPair F (d n) r)) :=
  negligible_of_le (negligible_const_div_two_pow 0) fun n => by
    rw [ddhOT_family_sender_advantage_zero]
    exact zero_le

/-- **Concrete statistical bound for word-level corrupted-sender privacy**: the strict-PPT
word-level execution `ddhOTRealWordRun` and simulator `ddhOTSenderSimWord` are within statistical
distinguishing distance `12 / 2 ^ n`. -/
theorem ddhOTWord_sender_advantage_le (d : ℕ → F.Desc) (n : ℕ)
    (x : (i : Fin 2) → OTIn (F.Carrier (d n)) i)
    (D : ℕ → List Bool × List Bool → ProbComp Bool) :
    Game.advantage
      (ProbComp.eval ((do
        let v_w ← ddhOTSenderSimWord F d (n, (encodeDDHOTInputWord F (d n) x).1)
        return (v_w, F.encode (d n) (otOutputs x 1))) >>= fun r => D n r))
      (ProbComp.eval (ddhOTRealWordRun F d (n, encodeDDHOTInputWord F (d n) x) >>=
        fun r => D n (r.1, ddhOTRunOut r))) ≤ 12 / 2 ^ n := by
  let : DecidableEq (F.Carrier (d n)) := Classical.decEq _
  have : NeZero (F.order (d n)) := ⟨(F.prime_order (d n)).ne_zero⟩
  have h1 := ddhOTSenderSimWord_advantage_le F d n x D
  have h2 := ddhOTRealWordRun_sender_advantage_le F d n x D
  have hid :
      ProbComp.eval (idealJoint (otFunctionality (F.Carrier (d n))) {0}
        (ddhOTSenderSim (F.generator (d n)) (F.order (d n))) x >>= fun r =>
          D n (encodeDDHOTSenderJointPair F (d n) r)) =
      (((ddhOTProtocol (F.generator (d n)) (F.order (d n))).realJoint noOracleWorld {0} x).bind
        fun r => ProbComp.eval (D n (encodeDDHOTSenderJointPair F (d n) r))) := by
    rw [ProbComp.eval_bind,
      idealJoint_ddhOT_sender (F.generator (d n)) (F.order (d n))
        (order_smul_eq_zero F (d n)) x]
  have hadv := Game.advantage_four_hop_le h1 h2
  rw [hid, Game.advantage_self, add_zero] at hadv
  refine hadv.trans ?_
  rw [← add_div, show (6 : ℝ≥0) + 6 = 12 by norm_num]

/-- **Asymptotic word-level privacy against a corrupted sender**: for any polynomial-time group
schedule `d`, `ddhOTRealWordRun` and `ddhOTSenderSimWord` are strict PPT and statistically
indistinguishable on all valid input families. -/
theorem ddhOTWord_asymptotic_sender_private {d : ℕ → F.Desc}
    (hd : ComputableInPolyTime d encUnary F.encDesc)
    (x : (n : ℕ) → (i : Fin 2) → OTIn (F.Carrier (d n)) i)
    (D : ℕ → List Bool × List Bool → ProbComp Bool) :
    IsPPTOn encDDHOTWordInput encDDHOTRunOut (ddhOTRealWordRun F d) ∧
    IsPPTOn encDDHOTWordPairInput encBits (ddhOTSenderSimWord F d) ∧
    Negligible fun n => Game.advantage
      (ProbComp.eval ((do
        let v_w ← ddhOTSenderSimWord F d (n, (encodeDDHOTInputWord F (d n) (x n)).1)
        return (v_w, F.encode (d n) (otOutputs (x n) 1))) >>= fun r => D n r))
      (ProbComp.eval (ddhOTRealWordRun F d (n, encodeDDHOTInputWord F (d n) (x n)) >>=
        fun r => D n (r.1, ddhOTRunOut r))) :=
  ⟨isPPTOn_ddhOTRealWordRun F hd, isPPTOn_ddhOTSenderSimWord F hd,
    negligible_of_le (negligible_const_div_two_pow 12)
      (fun n => ddhOTWord_sender_advantage_le F d n (x n) D)⟩

/-- **Concrete reduction from typed DDH-OT receiver privacy to word-level `DDH`**: bounds the
semi-honest receiver distinguishing advantage of `ddhOTProtocol` on `x n` by the `ddhRealGame` vs
`ddhIdealGame` advantage of `ddhOTWordReduction` plus `6 / 2 ^ n`. -/
theorem ddhOT_family_receiver_advantage_le (d : ℕ → F.Desc) (n : ℕ)
    [DecidableEq (F.Carrier (d n))] [Fintype (F.Carrier (d n))]
    (x_word : ℕ → (List Bool × List Bool) × Bool)
    (x : (i : Fin 2) → OTIn (F.Carrier (d n)) i)
    (hx_eq : x_word n = encodeDDHOTInputWord F (d n) x)
    (D : ℕ → List Bool × List Bool → ProbComp Bool) :
    semiHonestAdvantage (ddhOTProtocol (F.generator (d n)) (F.order (d n))) noOracleWorld
      (otFunctionality (F.Carrier (d n))) {1}
      (ddhOTReceiverSim (F.generator (d n)) (F.order (d n))) x
      (fun r => D n (encodeDDHOTReceiverJointPair F (d n) r)) ≤
      Game.advantage
        (F.ddhRealGame (fun k => PMF.pure (d k)) (ddhOTWordReduction F x_word D) n)
        (F.ddhIdealGame (fun k => PMF.pure (d k)) (ddhOTWordReduction F x_word D) n) +
      6 / 2 ^ n := by
  have : NeZero (F.order (d n)) := ⟨(F.prime_order (d n)).ne_zero⟩
  have hcard : Fintype.card (F.Carrier (d n)) = F.order (d n) := by
    rw [Fintype.card_eq_nat_card, F.card_carrier (d n)]
  rw [semiHonestAdvantage_ddhOT_receiver_eq (F.generator (d n)) (F.order (d n)) hcard
    (smul_generator_val_surjective F (d n))]
  have h1 := (Game.advantage_comm _ _).trans_le
    (ddhRealGame_ddhOTWordReduction_le F d n x_word x hx_eq D)
  have h2 := (Game.advantage_comm _ _).trans_le
    (ddhIdealGame_ddhOTWordReduction_le F d n x_word x hx_eq D)
  have hfour := Game.advantage_four_hop_le h1 h2
  refine hfour.trans ?_
  rw [add_assoc, add_comm (Game.advantage _ _), ← add_assoc, add_comm (3 / 2 ^ n + 3 / 2 ^ n),
    ← add_div, show (3 : ℝ≥0) + 3 = 6 by norm_num]

/-- **Concrete reduction from word-level DDH-OT receiver privacy to `DDH`**: bounds the word-level
distinguishing advantage between `ddhOTReceiverSimWord` and `ddhOTRealWordRun` by the `ddhRealGame`
vs `ddhIdealGame` advantage of `ddhOTWordReduction` plus `18 / 2 ^ n`. -/
theorem ddhOTWord_receiver_advantage_le (d : ℕ → F.Desc) (n : ℕ)
    (x_word : ℕ → (List Bool × List Bool) × Bool)
    (x : (i : Fin 2) → OTIn (F.Carrier (d n)) i)
    (hx_eq : x_word n = encodeDDHOTInputWord F (d n) x)
    (D : ℕ → List Bool × List Bool → ProbComp Bool) :
    Game.advantage
      (ProbComp.eval ((do
        let σ := x 1
        let m_σ_w := F.encode (d n) (otOutputs x 1)
        let v_w ← ddhOTReceiverSimWord F d (n, σ, m_σ_w)
        return (v_w, m_σ_w)) >>= fun r => D n r))
      (ProbComp.eval (ddhOTRealWordRun F d (n, encodeDDHOTInputWord F (d n) x) >>=
        fun r => D n (ddhOTRunReceiverView r, ddhOTRunOut r))) ≤
      Game.advantage
        (F.ddhRealGame (fun k => PMF.pure (d k)) (ddhOTWordReduction F x_word D) n)
        (F.ddhIdealGame (fun k => PMF.pure (d k)) (ddhOTWordReduction F x_word D) n) +
      18 / 2 ^ n := by
  let : DecidableEq (F.Carrier (d n)) := Classical.decEq _
  let : Fintype (F.Carrier (d n)) := carrierFintype F (d n)
  have : NeZero (F.order (d n)) := ⟨(F.prime_order (d n)).ne_zero⟩
  have hsim := ddhOTReceiverSimWord_advantage_le F d n x D
  have hreal := ddhOTRealWordRun_receiver_advantage_le F d n x D
  have hmid :
      Game.advantage
        (ProbComp.eval (idealJoint (otFunctionality (F.Carrier (d n))) {1}
          (ddhOTReceiverSim (F.generator (d n)) (F.order (d n))) x >>= fun r =>
            D n (encodeDDHOTReceiverJointPair F (d n) r)))
        (((ddhOTProtocol (F.generator (d n)) (F.order (d n))).realJoint noOracleWorld {1} x).bind
          fun r => ProbComp.eval (D n (encodeDDHOTReceiverJointPair F (d n) r))) ≤
      Game.advantage
        (F.ddhRealGame (fun k => PMF.pure (d k)) (ddhOTWordReduction F x_word D) n)
        (F.ddhIdealGame (fun k => PMF.pure (d k)) (ddhOTWordReduction F x_word D) n) +
      6 / 2 ^ n := by
    simpa only [semiHonestAdvantage, ProbComp.eval_bind] using
      ddhOT_family_receiver_advantage_le F d n x_word x hx_eq D
  have hfour := Game.advantage_four_hop_le hsim hreal
  have hsum :
      6 / 2 ^ n + (Game.advantage
        (F.ddhRealGame (fun k => PMF.pure (d k)) (ddhOTWordReduction F x_word D) n)
        (F.ddhIdealGame (fun k => PMF.pure (d k)) (ddhOTWordReduction F x_word D) n) +
        6 / 2 ^ n) + 6 / 2 ^ n =
      Game.advantage
        (F.ddhRealGame (fun k => PMF.pure (d k)) (ddhOTWordReduction F x_word D) n)
        (F.ddhIdealGame (fun k => PMF.pure (d k)) (ddhOTWordReduction F x_word D) n) +
      18 / 2 ^ n := by
    calc
      6 / 2 ^ n + (Game.advantage
          (F.ddhRealGame (fun k => PMF.pure (d k)) (ddhOTWordReduction F x_word D) n)
          (F.ddhIdealGame (fun k => PMF.pure (d k)) (ddhOTWordReduction F x_word D) n) +
          6 / 2 ^ n) + 6 / 2 ^ n
        = Game.advantage
            (F.ddhRealGame (fun k => PMF.pure (d k)) (ddhOTWordReduction F x_word D) n)
            (F.ddhIdealGame (fun k => PMF.pure (d k)) (ddhOTWordReduction F x_word D) n) +
            (6 / 2 ^ n + 6 / 2 ^ n + 6 / 2 ^ n) := by ring
      _ = Game.advantage
            (F.ddhRealGame (fun k => PMF.pure (d k)) (ddhOTWordReduction F x_word D) n)
            (F.ddhIdealGame (fun k => PMF.pure (d k)) (ddhOTWordReduction F x_word D) n) +
            18 / 2 ^ n := by
          rw [← add_div, ← add_div, show (6 : ℝ≥0) + 6 + 6 = 18 by norm_num]
  exact hfour.trans ((add_le_add (add_le_add le_rfl hmid) le_rfl).trans hsum.le)

/-- **Asymptotic typed privacy against a corrupted receiver**: under `PrimeOrderGroupFamily.DDH`,
for any polynomial-time computable group-element input family `x` and uniform strict-PPT
distinguisher `D`, the corrupted-receiver (`{1}`) `semiHonestAdvantage` of `ddhOTProtocol` is
negligible. -/
theorem ddhOT_asymptotic_receiver_private {d : ℕ → F.Desc}
    (hDDH : F.DDH fun n => PMF.pure (d n))
    (x : (n : ℕ) → (i : Fin 2) → OTIn (F.Carrier (d n)) i)
    [∀ n, DecidableEq (F.Carrier (d n))] [∀ n, Fintype (F.Carrier (d n))]
    (hx : ComputableInPolyTime (fun n => encodeDDHOTInputWord F (d n) (x n))
      encUnary encDDHOTWordPair)
    (D : ℕ → List Bool × List Bool → ProbComp Bool)
    (hD : IsPPTOn encDDHOTWordPairInput encBool (fun p => D p.1 p.2)) :
    Negligible fun n =>
      semiHonestAdvantage (ddhOTProtocol (F.generator (d n)) (F.order (d n))) noOracleWorld
        (otFunctionality (F.Carrier (d n))) {1}
        (ddhOTReceiverSim (F.generator (d n)) (F.order (d n))) (x n)
        (fun r => D n (encodeDDHOTReceiverJointPair F (d n) r)) := by
  let x_word := fun n => encodeDDHOTInputWord F (d n) (x n)
  have hddh := hDDH _ (isPPTOn_ddhOTWordReduction F hx hD)
  have h6 : Negligible fun n => (6 : ℝ≥0) / 2 ^ n := negligible_const_div_two_pow 6
  exact negligible_of_le (hddh.add h6) fun n =>
    ddhOT_family_receiver_advantage_le F d n x_word (x n) rfl D

/-- **Asymptotic word-level privacy against a corrupted receiver**: under
`PrimeOrderGroupFamily.DDH`, the strict-PPT word-level protocol `ddhOTRealWordRun` and simulator
`ddhOTReceiverSimWord` are computationally indistinguishable on every polynomial-time computable
group-element input family `x`. -/
theorem ddhOTWord_asymptotic_receiver_private {d : ℕ → F.Desc}
    (hDDH : F.DDH fun n => PMF.pure (d n))
    (hd : ComputableInPolyTime d encUnary F.encDesc)
    (x : (n : ℕ) → (i : Fin 2) → OTIn (F.Carrier (d n)) i)
    (hx : ComputableInPolyTime (fun n => encodeDDHOTInputWord F (d n) (x n))
      encUnary encDDHOTWordPair)
    (D : ℕ → List Bool × List Bool → ProbComp Bool)
    (hD : IsPPTOn encDDHOTWordPairInput encBool (fun p => D p.1 p.2)) :
    IsPPTOn encDDHOTWordInput encDDHOTRunOut (ddhOTRealWordRun F d) ∧
    IsPPTOn (encPair encUnary (encPair encBool encBits)) encBits (ddhOTReceiverSimWord F d) ∧
    Negligible fun n => Game.advantage
      (ProbComp.eval ((do
        let σ := x n 1
        let m_σ_w := F.encode (d n) (otOutputs (x n) 1)
        let v_w ← ddhOTReceiverSimWord F d (n, σ, m_σ_w)
        return (v_w, m_σ_w)) >>= fun r => D n r))
      (ProbComp.eval (ddhOTRealWordRun F d (n, encodeDDHOTInputWord F (d n) (x n)) >>=
        fun r => D n (ddhOTRunReceiverView r, ddhOTRunOut r))) := by
  let x_word := fun n => encodeDDHOTInputWord F (d n) (x n)
  have hddh := hDDH _ (isPPTOn_ddhOTWordReduction F hx hD)
  have h18 : Negligible fun n => (18 : ℝ≥0) / 2 ^ n := negligible_const_div_two_pow 18
  exact ⟨isPPTOn_ddhOTRealWordRun F hd, isPPTOn_ddhOTReceiverSimWord F hd,
    negligible_of_le (hddh.add h18) fun n =>
      ddhOTWord_receiver_advantage_le F d n x_word (x n) rfl D⟩

end Cslib.Crypto.Protocols.MPC
