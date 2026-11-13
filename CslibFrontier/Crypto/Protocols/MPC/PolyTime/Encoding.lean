/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.MPC.PolyTime.RunEncoded
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure

/-!
# Family Inputs, View Encodings and Efficiency Predicates for the GMW Completeness Theorem

This module fixes the word-level interface of the uniform efficiency claims in
`Cslib.Crypto.Protocols.MPC.PolyTime`. A family instance is packaged with its party inputs
(`FamilyRunInput`) or with a coalition's inputs and outputs (`FamilySimInput`), records encoded
injectively as bit lists by `enc_structure`. Party views of `gmwOT14RandomizedProtocol` are
encoded by `encGMWPartyView`, and coalition view tuples by `encodeCoalitionView`. The named
predicates `Protocol.Family.IsOraclePPT` and `CoalitionSimulator.Family.IsPPT` state uniform
efficiency of a protocol family's joint word-level runner and of a coalition simulator family.

## Main definitions

* `Cslib.Crypto.Protocols.MPC.FamilyRunInput`, `Cslib.Crypto.Protocols.MPC.FamilySimInput`,
  `Cslib.Crypto.Protocols.MPC.encFamilyRunInput`, `Cslib.Crypto.Protocols.MPC.encFamilySimInput`:
  family input records and their injective bit-list encodings.
* `Cslib.Crypto.Protocols.MPC.encGMWPartyView`, `Cslib.Crypto.Protocols.MPC.encodeCoalitionView`:
  word-level view encoders for `gmwOT14RandomizedProtocol` and `gmwOT14RandomizedSim`.
* `Cslib.Crypto.Protocols.MPC.Protocol.Family.IsOraclePPT`,
  `Cslib.Crypto.Protocols.MPC.CoalitionSimulator.Family.IsPPT`: uniform efficiency of a
  protocol family's joint word-level runner and of a coalition simulator family.

## References

* [O. Goldreich, *Foundations of Cryptography, Volume 2: Basic Applications*][Goldreich2004],
  Section 7.3.2 (Eq. 7.20, p. 640), Section 7.3.3 (Construction 7.3.7, pp. 643–644),
  Section 7.3.4 (Theorem 7.3.11, p. 648), Section 7.5.1.2 (Definition 7.5.1, Eqs. 7.39–7.40,
  p. 696; p. 697), Section 7.5.2.1 (p. 703), Section 7.5.2.2 (Construction 7.5.8, p. 704),
  Section 7.5.2.3 (Construction 7.5.10, p. 706), and Section 7.5.2.4 (Theorem 7.5.12, p. 707).
-/

public section

namespace Cslib.Crypto.Protocols.MPC

open Cslib.Probability Cslib.ProbComp Cslib.Circuits Turing.MultiTapeTM

/-! ### Family input records and `encGMWPartyView` -/

/-- Input record for executing a protocol family: the instance `index : α` and the `n index`-bit
party inputs. -/
structure FamilyRunInput (α : Type) (m : ℕ) (n : α → ℕ) where
  /-- The instance of the family. -/
  index : α
  /-- The party inputs. -/
  inputs : Fin m → BitString (n index)

/-- Input record for running a coalition simulator family: the instance `index : α` with the
coalition's `n index`-bit inputs and `k index`-bit outputs. -/
structure FamilySimInput (α : Type) (m : ℕ) (n k : α → ℕ) (I : Finset (Fin m)) where
  /-- The instance of the family. -/
  index : α
  /-- The coalition's inputs. -/
  inputs : (i : I) → BitString (n index)
  /-- The coalition's outputs. -/
  outputs : (i : I) → BitString (k index)

/-- Pad a coalition-indexed bitstring tuple `vI : (i : I) → BitString len` with `0` outside `I`
and serialize the resulting `m` blocks of width `len` to a `m * len`-bit list. -/
@[expose] def extendCoalitionBits {m len : ℕ} (I : Finset (Fin m)) (vI : (i : I) → BitString len) :
    List Bool :=
  List.ofFn ((Cslib.BitString.blocksEquiv (α := Bool) (m := m) (k := len)).symm
    (GMWCircuit.extendByZero I vI))

/-- Zero-extension and serialization of coalition tuples is injective. -/
theorem extendCoalitionBits_injective {m len : ℕ} (I : Finset (Fin m)) :
    Function.Injective (extendCoalitionBits (len := len) I) := by
  intro u v h
  have h1 := Cslib.BitString.blocksEquiv.symm.injective (List.ofFn_injective h)
  ext ⟨i, hi⟩ j
  have hi_eq := congrFun h1 i
  simp only [GMWCircuit.extendByZero, hi, ↓reduceDIte] at hi_eq
  exact congrFun hi_eq j

section FamilyInputEncodings

variable {α : Type}

/-- Injective bit-list encoding of `FamilyRunInput α m n`: pairs `enc index` with the packed
`m * n index` party input bits `List.ofFn (BitString.blocksEquiv.symm inputs)`. -/
enc_structure encFamilyRunInput (enc : α ↪ List Bool) (m : ℕ) (n : α → ℕ) :
    FamilyRunInput α m n where
  index : enc,
  inputs :
    (fun x : Fin m → BitString (n index) =>
      List.ofFn ((Cslib.BitString.blocksEquiv (α := Bool) (m := m) (k := n index)).symm x))
    using (List.ofFn_injective.comp Cslib.BitString.blocksEquiv.symm.injective)

/-- Injective bit-list encoding of `FamilySimInput α m n k I`: pairs `enc index` with the
zero-extended packed coalition input bits `extendCoalitionBits I inputs` and output bits
`extendCoalitionBits I outputs`. -/
enc_structure encFamilySimInput (enc : α ↪ List Bool) (m : ℕ) (n : α → ℕ) (k : α → ℕ)
    (I : Finset (Fin m)) : FamilySimInput α m n k I where
  index : enc,
  inputs : (extendCoalitionBits (len := n index) I)
    using (extendCoalitionBits_injective (len := n index) I),
  outputs : (extendCoalitionBits (len := k index) I)
    using (extendCoalitionBits_injective (len := k index) I)

end FamilyInputEncodings

/-- Serialize party `i`'s `twoPartyMulProtocol` subcoins along any `sharedMulSpec 2` schedule `sc`:
appends `[c_head 0 h]` at each `.oracle () parties` round where `parties 0 = i`. -/
private def encOTSubCoins {m : ℕ} :
    (sc : Schedule m (sharedMulSpec 2)) → (i : Fin m) →
      Schedule.SubCoins (spec₁ := sharedMulSpec 2)
        (fun _ : Unit => Fin.cases Bool (fun _ => Unit)) sc i → List Bool
  | [], _, () => []
  | .message _ _ _ :: sc, i, c => encOTSubCoins sc i c
  | .oracle () parties :: sc, i, (c_head, c_tail) =>
    (if h : parties 0 = i then ([c_head 0 h] : List Bool) else []) ++ encOTSubCoins sc i c_tail

/-- Serialize party `i`'s received `ot14Spec` oracle answers along
`Schedule.compose (fun _ => twoPartyMulSchedule) sc`: appends `[r_head 1 h]` at each
`.oracle () parties` round where `parties 1 = i`. -/
private def encOTOracleAnswers {m : ℕ} :
    (sc : Schedule m (sharedMulSpec 2)) → (i : Fin m) →
      (Schedule.compose (fun _ => twoPartyMulSchedule) sc).Received i → List Bool
  | [], _, () => []
  | .message _ _ _ :: sc, i, (_, r_tail) => encOTOracleAnswers sc i r_tail
  | .oracle () parties :: sc, i, (r_head, r_tail) =>
    (if h : parties 1 = i then ([r_head 1 h] : List Bool) else []) ++ encOTOracleAnswers sc i r_tail

/-- Double schedule composition from `sharedMulSpec m` to `ot14Spec` via `multiPartyMulSchedule m`
and `twoPartyMulSchedule`. -/
@[reducible] private def otMulCompose {m : ℕ} (sc : Schedule m (sharedMulSpec m)) :
    Schedule m ot14Spec :=
  Schedule.compose (fun _ => twoPartyMulSchedule)
    (Schedule.compose (fun _ => multiPartyMulSchedule m) sc)

/-- Split a received transcript along `((pairsSchedule L).map (Round.embed parties) ++ rest₁)`
composed with `twoPartyMulSchedule`. -/
private def splitPairsOTReceived {m : ℕ} {α : Type} (parties : Fin m ↪ Fin m) (i : Fin m) :
    (L : List (OrderedPair m)) → {rest₁ rest₂ : Schedule m (sharedMulSpec 2)} →
      ((Schedule.compose (fun _ => twoPartyMulSchedule) rest₁).Received i →
        (Schedule.compose (fun _ => twoPartyMulSchedule) rest₂).Received i × α) →
      (Schedule.compose (fun _ => twoPartyMulSchedule)
        ((pairsSchedule L).map (Round.embed parties) ++ rest₁)).Received i →
      (Schedule.compose (fun _ => twoPartyMulSchedule)
        ((pairsSchedule L).map (Round.embed parties) ++ rest₂)).Received i × α
  | [], _, _, k, r => k r
  | _ :: L, _, _, k, (r_head, r_tail) =>
    let p := splitPairsOTReceived parties i L k r_tail
    ((r_head, p.1), p.2)

/-- Split a received transcript along `otMulCompose (a ++ b)` into transcripts along
`otMulCompose a` and `otMulCompose b`. -/
private def splitOTMulCompose {m : ℕ} :
    (a b : Schedule m (sharedMulSpec m)) → (i : Fin m) →
      (otMulCompose (a ++ b)).Received i →
      (otMulCompose a).Received i × (otMulCompose b).Received i
  | [], _, _, r => ((), r)
  | .message _ _ _ :: a, b, i, (r_head, r_tail) =>
    let p := splitOTMulCompose a b i r_tail
    ((r_head, p.1), p.2)
  | .oracle () parties :: a, b, i, r =>
    splitPairsOTReceived parties i (orderedPairs m) (splitOTMulCompose a b i) r

/-- Serialize party `i`'s Step 1 received share messages along
`msgSchedule (BitString N) L`. -/
private def encPairsMsgReceived {m N : ℕ} (i : Fin m) :
    (L : List (Fin m × Fin m)) →
      (otMulCompose (msgSchedule (spec := sharedMulSpec m) (BitString N) L)).Received i →
      List Bool
  | [], () => []
  | p :: L, (r_head, r_tail) =>
    (if h : i = p.2 then List.ofFn (r_head h) else []) ++ encPairsMsgReceived i L r_tail

/-- Skip one expanded `multiPartyMulSchedule m` block of `ot14Spec` oracle answers. -/
private def dropPairsOTReceived {m : ℕ} (parties : Fin m ↪ Fin m) (i : Fin m) :
    (L : List (OrderedPair m)) → {rest : Schedule m (sharedMulSpec 2)} →
      (Schedule.compose (fun _ => twoPartyMulSchedule)
        ((pairsSchedule L).map (Round.embed parties) ++ rest)).Received i →
      (Schedule.compose (fun _ => twoPartyMulSchedule) rest).Received i
  | [], _, r => r
  | _ :: L, _, (_, r_tail) => dropPairsOTReceived parties i L r_tail

/-- Serialize party `i`'s received bits along `gatherSchedule m recipient S`. -/
private def encGatherOTReceived {m : ℕ} (recipient i : Fin m) :
    (S : List (Fin m)) →
      (otMulCompose (GMWCircuit.gatherSchedule m recipient S)).Received i → List Bool
  | [], () => []
  | _ :: S, (r_head, r_tail) =>
    (if h : i = recipient then [r_head h] else []) ++ encGatherOTReceived recipient i S r_tail

/-- Serialize party `i`'s Step 3 received output-share messages along `outCoordsSchedule m L`. -/
private def encOutCoordsMsgReceived {m k : ℕ} (i : Fin m) :
    (L : List (Fin m × Fin k)) →
      (otMulCompose (GMWCircuit.outCoordsSchedule m L)).Received i → List Bool
  | [], () => []
  | coord :: L, r =>
    let r_after_ot :=
      dropPairsOTReceived (Function.Embedding.refl (Fin m)) i (orderedPairs m) r
    let (r_gather, r_rest) :=
      splitOTMulCompose (GMWCircuit.gatherSchedule m coord.1 (List.finRange m))
        (GMWCircuit.outCoordsSchedule m L) i r_after_ot
    encGatherOTReceived coord.1 i (List.finRange m) r_gather ++
      encOutCoordsMsgReceived i L r_rest

/-- The view word of a `gmwOT14RandomizedProtocol` party from its seven component words: input,
wrapper coins, Step 1 coins, $\text{OT}_1^4$ sender coins, Step 1 received shares,
$\text{OT}_1^4$ answers and Step 3 received shares. -/
private def gmwViewWord
    (input coins circuitCoins otCoins inShares otAnswers outShares : List Bool) : List Bool :=
  encPair
    (encPair (encPair encBits encBits) (encPair encBits encBits))
    (encPair encBits (encPair encBits encBits))
    (((input, coins), (circuitCoins, otCoins)), (inShares, (otAnswers, outShares)))

/-- Serialize party `i`'s complete `PartyView` in `gmwOT14RandomizedProtocol m coins n k C` to a
`List Bool` encoding:
- `v.input : BitString n`
- `v.coins.1 : BitString coins` (randomized-wrapper coin share)
- `v.coins.2.1.1 : Fin (n + coins) → Fin (m - 1) → Bool` (Step 1 input-sharing coins)
- `encOTSubCoins _ i v.coins.2.2` (Step 2 & Step 3 $\text{OT}_1^4$ sender coins)
- Step 1 received input shares (`encPairsMsgReceived`)
- Step 2 & Step 3 received $\text{OT}_1^4$ receiver answers (`encOTOracleAnswers`)
- Step 3 received output-reconstruction shares (`encOutCoordsMsgReceived`). -/
def encGMWPartyView (m coins n k : ℕ)
    (C : Cslib.Circuits.Circuit Boolean.signature (m * n + coins) (m * k)) (i : Fin m)
    (v : PartyView (fun _ => BitString n)
      (fun j => BitString coins ×
        Schedule.ComposedCoins (spec₁ := sharedMulSpec 2)
          (fun _ : Unit => Fin.cases Bool (fun _ => Unit))
          (Schedule.ComposedCoins (spec₁ := sharedMulSpec m)
            (fun _ : Unit => fun _ => Unit)
            (fun _ => Fin (n + coins) → Fin (m - 1) → Bool)
            (gmwCircuitSchedule m (n + coins) k (C.comp (xorPreludeCircuit m n coins))))
          (Schedule.compose (fun _ => multiPartyMulSchedule m)
            (gmwCircuitSchedule m (n + coins) k (C.comp (xorPreludeCircuit m n coins)))) j)
      (Schedule.compose (fun _ => twoPartyMulSchedule)
        (Schedule.compose (fun _ => multiPartyMulSchedule m)
          (gmwCircuitSchedule m (n + coins) k (C.comp (xorPreludeCircuit m n coins))))) i) :
    List Bool :=
  let N := n + coins
  let D := C.comp (xorPreludeCircuit m n coins)
  let (r_in, r_prog_out) :=
    splitOTMulCompose (GMWCircuit.inputShareSchedule m N)
      (GMWCircuit.progSchedule m D.program ++ GMWCircuit.outputSchedule m k) i v.received
  let (_, r_out) :=
    splitOTMulCompose (GMWCircuit.progSchedule m D.program)
      (GMWCircuit.outputSchedule m k) i r_prog_out
  let (preludeCoins, (circuitCoins, _), otSubCoins) := v.coins
  gmwViewWord (List.ofFn v.input) (List.ofFn preludeCoins)
    (List.ofFn ((Cslib.BitString.blocksEquiv (α := Bool) (m := N) (k := m - 1)).symm circuitCoins))
    (encOTSubCoins _ i otSubCoins) (encPairsMsgReceived i (allPairs m) r_in)
    (encOTOracleAnswers _ i v.received) (encOutCoordsMsgReceived i (GMWCircuit.outCoords m k) r_out)

/-- Encode a coalition view tuple `vI : (i : I) → PartyView In Coins sc i.1` into `List Bool`
by listing `encView i (vI ⟨i, hi⟩)` for `i ∈ I` and `[]` for `i ∉ I`. -/
@[expose] def encodeCoalitionView {m : ℕ} {spec : MultiOracleSpec} {sc : Schedule m spec}
    {In Coins : Fin m → Type}
    (encView : (i : Fin m) → PartyView In Coins sc i → List Bool)
    (I : Finset (Fin m)) (vI : (i : I) → PartyView In Coins sc i.1) : List Bool :=
  encList encBits
    ((List.finRange m).map fun i => if hi : i ∈ I then encView i (vI ⟨i, hi⟩) else [])

/-! ### Named efficiency predicates for protocol and simulator families -/

/-- A family of `m`-party $\text{OT}_1^4$-hybrid protocols `proto a`, indexed by `a : α` with
`n a`-bit party inputs, has a uniform oracle-PPT joint word-level execution: the centralized runner
`Protocol.runEncoded`, with party views encoded by `encView a` and outputs by `encOut a`, is
`Cslib.Probability.IsOraclePPTOn` over the family input encoding `encFamilyRunInput enc m n`. One
machine and clock serve every instance, and the runner is charged for the whole family input. This
certifies the joint execution across all parties rather than separate per-party strategies. -/
@[expose] def Protocol.Family.IsOraclePPT {α : Type} (enc : α ↪ List Bool) (m : ℕ) (n : α → ℕ)
    {sc : α → Schedule m ot14Spec} {Coins Out : α → Fin m → Type}
    (proto : (a : α) → Protocol m ot14Spec (sc a) (fun _ => BitString (n a)) (Coins a) (Out a))
    (encView : (a : α) → (i : Fin m) →
      PartyView (fun _ => BitString (n a)) (Coins a) (sc a) i → List Bool)
    (encOut : (a : α) → (i : Fin m) → Out a i → List Bool) : Prop :=
  Cslib.Probability.IsOraclePPTOn (encFamilyRunInput enc m n) encBits
    fun inp => (proto inp.index).runEncoded (encView inp.index) (encOut inp.index) inp.inputs

/-- A family of coalition-`I` simulators `S a`, indexed by `a : α` with `n a`-bit party inputs and
`k a`-bit party outputs, is uniformly PPT: on the family input encoding `encFamilySimInput enc m n k
I`, sampling the simulated coalition views and encoding them with `encodeCoalitionView (encView a)
I` is `Cslib.Probability.IsPPTOn`. -/
@[expose] def CoalitionSimulator.Family.IsPPT {α : Type} (enc : α ↪ List Bool) (m : ℕ)
    (n k : α → ℕ) {spec : MultiOracleSpec} {sc : α → Schedule m spec} {Coins : α → Fin m → Type}
    (I : Finset (Fin m))
    (encView : (a : α) → (i : Fin m) →
      PartyView (fun _ => BitString (n a)) (Coins a) (sc a) i → List Bool)
    (S : (a : α) →
      CoalitionSimulator (sc a) (fun _ => BitString (n a)) (Coins a) (fun _ => BitString (k a)) I) :
    Prop :=
  Cslib.Probability.IsPPTOn (encFamilySimInput enc m n k I) encBits
    fun inp => encodeCoalitionView (encView inp.index) I <$> S inp.index inp.inputs inp.outputs

end Cslib.Crypto.Protocols.MPC
