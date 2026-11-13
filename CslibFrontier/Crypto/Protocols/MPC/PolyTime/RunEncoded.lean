/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.MPC.Composition
public import CslibFrontier.Computability.Probabilistic.Oracle.Composition
public import CslibFrontier.Languages.Probabilistic.Oracle.Interaction

/-!
# Word-Level Execution of $\text{OT}_1^4$-Hybrid Protocols

This module runs an `ot14Spec`-hybrid protocol as a word-level oracle program in
`Cslib.Probability.WordOracleComp Unit (List Bool)`: each typed `ot14Spec` query becomes a 6-bit
word query to `ot14WordHandler`, whose 1-bit reply prefix is decoded back to the typed answer.
The bridge lemma `Protocol.eval_runEncoded_eq_evalWith_map` identifies the word-level run with the
typed execution `Protocol.evalWith ot14World`. It also defines the word-encoded randomized
functionality family that the completeness theorem in `Cslib.Crypto.Protocols.MPC.PolyTime`
compiles.

## Main definitions

* `Cslib.Crypto.Protocols.MPC.encodeCoinsAndInputs`,
  `Cslib.Crypto.Protocols.MPC.wordRandomizedFunctionality`: word-encoded `m`-party randomized
  functionality family induced by `F : α × List Bool → List Bool`.
* `Cslib.Crypto.Protocols.MPC.encodeOT14Query`, `Cslib.Crypto.Protocols.MPC.ot14WordHandler`,
  `Cslib.Crypto.Protocols.MPC.decodeOT14Reply`: 6-bit query encoding and stateful word-oracle
  handler for `ot14World` (Section 7.3.2, Eq. 7.20, p. 640).
* `Cslib.Crypto.Protocols.MPC.Steps.runEncoded`, `Cslib.Crypto.Protocols.MPC.Protocol.runEncoded`,
  `Cslib.Crypto.Protocols.MPC.encodeViewsAndOutputs`: generic word-level protocol runner in
  `WordOracleComp Unit (List Bool)`.

## Main results

* `Cslib.Crypto.Protocols.MPC.Steps.runEncoded_mapState`,
  `Cslib.Crypto.Protocols.MPC.Steps.runEncoded_append`,
  `Cslib.Crypto.Protocols.MPC.Steps.runEncoded_embed`: `Steps.runEncoded` commutes with
  relabelling states, concatenating steps and embedding a sub-protocol's parties.
* `Cslib.Crypto.Protocols.MPC.Steps.runWith_runEncoded_eq_evalWith`,
  `Cslib.Crypto.Protocols.MPC.Protocol.eval_runEncoded_eq_evalWith_map`: bridge lemmas relating
  `Steps.runEncoded` / `Protocol.runEncoded` under `ot14WordHandler` to `evalWith ot14World`.

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

/-! ### Part 1: Word-Level Functionality, `ot14Spec` Word Handler, and `Protocol.runEncoded` -/

/-- Encode `x : Fin m → BitString n` and shared coin tape `r : BitString coins` as the
`m * n + coins`-bit list `List.ofFn (Fin.append (BitString.blocksEquiv.symm x) r)`. -/
@[expose] def encodeCoinsAndInputs (m coins n : ℕ) (r : BitString coins)
    (x : Fin m → BitString n) : List Bool :=
  List.ofFn (Fin.append ((Cslib.BitString.blocksEquiv (α := Bool) (m := m) (k := n)).symm x) r)

/-- Randomized `m`-party functionality family induced by a word-level function
`F : α × List Bool → List Bool` with `coins a` random bits, `n a`-bit party inputs, and `k a`-bit
party outputs. -/
@[expose] noncomputable def wordRandomizedFunctionality {α : Type} (m : ℕ)
    (coins n k : α → ℕ) (F : α × List Bool → List Bool) (a : α) :
    Functionality m (fun _ => BitString (n a)) (fun _ => BitString (k a)) :=
  randomizedFunctionality (coins a) (fun r x i j =>
    (F (a, encodeCoinsAndInputs m (coins a) (n a) r x)).getD (i.val * k a + j.val) false)

/-- Serialize a typed `ot14Spec` query `q : (s : Fin 2) → ot14Spec.Query () s` as a 6-bit word:
the sender's four table bits `q 0 0, q 0 1, q 0 2, q 0 3` followed by the receiver's two selector
bits `(fin4ToBoolPair (q 1)).1, (fin4ToBoolPair (q 1)).2`. -/
@[expose] def encodeOT14Query (q : (s : Fin 2) → ot14Spec.Query () s) : List Bool :=
  [q 0 0, q 0 1, q 0 2, q 0 3, (fin4ToBoolPair (q 1)).1, (fin4ToBoolPair (q 1)).2]

/-- Stateful word-oracle handler realizing `ot14World` on 6-bit requests produced by
`encodeOT14Query`: returns the selected sender bit `[req.getD idx false]` while leaving the `Unit`
state unchanged. -/
@[expose] noncomputable def ot14WordHandler : Unit × List Bool → StateT Unit PMF (List Bool) :=
  fun (_, req) s =>
    let idx := boolPairToFin4 (req.getD 4 false, req.getD 5 false)
    PMF.pure ([req.getD idx.val false], s)

@[simp] private theorem boolPairToFin4_fin4ToBoolPair (idx : Fin 4) :
    boolPairToFin4 (fin4ToBoolPair idx) = idx := by
  fin_cases idx <;> decide

private theorem ot14WordHandler_encodeOT14Query (q : (s : Fin 2) → ot14Spec.Query () s)
    (s : Unit) :
    ot14WordHandler ((), encodeOT14Query q) s = PMF.pure ([q 0 (q 1)], s) := by
  dsimp [ot14WordHandler, encodeOT14Query]
  have h45 :
      boolPairToFin4
        ([q 0 0, q 0 1, q 0 2, q 0 3, (fin4ToBoolPair (q 1)).1, (fin4ToBoolPair (q 1)).2].getD 4
          false,
         [q 0 0, q 0 1, q 0 2, q 0 3, (fin4ToBoolPair (q 1)).1, (fin4ToBoolPair (q 1)).2].getD 5
          false) = q 1 := by
    simpa using boolPairToFin4_fin4ToBoolPair (q 1)
  rw [h45]
  rcases hq : q 1 with ⟨val, isLt⟩
  interval_cases val <;> rfl

/-- Decode a 1-bit word-oracle reply `rep : List Bool` into an `ot14Spec` answer tuple:
returns `()` to slot `0` and `rep.headD false` to slot `1`. -/
@[expose] def decodeOT14Reply (rep : List Bool) : (s : Fin 2) → ot14Spec.Answer () s :=
  Fin.cases () (fun _ => rep.headD false)

@[simp] private theorem ot14Answer_eq (q : (s : Fin 2) → ot14Spec.Query () s) :
    ot14Answer q = Fin.cases () (fun _ => q 0 (q 1)) := rfl

/-- Execute `steps : Steps State Out sc` over `ot14Spec` in `WordOracleComp Unit`, translating each
`.oracle` round into a 1-bit `ProbOracleComp.query` call with payload `encodeOT14Query`. -/
@[expose] def Steps.runEncoded {m : ℕ} {State Out : Fin m → Type} {sc : Schedule m ot14Spec}
    (steps : Steps State Out sc) (st : (i : Fin m) → State i) :
    WordOracleComp Unit ((i : Fin m) → sc.Received i) :=
  match steps with
  | .done _ => pure (fun _ => ())
  | .message (sender := sender) send next => do
    let r_head : (i : Fin m) → _ := Round.deliverMessage (send (st sender))
    let r_tail ← next.runEncoded (fun i => (st i, r_head i))
    return fun i => (r_head i, r_tail i)
  | .oracle (parties := parties) query next => do
    let rep ← List.take 1 <$>
      ProbOracleComp.query (spec := fun _ : Unit × List Bool => List Bool)
        ((), encodeOT14Query (fun s => query s (st (parties s))))
    let ans := decodeOT14Reply rep
    let r_head : (i : Fin m) → _ := Round.deliverOracle parties ans
    let r_tail ← next.runEncoded (fun i => (st i, r_head i))
    return fun i => (r_head i, r_tail i)

/-- Encode a complete `(views, outputs)` execution outcome into a single bit string `List Bool`
by pairing the framed list of all `m` encoded party views with the framed list of all `m` encoded
party outputs. -/
@[expose] def encodeViewsAndOutputs {m : ℕ} {spec : MultiOracleSpec} {sc : Schedule m spec}
    {In Coins Out : Fin m → Type}
    (encView : (i : Fin m) → PartyView In Coins sc i → List Bool)
    (encOut : (i : Fin m) → Out i → List Bool)
    (vo : ((i : Fin m) → PartyView In Coins sc i) × ((i : Fin m) → Out i)) : List Bool :=
  encPair (encList encBits) (encList encBits)
    ((List.finRange m).map (fun i => encView i (vo.1 i)),
     (List.finRange m).map (fun i => encOut i (vo.2 i)))

/-- Generic word-level execution of `proto.run x` in `WordOracleComp Unit (List Bool)`, translating
each `ot14Spec` query to a word-oracle call and encoding the resulting `(views, outputs)` pair
via `(encView, encOut)`. -/
@[expose] def Protocol.runEncoded {m : ℕ} {sc : Schedule m ot14Spec} {In Coins Out : Fin m → Type}
    (encView : (i : Fin m) → PartyView In Coins sc i → List Bool)
    (encOut : (i : Fin m) → Out i → List Bool)
    (proto : Protocol m ot14Spec sc In Coins Out) (x : (i : Fin m) → In i) :
    WordOracleComp Unit (List Bool) := do
  let r ← ProbOracleComp.sample (OracleComp.pi proto.sampleCoins)
  let recv ← proto.steps.runEncoded (fun i => (x i, r i))
  let views : (i : Fin m) → PartyView In Coins sc i := fun i => ⟨x i, r i, recv i⟩
  return encodeViewsAndOutputs encView encOut
    (views, fun i => proto.outputOfView i (views i))

@[simp] private theorem decodeOT14Reply_singleton (b : Bool) :
    decodeOT14Reply [b] = Fin.cases () (fun _ => b) := by
  ext s
  fin_cases s <;> rfl

/-- Step-level bridge lemma: interpreting `steps.runEncoded st` against `ot14WordHandler` produces
the exact distribution of `steps.evalWith ot14World st` paired with `()`. -/
theorem Steps.runWith_runEncoded_eq_evalWith {m : ℕ} {State Out : Fin m → Type}
    {sc : Schedule m ot14Spec} (steps : Steps State Out sc) (st : (i : Fin m) → State i) :
    ProbOracleComp.runWith ot14WordHandler (steps.runEncoded st) () =
      (steps.evalWith ot14World st).map (·, ()) := by
  induction steps with
  | done output =>
    simp [Steps.runEncoded, Steps.evalWith_done]
  | message send next ih =>
    simp [Steps.runEncoded, Steps.evalWith_message, ih, PMF.map_comp, Function.comp_def]
  | oracle query next ih =>
    simp [Steps.runEncoded, Steps.evalWith_oracle, ot14World, ot14WordHandler_encodeOT14Query,
      ih, PMF.map_comp, Function.comp_def]

/-- Bridge lemma: interpreting `proto.runEncoded` against the word-encoded `ot14World` handler
produces the exact law of `proto.evalWith ot14World x` mapped through `encodeViewsAndOutputs`. -/
theorem Protocol.eval_runEncoded_eq_evalWith_map {m : ℕ} {sc : Schedule m ot14Spec}
    {In Coins Out : Fin m → Type}
    (encView : (i : Fin m) → PartyView In Coins sc i → List Bool)
    (encOut : (i : Fin m) → Out i → List Bool)
    (proto : Protocol m ot14Spec sc In Coins Out) (x : (i : Fin m) → In i) :
    (ProbOracleComp.runWith ot14WordHandler
      (proto.runEncoded encView encOut x) ()).map Prod.fst =
      (proto.evalWith ot14World x).map (encodeViewsAndOutputs encView encOut) := by
  rw [Protocol.runEncoded, Protocol.evalWith_eq]
  simp [Steps.runWith_runEncoded_eq_evalWith, PMF.map_bind, PMF.bind_map, PMF.map_comp,
    Function.comp_def, Protocol.outputOfView]

/-- `Steps.runEncoded` commutes with relabelling the party states. -/
@[simp] theorem Steps.runEncoded_mapState {m : ℕ} {State State' Out : Fin m → Type}
    {sc : Schedule m ot14Spec} (f : (i : Fin m) → State i → State' i)
    (steps : Steps State' Out sc) (st : (i : Fin m) → State i) :
    (steps.mapState f).runEncoded st = steps.runEncoded (fun i => f i (st i)) := by
  induction steps generalizing State with
  | done output => rfl
  | message send next ih =>
    simp [Steps.mapState, Steps.runEncoded, ih]
  | oracle query next ih =>
    simp [Steps.mapState, Steps.runEncoded, ih]

/-- `Steps.runEncoded` of concatenated steps runs the two parts in sequence. -/
@[simp] theorem Steps.runEncoded_append {m : ℕ} {State Mid Out : Fin m → Type}
    {sc₁ sc₂ : Schedule m ot14Spec}
    (steps₁ : Steps State Mid sc₁)
    (steps₂ : Steps Mid Out sc₂)
    (st : (i : Fin m) → State i) :
    (steps₁.append steps₂).runEncoded st = (do
      let r₁ ← steps₁.runEncoded st
      let r₂ ← steps₂.runEncoded (fun i => steps₁.outputAt i (st i) (r₁ i))
      return fun i => Schedule.Received.append (r₁ i) (r₂ i)) := by
  induction steps₁ with
  | done output =>
    simp [Steps.append, Steps.runEncoded, Steps.outputAt, Schedule.Received.append]
  | message send next ih =>
    simp [Steps.append, Steps.runEncoded, ih, Steps.outputAt,
      Schedule.Received.append]
  | oracle query next ih =>
    simp [Steps.append, Steps.runEncoded, ih, Steps.outputAt,
      Schedule.Received.append]

/-- `Steps.runEncoded` of an embedded sub-protocol runs the sub-protocol and pushes its
received messages to the embedded parties. -/
@[simp] theorem Steps.runEncoded_embed {k m : ℕ} (parties : Fin k ↪ Fin m)
    (Outer : Fin m → Type) {State_k Out_k : Fin k → Type} {sc : Schedule k ot14Spec}
    (steps : Steps State_k Out_k sc)
    (st : (i : Fin m) → Outer i × ((s : Fin k) → (parties s = i) → State_k s)) :
    (Composition.Steps.embed parties Outer steps).runEncoded st =
      Composition.pushScheduleReceived parties sc <$>
        steps.runEncoded (fun s => (st (parties s)).2 s rfl) := by
  induction steps with
  | done output =>
    simp [Composition.Steps.embed, Steps.runEncoded, Composition.pushScheduleReceived]
  | @message _ _ s₀ r₀ Msg _ send next ih =>
    simp only [Composition.Steps.embed, Steps.runEncoded, Steps.runEncoded_mapState, ih,
      bind_pure_comp, Functor.map_map]
    rfl
  | @oracle _ _ op subParties _ query next ih =>
    simp only [Composition.Steps.embed, Steps.runEncoded, Steps.runEncoded_mapState, ih,
      bind_pure_comp, Functor.map_map, map_bind, bind_map_left]
    refine congrArg (Bind.bind _) (funext fun rep => ?_)
    rfl

end Cslib.Crypto.Protocols.MPC
